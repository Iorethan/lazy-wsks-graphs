{-|
Module      : MonaFormulaOperationSubst
Description : Mona formulae subtitution operations.
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module MonaFormulaOperationSubst where

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.String
import Text.Parsec.Token
import Data.List
import Data.Maybe

import MonaParser

import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Debug.Trace as Dbg
import qualified LabelledGraph as Lg


--------------------------------------------------------------------------------------------------------------
-- Part with variables substitutions.
--------------------------------------------------------------------------------------------------------------

-- |Substitute variables with mona terms (does not check whether variables are
-- of appropriate types).
-- arg1: MonaMacroParam (parameter of a predicate), MonaTerm (term that should
-- replaced the macro parameter)
substituteVars :: [(MonaMacroParam, MonaTerm)] -> MonaFormula -> MonaFormula
substituteVars repl (MonaFormulaPredCall name terms) = MonaFormulaPredCall name $ map (substituteTerms repl) terms
substituteVars repl (MonaFormulaAtomic atom) = MonaFormulaAtomic $ substituteAtoms repl atom
substituteVars repl (MonaFormulaVar var) = MonaFormulaAtomic $  MonaAtomTerm $ substituteVar repl var
substituteVars repl (MonaFormulaNeg f) = MonaFormulaNeg (substituteVars repl f)
substituteVars repl (MonaFormulaDisj f1 f2) = MonaFormulaDisj (substituteVars repl f1) (substituteVars repl f2)
substituteVars repl (MonaFormulaConj f1 f2) = MonaFormulaConj (substituteVars repl f1) (substituteVars repl f2)
substituteVars repl (MonaFormulaImpl f1 f2) = MonaFormulaImpl (substituteVars repl f1) (substituteVars repl f2)
substituteVars repl (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (substituteVars repl f1) (substituteVars repl f2)
substituteVars repl (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (substituteVars repl' f) where
  repl' = filter (\a -> not $ elem (varFromMacroParam a) vars) repl
substituteVars repl (MonaFormulaEx1 vardecl f) = MonaFormulaEx1 vardecl' (substituteVars repl' f) where
  vardecl' = applyVarDecl (substituteVars repl') vardecl
  repl' = filterSubst vardecl repl
substituteVars repl (MonaFormulaEx2 vardecl f) = MonaFormulaEx2 vardecl'  (substituteVars repl' f) where
  vardecl' = applyVarDecl (substituteVars repl') vardecl
  repl' = filterSubst vardecl repl
substituteVars repl (MonaFormulaAll0 vars f) = MonaFormulaAll0 vars (substituteVars repl' f) where
  repl' = filter (\a -> not $ elem (varFromMacroParam a) vars) repl
substituteVars repl (MonaFormulaAll1 vardecl f) = MonaFormulaAll1 vardecl' (substituteVars repl' f) where
  vardecl' = applyVarDecl (substituteVars repl') vardecl
  repl' = filterSubst vardecl repl
substituteVars repl (MonaFormulaAll2 vardecl f) = MonaFormulaAll2 vardecl' (substituteVars repl' f) where
  vardecl' = applyVarDecl (substituteVars repl') vardecl
  repl' = filterSubst vardecl repl
--substituteVars repl _ = error "Cyclic dependecy between predicates"


-- |Subtitute variable (given by its name) with a corresponding substitution term.
substituteVar :: [(MonaMacroParam, MonaTerm)] -> String -> MonaTerm
substituteVar repl var = Map.findWithDefault (MonaTermVar var) var sub
  where
    sub = Map.fromList $ map (mappred) repl
    mappred ((MonaMacroParamVar0 vars),b) = (head vars, b)
    mappred ((MonaMacroParamVar1 vars),b) = (fst $ head vars, b)
    mappred ((MonaMacroParamVar2 vars),b) = (fst $ head vars, b)


-- |Subtitute variables in atoms with corresponding substitutions (terms).
substituteAtoms :: [(MonaMacroParam, MonaTerm)] -> MonaAtom -> MonaAtom
substituteAtoms repl (MonaAtomLe t1 t2) = MonaAtomLe (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomLeq t1 t2) = MonaAtomLeq (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomGe t1 t2) = MonaAtomGe (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomGeq t1 t2) = MonaAtomGeq (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomEq t1 t2) = MonaAtomEq (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomNeq t1 t2) = MonaAtomNeq (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomIn t1 t2) = MonaAtomIn (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomNotIn t1 t2) = MonaAtomNotIn (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomSub t1 t2) = MonaAtomSub (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomSing t) = MonaAtomSing $ substituteTerms repl t
substituteAtoms repl (MonaAtomEps t) = MonaAtomEps $ substituteTerms repl t
substituteAtoms repl (MonaAtomTerm t) = MonaAtomTerm $ substituteTerms repl t
substituteAtoms repl (MonaAtomIsEmpty t) = MonaAtomIsEmpty $ substituteTerms repl t
substituteAtoms _ MonaAtomTrue = MonaAtomTrue
substituteAtoms _ MonaAtomFalse = MonaAtomFalse


-- |Subtitute variables in terms with corresponding substitutions (terms).
substituteTerms :: [(MonaMacroParam, MonaTerm)] -> MonaTerm -> MonaTerm
substituteTerms repl (MonaTermVar var) = substituteVar repl var
substituteTerms repl (MonaTermPlus t1 t2) = MonaTermPlus (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermMinus t1 t2) = MonaTermMinus (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermCat t1 t2) = MonaTermCat (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermUp t) = MonaTermUp (substituteTerms repl t)
substituteTerms repl (MonaTermBoolCall name terms) = MonaTermBoolCall name $ map (substituteTerms repl) terms
substituteTerms repl (MonaTermBool atom) = MonaTermBool $ substituteAtoms repl atom
substituteTerms repl (MonaTermUnion t1 t2) = MonaTermUnion (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermInter t1 t2) = MonaTermInter (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermDifference t1 t2) = MonaTermDifference (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermSet t) = MonaTermSet $ map (substituteTerms repl) t
substituteTerms repl t = t


-- |Filter substitutions (remove substitutions that are in var list).
-- arg1: varlist (list of quantified variables)
-- arg2: given substitution
filterSubst :: [(String, Maybe MonaFormula)] -> [(MonaMacroParam, MonaTerm)] -> [(MonaMacroParam, MonaTerm)]
filterSubst vars = filter (\a -> not $ elem (varFromMacroParam a) vars')
  where
    vars' = map (fst) vars


-- |Get variable name from mona macro param.
varFromMacroParam :: (MonaMacroParam, MonaTerm) -> String
varFromMacroParam ((MonaMacroParamVar0 vars),_) = head vars
varFromMacroParam ((MonaMacroParamVar1 vars),_) = fst $ head vars
varFromMacroParam ((MonaMacroParamVar2 vars),_) = fst $ head vars


-- |Apply function on list of variable declarations.
applyVarDecl :: (MonaFormula -> MonaFormula) -> [(String, Maybe MonaFormula)] -> [(String, Maybe MonaFormula)]
applyVarDecl f = map (\(a,b) -> (a,b >>= \a -> return $ f a))



--------------------------------------------------------------------------------------------------------------
-- Part with renaming bound variables.
--------------------------------------------------------------------------------------------------------------

renameBVFile :: MonaFile -> MonaFile
renameBVFile (MonaFile dom decls) = MonaFile dom (renameBVDecl [] decls [])


renameBVDecl :: [MonaDeclaration] -> [MonaDeclaration] -> [Lo.Var] -> [MonaDeclaration]
renameBVDecl _ [] _ = []
renameBVDecl done (x:xs) vars = conv:(renameBVDecl (done ++ [conv]) xs (vars ++ v)) where
    conv = case x of
      MonaDeclPred name pars fle -> MonaDeclPred name pars (renameBVFormula vars fle)
      MonaDeclMacro name pars fle -> MonaDeclMacro name pars (renameBVFormula vars fle)
      MonaDeclFormula fle -> MonaDeclFormula $ renameBVFormula vars fle
      MonaDeclVar0 vardecl -> MonaDeclVar0 vardecl -- We do not rename free variables
      MonaDeclVar1 vardecl -> MonaDeclVar1 vardecl -- We do not rename free variables
      MonaDeclVar2 vardecl -> MonaDeclVar2 vardecl
      MonaDeclAssert fle -> MonaDeclAssert $ renameBVFormula vars fle
      MonaDeclAllpos var -> MonaDeclAllpos var
      MonaDeclLastpos var -> MonaDeclLastpos var
      MonaDeclConst atom -> MonaDeclConst atom
      a -> error $ "Unsupported formula: " ++ (show a)
    v = varsDecl conv


renameBVForDecl :: [(String, Maybe MonaFormula)] -> [Lo.Var] -> [(String, Maybe MonaFormula)]
renameBVForDecl [] _ = []
renameBVForDecl ((var,f):xs) vars =
  if elem var vars then (new, f >>= \a -> Just $ substituteVars repl a):(renameBVForDecl xs (new:vars))
  else  (var,f):(renameBVForDecl xs (var:vars)) where
    new = getNewVarName (vars ++ vars') 0
    repl = [(MonaMacroParamVar1 [(var, Nothing)], MonaTermVar new)]
    vars' = case f of
      Just a -> varsFormula a
      Nothing -> []


-- Works for formulae without forall
renameBVFormula :: [Lo.Var] -> MonaFormula -> MonaFormula
renameBVFormula vars t@(MonaFormulaPredCall name terms) = t
renameBVFormula vars (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
renameBVFormula vars (MonaFormulaVar var) = MonaFormulaVar var
renameBVFormula vars (MonaFormulaNeg f) = MonaFormulaNeg (renameBVFormula vars f)
renameBVFormula vars (MonaFormulaDisj f1 f2) = MonaFormulaDisj (renameBVFormula vars f1) (renameBVFormula vars f2)
renameBVFormula vars (MonaFormulaConj f1 f2) = MonaFormulaConj (renameBVFormula vars f1) (renameBVFormula vars f2)
renameBVFormula vars (MonaFormulaImpl f1 f2) = MonaFormulaImpl (renameBVFormula vars f1) (renameBVFormula vars f2)
renameBVFormula vars (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (renameBVFormula vars f1) (renameBVFormula vars f2)
renameBVFormula vars (MonaFormulaEx0 [var] f) = handleQuantifRename vars var f var (MonaFormulaEx0) (fst)
renameBVFormula vars (MonaFormulaEx1 [decl] f) = handleQuantifRename vars (fst decl) f decl (MonaFormulaEx1) (id)
renameBVFormula vars (MonaFormulaEx2 [decl] f) = handleQuantifRename vars (fst decl) f decl (MonaFormulaEx2) (id)
renameBVFormula vars (MonaFormulaAll0 [var] f) = handleQuantifRename vars var f var (MonaFormulaAll0) (fst)
renameBVFormula vars (MonaFormulaAll1 [decl] f) = handleQuantifRename vars (fst decl) f decl (MonaFormulaAll1) (id)
renameBVFormula vars (MonaFormulaAll2 [decl] f) = handleQuantifRename vars (fst decl) f decl (MonaFormulaAll2) (id)
renameBVFormula vars t = error $ "renameBVFormula: " ++ show t


handleQuantifRename :: [Lo.Var] -> Lo.Var -> MonaFormula -> a -> ([a] -> MonaFormula -> MonaFormula) -> ((String, Maybe MonaFormula) -> a) -> MonaFormula
handleQuantifRename vars var f decl cons proj =
  if (elem var vars) then cons [decl] (renameBVFormula (var:vars) f)
  else cons decl' (renameBVFormula (new:vars) f') where
    repl = [(MonaMacroParamVar1 [(var, Nothing)], MonaTermVar new)]
    new = getNewVarName (vars ++ (varsFormula f)) 0
    f' = substituteVars repl f
    decl' = [proj (new, Nothing)]

getNewVarName :: [Lo.Var] -> Int -> Lo.Var
getNewVarName lst i =
  if elem var lst then getNewVarName lst (i+1)
  else var where
    var = "T" ++ (show i)


--------------------------------------------------------------------------------------------------------------
-- Part with (free) variables determination.
--------------------------------------------------------------------------------------------------------------

freeVarsTerm :: MonaTerm -> [Lo.Var]
freeVarsTerm (MonaTermVar var) = [var]
freeVarsTerm MonaTermEmpty = []
freeVarsTerm MonaTermDots = []
freeVarsTerm (MonaTermConst num) = []
freeVarsTerm (MonaTermPlus t1 t2) = nub $ (freeVarsTerm t1) ++ (freeVarsTerm t2)
freeVarsTerm (MonaTermCat t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2
freeVarsTerm (MonaTermMinus t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2
freeVarsTerm (MonaTermUp t) = freeVarsTerm t
freeVarsTerm (MonaTermRoot) = []
freeVarsTerm (MonaTermBool atom) = freeVarsAtom atom
freeVarsTerm (MonaTermBoolCall _ t) = concat $ map (freeVarsTerm) t
freeVarsTerm (MonaTermPConst _) =  []
freeVarsTerm (MonaTermUnion t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2
freeVarsTerm (MonaTermInter t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2
freeVarsTerm (MonaTermSet t) = concat $ map (freeVarsTerm) t
freeVarsTerm (MonaTermDifference t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2



freeVarsAtom :: MonaAtom -> [Lo.Var]
freeVarsAtom (MonaAtomLe t1 t2) = nub $ (freeVarsTerm t1) ++ (freeVarsTerm t2)
freeVarsAtom (MonaAtomLeq t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomEq t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomNeq t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomGe t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomGeq t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomIn t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomNotIn t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomSub t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomEps t) = freeVarsTerm t
freeVarsAtom (MonaAtomSing t) = freeVarsTerm t
freeVarsAtom (MonaAtomTerm t) = freeVarsTerm t
freeVarsAtom (MonaAtomIsEmpty t) = freeVarsTerm t
freeVarsAtom MonaAtomTrue = []
freeVarsAtom MonaAtomFalse = []


varsDecl (MonaDeclPred _ _ f) = boundVarsFormula f --varsFormula f
varsDecl (MonaDeclMacro _ _ f) = boundVarsFormula f -- varsFormula f
varsDecl (MonaDeclVar0 vars) = [] -- vars
varsDecl (MonaDeclVar1 decl) = [] -- nub $ map (fst) decl
varsDecl (MonaDeclVar2 decl) = [] -- nub $ map (fst) decl
varsDecl (MonaDeclLastpos _) = []
varsDecl (MonaDeclAllpos _) = []
varsDecl (MonaDeclFormula f) = boundVarsFormula f -- varsFormula f
varsDecl (MonaDeclAssert f) = boundVarsFormula f -- varsFormula f
varsDecl (MonaDeclConst atom) = []


boundVarsFormula :: MonaFormula -> [Lo.Var]
boundVarsFormula f = (varsFormula f) \\ (freeVarsFormula f)


varsFormula :: MonaFormula -> [Lo.Var]
varsFormula (MonaFormulaAtomic atom) = freeVarsAtom atom
varsFormula (MonaFormulaVar var) = [var]
varsFormula (MonaFormulaNeg f) = varsFormula f
varsFormula (MonaFormulaConj f1 f2) = nub $ (varsFormula f1) ++ (varsFormula f2)
varsFormula (MonaFormulaDisj f1 f2) = varsFormula (MonaFormulaConj f1 f2)
varsFormula (MonaFormulaImpl f1 f2) = varsFormula (MonaFormulaConj f1 f2)
varsFormula (MonaFormulaEquiv f1 f2) = varsFormula (MonaFormulaConj f1 f2)
varsFormula (MonaFormulaEx0 [var] f) = var:(varsFormula f)
varsFormula (MonaFormulaEx1 [var] f) = (fst var):(mapVarDecl (varsFormula) var) ++ (varsFormula f)
varsFormula (MonaFormulaEx2 [var] f) = (fst var):(mapVarDecl (varsFormula) var) ++ (varsFormula f)
varsFormula (MonaFormulaAll0 v f) = varsFormula (MonaFormulaEx0 v f)
varsFormula (MonaFormulaAll1 v f) = varsFormula (MonaFormulaEx1 v f)
varsFormula (MonaFormulaAll2 v f) = varsFormula (MonaFormulaEx2 v f)
varsFormula (MonaFormulaPredCall _ t) = concat $ map (freeVarsTerm) t
varsFormula t = error $ "varsFormula: unimplemented: " ++ show t  -- TODO: incomplete


freeVarsFormula :: MonaFormula -> [Lo.Var]
freeVarsFormula (MonaFormulaAtomic atom) = freeVarsAtom atom
freeVarsFormula f@(MonaFormulaPredCall _ terms) = varsFormula f
freeVarsFormula (MonaFormulaVar var) = [var]
freeVarsFormula (MonaFormulaNeg f) = freeVarsFormula f
freeVarsFormula (MonaFormulaConj f1 f2) = nub $ (freeVarsFormula f1) ++ (freeVarsFormula f2)
freeVarsFormula (MonaFormulaDisj f1 f2) = freeVarsFormula (MonaFormulaConj f1 f2)
freeVarsFormula (MonaFormulaImpl f1 f2) = freeVarsFormula (MonaFormulaConj f1 f2)
freeVarsFormula (MonaFormulaEquiv f1 f2) = freeVarsFormula (MonaFormulaConj f1 f2)
freeVarsFormula (MonaFormulaExGen var f) = delete var $ freeVarsFormula f
freeVarsFormula (MonaFormulaEx0 [var] f) = delete var $ freeVarsFormula f
freeVarsFormula (MonaFormulaEx1 [var] f) = delete (fst var) $ (mapVarDecl (freeVarsFormula) var) ++ (freeVarsFormula f)
freeVarsFormula (MonaFormulaEx2 [var] f) = delete (fst var) $ (mapVarDecl (freeVarsFormula) var) ++ (freeVarsFormula f)
freeVarsFormula (MonaFormulaAll0 v f) = freeVarsFormula (MonaFormulaEx0 v f)
freeVarsFormula (MonaFormulaAll1 v f) = freeVarsFormula (MonaFormulaEx1 v f)
freeVarsFormula (MonaFormulaAll2 v f) = freeVarsFormula (MonaFormulaEx2 v f)
freeVarsFormula _ = error "freeVarsFormula: unimplemented" -- TODO: incomplete


mapVarDecl :: (MonaFormula -> [a]) -> (String, Maybe MonaFormula) -> [a]
mapVarDecl f var = Aux.mapLstMaybe f (snd var)

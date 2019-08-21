{-|
Module      : MonaFormulaOperation
Description : Mona formulae operations.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaFormulaOperation where

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.String
import Text.Parsec.Token
import Data.List
import Data.Maybe
import Debug.Trace

import MonaParser
import MonaFormulaOperationSubst

import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Debug.Trace as Dbg
import qualified LabelledGraph as Lg


--------------------------------------------------------------------------------------------------------------
-- Part with unwinding quantifiers (ex2 X,Y: ---> ex2 X: ex2 Y:)
--------------------------------------------------------------------------------------------------------------

-- |Unwind quantifiers of a formula, i.e, ex1 x,y --> ex1 x: ex1 y
unwindQuantifFormula :: MonaFormula -> MonaFormula
unwindQuantifFormula (MonaFormulaEx0 xs f) = foldr (\a g -> MonaFormulaEx0 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaEx1 xs f) = foldr (\a g -> MonaFormulaEx1 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaEx2 xs f) = foldr (\a g -> MonaFormulaEx2 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaAll0 xs f) = foldr (\a g -> MonaFormulaAll0 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaAll1 xs f) = foldr (\a g -> MonaFormulaAll1 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaAll2 xs f) = foldr (\a g -> MonaFormulaAll2 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
unwindQuantifFormula (MonaFormulaVar var) = MonaFormulaVar var
unwindQuantifFormula (MonaFormulaNeg f) = MonaFormulaNeg (unwindQuantifFormula f)
unwindQuantifFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (unwindQuantifFormula f1) (unwindQuantifFormula f2)
unwindQuantifFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (unwindQuantifFormula f1) (unwindQuantifFormula f2)
unwindQuantifFormula (MonaFormulaImpl f1 f2) = MonaFormulaImpl (unwindQuantifFormula f1) (unwindQuantifFormula f2)
unwindQuantifFormula (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (unwindQuantifFormula f1) (unwindQuantifFormula f2)
unwindQuantifFormula (MonaFormulaPredCall s t) = MonaFormulaPredCall s t


-- |Unwind quantifiers of a macro parameter, i.e, ex1 x,y --> ex1 x: ex1 y
unwindQuantifMacroParam :: MonaMacroParam -> [MonaMacroParam]
unwindQuantifMacroParam (MonaMacroParamVar0 vars) = map (\a -> MonaMacroParamVar0 [a]) vars
unwindQuantifMacroParam (MonaMacroParamVar1 vars) = map (\a -> MonaMacroParamVar1 [a]) vars
unwindQuantifMacroParam (MonaMacroParamVar2 vars) = map (\a -> MonaMacroParamVar2 [a]) vars
unwindQuantifMacroParam a = return a


-- |Unwind quantifiers of a declaration, i.e, ex1 x,y --> ex1 x: ex1 y
unwindQuantifDecl :: MonaDeclaration -> [MonaDeclaration]
unwindQuantifDecl (MonaDeclFormula f) = [MonaDeclFormula $ unwindQuantifFormula f]
unwindQuantifDecl (MonaDeclAssert f) = [MonaDeclAssert $ unwindQuantifFormula f]
unwindQuantifDecl (MonaDeclVar0 vars) = map (\a -> MonaDeclVar0 [a]) vars
unwindQuantifDecl (MonaDeclVar1 vars) = map (\a -> MonaDeclVar1 [a]) vars
unwindQuantifDecl (MonaDeclVar2 vars) = map (\a -> MonaDeclVar2 [a]) vars
unwindQuantifDecl (MonaDeclPred name params f) = [MonaDeclPred name (params >>= unwindQuantifMacroParam) (unwindQuantifFormula f)]
unwindQuantifDecl (MonaDeclMacro name params f) = [MonaDeclMacro name (params >>= unwindQuantifMacroParam) (unwindQuantifFormula f)]
unwindQuantifDecl a = return a                                           -- TODO: need to be refined


-- |Unwind quantifiers of a mona file, i.e, ex1 x,y --> ex1 x: ex1 y
unwindQuantifFile :: MonaFile -> MonaFile
unwindQuantifFile (MonaFile dom decls) = MonaFile dom (decls >>= unwindQuantifDecl)


--------------------------------------------------------------------------------------------------------------
-- Part with formula flattening (removing predicate calls).
--------------------------------------------------------------------------------------------------------------

replaceAllCallsFile :: MonaFile -> MonaFile
replaceAllCallsFile file
  | Lg.isReachEmptyLabelGraph "root" $ buildCallGraph file = file
  | otherwise = replaceAllCallsFile $ replaceCallsFile file


-- |Replace calls of predicates with its body.
replaceCallsFile :: MonaFile -> MonaFile
replaceCallsFile (MonaFile dom decls) = MonaFile dom (replaceCallsDecl [] decls)


-- |Replace calls of predicates with its body in mona declaration list.
replaceCallsDecl :: [MonaDeclaration] -> [MonaDeclaration] -> [MonaDeclaration]
replaceCallsDecl _ [] = []
replaceCallsDecl done (x:xs) = conv:(replaceCallsDecl (done ++ [conv]) xs) where
    conv = case x of
      MonaDeclPred name pars fle -> MonaDeclPred name pars (replaceCallsFormulas done fle)
      MonaDeclMacro name pars fle -> MonaDeclMacro name pars (replaceCallsFormulas done fle)
      MonaDeclFormula fle -> MonaDeclFormula $ replaceCallsFormulas done fle
      MonaDeclVar0 vardecl -> MonaDeclVar0 vardecl
      MonaDeclVar1 vardecl -> MonaDeclVar1 $ applyVarDecl (replaceCallsFormulas done) vardecl
      MonaDeclVar2 vardecl -> MonaDeclVar2 $ applyVarDecl (replaceCallsFormulas done) vardecl
      MonaDeclAssert fle -> MonaDeclAssert $ replaceCallsFormulas done fle
      MonaDeclAllpos x -> MonaDeclAllpos x
      MonaDeclLastpos x -> MonaDeclLastpos x
      MonaDeclConst atom -> MonaDeclConst $ at' where
        MonaFormulaAtomic at' = replaceCallsFormulas done $ MonaFormulaAtomic atom
      a -> error $ "Unsupported formula: " ++ (show a)


-- |Replace pred calls in a given formula with already flattened declarations. No
-- cyclic dependency is allowed.
replaceCallsFormulas :: [MonaDeclaration] -> MonaFormula -> MonaFormula
replaceCallsFormulas decls (MonaFormulaAtomic (MonaAtomTerm (MonaTermBoolCall name params))) =
  fromJust $ find (filterMacro name) decls >>= replacePred params
replaceCallsFormulas decls f@(MonaFormulaAtomic (MonaAtomTerm (MonaTermVar name)))  = fromJust ret where
  ret = case find (filterMacro name) decls of
    Just x -> replacePred [] x
    Nothing -> Just f
replaceCallsFormulas decls f@(MonaFormulaAtomic _) = f
replaceCallsFormulas decls f@(MonaFormulaVar name) = fromJust ret where
  ret = case find (filterMacro name) decls of
    Just x -> replacePred [] x
    Nothing -> Just f
replaceCallsFormulas decls (MonaFormulaNeg f) = MonaFormulaNeg (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaDisj f1 f2) =
    MonaFormulaDisj (replaceCallsFormulas decls f1) (replaceCallsFormulas decls f2)
replaceCallsFormulas decls (MonaFormulaConj f1 f2) =
    MonaFormulaConj (replaceCallsFormulas decls f1) (replaceCallsFormulas decls f2)
replaceCallsFormulas decls (MonaFormulaImpl f1 f2) =
    MonaFormulaImpl (replaceCallsFormulas decls f1) (replaceCallsFormulas decls f2)
replaceCallsFormulas decls (MonaFormulaEquiv f1 f2) =
    MonaFormulaEquiv (replaceCallsFormulas decls f1) (replaceCallsFormulas decls f2)
replaceCallsFormulas decls (MonaFormulaEx0 vars f) =
    MonaFormulaEx0 vars (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaEx1 vardecl f) =
    MonaFormulaEx1 (applyVarDecl (replaceCallsFormulas decls) vardecl) (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaEx2 vardecl f) =
    MonaFormulaEx2 (applyVarDecl (replaceCallsFormulas decls) vardecl) (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaAll0 vars f) =
    MonaFormulaAll0 vars (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaAll1 vardecl f) =
    MonaFormulaAll1 (applyVarDecl (replaceCallsFormulas decls) vardecl) (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaAll2 vardecl f) =
    MonaFormulaAll2 (applyVarDecl (replaceCallsFormulas decls) vardecl) (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaPredCall name params) =
    fromJust $ find (filterMacro name) decls >>= replacePred params


-- |Replace a predicate call (given arguments) with predicate body.
replacePred :: [MonaTerm] -> MonaDeclaration -> Maybe MonaFormula
replacePred args (MonaDeclPred _ params formula) = return $ substituteVars (zip (expandPredParams params) args) formula
replacePred args (MonaDeclMacro _ params formula) = return $ substituteVars (zip (expandPredParams params) args) formula


-- |Expand variables in predicate declaration into singleton variable declaration -- ex2 X,Y --> ex2 X, ex2 Y
expandPredParams :: [MonaMacroParam] -> [MonaMacroParam]
expandPredParams xs = xs >>= expand where
  expand (MonaMacroParamVar0 a) = a >>= \x -> return $ MonaMacroParamVar0 [x]
  expand (MonaMacroParamVar1 a) = a >>= \x -> return $ MonaMacroParamVar1 [x]
  expand (MonaMacroParamVar2 a) = a >>= \x -> return $ MonaMacroParamVar2 [x]


-- |Filter mona declarations that have a specified name.
filterMacro :: String -> MonaDeclaration -> Bool
filterMacro name (MonaDeclPred nm _ _) = nm == name
filterMacro name (MonaDeclMacro nm _ _) = nm == name
filterMacro name _ = False


--------------------------------------------------------------------------------------------------------------
-- Part with removing where construction.
--------------------------------------------------------------------------------------------------------------

-- |Assumes singleton quatified variables (i.e. after unwindQuantif function).
removeWhereFormula :: MonaFormula -> MonaFormula
removeWhereFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
removeWhereFormula f@(MonaFormulaPredCall _ _) = f
removeWhereFormula (MonaFormulaVar var) = MonaFormulaVar var
removeWhereFormula (MonaFormulaNeg f) = MonaFormulaNeg (removeWhereFormula f)
removeWhereFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (removeWhereFormula f1) (removeWhereFormula f2)
removeWhereFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (removeWhereFormula f1) (removeWhereFormula f2)
removeWhereFormula (MonaFormulaImpl f1 f2) = MonaFormulaImpl (removeWhereFormula f1) (removeWhereFormula f2)
removeWhereFormula (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (removeWhereFormula f1) (removeWhereFormula f2)
removeWhereFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (removeWhereFormula f)
removeWhereFormula (MonaFormulaEx1 decl f) = expandWhereExQuantif (MonaFormulaEx1) decl (removeWhereFormula f)
removeWhereFormula (MonaFormulaEx2 decl f) = expandWhereExQuantif (MonaFormulaEx2) decl (removeWhereFormula f)
removeWhereFormula (MonaFormulaAll0 vars f) = MonaFormulaAll0 vars (removeWhereFormula f)
removeWhereFormula (MonaFormulaAll1 decl f) = expandWhereAllQuantif (MonaFormulaAll1) decl (removeWhereFormula f)
removeWhereFormula (MonaFormulaAll2 decl f) = expandWhereAllQuantif (MonaFormulaAll2) decl (removeWhereFormula f)

expandWhereExQuantif cons [(var, fwh)] f = cons [(var, Nothing)] (expand fwh f) where
  expand (Just f1) f2 = MonaFormulaConj f1 f2
  expand Nothing f2 = f2


expandWhereAllQuantif cons [(var, fwh)] f = cons [(var, Nothing)] (expand fwh f) where
  expand (Just f1) f2 = MonaFormulaImpl f1 f2
  expand Nothing f2 = f2


removeWhereFile :: MonaFile -> MonaFile
removeWhereFile (MonaFile dom decls) = MonaFile dom (map (removeWhereDecl) decls)


removeWhereDecl :: MonaDeclaration -> MonaDeclaration
removeWhereDecl (MonaDeclFormula f) = MonaDeclFormula $ removeWhereFormula f
removeWhereDecl (MonaDeclPred name params f) = MonaDeclPred name params (removeWhereFormula f)
removeWhereDecl a = a  -- TODO: need to be refined


-- |Assumes singleton quatified variables (i.e. after unwindQuantif function).
removeWhereAllFormula :: MonaFormula -> MonaFormula
removeWhereAllFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
removeWhereAllFormula f@(MonaFormulaPredCall _ _) = f
removeWhereAllFormula (MonaFormulaVar var) = MonaFormulaVar var
removeWhereAllFormula (MonaFormulaNeg f) = MonaFormulaNeg (removeWhereAllFormula f)
removeWhereAllFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (removeWhereAllFormula f1) (removeWhereAllFormula f2)
removeWhereAllFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (removeWhereAllFormula f1) (removeWhereAllFormula f2)
removeWhereAllFormula (MonaFormulaImpl f1 f2) = MonaFormulaImpl (removeWhereAllFormula f1) (removeWhereAllFormula f2)
removeWhereAllFormula (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (removeWhereAllFormula f1) (removeWhereAllFormula f2)
removeWhereAllFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (removeWhereAllFormula f)
removeWhereAllFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (removeWhereAllFormula f)
removeWhereAllFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (removeWhereAllFormula f)
removeWhereAllFormula (MonaFormulaAll0 vars f) = MonaFormulaAll0 vars (removeWhereAllFormula f)
removeWhereAllFormula (MonaFormulaAll1 decl f)
  | isRestricted decl = MonaFormulaNeg $ MonaFormulaEx1 decl (MonaFormulaNeg $ removeWhereAllFormula f)
  | otherwise = MonaFormulaAll1 decl $ removeWhereAllFormula f
removeWhereAllFormula (MonaFormulaAll2 decl f)
  | isRestricted decl = MonaFormulaNeg $ MonaFormulaEx2 decl (MonaFormulaNeg $ removeWhereAllFormula f)
  | otherwise = MonaFormulaAll2 decl $ removeWhereAllFormula f

isRestricted [(var, fwh)] = isJust fwh


removeWhereAllFile :: MonaFile -> MonaFile
removeWhereAllFile (MonaFile dom decls) = MonaFile dom (map (removeWhereAllDecl) decls)


removeWhereAllDecl :: MonaDeclaration -> MonaDeclaration
removeWhereAllDecl (MonaDeclFormula f) = MonaDeclFormula $ removeWhereAllFormula f
removeWhereAllDecl (MonaDeclPred name params f) = MonaDeclPred name params (removeWhereAllFormula f)
removeWhereAllDecl a = a  -- TODO: need to be refined


--------------------------------------------------------------------------------------------------------------
-- Part with the predicate and macros triming
--------------------------------------------------------------------------------------------------------------

getCallsFromula :: [String] -> MonaFormula -> [String]
getCallsFromula int (MonaFormulaPredCall name terms) = nub $ name:(concat $ map (getCallsTerm int) terms)
getCallsFromula int (MonaFormulaAtomic atom) = getCallsAtom int atom
getCallsFromula int (MonaFormulaVar var) = intersect [var] int
getCallsFromula int (MonaFormulaNeg f) = nub $ getCallsFromula int f
getCallsFromula int (MonaFormulaDisj f1 f2) = nub $ (getCallsFromula int f1) ++ (getCallsFromula int f2)
getCallsFromula int (MonaFormulaConj f1 f2) = nub $ (getCallsFromula int f1) ++ (getCallsFromula int f2)
getCallsFromula int (MonaFormulaImpl f1 f2) = nub $ (getCallsFromula int f1) ++ (getCallsFromula int f2)
getCallsFromula int (MonaFormulaEquiv f1 f2) = nub $ (getCallsFromula int f1) ++ (getCallsFromula int f2)
getCallsFromula int (MonaFormulaEx0 vars f) = getCallsFromula int f
getCallsFromula int (MonaFormulaEx1 decl f) = nub $ (getListCalls int decl) ++ (getCallsFromula int f)
getCallsFromula int (MonaFormulaEx2 decl f) = nub $ (getListCalls int decl) ++ (getCallsFromula int f)
getCallsFromula int (MonaFormulaAll0 vars f) = getCallsFromula int f
getCallsFromula int (MonaFormulaAll1 decl f) = nub $ (getListCalls int decl) ++ (getCallsFromula int f)
getCallsFromula int (MonaFormulaAll2 decl f) = nub $ (getListCalls int decl) ++ (getCallsFromula int f)


getCallsAtom :: [String] -> MonaAtom -> [String]
getCallsAtom int (MonaAtomTerm term) = getCallsTerm int term
getCallsAtom int atom = intersect (freeVarsAtom atom) int


getCallsTerm :: [String] -> MonaTerm -> [String]
getCallsTerm int (MonaTermBoolCall name terms) = name:(concat $ map (getCallsTerm int) terms)
getCallsTerm int t = intersect (freeVarsTerm t) int


getPredsMacros :: [MonaDeclaration] -> [String]
getPredsMacros = map (getPredMacroName) . filter (isPredMacro) where
  isPredMacro (MonaDeclPred _ _ _) = True
  isPredMacro (MonaDeclMacro _ _ _) = True
  isPredMacro _ = False
  getPredMacroName (MonaDeclPred name _ _) = name
  getPredMacroName (MonaDeclMacro name _ _) = name
  getPredMacroName _ = error "wrong filter"


getListCalls :: [String] -> [(String, Maybe MonaFormula)] -> [String]
getListCalls int lst = (catMaybes $ map (snd) lst) >>= getCallsFromula int


buildCallGraph :: MonaFile -> Lg.LabGraph String
buildCallGraph (MonaFile _ decls) = Lg.builLabelGraph $ graphDecl decls where
  graphDecl [] = []
  graphDecl ((MonaDeclFormula f):xs) = ("root", callsFormula f):(graphDecl xs)
  graphDecl ((MonaDeclPred name _ f):xs) = (name, callsFormula f):(graphDecl xs)
  graphDecl ((MonaDeclMacro name _ f):xs) = (name, callsFormula f):(graphDecl xs)
  graphDecl ((MonaDeclVar0 _):xs) = graphDecl xs
  graphDecl ((MonaDeclVar1 dec):xs) = ("root", paramsCalls dec):(graphDecl xs)
  graphDecl ((MonaDeclVar2 dec):xs) = ("root", paramsCalls dec):(graphDecl xs)
  graphDecl ((MonaDeclAssert f):xs) = ("root", callsFormula f):(graphDecl xs)
  graphDecl ((MonaDeclAllpos _):xs) = graphDecl xs
  graphDecl ((MonaDeclLastpos _):xs) = graphDecl xs
  graphDecl ((MonaDeclConst atom):xs) = ("root", getCallsAtom allMP atom):(graphDecl xs)
  allMP = getPredsMacros decls
  callsFormula f = getCallsFromula allMP f
  paramsCalls dec = getListCalls allMP dec


gdDebug :: MonaFile -> [(String, [String])]
gdDebug (MonaFile _ decls) = graphDecl decls where
  graphDecl [] = []
  graphDecl ((MonaDeclFormula f):xs) = ("root", getCallsFromula allMP f):(graphDecl xs)
  graphDecl ((MonaDeclPred name _ f):xs) = (name, getCallsFromula allMP f):(graphDecl xs)
  graphDecl ((MonaDeclMacro name _ f):xs) = (name, getCallsFromula allMP f):(graphDecl xs)
  graphDecl ((MonaDeclVar0 _):xs) = graphDecl xs
  graphDecl ((MonaDeclVar1 dec):xs) = ("root", getListCalls allMP dec):(graphDecl xs)
  graphDecl ((MonaDeclVar2 dec):xs) = ("root", getListCalls allMP dec):(graphDecl xs)
  allMP = getPredsMacros decls


removeRedundantPreds :: MonaFile -> MonaFile
removeRedundantPreds mf@(MonaFile dom decls) = MonaFile dom $ filter flt decls where
  reach = Lg.reachableLabelGraph "root" $ buildCallGraph mf
  flt (MonaDeclFormula _) = True
  flt (MonaDeclPred name _ f) = name `elem` reach
  flt (MonaDeclMacro name _ f) = name `elem` reach
  flt (MonaDeclVar0 _) = True
  flt (MonaDeclVar1 _) = True
  flt (MonaDeclVar2 _) = True
  flt (MonaDeclAssert _) = True
  flt (MonaDeclAllpos _) = True
  flt (MonaDeclLastpos _) = True
  flt (MonaDeclConst _) = True


--------------------------------------------------------------------------------------------------------------
-- Part with removing universal quantification.
--------------------------------------------------------------------------------------------------------------

removeForAllFormula :: MonaFormula -> MonaFormula
removeForAllFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
removeForAllFormula (MonaFormulaPredCall name f) = MonaFormulaPredCall name f
removeForAllFormula (MonaFormulaVar var) = MonaFormulaVar var
removeForAllFormula (MonaFormulaNeg f) = MonaFormulaNeg (removeForAllFormula f)
removeForAllFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (removeForAllFormula f1) (removeForAllFormula f2)
removeForAllFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (removeForAllFormula f1) (removeForAllFormula f2)
removeForAllFormula (MonaFormulaImpl f1 f2) = MonaFormulaImpl (removeForAllFormula f1) (removeForAllFormula f2)
removeForAllFormula (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (removeForAllFormula f1) (removeForAllFormula f2)
removeForAllFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (removeForAllFormula f)
removeForAllFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (removeForAllFormula f)
removeForAllFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (removeForAllFormula f)
removeForAllFormula (MonaFormulaAll0 vars f) = MonaFormulaNeg $ MonaFormulaEx0 vars (MonaFormulaNeg $ removeForAllFormula f)
removeForAllFormula (MonaFormulaAll1 decl f) = MonaFormulaNeg $ MonaFormulaEx1 decl (MonaFormulaNeg $ removeForAllFormula f)
removeForAllFormula (MonaFormulaAll2 decl f) = MonaFormulaNeg $ MonaFormulaEx2 decl (MonaFormulaNeg $ removeForAllFormula f)


removeForAllDecl :: MonaDeclaration -> MonaDeclaration
removeForAllDecl (MonaDeclFormula f) = MonaDeclFormula $ removeForAllFormula f
removeForAllDecl (MonaDeclVar0 [var]) = MonaDeclVar0 [var]
removeForAllDecl (MonaDeclVar1 [(var,f)]) = MonaDeclVar1 [(var, f >>= return . removeForAllFormula)]
removeForAllDecl (MonaDeclVar2 [(var,f)]) = MonaDeclVar2 [(var, f >>= return . removeForAllFormula)]
removeForAllDecl (MonaDeclPred name params f) = MonaDeclPred name params (removeForAllFormula f)  -- TODO: not considering complex declarations of parameters
removeForAllDecl (MonaDeclMacro name params f) = MonaDeclMacro name params (removeForAllFormula f)
removeForAllDecl (MonaDeclAssert f) = MonaDeclAssert $ removeForAllFormula f
removeForAllDecl (MonaDeclConst atom) = MonaDeclConst atom
removeForAllDecl (MonaDeclLastpos var) = MonaDeclLastpos var
--removeForAllDecl a = a -- TODO: incomplete


removeForAllFile :: MonaFile -> MonaFile
removeForAllFile (MonaFile dom decls) = MonaFile dom (map (removeForAllDecl) decls)


--------------------------------------------------------------------------------------------------------------
-- Part with counting subformulas
--------------------------------------------------------------------------------------------------------------

subFormulas :: MonaFormula -> Int
subFormulas (MonaFormulaAtomic atom) = length $ freeVarsAtom atom
subFormulas (MonaFormulaPredCall name f) = 1
subFormulas (MonaFormulaVar var) = 1
subFormulas (MonaFormulaNeg f) = (subFormulas f)
subFormulas (MonaFormulaDisj f1 f2) = 1 + (subFormulas f1) + (subFormulas f2)
subFormulas (MonaFormulaConj f1 f2) = 1 + (subFormulas f1) + (subFormulas f2)
--subFormulas (MonaFormulaImpl f1 f2) = MonaFormulaImpl (subFormulas f1) (subFormulas f2)
--subFormulas (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (subFormulas f1) (subFormulas f2)
subFormulas (MonaFormulaEx0 vars f) = 1 + (subFormulas f)
subFormulas (MonaFormulaEx1 decl f) = 1 + (subFormulas f)
subFormulas (MonaFormulaEx2 decl f) = 1 + (subFormulas f)

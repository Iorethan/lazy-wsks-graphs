{-|
Module      : MonaFormulaAntiprenex
Description : Mona formulae antiprenexing
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaFormulaAntiprenex where


import Data.List
import Data.Maybe

import AntiprenexConfig
import MonaParser
import MonaFormulaOperation
import MonaFormulaOperationSubst
import MonaFormulaBalance
import MonaFormulaDistr

import qualified Relation as Rel
import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as Lst
import qualified Debug.Trace as Dbg


--------------------------------------------------------------------------------------------------------------
-- Part with antiprenexing
--------------------------------------------------------------------------------------------------------------

-- |Propagate quantifiers to binary formula operator (conjunction, disjunction).
propagateTo :: (MonaFormula -> MonaFormula -> MonaFormula) -> MonaFormula -> MonaFormula -> [QuantifVarChain] -> MonaFormula
propagateTo cons f1 f2 chain = flushQuantifChain remChain (cons (antiprenexFreeVar f1 rem1) (antiprenexFreeVar f2 rem2)) where --TODO: ex1 x where ..., y where ..., --> does not consider free variables in where declaration
  vars1 = freeVarsFormula f1
  vars2 = freeVarsFormula f2
  fv1 = filter (\a -> elem (getChainVarName a) vars1) chain
  fv2 = filter (\a -> elem (getChainVarName a) vars2) chain
  remChain = reverse $ intersect fv1 fv2
  rem1 = fv1 \\ remChain
  rem2 = fv2 \\ remChain


-- |Antiprenexing  with quantifiers distribution and permutation. Given starting
-- chain of quantifiers.
antiprenexFreeVar :: MonaFormula -> [QuantifVarChain] -> MonaFormula
antiprenexFreeVar (MonaFormulaNeg f) chain = flushQuantifChain chain (MonaFormulaNeg $ antiprenexFreeVar f [])
--antiprenexFreeVar (MonaFormulaConj f1 f2) chain = propagateTo (MonaFormulaConj) f1 f2 chain
antiprenexFreeVar f@(MonaFormulaConj f1 f2) chain = case balanceFormulaConfig of
  BalInformed -> balanceFormulaInf (antiprenexFreeVar) f $ reverse chain
  BalInformedSplit -> balanceFormulaInfSplit (antiprenexFreeVar) f $ reverse chain
  BalFullTree -> propagateTo (MonaFormulaConj) f1 f2 chain
antiprenexFreeVar (MonaFormulaDisj f1 f2) chain = MonaFormulaDisj (antiprenexFreeVar f1 chain) (antiprenexFreeVar f2 chain) -- propagateTo (MonaFormulaDisj) f1 f2 chain
antiprenexFreeVar (MonaFormulaEx0 [var] f) chain = MonaFormulaEx0 [var] (antiprenexFreeVar f chain) --antiprenexFreeVar f ((Exists0Chain (var, Nothing)):chain)
antiprenexFreeVar (MonaFormulaEx1 [var] f) chain = antiprenexFreeVar f ((Exists1Chain var):chain)
antiprenexFreeVar (MonaFormulaEx2 [var] f) chain = antiprenexFreeVar f ((Exists2Chain var):chain)
antiprenexFreeVar (MonaFormulaAll0 [var] f) chain = antiprenexFreeVar f ((ForAll0Chain (var, Nothing)):chain)
antiprenexFreeVar (MonaFormulaAll1 [var] f) chain = antiprenexFreeVar f ((ForAll1Chain var):chain)
antiprenexFreeVar (MonaFormulaAll2 [var] f) chain = antiprenexFreeVar f ((ForAll2Chain var):chain)
antiprenexFreeVar atom@(MonaFormulaAtomic _) chain = flushQuantifChain chain atom
antiprenexFreeVar atom@(MonaFormulaPredCall _ _) chain = flushQuantifChain chain atom
antiprenexFreeVar atom@(MonaFormulaVar _) chain = flushQuantifChain chain atom
antiprenexFreeVar a _ = error $ "antiprenexFreeVar: not supported " ++ (show a)


antiprenexEmpty :: MonaFormula -> MonaFormula
antiprenexEmpty f = antiprenexFreeVar f []


antiprenexFormula :: MonaFormula -> MonaFormula
antiprenexFormula = distr . simplifyNegFormula . moveNegToLeavesFormula . antiprenexEmpty . bal  . simplifyNegFormula . moveNegToLeavesFormula . convertToBaseFormula where
  bal = if balanceFormulaConfig == BalFullTree then balanceFormula else id -- balanceFormula
  distr f = (iterate (antiprenexEmpty . distributeFormula []) f) !! distrSteps


convertDecl :: (MonaFormula -> MonaFormula) -> MonaDeclaration -> MonaDeclaration
convertDecl g (MonaDeclFormula f) = MonaDeclFormula $ g f
convertDecl g (MonaDeclVar0 decl) = MonaDeclVar0 decl
convertDecl g (MonaDeclVar1 [(var, decl)]) = MonaDeclVar1 [(var,decl >>= return . g)]
convertDecl g (MonaDeclVar2 [(var, decl)]) = MonaDeclVar2 [(var,decl >>= return . g)]
convertDecl g (MonaDeclPred name params f) = MonaDeclPred name params (g f) -- TODO: params are not converted
convertDecl g (MonaDeclMacro name params f) = MonaDeclMacro name params (g f)
convertDecl g (MonaDeclAssert f) = MonaDeclAssert $ g f
convertDecl g (MonaDeclConst atom) = MonaDeclConst atom -- TODO: antiprenexing is skipped
convertDecl g (MonaDeclLastpos var) = MonaDeclLastpos var
--convertDecl _ a = a -- TODO: incomplete

antiprenexFile :: MonaFile -> MonaFile
antiprenexFile (MonaFile dom decls) = MonaFile dom $ map (convertDecl (antiprenexFormula)) decls


--------------------------------------------------------------------------------------------------------------
-- Part with the formula simplification
--------------------------------------------------------------------------------------------------------------

-- |Simplify formula: balance formula, move negations to leaves, simplify
-- formula (without antiprenexing).
simplifyFormula :: MonaFormula -> MonaFormula
simplifyFormula = simplifyNegFormula . moveNegToLeavesFormula . balanceFormula . simplifyNegFormula . moveNegToLeavesFormula . convertToBaseFormula


-- |Simplify MONA file: balance formula, move negations to leaves, simplify
-- formula (without antiprenexing).
simplifyFile :: MonaFile -> MonaFile
simplifyFile (MonaFile dom decls) = MonaFile dom $ map (convertDecl (simplifyFormula)) decls


--------------------------------------------------------------------------------------------------------------
-- Part with a conversion to formula without implications and equivalences.
--------------------------------------------------------------------------------------------------------------

convertToBaseAtom :: MonaAtom -> MonaFormula
convertToBaseAtom (MonaAtomNeq t1 t2) = MonaFormulaNeg $ MonaFormulaAtomic $ (MonaAtomEq t1 t2)
convertToBaseAtom atom = MonaFormulaAtomic atom


convertToBaseFormula :: MonaFormula -> MonaFormula
convertToBaseFormula (MonaFormulaAtomic atom) = convertToBaseAtom atom
convertToBaseFormula f@(MonaFormulaPredCall _ _) = f
convertToBaseFormula (MonaFormulaVar var) = MonaFormulaVar var
convertToBaseFormula (MonaFormulaNeg f) = MonaFormulaNeg (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaImpl f1 f2) = MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaEquiv f1 f2) = MonaFormulaConj (MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f1) (convertToBaseFormula f2)) (MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f2) (convertToBaseFormula f1))
convertToBaseFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (convertToBaseFormula f)




--------------------------------------------------------------------------------------------------------------
-- Part with negation simplifying.
--------------------------------------------------------------------------------------------------------------

moveNegToLeavesFormula :: MonaFormula -> MonaFormula
moveNegToLeavesFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
moveNegToLeavesFormula f@(MonaFormulaPredCall _ _) = f
moveNegToLeavesFormula (MonaFormulaVar var) = MonaFormulaVar var
moveNegToLeavesFormula (MonaFormulaNeg (MonaFormulaConj f1 f2)) = moveNegToLeavesFormula $ MonaFormulaDisj (MonaFormulaNeg f1) (MonaFormulaNeg f2)
moveNegToLeavesFormula (MonaFormulaNeg (MonaFormulaDisj f1 f2)) = moveNegToLeavesFormula $ MonaFormulaConj (MonaFormulaNeg f1) (MonaFormulaNeg f2)
moveNegToLeavesFormula (MonaFormulaNeg f) = MonaFormulaNeg (moveNegToLeavesFormula f)
moveNegToLeavesFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (moveNegToLeavesFormula f1) (moveNegToLeavesFormula f2)
moveNegToLeavesFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (moveNegToLeavesFormula f1) (moveNegToLeavesFormula f2)
moveNegToLeavesFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (moveNegToLeavesFormula f)
moveNegToLeavesFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (moveNegToLeavesFormula f)
moveNegToLeavesFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (moveNegToLeavesFormula f)


simplifyNegFormula :: MonaFormula -> MonaFormula
simplifyNegFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
simplifyNegFormula f@(MonaFormulaPredCall _ _) = f
simplifyNegFormula (MonaFormulaVar var) = MonaFormulaVar var
simplifyNegFormula (MonaFormulaNeg (MonaFormulaNeg f)) = simplifyNegFormula f
simplifyNegFormula (MonaFormulaNeg f) = MonaFormulaNeg (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (simplifyNegFormula f1) (simplifyNegFormula f2)
simplifyNegFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (simplifyNegFormula f1) (simplifyNegFormula f2)
simplifyNegFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (simplifyNegFormula f)

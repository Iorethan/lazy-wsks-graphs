{-|
Module      : FormulaOperation
Description : More involved operations for logic formulae
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module FormulaOperation (
  antiprenex
  , simplifyFormula
  , balanceFormula
  , replaceSubformulas
) where

import Logic
import Data.List
import Data.Monoid
import qualified Data.Foldable as Fd
import qualified Data.Semigroup as S

-- Chain of quantifiers
data QuantifChain a =
  EmptyChain
  | ForAllChain a
  | ExistsChain a


-- Chain of quantifiers with variables
type QuantifVarChain = QuantifChain [Var]


-- |Definition of functor of QuantifChain
instance Functor QuantifChain where
  fmap f EmptyChain = EmptyChain
  fmap f (ExistsChain val) = ExistsChain (f val)
  fmap f (ForAllChain val) = ForAllChain (f val)


-- |Definition of applicative functor of QuantifChain
instance Applicative QuantifChain where
  pure = ExistsChain
  EmptyChain <*> _ = EmptyChain
  (ExistsChain f) <*> st = fmap f st
  (ForAllChain f) <*> st = fmap f st


-- |Definition of Semigroup of QuantifChain
instance (Monoid a) => S.Semigroup (QuantifChain a) where
  (<>) = mappend


-- |Definition of monoid of QuantifChain
instance (Monoid a) => Monoid (QuantifChain a) where
  mempty = EmptyChain
  mappend EmptyChain s = s
  mappend s EmptyChain = s
  mappend (ForAllChain v1) (ForAllChain v2) = ForAllChain (mappend v1 v2)
  mappend (ExistsChain v1) (ExistsChain v2) = ExistsChain (mappend v1 v2)


--------------------------------------------------------------------------------------------------------------
-- Part with antiprenexing
--------------------------------------------------------------------------------------------------------------

-- |Flush (unfold) a chain of existential quantifiers. Given list of variables,
-- it expands to a chain of existential quatifiers, on the most nested level with
-- formula f.
flushQuantifChain :: QuantifVarChain -> Formula -> Formula
flushQuantifChain EmptyChain f = f
flushQuantifChain (ForAllChain xs) f = Fd.foldr (ForAll) f xs
flushQuantifChain (ExistsChain xs) f = Fd.foldr (Exists) f xs


-- |Propagate quantifiers to binary formula operator (conjunction, disjunction).
propagateTo :: (Formula -> Formula -> Formula) -> Formula -> Formula -> QuantifVarChain -> Formula
propagateTo cons f1 f2 chain = flushQuantifChain remChain (cons (antiprenexFreeVar f1 rem1) (antiprenexFreeVar f2 rem2)) where
  fv1 = fmap (intersect (freeVars f1)) chain
  fv2 = fmap (intersect (freeVars f2)) chain
  remChain = (intersect) <$> fv1 <*> fv2
  rem1 = (\\) <$> fv1 <*> remChain
  rem2 = (\\) <$> fv2 <*> remChain


-- |Antiprenexing  with quantifiers distribution and permutation. Given starting
-- chain of quantifiers.
antiprenexFreeVar :: Formula -> QuantifVarChain -> Formula
antiprenexFreeVar (Neg f) chain = flushQuantifChain chain (Neg $ antiprenexFreeVar f EmptyChain)
antiprenexFreeVar (Conj f1 f2) chain = propagateTo (Conj) f1 f2 chain
antiprenexFreeVar (Disj f1 f2) chain = propagateTo (Disj) f1 f2 chain
antiprenexFreeVar (Exists var f) chain@(ForAllChain c) = flushQuantifChain chain (antiprenexFreeVar f (ExistsChain [var]))
antiprenexFreeVar (Exists var f) EmptyChain = antiprenexFreeVar f ((:) <$> (ExistsChain var) <*> (ExistsChain []))
antiprenexFreeVar (Exists var f) chain = antiprenexFreeVar f ((:) <$> (ForAllChain var) <*> chain)
antiprenexFreeVar (ForAll var f) chain@(ExistsChain c) = flushQuantifChain chain (antiprenexFreeVar f (ForAllChain [var]))
antiprenexFreeVar (ForAll var f) EmptyChain = antiprenexFreeVar f ((:) <$> (ForAllChain var) <*> (ForAllChain []))
antiprenexFreeVar (ForAll var f) chain = antiprenexFreeVar f ((:) <$> (ForAllChain var) <*> chain)
antiprenexFreeVar f@(FormulaAtomic _) chain = flushQuantifChain chain f


-- |Antiprenexing.
antiprenex :: Formula -> Formula
antiprenex f = antiprenexFreeVar f EmptyChain


--------------------------------------------------------------------------------------------------------------
-- Part with negation propagation
--------------------------------------------------------------------------------------------------------------

-- |Simplyfication of a given formula.
simplifyFormula :: Formula -> Formula
simplifyFormula = moveNegToLeaves . simplifyNeg . moveNegToLeaves


-- |Simplification of double negation.
simplifyNeg :: Formula -> Formula
simplifyNeg (Neg (Neg f)) = simplifyNeg f
simplifyNeg f@(FormulaAtomic _) = f
simplifyNeg (Disj f1 f2) = Disj (simplifyNeg f1) (simplifyNeg f2)
simplifyNeg (Conj f1 f2) = Conj (simplifyNeg f1) (simplifyNeg f2)
simplifyNeg (Neg f) = Neg $ simplifyNeg f
simplifyNeg (ForAll var f) = ForAll var (simplifyNeg f)
simplifyNeg (Exists var f) = Exists var (simplifyNeg f)


-- |Move negation to the formula leaves.
moveNegToLeaves :: Formula -> Formula
moveNegToLeaves (Neg (Conj f1 f2)) = moveNegToLeaves $ Disj (Neg f1) (Neg f2)
moveNegToLeaves (Neg (Disj f1 f2)) = moveNegToLeaves $ Conj (Neg f1) (Neg f2)
moveNegToLeaves (Disj f1 f2) = Disj (moveNegToLeaves f1) (moveNegToLeaves f2)
moveNegToLeaves (Conj f1 f2) = Conj (moveNegToLeaves f1) (moveNegToLeaves f2)
moveNegToLeaves (Neg f) = Neg $ moveNegToLeaves f
moveNegToLeaves (ForAll var f) = ForAll var (moveNegToLeaves f)
moveNegToLeaves (Exists var f) = Exists var (moveNegToLeaves f)
moveNegToLeaves f@(FormulaAtomic _) = f


--------------------------------------------------------------------------------------------------------------
-- Part with conjunction and disjunction balancing
--------------------------------------------------------------------------------------------------------------

-- |Balance conjunctions and disjunctions in formula.
balanceFormula :: Formula -> Formula
balanceFormula f@(Conj _ _) = rebuildFormula (Conj) $ map (balanceFormula) (getConjList f)
balanceFormula f@(Disj _ _) = rebuildFormula (Disj) $ map (balanceFormula) (getDisjList f)
balanceFormula (Neg f) = Neg $ balanceFormula f
balanceFormula (ForAll var f) = ForAll var (balanceFormula f)
balanceFormula (Exists var f) = Exists var (balanceFormula f)
balanceFormula f@(FormulaAtomic _) = f


-- |Rebuild formula from a list of subformulae using given formula constructor.
-- Builds a balanced tree from the leaves in the list.
rebuildFormula :: (Formula -> Formula -> Formula) -> [Formula] -> Formula
rebuildFormula _ [f] = f
rebuildFormula con xs = con (rebuildFormula con h) (rebuildFormula con t) where
  m = (length xs) `div` 2
  h = take m xs
  t = drop m xs


-- |Get all conjunctions that are on the top of a given formula.
getConjList :: Formula -> [Formula]
getConjList (Conj f1 f2) = (getConjList f1) ++ (getConjList f2)
getConjList v = [v]


-- |Get all disjunctions that are on the top of a given formula.
getDisjList :: Formula -> [Formula]
getDisjList (Disj f1 f2) = (getDisjList f1) ++ (getDisjList f2)
getDisjList v = [v]


--------------------------------------------------------------------------------------------------------------
-- Part with formula replacing (according to propositional logic equivalences,
-- first-, second-order logic equivalences)
--------------------------------------------------------------------------------------------------------------

-- |Recursively replace formula for equivalent formulas.
replaceSubformulas :: Formula -> Formula
replaceSubformulas (Disj f1 f2) = Disj (replaceSubformulas f1) (replaceSubformulas f2)
replaceSubformulas (Conj f1 f2) =  Conj (replaceSubformulas f1) (replaceSubformulas f2)
replaceSubformulas (Neg f) = replaceSubformula (Neg (replaceSubformulas f))
replaceSubformulas (ForAll var f) = ForAll var (replaceSubformulas f)
replaceSubformulas (Exists var f) = Exists var (replaceSubformulas f)
replaceSubformulas f@(FormulaAtomic _) = f


-- |Replace a given formula for an equivalent formula.
replaceSubformula :: Formula -> Formula
--replaceSubformula (Conj (FormulaAtomic (Subseteq v1 v2)) (FormulaAtomic (Neq v3 v4)))
--  | (v1 == v3) && (v2 == v4) = FormulaAtomic (Subset v1 v2)
replaceSubformula (Neg (FormulaAtomic (Subseteq v1 v2))) = FormulaAtomic (Subset v2 v1)
replaceSubformula t = t

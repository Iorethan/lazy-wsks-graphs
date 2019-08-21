{-|
Module      : StrictDecisionProcedure
Description : Strict (non lazy) decision procedure for WS2S.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module StrictDecisionProcedure (
   isValid
   , formula2Terms
   , unwindFixpoints
) where


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified ComTreeAutomaton as CTA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp

import BaseDecisionProcedure
import BasicAutomata

import qualified Debug.Trace as Dbg


-- |Ominus for a set of symbols. Defined only for a term of the form (TSet a).
ominusSymbols :: Term -> Set.Set Alp.Symbol -> Term
ominusSymbols (TSet tset) sset = TSet $ Set.fromList [minusSymbol t1 t2 s | s <- Set.toList sset, t1 <- Set.toList tset, t2 <- Set.toList tset]
ominusSymbols _ _ = error "ominusSymbols: Ominus is defined only on a set of terms"


-- |Fixpoint minus computation of the given term and a set of symbols.
fixpointComp :: Term -> Set.Set Alp.Symbol -> Term
fixpointComp term@(TSet tset) sset | Dbg.trace ("fixpointComp " ++ show (term)) False = undefined
fixpointComp term@(TSet tset) sset =
   case ominusSymbols term sset of
      TSet modifset ->
         if isSubsumedStrict (TSet modifset) term then term
         else fixpointComp (removeSet $ TSet $ Set.union modifset tset) sset
      _ -> error "fixpointComp: Ominus is defined only on a set of terms"


-- |Unwind fixpoints into sets of terms (corresponding to applying all fixpoints).
unwindFixpoints :: Term -> Term
unwindFixpoints t@(TStates _ _ _) = t
unwindFixpoints (TMinusClosure t _ sset) = fixpointComp (unwindFixpoints t) sset
unwindFixpoints (TUnion t1 t2) = TUnion (unwindFixpoints t1) (unwindFixpoints t2)
unwindFixpoints (TIntersect t1 t2) = TIntersect (unwindFixpoints t1) (unwindFixpoints t2)
unwindFixpoints (TCompl t) = TCompl (unwindFixpoints t)
unwindFixpoints (TProj var t) = TProj var (TSet $ Set.fromList [unwindFixpoints t])
unwindFixpoints (TSet tset) = TSet $ Set.fromList [unwindFixpoints t | t <- Set.toList tset]
unwindFixpoints t = error ("unwindFixpoints: Unwind is not defined for pair and minus terms" ++ (show t))


-- |Is first term subsumed by the second one?
isSubsumedStrict :: Term -> Term -> Bool
isSubsumedStrict (TUnion t1 t2) (TUnion t3 t4) = (isSubsumedStrict t1 t3) && (isSubsumedStrict t2 t4)
isSubsumedStrict (TIntersect t1 t2) (TIntersect t3 t4) = (isSubsumedStrict t1 t3) && (isSubsumedStrict t2 t4)
isSubsumedStrict (TCompl t1) (TCompl t2) = isSubsumedStrict t2 t1
isSubsumedStrict (TProj v1 t1) (TProj v2 t2)
  | v1 == v2 = isSubsumedStrict t1 t2
  | otherwise = False
isSubsumedStrict (TSet tset1) (TSet tset2) = foldr (&&) True ((Set.toList tset1) >>= (\a -> return $ any (isSubsumedStrict a) lst))
  where
    lst = Set.toList tset2
isSubsumedStrict (TStates aut1 var1 st1) (TStates aut2 var2 st2) = (var1 == var2) && (subsetSetStates st1 st2)
isSubsumedStrict _ _ = False


-- |Test whether bottom is in the language of the term.
botIn :: Term -> Bool
botIn (TUnion t1 t2) = (botIn t1) || (botIn t2)
botIn (TIntersect t1 t2) = (botIn t1) && (botIn t2)
botIn (TCompl t) = not $ botIn t
botIn (TSet tset) =
   foldr gather False (Set.toList tset) where
      gather t b = (botIn t) || b
botIn (TProj _ t) = botIn t
botIn (TStates aut _ st) =  CTA.containsRoot aut st --(Set.intersection (TA.roots aut) st) /= Set.empty
botIn _ = error "botIn: Bottom membership is not defined"


-- |Convert formula to term representation.
formula2Terms :: Lo.Formula -> Term
formula2Terms f = joinSetTerm $ formula2TermsVars Map.empty f []


-- |Decide whether given ground formula is valid (strict approach).
isValid :: Lo.Formula -> Either Bool String
isValid f
   | Lo.freeVars f == [] = Left $ botIn $ unwindFixpoints $ formula2Terms $ Lo.removeForAll f
   | otherwise = Right "isValid: Only ground formula is allowed"

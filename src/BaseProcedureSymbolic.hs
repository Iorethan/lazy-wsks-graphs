{-|
Module      : BaseProcedureSymbolic
Description : Auxiliary functions for symbolic handling with symbols and
              transition relation (BDD based approach) in WS2S decision
              procedure.
Author      : Vojtech Havlena, November 2018
License     : GPL-3
-}

{-# OPTIONS_GHC -XTypeOperators #-}

module BaseProcedureSymbolic where

import Data.Maybe
import qualified Data.Set as Set
import qualified Control.Monad.Fix as Fix
import qualified Data.Tuple as Tuple
import qualified Data.Map as Map
import qualified Data.List as List
import qualified TreeAutomaton as TA
import qualified ComTreeAutomaton as CTA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp

import BaseDecisionProcedure
import Control.Applicative

import qualified Debug.Trace as Dbg

--------------------------------------------------------------------------------------------------------------
-- Part with the Literal type and symbolic term
--------------------------------------------------------------------------------------------------------------

-- Note that set of literals represent clause (conjunction of literals).

data Literal =
  Var String
  | Not String
  deriving (Eq, Ord, Show)

-- |Set of literals describing possible assigments to vars (=this define symbols)
-- and corresponding term.
type SymTerm = (Set.Set Literal, Term)


--------------------------------------------------------------------------------------------------------------
-- Part with the Minus symbols symbolically (pre on the terms)
--------------------------------------------------------------------------------------------------------------

-- |Join (union) two terms.
joinTerm :: Term -> Term -> Term
joinTerm (TSet t1) (TSet t2) = TSet $ Set.union t1 t2
joinTerm (TProj v1 t1) (TProj v2 t2) = TProj v1 (joinTerm t1 t2)
joinTerm t1 t2 = error $ "joinTerm: structure"


-- |Minus symbolically (symbolic transition function) over a set of symbols.
minusSymbolSym :: Term -> Term -> Set.Set Alp.Symbol -> [SymTerm]
minusSymbolSym t1@(TStates aut1 var1 st1) t2@(TStates aut2 var2 st2) sym =
  lst where
    lst = [(convSymToFle s, minusSymbol t1 t2 s) | s <- unsyms]
    unsyms = Set.toList $ Alp.unwindSymbolsX $ Alp.cylindrifySymbols var1 sym
minusSymbolSym (TIntersect t1 t2) (TIntersect t3 t4) sym = satTermProductWith l1 l2 (TIntersect) -- removed List.nub
  where
    l1 = minusSymbolSym t1 t3 sym
    l2 = minusSymbolSym t2 t4 sym
minusSymbolSym (TUnion t1 t2) (TUnion t3 t4) sym = satTermProductWith l1 l2 (TUnion)
  where
    l1 = minusSymbolSym t1 t3 sym
    l2 = minusSymbolSym t2 t4 sym
minusSymbolSym (TCompl t1) (TCompl t2) sym = map g (minusSymbolSym t1 t2 sym)
  where
    g (a,b) = (a, TCompl b)
minusSymbolSym (TProj v1 t1) (TProj v2 t2) sym
  | v1 /= v2 = error "minusSymbolSym: Projection variables do not match"
  | v1 == v2 = unifySymTerm $ map (g) l
    where
      l = minusSymbolSym t1 t2 (Alp.projSymbolsX sym v1)
      g (f, t) = (Set.delete (Not v1) (Set.delete (Var v1) f), TProj v1 t)
minusSymbolSym (TSet tset1) (TSet tset2) sym = ret where
  cr = [minusSymbolSym t1 t2 sym | t1 <- Set.toList tset1, t2 <- Set.toList tset2]
  cr' = map (\(a,b) -> (a, TSet $ Set.singleton b)) $ concat cr -- foldr (++) []
  ret = unifySymTerm cr'


-- |Unify symbolic terms. Symbolic terms having equal the literal part will be
-- merged together using the fuction joinTerm.
unifySymTerm :: [SymTerm] -> [SymTerm]
unifySymTerm =  Map.toList . Map.fromListWith (joinTerm)


-- |Unify symbolic terms that have equivalent term part and differs on value
-- of one variable in literal part.
unifyEqualSymTerm :: [SymTerm] -> [SymTerm]
unifyEqualSymTerm l = concat $ map (f) lst
  where
    lst :: [[SymTerm]]
    lst = List.groupBy ((==) `comp` (snd)) $ List.sortBy ((compare) `comp` (snd)) l
    f :: [SymTerm] -> [SymTerm]
    f l = Fix.fix (r) l
    r re v = if v' == v then v else re v' where
      v' = h v
    g xs ys = liftA2 (,) xs ys
    h :: [SymTerm] -> [SymTerm]
    h lst = case List.find (differsInVar) $ g lst lst of
      (Just (x,y)) -> (Set.intersection (fst x) (fst y), snd y):lst' where
        lst' =  lst List.\\ [x,y]
      Nothing -> lst


-- removeRedundantLiterals :: Set.Set Literal -> Set.Set Literal
-- removeRedundantLiterals set = newSet where
--   vars = Set.toList $ proj set
--   parRem = vars >>= \(Var x) -> let singX = Set.fromList [Var x, Not x] in if Set.isSubsetOf (singX) set then return $ set Set.\\ (singX) else [] where
--     sing x = Set.fromList [Var x, Not x]
--   newSet = foldr (Set.intersection) set parRem


-- |Function composition for f: a->a->b and g: c->a do f(g(x), g(y)).
comp :: (a -> a -> b) -> (c -> a) -> (c -> c -> b)
comp f g = \x y -> f (g x) (g y)


-- |Does literal parts of two symbolic terms differ only in one variable?
differsInVar :: (SymTerm, SymTerm) -> Bool
differsInVar (sym1, sym2) = ((Set.size $ fst sym1) == (Set.size $ fst sym2))
  && (Set.size $ Set.intersection (fst sym1) (fst sym2)) == (Set.size $ fst sym1) - 1


-- |Forget the literal part of the symbolic term yielding the ordinary term.
forgetFle :: [SymTerm] -> [Term]
forgetFle = map (snd)


-- |Convert symbol to clause (set of literals).
convSymToFle :: Alp.Symbol -> Set.Set Literal
convSymToFle (lst, var) = Set.fromList $ zipWith (fmerge) lst (Set.toAscList var)
  where
    fmerge sym var
      | sym == '0' = Not var
      | sym == '1' = Var var
      | otherwise = error $ "convSymToFle: unrecognized symbol"


-- |Partition the set of literals into two sets -- sat literals and unsat literals.
getSatUnsat :: Set.Set Literal -> (Set.Set Literal, Set.Set Literal)
getSatUnsat s = (tr, fs) where
  (tr, fs) = Set.partition g s
  --sat = Set.filter g s
  g (Var v) = True
  g _ = False


proj = Set.mapMonotonic (fn) where -- Replaced with Set.map (fn)
  fn t@(Var v) = t
  fn (Not v) = Var v


-- |Are two clauses = set of literals satisfiable?
isSatConjSet :: Set.Set Literal -> Set.Set Literal -> Bool
isSatConjSet s1 s2 = (Set.disjoint sat1 (proj unsat2)) && (Set.disjoint sat2 (proj unsat1)) where
  (sat1, unsat1) = getSatUnsat s1
  (sat2, unsat2) = getSatUnsat s2


-- |Cartesian product of two lists of symbolic terms with a given constructor
-- (only pairs of satisfiable sym terms are considered).
satTermProductWith :: [SymTerm] -> [SymTerm] -> (Term -> Term -> Term) -> [SymTerm]
satTermProductWith l1 l2 cons = [(Set.union f1 f2, cons t1 t2) | (f1, t1) <- l1, (f2, t2) <- l2, isSatConjSet f1 f2]


--------------------------------------------------------------------------------------------------------------
-- Part with debug functions
--------------------------------------------------------------------------------------------------------------

test1 = minusSymbolSym t3 t4 (Set.singleton ("X", Set.fromList ["Y"]) ) where
  t1 = atom2Terms Map.empty (Lo.Subseteq "X" "Y")
  t2 = atom2Terms Map.empty (Lo.Subseteq "X" "Y")
  t3 = TProj "X" t1
  t4 = TProj "X" t2


test2 =unifyEqualSymTerm $ minusSymbolSym t1 t2 (Alp.unwindSymbolX ("XX", Set.fromList ["X","Y"])) where
  t1 = atom2Terms Map.empty (Lo.Cat2 "X" "Y")
  t2 = atom2Terms Map.empty (Lo.Cat2 "X" "Y")
  s1 = (Set.fromList [Var "X", Not "Y"], t1)
  s2 = (Set.fromList [Var "X", Var "Y"], t1)
  s3 = (Set.fromList [Var "X", Not "Y"], t2)


test3 = minusSymbolSym t1 t2 (Alp.unwindSymbolX ("XX", Set.fromList ["X","Y"])) where
  t1 = atom2Terms Map.empty (Lo.Cat2 "X" "Y")
  t2 = atom2Terms Map.empty (Lo.Cat2 "X" "Y")
  s1 = (Set.fromList [Var "X", Not "Y"], t1)
  s2 = (Set.fromList [Var "X", Var "Y"], t1)
  s3 = (Set.fromList [Var "X", Not "Y"], t2)

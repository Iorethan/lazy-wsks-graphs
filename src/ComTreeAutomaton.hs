{-|
Module      : ComTreeAutomaton
Description : Compound tree automata (composition of tree automata using boolean
              connectives and, or).
Author      : Vojtech Havlena, November 2018
License     : GPL-3
-}

module ComTreeAutomaton (
   preCom
   , ComState(..)
   , stateSize
   , ComTA(..)
   , containsRoot
) where


import Data.List
import TreeAutomaton
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified AuxFunctions as Aux
import qualified Alphabet as Alp

-- |Compbound state of TA
data ComState a =
  Sink
  | SetSt (Set.Set a)
  | State a
  | ConjSt (ComState a) (ComState a)
  | DisjSt (ComState a) (ComState a)
  deriving (Eq, Ord)


-- |Compbound TA (using connectives conj, disj)
data ComTA a b =
  Base (BATreeAutomaton a b) [Alp.Variable]
  | ConjTA (ComTA a b) (ComTA a b)
  | DisjTA (ComTA a b) (ComTA a b)
--  deriving (Eq, Ord)


instance (Show a) => Show (ComState a) where
  show Sink = "#"
  show (SetSt set) = Aux.prArr "," (Set.toList set)
  show (State s) = show s
  show (ConjSt s1 s2) = show s1 ++ "&" ++ show s2
  show (DisjSt s1 s2) = show s1 ++ "+" ++ show s2


instance (Show a, Show b) => Show (ComTA a b) where
  show (Base a _) = show a
  show (ConjTA a1 a2) = show a1 ++ "&" ++ show a2
  show (DisjTA a1 a2) = show a1 ++ "+" ++ show a2


instance (Eq m, Eq n) => Eq (ComTA m n) where
   a1 == a2 = True -- DIRTY PERFORMANCE HACK!!!!

-- |Syntax ordering of two tree automata.
instance (Ord m, Ord n) => Ord (ComTA m n) where
   a1 <= a2 = True -- DIRTY PERFORMANCE HACK!!!!


stateSize :: ComState a -> Int
stateSize (SetSt s) = Set.size s
stateSize _ = 1

--------------------------------------------------------------------------------------------------------------
-- Part with the pre function on compound tree automata
--------------------------------------------------------------------------------------------------------------

-- |Pre (Up) of a set of states wrt given symbol. First param is projection function
-- (modifies symbol to certain automaton).
preCom :: (Ord a, Ord b) => ([Alp.Variable] -> b -> b) -> ComTA a b -> [Set.Set (ComState a)] -> b -> Set.Set (ComState a)
preCom proj aut st sym =
  foldr (Set.union) Set.empty [preComEx proj aut s1 s2 sym | [s1, s2] <- Aux.crossProd st ]


-- |Pre (Up) of two states wrt given symbol. First param is projection function
-- (modifies symbol to certain automaton).
preComEx :: (Ord a, Ord b) => ([Alp.Variable] -> b -> b) -> ComTA a b -> ComState a -> ComState a -> b -> Set.Set (ComState a)
preComEx proj (ConjTA aut1 aut2) (ConjSt s1 s2) (ConjSt u1 u2) sym = Set.fromList [ConjSt a b | a <- a1, b <- a2]
  where
    a1 = Set.toList $ preComEx proj aut1 s1 u1 sym
    a2 = Set.toList $ preComEx proj aut2 s2 u2 sym
preComEx proj (DisjTA aut1 aut2) (DisjSt s1 s2) (DisjSt u1 u2) sym = Set.fromList [DisjSt a b | a <- a1, b <- a2]
  where
    a1 = Set.toList $ preComEx proj aut1 s1 u1 sym
    a2 = Set.toList $ preComEx proj aut2 s2 u2 sym
preComEx _ _ (State q) Sink _ = Set.singleton Sink
preComEx _ _ Sink (State q) _ = Set.singleton Sink
preComEx _ _ Sink Sink _ = Set.singleton Sink
preComEx proj (Base (BATreeAutomaton _ _ _ tr) vars) (State q) (State r) sym =
    if null step then Set.singleton Sink
    else Set.map (State) step where
      step = Map.findWithDefault (Set.empty) ([q,r], (proj vars sym)) tr
preComEx proj (Base (BATreeAutomaton _ _ _ tr) vars) (SetSt s1) (SetSt s2) sym =
  Set.singleton $ SetSt $ foldr (Set.union) Set.empty [Map.findWithDefault Set.empty ([q1, q2],sym') tr |
    q1 <- Set.toList s1, q2 <- Set.toList s2 ] where
      sym' = proj vars sym


-- |Is a given compbound state root state in given compound TA?
isRoot :: (Ord a, Ord b) => ComTA a b -> ComState a -> Bool
isRoot _ Sink = False
isRoot (Base aut _) (State st) = Set.member st (roots aut)
isRoot (ConjTA aut1 aut2) (ConjSt st1 st2) = (isRoot aut1 st1) && (isRoot aut2 st2)
isRoot (DisjTA aut1 aut2) (DisjSt st1 st2) = (isRoot aut1 st1) || (isRoot aut2 st2)
isRoot (Base aut _) (SetSt st) = not $ null $ Set.intersection st (roots aut)


-- |For a set of compbound states check whether in the set is a root state.
containsRoot :: (Ord a, Ord b) => ComTA a b -> Set.Set (ComState a) -> Bool
containsRoot aut st = any (isRoot aut) (Set.toList st)

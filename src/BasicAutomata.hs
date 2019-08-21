{-|
Module      : BasicAutomata
Description : Basic tree automata used for WS2S decision procedure.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module BasicAutomata where


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified TreeAutomaton as TA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp

import qualified Debug.Trace as Dbg

type State = Int
type WS2STreeAut = TA.BATreeAutomaton State Alp.Symbol

--------------------------------------------------------------------------------------------------------------
-- Part with the definitions of basic tree automata
--------------------------------------------------------------------------------------------------------------

singSymbol s x = ([s], Set.fromList [x])
pairSymbol v1 v2 x1 x2 = if x1 <= x2 then ([v1,v2], Set.fromList [x1, x2])
                         else ([v2,v1], Set.fromList [x1, x2])


-- |Tree automaton for an atomic predicate Sing(X).
singAut :: Lo.Var -> WS2STreeAut
singAut var = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [1])
   (Map.fromList[ (([1,0], (singSymbol '0' var)), Set.fromList [0])
      , (([1,1], (singSymbol '1' var)), Set.fromList [0])
      , (([0,1], (singSymbol '0' var)), Set.fromList [0])
      , (([1,1], (singSymbol '0' var)), Set.fromList [1])])


-- |Tree automaton for an atomic predicate X=Y.0.
cat1Aut :: Lo.Var -> Lo.Var -> WS2STreeAut
cat1Aut v1 v2 = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [0])
   (Map.fromList[ (([0,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '1' '0' v1 v2)), Set.fromList [1])
      , (([1,0], (pairSymbol '1' '1' v1 v2)), Set.fromList [1])
      , (([1,0], (pairSymbol '0' '1' v1 v2)), Set.fromList [0])])


-- |Tree automaton for an atomic predicate X=Y.1.
cat2Aut :: Lo.Var -> Lo.Var -> WS2STreeAut
cat2Aut v1 v2 = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [0])
   (Map.fromList[ (([0,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '1' '0' v1 v2)), Set.fromList [1])
      , (([0,1], (pairSymbol '1' '1' v1 v2)), Set.fromList [1])
      , (([0,1], (pairSymbol '0' '1' v1 v2)), Set.fromList [0])])


-- |Tree automaton for an atomic predicate x \in Y.
inAut :: Lo.Var -> Lo.Var -> WS2STreeAut
inAut v1 v2 = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [1])
    (Map.fromList[ (([0,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [0])
       , (([0,0], (pairSymbol '0' '1' v1 v2)), Set.fromList [0])
       , (([1,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [1])
       , (([0,1], (pairSymbol '0' '0' v1 v2)), Set.fromList [1])
       , (([1,1], (pairSymbol '0' '0' v1 v2)), Set.fromList [1])
       , (([0,0], (pairSymbol '1' '1' v1 v2)), Set.fromList [1])])


-- |Tree automaton for atomic predicate X subseteq Y
subseteqAut :: Lo.Var -> Lo.Var -> WS2STreeAut
subseteqAut v1 v2 = TA.BATreeAutomaton (Set.fromList [0,1]) (Set.fromList [0]) (Set.fromList [0])
   (Map.fromList[ (([0,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '0' '1' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '1' '1' v1 v2)), Set.fromList [0])
      --, (([0,0], (pairSymbol '1' '0' v1 v2)), Set.fromList [1])
      --, (([1,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [1])
      --, (([1,0], (pairSymbol '0' '1' v1 v2)), Set.fromList [1])
      --, (([1,0], (pairSymbol '1' '0' v1 v2)), Set.fromList [1])
      --, (([1,0], (pairSymbol '1' '1' v1 v2)), Set.fromList [1])
      -- , (([1,1], (pairSymbol '0' '0' v1 v2)), Set.fromList [1])
      -- , (([1,1], (pairSymbol '0' '1' v1 v2)), Set.fromList [1])
      -- , (([1,1], (pairSymbol '1' '0' v1 v2)), Set.fromList [1])
      -- , (([1,1], (pairSymbol '1' '1' v1 v2)), Set.fromList [1])
      -- , (([0,1], (pairSymbol '0' '0' v1 v2)), Set.fromList [1])
      --, (([0,1], (pairSymbol '0' '1' v1 v2)), Set.fromList [1])
      --, (([0,1], (pairSymbol '1' '0' v1 v2)), Set.fromList [1])
      --, (([0,1], (pairSymbol '1' '1' v1 v2)), Set.fromList [1])
      ])


-- |Tree automaton for atomic predicate X subset Y
subsetAut :: Lo.Var -> Lo.Var -> WS2STreeAut
subsetAut v1 v2 = TA.BATreeAutomaton (Set.fromList [0,1]) (Set.fromList [0]) (Set.fromList [1])
   (Map.fromList[ (([0,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '1' '1' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '0' '1' v1 v2)), Set.fromList [0])
      , (([1,1], (pairSymbol '0' '1' v1 v2)), Set.fromList [0])
      , (([1,1], (pairSymbol '1' '1' v1 v2)), Set.fromList [1])
      , (([1,1], (pairSymbol '0' '0' v1 v2)), Set.fromList [1])])


-- |Tree automaton for atomic predicate X = Y
eqAut :: Lo.Var -> Lo.Var -> WS2STreeAut
eqAut v1 v2 = TA.BATreeAutomaton (Set.fromList [0]) (Set.fromList [0]) (Set.fromList [0])
   (Map.fromList[ (([0,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '1' '1' v1 v2)), Set.fromList [0])])


-- |Tree automaton for atomic predicat X=eps
epsAut :: Lo.Var -> WS2STreeAut
epsAut var = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [1])
   (Map.fromList[ (([1,1], (singSymbol '1' var)), Set.fromList [0])
      , (([1,1], (singSymbol '0' var)), Set.fromList [1])])


-- |Tree automaton for first order const term of the form z=0.1....
treeConstAut :: Lo.Var -> [Integer] -> WS2STreeAut
treeConstAut var tree = TA.BATreeAutomaton (Set.fromList [0..n+1]) (Set.fromList [n+1]) (Set.fromList [0]) (Map.fromList trans)
  where
    n = length tree
    trans = [(([0,0], (singSymbol '0' var)), Set.fromList [0]),(([0,0], (singSymbol '1' var)), Set.fromList [1])]++(treeTransitions (reverse tree) 1)
    treeTransitions [] st = []
    treeTransitions (x:xs) st
      | x == 0 = (([st,0], (singSymbol '0' var)), Set.fromList [st+1]):(treeTransitions xs (st+1))
      | x == 1 = (([0,st], (singSymbol '0' var)), Set.fromList [st+1]):(treeTransitions xs (st+1))

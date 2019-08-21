{-|
Module      : MonaAutomataWrapper
Description : Mona automata wrapper
Author      : Vojtech Havlena, August 2018
License     : GPL-3
-}

module MonaAutomataWrapper (
  monaGTAToTA
  , convertGTA -- For debugging purposes
) where

import MonaAutomataParser
import TreeAutomaton
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Alphabet as Alp


-- |SizeMap: StateSpace ID -> size
type SizeMap = Map.Map Int Int
-- |GuideMap: MonaState -> [MonaState]
type GuideMap = Map.Map MonaState [MonaState]


-- |Convert Mona guided tree automaton into regular TA (only automaton
-- corresponding to state space <univ> is considered)
-- Steps: 1) According to state spaces sizes determine states of the TA
--        2) Convert mona transitions according to guide
--        2.a) Convert source states
--        2.b) Convert mona symbols
--        3) Convert leaf and root states (root state is considered in the first state space)
monaGTAToTA :: MonaGTA -> BATreeAutomaton MonaState Alp.Symbol
monaGTAToTA (MonaGTA header (MonaGuide guide) spaces) = (autRestriction (Set.fromList univstates) $
   BATreeAutomaton states rts leaves trans)
  { roots = Set.fromList univroot }
  where
    guide' = Map.fromList $ map (\(MonaGuideRule _ fr dest) -> (fr, dest)) guide
    vars = variables header
    expSpaces = expandTrans vars spaces
    sizes = getSizes expSpaces
    sizedict = getSizesDict expSpaces sizes
    trans = unifyTransitions vars guide' sizedict expSpaces
    totalStates = foldr (+) 0 (map (size) spaces)
    states = Set.fromList [0..totalStates-1]
    leaves = Set.fromList $ zipWith (+) sizes $ map (initial) expSpaces
    rts = Set.fromList $ accept header
    -- Projection to states which are in the state space <univ>
    univspace = head $ filter (\t@(MonaStateSpace _ name _ _ _) -> name == "<univ>") spaces
    hatspace = head $ filter (\t@(MonaStateSpace _ name _ _ _) -> name == "<hat>") spaces
    univstates = getSpaceTAStates sizedict univspace
    hatstates = getSpaceTAStates sizedict univspace
    univroot = (Map.toList trans) >>= \((a,_),c) -> if not $ Set.disjoint rts c then intersect univstates a else []


-- |Get states corresponding to a given mona state space.
-- sizedict: Sizes of each state space
getSpaceTAStates :: SizeMap -> MonaStateSpace -> [Int]
getSpaceTAStates sizedict (MonaStateSpace iden _ size _ _) = [start..start+size-1] where
  start = Map.findWithDefault 0 iden sizedict


-- |Get map (dict) containing for each mona state space number of states contained
-- in predecessors state spaces (i.e., map contains index of the first state in
-- a given state space, numbered from 0).
-- arr: size array (obtained via function getSizes)
getSizesDict :: [MonaStateSpace] -> [Int] -> SizeMap
getSizesDict spaces arr = Map.fromList dict where
  dict = zipWith (\a b -> (iden a,b)) spaces arr


-- |Get a list containing for each mona state space number of states contained
-- in predecessors state spaces (i.e., map contains index of the first state in
-- a given state space, numbered from 0).
getSizes :: [MonaStateSpace] -> [Int]
getSizes spaces = init . scanl (+) 0 $ map (size) spaces


-- |Gather transitions from all state spaces and convert them into TA
-- transitions.
unifyTransitions :: [Alp.Variable] -> GuideMap -> SizeMap -> [MonaStateSpace] -> Transitions MonaState Alp.Symbol
unifyTransitions vars guide sizes spaces = Map.fromListWith (Set.union) $
      foldr1 (++) $ map (unifyStateSpace vars guide sizes) spaces


-- |Gather transtions from a single mona state space and convert then into TA
-- transition (it mean rename states, replace don't care symbol X).
unifyStateSpace :: [Alp.Variable] -> GuideMap -> SizeMap -> MonaStateSpace  -> [Transition MonaState Alp.Symbol]
unifyStateSpace vars guide sizes (MonaStateSpace iden _ _ initial trans) = map (conv) trans where
  conv (MonaTransition src sym dest) = ((src', convToSymbol vars sym), Set.singleton dest') where
    pl = Map.findWithDefault [] iden guide
    sizes' = map (\a -> Map.findWithDefault 0 a sizes) pl
    src' = zipWith (+) src sizes'
    dest' = (Map.findWithDefault 0 iden sizes) + dest


-- |Expand don't care symbols in mona state space transitions.
expandTrans :: [Alp.Variable] -> [MonaStateSpace] -> [MonaStateSpace]
expandTrans vars = map (conv) where
  conv (MonaStateSpace i n s ini tr) = MonaStateSpace i n s ini (tr >>= expandSymbols vars)


-- |Expand don't care symbol in single mona transition and return a list of
-- mona transitions.
expandSymbols :: [Alp.Variable] -> MonaTransition -> [MonaTransition]
expandSymbols vars (MonaTransition src sym dest) = map (\s -> MonaTransition src s dest) expX where
  expX = expandX $ reorderMonaSymbol vars sym


-- |Replace X in a given string for symbols [0,1] (yielding more strings).
expandX :: String -> [String]
expandX str = listProd (reverse $ str >>= gen) [[]] where
  gen a = if a == 'X' then return ['0','1']
         else return [a]


-- |Convert string to a TA symbol.
convToSymbol :: [Alp.Variable] -> String -> Alp.Symbol
convToSymbol vars sym = (sym, Set.fromList vars)


-- |Reorder mona symbol according to order on variables (e.g. X < Y < Z,
-- lexicographic order).
reorderMonaSymbol :: [Alp.Variable] -> String -> String
reorderMonaSymbol vars sym = sym' where
  pair = zip vars sym
  sym' = map (snd) $ sortBy (\x y -> compare (fst x) (fst y)) pair


-- |Cartesian product (wrt operation : concatenation) of a list of lists.
listProd [] a = a
listProd (x:xs) a = listProd xs (x >>= \b -> map (b:) a)


-- |Only for debug purposes.
convertGTA filename = do
  monagta <- parseFile filename
  let aut = monaGTAToTA monagta
    in do
    putStrLn $ show $ accept $ header monagta
    putStrLn $ show $ aut
    putStrLn $ show $ removeUnreachable aut

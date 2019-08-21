{-|
Module      : Alphabet
Description : Functions for working with symbols with variables.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module Alphabet (
   Variable
   , Symbol
   , emptySymbol
   , projSymbol
   , projSymbolX
   , projSymbolsX
   , projSymbolVars
   , remSymbol
   , remSymbolVars
   , cylindrifySymbol
   , cylindrifySymbols
   , showSymbolDbg
   , zeroSymbol
   , projZeroSymbol
   , projXZeroSymbol
   , unwindSymbolX
   , unwindSymbolsX
) where


import qualified Data.Set as Set
import qualified Data.List as List
import qualified AuxFunctions as Aux


type Variable = String
-- |(assigment of values, variables) ("001",{X,Y,Z}) where X < Y < Z
type Symbol = ([Char], Set.Set Variable)


-- |Empty symbol = epsilon
emptySymbol = ([], Set.empty)

-- |Symbol with all variables assigned to 0.
zeroSymbol vars = (replicate (length vars) '0', Set.fromList vars)


-- |Show symbol in human readable debug format.
showSymbolDbg :: Symbol -> String
showSymbolDbg (str, _) = str


-- |Make projection of a symbol wrt a given variable (i.e. it returns symbols
-- where the values of this variable are set to 0, 1).
projSymbol :: Symbol -> Variable -> Set.Set Symbol
projSymbol s new = Set.fromList [insertVarVal s new a | a <- ['0', '1']]


projSymbolX :: Symbol -> Variable -> Symbol
projSymbolX s@(_, vars) new =
  if Set.member new vars then updateVarVal s new 'X'
  else insertVarVal s new 'X'


projSymbolsX :: Set.Set Symbol -> Variable -> Set.Set Symbol
projSymbolsX s var = Set.map (\a -> projSymbolX a var) s


updateVarVal :: Symbol -> Variable -> Char -> Symbol
updateVarVal (lst, vars) new val =
  case List.elemIndex new (Set.toAscList vars) of
    Just idx -> (Aux.updateAt val lst idx, vars)
    Nothing -> error "updateVarVal: Index not found"


insertVarVal :: Symbol -> Variable -> Char -> Symbol
insertVarVal (lst, vars) new val =
   case List.elemIndex new (Set.toAscList vars') of --List.sort $ Set.toList vars'
      Just idx -> (Aux.insertAt val lst idx, vars')
      Nothing -> error "projSymbol: Index not found"
   where
      vars' = Set.insert new vars


unwindSymbolX :: Symbol -> Set.Set Symbol
unwindSymbolX (lst, vars) = Set.fromList [(l, vars) | l <- lst'] where
  lst' = Aux.crossProd $ lst >>= \a ->
    if a == 'X' then  [Set.fromList "01"]
    else [Set.singleton a]


unwindSymbolsX :: Set.Set Symbol -> Set.Set Symbol
unwindSymbolsX st = Set.unions $ Set.toList $ Set.map (unwindSymbolX) st


-- |Pointwise extension of projSymbol to a set of variables and a set of symbols.
projSymbolVars :: Set.Set Symbol -> [Variable] -> Set.Set Symbol
projSymbolVars s [] = s
projSymbolVars s (x:xs) = projSymbolVars s' xs where
   s' = foldr (Set.union) Set.empty [ projSymbol sym x | sym <- Set.toList s ]


-- |Remove value of given variable from a symbol.
remSymbol :: Symbol -> Variable -> Symbol
remSymbol (lst, vars) new =
   case List.elemIndex new (Set.toAscList vars) of
      Just idx -> (Aux.deleteAt lst idx, vars')
      Nothing -> error "remSymbol: Index not found"
   where
      vars' = Set.delete new vars


-- |Pointwise extension of remSymbol to a set of variables.
remSymbolVars :: Symbol -> [Variable] -> Symbol
remSymbolVars s [] = s
remSymbolVars s (x:xs) = remSymbolVars (remSymbol s x) xs


-- |Cylindrify symbol -- maintain values of only those variables which are in the list.
cylindrifySymbol :: [Variable] -> Symbol -> Symbol
cylindrifySymbol = cylidrifySymbol' -- = remSymbolVars sym (Set.toList $ Set.difference (snd sym) (Set.fromList vars))


cylidrifySymbol' :: [Variable] -> Symbol -> Symbol
cylidrifySymbol' vars (val,var) = (a, Set.fromList b) where
  (a,b) = unzip $ filter (\(a,b) -> elem b vars) $ zip val (Set.toAscList var)


-- |Cylindrify symbols (extension of cylindrifySymbol).
cylindrifySymbols :: [Variable] -> Set.Set Symbol -> Set.Set Symbol
cylindrifySymbols vars sym = Set.map (cylindrifySymbol vars) sym


-- |Project the zero symbol (consisting of all zeros).
projZeroSymbol :: [Variable] -> Set.Set Symbol
projZeroSymbol (var:vars) = projSymbolVars (Set.fromList [zeroSymbol vars]) [var]


projXZeroSymbol :: [Variable] -> Set.Set Symbol
projXZeroSymbol (var:vars) = Set.singleton $ projSymbolX (zeroSymbol vars) var

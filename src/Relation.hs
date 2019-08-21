{-|
Module      : Relation
Description : Auxiliary function for working with relations
Author      : Vojtech Havlena, July 2019
License     : GPL-3
-}

module Relation where

import Data.Tuple

import qualified Data.Map as Map
import qualified Data.Set as Set

type Relation a b = Set.Set (a,b)


symRel :: (Ord a) => Relation a a -> Relation a a
symRel = Set.map (swap)


symClosure :: (Ord a) => Relation a a -> Relation a a
symClosure rel = Set.union rel $ symRel rel


idRel :: (Ord a) => Set.Set a -> Relation a a
idRel = Set.map (\x -> (x,x))


getRelated :: (Ord a, Ord b) => Relation a b -> a -> Set.Set b
getRelated st x = Set.map (snd) $ Set.filter (\(u,_) -> x == u) st

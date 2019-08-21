{-|
Module      : AntiprenexConfig
Description : Antiprenex config file
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module AntiprenexConfig where


-- |Formula balancing alternatives
data BalanceFormulaConfig =
  BalInformed
  | BalInformedSplit
  | BalFullTree
  deriving (Eq)

-- |Rename bound vars.
renameBoundVars = True

-- |Formula balancing (conjunction and disjunction)
balanceFormulaConfig = BalFullTree

-- |Number of distribution steps
distrSteps = 3 :: Int


-- |Number of chunks for splitting in informed balancing
balInforSplitChunks = 5 :: Int

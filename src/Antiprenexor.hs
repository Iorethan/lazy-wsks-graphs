{-|
Module      : Antiprenexor
Description : Main file for WSkS formulae antiprenexing.
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

import System.Environment
import Control.Monad.Writer
import Data.Time

import MonaFormulaOperation
import MonaFormulaAntiprenex

import AntiprenexConfig
import qualified BaseDecisionProcedure as BP
import qualified Data.Map as Map
import qualified LazyDecisionProcedure as LDP
import qualified StrictDecisionProcedure as SDP
import qualified Logic as Lo
import qualified FormulaOperation as FO
import qualified MonaFormulaOperationSubst as FOS
import qualified Examples as Ex
import qualified MonaWrapper as MoWr
import qualified MonaParser as MoPa
import qualified BasicAutomata as BA
import qualified MonaSocket as MS


-- |Parameters of the decision procedure.
data ProcedureArgs =
  Where
  | Pred
  | None
  deriving (Eq)

-- |Program arguments.
data ProgArgs =
  Antiprenex ProcedureArgs FilePath
  | Help
  | Error


-- |Parse program arguments.
parseArgs :: [String] -> ProgArgs
parseArgs args
  | (length args) == 1 && (last args) == "--help" = Help
  | (length args) >= 1 = Antiprenex (parseProcedureArgs $ tail args) (head args)
  | otherwise = Error


parseProcedureArgs :: [String] -> ProcedureArgs
parseProcedureArgs args
  | (length args) == 1 && (last args) == "-w" = Where
  | (length args) == 1 && (last args) == "-p" = Pred
  | otherwise = None


-- |Show formula and its simplicication for debug purposes.
formulaOperationsDebug :: Lo.Formula -> IO ()
formulaOperationsDebug f = do
  let sf = FO.simplifyFormula f in do
    putStrLn $ show $ FO.antiprenex sf
    putStrLn $ show $ FO.antiprenex $ FO.balanceFormula sf


-- |Wrap for renaming bound variables in Mona file.
renameBVFileWrap :: MoPa.MonaFile -> MoPa.MonaFile
renameBVFileWrap = if renameBoundVars then FOS.renameBVFile else id


-- |Show help.
showHelp :: IO ()
showHelp = do
  prname <- getProgName
  putStrLn $ "Usage: ./" ++ prname ++ " [file] [args]"
  putStrLn $ "where [args] is one of\n  [--help] show this help\n  [-w] remove where in quatification\n  [-p] do not replace predicate and macros calls"


-- |Main function
main = do
   args <- getArgs
   start <- getCurrentTime
   case (parseArgs args) of
     (Antiprenex arg file) -> do
       mona <- MoPa.parseFile file

       case arg of
         Where -> putStrLn $ show $ removeWhereFile $ unwindQuantifFile mona
         None -> putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeRedundantPreds $ replaceAllCallsFile $ renameBVFileWrap $ removeWhereFile $ unwindQuantifFile mona
         Pred -> putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeRedundantPreds $ removeWhereFile $ unwindQuantifFile mona

       --putStrLn $ show $ antiprenexFile $ renameBVFileWrap $ removeWhereFile $ unwindQuantifFile mona
       stop <- getCurrentTime
       putStrLn $ "Time: " ++ show (diffUTCTime stop start)
     Help -> showHelp
     Error -> do
       putStrLn $ "Bad input params"
       showHelp

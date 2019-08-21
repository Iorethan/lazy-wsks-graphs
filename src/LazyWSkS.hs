{-|
Module      : LazyWSkS
Description : Main file for WSkS decision procedure.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

import System.Environment
import Control.Monad.Writer
import Data.Time

import MonaFormulaOperation
import MonaFormulaAntiprenex

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


-- |Use Mona for translating formulas (so far only support for atoms)
-- to tree automata.
useMona = False
-- |Rename bound vars.
renameBoundVars = False

-- |Parameters of the decision procedure.
data ProcedureArgs =
  Prenex
  | None
  deriving (Eq)

-- |Program arguments.
data ProgArgs =
  Validity FilePath ProcedureArgs
  | Antiprenex FilePath
  | Help
  | Error


-- |Parse program arguments.
parseArgs :: [String] -> ProgArgs
parseArgs args
  | (length args) == 1 && (last args) == "--help" = Help
  | (length args) == 1 = Validity (head args) None
  | (length args) == 2 && (last args) == "-p" = Validity (head args) Prenex
  | (length args) == 2 && (last args) == "--prenex" = Antiprenex $ head args
  | otherwise = Error


-- |Show formula and its validity (strict approach)
showValid :: Lo.Formula -> IO ()
showValid f = do
   putStrLn $ show f
   putStrLn $ formatAnswer $ SDP.isValid f


-- |Show formula and its validity (lazy approach)
showValidLazy :: Lo.Formula -> IO ()
showValidLazy f = showValidMonaLazy [] f


-- |Show formula and its validity using MONA
showValidMonaLazy :: [(String, BA.WS2STreeAut)] -> Lo.Formula -> IO ()
showValidMonaLazy aut f = do
   putStrLn $ show f
   putStrLn $ formatAnswerStat $ LDP.isValid (Map.fromList aut) f


formatAnswerStat :: Either BP.FormulaStat String -> String
formatAnswerStat (Left (BP.FormulaStat val states)) = (if val then "valid" else "unsatisfiable") ++ "\nStates: " ++ (show states)
formatAnswerStat (Right y) = "Error: " ++ show y


-- |Format validity answer
formatAnswer :: Either Bool String -> String
formatAnswer (Left x) = formatAnswerStat (Left $ BP.FormulaStat x (-1))
formatAnswer (Right y) = "Error: " ++ show y


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
  putStrLn $ "where [args] is one of\n  [--help] show this help\n  [-p] for " ++
    "supress of formula antiprenexing\n  [--prenex] only for converting "++
    "formula to antiprenexed MONA formula"


-- |Main function
main = do
   args <- getArgs
   start <- getCurrentTime
   case (parseArgs args) of
     (Antiprenex file) -> do
       mona <- MoPa.parseFile file
       putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeWhereFile $ replaceCallsFile $ renameBVFileWrap $ unwindQuantifFile mona
       stop <- getCurrentTime
       putStrLn $ "Time: " ++ show (diffUTCTime stop start)
     (Validity file par) -> do
       mona <- MoPa.parseFile file
       let fnc = if par == Prenex then simplifyFile else antiprenexFile
           prenexFile = fnc $ removeForAllFile $ removeWhereFile $ replaceCallsFile $ renameBVFileWrap $ unwindQuantifFile mona
           (hf, monareq) = runWriter $ Lo.convertMonaSub useMona $ Lo.simplifyTrueFalse $ MoWr.getBaseFormula prenexFile in
           do
             auts <- MS.getMonaAutomata monareq
             showValidMonaLazy auts hf
             stop <- getCurrentTime
             putStrLn $ "Time: " ++ show (diffUTCTime stop start)
     Help -> showHelp
     Error -> do
       putStrLn $ "Bad input params"
       showHelp

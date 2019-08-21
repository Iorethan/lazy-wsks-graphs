{-|
Module      : MonaAutomataParser
Description : Mona automata parser
Author      : Vojtech Havlena, August 2018
License     : GPL-3
-}

module MonaAutomataParser where

import Control.Applicative ((<*))

import Data.List

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.String
import Text.Parsec.Token

import qualified TreeAutomaton as TA
import qualified BasicAutomata as BA
import AuxFunctions

--------------------------------------------------------------------------------------------------------------
-- Part with the data types
--------------------------------------------------------------------------------------------------------------

type MonaState = Int
type MonaSymbol = String

data MonaTransition =
  MonaTransition [MonaState] MonaSymbol MonaState

data MonaGuideRule =
  MonaGuideRule String MonaState [MonaState]

data MonaGuide = MonaGuide [MonaGuideRule]

data MonaStateSpace = MonaStateSpace {
  iden :: MonaState
  , name :: String
  , size :: Int
  , initial :: MonaState
  , transitions :: [MonaTransition]
}

data MonaGTAHeader = MonaGTAHeader {
  variables :: [String]
  , accept :: [MonaState]
  , reject :: [MonaState]
}

data MonaGTA = MonaGTA {
  header :: MonaGTAHeader
  , guide :: MonaGuide
  , spaces :: [MonaStateSpace]
}


instance Show MonaTransition where
  show (MonaTransition sts sym st) = "(" ++ (prArr "," sts) ++
      ","++ sym ++") -> " ++ show st

instance Show MonaGuideRule where
  show (MonaGuideRule name src dest) = name ++ ": " ++ show src ++
      " -> " ++ "(" ++ (prArr "," dest) ++ ")"

instance Show MonaStateSpace where
  show (MonaStateSpace iden name size initial trans) = "State space " ++
      show iden ++ " " ++ name ++ " (size "++ show size ++")\nInitial state: " ++
      show initial ++ "\nTransitions:\n" ++ (prArr "\n" trans) ++ "\n"

instance Show MonaGTAHeader where
  show (MonaGTAHeader var acc rej) = "GTA for formula with free variables: " ++
      intercalate " " var ++ "\nAccepting states: " ++ (prArr " " acc) ++
      "\nRejecting states: " ++ (prArr " " rej) ++ "\n"

instance Show MonaGTA where
  show (MonaGTA header guide spaces) = show guide ++ "\n" ++ show header ++
      "\n" ++ (prArr "\n" spaces)

instance Show MonaGuide where
  show (MonaGuide rules) = "Guide:\n" ++ (prArr "\n" rules) ++ "\n"


--------------------------------------------------------------------------------------------------------------
-- Part with the definitions of lexemes
--------------------------------------------------------------------------------------------------------------

lexer = makeTokenParser emptyDef
m_comma = lexeme lexer (char ',')
m_lparen = lexeme lexer (char '(')
m_rparen = lexeme lexer (char ')')
m_ddot = lexeme lexer (char ':')
m_to = lexeme lexer (string "->")
m_quot = lexeme lexer (char '\'')
m_statespace = lexeme lexer (string "State space")
m_size = lexeme lexer (string "size")
m_initial = lexeme lexer (string "Initial state:")
m_trans = lexeme lexer (string "Transitions:")
m_guide = lexeme lexer (string "Guide:")
m_gtaheader = string "GTA for formula with free variables:"
m_accept = string "Accepting states:"
m_reject = string "Rejecting states:"
m_dontcare = string "Don't-care states:"
m_white = whiteSpace lexer
m_space = ((oneOf " "))
m_variable = many1 (alphaNum <|> char '$')
m_identifier = lexeme lexer (many alphaNum)
m_guideName = lexeme lexer (many1 (noneOf " \t\n:()\'"))


parseFile :: FilePath -> IO MonaGTA
parseFile filename = do
  str <- readFile filename
  return $ parseString str


parseString :: String -> MonaGTA
parseString str = case (parse parseGTA "MonaAutomataParser" str) of
  Left err   -> error $ show err
  Right res  -> res


--------------------------------------------------------------------------------------------------------------
-- Part with the definitions of parsing rules
--------------------------------------------------------------------------------------------------------------

parseTransition :: Parser MonaTransition
parseTransition = do
  m_white
  m_lparen
  s <- sepBy m_identifier m_comma
  m_rparen
  m_to
  dest <- m_identifier
  return $ makeTransition (init s) (last s) dest


parseGuideRule :: Parser MonaGuideRule
parseGuideRule = do
  m_white
  name <- m_guideName
  m_ddot
  src <- m_identifier
  m_to
  m_lparen
  dst <- sepBy m_identifier m_comma
  m_rparen
  return $ makeGuideRule name src dst


parseTransitionSet :: Parser [MonaTransition]
parseTransitionSet = do
  trans <- many (try parseTransition)
  return trans


parseGuideRuleSet :: Parser [MonaGuideRule]
parseGuideRuleSet = do
  gds <- many (try parseGuideRule)
  return gds


parseGuide :: Parser MonaGuide
parseGuide = do
  m_white
  m_guide
  rules <- parseGuideRuleSet
  return $ MonaGuide rules


parseStateSpaceHeader :: Parser MonaStateSpace
parseStateSpaceHeader = do
  m_white
  m_statespace
  iden <- m_identifier
  m_quot
  name <- m_guideName
  m_quot
  m_lparen
  m_size
  size <- m_identifier
  m_rparen
  m_ddot
  return $ MonaStateSpace (read iden :: Int) name (read size :: Int) 0 [] --Dangerous, default 0 is for Int, not for general MonaState


parseStateSpace :: Parser MonaStateSpace
parseStateSpace = do
  m_white
  sp <- parseStateSpaceHeader
  m_initial
  ini <- m_identifier
  m_trans
  trans <- parseTransitionSet
  return $ MonaStateSpace {iden = iden sp, name=name sp, size=size sp,
    initial=(read ini :: Int), transitions=trans}


parseGTAHeader :: Parser MonaGTAHeader
parseGTAHeader = do
  m_white
  vars <- parseVarList m_gtaheader
  newline
  acc <- parseVarList m_accept
  newline
  reject <- parseVarList m_reject
  newline
  optional $ parseVarList m_dontcare
  return $ MonaGTAHeader vars (toInt acc) (toInt reject)


parseVarList :: Parser String -> Parser [String]
parseVarList str = do
  str
  optionMaybe m_space
  vars <- sepEndBy m_variable m_space
  return vars


parseGTA :: Parser MonaGTA
parseGTA = do
  guide <- parseGuide
  header <- parseGTAHeader
  spaces <- many1 (try parseStateSpace)
  return $ MonaGTA header guide spaces


toInt :: [String] -> [Int]
toInt = map (\a -> read a :: Int)


makeGuideRule :: String -> String -> [String] -> MonaGuideRule
makeGuideRule name src dest = MonaGuideRule name (read src :: Int) (toInt dest)


makeTransition :: [String] -> String -> String -> MonaTransition
makeTransition sts sym st = MonaTransition (toInt sts) sym (read st :: Int)

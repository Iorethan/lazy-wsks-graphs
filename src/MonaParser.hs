{-|
Module      : MonaParser
Description : Mona formulae parser
Author      : Ondrej Lengal, 2018
License     : GPL-3
-}

module MonaParser where

import Control.Applicative ((<*))

import Data.List

import AuxFunctions
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.String
import Text.Parsec.Token

--import Logic


parseFile :: FilePath -> IO MonaFile
parseFile filename = do
  str <- readFile filename
  return $ parseString str


parseString :: String -> MonaFile
parseString str = case (parse monaFileParser "MONA parser" str) of
  Left err   -> error $ show err
  Right res  -> res
-- parseString = error "Unimplemented"


def = emptyDef{ commentStart = "/*"
              , commentEnd = "*/"
              , commentLine = "#"
              , nestedComments = False
              , caseSensitive = True
              , identStart = letter <|> char '_' <|> char '$' <|> char '\''
              , identLetter = alphaNum <|> char '_' <|> char '$' <|> char '\''
              , opStart = oneOf "~&:|.<=>+-,\"\\^"
              , opLetter = oneOf "~&:|.<=>+-,\"\\^"
              , reservedOpNames =
                [ "~"     -- NOT
                , "&"     -- AND
                , "|"     -- OR
                , "=>"    -- IMPLIES
                , "<=>"   -- EQUIV
                , "="     -- EQUALS
                , "~="    -- NEQUALS
                , "<"     -- LT
                , "<="    -- LEQ
                , ">"     -- GT
                , ">="    -- GEQ
                , "+"     -- PLUS
                , "-"     -- MINUS
                , ":"     --
                , ","     --
                , "."
                , "^"
                , "\\"
                --, ".1"    -- Right successor
                --, ".0"    -- Right successor
                ]
              , reservedNames =
                [ "ex0"
                , "ex1"
                , "ex2"
                , "all0"
                , "all1"
                , "all2"
                , "var0"
                , "var1"
                , "var2"
                , "let0"
                , "let1"
                , "let2"
                , "sub"
                , "in"
                , "notin"
                , "true"
                , "false"
                , "macro"
                , "pred"
                , "allpos"
                , "type"
                , "ws1s"
                , "ws2s"
                , "m2l-str"
                , "m2l-tree"
                , "where"
                , "export"
                , "import"
                , "restrict"
                , "empty"
                , "prefix"
                , "root"
                , "variant"
                , "type"
                , "in_state_space"
                , "tree"
                , "sometype"
                , "min"
                , "max"
                , "assert"
                , "pconst"
                , "union"
                , "inter"
                , "tree_root"
                , "succ"
                , "const_tree"
                , "universe"
                , "guide"
                , "include"
                , "execute"
                , "const"
                , "sing"
                , "cat1"
                , "..."
                , "lastpos"
                ]
              }


-- generate parsers
TokenParser{ parens = m_parens
           , braces = m_braces
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , comma = m_comma
           , commaSep = m_commaSep
           , commaSep1 = m_commaSep1
           , semi = m_semi
           , semiSep1 = m_semiSep1
           , natural = m_natural
           , stringLiteral = m_stringLiteral
           , whiteSpace = m_whiteSpace } = makeTokenParser def


-- terms in MONA expressions
data MonaTerm
  = MonaTermVar String
  | MonaTermConst Integer
  | MonaTermPlus MonaTerm MonaTerm
  | MonaTermCat MonaTerm MonaTerm
  | MonaTermUp MonaTerm
  | MonaTermMinus MonaTerm MonaTerm
  | MonaTermRoot
  | MonaTermEmpty
  | MonaTermDots
  | MonaTermBool MonaAtom
  | MonaTermBoolCall String [MonaTerm]
  | MonaTermPConst Integer
  | MonaTermUnion MonaTerm MonaTerm
  | MonaTermInter MonaTerm MonaTerm
  | MonaTermDifference MonaTerm MonaTerm
  | MonaTermSet [MonaTerm]
  deriving (Eq, Ord)

instance Show MonaTerm where
  show (MonaTermVar str) = str
  show (MonaTermRoot) = "root"
  show (MonaTermDots) = "..."
  show (MonaTermConst n) = show n
  show (MonaTermPlus t1 t2) = (pars $ show t1) ++ " + " ++ (show t2)
  show (MonaTermCat t1 t2) = (pars $ show t1) ++ " . " ++ (show t2)
  show (MonaTermMinus t1 t2) = (pars $ show t1) ++ " - " ++ (show t2)
  show (MonaTermUp t) = (pars $ show t) ++ "^"
  show (MonaTermBool atom) = show atom
  show (MonaTermBoolCall name terms) = name ++ "(" ++ (prArr "," terms) ++ ")"
  show (MonaTermPConst n) = "pconst(" ++ (show n) ++ ")"
  show (MonaTermEmpty) = "empty"
  show (MonaTermUnion t1 t2) = (pars $ show t1) ++ " union " ++ (pars $ show t2)
  show (MonaTermInter t1 t2) = (pars $ show t1) ++ " inter " ++ (pars $ show t2)
  show (MonaTermDifference t1 t2) = (pars $ show t1) ++ " \\ " ++ (pars $ show t2)
  show (MonaTermSet t) = "{" ++ (prArr "," t) ++  "}"


-- put something inside parenthesis
pars :: String -> String
pars str = "(" ++ str ++ ")"


-- parses terms
termParser :: Parser MonaTerm
termParser = buildExpressionParser termOpTable termP <?> "term"

-- term operator table
termOpTable = [ [ Infix (m_reservedOp "+" >> return MonaTermPlus) AssocLeft
                , Infix (m_reservedOp "." >> return MonaTermCat) AssocLeft
                , Postfix (m_reservedOp "^" >> return MonaTermUp)
                , Infix (m_reservedOp "-" >> return MonaTermMinus) AssocLeft
                , Infix (m_reservedOp "union" >> return MonaTermUnion) AssocLeft
                , Infix (m_reservedOp "inter" >> return MonaTermInter) AssocLeft
                , Infix (m_reservedOp "\\" >> return MonaTermDifference) AssocLeft
                ]
              ]

termP :: Parser MonaTerm
termP = m_parens termParser
    <|> try (do { t <- m_braces $ m_commaSep termParam
                ; return $ MonaTermSet t
              })
    <|> try (do { m_reserved "pconst"
                ; n <- m_parens $ m_natural
                ; return (MonaTermPConst n)
                })
    <|> fmap MonaTermVar m_identifier
    <|> fmap MonaTermConst m_natural
    <|>  (m_reserved "root" >> return MonaTermRoot)
    <|>  (m_reserved "empty" >> return MonaTermEmpty)
    <|>  (m_reserved "..." >> return MonaTermDots)


-- parses terms
termParamParser :: Parser MonaTerm
termParamParser = buildExpressionParser termOpTable termParam <?> "term"


termParam :: Parser MonaTerm
termParam = m_parens termParamParser
    <|> fmap MonaTermBool atomicFormulaParser
    <|> try (do { m_reserved "pconst"
                ; n <- m_parens $ m_natural
                ; return (MonaTermPConst n)
                })
    <|> try (do { predname <- m_identifier
                ; args <- m_parens $ m_commaSep termParam
                ; return (MonaTermBoolCall predname $ args)
                })
    <|> termParser
    -- <|> fmap MonaTermVar m_identifier
    -- <|> fmap MonaTermConst m_natural
    -- <|> (m_reserved "root" >> return MonaTermRoot)


-- sanitizes terms
sanitizeTerm :: MonaTerm -> MonaTerm
sanitizeTerm = error "Unimplemented"


-- atomic formulae (atom) in MONA
data MonaAtom
  = MonaAtomLe MonaTerm MonaTerm
  | MonaAtomEq MonaTerm MonaTerm
  | MonaAtomNeq MonaTerm MonaTerm
  | MonaAtomLeq MonaTerm MonaTerm
  | MonaAtomGe MonaTerm MonaTerm
  | MonaAtomGeq MonaTerm MonaTerm
  | MonaAtomIn MonaTerm MonaTerm
  | MonaAtomNotIn MonaTerm MonaTerm
  | MonaAtomSub MonaTerm MonaTerm
  | MonaAtomSing MonaTerm
  | MonaAtomEps MonaTerm
  | MonaAtomTerm MonaTerm
  | MonaAtomIsEmpty MonaTerm
  | MonaAtomTrue
  | MonaAtomFalse
  deriving (Eq, Ord)

instance Show MonaAtom where
  show (MonaAtomLe t1 t2) = (show t1) ++ " < " ++ (show t2)
  show (MonaAtomLeq t1 t2) = (show t1) ++ " <= " ++ (show t2)
  show (MonaAtomEq t1 t2) = (show t1) ++ " = " ++ (show t2)
  show (MonaAtomNeq t1 t2) = (show t1) ++ " ~= " ++ (show t2)
  show (MonaAtomGe t1 t2) = (show t1) ++ " > " ++ (show t2)
  show (MonaAtomGeq t1 t2) = (show t1) ++ " >= " ++ (show t2)
  show (MonaAtomIn t1 t2) = pars ((show t1) ++ " in " ++ (show t2))
  show (MonaAtomNotIn t1 t2) = (show t1) ++ " notin " ++ (show t2)
  show (MonaAtomSub t1 t2) = (show t1) ++ " sub " ++ (show t2)
  show (MonaAtomTerm t) = show t
  show (MonaAtomSing t) = "sing( " ++ (show t) ++ " )"
  show (MonaAtomEps t) = "eps( " ++ (show t) ++ " )"
  show (MonaAtomIsEmpty t) = "empty(" ++ (show t) ++ ")"
  show MonaAtomTrue = "true"
  show MonaAtomFalse = "false"


-- formulae in MONA
data MonaFormula
  = MonaFormulaAtomic MonaAtom
  | MonaFormulaVar String
  | MonaFormulaNeg MonaFormula
  | MonaFormulaDisj MonaFormula MonaFormula
  | MonaFormulaConj MonaFormula MonaFormula
  | MonaFormulaImpl MonaFormula MonaFormula
  | MonaFormulaEquiv MonaFormula MonaFormula
  | MonaFormulaEx0 [String] MonaFormula
  | MonaFormulaEx1 [(String, Maybe MonaFormula)] MonaFormula
  | MonaFormulaEx2 [(String, Maybe MonaFormula)] MonaFormula
  | MonaFormulaExGen String MonaFormula
  | MonaFormulaAll0 [String] MonaFormula
  | MonaFormulaAll1 [(String, Maybe MonaFormula)] MonaFormula
  | MonaFormulaAll2 [(String, Maybe MonaFormula)] MonaFormula
  | MonaFormulaPredCall String [MonaTerm]
  deriving (Eq, Ord)

instance Show MonaFormula where
  show (MonaFormulaAtomic atom) = show atom
  show (MonaFormulaVar str) = str
  show (MonaFormulaNeg phi) = "~(" ++ (show phi) ++ ")"
  show (MonaFormulaDisj f1 f2) = "((" ++ (show f1) ++ ") | (" ++ (show f2) ++ "))"
  show (MonaFormulaConj f1 f2) = "((" ++ (show f1) ++ ") & (" ++ (show f2) ++ "))"
  show (MonaFormulaImpl f1 f2) = "((" ++ (show f1) ++ ") => (" ++ (show f2) ++ "))"
  show (MonaFormulaEquiv f1 f2) = "((" ++ (show f1) ++ ") <=> (" ++ (show f2) ++ "))"
  show (MonaFormulaEx0 varList phi) = pars $
    "ex0 " ++ (unwords varList) ++ ": " ++ (show phi)
  show (MonaFormulaEx1 varWhereCl phi) = pars $
    "ex1 " ++ (showVarWhereClause varWhereCl) ++ ": " ++ (show phi)
  show (MonaFormulaEx2 varWhereCl phi) = pars $
    "ex2 " ++ (showVarWhereClause varWhereCl) ++ ": " ++ (show phi)
  show (MonaFormulaExGen var phi) = pars $
    "allGen " ++ var ++ ": " ++ (show phi)
  show (MonaFormulaAll0 varList phi) = pars $
    "all0 " ++ (unwords varList) ++ ": " ++ (show phi)
  show (MonaFormulaAll1 varWhereCl phi) = pars $
    "all1 " ++ (showVarWhereClause varWhereCl) ++ ": " ++ (show phi)
  show (MonaFormulaAll2 varWhereCl phi) = pars $
    "all2 " ++ (showVarWhereClause varWhereCl) ++ ": " ++ (show phi)
  show (MonaFormulaPredCall name terms) = name ++ "(" ++ (prArr "," terms) ++ ")"


-- parses a binary atom
binAtomParser :: String -> (MonaTerm -> MonaTerm -> MonaAtom) -> Parser MonaAtom
binAtomParser op f = do { lhs <- termParser
                      ; m_reservedOp op
                      ; rhs <- termParser
                      ; return (f lhs rhs) ---((show lhs) ++ " " ++ op ++ " " ++ (show rhs)))
                      }


-- binAtomParserSuff :: String -> String -> Parser MonaFormula
-- binAtomParserSuff op suff = do { lhs <- termParser
--                                ; m_reservedOp op
--                                ; rhs <- termParser
--                                ; m_reservedOp suff
--                                ; return (MonaFormulaAtomic ((show lhs) ++ " " ++ op ++ suff ++ " " ++ (show rhs)))
--                              }


-- parses atomic formulae
atomicFormulaParser :: Parser MonaAtom
atomicFormulaParser = try (binAtomParser "=" (MonaAtomEq))
                  <|> try (binAtomParser "~=" (MonaAtomNeq))
                  <|> try (binAtomParser "<" (MonaAtomLe))
                  <|> try (binAtomParser "<=" (MonaAtomLeq))
                  <|> try (binAtomParser ">" (MonaAtomGe))
                  <|> try (binAtomParser ">=" (MonaAtomGeq))
                  <|> try (binAtomParser "in" (MonaAtomIn))
                  <|> try (binAtomParser "notin" (MonaAtomNotIn))
                  <|> try (binAtomParser "sub" (MonaAtomSub))
                  <?> "atomic formula"


-- parses a "varwhere" string
varWhereParser :: Parser (String, Maybe MonaFormula)
varWhereParser = do { varname <- m_identifier
                    ; phi <- optionMaybe (m_reserved "where" >> formulaParser)
                    ; return (varname, phi)
                    }

-- parses formulae
formulaParser :: Parser MonaFormula
formulaParser = buildExpressionParser formulaOpTable formulaTerm <?> "formula"

-- formula operator table
formulaOpTable = [ [ Prefix (m_reservedOp "~"   >> return MonaFormulaNeg) ]
                 , [ Infix  (m_reservedOp "&"   >> return MonaFormulaConj) AssocLeft ]
                 , [ Infix  (m_reservedOp "|"   >> return MonaFormulaDisj) AssocLeft ]
                 , [ Infix  (m_reservedOp "=>"  >> return MonaFormulaImpl) AssocRight ]
                 , [ Infix  (m_reservedOp "<=>" >> return MonaFormulaEquiv) AssocRight ]
                 ]

formulaTerm :: Parser MonaFormula
formulaTerm = m_parens formulaParser
          <|> do { atom <- atomicFormulaParser
                 ; return $ MonaFormulaAtomic atom
                 }
          <|> (m_reserved "true" >> return (MonaFormulaAtomic $ MonaAtomTrue))
          <|> (m_reserved "false" >> return (MonaFormulaAtomic $ MonaAtomFalse))
          <|> do { m_reserved "sing"
                 ; var <- m_identifier
                 ; return (MonaFormulaAtomic $ MonaAtomSing $ MonaTermVar var )
                 }
          <|> do { m_reserved "empty"
                 ; term <- termParser
                 ; return (MonaFormulaAtomic $ MonaAtomIsEmpty term )
                 }
          <|> do { m_reserved "eps"
                ; var <- m_identifier
                ; return (MonaFormulaAtomic $ MonaAtomEps $ MonaTermVar var )
                }
          <|> do { m_reserved "ex0"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; let varList = map fst varWhereList
                 ; return (MonaFormulaEx0 varList phi)
                 }
          <|> do { m_reserved "ex1"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; return (MonaFormulaEx1 varWhereList phi)
                 }
          <|> do { m_reserved "ex2"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; return (MonaFormulaEx2 varWhereList phi)
                 }
          <|> do { m_reserved "all0"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; let varList = map fst varWhereList
                 ; return (MonaFormulaAll0 varList phi)
                 }
          <|> do { m_reserved "all1"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; return (MonaFormulaAll1 varWhereList phi)
                 }
          <|> do { m_reserved "all2"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; return (MonaFormulaAll2 varWhereList phi)
                 }
          <|> try (do { predname <- m_identifier
                      ; args <- m_parens $ m_commaSep termParam
                      ; return (MonaFormulaPredCall predname $ args)
                      })
          <|> fmap MonaFormulaVar m_identifier
  where
    parseQuantSuffix :: Parser ([(String, Maybe MonaFormula)], MonaFormula)
    parseQuantSuffix = do { varWhereList <- m_commaSep1 varWhereParser
                          ; m_reservedOp ":"
                          ; phi <- formulaParser
                          ; return (varWhereList, phi)
                          }

-- intercalate with commas
commatize :: [String] -> String
commatize list = intercalate ", " list

-- MONA file declarations
data MonaDeclaration
  = MonaDeclFormula MonaFormula
  | MonaDeclVar0 [String]
  | MonaDeclVar1 [(String, Maybe MonaFormula)]
  | MonaDeclVar2 [(String, Maybe MonaFormula)]
  | MonaDeclAllpos String
  | MonaDeclLastpos String
  | MonaDeclDefWhere1 String MonaFormula
  | MonaDeclDefWhere2 String MonaFormula
  | MonaDeclMacro String [MonaMacroParam] MonaFormula
  | MonaDeclPred String [MonaMacroParam] MonaFormula
  | MonaDeclExport String MonaFormula
  | MonaDeclAssert MonaFormula
  | MonaDeclConst MonaAtom

instance Show MonaDeclaration where
  show (MonaDeclFormula phi) = show phi
  show (MonaDeclVar0 varList) = "var0 " ++ (commatize varList)
  show (MonaDeclVar1 varWhereList) = "var1 " ++ showVarWhereClause varWhereList
  show (MonaDeclVar2 varWhereList) = "var2 " ++ showVarWhereClause varWhereList
  show (MonaDeclAllpos var) = "allpos " ++ var
  show (MonaDeclLastpos var) = "lastpos " ++ var
  show (MonaDeclDefWhere1 var phi) = "defaultwhere1(" ++ var ++ ") = " ++ (show phi)
  show (MonaDeclDefWhere2 var phi) = "defaultwhere2(" ++ var ++ ") = " ++ (show phi)
  show (MonaDeclMacro name params phi) = "macro " ++ name ++ "(" ++ (commatize $ map show params) ++ ") = " ++ (show phi)
  show (MonaDeclPred name params phi) = "pred " ++ name ++ "(" ++ (commatize $ map show params) ++ ") = " ++ (show phi)
  show (MonaDeclExport name phi) = "export(\"" ++ name ++ "\", " ++ (show phi) ++ ")"
  show (MonaDeclAssert phi) = "assert " ++ (show phi)
  show (MonaDeclConst atom) = "const "++ (show atom)


showVarWhereClause :: [(String, Maybe MonaFormula)] -> String
showVarWhereClause = commatize . (map showVarWhere)
  where
    showVarWhere (var, whereCl) = var ++
      (case whereCl of
         Nothing  -> ""
         Just phi -> " where " ++ (show phi)
      )

-- representation of a MONA file
data MonaFile
  = MonaFile { mf_domain :: Maybe String
             , mf_decls :: [MonaDeclaration]
             }

instance Show MonaFile where
  show f = (case mf_domain f of
              Nothing  -> ""
              Just dom -> dom ++ ";")
           ++ "\n" ++
           ((unlines . (map (\x -> (show x) ++ ";"))) (mf_decls f))


-- parses a MONA declaration
declarationParser :: Parser MonaDeclaration
declarationParser = do { m_reserved "var0"
                       ; varList <- m_commaSep1 m_identifier
                       ; return (MonaDeclVar0 varList)
                       }
                <|> do { m_reserved "var1"
                       ; varWhereList <- m_commaSep1 varWhereParser
                       ; return (MonaDeclVar1 varWhereList)
                       }
                <|> do { m_reserved "var2"
                       ; varWhereList <- m_commaSep1 varWhereParser
                       ; return (MonaDeclVar2 varWhereList)
                       }
                <|> do { m_reserved "allpos"
                       ; varname <- m_identifier
                       ; return (MonaDeclAllpos varname)
                       }
                <|> do { m_reserved "lastpos"
                       ; varname <- m_identifier
                       ; return (MonaDeclLastpos varname)
                       }
                <|> do { m_reserved "defaultwhere1"
                       ; varname <- m_parens m_identifier
                       ; m_reservedOp "="
                       ; phi <- formulaParser
                       ; return (MonaDeclDefWhere1 varname phi)
                       }
                <|> do { m_reserved "defaultwhere2"
                       ; varname <- m_parens m_identifier
                       ; m_reservedOp "="
                       ; phi <- formulaParser
                       ; return (MonaDeclDefWhere2 varname phi)
                       }
                <|> do { m_reserved "assert"
                       ; phi <- formulaParser
                       ; return (MonaDeclAssert phi)
                       }
                <|> do { m_reserved "const"
                       ; atom <- atomicFormulaParser
                       ; return (MonaDeclConst atom)
                       }
                <|> do { m_reserved "macro"
                       ; name <- m_identifier
                       ; args <- optionMaybe (m_parens $ m_commaSep paramParser)
                       ; let sanArgs = (case args of
                                          Nothing -> []
                                          Just ls -> ls
                                       )
                       ; m_reservedOp "="
                       ; phi <- formulaParser
                       ; return (MonaDeclMacro name sanArgs phi)
                       }
                <|> do { m_reserved "pred"
                       ; name <- m_identifier
                       ; args <- optionMaybe (m_parens $ m_commaSep paramParser)
                       ; let sanArgs = (case args of
                                          Nothing -> []
                                          Just ls -> ls
                                       )
                       ; m_reservedOp "="
                       ; phi <- formulaParser
                       ; return (MonaDeclPred name sanArgs phi)
                       }
                <|> do { m_reserved "export"
                       ; (filename, phi) <- m_parens
                           (do { fn <- m_stringLiteral
                               ; m_comma
                               ; phi' <- formulaParser
                               ; return (fn, phi')
                               }
                           )
                       ; return (MonaDeclExport filename phi)
                       }
                <|> fmap MonaDeclFormula formulaParser
                <?> "declaration"


-- macro parameters
data MonaMacroParam
  = MonaMacroParamVar0 [String]
  | MonaMacroParamVar1 [(String, Maybe MonaFormula)]
  | MonaMacroParamVar2 [(String, Maybe MonaFormula)]
  | MonaMacroParamUniv String

instance Show MonaMacroParam where
  show (MonaMacroParamVar0 varList) = "var0 " ++ (commatize varList)
  show (MonaMacroParamVar1 varWhereList) = "var1 " ++ (showVarWhereClause varWhereList)
  show (MonaMacroParamVar2 varWhereList) = "var2 " ++ (showVarWhereClause varWhereList)


-- parses macro/pred parameters
paramParser :: Parser MonaMacroParam
paramParser = do { m_reserved "var0"
                 ; varWhereList <- parseParamNames
                 ; return (MonaMacroParamVar0 $ map fst varWhereList)
                 }
          <|> do { m_reserved "var1"
                 ; varWhereList <- parseParamNames
                 ; return (MonaMacroParamVar1 varWhereList)
                 }
          <|> do { m_reserved "var2"
                 ; varWhereList <- parseParamNames
                 ; return (MonaMacroParamVar2 varWhereList)
                 }
          <?> "parameter"
  where
    parseParamNames :: Parser [(String, Maybe MonaFormula)]
    parseParamNames = sepBy1 varWhereParser (try parseComma)
    parseComma :: Parser ()
    parseComma = do { m_comma
                    ; notFollowedBy (m_reserved "var0" <|> m_reserved "var1" <|> m_reserved "var2")
                    }


-- parses a MONA file header
headerParser :: Parser String
headerParser = (m_reserved "ws1s" >> return "ws1s")
           <|> (m_reserved "ws2s" >> return "ws2s")
           <|> (m_reserved "m2l-str" >> return "m2l-str")
           <|> (m_reserved "m2l-tree" >> return "m2l-tree")


-- parses a MONA file
monaFileParser :: Parser MonaFile
monaFileParser = do { m_whiteSpace
                    ; domain <- optionMaybe (do { hdr <- headerParser
                                                ; m_semi
                                                ; return hdr
                                             })
                    ; decls <- many1 (declarationParser <* m_semi)
                    ; return MonaFile{mf_domain = domain, mf_decls = decls}
                    }
              <* eof

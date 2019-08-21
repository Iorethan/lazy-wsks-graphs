{-|
Module      : MonaWrapper
Description : Mona formulae wrapper
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaWrapper (
  getBaseFormula
) where

import Data.List
import Data.Maybe

import MonaParser
import MonaFormulaOperation
import MonaFormulaOperationSubst
import MonaFormulaAntiprenex

import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Debug.Trace as Dbg


-- |Convert Mona string containing atom to Logic.Atom
convertAtom :: MonaAtom -> Lo.Atom
convertAtom (MonaAtomEq (MonaTermVar v1) (MonaTermCat (MonaTermVar v2) (MonaTermConst 0))) = Lo.Cat1 v1 v2
convertAtom (MonaAtomEq (MonaTermVar v1) (MonaTermCat (MonaTermVar v2) (MonaTermConst 1))) = Lo.Cat2 v1 v2
convertAtom a@(MonaAtomEq (MonaTermVar v1) t@(MonaTermCat _ _)) =
  case parseSucc t [] of
    Just x -> Lo.TreeConst v1 x
    Nothing -> Lo.MonaAt a (freeVarsAtom a)
  where
    parseSucc (MonaTermRoot) lst = Just lst
    parseSucc (MonaTermCat t (MonaTermConst x)) lst = parseSucc t (x:lst)
    parseSucc t _ = Nothing
convertAtom (MonaAtomEq (MonaTermVar v1) (MonaTermVar v2)) = Lo.Eqn v1 v2
convertAtom (MonaAtomNeq (MonaTermVar v1) (MonaTermVar v2)) = Lo.Neq v1 v2
convertAtom (MonaAtomIn (MonaTermVar v1) (MonaTermVar v2)) = Lo.Subseteq v1 v2
convertAtom (MonaAtomSub (MonaTermVar v1) (MonaTermVar v2)) = Lo.Subseteq v1 v2
convertAtom (MonaAtomSing (MonaTermVar v)) = Lo.Sing v
convertAtom (MonaAtomEps (MonaTermVar v)) = Lo.Eps v
convertAtom MonaAtomTrue = Lo.AtTrue
convertAtom MonaAtomFalse = Lo.AtFalse
convertAtom atom = Lo.MonaAt atom (freeVarsAtom atom)
--convertAtom a = error $ "convertAtom: Unsupported behaviour: " ++ (show a)


-- |Convert Formula in Mona internal type to simplified logic internal type.
convertBaseMonaToFormula :: MonaFormula -> Lo.Formula
convertBaseMonaToFormula (MonaFormulaAtomic atom) = Lo.FormulaAtomic $ convertAtom atom
convertBaseMonaToFormula (MonaFormulaDisj f1 f2) = Lo.Disj (convertBaseMonaToFormula f1) (convertBaseMonaToFormula f2)
convertBaseMonaToFormula (MonaFormulaConj f1 f2) = Lo.Conj (convertBaseMonaToFormula f1) (convertBaseMonaToFormula f2)
convertBaseMonaToFormula (MonaFormulaNeg f) = Lo.Neg $ convertBaseMonaToFormula f
convertBaseMonaToFormula (MonaFormulaEx1 [p] f) = Lo.Exists var $ Lo.Conj (convertBaseMonaToFormula f) (Lo.FormulaAtomic $ Lo.Sing var) where
  var = fst p
convertBaseMonaToFormula (MonaFormulaEx2 [p] f) = Lo.Exists (fst p) (convertBaseMonaToFormula f)
convertBaseMonaToFormula f = error $ "convertBaseMonaToFormula: Unsupported behaviour: " ++ (show f)


-- |Convert MonaFile to siplified logic formula.
getBaseFormula :: MonaFile -> Lo.Formula
getBaseFormula (MonaFile dom decls) = convertBaseMonaToFormula fle where
  (MonaDeclFormula fle) = head $ filter (flt) decls
  flt (MonaDeclFormula f) = True
  flt _ = False


-- |Only for debugging purposes.
flatTest file = do
  mona <- parseFile file
  putStrLn $ show mona
  putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeWhereFile $ unwindQuantifFile $ replaceCallsFile mona

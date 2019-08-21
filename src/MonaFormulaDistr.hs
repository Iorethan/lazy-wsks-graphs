{-|
Module      : MonaFormulaDistr
Description : Mona formulae distributivity
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module MonaFormulaDistr where

import Data.List
import Data.Maybe
import MonaParser
import MonaFormulaOperationSubst

import qualified Data.Map as Map
import qualified Debug.Trace as Dbg


distributeFormula :: [String] -> MonaFormula -> MonaFormula
distributeFormula _ (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
distributeFormula _ f@(MonaFormulaPredCall _ _) = f
distributeFormula _ (MonaFormulaVar var) = MonaFormulaVar var
distributeFormula _ (MonaFormulaNeg f) = MonaFormulaNeg (distributeFormula [] f)
distributeFormula c (MonaFormulaDisj f1 f2) = MonaFormulaDisj (distributeFormula c f1) (distributeFormula c f2)
distributeFormula c (MonaFormulaConj f1 (MonaFormulaDisj f2 f3)) =
  if (length c) /= 0 then MonaFormulaDisj (distributeFormula c (MonaFormulaConj f1 f2)) (distributeFormula c (MonaFormulaConj f1 f3))
  else (MonaFormulaConj (distributeFormula [] f1) (distributeFormula [] (MonaFormulaDisj f2 f3)))
distributeFormula c (MonaFormulaConj (MonaFormulaDisj f2 f3) f1) =
  if (length c) /= 0 then MonaFormulaDisj (distributeFormula c (MonaFormulaConj f2 f1)) (distributeFormula c (MonaFormulaConj f3 f1))
  else MonaFormulaConj (distributeFormula c (MonaFormulaDisj f2 f3)) (distributeFormula c f1)
distributeFormula c (MonaFormulaConj f1 f2) = MonaFormulaConj (distributeFormula [] f1) (distributeFormula [] f2)
distributeFormula c (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (distributeFormula ("x":c) f)
distributeFormula c (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (distributeFormula ("x":c) f)
distributeFormula c (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (distributeFormula ("x":c) f)

--
-- applyConc1 :: (MonaFormula -> MonaFormula)
--   -> (MonaFormula, MonaDeclaration)
--   -> (MonaFormula, MonaDeclaration)
-- applyConc1 f (fr, rr) = (f fr, rr)
--
--
-- applyConc2 :: (MonaFormula -> MonaFormula -> MonaFormula)
--   -> (MonaFormula, MonaDeclaration)
--   -> (MonaFormula, MonaDeclaration)
--   -> (MonaFormula, MonaDeclaration)
-- applyConc2 f (fr1, rr1) (fr2, rr2) = (f fr1 fr2, rr1 ++ rr2)
--
--
getFormulaShare :: Map.Map String Int
  -> [String]
  -> MonaFormula
  -> [MonaDeclaration]
getFormulaShare _ _ (MonaFormulaAtomic atom) = []
getFormulaShare _ _ f@(MonaFormulaPredCall _ _) = []
getFormulaShare _ _ (MonaFormulaVar var) = []
getFormulaShare mp _ (MonaFormulaNeg f) = getFormulaShare mp [] f
getFormulaShare mp c (MonaFormulaDisj f1 f2) = (getFormulaShare mp c f1) ++ (getFormulaShare mp c f2)
getFormulaShare mp c (MonaFormulaConj f1 (MonaFormulaDisj f2 f3)) =
  if (length c) /= 0 then (createPred mp "predTmp" f1):(getFormulaShare mp c (MonaFormulaConj f1 f2)) ++ (getFormulaShare mp c (MonaFormulaConj f1 f3))
  else  (getFormulaShare mp [] f1) ++ (getFormulaShare mp [] (MonaFormulaDisj f2 f3))
getFormulaShare mp c (MonaFormulaConj (MonaFormulaDisj f2 f3) f1) =
  if (length c) /= 0 then (createPred mp "predTmp" f1):(getFormulaShare mp c (MonaFormulaConj f2 f1)) ++ (getFormulaShare mp c (MonaFormulaConj f3 f1))
  else (getFormulaShare mp c (MonaFormulaDisj f2 f3)) ++ (getFormulaShare mp c f1)
getFormulaShare mp c (MonaFormulaConj f1 f2) = (getFormulaShare mp [] f1) ++ (getFormulaShare mp [] f2)
getFormulaShare mp c (MonaFormulaEx0 [var] f) = getFormulaShare (Map.insert var 0 mp) ("x":c) f
getFormulaShare mp c (MonaFormulaEx1 [decl] f) = getFormulaShare (Map.insert (fst decl) 1 mp) ("x":c) f
getFormulaShare mp c (MonaFormulaEx2 [decl] f) = getFormulaShare (Map.insert (fst decl) 2 mp) ("x":c) f


createPred :: Map.Map String Int -> String -> MonaFormula -> MonaDeclaration
createPred mp name f = MonaDeclPred name params f where
  fvs = freeVarsFormula f
  params = map (\x -> conv x $ mp Map.! x) fvs
  conv name 0 = MonaMacroParamVar0 [name]
  conv name 1 = MonaMacroParamVar1 [(name, Nothing)]
  conv name 2 = MonaMacroParamVar2 [(name, Nothing)]


replaceSharedFormula :: Map.Map MonaFormula String
  -> [String]
  -> MonaFormula
  -> MonaFormula
replaceSharedFormula _ _ (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
replaceSharedFormula _ _ f@(MonaFormulaPredCall _ _) = f
replaceSharedFormula _ _ (MonaFormulaVar var) = MonaFormulaVar var
replaceSharedFormula mp _ (MonaFormulaNeg f) = MonaFormulaNeg (replaceSharedFormula mp [] f)
replaceSharedFormula mp c (MonaFormulaDisj f1 f2) = MonaFormulaDisj (replaceSharedFormula mp c f1) (replaceSharedFormula mp c f2)
replaceSharedFormula mp c (MonaFormulaConj f1 (MonaFormulaDisj f2 f3)) =
  if (length c) /= 0 then MonaFormulaDisj (replaceSharedFormula mp c (MonaFormulaConj cl f2)) (replaceSharedFormula mp c (MonaFormulaConj cl f3))
  else (MonaFormulaConj (replaceSharedFormula mp [] f1) (replaceSharedFormula mp [] (MonaFormulaDisj f2 f3))) where
    cl = replaceFormulaPred f1 mp
replaceSharedFormula mp c (MonaFormulaConj (MonaFormulaDisj f2 f3) f1) =
  if (length c) /= 0 then MonaFormulaDisj (replaceSharedFormula mp c (MonaFormulaConj f2 cl)) (replaceSharedFormula mp c (MonaFormulaConj f3 cl))
  else MonaFormulaConj (replaceSharedFormula mp c (MonaFormulaDisj f2 f3)) (replaceSharedFormula mp c f1) where
    cl = replaceFormulaPred f1 mp
replaceSharedFormula mp c (MonaFormulaConj f1 f2) = MonaFormulaConj (replaceSharedFormula mp [] f1) (replaceSharedFormula mp [] f2)
replaceSharedFormula mp c (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (replaceSharedFormula mp ("x":c) f)
replaceSharedFormula mp c (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (replaceSharedFormula mp ("x":c) f)
replaceSharedFormula mp c (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (replaceSharedFormula mp ("x":c) f)


replaceFormulaPred :: MonaFormula -> Map.Map MonaFormula String -> MonaFormula
replaceFormulaPred f mp = MonaFormulaPredCall name params  where
  fvs = freeVarsFormula f
  name = mp Map.! f
  params = map (MonaTermVar) fvs

{-|
Module      : MonaFormulaBalance
Description : Mona formulae balancing
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module MonaFormulaBalance(
  QuantifChain(..)
  , QuantifVarChain
  , balanceFormulaInf
  , flushQuantifChain
  , getChainVarName
  , balanceFormula
  , balanceFormulaInfSplit
) where


import Data.List
import Data.Maybe

import AntiprenexConfig
import MonaParser
import MonaFormulaOperation
import MonaFormulaOperationSubst

import qualified Relation as Rel
import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as Lst
import qualified Data.List.Split as LstSpl
import qualified Debug.Trace as Dbg



-- Chain of quantifiers
data QuantifChain a =
  ForAll0Chain a
  | ForAll1Chain a
  | ForAll2Chain a
  | Exists0Chain a
  | Exists1Chain a
  | Exists2Chain a
  deriving (Eq, Show)


-- Chain of quantifiers with variables
type QuantifVarChain = QuantifChain (String, Maybe MonaFormula)


--------------------------------------------------------------------------------------------------------------
-- Part with the chain quantifiers functions
--------------------------------------------------------------------------------------------------------------

-- |Flush (unfold) a chain of existential quantifiers. Given list of variables,
-- it expands to a chain of existential quatifiers, on the most nested level with
-- formula f.
flushQuantifChain :: [QuantifVarChain] -> MonaFormula -> MonaFormula
flushQuantifChain [] f = f
--flushQuantifChain ((ForAll0Chain x):xs) f = MonaFormulaAll0 [fst x] (flushQuantifChain xs f)
--flushQuantifChain ((ForAll1Chain x):xs) f = MonaFormulaAll1 [x] (flushQuantifChain xs f)
--flushQuantifChain ((ForAll2Chain x):xs) f = MonaFormulaAll2 [x] (flushQuantifChain xs f)
flushQuantifChain ((Exists0Chain x):xs) f = filterQuantifiers (MonaFormulaEx0 [fst x]) (fst x) f $ (flushQuantifChain xs f)
flushQuantifChain ((Exists1Chain x):xs) f = filterQuantifiers (MonaFormulaEx1 [x]) (fst x) f $ (flushQuantifChain xs f)
flushQuantifChain ((Exists2Chain x):xs) f = filterQuantifiers (MonaFormulaEx2 [x]) (fst x) f $ (flushQuantifChain xs f)


filterQuantifiers :: (MonaFormula -> MonaFormula) -> String -> MonaFormula -> (MonaFormula -> MonaFormula)
filterQuantifiers con var f
  | var `elem` (freeVarsFormula f) = con
  | otherwise = id


getChainVarName :: QuantifVarChain -> String
getChainVarName (ForAll0Chain a) = fst a
getChainVarName (ForAll1Chain a) = fst a
getChainVarName (ForAll2Chain a) = fst a
getChainVarName (Exists0Chain a) = fst a
getChainVarName (Exists1Chain a) = fst a
getChainVarName (Exists2Chain a) = fst a


--------------------------------------------------------------------------------------------------------------
-- Part with the uninformed balancing
--------------------------------------------------------------------------------------------------------------

balanceFormula :: MonaFormula -> MonaFormula
balanceFormula f@(MonaFormulaConj _ _) = rebuildFormulaOrd (MonaFormulaConj) $ map (balanceFormula) (getConjList f)
balanceFormula f@(MonaFormulaDisj _ _) = rebuildFormula (MonaFormulaDisj) $ map (balanceFormula) (getDisjList f)
balanceFormula (MonaFormulaNeg f) = MonaFormulaNeg $ balanceFormula f
balanceFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (balanceFormula f)
balanceFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (balanceFormula f)
balanceFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (balanceFormula f)
balanceFormula (MonaFormulaAll0 vars f) = MonaFormulaAll0 vars (balanceFormula f)
balanceFormula (MonaFormulaAll1 decl f) = MonaFormulaAll1 decl (balanceFormula f)
balanceFormula (MonaFormulaAll2 decl f) = MonaFormulaAll2 decl (balanceFormula f)
balanceFormula (MonaFormulaVar var) = MonaFormulaVar var
balanceFormula f@(MonaFormulaAtomic _) = f
balanceFormula f@(MonaFormulaPredCall _ _) = f


rebuildFormula :: (MonaFormula -> MonaFormula -> MonaFormula) -> [MonaFormula] -> MonaFormula
rebuildFormula _ [f] = f
rebuildFormula con xs = con (rebuildFormula con h) (rebuildFormula con t) where
  m = (length xs) `div` 2
  h = take m xs
  t = drop m xs


rebuildFormulaOrd :: (MonaFormula -> MonaFormula -> MonaFormula) -> [MonaFormula] -> MonaFormula
rebuildFormulaOrd _ [f] = f
rebuildFormulaOrd con xs = if (length c2) == 0 then foldl1 (con) c1 else foldl (con) f1 c1 where
  (c1, c2) = Lst.partition (distrSuit) xs
  f1 = rebuildFormula con c2

  distrSuit (MonaFormulaDisj _ _) = True
  distrSuit _ = False




getConjList :: MonaFormula -> [MonaFormula]
getConjList (MonaFormulaConj f1 f2) = (getConjList f1) ++ (getConjList f2)
getConjList v = [v]

getDisjList :: MonaFormula -> [MonaFormula]
getDisjList (MonaFormulaDisj f1 f2) = (getDisjList f1) ++ (getDisjList f2)
getDisjList v = [v]


--------------------------------------------------------------------------------------------------------------
-- Part with the informed balancing
--------------------------------------------------------------------------------------------------------------

type VarFleMap = Map.Map String (Set.Set MonaFormula)
type VarConstr = [(String, String)]

-- getSubFV :: [MonaFormula] -> [(MonaFormula, [String])]
-- getSubFV = map (\x -> (x, freeVarsFormula x))


getSubFVInt :: [String] -> [MonaFormula] -> [(MonaFormula, [String])]
getSubFVInt int = map (\x -> (x, intersect int $ freeVarsFormula x))


getVarSubFleMap :: [(MonaFormula, [String])] -> VarFleMap
getVarSubFleMap = Map.fromListWith (Set.union) . concat . map (switch) where
  switch (f, vars) = [(v, Set.singleton f) | v <- vars]


-- getVarsFromConstr :: VarConstr -> [String]
-- getVarsFromConstr = nub . concat . map (\(x,y) -> [x,y])


getComparableVarsTmp :: [String] -> VarFleMap -> Rel.Relation String String
getComparableVarsTmp vars mp = Set.fromList [(x,y) | x <- vars, y <- vars,
  let phi1 = (mp Map.! x), let phi2 = (mp Map.! y),
  not $ Set.disjoint phi1 phi2, phi1 /= phi2]


getComparableVars :: [String] -> [MonaFormula] -> Rel.Relation String String
getComparableVars vars fs = getComparableVarsTmp vars mp where
  mp = getVarSubFleMap $ getSubFVInt vars fs


getIncomparableVars :: [String] -> Rel.Relation String String -> Rel.Relation String String
getIncomparableVars vars comp = cp Set.\\ (Set.union (Rel.symClosure comp) (Rel.idRel vset))  where
  vset = Set.fromList vars
  cp = Set.cartesianProduct vset vset


-- getConstraints :: [String] -> VarFleMap -> [VarConstr]
-- getConstraints vars mp = sequence $ map (dupl) constr where
--   dupl (x,y) = [(x,y), (y,x)]
--   constr = Set.toList $ getComparableVarsTmp vars mp


-- buildFormulaChain :: [String] -> [MonaFormula] -> MonaFormula
-- buildFormulaChain chain fs = bfc chain fs where
--   bfc [] fs = rebuildFormula (MonaFormulaConj) fs
--   bfc (x:xs) fs = bfc xs fs' where
--     (fs1, fs2) = Lst.partition (\f -> x `elem` (freeVarsFormula f)) fs
--     fs' = (MonaFormulaExGen x $ rebuildFormula (MonaFormulaConj) fs1):fs2


builFormulaList :: [String] -> [MonaFormula] -> [MonaFormula]
builFormulaList chain fs = bfc chain fs where
  bfc [] fs = fs
  bfc (x:xs) fs = bfc xs fs' where
    (fs1, fs2) = Lst.partition (\f -> x `elem` (freeVarsFormula f)) fs
    fs' = fs2 ++ [(MonaFormulaExGen x $ rebuildFormulaOrd (MonaFormulaConj) fs1)]



optimalBalance :: [String] -> [MonaFormula] -> MonaFormula
optimalBalance vars = fst . allComb vars where
  minF [(f,c)] = (f,c)
  minF ((f1, c1):xs) = if c1 <= c2 then (f1, c1) else (f2, c2) where
    (f2, c2) = minF xs
  allComb :: [String] -> [MonaFormula] -> (MonaFormula, Int)
  allComb [] fs = (f', formulaValue 0 f') where
    f' = rebuildFormulaOrd (MonaFormulaConj) fs
  allComb vars fs = minF $ map (applyComb vars fs) lv  where
    comp = getComparableVars vars fs
    rel = getIncomparableVars vars comp
    lv = level vars fs rel

  applyComb vars fs apvar = allComb vars' fs' where
    fs' = builFormulaList apvar fs
    vars' = vars Lst.\\ apvar

  level [] _ _ = []
  level vars@(x:xs) fs incomp = related:(level xs' fs incomp) where
    related = intersect vars $ x:(Set.toList $ Rel.getRelated incomp x)
    xs' = vars Lst.\\ related


balanceFormulaInf ::
  (MonaFormula -> [QuantifVarChain] -> MonaFormula)
  -> MonaFormula
  -> [QuantifVarChain]
  -> MonaFormula
balanceFormulaInf rest (MonaFormulaConj f1 f2) [] = MonaFormulaConj (balanceFormulaInf rest f1 []) (balanceFormulaInf rest f2 [])
balanceFormulaInf rest f [] = rebuildFormulaOrd (MonaFormulaConj) $ map (\x -> rest x []) $ getConjList f
balanceFormulaInf rest f chain = procAntiprenex varmap balfor [] where
  fs = getConjList f
  vars = map (getChainVarName) chain
  varmap = Map.fromList $ zip vars chain
  balfor = optimalBalance (intersect (freeVarsFormula f) vars) fs

  procAntiprenex mp f@(MonaFormulaConj f1 f2) ch = flushQuantifChain ch $ MonaFormulaConj (procAntiprenex mp f1 []) (procAntiprenex mp f2 [])
  procAntiprenex mp (MonaFormulaExGen var f) ch = (procAntiprenex mp f (chainmember:ch)) where
    chainmember = mp Map.! var
  procAntiprenex _ f ch = rest f ch


balanceFormulaInfSplit ::
  (MonaFormula -> [QuantifVarChain] -> MonaFormula)
  -> MonaFormula
  -> [QuantifVarChain]
  -> MonaFormula
balanceFormulaInfSplit rest f [] = balanceFormulaInf rest f []
balanceFormulaInfSplit rest f chain =  balIter rest f divc where
  divc = LstSpl.chunksOf balInforSplitChunks $ reverse chain

  balIter rest fl [] = balanceFormulaInf rest fl []
  balIter rest fl@(MonaFormulaConj _ _) [c] = balanceFormulaInf rest fl c
  balIter rest fl [c] = flushQuantifChain (reverse c) fl
  balIter rest fl (c:xs) = balIter rest (balanceFormulaInf rest fl (reverse c)) xs


--------------------------------------------------------------------------------------------------------------
-- Part with the cost functions
--------------------------------------------------------------------------------------------------------------

formulaValue :: Int -> MonaFormula -> Int
formulaValue d (MonaFormulaExGen _ f) = (formulaCountSubFle f) + (formulaValue (d) f)
formulaValue d (MonaFormulaConj f1 f2) = (formulaValue (d+1) f1) + (formulaValue (d+1) f2)
formulaValue d _ = 0 --1000*d


formulaCountSubFle :: MonaFormula -> Int
formulaCountSubFle (MonaFormulaExGen _ f) = formulaCountSubFle f
formulaCountSubFle (MonaFormulaConj f1 f2) = (formulaCountSubFle f1) + (formulaCountSubFle f2)
formulaCountSubFle _ = 1


formulaValueStruct :: MonaFormula -> Int
formulaValueStruct (MonaFormulaExGen _ f) = (formulaCountSubFleStruct f) + (formulaValueStruct f)
formulaValueStruct (MonaFormulaConj f1 f2) = (formulaValueStruct f1) + (formulaValueStruct f2)
formulaValueStruct _ = 0


formulaCountSubFleStruct :: MonaFormula -> Int
formulaCountSubFleStruct (MonaFormulaExGen _ f) = 4 + (formulaCountSubFleStruct f)
formulaCountSubFleStruct (MonaFormulaConj f1 f2) = (formulaCountSubFleStruct f1) + (formulaCountSubFleStruct f2)
formulaCountSubFleStruct f = subFormulas f

--------------------------------------------------------------------------------------------------------------
-- Part with the debug functions
--------------------------------------------------------------------------------------------------------------

flContainsDBG :: [String] -> MonaFormula
flContainsDBG [x,y] = MonaFormulaAtomic $ MonaAtomSub (MonaTermVar x) (MonaTermVar y)
flContainsDBG (x:y:xs) = MonaFormulaDisj (flContainsDBG [x,y]) $ flContainsDBG (y:xs)


optimalBalanceDBG = do
  let f1 = [flContainsDBG ["X1", "X2"], flContainsDBG ["X2", "X3"], flContainsDBG ["X3", "X1"], flContainsDBG ["X1", "X4"]]
      f2 = [flContainsDBG ["X1", "X2"], flContainsDBG ["X3", "X4"]]
      f3 = [flContainsDBG ["X1", "X2"]]
      vars1 = ["X1", "X2", "X3", "X4"]
      vars2 = ["X1", "X2"]
  putStrLn $ show $ optimalBalance vars1 f1

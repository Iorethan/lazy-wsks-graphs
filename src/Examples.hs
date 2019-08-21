{-|
Module      : Examples
Description : Examples of formulas
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module Examples where

import qualified Logic as Lo

-- |Examples of WSkS formulas.
exampleFormula0 = Lo.Exists "X" (Lo.Neg (Lo.FormulaAtomic (Lo.Sing "X")))
exampleFormula1 = Lo.Neg (Lo.Exists "X" (Lo.Neg (Lo.FormulaAtomic (Lo.Sing "X"))))
exampleFormula2 = Lo.Exists "X" (Lo.Conj (Lo.FormulaAtomic (Lo.Sing "X")) ( Lo.Exists "Y" (Lo.FormulaAtomic (Lo.Cat1 "X" "Y"))))
exampleFormula3 = Lo.Exists "X" (Lo.Conj (Lo.Neg (Lo.FormulaAtomic (Lo.Sing "X"))) (Lo.FormulaAtomic (Lo.Sing "X")))
exampleFormula4 = Lo.Exists "X" (Lo.Exists "Y" (Lo.FormulaAtomic (Lo.Subseteq "X" "Y")))
exampleFormula5 = Lo.Exists "X" (Lo.Exists "Y" (Lo.Conj (Lo.FormulaAtomic (Lo.Eps "X")) (Lo.FormulaAtomic (Lo.Subseteq "X" "Y"))))
exampleFormula6 = Lo.Exists "X" (Lo.Exists "Y" (Lo.Conj (Lo.Conj (Lo.Conj (Lo.FormulaAtomic (Lo.Sing "Y")) (Lo.Neg (Lo.FormulaAtomic (Lo.Eps "Y"))))  (Lo.FormulaAtomic (Lo.Eps "X"))) (Lo.FormulaAtomic (Lo.Subseteq "Y" "X"))))
exampleFormula7 = Lo.Exists "X" (Lo.Exists "Y" (Lo.Conj (Lo.Conj (Lo.FormulaAtomic (Lo.Eps "X")) (Lo.Neg (Lo.FormulaAtomic (Lo.Eps "X")))) (Lo.FormulaAtomic (Lo.Subseteq "X" "Y"))))
exampleFormula8 = Lo.Exists "X" (Lo.Exists "Y" (Lo.Conj (Lo.Conj (Lo.FormulaAtomic (Lo.Sing "Y"))  (Lo.FormulaAtomic (Lo.Eps "X"))) (Lo.FormulaAtomic (Lo.Subseteq "Y" "X"))))

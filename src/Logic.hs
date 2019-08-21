{-|
Module      : Logic
Description : Basic operations for logic formulae
Author      : Ondrej Lengal, Vojtech Havlena, 2018
License     : GPL-3
-}

module Logic where

import MonaParser
import Data.List
import Data.Monoid
import Control.Monad.Writer


-- second-order variable type
type Var = String

type MonaFormulaItem = (String, Formula)

-- Atomic formula
data Atom =
   Sing Var
   | Cat1 Var Var
   | Cat2 Var Var
   | Subseteq Var Var
   | Subset Var Var
   | In Var Var
   | Eps Var
   | Neq Var Var
   | Eqn Var Var
   | MonaAt MonaAtom [Var]
   | AtTrue
   | AtFalse
   | TreeConst Var [Integer]


-- formula type
data Formula =
  FormulaAtomic Atom
  | Disj Formula Formula
  | Conj Formula Formula
  | Neg Formula
  | Exists Var Formula
  | ForAll Var Formula


--------------------------------------------------------------------------------------------------------------
-- Part with a formula print functions
--------------------------------------------------------------------------------------------------------------

-- prints the formula in human-readable format
showFormula :: Formula -> String
showFormula (FormulaAtomic phi) = show phi
showFormula (Disj f1 f2)        = "(" ++ (showFormula f1) ++ ") ∨ (" ++ (showFormula f2) ++ ")"
showFormula (Conj f1 f2)        = "(" ++ (showFormula f1) ++ ") ∧ (" ++ (showFormula f2) ++ ")"
showFormula (Neg f)             = "¬(" ++ (showFormula f) ++ ")"
showFormula (Exists var f)      = "∃" ++ var ++ ". (" ++ (showFormula f) ++ ")"
showFormula (ForAll var f)      = "∀" ++ var ++ ". (" ++ (showFormula f) ++ ")"


-- |Print atom in human-readable format
showAtom :: Atom -> String
showAtom (Sing v) = "Sing(" ++ v ++ ")"
showAtom (Cat1 v1 v2) = v1 ++ "=" ++ v2 ++ ".0"
showAtom (Cat2 v1 v2) = v1 ++ "=" ++ v2 ++ ".1"
showAtom (Subseteq v1 v2) = v1 ++ "⊆" ++ v2
showAtom (Eps v) = v ++ "=ε"
showAtom (Neq v1 v2) = v1 ++ "~=" ++ v2
showAtom (Eqn v1 v2) = v1 ++ "=" ++ v2
showAtom (In v1 v2) = v1 ++ " in " ++ v2
showAtom (Subset v1 v2) = v1 ++ "⊂" ++ v2
showAtom (TreeConst v tree) = v ++ "=" ++ (show tree)
showAtom (MonaAt atom var) = "MA: {" ++ show atom ++ "}"
showAtom AtTrue = "true"
showAtom AtFalse = "false"


-- |Show formula in Mona format.
showFormulaMona :: Formula -> String
showFormulaMona (FormulaAtomic atom) = showAtomMona atom
showFormulaMona (Conj f1 f2) = "(" ++ (showFormulaMona f1) ++ ") & (" ++ (showFormulaMona f2) ++ ")"
showFormulaMona (Disj f1 f2) = "(" ++ (showFormulaMona f1) ++ ") | (" ++ (showFormulaMona f2) ++ ")"
showFormulaMona (Neg f)             = "~(" ++ (showFormulaMona f) ++ ")"
showFormulaMona (Exists var f)      = "ex2 " ++ var ++ ": (" ++ (showFormulaMona f) ++ ")"
showFormulaMona (ForAll var f)      = "all2 " ++ var ++ ": (" ++ (showFormulaMona f) ++ ")"


-- |Show atom in Mona format.
showAtomMona :: Atom -> String
showAtomMona (Subseteq v1 v2) = v1 ++ " sub " ++ v2
showAtomMona (Eqn v1 v2) = v1 ++ " = " ++ v2
showAtomMona (Neq v1 v2) = v1 ++ " ~= " ++ v2
showAtomMona (Cat1 v1 v2) = v1 ++ " = " ++ v2 ++ ".0"
showAtomMona (Cat2 v1 v2) = v1 ++ " = " ++ v2 ++ ".1"
showAtomMona AtTrue = "true"
showAtomMona (MonaAt atom vars) =  show atom
showAtomMona (Sing v) = "sing " ++ show v
--showAtomMona a_= error "Not implemented"


-- instantiance of the data type as class Show
instance Show Formula where
  show = showFormula


-- |For converting atom to string
instance Show Atom where
   show = showAtom


--------------------------------------------------------------------------------------------------------------
-- Part with a conversion logic formula to basic form (without forall)
--------------------------------------------------------------------------------------------------------------

-- removes the universal quantifier
removeForAll :: Formula -> Formula
removeForAll (FormulaAtomic phi) = FormulaAtomic phi
removeForAll (Disj f1 f2)        = Disj (removeForAll f1) (removeForAll f2)
removeForAll (Conj f1 f2)        = Conj (removeForAll f1) (removeForAll f2)
removeForAll (Neg f)             = Neg $ removeForAll f
removeForAll (Exists var f)      = Exists var (removeForAll f)
removeForAll (ForAll var f)      = Neg $ Exists var $ Neg (removeForAll f)


-- |Replace atoms which are not basic.
removeAtoms :: Formula -> Formula
removeAtoms (FormulaAtomic (Neq v1 v2)) = Neg $ FormulaAtomic (Eqn v1 v2)
removeAtoms (FormulaAtomic phi) = FormulaAtomic phi
removeAtoms (Disj f1 f2)        = Disj (removeAtoms f1) (removeAtoms f2)
removeAtoms (Conj f1 f2)        = Conj (removeAtoms f1) (removeAtoms f2)
removeAtoms (Neg f)             = Neg $ removeAtoms f
removeAtoms (Exists var f)      = Exists var (removeAtoms f)
removeAtoms (ForAll var f)      = Neg $ Exists var $ Neg (removeAtoms f)


-- |Replace parts of formula with a special atom denoting that this part is
-- directly converted to TA via Mona.
removeMonaFormulas :: Formula -> Writer [(String, Formula)] Formula
removeMonaFormulas (FormulaAtomic phi) = removeMonaAtom phi >>=
  (\x -> return $ FormulaAtomic x)
removeMonaFormulas (Disj f1 f2) = removeMonaFormulas f1 >>=
  \x -> removeMonaFormulas f2 >>=
  \y -> return $ Disj x y
removeMonaFormulas (Conj f1 f2) = removeMonaFormulas f1 >>=
  \x -> removeMonaFormulas f2 >>=
  \y -> return $ Conj x y
removeMonaFormulas (Neg f) = removeMonaFormulas f >>= \x -> return $ Neg x
removeMonaFormulas (Exists var f) = removeMonaFormulas f >>=
  \x -> return $ Exists var x
removeMonaFormulas (ForAll var f) = removeMonaFormulas f >>=
  \x -> return $ ForAll var x


--removeMonaStop :: Formula -> Writer [(String, Formula)] Formula
--removeMonaStop fle = writer (FormulaAtomic $ MonaAt iden (freeVars fle), [(iden, fle)]) where
--  iden = showFormulaMona fle


-- |Replace certain atoms with a special atom denoting that this part is
-- directly converted to TA via Mona.
removeMonaAtom :: Atom -> Writer [(String, Formula)] Atom
--removeMonaAtom t@(Subseteq v1 v2) = writer (MonaAtom iden [v1,v2], [(iden, FormulaAtomic t)]) where
--  iden = v1++"sub"++v2
-- removeMonaAtom t@(Cat1 v1 v2) = writer (MonaAtom iden [v1,v2], [(iden, FormulaAtomic t)]) where
--   iden = v1++"cat1"++v2
-- removeMonaAtom t@(Cat2 v1 v2) = writer (MonaAtom iden [v1,v2], [(iden, FormulaAtomic t)]) where
--  iden = v1++"cat2"++v2
removeMonaAtom t@(MonaAt atom vars) = writer (t, [(iden, FormulaAtomic t)]) where
  iden = show atom
removeMonaAtom t = return t


-- |Convert to base formula containing only basic atoms and quantifiers.
-- useMona: Use Mona for translating atoms (formulas) to tree automata (atoms
-- are replaced with a special atom representing that Mona is used to obtain TA)
convertMonaSub :: Bool -> Formula -> Writer [(String, Formula)] Formula
convertMonaSub useMona = preproc where
  preproc = if useMona then removeMonaFormulas else return


-- |Simplify formulas containing true, false (tmp function).
simplifyTrueFalseRule :: Formula -> Formula
simplifyTrueFalseRule (Disj (FormulaAtomic AtTrue) fl) = FormulaAtomic AtTrue
simplifyTrueFalseRule (Disj fl (FormulaAtomic AtTrue)) = FormulaAtomic AtTrue
simplifyTrueFalseRule (Conj (FormulaAtomic AtTrue) fl) = fl
simplifyTrueFalseRule (Conj fl (FormulaAtomic AtTrue)) = fl
simplifyTrueFalseRule (Exists _ (FormulaAtomic AtTrue)) = FormulaAtomic AtTrue
simplifyTrueFalseRule (Neg (FormulaAtomic AtTrue)) = FormulaAtomic AtFalse
simplifyTrueFalseRule (Disj (FormulaAtomic AtFalse) fl) = fl
simplifyTrueFalseRule (Disj fl (FormulaAtomic AtFalse)) = fl
simplifyTrueFalseRule (Conj (FormulaAtomic AtFalse) fl) = FormulaAtomic AtFalse
simplifyTrueFalseRule (Conj fl (FormulaAtomic AtFalse)) = FormulaAtomic AtFalse
simplifyTrueFalseRule (Exists _ (FormulaAtomic AtFalse)) = FormulaAtomic AtFalse
simplifyTrueFalseRule (Neg (FormulaAtomic AtFalse)) = FormulaAtomic AtTrue
simplifyTrueFalseRule f = f


-- |Simplify formulas containing true, false.
simplifyTrueFalse :: Formula -> Formula
simplifyTrueFalse (FormulaAtomic at) = FormulaAtomic at
simplifyTrueFalse (Conj f1 f2) = simplifyTrueFalseRule $ Conj (simplifyTrueFalse f1) (simplifyTrueFalse f2)
simplifyTrueFalse (Disj f1 f2) = simplifyTrueFalseRule $ Disj (simplifyTrueFalse f1) (simplifyTrueFalse f2)
simplifyTrueFalse (Neg f) = simplifyTrueFalseRule $ Neg $ simplifyTrueFalse f
simplifyTrueFalse (Exists var f) = simplifyTrueFalseRule $ Exists var (simplifyTrueFalse f)
simplifyTrueFalse (ForAll var f) = simplifyTrueFalseRule $ ForAll var (simplifyTrueFalse f)


-- retrieves free variables of a formula
freeVars :: Formula -> [Var]
freeVars (FormulaAtomic phi) = freeVarsAtom phi
freeVars (Disj f1 f2)   = nub $ (freeVars f1) ++ (freeVars f2)
freeVars (Conj f1 f2)   = freeVars (Disj f1 f2)
freeVars (Neg f)        = freeVars f
freeVars (Exists var f) = delete var $ freeVars f
freeVars (ForAll var f) = freeVars (Exists var f)


-- |Free variables in atoms.
freeVarsAtom :: Atom -> [Var]
freeVarsAtom (Sing x) = [x]
freeVarsAtom (Cat1 x y) = [x,y]
freeVarsAtom (Cat2 x y) = [x,y]
freeVarsAtom (Subseteq x y) = [x,y]
freeVarsAtom (Subset x y) = [x,y]
freeVarsAtom (Eps x) = [x]
freeVarsAtom (Neq x y) = [x,y]
freeVarsAtom (Eqn x y) = [x,y]
freeVarsAtom (In x y) = [x,y]
freeVarsAtom (MonaAt _ vars) = vars
freeVarsAtom AtTrue = []
freeVarsAtom AtFalse = []
freeVarsAtom (TreeConst var _) = [var]

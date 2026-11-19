{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Sound -- soundness on a lasso: a derivable formula evaluates
-- to true at every stage.  It is sound of LTL.Countermodel.LassoEval, taken at
-- the lassos of LTL.Countermodel.Lasso.

module LTL.Countermodel.Sound where

open import LTL.Countermodel.Eval public
import LTL.Countermodel.LassoEval

------------------------------------------------------------------------
-- Soundness on a lasso, at every stage

module _ (P : Formula) where

  soundLasso : (v0 : Val) (l : Lasso P v0) {C : Formula} -> ⊢ C
          -> (i : Nat) -> eval P v0 l C i ≡ true
  soundLasso v0 l d i =
    LTL.Countermodel.LassoEval.sound Val (readVal P) loop d (posIter loop i (v0 , rest))
    where open Lasso l

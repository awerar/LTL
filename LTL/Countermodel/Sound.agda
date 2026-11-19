{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Sound -- soundness on a run: a derivable formula evaluates
-- to true at every stage.  It is sound of LTL.Countermodel.LassoEval, taken at
-- the runs of LTL.Countermodel.Run.

module LTL.Countermodel.Sound where

open import LTL.Countermodel.Eval public
import LTL.Countermodel.LassoEval

------------------------------------------------------------------------
-- Soundness on a run, at every stage

module _ (P : Formula) where

  soundRun : (v0 : Val) (r : Run P v0) {C : Formula} -> ⊢ C
          -> (i : Nat) -> eval P v0 r C i ≡ true
  soundRun v0 r d i =
    LTL.Countermodel.LassoEval.sound Val (readVal P) c0 c1 d (posIter c0 c1 i (v0 , rest))
    where open Run r

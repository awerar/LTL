{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sound -- G26 of FORMALISATION-PLAN.md.
--
--   "One checks by induction on derivations that |- C implies [[C]]_s = 1 at
--    every state of every lasso."                          -- m4.tex section 5
--
-- The induction is LTL.LassoEval's sound, which holds on every lasso with
-- states of any type and at every position.  Here it is taken at the runs of
-- LTL.Run, at every stage.

module LTL.Sound where

open import LTL.Eval public
import LTL.LassoEval

------------------------------------------------------------------------
-- Soundness on a run, at every stage

module _ (P : Formula) where

  soundRun : (v0 : Val) (r : Run P v0) {C : Formula} -> ⊢ C
          -> (i : Nat) -> eval P v0 r C i ≡ true
  soundRun v0 r d i =
    LTL.LassoEval.sound Val (readVal P) c0 c1 d (posIter c0 c1 i (v0 , rest))
    where open Run r

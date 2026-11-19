{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Lasso -- the fulfilling lasso of Proposition 5.3 of m4.tex.
--
--   a finite path v_0 -> ... -> v_p followed by a cycle
--   v_p -> ... -> v_q = v_p such that every eventuality pending at a state of
--   the cycle is fulfilled at a state of the cycle.
--
-- This module only states what such a lasso is.  The one that the development
-- builds comes from a fair component of the state graph: sccLasso of
-- LTL.SCC.SccLasso reads the FairLoop of LTL.SCC.Graph as a Lasso, and runOf
-- (LTL.Countermodel.Run) unwinds it into the Run that Hintikka's lemma and
-- soundness are stated on.
--
-- Every side condition is against U_inf P: the base point b lies in it, and
-- both walks stay inside it.  The cycle is non-empty, so that it contains at
-- least one transition, and every eventuality pending at a state of the cycle
-- (b included) is fulfilled at a state the cycle visits.

module LTL.Countermodel.Lasso where

open import LTL.Countermodel.Walk public

------------------------------------------------------------------------
-- The lasso

record Lasso (P : Formula) (v0 : Val) : Set where
  constructor mkLasso
  field
    b             : Val   -- where the cycle starts and ends
    bIn           : b ∈ Uinf P
    stem          : List Val
    stemWalk      : Walk P (Uinf P) v0 stem b
    cycle         : List Val
    cycleWalk     : Walk P (Uinf P) b cycle b
    cycleNonEmpty : null cycle ≡ false
    fulfilled     : AllFulfilled P b cycle (b ∷ cycle)

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Lasso -- a fulfilling lasso from v0: a stem from v0 to b,
-- and a non-empty cycle from b back to b, such that every eventuality pending
-- at a state of the cycle is fulfilled at a state of the cycle.
--
-- All states lie in Uinf P.  sccLasso (LTL.SCC.SccLasso) builds one from a
-- fair loop of the state graph, and runOf (LTL.Countermodel.Run) unwinds it
-- into a Run.

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

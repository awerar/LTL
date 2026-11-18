{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Eval -- G25 of FORMALISATION-PLAN.md.
--
-- The Boolean evaluation of LTL.LassoEval on the runs the elimination builds:
-- the states are valuations, and a variable is read off the state through
-- valOf.  For a variable not occurring in Sub(P) this gives false -- indexOf
-- returns length (sub P), off the end of the vector -- which is a perfectly
-- good valuation; soundness needs the evaluation to be total on ALL formulas,
-- not only on subformulas of P, since a derivation may mention anything.
--
-- evalAt P has the same five clauses as LassoEval's evalAt, definitionally, so
-- everything that computes with it (Hintikka's lemma, the refl checks) sees
-- ¬ᵇ, ⇒ᵇ, nextPos and all over orbitOf exactly as before.  eval then indexes
-- by a Nat, as the plan asks, by iterating the successor that many times from
-- the start of the run.

module LTL.Eval where

open import LTL.Global public
import LTL.LassoEval

------------------------------------------------------------------------
-- The Boolean evaluation at a position

-- a valuation read as an assignment to the variables
readVal : Formula -> Val -> Nat -> Bool
readVal P v n = valOf P v (var n)

module _ (P : Formula) where

  open LTL.LassoEval Val (readVal P) public
    using (evalAt; eval□-at; eval□-intro; eval□-false)

  ------------------------------------------------------------------------
  -- The evaluation on a run, indexed as in the note's unwinding

  eval : (v0 : Val) -> Run P v0 -> Formula -> Nat -> Bool
  eval v0 r A i = evalAt c0 c1 A (posIter c0 c1 i (v0 , rest))
    where open Run r

  ------------------------------------------------------------------------
  -- Running it.
  --
  -- evalOn P v e A i evaluates A at stage i of the lasso built from the named
  -- surviving state v.  It is the whole pipeline in one expression: the states,
  -- the elimination, Proposition 5.3, the unwinding, and the Boolean semantics.

  evalOn : (v : Val) -> v ∈ᵛ Uinf P ≡ true
        -> Formula -> Nat -> Bool
  evalOn v e A i = eval v (runOf P v m (lasso P v m)) A i
    where
      m : v ∈ Uinf P
      m = ∈ᵛ-sound v (Uinf P) e

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Eval -- the evaluation of LTL.Countermodel.LassoEval on the
-- runs of LTL.Countermodel.Run.
--
-- A variable is read off the state through valOf.  For a variable not in sub
-- P this gives false (indexOf runs off the end of the vector), so the
-- evaluation is total on all formulas, as soundness needs.  eval indexes a run
-- by a stage number, iterating the successor from the start.

module LTL.Countermodel.Eval where

open import LTL.Countermodel.Global public
import LTL.Countermodel.LassoEval

------------------------------------------------------------------------
-- The Boolean evaluation at a position

-- a valuation read as an assignment to the variables
readVal : Formula -> Val -> Nat -> Bool
readVal P v n = valOf P v (var n)

module _ (P : Formula) where

  open LTL.Countermodel.LassoEval Val (readVal P) public
    using (evalAt; eval□-at; eval□-intro; eval□-false)

  ------------------------------------------------------------------------
  -- The evaluation on a run, at stage i

  eval : (v0 : Val) -> Run P v0 -> Formula -> Nat -> Bool
  eval v0 r A i = evalAt loop A (posIter loop i (v0 , rest))
    where open Run r

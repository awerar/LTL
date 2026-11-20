{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Eval -- the evaluation of LTL.Countermodel.OrbitEval on the
-- lassos of LTL.Countermodel.Lasso.
--
-- A variable is read off the state through valOf.  For a variable not in sub
-- P this gives false (indexOf runs off the end of the vector), so the
-- evaluation is total on all formulas, as soundness needs.  eval indexes a
-- lasso by a stage number, iterating the successor from the start.

open import LTL.Syntax.Formula using (Formula)

module LTL.Countermodel.Eval (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.Countermodel.Lasso P
import LTL.Countermodel.OrbitEval

------------------------------------------------------------------------
-- The Boolean evaluation at a position

-- a valuation read as an assignment to the variables
readVal : Val -> Nat -> Bool
readVal v n = valOf v (var n)

open LTL.Countermodel.OrbitEval Val readVal public
  using (evalAt; eval□-at; eval□-intro; eval□-false)

------------------------------------------------------------------------
-- The evaluation on a lasso, at stage i

eval : (v0 : Val) -> Lasso v0 -> Formula -> Nat -> Bool
eval v0 l A i = evalAt loop A (posIter loop i (v0 , rest))
  where open Lasso l

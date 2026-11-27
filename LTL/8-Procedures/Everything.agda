{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.8-Procedures.Everything -- the whole procedure, for importers outside it.
--
-- The P-modules are parameterised by the formula P, and Decide by the input
-- Q.  This module opens all of them unapplied and re-exports them, so every
-- name takes its formula first: allStates P, Lasso P v0, Cert P fs ws, decide Q.
-- LTL.8-Procedures.Correct, LTL.Pretty, the tests and the benchmarks import
-- this module.

module LTL.8-Procedures.Everything where

open import LTL.5-States.Common           public
open import LTL.5-States.RowFinite        public
open import LTL.5-States.Valuation        public
open import LTL.5-States.Taut             public
open import LTL.5-States.State            public
open import LTL.5-States.Step             public
open import LTL.5-States.StepLemma        public
open import LTL.5-States.Closure          public
open import LTL.5-States.Extract          public
open import LTL.5-States.CompletePC   public
open import LTL.6-Countermodel.Walk       public
open import LTL.6-Countermodel.Lasso      public
open import LTL.6-Countermodel.Hintikka   public
open import LTL.7-SCC.SccLasso            public
open import LTL.7-SCC.SccExtract          public
open import LTL.7-SCC.SccSeed             public
open import LTL.8-Procedures.Answer       public
open import LTL.8-Procedures.Inspect      public
open import LTL.8-Procedures.Decide       public

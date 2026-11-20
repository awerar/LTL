{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Procedures.Everything -- the whole procedure, for importers outside it.
--
-- The P-modules are parameterised by the formula P, and Decide by the input
-- Q.  This module opens all of them unapplied and re-exports them, so every
-- name takes its formula first: St P, Lasso P v0, Cert P fs ws, decide Q.
-- LTL.Correct, LTL.Pretty, the tests and the benchmarks import this module.

module LTL.Procedures.Everything where

open import LTL.States.Common           public
open import LTL.States.VecBar           public
open import LTL.States.Taut             public
open import LTL.States.State            public
open import LTL.States.Step             public
open import LTL.States.Proj             public
open import LTL.States.Complete         public
open import LTL.States.StepLemma        public
open import LTL.States.Closure          public
open import LTL.States.Extract          public
open import LTL.Procedures.CompletePC   public
open import LTL.Countermodel.Walk       public
open import LTL.Countermodel.Lasso      public
open import LTL.Countermodel.Hintikka   public
open import LTL.SCC.SccLasso            public
open import LTL.SCC.SccExtract          public
open import LTL.SCC.SccSeed             public
open import LTL.Procedures.Answer       public
open import LTL.Procedures.Decide       public

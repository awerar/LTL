{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.8-Procedures.Everything -- the whole procedure, for importers outside it.
--
-- The P-modules are parameterised by the formula P, and Decide by the input
-- Q.  This module opens all of them unapplied and re-exports them, so every
-- name takes its formula first: St P, Lasso P v0, Cert P fs ws, decide Q.
-- LTL.Correct, LTL.Pretty, the tests and the benchmarks import this module.
-- It also re-exports LTL.1-Lib.CertStep, the type of Decide's sccShape.

module LTL.8-Procedures.Everything where

open import LTL.5-States.Common           public
open import LTL.5-States.VecBar           public
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
open import LTL.1-Lib.CertStep            public

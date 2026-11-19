{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Correct -- decideSCC meets the specification of LTL.Trusted.
--
-- A DecisionProcedure answers true only for formulas valid on every lasso, and
-- false only with a lasso on which the formula fails.  fromDecider
-- (LTL.Semantics) turns decideSCC into one.  Formula is LTL.Trusted's own
-- datatype, so the statement is about the formulas the procedure runs on.

module LTL.Correct where

open import LTL.Procedures.DecideSCC public
open import LTL.Semantics public
import LTL.Trusted as T

decideSCCCorrect : T.DecisionProcedure
decideSCCCorrect = fromDecider decideSCC

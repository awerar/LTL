{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Correct -- the statement of LTL.Trusted, proved for the decision
-- procedure of the development.
--
-- LTL.Trusted is the hand-checked specification: a DecisionProcedure answers
-- true only for formulas valid on every lasso, and false only with a lasso on
-- which the formula fails.  decideSCC (LTL.Procedures.DecideSCC, m5.tex: fair
-- strongly connected components) returns  ⊢ Q ⊎ LassoCountermodel Q , and
-- fromDecider (LTL.Semantics) turns any such function into a
-- DecisionProcedure.  Formula here IS LTL.Trusted's Formula (LTL.Syntax.Formula
-- re-exports it), so the statement is proved about the formulas the procedure
-- actually runs on.

module LTL.Correct where

open import LTL.Procedures.DecideSCC public
open import LTL.Semantics public
import LTL.Trusted as T

decideSCCCorrect : T.DecisionProcedure
decideSCCCorrect = fromDecider decideSCC

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Correct -- the statement of LTL.Trusted, proved for every decision
-- procedure of the development.
--
-- LTL.Trusted is the hand-checked specification: a DecisionProcedure answers
-- true only for formulas valid on every lasso, and false only with a lasso on
-- which the formula fails.  The three procedures,
--
--   decide     (LTL.Procedures.Decide,    Theorem 6.1 of m4.tex: state elimination)
--   decideSCC  (LTL.Procedures.DecideSCC, m5.tex: fair strongly connected components)
--   decidePC   (LTL.Procedures.ShortPC,   decide with short (PC) certificates)
--
-- all return  ⊢ Q ⊎ LassoCountermodel Q , and fromDecider (LTL.Semantics)
-- turns any such function into a DecisionProcedure.  Formula here IS
-- LTL.Trusted's Formula (LTL.Syntax.Formula re-exports it), so the statement is
-- proved about the formulas the procedures actually run on.

module LTL.Correct where

open import LTL.Procedures.DecideSCC public
open import LTL.Procedures.ShortPC   public
open import LTL.Semantics public
import LTL.Trusted as T

decideCorrect : T.DecisionProcedure
decideCorrect = fromDecider decide

decideSCCCorrect : T.DecisionProcedure
decideSCCCorrect = fromDecider decideSCC

decidePCCorrect : T.DecisionProcedure
decidePCCorrect = fromDecider decidePC

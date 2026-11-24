{-# OPTIONS --safe --without-K --exact-split #-}

-- This file states that the proof statement holds, and like LTL.Statement it
-- may only be modified by hand.
--
-- LTL.Main -- the development meets LTL.Statement.
--
-- Statement's record Statement collects the obligations: a decision
-- procedure, and that derivability and having a lasso countermodel each
-- coincide with (in)validity.  If this module typechecks, they hold.  --safe
-- is coinfective, so every module it imports is --safe too: no postulates and
-- no unchecked termination anywhere below.  Reviewing the result means
-- reading LTL.Statement and this file.

module LTL.Main where

import LTL.Statement as S
open import LTL.8-Procedures.Correct using (decideCorrect; deriveComplete; countermodelComplete)

statement : S.Statement
statement = record
  { procedure            = decideCorrect
  ; deriveComplete       = deriveComplete
  ; countermodelComplete = countermodelComplete
  }

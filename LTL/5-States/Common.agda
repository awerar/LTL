{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Common -- the formula-independent base of the P-modules.
--
-- The modules from LTL.5-States.State to LTL.7-SCC.SccSeed are parameterised by
-- the formula P.  What they share that does not mention P is opened from
-- here, so that an importer who opens them unapplied does not see a spurious
-- P argument: the derived rules (LTL.3-Rules.Temporal, with the refutation
-- lemmas refute and refute○) and the set layer (LTL.1-Lib.Sets,
-- LTL.1-Lib.Exhaustible).  The module only re-exports.  The valuations of P,
-- with positions over them, are LTL.5-States.Valuation, a P-module, so a
-- P-module opens this module, Valuation at P, and its other P-modules.

module LTL.5-States.Common where

open import LTL.3-Rules.Temporal  public
open import LTL.1-Lib.Sets        public
open import LTL.1-Lib.Exhaustible public

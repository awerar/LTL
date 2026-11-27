{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Reach -- the valuations of P as a set.
--
-- A valuation of P is a row over its atoms (LTL.2-Syntax.Skel), so its type
-- names the formula its bits are about.  This module instantiates
-- LTL.1-Lib.Nodes at their equality test valEq (rowEq of
-- LTL.5-States.RowFinite), which supplies ≡ᵛ, ∈ᵛ, ≢ᵛ, the hypothesis names
-- (Closed, All, ...) and listFinite, and LTL.4-Semantics.Orbit at Val, which
-- supplies positions.  It is the one P-module the others open that
-- re-exports: what it re-exports is the base they all share, and no other
-- P-module re-exports Nodes or Orbit.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.Reach (P : Formula) where

open import LTL.2-Syntax.Deriv
open import LTL.1-Lib.DecEq using (DecEq)
open import LTL.5-States.RowFinite using (rowEq)

------------------------------------------------------------------------
-- Valuations: a bit for each atom of P (LTL.5-States.State's stateAtoms).

Val : Set
Val = Row (atoms P)

valEq : DecEq Val
valEq = rowEq (atoms P)

-- The set layer, at Val.  ∈ᵛ comes from here:  v ∈ᵛ us = any (v ≡ᵛ_) us .

open import LTL.1-Lib.Nodes valEq public

-- Positions and orbits of LTL.4-Semantics.Orbit, at valuations.

open import LTL.4-Semantics.Orbit Val public

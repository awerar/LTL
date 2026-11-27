{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.7-SCC.SccSeed -- every state of Ust is reached from a state containing
-- P (ustSeedTo).
--
-- The graph search covers all of Ust P, so a fair component can lie anywhere
-- in it; this lemma gives the countermodel a start that contains P, with a
-- stem from there to the component.  Ust is a growing search seeded by
-- containsP, so closureSeeded (LTL.1-Lib.Graph) gives a seed and a trail
-- inside St P, and reachesInto moves it into Ust using ustClosed.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.7-SCC.SccSeed (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.Valuation P
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.Closure P
open import LTL.6-Countermodel.Walk P

ustSeedTo : ∀[ w ∈ Ust ] Seeded containsP Ust w
ustSeedTo w m =
  seededBy seed mu seedHolds (reachesInto ustClosed mu reaches)
  where
    open Seeded (closureSeeded containsP St stInPool stateFinite w m)

    mu : seed ∈ Ust
    mu = ustSeed seedIn seedHolds

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.7-SCC.SccSeed -- every state of Ust is reached from a state containing
-- P (ustSeedTo).
--
-- The graph search covers all of Ust P, so a fair component can lie anywhere
-- in it; this lemma gives the countermodel a start that contains P, with a
-- stem from there to the component.  Ust is a growing search seeded by
-- containsP, so closureSeeded (LTL.1-Lib.Graph) gives a seed and a trail
-- inside St P, and seedTrail lifts the trail into Ust using ustClosed.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.7-SCC.SccSeed (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.Closure P
open import LTL.6-Countermodel.Walk P

-- A trail of states out of Ust stays in Ust P.

seedTrail : {s : Val} {zs : List Val} {w : Val}
         -> s ∈ Ust -> Trail St s zs w
         -> Trail Ust s zs w
seedTrail ms tNil                   = tNil
seedTrail ms (tCons {x = y} m e t) = tCons my e (seedTrail my t)
  where
    my : y ∈ Ust
    my = ustClosed ms m e

ustSeedTo : ∀[ w ∈ Ust ] Seeded containsP Ust w
ustSeedTo w m =
  seededBy seed mu seedHolds (reachesBy via (seedTrail mu trail))
  where
    open Seeded (closureSeeded containsP St stAllSat vecBar w m)
    open Reaches reaches

    mu : seed ∈ Ust
    mu = ustSeed seedIn seedHolds

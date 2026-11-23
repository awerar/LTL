{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.State -- which valuations are states, St, the list of all
-- states, and the characteristic formulas chi and beta.
--
-- A valuation is a row of bits over the ATOMS of sub P (its var, ○ and □
-- subformulas, without repetition), and valOf reads any subformula from it
-- by the skeleton evaluation valFrom of LTL.Syntax.Skel.  So (S1), that a
-- state respects ¬ and ⇒, holds by definition, and the one remaining
-- condition is (S2): □ A in v implies A in v.  chi v has one literal per
-- entry of sub P; where sub P repeats a formula, chi repeats the literal.
--
-- This module and the ones built on it (Step, StepLemma, ..., SccSeed) are
-- parameterised by P, the formula whose subformulas index the valuations.  They
-- open each other at P privately and re-export nothing: an importer outside
-- opens them unapplied, which gives every name P as its first argument.

open import LTL.Syntax.Formula using (Formula)

module LTL.States.State (P : Formula) where

open import LTL.Syntax.Val
open import LTL.Lib.Sets using (filter-sub)

------------------------------------------------------------------------
-- Reading a valuation

-- The positions of a valuation.
stateAtoms : List Formula
stateAtoms = atoms (sub P)

valOf : Val -> Formula -> Bool
valOf v A = valFrom stateAtoms v A

------------------------------------------------------------------------
-- The characteristic formula chi v of a valuation, and beta vs, the
-- disjunction of chi over a list of valuations.

-- The literal of A that v makes true.
litOf : Val -> Formula -> Formula
litOf v A = lit A (valOf v A)

chi : Val -> Formula
chi v = ⋀ (map (litOf v) (sub P))

beta : List Val -> Formula
beta vs = ⋁ (map chi vs)

------------------------------------------------------------------------
-- (S2), imposed at each eventuality.  var and ○ carry no local condition:
-- ○ is handled by the transition relation (LTL.States.Step).

s2At : Val -> Formula -> Bool
s2At v A = valOf v (□ A) ⇒ᵇ valOf v A

isState : Val -> Bool
isState v = all (s2At v) (□Args (sub P))

St : List Val
St = filter isState (allVecs (length stateAtoms))

-- Every state has the length the search's Bar expects.

stLen : {v : Val} -> v ∈ St -> length v ≡ length stateAtoms
stLen {v} m =
  allVecs-len (length stateAtoms) v (filter-sub isState (allVecs (length stateAtoms)) m)

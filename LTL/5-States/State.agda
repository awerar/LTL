{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.State -- which valuations are states, St, the list of all
-- states, and the characteristic formulas chi and beta.
--
-- A valuation is a row of bits over the ATOMS of sub P (its var, ○ and □
-- subformulas, without repetition), and valOf reads any subformula from it
-- by the skeleton evaluation valFrom of LTL.2-Syntax.Skel.  So (S1), that a
-- state respects ¬ and ⇒, holds by definition, and the one remaining
-- condition is (S2): □ A in v implies A in v.  chi v has one literal per
-- subformula of P.  The eventualities and the arguments of ○ are read off
-- the atoms, so each is listed once.
--
-- This module and the ones built on it (Step, StepLemma, ..., SccSeed) are
-- parameterised by P, the formula whose subformulas index the valuations.  They
-- open each other at P privately and re-export nothing: an importer outside
-- opens them unapplied, which gives every name P as its first argument.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.State (P : Formula) where

open import LTL.2-Syntax.Val
open import LTL.1-Lib.Sets using (filter-sub)

------------------------------------------------------------------------
-- Reading a valuation

-- The positions of a valuation.
stateAtoms : List Formula
stateAtoms = atoms (sub P)

valOf : Val -> Formula -> Bool
valOf v A = valFrom stateAtoms v A

-- The subformulas of P, each once.
subformulas : List Formula
subformulas = nub (sub P)

------------------------------------------------------------------------
-- The eventualities (the A with □ A in sub P) and the arguments of ○, each
-- once, with their round trips to sub P.

eventualities : List Formula
eventualities = □Args stateAtoms

nexts : List Formula
nexts = ○Args stateAtoms

evIn : {A : Formula} -> □ A ∈ sub P -> A ∈ eventualities
evIn m = □Args-of stateAtoms (atomMem (sub P) m refl)

evSub : ∀ⁱ[ A ∈ eventualities ] □ A ∈ sub P
evSub m = atomSub (sub P) (□Args-mem stateAtoms m)

nextIn : {A : Formula} -> ○ A ∈ sub P -> A ∈ nexts
nextIn m = ○Args-of stateAtoms (atomMem (sub P) m refl)

nextSub : ∀ⁱ[ A ∈ nexts ] ○ A ∈ sub P
nextSub m = atomSub (sub P) (○Args-mem stateAtoms m)

------------------------------------------------------------------------
-- The characteristic formula chi v of a valuation, and beta vs, the
-- disjunction of chi over a list of valuations.

-- The literal of A that v makes true.
litOf : Val -> Formula -> Formula
litOf v A = lit A (valOf v A)

chi : Val -> Formula
chi v = ⋀ (map (litOf v) subformulas)

beta : List Val -> Formula
beta vs = ⋁ (map chi vs)

------------------------------------------------------------------------
-- (S2), imposed at each eventuality.  var and ○ carry no local condition:
-- ○ is handled by the transition relation (LTL.5-States.Step).

s2At : Val -> Formula -> Bool
s2At v A = valOf v (□ A) ⇒ᵇ valOf v A

isState : Val -> Bool
isState v = all (s2At v) eventualities

St : List Val
St = filter isState (allVecs (length stateAtoms))

-- Every state has the length the search's Bar expects.

stLen : ∀ⁱ[ v ∈ St ] length v ≡ length stateAtoms
stLen {v} m =
  allVecs-len (length stateAtoms) v (filter-sub isState (allVecs (length stateAtoms)) m)

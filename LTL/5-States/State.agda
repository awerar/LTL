{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.State -- which valuations are states, the list allStates of
-- them, and the characteristic formulas chi and beta.
--
-- A valuation v is a row of bits over the ATOMS of P (its var, ○ and □
-- subformulas, without repetition), and holdsIn v reads any formula as
-- propValue at readingOf v (LTL.5-States.Valuation) -- the skeleton
-- evaluation of LTL.2-Syntax.Skel, the one LTL.Statement's (PC) uses.  So
-- (S1), that a state respects ¬ and ⇒, holds by definition, and the one
-- remaining condition is (S2): □ A in v implies A in v.  chi v has one
-- literal per atom, the bits of v, rather than one per subformula as in m4:
-- the atoms fix the rest, and LTL.5-States.Taut's tautProj projects any
-- subformula's literal in one pc node.  The eventualities and the arguments
-- of ○ are read off the atoms, so each is listed once.
--
-- This module and the ones built on it (Step, StepLemma, ..., SccSeed) are
-- parameterised by P, the formula whose atoms index the valuations.  They
-- open each other at P privately and re-export nothing: an importer outside
-- opens them unapplied, which gives every name P as its first argument.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.State (P : Formula) where

open import LTL.2-Syntax.Deriv
open import LTL.5-States.Valuation P using (Val; holdsIn)

------------------------------------------------------------------------
-- The eventualities (the A with □ A in sub P) and the arguments of ○, each
-- once, with their round trips to sub P.

eventualities : List Formula
eventualities = concatMap □Arg (atoms P)

nexts : List Formula
nexts = concatMap ○Arg (atoms P)

evIn : {A : Formula} -> □ A ∈ sub P -> A ∈ eventualities
evIn m = ∈-concatMap⁺ □Arg (∈-atoms⁺ P _ m refl) here

evSub : ∀ⁱ[ A ∈ eventualities ] □ A ∈ sub P
evSub {A} m with ∈-concatMap⁻ □Arg (atoms P) m
... | X , mX , k = atomSub P (subst (λ Y -> Y ∈ atoms P) (□Arg-inv X k) mX)

nextIn : {A : Formula} -> ○ A ∈ sub P -> A ∈ nexts
nextIn m = ∈-concatMap⁺ ○Arg (∈-atoms⁺ P _ m refl) here

nextSub : ∀ⁱ[ A ∈ nexts ] ○ A ∈ sub P
nextSub {A} m with ∈-concatMap⁻ ○Arg (atoms P) m
... | X , mX , k = atomSub P (subst (λ Y -> Y ∈ atoms P) (○Arg-inv X k) mX)

------------------------------------------------------------------------
-- The characteristic formula chi v of a valuation, and beta vs, the
-- disjunction of chi over a list of valuations.

-- The literal of A that v makes true.
litOf : Val -> Formula -> Formula
litOf v A = lit A (holdsIn v A)

-- The atoms of P, each signed by its bit in v (lits, LTL.2-Syntax.Skel).
chi : Val -> Formula
chi v = ⋀ (lits v)

beta : List Val -> Formula
beta vs = ⋁ (map chi vs)

------------------------------------------------------------------------
-- (S2), imposed at each eventuality.  var and ○ carry no local condition:
-- ○ is handled by the transition relation (LTL.5-States.Step).

s2At : Val -> Formula -> Bool
s2At v A = holdsIn v (□ A) ⇒ᵇ holdsIn v A

isState : Val -> Bool
isState v = all (s2At v) eventualities

-- All the states: the valuations meeting (S2).  St in m4.
allStates : List Val
allStates = filter isState (rows (atoms P))

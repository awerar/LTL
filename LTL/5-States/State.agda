{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.State -- which valuations are states, St, the list of all
-- states, and the characteristic formulas chi and beta.
--
-- A valuation v is a row of bits over the ATOMS of P (its var, ○ and □
-- subformulas, without repetition; LTL.5-States.Reach), and valOf v reads
-- any formula as propValue at the reading atomBit v -- the skeleton
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
open import LTL.5-States.Reach P using (Val)

------------------------------------------------------------------------
-- Reading a valuation

-- The positions of a valuation: Val is Row stateAtoms.
stateAtoms : List Formula
stateAtoms = atoms P

-- What v says of a formula: its bit at an atom, and ¬ᵇ and ⇒ᵇ above.
valOf : Val -> Formula -> Bool
valOf v = propValue (atomBit v)

------------------------------------------------------------------------
-- The eventualities (the A with □ A in sub P) and the arguments of ○, each
-- once, with their round trips to sub P.

eventualities : List Formula
eventualities = concatMap □Arg stateAtoms

nexts : List Formula
nexts = concatMap ○Arg stateAtoms

evIn : {A : Formula} -> □ A ∈ sub P -> A ∈ eventualities
evIn m = ∈-concatMap⁺ □Arg (∈-atoms⁺ P _ m refl) here

evSub : ∀ⁱ[ A ∈ eventualities ] □ A ∈ sub P
evSub {A} m with ∈-concatMap⁻ □Arg stateAtoms m
... | X , mX , k = atomSub P (subst (λ Y -> Y ∈ stateAtoms) (□Arg-inv X k) mX)

nextIn : {A : Formula} -> ○ A ∈ sub P -> A ∈ nexts
nextIn m = ∈-concatMap⁺ ○Arg (∈-atoms⁺ P _ m refl) here

nextSub : ∀ⁱ[ A ∈ nexts ] ○ A ∈ sub P
nextSub {A} m with ∈-concatMap⁻ ○Arg stateAtoms m
... | X , mX , k = atomSub P (subst (λ Y -> Y ∈ stateAtoms) (○Arg-inv X k) mX)

------------------------------------------------------------------------
-- The characteristic formula chi v of a valuation, and beta vs, the
-- disjunction of chi over a list of valuations.

-- The literal of A that v makes true.
litOf : Val -> Formula -> Formula
litOf v A = lit A (valOf v A)

chi : Val -> Formula
chi v = ⋀ (map (litOf v) stateAtoms)

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
St = filter isState (rows stateAtoms)

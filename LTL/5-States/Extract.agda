{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Extract -- building blocks for refuting states.
--
--   Refuted us = every state of Ust outside us is refutable.
--
-- It is HoldsOutside UstRef us, the hypothesis certAll carries, so the
-- induction hands it over unchanged.  Refuted Ust holds trivially
-- (ustRefuted).  betaElim and betaIntro treat beta as a disjunction indexed
-- by states, and extractR1 refutes a state with no successor inside us.  The induction that uses them is certAll's,
-- run by LTL.7-SCC.SccExtract: extractR1 is its sink step, and extractBlock its
-- block step.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.Extract (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.Valuation P
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.StepLemma P
open import LTL.5-States.Closure P

------------------------------------------------------------------------
-- beta_U as a disjunction indexed by states: introduction at one state,
-- elimination over all of them, and the refutation of a beta all of whose
-- disjuncts are refuted (for the empty list, beta [] is ⊥).

betaElim : {C : Formula} (ws : List Val)
        -> (∀[ w ∈ ws ] ⊢ (chi w) ⇒ C)
        -> ⊢ (beta ws) ⇒ C
betaElim ws h = ⋁Elim (map chi ws) (allInto-map chi ws h)

betaIntro : (ws : List Val)
         -> ∀ⁱ[ w ∈ ws ] ⊢ (chi w) ⇒ (beta ws)
betaIntro ws m = ⋁Intro (map chi ws) (∈-map⁺ chi m)

¬Beta : (ws : List Val)
     -> (∀[ w ∈ ws ] ⊢ ¬ (chi w))
     -> ⊢ ¬ (beta ws)
¬Beta ws h =
  refute {beta ws} {⊤}
         (liftP deriv⊤)
         (betaElim ws (λ w m -> mp ¬Elim (h w m)))

------------------------------------------------------------------------
-- The induction hypothesis

-- It ranges over Ust P, not allStates P: a state outside Ust cannot contain
-- the input and is disposed of by (S1).  ustClosed makes this work: the step
-- lemma offers ALL state-successors of u, and each lies in Ust P, where the
-- hypothesis applies.  UstRef is the property, relativised to Ust because
-- HoldsOutside covers every valuation outside us.

UstRef : Val -> Set
UstRef u = u ∈ Ust -> ⊢ ¬ (chi u)

Refuted : Subgraph -> Set
Refuted us = HoldsOutside UstRef us

------------------------------------------------------------------------
-- (R1): u has no successor inside us.

r1 : Subgraph -> Val -> Bool
r1 us u = null (succs us u)

-- A state to which (R1) applies.  stepLemma gives the successors of u
-- inside allStates; one inside us would be in succs us u, which (R1) says is
-- empty.  So every disjunct of beta is refuted by the hypothesis, (D1) puts
-- the refutation under ○, and (Lin) brings the negation out.

extractR1 : (us : Subgraph) (u : Val)
         -> u ∈ Ust -> Refuted us -> r1 us u ≡ true
         -> ⊢ ¬ (chi u)
extractR1 us u mu ih e1 =
  refute (stepLemma u)
         (liftP (mp linFwd (○Gen (¬Beta (succs allStates u) each))))
  where
    outside : ∀[ w ∈ succs allStates u ] w ∈ᵛ us ≡ false
    outside w m = ∉ᵛ-intro us w λ mw ->
      null-∈ (succs us u) e1 (succsIn us u mw (snd (∈-succs⁻ allStates u m)))

    each : ∀[ w ∈ succs allStates u ] ⊢ ¬ (chi w)
    each w m = ih w (outside w m)
                    (ustClosed mu (fst (∈-succs⁻ allStates u m)) (snd (∈-succs⁻ allStates u m)))

------------------------------------------------------------------------
-- The base of the induction: outside Ust there is nothing to refute.

ustRefuted : Refuted Ust
ustRefuted u e mu = emptyElim (∈ᵛ-false Ust u e mu)

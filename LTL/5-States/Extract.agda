{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Extract -- building blocks for refuting states.
--
--   Refuted us = every state of Ust outside us is refutable.
--
-- Refuted Ust holds trivially (ustRefuted).  betaElim and betaIntro
-- treat beta as a disjunction indexed by states, and extractR1 refutes a state
-- with no successor inside us.  The induction that uses them is certAll's,
-- run by LTL.7-SCC.SccExtract: extractR1 is its sink step, and extractBlock its
-- block step.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.Extract (P : Formula) where

open import LTL.5-States.Common
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
betaElim ws h = ⋁Elim (map chi ws) (allIntoMap chi ws h)

betaIntro : (ws : List Val)
         -> ∀ⁱ[ w ∈ ws ] ⊢ (chi w) ⇒ (beta ws)
betaIntro ws m = ⋁Intro (map chi ws) (memMap chi m)

¬Beta : (ws : List Val)
     -> (∀[ w ∈ ws ] ⊢ ¬ (chi w))
     -> ⊢ ¬ (beta ws)
¬Beta ws h =
  refute {beta ws} {⊤}
         (liftP deriv⊤)
         (betaElim ws (λ w m -> mp ¬Elim (h w m)))

------------------------------------------------------------------------
-- The induction hypothesis

-- It ranges over Ust P, not St P: a state outside Ust cannot contain the
-- input and is disposed of by (S1).  ustClosed makes this work: the step
-- lemma offers ALL state-successors of u, and each lies in Ust P, where the
-- hypothesis applies.

Refuted : List Val -> Set
Refuted us =
  (u : Val) -> u ∈ Ust -> u ∈ᵛ us ≡ false -> ⊢ ¬ (chi u)

------------------------------------------------------------------------
-- (R1): u has no successor inside us.

r1 : List Val -> Val -> Bool
r1 us u = null (succs us u)

-- A state to which (R1) applies.  stepLemma gives the successors of u
-- inside St; one inside us would be in succs us u, which (R1) says is
-- empty.  So every disjunct of beta is refuted by the hypothesis, (D1) puts
-- the refutation under ○, and (Lin) brings the negation out.

extractR1 : (us : List Val) (u : Val)
         -> u ∈ Ust -> Refuted us -> r1 us u ≡ true
         -> ⊢ ¬ (chi u)
extractR1 us u mu ih e1 =
  refute (stepLemma u)
         (liftP (mp linFwd (○Gen (¬Beta (succs St u) each))))
  where
    outside : ∀[ w ∈ succs St u ] w ∈ᵛ us ≡ false
    outside w m = refuteTrue (w ∈ᵛ us) λ eb ->
      null-mem (succs us u) e1
       (succsIn us u (∈ᵛ-sound w us eb)
                (snd (succsMem St u m)))

    each : ∀[ w ∈ succs St u ] ⊢ ¬ (chi w)
    each w m = ih w (ustClosed mu (fst (succsMem St u m))
                               (snd (succsMem St u m)))
                 (outside w m)

------------------------------------------------------------------------
-- The base of the induction: outside Ust there is nothing to refute.

ustRefuted : Refuted Ust
ustRefuted u mu e = emptyElim (∈ᵛ-false u Ust e mu)

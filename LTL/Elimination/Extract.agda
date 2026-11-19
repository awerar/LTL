{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Elimination.Extract -- building blocks for refuting states.
--
--   Refuted P us = every state of Ust P outside us is refutable.
--
-- Refuted P (Ust P) holds trivially (ustRefuted).  betaElim and betaIntro
-- treat beta as a disjunction indexed by states, and extractR1 refutes a state
-- with no successor inside us.  The induction that uses them is certAll's,
-- run by LTL.SCC.SccExtract: extractR1 is its sink step, and extractBlock its
-- block step.

module LTL.Elimination.Extract where

open import LTL.Elimination.Elim      public
open import LTL.States.StepLemma public

------------------------------------------------------------------------
-- Every state has the length chi expects

allLen-mem : {n : Nat} {vs : List Val} -> AllLen n vs -> {v : Val}
          -> v ∈ vs -> length v ≡ n
allLen-mem alNil         ()
allLen-mem (alCons e al) here      = e
allLen-mem (alCons e al) (there m) = allLen-mem al m

stAllLen : (P : Formula) -> AllLen (length (sub P)) (St P)
stAllLen P = allLen-filter (isState P) (allVecs-allLen (length (sub P)))

stLen : (P : Formula) {v : Val} -> v ∈ St P
     -> length v ≡ length (sub P)
stLen P m = allLen-mem (stAllLen P) m

------------------------------------------------------------------------
-- beta_U as a disjunction indexed by states: introduction at one state,
-- elimination over all of them, and the refutation of a beta all of whose
-- disjuncts are refuted (for the empty list, beta [] is ⊥).

-- AllInto for a mapped list, one derivation of  f w ⇒ C  per w.

allIntoMap : {C : Formula} (f : Val -> Formula) (ws : List Val)
          -> ((w : Val) -> w ∈ ws -> ⊢ (f w) ⇒ C) -> AllInto C (map f ws)
allIntoMap f []       h = intoNil
allIntoMap f (w ∷ ws) h = intoCons (h w here) (allIntoMap f ws (λ z m -> h z (there m)))

module _ (P : Formula) where

  betaElim : {C : Formula} (ws : List Val)
          -> ((w : Val) -> w ∈ ws -> ⊢ (chi P w) ⇒ C)
          -> ⊢ (beta P ws) ⇒ C
  betaElim ws h = ⋁Elim (map (chi P) ws) (allIntoMap (chi P) ws h)

  betaIntro : (ws : List Val) {w : Val}
           -> w ∈ ws -> ⊢ (chi P w) ⇒ (beta P ws)
  betaIntro ws m = ⋁Intro (map (chi P) ws) (memMap (chi P) m)

  ¬Beta : (ws : List Val)
       -> ((w : Val) -> w ∈ ws -> ⊢ ¬ (chi P w))
       -> ⊢ ¬ (beta P ws)
  ¬Beta ws h =
    refute {beta P ws} {⊤}
           (liftP deriv⊤)
           (betaElim ws (λ w m -> mp ¬Elim (h w m)))

  ------------------------------------------------------------------------
  -- The induction hypothesis

  -- It ranges over Ust P, not St P: a state outside Ust P cannot contain the
  -- input and is disposed of by (S1).  ustClosed makes this work: the step
  -- lemma offers ALL state-successors of u, and each lies in Ust P, where the
  -- hypothesis applies.

  Refuted : List Val -> Set
  Refuted us =
    (u : Val) -> u ∈ Ust P -> u ∈ᵛ us ≡ false -> ⊢ ¬ (chi P u)

  ------------------------------------------------------------------------
  -- A state with no successor inside us.  stepLemma gives the successors of u
  -- inside St P; one inside us would be in succs P us u, which (R1) says is
  -- empty.  So every disjunct of beta is refuted by the hypothesis, (D1) puts
  -- the refutation under ○, and (Lin) brings the negation out.

  extractR1 : (us : List Val) (u : Val)
           -> u ∈ Ust P -> Refuted us -> r1 P us u ≡ true
           -> ⊢ ¬ (chi P u)
  extractR1 us u mu ih e1 =
    refute (stepLemma P u (stLen P (ustSt P mu)))
           (liftP (mp linFwd (○Gen (¬Beta (succs P (St P) u) each))))
    where
      outside : (w : Val) -> w ∈ succs P (St P) u -> w ∈ᵛ us ≡ false
      outside w m = refuteTrue (w ∈ᵛ us) λ eb ->
        null-mem (succs P us u) e1
         (succsIn P us u (∈ᵛ-sound w us eb)
                  (snd (succsMem P (St P) u m)))

      each : (w : Val) -> w ∈ succs P (St P) u -> ⊢ ¬ (chi P w)
      each w m = ih w (ustClosed P mu (fst (succsMem P (St P) u m))
                                 (snd (succsMem P (St P) u m)))
                   (outside w m)

  ------------------------------------------------------------------------
  -- The base of the induction: outside Ust P there is nothing to refute.

  ustRefuted : Refuted (Ust P)
  ustRefuted u mu e = emptyElim (∈ᵛ-false u (Ust P) e mu)

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Elimination.Extract -- G21 of FORMALISATION-PLAN.md, the proof-extraction
-- apparatus of Theorem 4.1 of m4.tex.
--
-- The note argues by induction on the round at which a state is removed, with
-- the induction hypothesis "every state outside U_k is refutable".  Here that
-- hypothesis is named,
--
--   Refuted P us = every state of Ust P outside us is refutable,
--
-- and it holds of Ust P for nothing (ustRefuted).  This module holds what the
-- extraction is built from: beta_U as a disjunction indexed by states
-- (betaElim, betaIntro), and case (R1) of the theorem, extractR1, which drops
-- all successors by the hypothesis and closes with (D1) and (Lin).
--
-- The induction itself is run by the SCC certificate in LTL.SCC.SccExtract:
-- its sink step is extractR1, and its block step, extractBlock, is the (R2)
-- case of the note, refuting a pending eventuality with a single use of (Ind).

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
-- beta_U as a disjunction indexed by states.
--
-- (L5) in the form the theorem uses: introduction at one state, elimination
-- over all of them, and the refutation of a beta all of whose disjuncts are
-- refuted -- which is (L0) when the list is empty, since beta [] is ⊥ and
-- ⋁Elim [] is exFalso.

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
  -- The induction hypothesis of the theorem

  -- The induction hypothesis ranges over Ust P, the set the search explores,
  -- not over St P: a state outside Ust P is never removed and never has to be
  -- refuted -- the provable branch disposes of it by (S1) instead.  What makes
  -- the change possible is ustClosed, used by extractR1 below and by extractBlock
  -- of LTL.SCC.SccExtract: the step lemma
  -- offers ALL state-successors of u, and forward-closure puts each of them
  -- back inside Ust P, where the hypothesis applies.

  Refuted : List Val -> Set
  Refuted us =
    (u : Val) -> u ∈ Ust P -> u ∈ᵛ us ≡ false -> ⊢ ¬ (chi P u)

  ------------------------------------------------------------------------
  -- Case (R1).
  --
  -- stepLemma gives the successors of u inside St P, while (R1) speaks of U_k;
  -- but a successor lying in U_k would be a member of succs P us u, which (R1)
  -- says is empty.  So every disjunct of beta_S is refuted by the hypothesis,
  -- (D1) puts the refutation under ○, and (Lin) brings the negation out.

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

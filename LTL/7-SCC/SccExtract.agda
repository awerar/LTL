{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.7-SCC.SccExtract -- a certificate refutes every state of Ust.
--
--     ustCertRefuted : Cert evPreds Ust -> (z : Val) -> z ∈ Ust -> ⊢ ¬ (chi z)
--
-- The graph search's NEGATIVE answer is a Cert: the order in which it removed
-- the vertices, each a sink or a block (a closed component missing some
-- fairness predicate).  certAll turns it into an induction:
--
--   sink   Sink ws x, null (outs ws x) ≡ true, is  r1 ws x ≡ true
--          definitionally, so extractR1 refutes x.
--   block  the component C misses  evPred A , i.e. at every state of C the
--          eventuality □ A is pending and A holds.  extractBlock refutes the
--          whole of C with one use of (Ind), the invariant being beta of C.
--
-- certAll knows nothing of Ust, while chi and the step lemma are stated for
-- its states, so the block is intersected with Ust on the spot (D below);
-- ustClosed keeps it closed.  provableSCC (LTL.8-Procedures.Decide) turns the
-- refutations into a derivation of Q at P = ¬ Q.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.7-SCC.SccExtract (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.Valuation P
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.StepLemma P
open import LTL.5-States.Closure P
open import LTL.5-States.Extract P
open import LTL.6-Countermodel.Walk P
open import LTL.7-SCC.SccLasso P

------------------------------------------------------------------------
-- The block case: a component C, closed inside ws, with □ A pending and A
-- holding at every state, is refuted by (Ind) with the invariant B = beta C:
-- (i) B ⇒ A by (L2) and (L5); (ii) B ⇒ ○ B by the step lemma, dropping the
-- successors outside ws by the induction hypothesis and keeping the rest by
-- closure; (iii) B ⇒ □ A by (Ind).

extractBlock : (ws : Subgraph) (C : List Val) (u : Val)
            -> u ∈ Ust -> Refuted ws
            -> (A : Formula) -> □ A ∈ sub P
            -> C ⊆ Ust
            -> Closed[ step ▷ St ∩ˡ ws ] C
            -> (∀[ z ∈ C ] holdsIn z A ≡ true)
            -> holdsIn u (□ A) ≡ false -> u ∈ C
            -> ⊢ ¬ (chi u)
extractBlock ws C u mu ih A mbox cUst cCl cHold pend mc = refute chi□ chi¬□
  where
    -- (i)
    bA : ⊢ (beta C) ⇒ A
    bA = betaElim C eachA
      where
        eachA : ∀[ w ∈ C ] ⊢ (chi w) ⇒ A
        eachA w m = subst (λ b -> ⊢ (chi w) ⇒ (lit A b)) (cHold w m)
                          (chiProj w (sub-□ P mbox))

    -- (ii)
    toC : ∀[ w ∈ C ] ⊢ (beta (succs St w)) ⇒ (beta C)
    toC w m = betaElim (succs St w) eachS
      where
        eachS : ∀[ w' ∈ succs St w ] ⊢ (chi w') ⇒ (beta C)
        eachS w' m' = by∈ᵛ
          where
            pr : w' ∈ St × step w w' ≡ true
            pr = ∈-succs⁻ St w m'

            by∈ᵛ : ⊢ (chi w') ⇒ (beta C)
            by∈ᵛ with w' ∈ᵛ ws in eb
            ... | false =
              mp ¬Elim (ih w' eb (ustClosed (cUst w m) (fst pr) (snd pr)))
            ... | true  =
              betaIntro C (cCl m (∈-∩ˡ⁺ ws (fst pr) (∈ᵛ-sound ws w' eb)) (snd pr))

    bNext : ⊢ (beta C) ⇒ ○ (beta C)
    bNext = betaElim C eachN
      where
        eachN : ∀[ w ∈ C ] ⊢ (chi w) ⇒ ○ (beta C)
        eachN w m = ⇒Trans (stepLemma w) (○Mono (toC w m))

    -- (iii)
    chi□ : ⊢ (chi u) ⇒ □ A
    chi□ = ⇒Trans (betaIntro C mc) (⇒Trans (indRule bNext) (□Mono bA))

    chi¬□ : ⊢ (chi u) ⇒ ¬ □ A
    chi¬□ = subst (λ b -> ⊢ (chi u) ⇒ (lit (□ A) b)) pend
                        (chiProj u mbox)

------------------------------------------------------------------------
-- certAll's two hypotheses, at R = UstRef, so that its hypothesis
-- HoldsOutside UstRef ws is Refuted ws.

-- The sink.  Sink ws x, null (outs ws x) ≡ true, IS  r1 ws x ≡ true .

sinkStep : (ws : Subgraph) (x : Val) -> Sink ws x
        -> Refuted ws -> UstRef x
sinkStep ws x e1 ih mu = extractR1 ws x mu ih e1

-- The block.  The fairness predicate is read back as an eventuality
-- (∈-evPreds⁻), its falsity on C gives the two hypotheses, and the
-- component is intersected with Ust P.

blockStep : (ws : Subgraph) (C : List Val) (f : Pred) -> f ∈ evPreds
         -> Closed[ step ▷ ws ] C -> None f C
         -> Refuted ws -> ∀[ z ∈ C ] UstRef z
blockStep ws C f mf cl mis ih z mz mzU = onA (∈-evPreds⁻ mf)
  where
    onA : (∃[ A ∈ eventualities ] f ≡ evPred A)
       -> ⊢ ¬ (chi z)
    onA (A , mA , ef) =
      extractBlock ws D z mzU ih A (evSub mA)
                   (∩ˡ-snd C Ust) dCl dHold pend (∈-∩ˡ⁺ Ust mz mzU)
      where
        missA : ∀[ y ∈ C ] y ∉ᵖ evPred A
        missA y my = subst (λ h -> h y ≡ false) ef (mis y my)

        -- the component, cut down to the states chi is stated for
        D : List Val
        D = C ∩ˡ Ust

        -- still closed: C's closure puts the successor in C, ustClosed puts
        -- it in Ust P, and D is the intersection
        dCl : Closed[ step ▷ St ∩ˡ ws ] D
        dCl my my' st =
          ∈-∩ˡ⁺ Ust (cl (∩ˡ-fst C Ust _ my) (∩ˡ-snd St ws _ my') st)
                    (ustClosed (∩ˡ-snd C Ust _ my) (∩ˡ-fst St ws _ my') st)

        dHold : ∀[ y ∈ D ] holdsIn y A ≡ true
        dHold y my =
          ¬ᵇ-false (holdsIn y A)
                   (∨ᵇ-falseʳ (holdsIn y (□ A)) (¬ᵇ holdsIn y A)
                              (missA y (∩ˡ-fst C Ust y my)))

        pend : holdsIn z (□ A) ≡ false
        pend = ∨ᵇ-falseˡ (holdsIn z (□ A)) (¬ᵇ holdsIn z A) (missA z mz)

------------------------------------------------------------------------
-- A certificate for Ust refutes all of it.  The induction starts from
-- ustRefuted: nothing of Ust is outside Ust.

ustCertRefuted : Cert evPreds Ust
              -> ∀[ z ∈ Ust ] ⊢ ¬ (chi z)
ustCertRefuted c = certAll evPreds UstRef sinkStep blockStep c ustRefuted

------------------------------------------------------------------------
-- The search, run on the whole state set.  fairOrCert rather than fairGraph:
-- fairGraph certifies only the states reachable from one vertex, while the
-- refutation has to cover every state of Ust P.

sccGraph : FairIn Ust evPreds ⊎
           Cert evPreds Ust
sccGraph =
  fairOrCert evPreds Ust (∈ᵛ-complete Ust) (listFinite Ust)

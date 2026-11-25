{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.7-SCC.SccExtract -- a certificate refutes every state of Ust.
--
--     ustCertRefuted : Cert evPreds Ust -> (z : Val) -> z ∈ Ust -> ⊢ ¬ (chi z)
--
-- The graph search's NEGATIVE answer is a Cert: the order in which it removed
-- the vertices, each a sink or a block (a closed component missing some
-- fairness predicate).  certAll turns it into an induction:
--
--   sink   null (outs ws x) ≡ true  is  r1 ws x ≡ true
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
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.StepLemma P
open import LTL.5-States.Closure P
open import LTL.5-States.Extract P
open import LTL.6-Countermodel.Walk P
open import LTL.7-SCC.SccLasso P

------------------------------------------------------------------------
-- The property certAll establishes: Refuted with the "outside us" discharged
-- by the induction, leaving the Ust-membership as a hypothesis.

UstRef : Val -> Set
UstRef z = z ∈ Ust -> ⊢ ¬ (chi z)

refutedOf : (ws : List Val)
         -> HoldsOutside UstRef ws -> Refuted ws
refutedOf ws ih u mu e = ih u e mu

------------------------------------------------------------------------
-- The block case: a component C, closed inside ws, with □ A pending and A
-- holding at every state, is refuted by (Ind) with the invariant B = beta C:
-- (i) B ⇒ A by (L2) and (L5); (ii) B ⇒ ○ B by the step lemma, dropping the
-- successors outside ws by the induction hypothesis and keeping the rest by
-- closure; (iii) B ⇒ □ A by (Ind).

extractBlock : (ws C : List Val) (u : Val)
            -> u ∈ Ust -> Refuted ws
            -> (A : Formula) -> □ A ∈ sub P
            -> C ⊆ Ust
            -> C closed-under step within (St ∩ˡ ws)
            -> (∀[ z ∈ C ] valOf z A ≡ true)
            -> valOf u (□ A) ≡ false -> u ∈ C
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
              mp ¬Elim (ih w' (ustClosed (cUst w m) (fst pr) (snd pr)) eb)
            ... | true  =
              betaIntro C (cCl m (∈-∩ˡ⁺ ws (fst pr) (∈ᵛ-sound w' ws eb)) (snd pr))

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
-- certAll's two hypotheses.

-- The sink.  null (outs ws x) ≡ true  IS  r1 ws x ≡ true .

sinkStep : (ws : List Val) (x : Val) -> x ∈ ws
        -> null (outs ws x) ≡ true
        -> HoldsOutside UstRef ws
        -> UstRef x
sinkStep ws x mx e1 ih mu = extractR1 ws x mu (refutedOf ws ih) e1

-- The block.  The fairness predicate is read back as an eventuality
-- (∈-evPreds⁻), its falsity on C gives the two hypotheses, and the
-- component is intersected with Ust P.

blockStep : (ws C : List Val) (f : Pred) -> f ∈ evPreds
         -> C closed-under step within ws -> C avoids f
         -> HoldsOutside UstRef ws
         -> ∀[ z ∈ C ] UstRef z
blockStep ws C f mf cl mis ih z mz mzU = onA (∈-evPreds⁻ mf)
  where
    onA : (∃[ A ∈ eventualities ] f ≡ evPred A)
       -> ⊢ ¬ (chi z)
    onA (A , mA , ef) =
      extractBlock ws D z mzU (refutedOf ws ih) A (evSub mA)
                   (∩ˡ-snd C Ust) dCl dHold pend (∈-∩ˡ⁺ Ust mz mzU)
      where
        missA : ∀[ y ∈ C ] y ∉ᵖ evPred A
        missA y my = subst (λ h -> h y ≡ false) ef (mis y my)

        -- the component, cut down to the states chi is stated for
        D : List Val
        D = C ∩ˡ Ust

        -- still closed: C's closure puts the successor in C, ustClosed puts
        -- it in Ust P, and D is the intersection
        dCl : D closed-under step within (St ∩ˡ ws)
        dCl my my' st =
          ∈-∩ˡ⁺ Ust (cl (∩ˡ-fst C Ust _ my) (∩ˡ-snd St ws _ my') st)
                    (ustClosed (∩ˡ-snd C Ust _ my) (∩ˡ-fst St ws _ my') st)

        dHold : ∀[ y ∈ D ] valOf y A ≡ true
        dHold y my =
          ¬ᵇ-false (valOf y A)
                   (∨ᵇ-falseʳ (valOf y (□ A)) (¬ᵇ valOf y A)
                              (missA y (∩ˡ-fst C Ust y my)))

        pend : valOf z (□ A) ≡ false
        pend = ∨ᵇ-falseˡ (valOf z (□ A)) (¬ᵇ valOf z A) (missA z mz)

------------------------------------------------------------------------
-- A certificate refutes everything it covers.

certRefuted : {ws : List Val}
           -> Cert evPreds ws -> Refuted ws
           -> ∀[ z ∈ Ust ] ⊢ ¬ (chi z)
certRefuted {ws} c ih =
  certAll evPreds UstRef sinkStep blockStep c
          (λ z e mu -> ih z mu e)

-- Over Ust itself the seed is vacuous: nothing is outside.

ustCertRefuted : Cert evPreds Ust
              -> ∀[ z ∈ Ust ] ⊢ ¬ (chi z)
ustCertRefuted c = certRefuted c ustRefuted

------------------------------------------------------------------------
-- The search, run on the whole state set.  graphGo rather than fairGraph:
-- fairGraph certifies only the states reachable from one vertex, while the
-- refutation has to cover every state of Ust P.

sccGraph : FairIn Ust evPreds ⊎
           Cert evPreds Ust
sccGraph =
  graphGo evPreds Ust (inside-∈ᵛ Ust) (listFinite Ust)

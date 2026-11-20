{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SCC.SccExtract -- a certificate gives a derivation.
--
--     provableSCC : (Q : Formula)
--                -> Cert (¬ Q) (evPreds (¬ Q)) (Ust (¬ Q))
--                -> ⊢ Q
--
-- The graph search's NEGATIVE answer is a Cert: the order in which it removed
-- the vertices, each a sink or a block (a closed component missing some
-- fairness predicate).  certAll turns it into an induction, refuting every
-- state of Ust (¬ Q):
--
--   sink   null (outs P ws x) ≡ true  is  r1 P ws x ≡ true
--          definitionally, so extractR1 refutes x.
--   block  the component C misses  evPred P A , i.e. at every state of C the
--          eventuality □ A is pending and A holds.  extractBlock refutes the
--          whole of C with one use of (Ind), the invariant being beta of C.
--
-- certAll knows nothing of Ust P, while chi and the step lemma are stated for
-- its states, so the block is intersected with Ust P on the spot (D below);
-- ustClosed keeps it closed.
--
-- The derivation closes with stateCompletePC and betaElimPC
-- (LTL.Procedures.CompletePC), and each state not containing ¬ Q is one pc
-- node (tautChi), so the certificate is short: only extractR1 and
-- extractBlock are derived step by step.

module LTL.SCC.SccExtract where

open import LTL.SCC.SccLasso public
open import LTL.States.Extract public
open import LTL.Procedures.CompletePC public

------------------------------------------------------------------------
-- The property certAll establishes: Refuted with the "outside us" discharged
-- by the induction, leaving the Ust-membership as a hypothesis.

module _ (P : Formula) where

  UstRef : Val -> Set
  UstRef z = z ∈ Ust P -> ⊢ ¬ (chi P z)

  refutedOf : (ws : List Val)
           -> HoldsOutside UstRef ws -> Refuted P ws
  refutedOf ws ih u mu e = ih u e mu

  ------------------------------------------------------------------------
  -- The block case: a component C, closed inside ws, with □ A pending and A
  -- holding at every state, is refuted by (Ind) with the invariant B = beta C:
  -- (i) B ⇒ A by (L2) and (L5); (ii) B ⇒ ○ B by the step lemma, dropping the
  -- successors outside ws by the induction hypothesis and keeping the rest by
  -- closure; (iii) B ⇒ □ A by (Ind).

  extractBlock : (ws C : List Val) (u : Val)
              -> u ∈ Ust P -> Refuted P ws
              -> (A : Formula) -> □ A ∈ sub P
              -> C ⊆ Ust P
              -> ((z y : Val) -> z ∈ C -> y ∈ St P -> y ∈ᵛ ws ≡ true
                    -> step P z y ≡ true -> y ∈ C)
              -> ((z : Val) -> z ∈ C -> valOf P z A ≡ true)
              -> valOf P u (□ A) ≡ false -> u ∈ C
              -> ⊢ ¬ (chi P u)
  extractBlock ws C u mu ih A mbox cUst cCl cHold pend mc = refute chi□ chi¬□
    where
      lenC : (w : Val) -> w ∈ C -> length w ≡ length (sub P)
      lenC w m = stLen P (ustSt P (cUst w m))

      -- (i)
      bA : ⊢ (beta P C) ⇒ A
      bA = betaElim P C eachA
        where
          eachA : (w : Val) -> w ∈ C -> ⊢ (chi P w) ⇒ A
          eachA w m = subst (λ b -> ⊢ (chi P w) ⇒ (lit A b)) (cHold w m)
                            (chiProjVal P w (lenC w m) (sub-□ P mbox))

      -- (ii)
      toC : (w : Val) -> w ∈ C
         -> ⊢ (beta P (succs P (St P) w)) ⇒ (beta P C)
      toC w m = betaElim P (succs P (St P) w) eachS
        where
          eachS : (w' : Val) -> w' ∈ succs P (St P) w
               -> ⊢ (chi P w') ⇒ (beta P C)
          eachS w' m' = byMem
            where
              pr : w' ∈ St P × step P w w' ≡ true
              pr = succsMem P (St P) w m'

              byMem : ⊢ (chi P w') ⇒ (beta P C)
              byMem with w' ∈ᵛ ws in eb
              ... | false =
                mp ¬Elim (ih w' (ustClosed P (cUst w m) (fst pr) (snd pr)) eb)
              ... | true  = betaIntro P C (cCl w w' m (fst pr) eb (snd pr))

      bNext : ⊢ (beta P C) ⇒ ○ (beta P C)
      bNext = betaElim P C eachN
        where
          eachN : (w : Val) -> w ∈ C -> ⊢ (chi P w) ⇒ ○ (beta P C)
          eachN w m = ⇒Trans (stepLemma P w (lenC w m)) (○Mono (toC w m))

      -- (iii)
      chi□ : ⊢ (chi P u) ⇒ □ A
      chi□ = ⇒Trans (betaIntro P C mc) (⇒Trans (indRule bNext) (□Mono bA))

      chi¬□ : ⊢ (chi P u) ⇒ ¬ □ A
      chi¬□ = subst (λ b -> ⊢ (chi P u) ⇒ (lit (□ A) b)) pend
                          (chiProjVal P u (stLen P (ustSt P mu)) mbox)

  ------------------------------------------------------------------------
  -- certAll's two hypotheses.

  -- The sink.  null (outs P ws x) ≡ true  IS  r1 P ws x ≡ true .

  sinkStep : (ws : List Val) (x : Val) -> x ∈ ws
          -> null (outs P ws x) ≡ true
          -> HoldsOutside UstRef ws
          -> UstRef x
  sinkStep ws x mx e1 ih mu = extractR1 P ws x mu (refutedOf ws ih) e1

  -- The block.  The fairness predicate is read back as an eventuality
  -- (evPredsInv), its falsity on C gives the two hypotheses, and the
  -- component is intersected with Ust P.

  blockStep : (ws C : List Val) (f : Pred) -> f ∈ evPreds P
           -> C ⊆ ws -> Closed ws (step P) C -> NoneSat f C
           -> HoldsOutside UstRef ws
           -> (z : Val) -> z ∈ C -> UstRef z
  blockStep ws C f mf sbC cl mis ih z mz mzU = onA (evPredsInv P mf)
    where
      onA : (Σ[ A ∈ Formula ] A ∈ □Args (sub P) × f ≡ evPred P A)
         -> ⊢ ¬ (chi P z)
      onA (A , mA , ef) =
        extractBlock ws D z mzU (refutedOf ws ih) A (□Args-mem (sub P) mA)
                     dUst dCl dHold pend mzD
        where
          missA : (y : Val) -> y ∈ C -> evPred P A y ≡ false
          missA y my = subst (λ h -> h y ≡ false) ef (mis y my)

          -- the component, cut down to the states chi is stated for
          D : List Val
          D = filter (λ y -> y ∈ᵛ Ust P) C

          dC : (y : Val) -> y ∈ D -> y ∈ C
          dC y m = filter-sub (λ t -> t ∈ᵛ Ust P) C m

          dUst : (y : Val) -> y ∈ D -> y ∈ Ust P
          dUst y m = ∈ᵛ-sound y (Ust P) (filter-prop (λ t -> t ∈ᵛ Ust P) C m)

          into : (y : Val) -> y ∈ C -> y ∈ Ust P -> y ∈ D
          into y my mu =
            filter-true (λ t -> t ∈ᵛ Ust P) C my (∈ᵛ-complete y (Ust P) mu)

          -- still closed: C's closure puts the successor in C, ustClosed puts
          -- it in Ust P, and D is the intersection
          dCl : (y y' : Val) -> y ∈ D -> y' ∈ St P -> y' ∈ᵛ ws ≡ true
             -> step P y y' ≡ true -> y' ∈ D
          dCl y y' my my' ew st =
            into y' (cl y y' (dC y my) (∈ᵛ-sound y' ws ew) st)
                    (ustClosed P (dUst y my) my' st)

          dHold : (y : Val) -> y ∈ D -> valOf P y A ≡ true
          dHold y my =
            ¬ᵇ-false (valOf P y A)
                     (∨ᵇ-falseʳ (valOf P y (□ A)) (¬ᵇ valOf P y A)
                                (missA y (dC y my)))

          pend : valOf P z (□ A) ≡ false
          pend = ∨ᵇ-falseˡ (valOf P z (□ A)) (¬ᵇ valOf P z A) (missA z mz)

          mzD : z ∈ D
          mzD = into z mz mzU

  ------------------------------------------------------------------------
  -- A certificate refutes everything it covers.

  certRefuted : {ws : List Val}
             -> Cert P (evPreds P) ws -> Refuted P ws
             -> (z : Val) -> z ∈ Ust P -> ⊢ ¬ (chi P z)
  certRefuted {ws} c ih =
    certAll P (evPreds P) UstRef sinkStep blockStep c
            (λ z e mu -> ih z mu e)

  -- Over Ust P itself the seed is vacuous: nothing is outside.

  ustCertRefuted : Cert P (evPreds P) (Ust P)
                -> (z : Val) -> z ∈ Ust P -> ⊢ ¬ (chi P z)
  ustCertRefuted c = certRefuted c (ustRefuted P)

  ------------------------------------------------------------------------
  -- The search, run on the whole state set.  graphGo rather than fairGraph:
  -- fairGraph certifies only the states reachable from one vertex, while the
  -- refutation has to cover every state of Ust P.

  sccGraph : FairIn P (Ust P) (evPreds P) ⊎
             Cert P (evPreds P) (Ust P)
  sccGraph =
    graphGo P (evPreds P) (Ust P) (memAllSat (Ust P)) (listBar (Ust P))

------------------------------------------------------------------------
-- The derivation of Q.  A state of St (¬ Q) outside Ust (¬ Q) cannot contain
-- ¬ Q (by ustSeed), so chi_w ⇒ Q is a tautology and one pc node.  A state
-- inside is refuted by the certificate.  State completeness, over all of
-- St (¬ Q), then gives Q.

provableEachSCC : (Q : Formula)
               -> Cert (¬ Q) (evPreds (¬ Q)) (Ust (¬ Q))
               -> (w : Val) -> w ∈ St (¬ Q) -> ⊢ (chi (¬ Q) w) ⇒ Q
provableEachSCC Q c w m = byPosition
  where
    R : Formula
    R = ¬ Q

    -- w does not contain R, so chi_w ⇒ Q is a tautology: one pc node
    fromR : valOf R w R ≡ false -> ⊢ (chi R w) ⇒ Q
    fromR ev = pc (tautChi Q w (stLen R m) ev)

    byPosition : ⊢ (chi R w) ⇒ Q
    byPosition with w ∈ᵛ Ust R in ec
    ... | false =
      fromR (refuteTrue (valOf R w R) λ ed ->
               ∈ᵛ-false w (Ust R) ec (ustSeed R m ed))
    ... | true = mp ¬Elim (ustCertRefuted R c w (∈ᵛ-sound w (Ust R) ec))

provableSCC : (Q : Formula)
           -> Cert (¬ Q) (evPreds (¬ Q)) (Ust (¬ Q)) -> ⊢ Q
provableSCC Q c =
  mp (betaElimPC (¬ Q) (St (¬ Q)) (provableEachSCC Q c)) (stateCompletePC (¬ Q))

------------------------------------------------------------------------
-- The two branches of the search, side by side: a fair component, or a
-- derivation of Q.

sccProof : (Q : Formula)
        -> FairIn (¬ Q) (Ust (¬ Q)) (evPreds (¬ Q)) ⊎ ⊢ Q
sccProof Q = sumElim inl (λ c -> inr (provableSCC Q c)) (sccGraph (¬ Q))

-- Reading a derivation out, on the strength of the computed boolean: a refl
-- argument says the search was run and took this branch.

proofFrom : {A : Set} {Q : Formula}
         -> (s : A ⊎ ⊢ Q) -> isInl s ≡ false -> ⊢ Q
proofFrom (inl a) ()
proofFrom (inr d) e = d

-- The shape of the certificate: removedBlock, removedSink, then emptied.

sccShape : (Q : Formula) -> List CertStep
sccShape Q = sumElim (λ fi -> []) (certShape (¬ Q)) (sccGraph (¬ Q))

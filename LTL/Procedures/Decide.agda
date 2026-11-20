{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Procedures.Decide -- the decision procedure:
--
--   decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
--
-- It searches Ust (¬ Q) for a fair component (sccGraph).  A certificate gives
-- a derivation (provableSCC, below).  A fair component gives a countermodel,
-- in three steps:
--
--   1. ustSeedTo: the component's representative is reached from a state s
--      containing ¬ Q.  Stem and circuit form a FairLoop from s.
--   2. sccLasso: a fair loop in Ust (¬ Q) is a Lasso.
--   3. buildCM: Hintikka's lemma at stage 0.
--
-- The search runs on all of Ust (¬ Q), not from one vertex, because the
-- certificate has to cover every state.
--
-- Everything here is about the input Q, so this module is not parameterised:
-- it opens the P-modules unapplied and uses them at ¬ Q.  It re-exports all
-- of them, so an importer (LTL.Correct, LTL.Pretty, the tests) needs only
-- this module.

module LTL.Procedures.Decide where

open import LTL.States.Common           public
open import LTL.States.VecBar           public
open import LTL.States.Taut             public
open import LTL.States.State            public
open import LTL.States.Step             public
open import LTL.States.Proj             public
open import LTL.States.NonState         public
open import LTL.States.Complete         public
open import LTL.States.StepLemma        public
open import LTL.States.Closure          public
open import LTL.States.Extract          public
open import LTL.Procedures.CompletePC   public
open import LTL.Countermodel.Walk       public
open import LTL.Countermodel.Lasso      public
open import LTL.Countermodel.Global     public
open import LTL.Countermodel.Eval       public
open import LTL.Countermodel.Hintikka   public
open import LTL.SCC.SccLasso            public
open import LTL.SCC.SccExtract          public
open import LTL.SCC.SccSeed             public
open import LTL.Procedures.Answer       public

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

------------------------------------------------------------------------
-- A countermodel from a lasso.
--
-- v0 contains ¬ Q and is a state, so by (S1) it does not contain Q;
-- Hintikka's lemma at stage 0 transfers that to the evaluation.

buildCM : (Q : Formula) (v0 : Val)
       -> Lasso (¬ Q) v0 -> valOf (¬ Q) v0 (¬ Q) ≡ true
       -> LassoCountermodel Q
buildCM Q v0 l ev = countermodel v0 l evalFalse
  where
    valQ : valOf (¬ Q) v0 Q ≡ false
    valQ =
      ¬ᵇ-true (valOf (¬ Q) v0 Q)
        (trans (sym (⇔ᵇ-sound (valOf (¬ Q) v0 (¬ Q))
                              (¬ᵇ valOf (¬ Q) v0 Q)
                                  (stateOk (¬ Q) v0 (Lasso.startIn l) (sub-self (¬ Q)))))
               ev)

    evalFalse : eval (¬ Q) v0 l Q 0 ≡ false
    evalFalse =
      trans (sym (hintStart (¬ Q) v0 l Q (there (sub-self Q)))) valQ

-- A fair circuit through r, reached from a state s containing ¬ Q, is a fair
-- loop from s, and so a countermodel.

fairCountermodel : (Q : Formula)
                -> FairIn (¬ Q) (Ust (¬ Q)) (evPreds (¬ Q))
                -> LassoCountermodel Q
fairCountermodel Q (fairIn r mr c) =
  buildCM Q seed (sccLasso (¬ Q) seed seedIn (fairLoop {¬ Q} r reaches c))
          seedHolds
  where open SeedTo (ustSeedTo (¬ Q) r mr)

------------------------------------------------------------------------
-- The decision

decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
decide Q with sccGraph (¬ Q)
... | inl fair = inr (fairCountermodel Q fair)
... | inr cert = inl (provableSCC Q cert)

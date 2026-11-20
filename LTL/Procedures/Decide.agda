{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Procedures.Decide -- the decision procedure:
--
--   decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
--
-- It searches Ust (¬ Q) for a fair component (sccGraph).  A certificate gives
-- a derivation (provableSCC).  A fair component gives a countermodel,
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
-- Everything here is about one input Q, so Q is the module parameter and the
-- P-modules are opened at P = ¬ Q.  Outside, decide Q and provableSCC Q read
-- as usual; LTL.Procedures.Everything re-exports this module with the rest.

open import LTL.Syntax.Formula using (Formula; ¬_)

module LTL.Procedures.Decide (Q : Formula) where

open import LTL.States.Common
open import LTL.States.Taut using (tautChi)
open import LTL.States.State           (¬ Q)
open import LTL.States.Closure         (¬ Q)
open import LTL.States.Extract         (¬ Q)
open import LTL.Procedures.CompletePC  (¬ Q)
open import LTL.Countermodel.Lasso     (¬ Q)
open import LTL.Countermodel.Eval      (¬ Q)
open import LTL.Countermodel.Hintikka  (¬ Q)
open import LTL.SCC.SccLasso           (¬ Q)
open import LTL.SCC.SccExtract         (¬ Q)
open import LTL.SCC.SccSeed            (¬ Q)
open import LTL.Procedures.Answer using (LassoCountermodel; countermodel)

------------------------------------------------------------------------
-- The derivation of Q.  A state of St outside Ust cannot contain ¬ Q (by
-- ustSeed), so chi_w ⇒ Q is a tautology and one pc node.  A state inside is
-- refuted by the certificate.  State completeness, over all of St, then
-- gives Q.

provableEachSCC : Cert evPreds Ust
               -> (w : Val) -> w ∈ St -> ⊢ (chi w) ⇒ Q
provableEachSCC c w m = byPosition
  where
    -- w does not contain ¬ Q, so chi_w ⇒ Q is a tautology: one pc node
    fromR : valOf w (¬ Q) ≡ false -> ⊢ (chi w) ⇒ Q
    fromR ev = pc (tautChi Q w (stLen m) ev)

    byPosition : ⊢ (chi w) ⇒ Q
    byPosition with w ∈ᵛ Ust in ec
    ... | false =
      fromR (refuteTrue (valOf w (¬ Q)) λ ed ->
               ∈ᵛ-false w Ust ec (ustSeed m ed))
    ... | true = mp ¬Elim (ustCertRefuted c w (∈ᵛ-sound w Ust ec))

provableSCC : Cert evPreds Ust -> ⊢ Q
provableSCC c =
  mp (betaElimPC St (provableEachSCC c)) stateCompletePC

------------------------------------------------------------------------
-- The two branches of the search, side by side: a fair component, or a
-- derivation of Q.  proofFrom (LTL.Procedures.Answer) reads the second out.

sccProof : FairIn Ust evPreds ⊎ ⊢ Q
sccProof = sumElim inl (λ c -> inr (provableSCC c)) sccGraph

-- The shape of the certificate: removedBlock, removedSink, then emptied.

sccShape : List CertStep
sccShape = sumElim (λ fi -> []) certShape sccGraph

------------------------------------------------------------------------
-- A countermodel from a lasso.
--
-- v0 contains ¬ Q and is a state, so by (S1) it does not contain Q;
-- Hintikka's lemma at stage 0 transfers that to the evaluation.

buildCM : (v0 : Val) -> Lasso v0 -> valOf v0 (¬ Q) ≡ true
       -> LassoCountermodel Q
buildCM v0 l ev = countermodel v0 l evalFalse
  where
    valQ : valOf v0 Q ≡ false
    valQ =
      ¬ᵇ-true (valOf v0 Q)
        (trans (sym (⇔ᵇ-sound (valOf v0 (¬ Q)) (¬ᵇ valOf v0 Q)
                              (stateOk v0 (Lasso.startIn l) (sub-self (¬ Q)))))
               ev)

    evalFalse : eval v0 l Q 0 ≡ false
    evalFalse = trans (sym (hintStart v0 l Q (there (sub-self Q)))) valQ

-- A fair circuit through r, reached from a state s containing ¬ Q, is a fair
-- loop from s, and so a countermodel.

fairCountermodel : FairIn Ust evPreds -> LassoCountermodel Q
fairCountermodel (fairIn r mr c) =
  buildCM seed (sccLasso seed seedIn (fairLoop r reaches c)) seedHolds
  where open SeedTo (ustSeedTo r mr)

------------------------------------------------------------------------
-- The decision

decide : ⊢ Q ⊎ LassoCountermodel Q
decide with sccGraph
... | inl fair = inr (fairCountermodel fair)
... | inr cert = inl (provableSCC cert)

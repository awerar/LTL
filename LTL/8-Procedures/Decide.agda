{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.8-Procedures.Decide -- the decision procedure:
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
-- as usual; LTL.8-Procedures.Everything re-exports this module with the rest.

open import LTL.2-Syntax.Formula using (Formula; ¬_)

module LTL.8-Procedures.Decide (Q : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.Taut using (tautChi)
open import LTL.5-States.State           (¬ Q)
open import LTL.5-States.Closure         (¬ Q)
open import LTL.5-States.Extract         (¬ Q)
open import LTL.5-States.CompletePC      (¬ Q)
open import LTL.6-Countermodel.Walk      (¬ Q)
open import LTL.6-Countermodel.Lasso     (¬ Q)
open import LTL.6-Countermodel.Hintikka  (¬ Q)
open import LTL.7-SCC.SccLasso           (¬ Q)
open import LTL.7-SCC.SccExtract         (¬ Q)
open import LTL.7-SCC.SccSeed            (¬ Q)
open import LTL.8-Procedures.Answer using (LassoCountermodel; countermodel)
open import LTL.1-Lib.CertStep using (CertStep)

------------------------------------------------------------------------
-- The derivation of Q.  A state of St outside Ust cannot contain ¬ Q (by
-- ustSeed), so chi_w ⇒ Q is a tautology and one pc node.  A state inside is
-- refuted by the certificate.  State completeness, over all of St, then
-- gives Q.

provableEachSCC : Cert evPreds Ust
               -> ∀[ w ∈ St ] ⊢ (chi w) ⇒ Q
provableEachSCC c w m = byPosition
  where
    -- w does not contain ¬ Q, so chi_w ⇒ Q is a tautology: one pc node
    fromR : valOf w (¬ Q) ≡ false -> ⊢ (chi w) ⇒ Q
    fromR ev = pc (tautChi Q w ev)

    byPosition : ⊢ (chi w) ⇒ Q
    byPosition with w ∈ᵛ Ust in ec
    ... | false =
      fromR (refuteTrue (valOf w (¬ Q)) λ ed ->
               ∈ᵛ-false w Ust ec (ustSeed m ed))
    ... | true = mp ¬Elim (ustCertRefuted c w (∈ᵛ-sound w Ust ec))

provableSCC : Cert evPreds Ust -> ⊢ Q
provableSCC c =
  mp (betaElimPC St (provableEachSCC c)) stateCompletePC

-- The shape of the certificate: removedBlock, removedSink, then emptied.

sccShape : List CertStep
sccShape = [ (λ fi -> []) , certShape ] sccGraph

------------------------------------------------------------------------
-- A countermodel from a lasso.
--
-- v0 contains ¬ Q, so it does not contain Q (valOf reads ¬ as ¬ᵇ); Hintikka's
-- lemma at stage 0 transfers that to the evaluation.

buildCM : (v0 : Val) -> Lasso v0 -> valOf v0 (¬ Q) ≡ true
       -> LassoCountermodel Q
buildCM v0 l ev = countermodel v0 l evalFalse
  where
    evalFalse : eval v0 l Q 0 ≡ false
    evalFalse = trans (sym (hintStart v0 l Q (there (sub-self Q))))
                      (¬ᵇ-true (valOf v0 Q) ev)

-- A fair circuit through r, reached from a state s containing ¬ Q, is a fair
-- loop from s, and so a countermodel.

fairCountermodel : FairIn Ust evPreds -> LassoCountermodel Q
fairCountermodel (fairIn r mr c) =
  buildCM seed (sccLasso seed seedIn (fairLoop r reaches c)) seedHolds
  where open Seeded (ustSeedTo r mr)

------------------------------------------------------------------------
-- The decision: the search's certificate gives a derivation, its fair
-- component a countermodel.

decide : ⊢ Q ⊎ LassoCountermodel Q
decide with sccGraph
... | inl fair = inr (fairCountermodel fair)
... | inr cert = inl (provableSCC cert)

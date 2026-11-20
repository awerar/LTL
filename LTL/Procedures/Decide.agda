{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Procedures.Decide -- the decision procedure:
--
--   decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
--
-- It searches Ust (¬ Q) for a fair component (sccGraph).  A certificate gives
-- a derivation (provableSCC, LTL.SCC.SccExtract).  A fair component gives a
-- countermodel, in three steps:
--
--   1. ustSeedTo: the component's representative is reached from a state s
--      containing ¬ Q.  Stem and circuit form a FairLoop from s.
--   2. sccLasso: a fair loop in Ust (¬ Q) is a Lasso.
--   3. buildCM: Hintikka's lemma at stage 0.
--
-- The search runs on all of Ust (¬ Q), not from one vertex, because the
-- certificate has to cover every state.

module LTL.Procedures.Decide where

open import LTL.SCC.SccSeed public
open import LTL.Procedures.Answer public

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
                -> FairIn (Ust (¬ Q)) (step (¬ Q)) (evPreds (¬ Q))
                -> LassoCountermodel Q
fairCountermodel Q (fairIn r mr c) =
  let seedTo s ms es stem = ustSeedTo (¬ Q) r mr
  in  buildCM Q s (sccLasso (¬ Q) s ms (fairLoop r stem c)) es

------------------------------------------------------------------------
-- The decision

decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
decide Q with sccGraph (¬ Q)
... | inl fair = inr (fairCountermodel Q fair)
... | inr cert = inl (provableSCC Q cert)

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SCC.SccLasso -- a fair loop of the state graph is a lasso.
--
-- LTL.SCC.Graph knows nothing about formulas; this module reads its positive
-- answer, a FairLoop (a stem, a non-empty cycle, and a witness on the cycle
-- for every fairness predicate), as a Lasso.
--
-- The fairness predicate for the eventuality □ A is
--
--     evPred P A z  =  valOf P z (□ A)  or  not (valOf P z A)
--
-- "□ A is not pending at z, or A fails at z".  A cycle meeting it either
-- visits a state where the eventuality is not pending (and then, by
-- persistence, it is pending nowhere on the cycle) or one where A fails.
--
-- Fairness of the cycle: given □ A pending at the base point r, persistTo
-- from r to the witness z either fulfils it or leaves it pending at z, where
-- evPred says A fails.
--
-- A Lasso's states must lie in Uinf P, but the graph search runs on Ust P.  So
-- sccLasso takes any vertex list with an inclusion into Uinf P as a
-- hypothesis; LTL.Procedures.DecideSCC supplies it with uinfTrap.

module LTL.SCC.SccLasso where

open import LTL.Countermodel.Lasso public
open import LTL.SCC.Graph _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl public

------------------------------------------------------------------------
-- Trails are walks: Trail us (step P) has the same three fields as
-- Walk P us.

module _ (P : Formula) where

  trailWalk : (us : List Val) {v : Val} {zs : List Val} {w : Val}
           -> Trail us (step P) v zs w -> Walk P us v zs w
  trailWalk us tNil          = wnil
  trailWalk us (tCons m e t) = wcons m e (trailWalk us t)

  ------------------------------------------------------------------------
  -- The fairness predicates, one per eventuality.  Their FALSITY at z is
  -- exactly what the refutation consumes (□ A pending, A holding); here only
  -- their truth at a witness is used.

  evPred : Formula -> Val -> Bool
  evPred A z = valOf P z (□ A) ∨ᵇ ¬ᵇ valOf P z A

  evPreds : List Pred
  evPreds = map evPred (□Args (sub P))

  evPredsMem : {A : Formula} -> A ∈ □Args (sub P)
            -> evPred A ∈ evPreds
  evPredsMem m = memMap evPred m

  evPredsInv : {g : Pred} -> g ∈ evPreds
            -> Σ[ A ∈ Formula ] A ∈ □Args (sub P) × g ≡ evPred A
  evPredsInv m = map-mem-inv evPred (□Args (sub P)) m

  -- Reading a witness: the predicate holds at z and the eventuality is still
  -- pending there, so the first disjunct is out and the second says A fails.

  evWitness : (A : Formula) (z : Val)
           -> evPred A z ≡ true -> valOf P z (□ A) ≡ false
           -> valOf P z A ≡ false
  evWitness A z ez pd =
    sumElim (λ e1 -> emptyElim (true≢false (trans (sym e1) pd)))
            (λ e2 -> ¬ᵇ-true (valOf P z A) e2)
            (∨ᵇ-true (valOf P z (□ A)) (¬ᵇ valOf P z A) ez)

  ------------------------------------------------------------------------
  -- Persistence to a state VISITED, not to the endpoint: walkPersist with the
  -- target carried along and the walk cut short when it is reached.

  persistTo : (us : List Val) (A : Formula) -> □ A ∈ sub P
           -> {v : Val} {ws : List Val} {x : Val} -> Walk P us v ws x
           -> valOf P v (□ A) ≡ false
           -> {z : Val} -> z ∈ ws
           -> Fulfil P A v ws ⊎ valOf P z (□ A) ≡ false
  persistTo us A mb wnil e ()
  persistTo us A mb (wcons {v} {w} {ws} {x} mw st wk) e {z} mz =
    onA z mz
    where
      onA : (y : Val) -> y ∈ w ∷ ws
         -> Fulfil P A v (w ∷ ws) ⊎ valOf P y (□ A) ≡ false
      onA y my with valOf P v A in ea
      ... | false = inl (ful v here ea)
      onA y here      | true = inr (persist P v w A mb st e ea)
      onA y (there k) | true =
        sumElim (λ f -> inl (fulfilCons f)) inr
                (persistTo us A mb wk (persist P v w A mb st e ea) k)

  ------------------------------------------------------------------------
  -- A FairLoop inside any vertex list contained in Uinf P is a Lasso.  The
  -- cycle is non-empty, so it splits at its head q, and the first edge of its
  -- trail is the lasso's closing step from the base point r to q.

  sccLasso : (vs : List Val)
          -> vs ⊆ Uinf P
          -> (v0 : Val) -> v0 ∈ Uinf P
          -> FairLoop vs (step P) evPreds v0 -> Lasso P v0
  sccLasso vs sb v0 mv0 (fairLoop r st [] ts tc () wit)
  sccLasso vs sb v0 mv0 (fairLoop r st cy@(q ∷ qs) ts (tCons mq e tqs) nn wit) =
    mkLasso cyc fair (st ++ cy)
            (vpos v0 (st ++ cy) mv0 (walkApp P (Uinf P) wst wcy))
    where
      wst : Walk P (Uinf P) v0 st r
      wst = trailWalk (Uinf P) (trailMono vs (Uinf P) (step P) sb ts)

      wqs : Walk P (Uinf P) q qs r
      wqs = trailWalk (Uinf P) (trailMono vs (Uinf P) (step P) sb tqs)

      wcy : Walk P (Uinf P) r cy r
      wcy = wcons (sb q mq) e wqs

      cyc : Cycle P
      cyc = mkCycle r (q , qs) (vpos q qs (sb q mq) wqs) e

      -- Pending at the base point: go out to the witness the graph layer
      -- chose for evPred P A.
      fair : Fair P cyc
      fair A mA pr = onW (wit (evPred A) (evPredsMem mA))
        where
          onW : (Σ[ z ∈ Val ] z ∈ cy × evPred A z ≡ true)
             -> Fulfil P A r cy
          onW (z , mz , ez) =
            sumElim (λ f -> f)
                    (λ pz -> ful z (there mz) (evWitness A z ez pz))
                    (persistTo (Uinf P) A (□Args-mem (sub P) mA) wcy pr mz)

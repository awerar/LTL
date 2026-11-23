{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SCC.SccLasso -- a fair loop of the state graph is a lasso.
--
-- LTL.Lib.FairGraph knows nothing about formulas; this module reads its positive
-- answer, a FairLoop (a stem, then a Circuit: a non-empty cycle with a witness
-- on it for every fairness predicate), as a Lasso.  Its application at step P
-- is made in LTL.Countermodel.Walk, whose Trail is the lasso's path type.
--
-- The fairness predicate for the eventuality □ A is
--
--     evPred A z  =  valOf z (□ A)  or  not (valOf z A)
--
-- "□ A is not pending at z, or A fails at z".  A cycle meeting it either
-- visits a state where the eventuality is not pending (and then, by
-- persistence, it is pending nowhere on the cycle) or one where A fails.
--
-- Fairness of the cycle: given □ A pending at the base point r, persistTo
-- from r to the witness z either fulfils it or leaves it pending at z, where
-- evPred says A fails.  The graph search runs on Ust P, whose members are
-- states, so its loops are lassos as they stand.

open import LTL.Syntax.Formula using (Formula)

module LTL.SCC.SccLasso (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Step P
open import LTL.States.Closure P
open import LTL.Countermodel.Walk P
open import LTL.Countermodel.Lasso P
------------------------------------------------------------------------
-- The fairness predicates, one per eventuality.  Their FALSITY at z is
-- exactly what the refutation consumes (□ A pending, A holding); here only
-- their truth at a witness is used.

evPred : Formula -> Val -> Bool
evPred A z = valOf z (□ A) ∨ᵇ ¬ᵇ valOf z A

evPreds : List Pred
evPreds = map evPred (eventualities)

evPredsMem : {A : Formula} -> A ∈ eventualities
          -> evPred A ∈ evPreds
evPredsMem m = memMap evPred m

evPredsInv : {g : Pred} -> g ∈ evPreds
          -> ∃[ A ∈ eventualities ] g ≡ evPred A
evPredsInv m = map-mem-inv evPred (eventualities) m

-- Reading a witness: the predicate holds at z and the eventuality is still
-- pending there, so the first disjunct is out and the second says A fails.

evWitness : (A : Formula) (z : Val)
         -> evPred A z ≡ true -> valOf z (□ A) ≡ false
         -> valOf z A ≡ false
evWitness A z ez pd =
  sumElim (λ e1 -> emptyElim (true≢false (trans (sym e1) pd)))
          (λ e2 -> ¬ᵇ-true (valOf z A) e2)
          (∨ᵇ-true (valOf z (□ A)) (¬ᵇ valOf z A) ez)

------------------------------------------------------------------------
-- Persistence to a state VISITED, not to the endpoint: trailPersist with the
-- target carried along and the walk cut short when it is reached.

persistTo : (us : List Val) (A : Formula) -> □ A ∈ sub P
         -> {v : Val} {ws : List Val} {x : Val} -> Trail us v ws x
         -> valOf v (□ A) ≡ false
         -> {z : Val} -> z ∈ ws
         -> Fulfil A v ws ⊎ valOf z (□ A) ≡ false
persistTo us A mb tNil e ()
persistTo us A mb (tCons {v} {w} {ws} {x} mw st wk) e {z} mz =
  onA z mz
  where
    onA : (y : Val) -> y ∈ w ∷ ws
       -> Fulfil A v (w ∷ ws) ⊎ valOf y (□ A) ≡ false
    onA y my with valOf v A in ea
    ... | false = inl (ful v here ea)
    onA y here      | true = inr (persist v w A mb st e ea)
    onA y (there k) | true =
      sumElim (λ f -> inl (fulfilCons f)) inr
              (persistTo us A mb wk (persist v w A mb st e ea) k)

------------------------------------------------------------------------
-- A FairLoop in Ust is a Lasso.  The cycle is non-empty, so it splits at
-- its head q, and the first edge of its trail is the lasso's closing step
-- from the base point r to q.

sccLasso : (v0 : Val) -> v0 ∈ Ust
        -> FairLoop Ust evPreds v0 -> Lasso v0
sccLasso v0 mv0 (fairLoop r stem (circuit (loopBy [] tc ()) wit))
sccLasso v0 mv0 (fairLoop r (reachesBy st ts)
                          (circuit (loopBy cy@(q ∷ qs) (tCons mq e tqs) nn) wit)) =
  mkLasso cyc fair (st ++ cy)
          (vpos v0 (st ++ cy) mv0 (trailApp Ust ts tcy))
  where
    tcy : Trail Ust r cy r
    tcy = tCons mq e tqs

    cyc : Cycle
    cyc = mkCycle r (q , qs) (vpos q qs mq tqs) e

    -- Pending at the base point: go out to the witness the graph layer
    -- chose for evPred A.
    fair : Fair cyc
    fair A mA pr = onW (wit (evPred A) (evPredsMem mA))
      where
        onW : (∃[ z ∈ cy ] evPred A z ≡ true)
           -> Fulfil A r cy
        onW (z , mz , ez) =
          sumElim (λ f -> f)
                  (λ pz -> ful z (there mz) (evWitness A z ez pz))
                  (persistTo Ust A (evSub mA) tcy pr mz)

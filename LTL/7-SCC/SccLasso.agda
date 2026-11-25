{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.7-SCC.SccLasso -- a fair loop of the state graph is a lasso.
--
-- LTL.1-Lib.FairGraph knows nothing about formulas; this module reads its positive
-- answer, a FairLoop (a stem, then a Circuit: a non-empty cycle with a witness
-- on it for every fairness predicate), as a Lasso.  Its application at step P
-- is made in LTL.6-Countermodel.Walk, whose Trail is the lasso's path type.
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

open import LTL.2-Syntax.Formula using (Formula)

module LTL.7-SCC.SccLasso (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.Closure P
open import LTL.6-Countermodel.Walk P
open import LTL.6-Countermodel.Lasso P
------------------------------------------------------------------------
-- The fairness predicates, one per eventuality.  Their FALSITY at z is
-- exactly what the refutation consumes (□ A pending, A holding); here only
-- their truth at a witness is used.

evPred : Formula -> Val -> Bool
evPred A z = valOf z (□ A) ∨ᵇ ¬ᵇ valOf z A

evPreds : List Pred
evPreds = map evPred (eventualities)

∈-evPreds⁺ : ∀ⁱ[ A ∈ eventualities ] evPred A ∈ evPreds
∈-evPreds⁺ m = ∈-map⁺ evPred m

∈-evPreds⁻ : ∀ⁱ[ g ∈ evPreds ] ∃[ A ∈ eventualities ] g ≡ evPred A
∈-evPreds⁻ m = ∈-map⁻ evPred (eventualities) m

-- Reading a witness: the predicate holds at z and the eventuality is still
-- pending there, so the first disjunct is out and the second says A fails.

evWitness : (A : Formula) (z : Val)
         -> evPred A z ≡ true -> valOf z (□ A) ≡ false
         -> valOf z A ≡ false
evWitness A z ez pd =
  [ (λ e1 -> emptyElim (true≢false (trans (sym e1) pd)))
  , ¬ᵇ-true (valOf z A)
  ] (∨ᵇ-true (valOf z (□ A)) (¬ᵇ valOf z A) ez)

------------------------------------------------------------------------
-- Persistence to a state VISITED, not to the endpoint: trailPersist with the
-- target carried along and the walk cut short when it is reached.

persistTo : (A : Formula) -> □ A ∈ sub P
         -> {v : Val} {ws : List Val} {x : Val} -> Trail v ws x
         -> valOf v (□ A) ≡ false
         -> ∀ⁱ[ z ∈ ws ] (Fulfil A v ws ⊎ valOf z (□ A) ≡ false)
persistTo A mb tNil e ()
persistTo A mb (tCons {v} {w} {ws} {x} st wk) e {z} mz =
  onA z mz
  where
    onA : (y : Val) -> y ∈ w ∷ ws
       -> Fulfil A v (w ∷ ws) ⊎ valOf y (□ A) ≡ false
    onA y my with valOf v A in ea
    ... | false = inl (ful v here ea)
    onA y here      | true = inr (persist v w A mb st e ea)
    onA y (there k) | true =
      [ (λ f -> inl (fulfilCons f)) , inr ]
        (persistTo A mb wk (persist v w A mb st e ea) k)

------------------------------------------------------------------------
-- A FairLoop in Ust is a Lasso.  The loop's cycle is q ∷ qs, and the first
-- edge of its trail is the lasso's closing step from the base point r to q.

sccLasso : (v0 : Val) -> v0 ∈ Ust
        -> FairLoop Ust evPreds v0 -> Lasso v0
sccLasso v0 mv0 (fairLoop r (reachesBy st ts sst)
                          (circuit (loopBy q qs (tCons e tqs) scy) wit)) =
  mkLasso cyc fair (st ++ cy)
          (vpos v0 (st ++ cy) (trailApp ts tcy) (∷-⊆ mv0 (++-⊆ st sst scy)))
  where
    cy : List Val
    cy = q ∷ qs

    tcy : Trail r cy r
    tcy = tCons e tqs

    cyc : Cycle
    cyc = mkCycle r (q , qs) (vpos q qs tqs scy) e

    -- Pending at the base point: go out to the witness the graph layer
    -- chose for evPred A.
    fair : Fair cyc
    fair A mA pr = onW (wit (evPred A) (∈-evPreds⁺ mA))
      where
        onW : (∃[ z ∈ cy ] z ∈ᵖ evPred A)
           -> Fulfil A r cy
        onW (z , mz , ez) =
          [ (λ f -> f) , (λ pz -> ful z (there mz) (evWitness A z ez pz)) ]
            (persistTo A (evSub mA) tcy pr mz)

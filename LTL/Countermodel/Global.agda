{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Global -- every eventuality pending at a position of a lasso
-- is fulfilled at a position of its forward orbit.
--
-- A valid position (s , rest) carries a walk from s to b, the cycle's end,
-- wherever on the lasso s sits.  trailPersist along that walk gives either a
-- fulfilling state among s ∷ rest, or the eventuality still pending at b,
-- where fairness finishes it.  So stem and cycle need no separate cases.
--
-- The conclusion is membership in the forward orbit, the form Hintikka's
-- lemma needs: □ A evaluates as a conjunction over the orbit, so a false
-- conjunct refutes it.  globalFulfilAfter restates it as "at a later stage".

open import LTL.Syntax.Formula using (Formula)

module LTL.Countermodel.Global (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Step P
open import LTL.States.Closure P
open import LTL.Countermodel.Walk P
open import LTL.Countermodel.Lasso P

------------------------------------------------------------------------
-- Fulfilment along the orbit

-- Both lemmas are about a fair cycle.

module _ (cy : Cycle) (fair : Fair cy) where

  open Cycle cy

  globalFulfil : {pos : Pos} -> ValidPos b pos
              -> (A : Formula) -> A ∈ □Args (sub P)
              -> valOf (posState pos) (□ A) ≡ false
              -> Σ[ q ∈ Pos ] q ∈ orbit loop pos ×
                                  valOf (posState q) A ≡ false
  globalFulfil (vpos s rest ms wk) A mA pend =
    sumElim onStem onCycle
            (trailPersist Ust A (□Args-mem (sub P) mA) wk pend)
    where
      place : (q : Pos) -> q ∈ orbit loop (s , rest) -> {z : Val}
           -> posState q ≡ z -> valOf z A ≡ false
           -> Σ[ q' ∈ Pos ] q' ∈ orbit loop (s , rest) ×
                                 valOf (posState q') A ≡ false
      place q mq eq ez =
        q , mq , subst (λ y -> valOf y A ≡ false) (sym eq) ez

      -- fulfilled before b is reached
      onStem : Fulfil A s rest
            -> Σ[ q ∈ Pos ] q ∈ orbit loop (s , rest) ×
                                valOf (posState q) A ≡ false
      onStem (ful z mz ez) = fromStretch (stretch-mem (s , rest) mz)
        where
          fromStretch : (Σ[ q ∈ Pos ] q ∈ stretch (s , rest) × posState q ≡ z)
                -> Σ[ q ∈ Pos ] q ∈ orbit loop (s , rest) ×
                                    valOf (posState q) A ≡ false
          fromStretch (q , mq , eq) =
            place q (stretch⊆orbit loop (s , rest) q mq) eq ez

      -- still pending at b: fairness fulfils it on the cycle
      onCycle : valOf b (□ A) ≡ false
             -> Σ[ q ∈ Pos ] q ∈ orbit loop (s , rest) ×
                                 valOf (posState q) A ≡ false
      onCycle pb = fromFul (fair A mA pb)
        where
          fromFul : Fulfil A b (stretchStates loop)
                 -> Σ[ q ∈ Pos ] q ∈ orbit loop (s , rest) ×
                                     valOf (posState q) A ≡ false
          fromFul (ful z mz ez) =
            fromStretch (stretch-mem loop (cycMem (endOnCycle cy) mz))
            where
              fromStretch : (Σ[ q ∈ Pos ] q ∈ loopStretch loop ×
                                         posState q ≡ z)
                    -> Σ[ q ∈ Pos ] q ∈ orbit loop (s , rest) ×
                                        valOf (posState q) A ≡ false
              fromStretch (q , mq , eq) =
                place q (loopStretch⊆orbit loop (s , rest) q mq) eq ez

  ------------------------------------------------------------------------
  -- Some LATER stage of the run fulfils it: j = i + t, so j >= i is built
  -- into the statement.

  globalFulfilAfter : (start : Pos) (i : Nat)
                   -> ValidPos b (posIter loop i start)
                   -> (A : Formula) -> A ∈ □Args (sub P)
                   -> valOf (posState (posIter loop i start)) (□ A) ≡ false
                   -> Σ[ t ∈ Nat ]
                        valOf (posState (posIter loop (i + t) start)) A ≡ false
  globalFulfilAfter start i vp A mA pend =
    fromOrbit (globalFulfil vp A mA pend)
    where
      fromOrbit : (Σ[ q ∈ Pos ] q ∈ orbit loop (posIter loop i start) ×
                                    valOf (posState q) A ≡ false)
               -> Σ[ t ∈ Nat ]
                    valOf (posState (posIter loop (i + t) start)) A ≡ false
      fromOrbit (q , mq , eq) =
        fromIter (∈orbit-iter loop (posIter loop i start) q mq)
        where
          fromIter : (Σ[ t ∈ Nat ] posIter loop t (posIter loop i start) ≡ q)
                  -> Σ[ t ∈ Nat ]
                       valOf (posState (posIter loop (i + t) start)) A ≡ false
          fromIter (t , et) =
            t , subst (λ r -> valOf (posState r) A ≡ false)
                      (sym (trans (posIter-+ˡ loop i t start) et))
                      eq

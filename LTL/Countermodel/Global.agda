{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Global -- every eventuality pending at a position of a run
-- is fulfilled at a position of its forward orbit.
--
-- A valid position (s , rest) carries a walk from s to b, the cycle's end,
-- wherever on the run s sits.  walkPersist along that walk gives either a
-- fulfilling state among s ∷ rest, or the eventuality still pending at b,
-- where the run's cycle-fulfilment field finishes it.  So stem and cycle need
-- no separate cases.
--
-- The conclusion is membership in the forward orbit, the form Hintikka's
-- lemma needs: □ A evaluates as a conjunction over the orbit, so a false
-- conjunct refutes it.  globalFulfilAfter restates it as "at a later stage".

module LTL.Countermodel.Global where

open import LTL.Countermodel.Run public

------------------------------------------------------------------------
-- b is a state of the cycle, so the two readings of "on the cycle" agree

cycMem : {b z : Val} {c0 : Val} {c1 : List Val}
      -> b ∈ c0 ∷ c1 -> z ∈ b ∷ c0 ∷ c1 -> z ∈ c0 ∷ c1
cycMem mb here      = mb
cycMem mb (there m) = m

------------------------------------------------------------------------
-- Fulfilment along the orbit

-- Both lemmas are about a run whose cycle c0 ∷ c1 passes through b, with every
-- box pending on b ∷ c0 ∷ c1 fulfilled on the cycle (the cyc field of Run).

module _ (P : Formula) (b c0 : Val) (c1 : List Val)
         (mbc : b ∈ c0 ∷ c1) (cyc : AllFulfilled P b (c0 ∷ c1) (b ∷ c0 ∷ c1))
         where

  globalFulfil : {pos : Pos} -> ValidPos P b pos
              -> (A : Formula) -> A ∈ □Args (sub P)
              -> valOf P (posState pos) (□ A) ≡ false
              -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 pos ×
                                  valOf P (posState q) A ≡ false
  globalFulfil (vpos s rest ms wk) A mA pend =
    sumElim onStem onCycle
            (walkPersist P (Uinf P) A (□Args-mem (sub P) mA) wk pend)
    where
      place : (q : Pos) -> q ∈ orbitOf c0 c1 (s , rest) -> {z : Val}
           -> posState q ≡ z -> valOf P z A ≡ false
           -> Σ[ q' ∈ Pos ] q' ∈ orbitOf c0 c1 (s , rest) ×
                                 valOf P (posState q') A ≡ false
      place q mq eq ez =
        q , mq , subst (λ y -> valOf P y A ≡ false) (sym eq) ez

      -- fulfilled before b is reached
      onStem : Fulfil P A s rest
            -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                                valOf P (posState q) A ≡ false
      onStem (ful z mz ez) = fromPL (posList-mem s rest mz)
        where
          fromPL : (Σ[ q ∈ Pos ] q ∈ posList s rest × posState q ≡ z)
                -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                                    valOf P (posState q) A ≡ false
          fromPL (q , mq , eq) =
            place q (orbitStem c0 c1 s rest q mq) eq ez

      -- still pending at b: the cycle-fulfilment field fulfils it on the cycle
      onCycle : valOf P b (□ A) ≡ false
             -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                                 valOf P (posState q) A ≡ false
      onCycle pb = fromFul (cyc b here A mA pb)
        where
          fromFul : Fulfil P A b (c0 ∷ c1)
                 -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                                     valOf P (posState q) A ≡ false
          fromFul (ful z mz ez) = fromPL (posList-mem c0 c1 (cycMem mbc mz))
            where
              fromPL : (Σ[ q ∈ Pos ] q ∈ posList c0 c1 ×
                                         posState q ≡ z)
                    -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                                        valOf P (posState q) A ≡ false
              fromPL (q , mq , eq) =
                place q (orbitCycle c0 c1 s rest q mq) eq ez

  ------------------------------------------------------------------------
  -- Some LATER stage of the run fulfils it: j = i + t, so j >= i is built
  -- into the statement.

  globalFulfilAfter : (start : Pos) (i : Nat)
                   -> ValidPos P b (posIter c0 c1 i start)
                   -> (A : Formula) -> A ∈ □Args (sub P)
                   -> valOf P (posState (posIter c0 c1 i start)) (□ A) ≡ false
                   -> Σ[ t ∈ Nat ]
                        valOf P (posState (posIter c0 c1 (i + t) start)) A ≡ false
  globalFulfilAfter start i vp A mA pend =
    fromOrbit (globalFulfil vp A mA pend)
    where
      fromOrbit : (Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (posIter c0 c1 i start) ×
                                    valOf P (posState q) A ≡ false)
               -> Σ[ t ∈ Nat ]
                    valOf P (posState (posIter c0 c1 (i + t) start)) A ≡ false
      fromOrbit (q , mq , eq) =
        fromIter (orbitOf-iter c0 c1 (posIter c0 c1 i start) q mq)
        where
          fromIter : (Σ[ t ∈ Nat ] posIter c0 c1 t (posIter c0 c1 i start) ≡ q)
                  -> Σ[ t ∈ Nat ]
                       valOf P (posState (posIter c0 c1 (i + t) start)) A ≡ false
          fromIter (t , et) =
            t , subst (λ r -> valOf P (posState r) A ≡ false)
                      (sym (trans (posIter-plus c0 c1 i t start) et))
                      eq

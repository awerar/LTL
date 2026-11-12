{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Global -- G24 of FORMALISATION-PLAN.md, Lemma 5.4 of m4.tex.
--
--   For every i and every □ A in Sub(phi) with □ A not in v_i, there is
--   j >= i with A not in v_j.
--
-- The note's proof splits on whether v_i lies on the cycle or on the stem, and
-- runs persistence forward along the stem to reduce the second case to the
-- first.  Here there is no such split: walkPersist does both at once.  A valid
-- position (s , rest) carries a walk from s to b, the cycle's end, whatever
-- part of the run s sits on; applying persistence to that walk gives either a
-- fulfilling state among s ∷ rest -- which is the stem case, and also the
-- "fulfilled before the cycle closes" half of the cycle case -- or the
-- eventuality still pending at b, where the cycle-fulfilment property of
-- Proposition 5.3 finishes it.
--
-- The conclusion is stated as membership in the forward orbit, which is the
-- form G27 needs: [[□ A]] is a conjunction over the orbit, so a false
-- conjunct is exactly what refutes it.  globalFulfilAfter recovers the note's
-- "j >= i" reading from it.

module LTL.Global where

open import LTL.Run public

------------------------------------------------------------------------
-- b is a state of the cycle, so the two readings of "on the cycle" agree

cycMem : {b z : Val} {c0 : Val} {c1 : List Val}
      -> b ∈ c0 ∷ c1 -> z ∈ b ∷ c0 ∷ c1 -> z ∈ c0 ∷ c1
cycMem mb here      = mb
cycMem mb (there m) = m

------------------------------------------------------------------------
-- Lemma 5.4

globalFulfil : (P : Formula) (b c0 : Val) (c1 : List Val)
            -> b ∈ c0 ∷ c1
            -> ((s : Val) -> s ∈ b ∷ c0 ∷ c1
                  -> (A : Formula) -> A ∈ □Args (sub P)
                  -> valOf P s (□ A) ≡ false -> Fulfil P A b (c0 ∷ c1))
            -> {pos : Pos} -> ValidPos P b pos
            -> (A : Formula) -> A ∈ □Args (sub P)
            -> valOf P (posState pos) (□ A) ≡ false
            -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 pos ×
                                valOf P (posState q) A ≡ false
globalFulfil P b c0 c1 mbc cyc (vpos s rest ms wk) A mA pend =
  sumElim onStem onCycle
          (walkPersist P (Uinf P) A (□Args_mem (sub P) mA) wk pend)
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
    onStem (ful z mz ez) = fromPL (posList_mem s rest mz)
      where
        fromPL : (Σ[ q ∈ Pos ] q ∈ posList s rest × posState q ≡ z)
              -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                                  valOf P (posState q) A ≡ false
        fromPL (q , mq , eq) =
          place q (orbitStem c0 c1 s rest q mq) eq ez

    -- still pending at b: Proposition 5.3 fulfils it on the cycle
    onCycle : valOf P b (□ A) ≡ false
           -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                               valOf P (posState q) A ≡ false
    onCycle pb = fromFul (cyc b here A mA pb)
      where
        fromFul : Fulfil P A b (c0 ∷ c1)
               -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                                   valOf P (posState q) A ≡ false
        fromFul (ful z mz ez) = fromPL (posList_mem c0 c1 (cycMem mbc mz))
          where
            fromPL : (Σ[ q ∈ Pos ] q ∈ posList c0 c1 ×
                                       posState q ≡ z)
                  -> Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (s , rest) ×
                                      valOf P (posState q) A ≡ false
            fromPL (q , mq , eq) =
              place q (orbitCycle c0 c1 s rest q mq) eq ez

------------------------------------------------------------------------
-- The note's reading: some LATER state of the run fulfils it.
--
-- j = i + t, so j >= i is built into the statement rather than asserted.

globalFulfilAfter : (P : Formula) (b c0 : Val) (c1 : List Val)
                 -> b ∈ c0 ∷ c1
                 -> ((s : Val) -> s ∈ b ∷ c0 ∷ c1
                       -> (A : Formula) -> A ∈ □Args (sub P)
                       -> valOf P s (□ A) ≡ false -> Fulfil P A b (c0 ∷ c1))
                 -> (start : Pos) (i : Nat)
                 -> ValidPos P b (posIter c0 c1 i start)
                 -> (A : Formula) -> A ∈ □Args (sub P)
                 -> valOf P (posState (posIter c0 c1 i start)) (□ A) ≡ false
                 -> Σ[ t ∈ Nat ]
                      valOf P (posState (posIter c0 c1 (i + t) start)) A ≡ false
globalFulfilAfter P b c0 c1 mbc cyc start i vp A mA pend =
  fromOrbit (globalFulfil P b c0 c1 mbc cyc vp A mA pend)
  where
    fromOrbit : (Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 (posIter c0 c1 i start) ×
                                  valOf P (posState q) A ≡ false)
             -> Σ[ t ∈ Nat ]
                  valOf P (posState (posIter c0 c1 (i + t) start)) A ≡ false
    fromOrbit (q , mq , eq) =
      fromIter (orbitOf_iter c0 c1 (posIter c0 c1 i start) q mq)
      where
        fromIter : (Σ[ t ∈ Nat ] posIter c0 c1 t (posIter c0 c1 i start) ≡ q)
                -> Σ[ t ∈ Nat ]
                     valOf P (posState (posIter c0 c1 (i + t) start)) A ≡ false
        fromIter (t , et) =
          t , subst (λ r -> valOf P (posState r) A ≡ false)
                    (sym (trans (posIter_plus c0 c1 i t start) et))
                    eq

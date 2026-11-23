{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Hintikka -- Hintikka's lemma: on a lasso, the state's bit
-- for a subformula agrees with its evaluation,
--
--   valOf (state at pos) A  =  evalAt loop A pos        for A in sub P,
--
-- where loop is the position the lasso loops back to.
--
-- By induction on A:
--
--   var       evalAt reads the state through valOf.
--   ¬, ⇒      valOf and evalAt are both ¬ᵇ at ¬ and ⇒ᵇ at ⇒.
--   ○         (T1), at the transition posStep supplies.
--   □         If □ A is in the state, (T2) carries it along the run (carry)
--             and (S2) gives A at every stage of the orbit.  If not,
--             globalFulfil gives a position of the orbit where A fails,
--             which refutes the conjunction.
--
-- globalFulfil, proved first, is where fairness enters: every eventuality
-- pending at a position of a fair lasso is fulfilled in its forward orbit.

open import LTL.Syntax.Formula using (Formula)

module LTL.Countermodel.Hintikka (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Step P
open import LTL.States.Closure P
open import LTL.Countermodel.Walk P
open import LTL.Countermodel.Lasso P

------------------------------------------------------------------------
-- Fulfilment along the orbit
--
-- A valid position (s , rest) carries a walk from s to b, the cycle's end.
-- trailPersist along it gives either a fulfilling state among s ∷ rest, or
-- the eventuality still pending at b, where fairness finishes it.  So stem and
-- cycle need no separate cases.  Both lemmas are about a fair cycle.

module _ (cy : Cycle) (fair : Fair cy) where

  open Cycle cy

  globalFulfil : {pos : Pos} -> ValidPos b pos
              -> (A : Formula) -> A ∈ □Args (sub P)
              -> valOf (posState pos) (□ A) ≡ false
              -> ∃[ q ∈ orbit loop pos ] valOf (posState q) A ≡ false
  globalFulfil (vpos s rest ms wk) A mA pend =
    sumElim onStem onCycle
            (trailPersist Ust A (□Args-mem (sub P) mA) wk pend)
    where
      place : (q : Pos) -> q ∈ orbit loop (s , rest) -> {z : Val}
           -> posState q ≡ z -> valOf z A ≡ false
           -> ∃[ q' ∈ orbit loop (s , rest) ] valOf (posState q') A ≡ false
      place q mq eq ez =
        q , mq , subst (λ y -> valOf y A ≡ false) (sym eq) ez

      -- fulfilled before b is reached
      onStem : Fulfil A s rest
            -> ∃[ q ∈ orbit loop (s , rest) ] valOf (posState q) A ≡ false
      onStem (ful z mz ez) = fromStretch (stretch-mem (s , rest) mz)
        where
          fromStretch : (∃[ q ∈ stretch (s , rest) ] posState q ≡ z)
                -> ∃[ q ∈ orbit loop (s , rest) ] valOf (posState q) A ≡ false
          fromStretch (q , mq , eq) =
            place q (stretch⊆orbit loop (s , rest) q mq) eq ez

      -- still pending at b: fairness fulfils it on the cycle
      onCycle : valOf b (□ A) ≡ false
             -> ∃[ q ∈ orbit loop (s , rest) ] valOf (posState q) A ≡ false
      onCycle pb = fromFul (fair A mA pb)
        where
          fromFul : Fulfil A b (stretchStates loop)
                 -> ∃[ q ∈ orbit loop (s , rest) ] valOf (posState q) A ≡ false
          fromFul (ful z mz ez) =
            fromStretch (stretch-mem loop (cycMem (endOnCycle cy) mz))
            where
              fromStretch : (∃[ q ∈ loopStretch loop ] posState q ≡ z)
                    -> ∃[ q ∈ orbit loop (s , rest) ]
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
      fromOrbit : (∃[ q ∈ orbit loop (posIter loop i start) ]
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

------------------------------------------------------------------------
-- Reading (S2) off a state of Ust

□S2 : (s : Val) -> s ∈ Ust -> (B : Formula)
   -> □ B ∈ sub P -> valOf s (□ B) ≡ true -> valOf s B ≡ true
□S2 s m B mb e =
  ⇒ᵇ-mp (valOf s (□ B)) (valOf s B)
        (all-at (s2At s) (□Args (sub P)) (□Args-of (sub P) mb) (ustState m)) e

------------------------------------------------------------------------
-- (T2) along the run, and its consequence at every position of an orbit

-- The lemmas below share the cycle of a lasso.

module _ (cy : Cycle) where

  open Cycle cy

  □Along : (B : Formula) -> □ B ∈ sub P
        -> (t : Nat) (pos : Pos) -> ValidPos b pos
        -> valOf (posState pos) (□ B) ≡ true
        -> valOf (posState (posIter loop t pos)) (□ B) ≡ true
  □Along B mb zero    pos vp e = e
  □Along B mb (suc t) pos vp e =
    □Along B mb t (nextPos loop pos)
             (fst (posStep cy vp))
             (carry (posState pos) (posState (nextPos loop pos)) B mb
                    (snd (posStep cy vp)) e)

  □True : (B : Formula) -> □ B ∈ sub P
       -> (pos q : Pos) -> ValidPos b pos -> q ∈ orbit loop pos
       -> valOf (posState pos) (□ B) ≡ true
       -> valOf (posState q) B ≡ true
  □True B mb pos q vp m e =
    orbit-all loop (λ r -> valOf (posState r) B ≡ true) pos
      (λ t -> □S2 (posState (posIter loop t pos))
                  (posIn b (posIterValid cy t pos vp))
                  B mb (□Along B mb t pos vp e))
      q m

  ------------------------------------------------------------------------
  -- Hintikka's lemma

  hintikka : Fair cy -> (A : Formula) -> A ∈ sub P
          -> (pos : Pos) -> ValidPos b pos
          -> valOf (posState pos) A ≡ evalAt loop A pos

  hintikka fair (var n) mA pos vp = refl

  hintikka fair (¬ B) mA pos vp =
    cong ¬ᵇ_ (hintikka fair B (sub-¬ P mA) pos vp)

  hintikka fair (B ⇒ C) mA pos vp =
    cong₂ _⇒ᵇ_ (hintikka fair B (sub-⇒L P mA) pos vp)
               (hintikka fair C (sub-⇒R P mA) pos vp)

  hintikka fair (○ B) mA pos vp =
    trans (⇔ᵇ-sound (valOf (posState pos) (○ B))
                    (valOf (posState (nextPos loop pos)) B)
                    (all-at (stepAt (posState pos)
                                    (posState (nextPos loop pos))) (sub P) mA
                                (snd (posStep cy vp))))
          (hintikka fair B (sub-○ P mA)
                    (nextPos loop pos) (fst (posStep cy vp)))

  hintikka fair (□ B) mA pos vp = by□
    where
      ih : (q : Pos) -> ValidPos b q
        -> valOf (posState q) B ≡ evalAt loop B q
      ih q vq = hintikka fair B (sub-□ P mA) q vq

      -- □ B holds: (T2) carries it, (S2) delivers B at every stage
      □Holds : valOf (posState pos) (□ B) ≡ true
            -> evalAt loop (□ B) pos ≡ true
      □Holds e =
        all-intro (evalAt loop B) (orbit loop pos) (λ {q} m -> atQ q m)
        where
          atQ : ∀[ q ∈ orbit loop pos ] evalAt loop B q ≡ true
          atQ q m =
            trans (sym (ih q (orbitValid cy pos q vp m)))
                  (□True B mA pos q vp m e)

      -- □ B fails: globalFulfil supplies the false conjunct
      allFalse : valOf (posState pos) (□ B) ≡ false
              -> evalAt loop (□ B) pos ≡ false
      allFalse e =
        fromGF (globalFulfil cy fair vp B (□Args-of (sub P) mA) e)
        where
          fromGF : (∃[ q ∈ orbit loop pos ] valOf (posState q) B ≡ false)
                -> evalAt loop (□ B) pos ≡ false
          fromGF (q , mq , eq) =
            eval□-false loop B pos q mq
              (trans (sym (ih q (orbitValid cy pos q vp mq)))
                     eq)

      by□ : valOf (posState pos) (□ B) ≡ evalAt loop (□ B) pos
      by□ with valOf (posState pos) (□ B) in e
      ... | true  = sym (□Holds e)
      ... | false = sym (allFalse e)

------------------------------------------------------------------------
-- Hintikka's lemma on a lasso, at every stage and at the start

hintLasso : (v0 : Val) (l : Lasso v0) (A : Formula) -> A ∈ sub P
       -> (i : Nat) -> valOf (stateAt v0 l i) A ≡ eval v0 l A i
hintLasso v0 (mkLasso cy fair rest sv) A mA i =
  hintikka cy fair A mA (posIter (Cycle.loop cy) i (v0 , rest))
           (posIterValid cy i (v0 , rest) sv)

hintStart : (v0 : Val) (l : Lasso v0) -> ∀[ A ∈ sub P ]
            valOf v0 A ≡ eval v0 l A 0
hintStart v0 (mkLasso cy fair rest sv) A mA =
  hintikka cy fair A mA (v0 , rest) sv

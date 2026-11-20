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
--   ¬, ⇒      (S1), at a state of Ust.
--   ○         (T1), at the transition posStep supplies.
--   □         If □ A is in the state, (T2) carries it along the run (carry)
--             and (S2) gives A at every stage of the orbit.  If not,
--             globalFulfil (LTL.Countermodel.Global) gives a position of the
--             orbit where A fails, which refutes the conjunction.

open import LTL.Syntax.Formula using (Formula)

module LTL.Countermodel.Hintikka (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Step P
open import LTL.States.Closure P
open import LTL.Countermodel.Lasso P
open import LTL.Countermodel.Global P
open import LTL.Countermodel.Eval P

------------------------------------------------------------------------
-- Reading (S1) and (S2) off a state of Ust

stateOk : (s : Val) -> s ∈ Ust -> {A : Formula}
       -> A ∈ sub P -> okAt s A ≡ true
stateOk s m mA =
  all-at (okAt s) (sub P) mA
           (∧ᵇ-trueˡ (allOk s (sub P)) (allCoh s (length (sub P)))
                     (ustState m))

-- (S2)
□S2 : (s : Val) -> s ∈ Ust -> (B : Formula)
   -> □ B ∈ sub P -> valOf s (□ B) ≡ true -> valOf s B ≡ true
□S2 s m B mb e =
  ⇒ᵇ-mp (valOf s (□ B)) (valOf s B) (stateOk s m mb) e

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
    fromIter (∈orbit-iter loop pos q m)
    where
      fromIter : (Σ[ t ∈ Nat ] posIter loop t pos ≡ q)
              -> valOf (posState q) B ≡ true
      fromIter (t , et) =
        subst (λ r -> valOf (posState r) B ≡ true) et
              (□S2 (posState (posIter loop t pos))
                     (posIn b (posIterValid cy t pos vp))
                     B mb (□Along B mb t pos vp e))

  ------------------------------------------------------------------------
  -- Hintikka's lemma

  hintikka : Fair cy -> (A : Formula) -> A ∈ sub P
          -> (pos : Pos) -> ValidPos b pos
          -> valOf (posState pos) A ≡ evalAt loop A pos

  hintikka fair (var n) mA pos vp = refl

  hintikka fair (¬ B) mA pos vp =
    trans (⇔ᵇ-sound (valOf (posState pos) (¬ B))
                    (¬ᵇ valOf (posState pos) B)
                        (stateOk (posState pos) (posIn b vp) mA))
          (cong ¬ᵇ_
                (hintikka fair B (sub-¬ P mA) pos vp))

  hintikka fair (B ⇒ C) mA pos vp =
    trans (⇔ᵇ-sound (valOf (posState pos) (B ⇒ C))
                    (valOf (posState pos) B ⇒ᵇ valOf (posState pos) C)
                    (stateOk (posState pos) (posIn b vp) mA))
          (cong₂ _⇒ᵇ_ (hintikka fair B (sub-⇒L P mA) pos vp)
                   (hintikka fair C (sub-⇒R P mA) pos vp))

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

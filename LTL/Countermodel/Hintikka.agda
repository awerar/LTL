{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Hintikka -- Hintikka's lemma: on a lasso, the state's bit
-- for a subformula agrees with its evaluation,
--
--   valOf P (state at pos) A  =  evalAt P loop A pos        for A in sub P,
--
-- where loop is the position the lasso loops back to.
--
-- By induction on A:
--
--   var       evalAt reads the state through valOf.
--   ¬, ⇒      (S1), at a state of Uinf.
--   ○         (T1), at the transition posStep supplies.
--   □         If □ A is in the state, (T2) carries it along the run (carry)
--             and (S2) gives A at every stage of the orbit.  If not,
--             globalFulfil (LTL.Countermodel.Global) gives a position of the
--             orbit where A fails, which refutes the conjunction.

module LTL.Countermodel.Hintikka where

open import LTL.Countermodel.Sound   public
open import LTL.Elimination.Extract public

------------------------------------------------------------------------
-- Reading (S1) and (S2) off a survivor

stateOk : (P : Formula) (s : Val) -> s ∈ Uinf P -> {A : Formula}
       -> A ∈ sub P -> okAt P s A ≡ true
stateOk P s m mA =
  all-at (okAt P s) (sub P) mA
           (∧ᵇ-trueˡ (allOk P s (sub P)) (allCoh P s (length (sub P)))
                     (uinfState P s m))

-- (S2)
□S2 : (P : Formula) (s : Val) -> s ∈ Uinf P -> (B : Formula)
   -> □ B ∈ sub P -> valOf P s (□ B) ≡ true -> valOf P s B ≡ true
□S2 P s m B mb e =
  ⇒ᵇ-mp (valOf P s (□ B)) (valOf P s B) (stateOk P s m mb) e

⇒Cong : {a a' b b' : Bool} -> a ≡ a' -> b ≡ b'
     -> a ⇒ᵇ b ≡ a' ⇒ᵇ b'
⇒Cong refl refl = refl

------------------------------------------------------------------------
-- (T2) along the run, and its consequence at every position of an orbit

-- The lemmas below share the cycle of a lasso.

module _ (P : Formula) (cy : Cycle P) where

  open Cycle cy

  □Along : (B : Formula) -> □ B ∈ sub P
        -> (t : Nat) (pos : Pos) -> ValidPos P b pos
        -> valOf P (posState pos) (□ B) ≡ true
        -> valOf P (posState (posIter loop t pos)) (□ B) ≡ true
  □Along B mb zero    pos vp e = e
  □Along B mb (suc t) pos vp e =
    □Along B mb t (nextPos loop pos)
             (fst (posStep P cy vp))
             (carry P (posState pos) (posState (nextPos loop pos)) B mb
                    (snd (posStep P cy vp)) e)

  □True : (B : Formula) -> □ B ∈ sub P
       -> (pos q : Pos) -> ValidPos P b pos -> q ∈ orbit loop pos
       -> valOf P (posState pos) (□ B) ≡ true
       -> valOf P (posState q) B ≡ true
  □True B mb pos q vp m e =
    fromIter (∈orbit-iter loop pos q m)
    where
      fromIter : (Σ[ t ∈ Nat ] posIter loop t pos ≡ q)
              -> valOf P (posState q) B ≡ true
      fromIter (t , et) =
        subst (λ r -> valOf P (posState r) B ≡ true) et
              (□S2 P (posState (posIter loop t pos))
                     (posIn P b (posIterValid P cy t pos vp))
                     B mb (□Along B mb t pos vp e))

  ------------------------------------------------------------------------
  -- Hintikka's lemma

  hintikka : Fair P cy -> (A : Formula) -> A ∈ sub P
          -> (pos : Pos) -> ValidPos P b pos
          -> valOf P (posState pos) A ≡ evalAt P loop A pos

  hintikka fair (var n) mA pos vp = refl

  hintikka fair (¬ B) mA pos vp =
    trans (⇔ᵇ-sound (valOf P (posState pos) (¬ B))
                    (¬ᵇ valOf P (posState pos) B)
                        (stateOk P (posState pos) (posIn P b vp) mA))
          (cong ¬ᵇ_
                (hintikka fair B (sub-¬ P mA) pos vp))

  hintikka fair (B ⇒ C) mA pos vp =
    trans (⇔ᵇ-sound (valOf P (posState pos) (B ⇒ C))
                    (valOf P (posState pos) B ⇒ᵇ valOf P (posState pos) C)
                    (stateOk P (posState pos) (posIn P b vp) mA))
          (⇒Cong (hintikka fair B (sub-⇒L P mA) pos vp)
                   (hintikka fair C (sub-⇒R P mA) pos vp))

  hintikka fair (○ B) mA pos vp =
    trans (⇔ᵇ-sound (valOf P (posState pos) (○ B))
                    (valOf P (posState (nextPos loop pos)) B)
                    (all-at (stepAt P (posState pos)
                                    (posState (nextPos loop pos))) (sub P) mA
                                (snd (posStep P cy vp))))
          (hintikka fair B (sub-○ P mA)
                    (nextPos loop pos) (fst (posStep P cy vp)))

  hintikka fair (□ B) mA pos vp = by□
    where
      ih : (q : Pos) -> ValidPos P b q
        -> valOf P (posState q) B ≡ evalAt P loop B q
      ih q vq = hintikka fair B (sub-□ P mA) q vq

      -- □ B holds: (T2) carries it, (S2) delivers B at every stage
      □Holds : valOf P (posState pos) (□ B) ≡ true
            -> evalAt P loop (□ B) pos ≡ true
      □Holds e =
        all-intro (evalAt P loop B) (orbit loop pos) (λ {q} m -> atQ q m)
        where
          atQ : (q : Pos) -> q ∈ orbit loop pos -> evalAt P loop B q ≡ true
          atQ q m =
            trans (sym (ih q (orbitValid P cy pos q vp m)))
                  (□True B mA pos q vp m e)

      -- □ B fails: globalFulfil supplies the false conjunct
      allFalse : valOf P (posState pos) (□ B) ≡ false
              -> evalAt P loop (□ B) pos ≡ false
      allFalse e =
        fromGF (globalFulfil P cy fair vp B (□Args-of (sub P) mA) e)
        where
          fromGF : (Σ[ q ∈ Pos ] q ∈ orbit loop pos ×
                                     valOf P (posState q) B ≡ false)
                -> evalAt P loop (□ B) pos ≡ false
          fromGF (q , mq , eq) =
            eval□-false P loop B pos q mq
              (trans (sym (ih q (orbitValid P cy pos q vp mq)))
                     eq)

      by□ : valOf P (posState pos) (□ B) ≡ evalAt P loop (□ B) pos
      by□ with valOf P (posState pos) (□ B) in e
      ... | true  = sym (□Holds e)
      ... | false = sym (allFalse e)

------------------------------------------------------------------------
-- Hintikka's lemma on a lasso, at every stage and at the start

hintLasso : (P : Formula) (v0 : Val) (l : Lasso P v0) (A : Formula) -> A ∈ sub P
       -> (i : Nat) -> valOf P (stateAt P v0 l i) A ≡ eval P v0 l A i
hintLasso P v0 (mkLasso cy fair rest sv) A mA i =
  hintikka P cy fair A mA (posIter (Cycle.loop cy) i (v0 , rest))
           (posIterValid P cy i (v0 , rest) sv)

hintStart : (P : Formula) (v0 : Val) (l : Lasso P v0) (A : Formula) -> A ∈ sub P
         -> valOf P v0 A ≡ eval P v0 l A 0
hintStart P v0 (mkLasso cy fair rest sv) A mA =
  hintikka P cy fair A mA (v0 , rest) sv

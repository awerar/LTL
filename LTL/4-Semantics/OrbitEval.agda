{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.4-Semantics.OrbitEval -- the Boolean evaluation of formulas on a lasso,
-- and its soundness: every derivable formula is true at every position.
--
-- The states have any type S, and read s n is the truth value of variable n
-- in s.  LTL.6-Countermodel.Lasso takes S to be valuations; LTL.Correct takes
-- it to be LTL.Statement's Instant.
--
-- evalAt has one clause per constructor: ○ is one step of nextPos and □ A is
-- the conjunction of A over the forward orbit (LTL.4-Semantics.Orbit), so the
-- recursion is structural.  It is total on all formulas and positions, so
-- soundness holds for any derivable C at any position.
--
-- In soundness, (P1)-(P3) are Boolean tautologies, and (K ○) and (Lin) hold
-- because evalAt commutes with ○ definitionally.  (K □) is pointwise on one
-- orbit; (Exp) needs the orbit to contain the position, its successor and the
-- successor's orbit (iter∈orbit).  (Ind) is the one with content: A propagates
-- along posIter pos t by induction on t, and every member of the orbit is
-- such a posIter (orbit-all).

open import LTL.2-Syntax.Deriv

module LTL.4-Semantics.OrbitEval (S : Set) (read : S -> Nat -> Bool) where

open import LTL.4-Semantics.Orbit S

module _ (loop : Pos) where

  ------------------------------------------------------------------------
  -- The Boolean evaluation at a position

  evalAt : Formula -> Pos -> Bool
  evalAt (var n) pos = read (posState pos) n
  evalAt (¬ A)   pos = ¬ᵇ evalAt A pos
  evalAt (A ⇒ B) pos = evalAt A pos ⇒ᵇ evalAt B pos
  evalAt (○ A)   pos = evalAt A (nextPos loop pos)
  evalAt (□ A)   pos = all (evalAt A) (orbit loop pos)

  ------------------------------------------------------------------------
  -- The two ways of using it

  eval□-true : (A : Formula) (pos : Pos)
            -> evalAt (□ A) pos ≡ true
            -> ∀[ q ∈ orbit loop pos ] evalAt A q ≡ true
  eval□-true A pos = all-true (evalAt A) (orbit loop pos)

  eval□-intro : (A : Formula) (pos : Pos)
             -> (∀[ q ∈ orbit loop pos ] evalAt A q ≡ true)
             -> evalAt (□ A) pos ≡ true
  eval□-intro A pos = all-intro (evalAt A) (orbit loop pos)

  eval□-false-intro : (A : Formula) (pos : Pos)
                   -> (∃[ q ∈ orbit loop pos ] evalAt A q ≡ false)
                   -> evalAt (□ A) pos ≡ false
  eval□-false-intro A pos = all-false-intro (evalAt A) (orbit loop pos)

  ------------------------------------------------------------------------
  -- Conjunction, as (Exp) and (Lin) need it

  eval∧-intro : (A B : Formula) (pos : Pos)
             -> evalAt A pos ≡ true -> evalAt B pos ≡ true
             -> evalAt (A ∧ B) pos ≡ true
  eval∧-intro A B pos = ¬ᵇ⇒ᵇ¬ᵇ-intro (evalAt A pos) (evalAt B pos)

  ------------------------------------------------------------------------
  -- (K □)

  k□Sound : (A B : Formula) (pos : Pos)
         -> evalAt (□ (A ⇒ B) ⇒ □ A ⇒ □ B) pos ≡ true
  k□Sound A B pos =
    ⇒ᵇ-intro (evalAt (□ (A ⇒ B)) pos)
             (evalAt (□ A) pos ⇒ᵇ evalAt (□ B) pos)
             (λ e1 -> ⇒ᵇ-intro (evalAt (□ A) pos)
                               (evalAt (□ B) pos) (body e1))
    where
      body : evalAt (□ (A ⇒ B)) pos ≡ true
          -> evalAt (□ A) pos ≡ true
          -> evalAt (□ B) pos ≡ true
      body e1 e2 =
        eval□-intro B pos
          (λ q m ->
             ⇒ᵇ-mp (evalAt A q) (evalAt B q)
                   (eval□-true (A ⇒ B) pos e1 q m)
                   (eval□-true A pos e2 q m))

  ------------------------------------------------------------------------
  -- (Exp)

  expSound : (A : Formula) (pos : Pos)
          -> evalAt (□ A ⇒ A ∧ ○ A ∧ ○ □ A) pos ≡
             true
  expSound A pos =
    ⇒ᵇ-intro (evalAt (□ A) pos)
              (evalAt (A ∧ ○ A ∧ ○ □ A) pos) body
    where
      body : evalAt (□ A) pos ≡ true
          -> evalAt (A ∧ ○ A ∧ ○ □ A) pos ≡ true
      body eb =
        eval∧-intro A (○ A ∧ ○ □ A) pos
          (eval□-true A pos eb pos (iter∈orbit loop pos zero))
          (eval∧-intro (○ A) (○ □ A) pos
            (eval□-true A pos eb (nextPos loop pos)
                        (iter∈orbit loop pos (suc zero)))
            (eval□-intro A (nextPos loop pos)
                         (λ q m ->
                            eval□-true A pos eb q
                                       (nextOrbit⊆orbit loop pos q m))))

  ------------------------------------------------------------------------
  -- (Ind): A propagates along the run, since the hypothesis is available at
  -- every stage and the orbit consists exactly of those stages.

  indSound : (A : Formula) (pos : Pos)
          -> evalAt (□ (A ⇒ ○ A) ⇒ A ⇒ □ A) pos ≡ true
  indSound A pos =
    ⇒ᵇ-intro (evalAt (□ (A ⇒ ○ A)) pos)
             (evalAt A pos ⇒ᵇ evalAt (□ A) pos)
             (λ e1 -> ⇒ᵇ-intro (evalAt A pos)
                               (evalAt (□ A) pos) (body e1))
    where
      body : evalAt (□ (A ⇒ ○ A)) pos ≡ true
          -> evalAt A pos ≡ true
          -> evalAt (□ A) pos ≡ true
      body e1 e2 =
        eval□-intro A pos (orbit-all loop (λ r -> evalAt A r ≡ true) pos along)
        where
          along : (t : Nat) -> evalAt A (posIter loop pos t) ≡ true
          along zero    = e2
          along (suc t) =
            ⇒ᵇ-mp (evalAt A (posIter loop pos t))
                  (evalAt A (posIter loop pos (suc t)))
                  (eval□-true (A ⇒ ○ A) pos e1 (posIter loop pos t)
                              (iter∈orbit loop pos t))
                  (along t)

  ------------------------------------------------------------------------
  -- Soundness

  sound : {C : Formula} -> ⊢ C
       -> (pos : Pos) -> evalAt C pos ≡ true

  sound (p1 {A} {B}) pos =
    ⇒ᵇ-P1 (evalAt A pos) (evalAt B pos)

  sound (p2 {A} {B} {C}) pos =
    ⇒ᵇ-P2 (evalAt A pos) (evalAt B pos) (evalAt C pos)

  sound (p3 {A} {B}) pos =
    ⇒ᵇ-P3 (evalAt A pos) (evalAt B pos)

  sound (k□ {A} {B}) pos = k□Sound A B pos

  -- both sides are evalAt A (nextPos pos) ⇒ᵇ evalAt B (nextPos pos)
  sound (k○ {A} {B}) pos =
    ⇒ᵇ-refl (evalAt A (nextPos loop pos) ⇒ᵇ
             evalAt B (nextPos loop pos))

  sound (exp {A}) pos = expSound A pos

  sound (ind {A}) pos = indSound A pos

  -- ○ ¬ A and ¬ ○ A evaluate to the same Boolean, so both halves of
  -- the biconditional are z ⇒ᵇ z
  sound (lin {A}) pos =
    eval∧-intro (○ ¬ A ⇒ ¬ ○ A) (¬ ○ A ⇒ ○ ¬ A) pos
          (⇒ᵇ-refl (¬ᵇ evalAt A (nextPos loop pos)))
          (⇒ᵇ-refl (¬ᵇ evalAt A (nextPos loop pos)))

  -- (PC): evalAt is DEFINED by ¬ᵇ at ¬ and ⇒ᵇ at ⇒, so the two hypotheses
  -- of tautSound are refl.
  sound (pc {C} e) pos =
    tautSound (λ X -> evalAt X pos) C
              (λ X m -> refl) (λ X Y m -> refl) e

  sound (mp {A} {B} d e) pos =
    ⇒ᵇ-mp (evalAt A pos) (evalAt B pos)
             (sound d pos)
             (sound e pos)

  sound (gen {A} d) pos =
    eval□-intro A pos (λ q m -> sound d q)

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.OrbitEval -- the Boolean evaluation of formulas on a lasso,
-- and its soundness: every derivable formula is true at every position.
--
-- The states have any type S, and read s n is the truth value of variable n
-- in s.  LTL.Countermodel.Lasso takes S to be valuations; LTL.Correct takes
-- it to be LTL.Trusted's Instant.
--
-- evalAt has one clause per constructor: ○ is one step of nextPos and □ A is
-- the conjunction of A over the forward orbit (LTL.Countermodel.Orbit), so the
-- recursion is structural.  It is total on all formulas and positions, so
-- soundness holds for any derivable C at any position.
--
-- In soundness, (P1)-(P3) are Boolean tautologies, and (K ○) and (Lin) hold
-- because evalAt commutes with ○ definitionally.  (K □) is pointwise on one
-- orbit; (Exp) needs the orbit to contain the position, its successor and the
-- successor's orbit (iter∈orbit).  (Ind) is the one with content: A propagates
-- along posIter t pos by induction on t, and every member of the orbit is
-- such a posIter (∈orbit-iter).

open import LTL.Syntax.Deriv

module LTL.Countermodel.OrbitEval (S : Set) (read : S -> Nat -> Bool) where

open import LTL.Countermodel.Orbit S

------------------------------------------------------------------------
-- The Boolean tautologies behind (P1), (P2), (P3) and the identity

tautP1 : (a b : Bool) -> a ⇒ᵇ b ⇒ᵇ a ≡ true
tautP1 true  true  = refl
tautP1 true  false = refl
tautP1 false b     = refl

tautP2 : (a b c : Bool)
      -> (a ⇒ᵇ b ⇒ᵇ c) ⇒ᵇ (a ⇒ᵇ b) ⇒ᵇ a ⇒ᵇ c ≡ true
tautP2 true  true  true  = refl
tautP2 true  true  false = refl
tautP2 true  false true  = refl
tautP2 true  false false = refl
tautP2 false b     c     = refl

tautP3 : (a b : Bool)
      -> (¬ᵇ b ⇒ᵇ ¬ᵇ a) ⇒ᵇ a ⇒ᵇ b ≡ true
tautP3 true  true  = refl
tautP3 true  false = refl
tautP3 false true  = refl
tautP3 false false = refl

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

  eval□-at : (A : Formula) (pos q : Pos)
          -> evalAt (□ A) pos ≡ true -> q ∈ orbit loop pos
          -> evalAt A q ≡ true
  eval□-at A pos q e m =
    all-at (evalAt A) (orbit loop pos) m e

  eval□-intro : (A : Formula) (pos : Pos)
             -> (∀[ q ∈ orbit loop pos ] evalAt A q ≡ true)
             -> evalAt (□ A) pos ≡ true
  eval□-intro A pos f =
    all-intro (evalAt A) (orbit loop pos) (λ {q} m -> f q m)

  eval□-false : (A : Formula) (pos q : Pos)
             -> q ∈ orbit loop pos -> evalAt A q ≡ false
             -> evalAt (□ A) pos ≡ false
  eval□-false A pos q m e =
    all-atFalse (evalAt A) (orbit loop pos) m e

  ------------------------------------------------------------------------
  -- Conjunction, as (Exp) and (Lin) need it

  ∧True : (X Y : Formula) (pos : Pos)
       -> evalAt X pos ≡ true -> evalAt Y pos ≡ true
       -> evalAt (X ∧ Y) pos ≡ true
  ∧True X Y pos ex ey =
    aux (evalAt X pos) (evalAt Y pos) ex ey
    where
      aux : (x y : Bool) -> x ≡ true -> y ≡ true
         -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
      aux true  true  ex' ey' = refl
      aux true  false ex' ()
      aux false y     ()  ey'

  ------------------------------------------------------------------------
  -- (K □)

  k□Sound : (A B : Formula) (pos : Pos)
         -> evalAt (□ (A ⇒ B)) pos ≡ true
         -> evalAt (□ A) pos ≡ true
         -> evalAt (□ B) pos ≡ true
  k□Sound A B pos e1 e2 =
    all-intro (evalAt B) (orbit loop pos)
      (λ {q} m ->
         ⇒ᵇ-mp (evalAt A q) (evalAt B q)
               (all-at (evalAt (A ⇒ B)) (orbit loop pos) m e1)
               (all-at (evalAt A) (orbit loop pos) m e2))

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
        ∧True A (○ A ∧ ○ □ A) pos
              (all-at (evalAt A) (orbit loop pos)
                        (iter∈orbit loop zero pos) eb)
                (∧True (○ A) (○ □ A) pos
                       (all-at (evalAt A) (orbit loop pos)
                                 (iter∈orbit loop (suc zero) pos) eb)
                         (all-intro (evalAt A)
                                    (orbit loop (nextPos loop pos))
                                    (λ {q} m ->
                                       all-at (evalAt A)
                                              (orbit loop pos)
                                              (nextOrbit⊆orbit loop pos q m) eb)))

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
        all-intro (evalAt A) (orbit loop pos)
                  (λ {q} m -> fromIter q (∈orbit-iter loop pos q m))
        where
          along : (t : Nat) -> evalAt A (posIter loop t pos) ≡ true
          along zero    = e2
          along (suc t) =
            subst (λ r -> evalAt A r ≡ true)
                  (sym (posIter-suc loop t pos))
                  (⇒ᵇ-mp (evalAt A (posIter loop t pos))
                            (evalAt A
                                    (nextPos loop (posIter loop t pos)))
                            (all-at (evalAt (A ⇒ ○ A))
                                    (orbit loop pos)
                                    (iter∈orbit loop t pos) e1)
                            (along t))

          fromIter : (q : Pos) -> (Σ[ t ∈ Nat ] posIter loop t pos ≡ q)
                  -> evalAt A q ≡ true
          fromIter q (t , et) =
            subst (λ r -> evalAt A r ≡ true) et (along t)

  ------------------------------------------------------------------------
  -- Soundness

  sound : {C : Formula} -> ⊢ C
       -> (pos : Pos) -> evalAt C pos ≡ true

  sound (p1 {A} {B}) pos =
    tautP1 (evalAt A pos) (evalAt B pos)

  sound (p2 {A} {B} {C}) pos =
    tautP2 (evalAt A pos) (evalAt B pos) (evalAt C pos)

  sound (p3 {A} {B}) pos =
    tautP3 (evalAt A pos) (evalAt B pos)

  sound (k□ {A} {B}) pos =
    ⇒ᵇ-intro (evalAt (□ (A ⇒ B)) pos)
              (evalAt (□ A) pos ⇒ᵇ evalAt (□ B) pos)
              (λ e1 -> ⇒ᵇ-intro (evalAt (□ A) pos)
                                 (evalAt (□ B) pos)
                                 (λ e2 -> k□Sound A B pos e1 e2))

  -- both sides are evalAt A (nextPos pos) ⇒ᵇ evalAt B (nextPos pos)
  sound (k○ {A} {B}) pos =
    ⇒ᵇ-refl (evalAt A (nextPos loop pos) ⇒ᵇ
             evalAt B (nextPos loop pos))

  sound (exp {A}) pos = expSound A pos

  sound (ind {A}) pos = indSound A pos

  -- ○ ¬ A and ¬ ○ A evaluate to the same Boolean, so both halves of
  -- the biconditional are z ⇒ᵇ z
  sound (lin {A}) pos =
    ∧True (○ ¬ A ⇒ ¬ ○ A) (¬ ○ A ⇒ ○ ¬ A) pos
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
    all-intro (evalAt A) (orbit loop pos)
              (λ {q} m -> sound d q)

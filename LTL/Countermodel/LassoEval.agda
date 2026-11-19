{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.LassoEval -- the Boolean evaluation of formulas on a lasso,
-- and its soundness: every derivable formula is true at every position.
--
-- The states have any type S, and read s n is the truth value of variable n
-- in s.  LTL.Countermodel.Eval takes S to be valuations; LTL.Semantics takes
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
-- successor's orbit (orbitIter).  (Ind) is the one with content: A propagates
-- along posIter t pos by induction on t, and every member of the orbit is
-- such a posIter (orbitOf-iter).

open import LTL.Syntax.Deriv

module LTL.Countermodel.LassoEval (S : Set) (read : S -> Nat -> Bool) where

open import LTL.Countermodel.Orbit S

------------------------------------------------------------------------
-- The Boolean evaluation at a position

evalAt : (c0 : S) (c1 : List S) -> Formula -> Pos -> Bool
evalAt c0 c1 (var n) pos = read (posState pos) n
evalAt c0 c1 (¬ A)   pos = ¬ᵇ evalAt c0 c1 A pos
evalAt c0 c1 (A ⇒ B) pos = evalAt c0 c1 A pos ⇒ᵇ evalAt c0 c1 B pos
evalAt c0 c1 (○ A)   pos = evalAt c0 c1 A (nextPos c0 c1 pos)
evalAt c0 c1 (□ A)   pos = all (evalAt c0 c1 A) (orbitOf c0 c1 pos)

------------------------------------------------------------------------
-- The two ways of using it

eval□-at : (c0 : S) (c1 : List S) (A : Formula) (pos q : Pos)
        -> evalAt c0 c1 (□ A) pos ≡ true -> q ∈ orbitOf c0 c1 pos
        -> evalAt c0 c1 A q ≡ true
eval□-at c0 c1 A pos q e m =
  all-at (evalAt c0 c1 A) (orbitOf c0 c1 pos) m e

eval□-intro : (c0 : S) (c1 : List S) (A : Formula) (pos : Pos)
           -> ((q : Pos) -> q ∈ orbitOf c0 c1 pos -> evalAt c0 c1 A q ≡ true)
           -> evalAt c0 c1 (□ A) pos ≡ true
eval□-intro c0 c1 A pos f =
  all-intro (evalAt c0 c1 A) (orbitOf c0 c1 pos) (λ {q} m -> f q m)

eval□-false : (c0 : S) (c1 : List S) (A : Formula) (pos q : Pos)
           -> q ∈ orbitOf c0 c1 pos -> evalAt c0 c1 A q ≡ false
           -> evalAt c0 c1 (□ A) pos ≡ false
eval□-false c0 c1 A pos q m e =
  all-atFalse (evalAt c0 c1 A) (orbitOf c0 c1 pos) m e

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

------------------------------------------------------------------------
-- Conjunction, as (Exp) and (Lin) need it

∧True : (c0 : S) (c1 : List S) (X Y : Formula) (pos : Pos)
     -> evalAt c0 c1 X pos ≡ true -> evalAt c0 c1 Y pos ≡ true
     -> evalAt c0 c1 (X ∧ Y) pos ≡ true
∧True c0 c1 X Y pos ex ey =
  aux (evalAt c0 c1 X pos) (evalAt c0 c1 Y pos) ex ey
  where
    aux : (x y : Bool) -> x ≡ true -> y ≡ true
       -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
    aux true  true  ex' ey' = refl
    aux true  false ex' ()
    aux false y     ()  ey'

------------------------------------------------------------------------
-- (K □)

k□Sound : (c0 : S) (c1 : List S) (A B : Formula) (pos : Pos)
       -> evalAt c0 c1 (□ (A ⇒ B)) pos ≡ true
       -> evalAt c0 c1 (□ A) pos ≡ true
       -> evalAt c0 c1 (□ B) pos ≡ true
k□Sound c0 c1 A B pos e1 e2 =
  all-intro (evalAt c0 c1 B) (orbitOf c0 c1 pos)
    (λ {q} m ->
       ⇒ᵇ-mp (evalAt c0 c1 A q) (evalAt c0 c1 B q)
             (all-at (evalAt c0 c1 (A ⇒ B)) (orbitOf c0 c1 pos) m e1)
             (all-at (evalAt c0 c1 A) (orbitOf c0 c1 pos) m e2))

------------------------------------------------------------------------
-- (Exp)

expSound : (c0 : S) (c1 : List S) (A : Formula) (pos : Pos)
        -> evalAt c0 c1 (□ A ⇒ A ∧ ○ A ∧ ○ □ A) pos ≡
           true
expSound c0 c1 A pos =
  ⇒ᵇ-intro (evalAt c0 c1 (□ A) pos)
            (evalAt c0 c1 (A ∧ ○ A ∧ ○ □ A) pos) body
  where
    body : evalAt c0 c1 (□ A) pos ≡ true
        -> evalAt c0 c1 (A ∧ ○ A ∧ ○ □ A) pos ≡ true
    body eb =
      ∧True c0 c1 A (○ A ∧ ○ □ A) pos
            (all-at (evalAt c0 c1 A) (orbitOf c0 c1 pos)
                      (orbitIter c0 c1 zero pos) eb)
              (∧True c0 c1 (○ A) (○ □ A) pos
                     (all-at (evalAt c0 c1 A) (orbitOf c0 c1 pos)
                               (orbitIter c0 c1 (suc zero) pos) eb)
                       (all-intro (evalAt c0 c1 A)
                                  (orbitOf c0 c1 (nextPos c0 c1 pos))
                                  (λ {q} m ->
                                     all-at (evalAt c0 c1 A)
                                            (orbitOf c0 c1 pos)
                                            (orbitSub c0 c1 pos q m) eb)))

------------------------------------------------------------------------
-- (Ind): A propagates along the run, since the hypothesis is available at
-- every stage and the orbit consists exactly of those stages.

indSound : (c0 : S) (c1 : List S) (A : Formula) (pos : Pos)
        -> evalAt c0 c1 (□ (A ⇒ ○ A) ⇒ A ⇒ □ A) pos ≡ true
indSound c0 c1 A pos =
  ⇒ᵇ-intro (evalAt c0 c1 (□ (A ⇒ ○ A)) pos)
           (evalAt c0 c1 A pos ⇒ᵇ evalAt c0 c1 (□ A) pos)
           (λ e1 -> ⇒ᵇ-intro (evalAt c0 c1 A pos)
                             (evalAt c0 c1 (□ A) pos) (body e1))
  where
    body : evalAt c0 c1 (□ (A ⇒ ○ A)) pos ≡ true
        -> evalAt c0 c1 A pos ≡ true
        -> evalAt c0 c1 (□ A) pos ≡ true
    body e1 e2 =
      all-intro (evalAt c0 c1 A) (orbitOf c0 c1 pos)
                (λ {q} m -> fromIter q (orbitOf-iter c0 c1 pos q m))
      where
        along : (t : Nat) -> evalAt c0 c1 A (posIter c0 c1 t pos) ≡ true
        along zero    = e2
        along (suc t) =
          subst (λ r -> evalAt c0 c1 A r ≡ true)
                (sym (posIter-suc c0 c1 t pos))
                (⇒ᵇ-mp (evalAt c0 c1 A (posIter c0 c1 t pos))
                          (evalAt c0 c1 A
                                  (nextPos c0 c1 (posIter c0 c1 t pos)))
                          (all-at (evalAt c0 c1 (A ⇒ ○ A))
                                  (orbitOf c0 c1 pos)
                                  (orbitIter c0 c1 t pos) e1)
                          (along t))

        fromIter : (q : Pos) -> (Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q)
                -> evalAt c0 c1 A q ≡ true
        fromIter q (t , et) =
          subst (λ r -> evalAt c0 c1 A r ≡ true) et (along t)

------------------------------------------------------------------------
-- Soundness

sound : (c0 : S) (c1 : List S) {C : Formula} -> ⊢ C
     -> (pos : Pos) -> evalAt c0 c1 C pos ≡ true

sound c0 c1 (p1 {A} {B}) pos =
  tautP1 (evalAt c0 c1 A pos) (evalAt c0 c1 B pos)

sound c0 c1 (p2 {A} {B} {C}) pos =
  tautP2 (evalAt c0 c1 A pos) (evalAt c0 c1 B pos) (evalAt c0 c1 C pos)

sound c0 c1 (p3 {A} {B}) pos =
  tautP3 (evalAt c0 c1 A pos) (evalAt c0 c1 B pos)

sound c0 c1 (k□ {A} {B}) pos =
  ⇒ᵇ-intro (evalAt c0 c1 (□ (A ⇒ B)) pos)
            (evalAt c0 c1 (□ A) pos ⇒ᵇ evalAt c0 c1 (□ B) pos)
            (λ e1 -> ⇒ᵇ-intro (evalAt c0 c1 (□ A) pos)
                               (evalAt c0 c1 (□ B) pos)
                               (λ e2 -> k□Sound c0 c1 A B pos e1 e2))

-- both sides are evalAt A (nextPos pos) ⇒ᵇ evalAt B (nextPos pos)
sound c0 c1 (k○ {A} {B}) pos =
  ⇒ᵇ-refl (evalAt c0 c1 A (nextPos c0 c1 pos) ⇒ᵇ
           evalAt c0 c1 B (nextPos c0 c1 pos))

sound c0 c1 (exp {A}) pos = expSound c0 c1 A pos

sound c0 c1 (ind {A}) pos = indSound c0 c1 A pos

-- ○ ¬ A and ¬ ○ A evaluate to the same Boolean, so both halves of
-- the biconditional are z ⇒ᵇ z
sound c0 c1 (lin {A}) pos =
  ∧True c0 c1 (○ ¬ A ⇒ ¬ ○ A) (¬ ○ A ⇒ ○ ¬ A) pos
        (⇒ᵇ-refl (¬ᵇ evalAt c0 c1 A (nextPos c0 c1 pos)))
        (⇒ᵇ-refl (¬ᵇ evalAt c0 c1 A (nextPos c0 c1 pos)))

-- (PC): evalAt is DEFINED by ¬ᵇ at ¬ and ⇒ᵇ at ⇒, so the two hypotheses
-- of tautSound are refl.
sound c0 c1 (pc {C} e) pos =
  tautSound (λ X -> evalAt c0 c1 X pos) C
            (λ X m -> refl) (λ X Y m -> refl) e

sound c0 c1 (mp {A} {B} d e) pos =
  ⇒ᵇ-mp (evalAt c0 c1 A pos) (evalAt c0 c1 B pos)
           (sound c0 c1 d pos)
           (sound c0 c1 e pos)

sound c0 c1 (gen {A} d) pos =
  all-intro (evalAt c0 c1 A) (orbitOf c0 c1 pos)
            (λ {q} m -> sound c0 c1 d q)

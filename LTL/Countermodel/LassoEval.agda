{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.LassoEval -- G25 and G26 of FORMALISATION-PLAN.md, for any lasso.
--
--   "The lasso is a finite structure with a total successor function, so Always
--    and Eventually evaluate on it by conjunction and disjunction over the
--    finite forward orbit of a state; write [[.]]_s for that Boolean
--    evaluation.  One checks by induction on derivations that |- C implies
--    [[C]]_s = 1 at every state of every lasso."            -- m4.tex section 5
--
-- The states of the lasso are of any type S, and read s n is the truth value
-- of the variable n in the state s.  LTL.Countermodel.Eval takes S to be valuations, read
-- against sub P, for the runs the elimination builds; LTL.Semantics takes it to
-- be LTL.Trusted's Instant, read as itself, for an arbitrary lasso.
--
-- The evaluation has five clauses, one per constructor of Formula.  □ A is the
-- conjunction of A over the forward orbit (LTL.Countermodel.Orbit); since orbitOf returns a
-- list, this is all, and the recursion is structural in the formula.
-- Eventually needs no clause of its own: ◇ A is ¬ □ ¬ A, so it comes out as
-- the disjunction the note describes.  The evaluation is by POSITION: ○ is one
-- step of nextPos and □ a conjunction over orbitOf, both functions of the
-- position alone.
--
-- Soundness has ten constructors.  Six are Boolean tautologies of at most three
-- variables, written out by cases; (K ○) and (Lin) reduce to  z ⇒ᵇ z  because
-- evalAt commutes with ○ definitionally, both sides of (Lin) being
-- ¬ᵇ evalAt A (nextPos pos) on the nose.  That leaves four.
--
--   (K □)  is all pointwise: the SAME orbit on both sides, so it is
--            all-at then ⇒ᵇ-mp then all-intro.
--
--   (Exp)    needs the orbit of pos to contain pos, its successor, and the
--            whole orbit of its successor.  All three are orbitIter, since
--            posIter 0, posIter 1 and posIter (suc t) all land in it.
--
--   (Ind)    is the only one with content.  Under  □ (A ⇒ ○ A)  and A at pos,
--            A holds at posIter t pos by induction on t -- the hypothesis is
--            available at posIter t pos because orbitIter puts it in the orbit
--            -- and every member of the orbit is a posIter t pos by
--            orbitOf-iter.  Twenty lines, no arithmetic.
--
--   (gen)    is the induction hypothesis at every position of the orbit.
--
-- The evaluation is total on all formulas and all positions, not only on
-- subformulas of some P or on the positions a run visits, which is what lets
-- soundness be stated for an arbitrary derivable C at an arbitrary position.

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
-- The two ways of using it, and the shapes G26 and G27 will want

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
-- (Ind).
--
-- The forward induction the note leaves to "one checks": A propagates along
-- the run because the hypothesis is available at every stage of it, and the
-- orbit consists exactly of those stages.

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

-- (PC).  evalAt is DEFINED by ¬ᵇ at ¬ and by ⇒ᵇ at ⇒, so the two
-- compositionality hypotheses of tautSound are refl and the case is one line.
-- This is the whole of Ben-Ari's Axiom 0, and it is where the substitution
-- lemma that Remark 6.4 feared would have gone.
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

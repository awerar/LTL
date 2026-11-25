{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Exhaustible -- pools that picking exhausts: inductively finite
-- sets, after the bar inductive type of Coquand and Siles, "A Decision
-- Procedure for Regular Expression Equivalence in Type Theory" (CPP 2011).
--
--   Exhaustible Apart Pool   holds when, starting from Pool and repeatedly
--                            picking an x in Pool and passing to
--                            Pool ∩ Apart x , one always stops.
--
-- Apart x is what may still be picked after x.  In every use it is "differs
-- from x" (≢ᵛ, ≢ᵇ, or prodApart: differs in some component), so Pool ∩ Apart x
-- is Pool without x, and exhaustibility says one cannot pick distinct
-- elements of Pool forever.  Every search in the development recurses on an
-- Exhaustible proof, including closure (LTL.1-Lib.Graph), whose accumulator
-- grows and so has no decreasing measure.  The constructor everyPick answers
-- every possible pick: its one field next says that for every x in the pool
-- (x∈), the pool left after picking x is exhaustible.  An empty pool is
-- everyPick of an absurd function.  It is an inductive record with pattern
-- matching, so proofs match on everyPick next and recurse on next x x∈.
--
-- Subsets are Boolean predicates, which keeps Exhaustible in Set.  The first
-- section names their algebra (∩, ∪, ⊆ᵖ, preimage ⁻¹) and the inclusions the
-- proofs use, so the Boolean bookkeeping stays there and the proofs below
-- read as set reasoning.  The rest is generic: Exhaustible and its closure
-- under subsets, union, product and preimage.  Finite (LTL.1-Lib.DecEq) is
-- Exhaustible with inequality as the apartness; the finite pools themselves
-- are boolFinite (LTL.1-Lib.DecEq), listFinite (LTL.1-Lib.Nodes, from a list
-- in hand) and guardedVecFinite (LTL.5-States.VecFinite, the vectors of a
-- given length).

module LTL.1-Lib.Exhaustible where

open import LTL.1-Lib.Prelude

------------------------------------------------------------------------
-- Subsets and apartness, as Boolean tests

Subset : Set -> Set
Subset A = A -> Bool

-- A Boolean relation read as apartness: Apart x y says that y may still be
-- picked after x.

Apartness : Set -> Set
Apartness A = A -> A -> Bool

-- The implicit arguments the signatures below leave out.

private variable
  A B        : Set
  E F G      : Subset A
  Pool Pool' : Subset A
  Apart      : Apartness A

infixr 7 _∩_
infixr 6 _∪_
infix  8 _⁻¹_
infix  4 _⊆ᵖ_

_∩_ : Subset A -> Subset A -> Subset A
(E ∩ F) x = E x ∧ᵇ F x

_∪_ : Subset A -> Subset A -> Subset A
(E ∪ F) x = E x ∨ᵇ F x

-- The preimage of E under f.
_⁻¹_ : (B -> A) -> Subset A -> Subset B
(f ⁻¹ E) y = E (f y)

_⊆ᵖ_ : Subset A -> Subset A -> Set
E ⊆ᵖ F = (x : _) -> E x ≡ true -> F x ≡ true

⊆ᵖ-refl : E ⊆ᵖ E
⊆ᵖ-refl x e = e

⊆ᵖ-trans : E ⊆ᵖ F -> F ⊆ᵖ G -> E ⊆ᵖ G
⊆ᵖ-trans s t x e = t x (s x e)

∩-intro : E ⊆ᵖ F -> E ⊆ᵖ G -> E ⊆ᵖ F ∩ G
∩-intro {F = F} {G = G} s t x e = ∧ᵇ-intro (F x) (G x) (s x e) (t x e)

∩-fst : E ∩ F ⊆ᵖ E
∩-fst {E = E} {F = F} x e = ∧ᵇ-trueˡ (E x) (F x) e

∩-monoˡ : E ⊆ᵖ F -> E ∩ G ⊆ᵖ F ∩ G
∩-monoˡ {E = E} {F = F} {G = G} subset x e =
  ∧ᵇ-intro (F x) (G x) (subset x (∧ᵇ-trueˡ (E x) (G x) e))
           (∧ᵇ-trueʳ (E x) (G x) e)

-- The sets are explicit: Agda cannot read them back off the Boolean
-- operators they unfold to.

∪-∩-distrib : (G H K : Subset A) -> (G ∪ H) ∩ K ⊆ᵖ G ∩ K ∪ H ∩ K
∪-∩-distrib G H K x = ∧ᵇ∨ᵇ-distribʳ (G x) (H x) (K x)

-- Distribution, forgetting K on the left
∪-∩-weaken : (G H K : Subset A) -> (G ∪ H) ∩ K ⊆ᵖ G ∪ H ∩ K
∪-∩-weaken G H K x = ∧ᵇ∨ᵇ-weaken (G x) (H x) (K x)

------------------------------------------------------------------------
-- Exhaustible, and a subset of an exhaustible pool is exhaustible

record Exhaustible {A : Set} (Apart : Apartness A) (Pool : Subset A)
                   : Set where
  inductive
  pattern
  constructor everyPick
  field
    next : (x : A) -> Pool x ≡ true -> Exhaustible Apart (Pool ∩ Apart x)

exhaustibleSubset : Pool ⊆ᵖ Pool'
                 -> Exhaustible Apart Pool' -> Exhaustible Apart Pool
exhaustibleSubset subset (everyPick next) =
  everyPick (λ x x∈ ->
    exhaustibleSubset (∩-monoˡ subset) (next x (subset x x∈)))

------------------------------------------------------------------------
-- Union, by lexicographic induction: on Pool₁'s proof when the picked x is
-- in Pool₁, and on Pool₂'s, with Pool₁'s unchanged, when x is in Pool₂.
-- exhaustibleSubset replaces funext, since the two sides are only pointwise
-- equal predicates.

exhaustibleUnion : {A : Set} {Apart : Apartness A} {Pool₁ Pool₂ : Subset A}
                -> Exhaustible Apart Pool₁ -> Exhaustible Apart Pool₂
                -> Exhaustible Apart (Pool₁ ∪ Pool₂)
exhaustibleUnion {A} {Apart} {Pool₁} (everyPick next₁) ex₂ = inner ex₂
  where
    inner : {Pool₂ : Subset A}
         -> Exhaustible Apart Pool₂ -> Exhaustible Apart (Pool₁ ∪ Pool₂)
    inner {Pool₂} ex₂@(everyPick next₂) = everyPick pick
      where
        pick : (x : A) -> (Pool₁ ∪ Pool₂) x ≡ true
            -> Exhaustible Apart ((Pool₁ ∪ Pool₂) ∩ Apart x)
        pick x x∈ = [ from₁ , from₂ ] (∨ᵇ-true (Pool₁ x) (Pool₂ x) x∈)
          where
            from₁ : Pool₁ x ≡ true
                 -> Exhaustible Apart ((Pool₁ ∪ Pool₂) ∩ Apart x)
            from₁ x∈₁ =
              exhaustibleSubset (∪-∩-distrib Pool₁ Pool₂ (Apart x))
                (exhaustibleUnion (next₁ x x∈₁) (exhaustibleSubset ∩-fst ex₂))

            from₂ : Pool₂ x ≡ true
                 -> Exhaustible Apart ((Pool₁ ∪ Pool₂) ∩ Apart x)
            from₂ x∈₂ =
              exhaustibleSubset (∪-∩-weaken Pool₁ Pool₂ (Apart x))
                (inner (next₂ x x∈₂))

------------------------------------------------------------------------
-- Product: the load-bearing closure lemma, by the same lexicographic
-- induction as union.  Picking (x , y) leaves the pairs that differ from it
-- in the first component or in the second (prodSplit).

prodPool : Subset A -> Subset B -> Subset (A × B)
prodPool Pool₁ Pool₂ (x , y) = Pool₁ x ∧ᵇ Pool₂ y

prodApart : Apartness A -> Apartness B -> Apartness (A × B)
prodApart Apart₁ Apart₂ (x , y) (u , v) = Apart₁ x u ∨ᵇ Apart₂ y v

exhaustibleProd : {A B : Set} {Apart₁ : Apartness A} {Apart₂ : Apartness B}
               -> {Pool₁ : Subset A} {Pool₂ : Subset B}
               -> Exhaustible Apart₁ Pool₁ -> Exhaustible Apart₂ Pool₂
               -> Exhaustible (prodApart Apart₁ Apart₂) (prodPool Pool₁ Pool₂)
exhaustibleProd {A} {B} {Apart₁} {Apart₂} {Pool₁} (everyPick next₁) ex₂ =
  inner ex₂
  where
    prodSplit : (Pool₂ : Subset B) (x : A) (y : B)
             -> prodPool Pool₁ Pool₂ ∩ prodApart Apart₁ Apart₂ (x , y)
                ⊆ᵖ prodPool (Pool₁ ∩ Apart₁ x) Pool₂
                   ∪ prodPool Pool₁ (Pool₂ ∩ Apart₂ y)
    prodSplit Pool₂ x y (u , v) e =
      split (Pool₁ u) (Pool₂ v) (Apart₁ x u) (Apart₂ y v) e
      where
        split : (e f r s : Bool)
             -> (e ∧ᵇ f) ∧ᵇ (r ∨ᵇ s) ≡ true
             -> (e ∧ᵇ r) ∧ᵇ f ∨ᵇ e ∧ᵇ f ∧ᵇ s ≡ true
        split true  true  true  s h = refl
        split true  true  false s h = h
        split true  false r     s ()
        split false f     r     s ()

    inner : {Pool₂ : Subset B} -> Exhaustible Apart₂ Pool₂
         -> Exhaustible (prodApart Apart₁ Apart₂) (prodPool Pool₁ Pool₂)
    inner {Pool₂} ex₂@(everyPick next₂) = everyPick pick
      where
        pick : (p : A × B) -> prodPool Pool₁ Pool₂ p ≡ true
            -> Exhaustible (prodApart Apart₁ Apart₂)
                           (prodPool Pool₁ Pool₂ ∩ prodApart Apart₁ Apart₂ p)
        pick (x , y) xy∈ =
          exhaustibleSubset (prodSplit Pool₂ x y)
            (exhaustibleUnion
               (exhaustibleProd (next₁ x (∧ᵇ-trueˡ (Pool₁ x) (Pool₂ y) xy∈))
                                ex₂)
               (inner (next₂ y (∧ᵇ-trueʳ (Pool₁ x) (Pool₂ y) xy∈))))

------------------------------------------------------------------------
-- The preimage along a map f that, on a domain Dom, keeps apart what is
-- apart: Apart₂-related members of Dom go to Apart₁-related elements.

exhaustiblePreimage : {A B : Set} {Apart₁ : Apartness A} {Apart₂ : Apartness B}
                   -> (f : B -> A) (Dom : Subset B)
                   -> ((y z : B) -> Dom y ≡ true -> Dom z ≡ true
                         -> Apart₂ y z ≡ true -> Apart₁ (f y) (f z) ≡ true)
                   -> {Pool : Subset A} -> Exhaustible Apart₁ Pool
                   -> Exhaustible Apart₂ (Dom ∩ f ⁻¹ Pool)
exhaustiblePreimage {A} {B} {Apart₁} {Apart₂} f Dom keepsApart {Pool}
                    (everyPick next) = everyPick pick
  where
    pick : (y : B) -> (Dom ∩ f ⁻¹ Pool) y ≡ true
        -> Exhaustible Apart₂ ((Dom ∩ f ⁻¹ Pool) ∩ Apart₂ y)
    pick y y∈ =
      exhaustibleSubset keep
        (exhaustiblePreimage f Dom keepsApart
           (next (f y) (∧ᵇ-trueʳ (Dom y) (Pool (f y)) y∈)))
      where
        keep : (Dom ∩ f ⁻¹ Pool) ∩ Apart₂ y ⊆ᵖ Dom ∩ f ⁻¹ (Pool ∩ Apart₁ (f y))
        keep z z∈ with ∧ᵇ-split (Dom z ∧ᵇ Pool (f z)) (Apart₂ y z) z∈
        ... | inBoth , apart with ∧ᵇ-split (Dom z) (Pool (f z)) inBoth
        ...   | inDom , fz∈ =
          ∧ᵇ-intro (Dom z) (Pool (f z) ∧ᵇ Apart₁ (f y) (f z)) inDom
                   (∧ᵇ-intro (Pool (f z)) (Apart₁ (f y) (f z)) fz∈
                             (keepsApart y z (∧ᵇ-trueˡ (Dom y) (Pool (f y)) y∈)
                                         inDom apart))

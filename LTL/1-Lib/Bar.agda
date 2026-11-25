{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Bar -- inductively finite sets, after Coquand and Siles, "A Decision
-- Procedure for Regular Expression Equivalence in Type Theory" (CPP 2011).
--
--   Bar Apart Pool   holds when, starting from Pool and repeatedly picking an
--                    x in Pool and passing to  Pool ∩ Apart x , one always
--                    stops.
--
-- Apart x is what may still be picked after x.  In every use it is "differs
-- from x" (≢ᵛ, ≢ᵇ, or prodApart: differs in some component), so Pool ∩ Apart x
-- is Pool without x, and a Bar says one cannot pick distinct elements of Pool
-- forever.  Every search in the development recurses on a Bar, including
-- closure (LTL.1-Lib.Graph), whose accumulator grows and so has no decreasing
-- measure.  In the proofs, next is the function picks carries (next x x∈ is
-- the Bar left after picking x), and x∈ says that x is in the pool.
--
-- Subsets are Boolean predicates, which keeps Bar in Set.  The first section
-- names their algebra (∩, ∪, ⊆ᵖ, preimage ⁻¹) and the inclusions the proofs
-- use, so the Boolean bookkeeping stays there and the Bar proofs read as set
-- reasoning.  The rest is generic: Bar, its closure under subsets, union,
-- product and preimage, and the Bar of Bool (boolFinite).  The other Bars are
-- listFinite (LTL.1-Lib.Nodes, from a list in hand) and guardedVecFinite
-- (LTL.5-States.VecBar, the vectors of a given length, built from boolFinite).

module LTL.1-Lib.Bar where

open import LTL.1-Lib.Prelude

------------------------------------------------------------------------
-- Subsets as Boolean predicates

Subset : Set -> Set
Subset A = A -> Bool

-- The implicit arguments the signatures below leave out.

private variable
  A B        : Set
  E F G      : Subset A
  Pool Pool' : Subset A
  Apart      : A -> A -> Bool

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
  ∧ᵇ-intro (F x) (G x) (subset x (∧ᵇ-trueˡ (E x) (G x) e)) (∧ᵇ-trueʳ (E x) (G x) e)

-- The sets are explicit: Agda cannot read them back off the Boolean
-- operators they unfold to.

∪-∩-distrib : (G H K : Subset A) -> (G ∪ H) ∩ K ⊆ᵖ G ∩ K ∪ H ∩ K
∪-∩-distrib G H K x = ∧ᵇ∨ᵇ-distribʳ (G x) (H x) (K x)

-- Distribution, forgetting K on the left
∪-∩-weaken : (G H K : Subset A) -> (G ∪ H) ∩ K ⊆ᵖ G ∪ H ∩ K
∪-∩-weaken G H K x = ∧ᵇ∨ᵇ-weaken (G x) (H x) (K x)

------------------------------------------------------------------------
-- Bar, and a subset of a Bar is a Bar

data Bar {A : Set} (Apart : A -> A -> Bool) : Subset A -> Set where
  picks : {Pool : Subset A}
       -> ((x : A) -> Pool x ≡ true -> Bar Apart (Pool ∩ Apart x))
       -> Bar Apart Pool

barSubset : Pool ⊆ᵖ Pool' -> Bar Apart Pool' -> Bar Apart Pool
barSubset subset (picks next) =
  picks (λ x x∈ -> barSubset (∩-monoˡ subset) (next x (subset x x∈)))

------------------------------------------------------------------------
-- Union, by lexicographic induction: on the Bar for Pool₁ when the picked x
-- is in Pool₁, and on the Bar for Pool₂, with Pool₁'s unchanged, when x is in
-- Pool₂.  barSubset replaces funext, since the two sides are only pointwise
-- equal predicates.

barUnion : {A : Set} {Apart : A -> A -> Bool} {Pool₁ Pool₂ : Subset A}
        -> Bar Apart Pool₁ -> Bar Apart Pool₂ -> Bar Apart (Pool₁ ∪ Pool₂)
barUnion {A} {Apart} {Pool₁} (picks next₁) bar₂ = inner bar₂
  where
    inner : {Pool₂ : Subset A} -> Bar Apart Pool₂ -> Bar Apart (Pool₁ ∪ Pool₂)
    inner {Pool₂} bar₂@(picks next₂) = picks pick
      where
        pick : (x : A) -> (Pool₁ ∪ Pool₂) x ≡ true
            -> Bar Apart ((Pool₁ ∪ Pool₂) ∩ Apart x)
        pick x x∈ = [ from₁ , from₂ ] (∨ᵇ-true (Pool₁ x) (Pool₂ x) x∈)
          where
            from₁ : Pool₁ x ≡ true -> Bar Apart ((Pool₁ ∪ Pool₂) ∩ Apart x)
            from₁ x∈₁ = barSubset (∪-∩-distrib Pool₁ Pool₂ (Apart x))
                                  (barUnion (next₁ x x∈₁) (barSubset ∩-fst bar₂))

            from₂ : Pool₂ x ≡ true -> Bar Apart ((Pool₁ ∪ Pool₂) ∩ Apart x)
            from₂ x∈₂ = barSubset (∪-∩-weaken Pool₁ Pool₂ (Apart x))
                                  (inner (next₂ x x∈₂))

------------------------------------------------------------------------
-- Product: the load-bearing closure lemma, by the same lexicographic
-- induction as union.  Picking (x , y) leaves the pairs that differ from it
-- in the first component or in the second (prodSplit).

prodPool : Subset A -> Subset B -> Subset (A × B)
prodPool Pool₁ Pool₂ (x , y) = Pool₁ x ∧ᵇ Pool₂ y

prodApart : (A -> A -> Bool) -> (B -> B -> Bool)
         -> A × B -> A × B -> Bool
prodApart Apart₁ Apart₂ (x , y) (u , v) = Apart₁ x u ∨ᵇ Apart₂ y v

barProd : {A B : Set} {Apart₁ : A -> A -> Bool} {Apart₂ : B -> B -> Bool}
       -> {Pool₁ : Subset A} {Pool₂ : Subset B}
       -> Bar Apart₁ Pool₁ -> Bar Apart₂ Pool₂
       -> Bar (prodApart Apart₁ Apart₂) (prodPool Pool₁ Pool₂)
barProd {A} {B} {Apart₁} {Apart₂} {Pool₁} (picks next₁) bar₂ = inner bar₂
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

    inner : {Pool₂ : Subset B} -> Bar Apart₂ Pool₂
         -> Bar (prodApart Apart₁ Apart₂) (prodPool Pool₁ Pool₂)
    inner {Pool₂} bar₂@(picks next₂) = picks pick
      where
        pick : (p : A × B) -> prodPool Pool₁ Pool₂ p ≡ true
            -> Bar (prodApart Apart₁ Apart₂)
                   (prodPool Pool₁ Pool₂ ∩ prodApart Apart₁ Apart₂ p)
        pick (x , y) xy∈ =
          barSubset (prodSplit Pool₂ x y)
            (barUnion (barProd (next₁ x (∧ᵇ-trueˡ (Pool₁ x) (Pool₂ y) xy∈)) bar₂)
                      (inner (next₂ y (∧ᵇ-trueʳ (Pool₁ x) (Pool₂ y) xy∈))))

------------------------------------------------------------------------
-- The preimage along a map f that, on a domain Dom, keeps apart what is
-- apart: Apart₂-related members of Dom go to Apart₁-related elements.

barPreimage : {A B : Set} {Apart₁ : A -> A -> Bool} {Apart₂ : B -> B -> Bool}
           -> (f : B -> A) (Dom : Subset B)
           -> ((y z : B) -> Dom y ≡ true -> Dom z ≡ true -> Apart₂ y z ≡ true
                 -> Apart₁ (f y) (f z) ≡ true)
           -> {Pool : Subset A} -> Bar Apart₁ Pool
           -> Bar Apart₂ (Dom ∩ f ⁻¹ Pool)
barPreimage {A} {B} {Apart₁} {Apart₂} f Dom keepsApart {Pool} (picks next) =
  picks pick
  where
    pick : (y : B) -> (Dom ∩ f ⁻¹ Pool) y ≡ true
        -> Bar Apart₂ ((Dom ∩ f ⁻¹ Pool) ∩ Apart₂ y)
    pick y y∈ =
      barSubset keep
        (barPreimage f Dom keepsApart
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

------------------------------------------------------------------------
-- Bool is inductively finite

noThreeDistinct : (x y z : Bool) -> x ≢ᵇ y ≡ true -> x ≢ᵇ z ≡ true
               -> y ≢ᵇ z ≡ true -> Empty
noThreeDistinct true  true  z     () e2 e3
noThreeDistinct true  false true  e1 () e3
noThreeDistinct true  false false e1 e2 ()
noThreeDistinct false false z     () e2 e3
noThreeDistinct false true  false e1 () e3
noThreeDistinct false true  true  e1 e2 ()

boolFinite : Bar _≢ᵇ_ (λ b -> true)
boolFinite =
  picks (λ x x∈ ->
  picks (λ y y∈ ->
  picks (λ z z∈ ->
    emptyElim (noThreeDistinct x y z y∈
                 (∧ᵇ-trueˡ (x ≢ᵇ z) (y ≢ᵇ z) z∈)
                 (∧ᵇ-trueʳ (x ≢ᵇ z) (y ≢ᵇ z) z∈)))))

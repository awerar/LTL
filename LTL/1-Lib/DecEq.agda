{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.DecEq -- a type with a sound, reflexive Boolean equality test,
-- lists as sets decided by it, and finiteness.
--
-- DecEq A bundles the test with its two lemmas, so the graph layer takes one
-- argument for it; boolEq is the instance at Bool, LTL.5-States.Reach builds
-- the one at Val, and LTL.9-Tests.GraphExamples one at Nat.  Membership eq
-- opens the record and adds membership ∈ᵛ, inequality ≢ᵛ, list difference
-- ∖ and ∖ᵛ, and list intersection ∩ˡ.  It is a module rather than
-- definitions inside the record, so each lemma stays a definition of its own.
-- Finite eq Pool is exhaustibility (LTL.1-Lib.Exhaustible) with ≢ᵛ as the
-- apartness; LTL.1-Lib.Nodes fixes eq.  The superscript ᵛ reads "vertex", the
-- use every instance but boolEq has.

module LTL.1-Lib.DecEq where

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.Exhaustible using (Exhaustible; everyPick; Subset)

record DecEq (A : Set) : Set where
  infix 4.5 _≡ᵛ_
  field
    _≡ᵛ_     : A -> A -> Bool
    ≡ᵛ-sound : (v w : A) -> v ≡ᵛ w ≡ true -> v ≡ w
    ≡ᵛ-refl  : (v : A) -> v ≡ᵛ v ≡ true

------------------------------------------------------------------------
-- Lists of elements as sets

module Membership {A : Set} (eq : DecEq A) where

  open DecEq eq public

  infix 4.5 _∈ᵛ_ _≢ᵛ_

  _∈ᵛ_ : A -> List A -> Bool
  v ∈ᵛ us = any (v ≡ᵛ_) us

  _≢ᵛ_ : A -> A -> Bool
  x ≢ᵛ y = ¬ᵇ (x ≡ᵛ y)

  ≢ᵛ-self : (x : A) -> x ≢ᵛ x ≡ false
  ≢ᵛ-self x = cong ¬ᵇ_ (≡ᵛ-refl x)

  ∈ᵛ-sound : (us : List A) -> ∀[ v ∈ᵖ (_∈ᵛ us) ] v ∈ us
  ∈ᵛ-sound us v e with any-true (v ≡ᵛ_) us e
  ... | u , m , e1 = subst (λ z -> z ∈ us) (sym (≡ᵛ-sound v u e1)) m

  ∈ᵛ-complete : (us : List A) -> ∀[ v ∈ us ] v ∈ᵛ us ≡ true
  ∈ᵛ-complete us v m = any-intro (v ≡ᵛ_) us m (≡ᵛ-refl v)

  ∈ᵛ-false : (us : List A) (v : A) -> v ∈ᵛ us ≡ false -> v ∈ us -> Empty
  ∈ᵛ-false us v e m = true≢false (trans (sym (∈ᵛ-complete us v m)) e)

  ∉ᵛ-intro : (us : List A) (v : A) -> (v ∈ us -> Empty) -> v ∈ᵛ us ≡ false
  ∉ᵛ-intro us v no = refuteTrue (v ∈ᵛ us) λ e -> no (∈ᵛ-sound us v e)

  null-∈ᵛ : (ws : List A) (z : A) -> null ws ≡ true -> z ∈ᵛ ws ≡ false
  null-∈ᵛ []       z e = refl
  null-∈ᵛ (w ∷ ws) z ()

  -- A test that holds at z and fails at x separates them.
  separate : (p : A -> Bool) {x z : A} -> x ∉ᵖ p -> z ∈ᵖ p -> x ≢ᵛ z ≡ true
  separate p {x} {z} q e = cong ¬ᵇ_ (refuteTrue (x ≡ᵛ z) λ eb ->
    true≢false (trans (sym (subst (λ u -> p u ≡ true) (sym (≡ᵛ-sound x z eb)) e)) q))

  -- List difference.  ws ∖ C is what is left of ws once C is taken out, and
  -- ws ∖ᵛ x is the case C = x ∷ [], so that removing a vertex and removing a
  -- block are one operation with one set of lemmas.  The lemmas take both lists
  -- explicitly, as filter's do, since Agda cannot read them back off the filter.

  infixl 6 _∖ᵛ_ _∖_

  _∖_ : List A -> List A -> List A
  ws ∖ C = filter (λ z -> ¬ᵇ (z ∈ᵛ C)) ws

  _∖ᵛ_ : List A -> A -> List A
  ws ∖ᵛ x = ws ∖ (x ∷ [])

  ∖-⊆ : (ws C : List A) -> ws ∖ C ⊆ ws
  ∖-⊆ ws C z m = ∈-filter⁻ (λ y -> ¬ᵇ (y ∈ᵛ C)) ws m

  ∈-∖⁺ : {ws : List A} {z : A} (C : List A)
      -> z ∈ ws -> z ∈ᵛ C ≡ false -> z ∈ ws ∖ C
  ∈-∖⁺ {ws} C m e = ∈-filter⁺ (λ y -> ¬ᵇ (y ∈ᵛ C)) ws m (cong ¬ᵇ_ e)

  ∈-∖⁻ : (ws C : List A) -> ∀ⁱ[ z ∈ ws ∖ C ] z ∈ᵛ C ≡ false
  ∈-∖⁻ ws C {z} m = ¬ᵇ-true (z ∈ᵛ C) (filter-prop (λ y -> ¬ᵇ (y ∈ᵛ C)) ws z m)

  -- A part of ws that misses C stays in ws ∖ C: how a cycle survives a
  -- removal step.

  ⊆-∖ : {zs ws : List A} (C : List A)
      -> zs ⊆ ws -> (∀[ z ∈ zs ] (z ∈ C -> Empty)) -> zs ⊆ ws ∖ C
  ⊆-∖ C subset out z mz = ∈-∖⁺ C (subset z mz) (∉ᵛ-intro C z (out z mz))

  ∖-antitone : (ws : List A) {C D : List A} -> C ⊆ D -> ws ∖ D ⊆ ws ∖ C
  ∖-antitone ws {C} {D} s z m =
    ∈-∖⁺ C (∖-⊆ ws D z m)
         (∉ᵛ-intro C z (λ mc -> ∈ᵛ-false D z (∈-∖⁻ ws D m) (s z mc)))

  -- List intersection.  C ∩ˡ D keeps the members of C that are in D; the
  -- superscript tells it from ∩, the intersection of predicates.

  infixl 7 _∩ˡ_

  _∩ˡ_ : List A -> List A -> List A
  C ∩ˡ D = filter (_∈ᵛ D) C

  ∩ˡ-fst : (C D : List A) -> C ∩ˡ D ⊆ C
  ∩ˡ-fst C D z m = ∈-filter⁻ (_∈ᵛ D) C m

  ∩ˡ-snd : (C D : List A) -> C ∩ˡ D ⊆ D
  ∩ˡ-snd C D z m = ∈ᵛ-sound D z (filter-prop (_∈ᵛ D) C z m)

  ∈-∩ˡ⁺ : {C : List A} {z : A} (D : List A)
       -> z ∈ C -> z ∈ D -> z ∈ C ∩ˡ D
  ∈-∩ˡ⁺ {C} {z} D mc md = ∈-filter⁺ (_∈ᵛ D) C mc (∈ᵛ-complete D z md)

------------------------------------------------------------------------
-- Inductive finiteness

-- Finite eq Pool: Pool is inductively finite, so a search that keeps picking
-- elements of Pool that differ (by eq) from those picked before stops.

Finite : {A : Set} -> DecEq A -> Subset A -> Set
Finite eq Pool = Exhaustible (Membership._≢ᵛ_ eq) Pool

------------------------------------------------------------------------
-- Bool, compared by ⇔ᵇ, so that its ≢ᵛ is ≢ᵇ, is inductively finite

boolEq : DecEq Bool
boolEq = record { _≡ᵛ_ = _⇔ᵇ_ ; ≡ᵛ-sound = ⇔ᵇ-sound ; ≡ᵛ-refl = ⇔ᵇ-refl }

noThreeDistinct : (x y z : Bool) -> x ≢ᵇ y ≡ true -> x ≢ᵇ z ≡ true
               -> y ≢ᵇ z ≡ true -> Empty
noThreeDistinct true  true  z     () e2 e3
noThreeDistinct true  false true  e1 () e3
noThreeDistinct true  false false e1 e2 ()
noThreeDistinct false false z     () e2 e3
noThreeDistinct false true  false e1 () e3
noThreeDistinct false true  true  e1 e2 ()

boolFinite : Finite boolEq (λ b -> true)
boolFinite =
  everyPick (λ x x∈ ->
  everyPick (λ y y∈ ->
  everyPick (λ z z∈ ->
    emptyElim (noThreeDistinct x y z y∈
                 (∧ᵇ-trueˡ (x ≢ᵇ z) (y ≢ᵇ z) z∈)
                 (∧ᵇ-trueʳ (x ≢ᵇ z) (y ≢ᵇ z) z∈)))))

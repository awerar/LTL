{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.DecEq -- a type with a sound, reflexive Boolean equality test, and
-- list membership and finiteness decided by it.
--
-- DecEq A bundles the test with its two lemmas, so the graph layer takes one
-- argument for it; boolEq is the instance at Bool, LTL.5-States.Reach builds
-- the one at Val, and LTL.9-Tests.GraphExamples one at Nat.  Membership eq
-- opens the record and adds ∈ᵛ and ≢ᵛ.  It is a module rather than
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

  ∈ᵛ-sound : (v : A) (us : List A) -> v ∈ᵛ us ≡ true -> v ∈ us
  ∈ᵛ-sound v us e with any-true (v ≡ᵛ_) us e
  ... | u , m , e1 = subst (λ z -> z ∈ us) (sym (≡ᵛ-sound v u e1)) m

  ∈ᵛ-complete : (v : A) (us : List A) -> v ∈ us -> v ∈ᵛ us ≡ true
  ∈ᵛ-complete v us m = any-intro (v ≡ᵛ_) us m (≡ᵛ-refl v)

  ∈ᵛ-false : (v : A) (us : List A) -> v ∈ᵛ us ≡ false -> v ∈ us -> Empty
  ∈ᵛ-false v us e m = true≢false (trans (sym (∈ᵛ-complete v us m)) e)

  null-∈ᵛ : (ws : List A) (z : A) -> null ws ≡ true -> z ∈ᵛ ws ≡ false
  null-∈ᵛ []       z e = refl
  null-∈ᵛ (w ∷ ws) z ()

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

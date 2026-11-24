{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.DecEq -- a type with a sound, reflexive Boolean equality test, and
-- list membership decided by it.
--
-- DecEq A bundles the test with its two lemmas, so the graph layer takes one
-- argument for it; LTL.5-States.Reach builds the instance at Val, and
-- LTL.9-Tests.GraphExamples one at Nat.  Membership eq opens the record and
-- adds ∈ᵛ and ≢ᵛ.  It is a module rather than definitions inside the record,
-- so each lemma stays a definition of its own.  The superscript ᵛ reads
-- "vertex": every instance is used on the nodes of a graph.

module LTL.1-Lib.DecEq where

open import LTL.1-Lib.Prelude

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

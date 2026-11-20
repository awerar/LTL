{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Reach -- valuations as a set.
--
-- Defines the equality test _≡ᵛ_ on valuations, proves it sound and reflexive,
-- and instantiates LTL.Lib.Nodes at Val with it.  That instance supplies ∈ᵛ,
-- ≢ᵛ, the hypothesis names (Closed, AllSat, ...) and listBar to the rest of
-- the development; LTL.Countermodel.Walk instantiates LTL.SCC.Graph the same way.

module LTL.States.Reach where

open import LTL.States.Val public
open import LTL.Lib.Bar  public

------------------------------------------------------------------------
-- Valuations as a set

infix 4.5 _≡ᵛ_

_≡ᵛ_ : Val -> Val -> Bool
[]      ≡ᵛ []      = true
[]      ≡ᵛ (c ∷ w) = false
(b ∷ v) ≡ᵛ []      = false
(b ∷ v) ≡ᵛ (c ∷ w) = (b ⇔ᵇ c) ∧ᵇ (v ≡ᵛ w)

≡ᵛ-refl : (v : Val) -> v ≡ᵛ v ≡ true
≡ᵛ-refl []          = refl
≡ᵛ-refl (true  ∷ v) = ≡ᵛ-refl v
≡ᵛ-refl (false ∷ v) = ≡ᵛ-refl v

≡ᵛ-sound : (v w : Val) -> v ≡ᵛ w ≡ true -> v ≡ w
≡ᵛ-sound []      []      e = refl
≡ᵛ-sound []      (c ∷ w) ()
≡ᵛ-sound (b ∷ v) []      ()
≡ᵛ-sound (b ∷ v) (c ∷ w) e =
  cong₂ _∷_ (⇔ᵇ-sound b c (∧ᵇ-trueˡ (b ⇔ᵇ c) (v ≡ᵛ w) e))
            (≡ᵛ-sound v w (∧ᵇ-trueʳ (b ⇔ᵇ c) (v ≡ᵛ w) e))

-- The set layer, at Val.  ∈ᵛ comes from here:  v ∈ᵛ us = any (v ≡ᵛ_) us .

open import LTL.Lib.Nodes _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl public

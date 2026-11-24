{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Reach -- valuations as a set.
--
-- Defines the equality test on valuations, proves it sound and reflexive,
-- bundles the three as valEq (LTL.1-Lib.DecEq), and instantiates
-- LTL.1-Lib.Nodes at it.  That instance supplies ≡ᵛ, ∈ᵛ, ≢ᵛ, the hypothesis
-- names (Closed, AllSat, ...) and listBar to the rest of the development;
-- LTL.6-Countermodel.Walk instantiates LTL.1-Lib.Graph at valEq too.  The test
-- itself is private (sameVal), so ≡ᵛ reaches importers once, as valEq's field.

module LTL.5-States.Reach where

open import LTL.2-Syntax.Deriv public
open import LTL.1-Lib.Sets public
open import LTL.1-Lib.Bar  public
open import LTL.1-Lib.DecEq using (DecEq)

------------------------------------------------------------------------
-- Valuations as a set

private
  sameVal : Val -> Val -> Bool
  sameVal []      []      = true
  sameVal []      (c ∷ w) = false
  sameVal (b ∷ v) []      = false
  sameVal (b ∷ v) (c ∷ w) = (b ⇔ᵇ c) ∧ᵇ sameVal v w

  sameVal-refl : (v : Val) -> sameVal v v ≡ true
  sameVal-refl []          = refl
  sameVal-refl (true  ∷ v) = sameVal-refl v
  sameVal-refl (false ∷ v) = sameVal-refl v

  sameVal-sound : (v w : Val) -> sameVal v w ≡ true -> v ≡ w
  sameVal-sound []      []      e = refl
  sameVal-sound []      (c ∷ w) ()
  sameVal-sound (b ∷ v) []      ()
  sameVal-sound (b ∷ v) (c ∷ w) e =
    cong₂ _∷_ (⇔ᵇ-sound b c (∧ᵇ-trueˡ (b ⇔ᵇ c) (sameVal v w) e))
              (sameVal-sound v w (∧ᵇ-trueʳ (b ⇔ᵇ c) (sameVal v w) e))

valEq : DecEq Val
valEq = record { _≡ᵛ_    = sameVal
               ; ≡ᵛ-sound = sameVal-sound
               ; ≡ᵛ-refl  = sameVal-refl }

-- The set layer, at Val.  ∈ᵛ comes from here:  v ∈ᵛ us = any (v ≡ᵛ_) us .

open import LTL.1-Lib.Nodes valEq public

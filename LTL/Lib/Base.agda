{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Lib.Base -- Nat, Bool, Empty, Unit and propositional equality.
--
-- No standard library: Nat, Bool and ≡ are Agda's builtins.  They have to be,
-- since Agda.Builtin.String (used by LTL.Pretty) binds the NATURAL and EQUALITY
-- builtins to them, and LTL.Trusted uses the same Bool.  Empty is LTL.Trusted's
-- own, so the semantics of ¬ is literally a function into it.  Empty and Unit
-- keep these names because ⊥ and ⊤ are LTL formulas.
--
-- Boolean-valued tests carry a superscript naming the type they compare (≡ⁿ on
-- Nat here, ≡ᵛ on nodes, ≡ᶠ on formulas).  They are infix 4.5: tighter than
-- ≡, looser than ∷ and ++.

module LTL.Lib.Base where

------------------------------------------------------------------------
-- Natural numbers

open import Agda.Builtin.Nat public using (Nat; zero; suc; _+_)
  renaming (_-_ to _∸_)

------------------------------------------------------------------------
-- Bool

open import Agda.Builtin.Bool public using (Bool; true; false)

infix 0 if_then_else_

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else _ = x
if false then _ else y = y

infix 4.5 _≡ⁿ_

_≡ⁿ_ : Nat -> Nat -> Bool
zero  ≡ⁿ zero  = true
zero  ≡ⁿ suc _ = false
suc _ ≡ⁿ zero  = false
suc n ≡ⁿ suc m = n ≡ⁿ m

------------------------------------------------------------------------
-- Empty and Unit

open import LTL.Trusted public using (Empty)

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

record Unit : Set where
  constructor tt

------------------------------------------------------------------------
-- Propositional equality

open import Agda.Builtin.Equality public using (_≡_; refl)

sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl q = q

cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B}
      -> x ≡ x' -> y ≡ y' -> f x y ≡ f x' y'
cong₂ f refl refl = refl

subst : {A : Set} (P : A -> Set) {x y : A} -> x ≡ y -> P x -> P y
subst P refl px = px

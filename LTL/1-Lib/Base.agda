{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Base -- Nat, Bool, Empty, Unit and propositional equality.
--
-- No standard library: Nat, Bool and ≡ are Agda's builtins.  They have to be,
-- since Agda.Builtin.String (used by LTL.Pretty) binds the NATURAL and EQUALITY
-- builtins to them, and LTL.Statement uses the same Bool.  Empty is
-- LTL.Statement's own, so the semantics of ¬ is literally a function into it.
-- Empty and Unit keep these names because ⊥ and ⊤ are LTL formulas.

module LTL.1-Lib.Base where

------------------------------------------------------------------------
-- Natural numbers

open import Agda.Builtin.Nat public using (Nat; zero; suc; _+_)
  renaming (_-_ to _∸_)

------------------------------------------------------------------------
-- Bool

open import Agda.Builtin.Bool public using (Bool; true; false)

-- The implicit arguments the signatures below leave out.

private variable
  A B C : Set
  x y z : A

infix 0 if_then_else_

if_then_else_ : Bool -> A -> A -> A
if true  then x else _ = x
if false then _ else y = y

------------------------------------------------------------------------
-- Empty and Unit

open import LTL.Statement public using (Empty)

emptyElim : Empty -> A
emptyElim ()

record Unit : Set where
  constructor tt

------------------------------------------------------------------------
-- Propositional equality

open import Agda.Builtin.Equality public using (_≡_; refl)

sym : x ≡ y -> y ≡ x
sym refl = refl

trans : x ≡ y -> y ≡ z -> x ≡ z
trans refl q = q

cong : (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong₂ : (f : A -> B -> C) {x x' : A} {y y' : B}
      -> x ≡ x' -> y ≡ y' -> f x y ≡ f x' y'
cong₂ f refl refl = refl

subst : (P : A -> Set) {x y : A} -> x ≡ y -> P x -> P y
subst P refl px = px

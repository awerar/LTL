{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Base  (after BRA3.Base) -- basic prelude (Nat, Bool, Empty, Unit, ≡).
--
-- Self-contained; no dependency on BRA2.  The one change from BRA3.Base: Nat is
-- Agda's own Agda.Builtin.Nat rather than a local copy bound with the NATURAL
-- pragma.  The two are the same datatype with the same constructor names, but
-- a NATURAL binding can be made only once in a development, and
-- Agda.Builtin.String (needed by LTL.Pretty, the proof printer) makes it
-- through Agda.Builtin.Nat.  This is Agda's builtin library, not the standard
-- library, and the module is --safe.
--
-- BRA3.Base was pure ASCII (Eq x y, eqSym, ...).  The notation here follows
-- Agda's standard library instead -- x ≡ y, sym, trans, cong, subst -- since
-- that is what readers of Agda expect, and so do if_then_else_ and the
-- builtin _+_ and _∸_ (Agda.Builtin.Nat's _-_).  Empty and Unit keep their
-- names: ⊥ and ⊤ are the LTL constants of LTL.Formula.
--
-- Boolean-valued tests carry a superscript naming the type they compare:
-- ≡ⁿ here on Nat, ≡ᵛ ∈ᵛ ≢ᵛ on valuations (LTL.Reach, LTL.Bar), ≡ᶠ ∈ᶠ on
-- formulas (LTL.Formula, LTL.Skel), just as ∧ᵇ etc. (LTL.Prelude) act on
-- Bool.  They are infix 4.5: tighter than ≡, looser than ∷ and ++.

module LTL.Base where

------------------------------------------------------------------------
-- Natural numbers

open import Agda.Builtin.Nat public using (Nat; zero; suc; _+_)
  renaming (_-_ to _∸_)

------------------------------------------------------------------------
-- Bool

data Bool : Set where
  true  : Bool
  false : Bool

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

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

record Unit : Set where
  constructor tt

------------------------------------------------------------------------
-- Propositional equality

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl q = q

cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

subst : {A : Set} (P : A -> Set) {x y : A} -> x ≡ y -> P x -> P y
subst P refl px = px

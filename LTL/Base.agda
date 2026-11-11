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
-- that is what readers of Agda expect.  Empty and Unit keep their names:
-- ⊥ and ⊤ are the LTL constants of LTL.Formula.

module LTL.Base where

------------------------------------------------------------------------
-- Natural numbers

open import Agda.Builtin.Nat public using (Nat; zero; suc)

------------------------------------------------------------------------
-- Bool

data Bool : Set where
  true  : Bool
  false : Bool

boolCase : {A : Set} -> Bool -> A -> A -> A
boolCase true  x _ = x
boolCase false _ y = y

natEq : Nat -> Nat -> Bool
natEq zero    zero    = true
natEq zero    (suc _) = false
natEq (suc _) zero    = false
natEq (suc n) (suc m) = natEq n m

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

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Base  (copy of BRA3.Base, module renamed) -- basic ASCII prelude (Nat, Bool, Eq).
--
-- Self-contained; no dependency on BRA2.  The one change from BRA3.Base: Nat is
-- Agda's own Agda.Builtin.Nat rather than a local copy bound with the NATURAL
-- pragma.  The two are the same datatype with the same constructor names, but
-- a NATURAL binding can be made only once in a development, and
-- Agda.Builtin.String (needed by LTL.Pretty, the proof printer) makes it
-- through Agda.Builtin.Nat.  This is Agda's builtin library, not the standard
-- library, and the module is --safe.

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

data Eq {A : Set} (x : A) : A -> Set where
  refl : Eq x x

eqSym : {A : Set} {x y : A} -> Eq x y -> Eq y x
eqSym refl = refl

eqTrans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
eqTrans refl q = q

eqCong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
eqCong f refl = refl

eqSubst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
eqSubst P refl px = px

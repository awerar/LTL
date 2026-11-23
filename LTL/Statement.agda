{-# OPTIONS --safe --without-K --exact-split #-}

-- This file contains the proof statement, and may only be modified by hand

module LTL.Statement where
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Bool
  open import Agda.Builtin.List
  open import Agda.Builtin.Nat

  Var : Set
  Var = Nat

  data Empty : Set where

  data Formula : Set where
    var : Var -> Formula
    ¬_  : Formula -> Formula
    _⇒_ : Formula -> Formula -> Formula
    ○_  : Formula -> Formula
    □_  : Formula -> Formula

  Instant : Set
  Instant = Var -> Bool

  Interpretation : Set
  Interpretation = Nat -> Instant

  Period : Set
  Period = List Instant

  record Position : Set where
    constructor at
    field
      now  : Instant
      rest : Period
  open Position

  record Lasso : Set where
    field
      start    : Period
      loop : Position
  open Lasso

  initial : Lasso -> Position
  initial l with start l
  ... | []     = loop l
  ... | x ∷ xs = at x xs

  step : Lasso -> Position -> Position
  step l (at _ (y ∷ ys)) = at y ys
  step l (at _ [])       = loop l

  position : Lasso -> Nat -> Position
  position l zero    = initial l
  position l (suc n) = step l (position l n)

  interpret : Lasso -> Interpretation
  interpret l n = now (position l n)

  infixr 8 _⇒_
  infix  9 ¬_ ○_ □_
  infix  4 _,_⊨_

  _,_⊨_ : Interpretation -> Nat -> Formula -> Set
  σ , n ⊨ var x = σ n x ≡ true
  σ , n ⊨ ¬ A   = σ , n ⊨ A -> Empty
  σ , n ⊨ A ⇒ B = σ , n ⊨ A -> σ , n ⊨ B
  σ , n ⊨ ○ A   = σ , suc n ⊨ A
  σ , n ⊨ □ A   = (k : Nat) -> σ , k + n ⊨ A

  valid : Formula -> Set
  valid f = (lasso : Lasso) -> (interpret lasso) , 0 ⊨ f

  record LassoCountermodel (f : Formula) : Set where
    constructor counter
    field
      lasso : Lasso
      falseAtStart : (interpret lasso) , 0 ⊨ (¬ f)

  record DecisionProcedure : Set where
    field
      decideValid : Formula -> Bool
      validIfTrue : (f : Formula) -> decideValid f ≡ true -> valid f
      counterIfFalse : (f : Formula) -> decideValid f ≡ false -> LassoCountermodel f
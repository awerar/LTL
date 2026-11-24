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

  record _↔_ (A B : Set) : Set where
    constructor iff
    field to : A -> B ; from : B -> A

  data Formula : Set where
    var : Var -> Formula
    ¬_  : Formula -> Formula
    _⇒_ : Formula -> Formula -> Formula
    ○_  : Formula -> Formula
    □_  : Formula -> Formula

  _∧_ : Formula -> Formula -> Formula
  A ∧ B = ¬ (A ⇒ ¬ B)

  _⇔_ : Formula -> Formula -> Formula
  A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)

  infix  30 ¬_ ○_ □_
  infixr 22 _∧_
  infixr 20 _⇒_
  infix  19 _⇔_
  infix  10 ⊢_ 
  infix   3 _↔_ 

  not : Bool -> Bool
  not true  = false
  not false = true

  imp : Bool -> Bool -> Bool
  imp true  b = b
  imp false b = true

  propValue : (Formula -> Bool) -> Formula -> Bool
  propValue ρ (¬ A)   = not (propValue ρ A)
  propValue ρ (A ⇒ B) = imp (propValue ρ A) (propValue ρ B)
  propValue ρ (var x) = ρ (var x)
  propValue ρ (○ A)   = ρ (○ A)
  propValue ρ (□ A)   = ρ (□ A)

  Tautology : Formula -> Set
  Tautology A = (ρ : Formula -> Bool) -> propValue ρ A ≡ true

  data ⊢_ : Formula -> Set where
    p1 : {A B : Formula} -> ⊢ A ⇒ B ⇒ A
    p2 : {A B C : Formula} -> ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
    p3 : {A B : Formula} -> ⊢ (¬ B ⇒ ¬ A) ⇒ A ⇒ B
    k□ : {A B : Formula} -> ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B
    k○ : {A B : Formula} -> ⊢ ○ (A ⇒ B) ⇒ ○ A ⇒ ○ B
    exp : {A : Formula} -> ⊢ □ A ⇒ A ∧ ○ A ∧ ○ □ A
    ind : {A : Formula} -> ⊢ □ (A ⇒ ○ A) ⇒ A ⇒ □ A
    lin : {A : Formula} -> ⊢ ○ ¬ A ⇔ ¬ ○ A

    mp : {A B : Formula} -> ⊢ A ⇒ B -> ⊢ A -> ⊢ B
    gen : {A : Formula} -> ⊢ A -> ⊢ □ A

    pc : {A : Formula} -> Tautology A -> ⊢ A

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
      start : Period
      loop  : Position
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

  infix   4 _,_⊨_

  _,_⊨_ : Interpretation -> Nat -> Formula -> Set
  σ , n ⊨ var x = σ n x ≡ true
  σ , n ⊨ ¬ A   = σ , n ⊨ A -> Empty
  σ , n ⊨ A ⇒ B = σ , n ⊨ A -> σ , n ⊨ B
  σ , n ⊨ ○ A   = σ , suc n ⊨ A
  σ , n ⊨ □ A   = (k : Nat) -> σ , k + n ⊨ A

  Valid : Formula -> Set
  Valid f = (lasso : Lasso) -> (interpret lasso) , 0 ⊨ f

  record LassoCountermodel (f : Formula) : Set where
    constructor counter
    field
      lasso : Lasso
      falseAtStart : (interpret lasso) , 0 ⊨ (¬ f)

  record DecisionProcedure : Set where
    field
      decideValid : Formula -> Bool
      validIfTrue : (f : Formula) -> decideValid f ≡ true -> Valid f
      counterIfFalse : (f : Formula) -> decideValid f ≡ false -> LassoCountermodel f

  record Statement : Set where
    field
      procedure      : DecisionProcedure
      deriveComplete : (f : Formula) -> (⊢ f) ↔ Valid f
      countermodelComplete  : (f : Formula) -> LassoCountermodel f ↔ (Valid f -> Empty)
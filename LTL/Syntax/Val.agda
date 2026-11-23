{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Syntax.Val -- signed literals, and conjunction and disjunction over a
-- list, the pieces of the characteristic formula chi v (LTL.States.State).
--
-- A valuation (Val, LTL.Syntax.Skel) is a row of bits over the atoms of
-- sub P.  The empty disjunction is ⊥ and the empty conjunction is ⊤.

module LTL.Syntax.Val where

open import LTL.Syntax.Deriv public

------------------------------------------------------------------------
-- Signed occurrences, conjunction and disjunction over a list

lit : Formula -> Bool -> Formula
lit A true  = A
lit A false = ¬ A

infix 30 ⋀_ ⋁_

⋀_ : List Formula -> Formula
⋀ []       = ⊤
⋀ (A ∷ As) = A ∧ ⋀ As

⋁_ : List Formula -> Formula
⋁ []       = ⊥
⋁ (A ∷ As) = A ∨ ⋁ As

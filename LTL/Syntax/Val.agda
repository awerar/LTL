{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Syntax.Val -- signed literals, and conjunction and disjunction over a
-- list, the pieces of the characteristic formula chi v (LTL.States.State).
--
-- A valuation is a List Bool read positionally against sub P.  Since sub P may
-- repeat formulas, LTL.States.State adds a coherence clause.  The empty
-- disjunction is ⊥ and the empty conjunction is ⊤.

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

------------------------------------------------------------------------
-- The characteristic formula

litList : List Formula -> Val -> List Formula
litList []       v         = []
litList (A ∷ As) []        = []
litList (A ∷ As) (b ∷ bs)  = lit A b ∷ litList As bs

------------------------------------------------------------------------
-- The projection lemma: a membership proof for A in sub P locates the literal
-- of A inside chi v, signed by v's bit at that position.  Every projection of
-- a conjunct of chi goes through it.

litList-mem : {A : Formula} (As : List Formula) (v : Val)
           -> length v ≡ length As
           -> (h : A ∈ As)
           -> lit A (bitAt v (index h)) ∈ litList As v
litList-mem []       v       e ()
litList-mem (A ∷ As) []      () h
litList-mem (A ∷ As) (b ∷ v) e here      = here
litList-mem (A ∷ As) (b ∷ v) e (there h) =
  there (litList-mem As v (sucInj e) h)

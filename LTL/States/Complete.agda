{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Complete -- state completeness: ⊢ beta St.
--
-- First the disjunction over ALL valuations, by induction along sub P,
-- splitting on the next formula with (L6) (splitD).  Then the non-states are
-- dropped with ⋁Drop and nonState.  stepEq lines up the shapes: allVecs
-- (suc n) and splitOn both cons onto a list and append, and agree once chi is
-- applied.  The proof is exponential in |sub P|; LTL.Procedures.CompletePC
-- proves the same formula with (PC).

open import LTL.Syntax.Formula using (Formula)

module LTL.States.Complete (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.NonState P

------------------------------------------------------------------------
-- Dropping the non-states

⋁Filter : (vs : List Val)
       -> AllLen (length (sub P)) vs
       -> ⊢ ⋁ (map chi vs)
            ⇒ ⋁ (map chi (filter isState vs))
⋁Filter []       alNil          = ⇒Refl
⋁Filter (v ∷ vs) (alCons len al) with isState v in e
... | true  = ∨MonoR (⋁Filter vs al)
... | false =
  ⇒Trans (⋁Drop (map chi vs) (nonState v len e)) (⋁Filter vs al)

------------------------------------------------------------------------
-- State completeness

stateComplete : ⊢ beta St
stateComplete =
  mp (⋁Filter (allVecs (length (sub P)))
                 (allVecs-allLen (length (sub P))))
     (allComplete (sub P))

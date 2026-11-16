{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Reach -- valuations as a set, and successor lists.
--
-- Here the generic set layer meets valuations.  LTL.Sets and LTL.Bar are
-- stated for any element type, and LTL.Nodes for any node type with an
-- equality test; below,  _≡ᵛ_  is defined, proved sound and reflexive, and
-- LTL.Nodes is instantiated at Val with it.  That instance supplies ∈ᵛ ≢ᵛ,
-- the hypothesis names (Closed, AllSat, ...) and listBar to the whole
-- development.  LTL.SccLasso instantiates LTL.Graph with the same three
-- arguments.
--
-- G7 of FORMALISATION-PLAN.md is Reach_U(v) of m4.tex section 3, the states
-- reachable from v by ->-steps inside U.  The elimination does not compute it:
-- (R2) uses the largest closed set of unfulfilling states instead (LTL.Gfp),
-- and gfpSound/gfpComplete there show that this is the note's condition, with
-- Reach_U(v) in its exact sense as the inductive type Path.  The SCC procedure
-- computes reachable sets in LTL.Graph (reachSet).

module LTL.Reach where

open import LTL.Step public
open import LTL.Bar  public

------------------------------------------------------------------------
-- Valuations as a set

infix 4.5 _≡ᵛ_

_≡ᵛ_ : Val -> Val -> Bool
[]      ≡ᵛ []      = true
[]      ≡ᵛ (c ∷ w) = false
(b ∷ v) ≡ᵛ []      = false
(b ∷ v) ≡ᵛ (c ∷ w) = (b ⇔ᵇ c) ∧ᵇ (v ≡ᵛ w)

≡ᵛ-refl : (v : Val) -> v ≡ᵛ v ≡ true
≡ᵛ-refl []          = refl
≡ᵛ-refl (true  ∷ v) = ≡ᵛ-refl v
≡ᵛ-refl (false ∷ v) = ≡ᵛ-refl v

≡ᵛ-sound : (v w : Val) -> v ≡ᵛ w ≡ true -> v ≡ w
≡ᵛ-sound []      []      e = refl
≡ᵛ-sound []      (c ∷ w) ()
≡ᵛ-sound (b ∷ v) []      ()
≡ᵛ-sound (b ∷ v) (c ∷ w) e =
  cong₂ _∷_ (⇔ᵇ-sound b c (∧ᵇ-trueˡ (b ⇔ᵇ c) (v ≡ᵛ w) e))
            (≡ᵛ-sound v w (∧ᵇ-trueʳ (b ⇔ᵇ c) (v ≡ᵛ w) e))

-- The set layer, at Val.  ∈ᵛ comes from here:  v ∈ᵛ us = any (v ≡ᵛ_) us .

open import LTL.Nodes _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl public

------------------------------------------------------------------------
-- Reading a successor list

module _ (P : Formula) where

  succsMem : (us : List Val) (v : Val) {w : Val}
          -> w ∈ succs P us v -> w ∈ us × step P v w ≡ true
  succsMem us v m =
    filter-sub (step P v) us m , filter-prop (step P v) us m

  succsIn : (us : List Val) (v : Val) {w : Val}
         -> w ∈ us -> step P v w ≡ true -> w ∈ succs P us v
  succsIn us v mw st = filter-true (step P v) us mw st

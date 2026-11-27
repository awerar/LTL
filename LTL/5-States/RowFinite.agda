{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.RowFinite -- the rows over a list of atoms (LTL.2-Syntax.Skel)
-- as a finite set: their equality test rowEq, inductive finiteness, and the
-- guard that keeps the searches over them cheap.
--
-- A row over X ∷ As is a Bool paired with a row over As, so exhaustibleProd
-- applies, and exhaustiblePreimage transports the result back along uncons:
-- O(|As|) steps, not 2^|As|.  rows never appears.  Every row over As has the
-- right shape by its type, so every set of rows is finite (AllFinite).

module LTL.5-States.RowFinite where

open import LTL.2-Syntax.Deriv
open import LTL.1-Lib.Exhaustible
open import LTL.1-Lib.DecEq using (DecEq; module Membership; Finite; boolFinite)

------------------------------------------------------------------------
-- Equality of rows

private
  sameRow : {As : List Formula} -> Row As -> Row As -> Bool
  sameRow ∅       ∅       = true
  sameRow (b ▸ v) (c ▸ w) = (b ⇔ᵇ c) ∧ᵇ sameRow v w

  sameRow-refl : {As : List Formula} (v : Row As) -> sameRow v v ≡ true
  sameRow-refl ∅           = refl
  sameRow-refl (true  ▸ v) = sameRow-refl v
  sameRow-refl (false ▸ v) = sameRow-refl v

  sameRow-sound : {As : List Formula} (v w : Row As) -> sameRow v w ≡ true -> v ≡ w
  sameRow-sound ∅       ∅       e = refl
  sameRow-sound (b ▸ v) (c ▸ w) e
    with ⇔ᵇ-sound b c (∧ᵇ-trueˡ (b ⇔ᵇ c) (sameRow v w) e)
       | sameRow-sound v w (∧ᵇ-trueʳ (b ⇔ᵇ c) (sameRow v w) e)
  ... | refl | refl = refl

rowEq : (As : List Formula) -> DecEq (Row As)
rowEq As = record { _≡ᵛ_    = sameRow
                  ; ≡ᵛ-sound = sameRow-sound
                  ; ≡ᵛ-refl  = sameRow-refl }

------------------------------------------------------------------------
-- Every row over As, as a pool, is inductively finite.

private
  uncons : {X : Formula} {As : List Formula} -> Row (X ∷ As) -> Bool × Row As
  uncons (b ▸ r) = b , r

  unconsApart : {X : Formula} {As : List Formula} (y z : Row (X ∷ As))
             -> Membership._≢ᵛ_ (rowEq (X ∷ As)) y z ≡ true
             -> prodApart _≢ᵇ_ (Membership._≢ᵛ_ (rowEq As)) (uncons y) (uncons z) ≡ true
  unconsApart (b ▸ v) (c ▸ w) e = ¬ᵇ-∧ᵇ (b ⇔ᵇ c) (sameRow v w) e

rowFinite : (As : List Formula) -> Finite (rowEq As) (λ r -> true)
rowFinite [] =
  everyPick (λ { ∅ x∈ -> everyPick (λ { ∅ () }) })
rowFinite (X ∷ As) =
  exhaustibleSubset (λ { (b ▸ r) e -> refl })
    (exhaustiblePreimage uncons (λ r -> true) (λ y y∈ z z∈ -> unconsApart y z)
                         (exhaustibleProd boolFinite (rowFinite As)))

------------------------------------------------------------------------
-- The guard of Barras, refined by Gonthier (Coquand and Siles, section 5).
--
-- A function defined by recursion on an Exhaustible proof forces the proof as
-- it runs.  rowFinite gives the Pi-form a guard needs (every pool of rows
-- over As is finite, by exhaustibleSubset), and guardFinite at a given depth
-- supplies 2^depth constructors lazily, so a search of fewer than 2^depth
-- picks never touches the fallback, rowFinite.

AllFinite : List Formula -> Set
AllFinite As = (Pool : Subset (Row As)) -> Finite (rowEq As) Pool

allRowFinite : (As : List Formula) -> AllFinite As
allRowFinite As Pool = exhaustibleSubset (λ r e -> refl) (rowFinite As)

module _ (As : List Formula) where

  open Membership (rowEq As) using (_≢ᵛ_)

  guardFinite : (depth : Nat) -> AllFinite As -> AllFinite As
  guardFinite zero        fallback = fallback
  guardFinite (suc depth) fallback =
    λ Pool -> everyPick (λ x x∈ ->
      guardFinite depth (guardFinite depth fallback) (Pool ∩ (x ≢ᵛ_)))

-- The guard depth is |As| itself.  A search choosing distinct rows over As
-- runs at most 2^|As| steps, so depth |As| is exactly enough.  A literal depth
-- would be worse: guardFinite at depth d unfolds to 2^d copies, and Agda
-- normalises the constructor types of data types that mention U_inf (Trail,
-- Lasso, ValidPos).  With As = atoms P and P a variable the match on the
-- depth is blocked and the guard stays folded; on a closed formula it reduces
-- and the guard does its job.

guardedRowFinite : (As : List Formula) -> AllFinite As
guardedRowFinite As = guardFinite As (length As) (allRowFinite As)

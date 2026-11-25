{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.VecBar -- valuations of a given length are inductively finite,
-- and the guard that keeps the searches over them cheap.

module LTL.5-States.VecBar where

open import LTL.5-States.Reach public

------------------------------------------------------------------------
-- Vectors of a given length are inductively finite -- in O(n), not 2^n.  A
-- valuation of length n+1 is a Bool paired with one of length n, so barProd
-- applies, and barPreimage transports the result back along uncons.  allVals
-- never appears.

-- v has length n, as a boolean predicate (so that it can be a Bar's pool).

hasLength : Nat -> Val -> Bool
hasLength n v = length v ≡ⁿ n

headV : Val -> Bool
headV []      = false
headV (b ∷ v) = b

tailV : Val -> Val
tailV []      = []
tailV (b ∷ v) = v

unconsV : Val -> Bool × Val
unconsV v = headV v , tailV v

lenZero : (v : Val) -> length v ≡ⁿ zero ≡ true -> v ≡ []
lenZero []      e = refl
lenZero (b ∷ v) ()

lenTail : (m : Nat) (v : Val) -> hasLength (suc m) v ≡ true
       -> hasLength m (tailV v) ≡ true
lenTail m []      ()
lenTail m (b ∷ v) e = e

unconsNeq : (m : Nat) (y z : Val) -> hasLength (suc m) y ≡ true
         -> hasLength (suc m) z ≡ true -> y ≢ᵛ z ≡ true
         -> prodApart _≢ᵇ_ _≢ᵛ_ (unconsV y) (unconsV z) ≡ true
unconsNeq m []      z       () ez e
unconsNeq m (b ∷ v) []      ey () e
unconsNeq m (b ∷ v) (c ∷ w) ey ez e = ¬ᵇ-∧ᵇ (b ⇔ᵇ c) (v ≡ᵛ w) e

vecFinite : (n : Nat) -> Finite (hasLength n)
vecFinite zero =
  picks (λ x x∈ -> picks (λ y y∈ ->
    emptyElim (clash x y x∈ (∧ᵇ-trueˡ (hasLength zero y) (x ≢ᵛ y) y∈)
                            (∧ᵇ-trueʳ (hasLength zero y) (x ≢ᵛ y) y∈))))
  where
    clash : (x y : Val) -> hasLength zero x ≡ true -> hasLength zero y ≡ true
         -> x ≢ᵛ y ≡ true -> Empty
    clash x y x∈ y∈ e = true≢false (sym nil2)
      where
        -- both are [], and [] ≢ᵛ [] is false
        nil2 : [] ≢ᵛ [] ≡ true
        nil2 = subst (λ u -> u ≢ᵛ [] ≡ true) (lenZero x x∈)
                     (subst (λ u -> x ≢ᵛ u ≡ true) (lenZero y y∈) e)
vecFinite (suc m) =
  barSubset (∩-intro ⊆ᵖ-refl (lenTail m))
            (barPreimage unconsV (hasLength (suc m)) (unconsNeq m)
                         (barProd boolFinite (vecFinite m)))

------------------------------------------------------------------------
-- A valuation of length n is in the pool hasLength n; with allVals-len
-- (LTL.2-Syntax.Skel) this makes it a correct pool for St P, and the search
-- never touches the enumeration.

hasLength-intro : (n : Nat) (v : Val) -> length v ≡ n -> hasLength n v ≡ true
hasLength-intro n v e = subst (λ k -> length v ≡ⁿ k ≡ true) e (≡ⁿ-refl (length v))

------------------------------------------------------------------------
-- The guard of Barras, refined by Gonthier (Coquand and Siles, section 5).
--
-- A function defined by recursion on a Bar forces the Bar as it runs.
-- vecFinite gives the Pi-form a guard needs (every pool inside the length-n
-- vectors is finite, by barSubset), and guardFinite at a given depth supplies
-- 2^depth constructors lazily, so a search of fewer than 2^depth picks never
-- touches the fallback, vecFinite.

AllFinite : Nat -> Set
AllFinite n = (Pool : Pred) -> Pool ⊆ᵖ hasLength n -> Finite Pool

allVecFinite : (n : Nat) -> AllFinite n
allVecFinite n Pool subset = barSubset subset (vecFinite n)

guardFinite : (n depth : Nat) -> AllFinite n -> AllFinite n
guardFinite n zero        fallback = fallback
guardFinite n (suc depth) fallback =
  λ Pool subset -> picks (λ x x∈ ->
    guardFinite n depth (guardFinite n depth fallback)
                (Pool ∩ (x ≢ᵛ_)) (⊆ᵖ-trans ∩-fst subset))

-- The guard depth is n itself.  A search choosing distinct vectors of length n
-- runs at most 2^n steps, so depth n is exactly enough.  A literal depth would
-- be worse: guardFinite at depth d unfolds to 2^d copies, and Agda normalises
-- the constructor types of data types that mention U_inf (Trail, Lasso,
-- ValidPos).  With depth n and P a variable the match on the depth is blocked
-- and the guard stays folded; on a closed formula n reduces and the guard
-- does its job.

guardedVecFinite : (n : Nat) -> AllFinite n
guardedVecFinite n = guardFinite n n (allVecFinite n)

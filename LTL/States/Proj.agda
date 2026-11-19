{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Proj -- from Boolean facts about a valuation to derivations.
--
-- Every refutation of a valuation has the same shape: a Boolean condition
-- fails, so some conjunct of chi P v carries a particular literal, so chi P v
-- is refutable.  This module supplies the projections ⊢ chi P v ⇒ literal
-- (chiProj, chiProjPos, chiProjVal), and cohLookup: under coherence, the bit
-- at ANY occurrence of a formula equals valOf.

module LTL.States.Proj where

open import LTL.Rules.Temporal public
open import LTL.States.State    public

------------------------------------------------------------------------
-- Refutation from a formula and its negation

refute : {C B : Formula} -> ⊢ C ⇒ B -> ⊢ C ⇒ ¬ B -> ⊢ ¬ C
refute f g = mp (¬IntroU (liftP f) (liftP g)) deriv⊤

------------------------------------------------------------------------
-- Under coherence, every occurrence of A carries the bit valOf P v A

module _ (P : Formula) where

  cohLookup : (v : Val)
           -> allCoh P v (length (sub P)) ≡ true
           -> {A : Formula} (h : A ∈ sub P)
           -> bitAt v (index h) ≡ valOf P v A
  cohLookup v ch {A} h =
    trans (⇔ᵇ-sound (bitAt v (index h))
                    (valOf P v (nth (sub P) (index h) ⊥))
                    (allCoh-at P v (length (sub P)) (index h)
                                   (index-length h) ch))
          (cong (valOf P v) (index-nth h ⊥))

  ------------------------------------------------------------------------
  -- Projection of a conjunct out of chi

  chiProjRaw : (v : Val)
            -> length v ≡ length (sub P)
            -> {A : Formula} (h : A ∈ sub P)
            -> ⊢ (chi P v) ⇒ (lit A (bitAt v (index h)))
  chiProjRaw v len h =
    ⋀Proj (litList (sub P) v) (litList-mem (sub P) v len h)

  chiProj : (v : Val)
         -> length v ≡ length (sub P)
         -> allCoh P v (length (sub P)) ≡ true
         -> {A : Formula} (h : A ∈ sub P)
         -> ⊢ (chi P v) ⇒ (lit A (valOf P v A))
  chiProj v len ch {A} h =
    subst (λ b -> ⊢ (chi P v) ⇒ (lit A b))
          (cohLookup v ch h)
          (chiProjRaw v len h)

------------------------------------------------------------------------
-- Positional projection, for the case where coherence fails and cohLookup is
-- not available.

litList-nth : (As : List Formula) (v : Val) (i : Nat)
           -> i < length As -> length v ≡ length As
           -> lit (nth As i ⊥) (bitAt v i) ∈ litList As v
litList-nth []       v       i       ()        len
litList-nth (A ∷ As) []      i       lt        ()
litList-nth (A ∷ As) (b ∷ v) zero    lt        len = here
litList-nth (A ∷ As) (b ∷ v) (suc i) (ltSuc l) len =
  there (litList-nth As v i l (sucInj len))

chiProjPos : (P : Formula) (v : Val)
          -> length v ≡ length (sub P)
          -> (i : Nat) -> i < length (sub P)
          -> ⊢ (chi P v) ⇒ (lit (nth (sub P) i ⊥) (bitAt v i))
chiProjPos P v len i lt =
  ⋀Proj (litList (sub P) v) (litList-nth (sub P) v i lt len)

------------------------------------------------------------------------
-- The first-occurrence index is a position in range that carries its formula.
-- This is what projecting the literal signed by valOf needs without
-- coherence.

indexOf-lt : (xs : List Formula) {X : Formula} -> X ∈ xs -> indexOf xs X < length xs
indexOf-lt []       ()
indexOf-lt (B ∷ Bs) here     = aux (B ≡ᶠ B) (≡ᶠ-refl B)
  where
    aux : (b : Bool) -> b ≡ true -> indexOfCons b (indexOf Bs B) < suc (length Bs)
    aux true  e  = ltZero
    aux false ()
indexOf-lt (B ∷ Bs) {X} (there m) = aux (B ≡ᶠ X)
  where
    aux : (b : Bool) -> indexOfCons b (indexOf Bs X) < suc (length Bs)
    aux true  = ltZero
    aux false = ltSuc (indexOf-lt Bs m)

indexOf-nth : (xs : List Formula) {X : Formula} -> X ∈ xs
           -> nth xs (indexOf xs X) ⊥ ≡ X
indexOf-nth []       ()
indexOf-nth (B ∷ Bs) here     = aux (B ≡ᶠ B) (≡ᶠ-refl B)
  where
    aux : (b : Bool) -> b ≡ true
       -> nth (B ∷ Bs) (indexOfCons b (indexOf Bs B)) ⊥ ≡ B
    aux true  e  = refl
    aux false ()
indexOf-nth (B ∷ Bs) {X} (there m) = aux (B ≡ᶠ X) (≡ᶠ-sound B X)
  where
    aux : (b : Bool) -> (b ≡ true -> B ≡ X)
       -> nth (B ∷ Bs) (indexOfCons b (indexOf Bs X)) ⊥ ≡ X
    aux true  f = f refl
    aux false f = indexOf-nth Bs m

-- Projection signed by valOf, available without coherence.

chiProjVal : (P : Formula) (v : Val)
          -> length v ≡ length (sub P)
          -> {X : Formula} (m : X ∈ sub P)
          -> ⊢ (chi P v) ⇒ (lit X (valOf P v X))
chiProjVal P v len {X} m =
  subst (λ Y -> ⊢ (chi P v) ⇒ (lit Y (bitAt v (indexOf (sub P) X))))
        (indexOf-nth (sub P) m)
        (chiProjPos P v len (indexOf (sub P) X) (indexOf-lt (sub P) m))

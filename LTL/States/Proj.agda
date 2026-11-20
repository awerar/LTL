{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Proj -- from Boolean facts about a valuation to derivations.
--
-- Every refutation of a valuation has the same shape: a Boolean condition
-- fails, so some conjunct of chi v carries a particular literal, so chi v
-- is refutable.  This module supplies the projections ⊢ chi v ⇒ literal
-- (chiProj, chiProjPos, chiProjVal), and cohLookup: under coherence, the bit
-- at ANY occurrence of a formula equals valOf.

open import LTL.Syntax.Formula using (Formula)

module LTL.States.Proj (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P

------------------------------------------------------------------------
-- Under coherence, every occurrence of A carries the bit valOf v A

cohLookup : (v : Val)
         -> allCoh v (length (sub P)) ≡ true
         -> {A : Formula} (h : A ∈ sub P)
         -> bitAt v (index h) ≡ valOf v A
cohLookup v ch {A} h =
  trans (⇔ᵇ-sound (bitAt v (index h))
                  (valOf v (nth (sub P) (index h) ⊥))
                  (allCoh-at v (length (sub P)) (index h)
                                 (index-length h) ch))
        (cong (valOf v) (index-nth h ⊥))

------------------------------------------------------------------------
-- Projection of a conjunct out of chi

chiProjRaw : (v : Val)
          -> length v ≡ length (sub P)
          -> {A : Formula} (h : A ∈ sub P)
          -> ⊢ (chi v) ⇒ (lit A (bitAt v (index h)))
chiProjRaw v len h =
  ⋀Proj (litList (sub P) v) (litList-mem (sub P) v len h)

chiProj : (v : Val)
       -> length v ≡ length (sub P)
       -> allCoh v (length (sub P)) ≡ true
       -> {A : Formula} (h : A ∈ sub P)
       -> ⊢ (chi v) ⇒ (lit A (valOf v A))
chiProj v len ch {A} h =
  subst (λ b -> ⊢ (chi v) ⇒ (lit A b))
        (cohLookup v ch h)
        (chiProjRaw v len h)

chiProjPos : (v : Val)
          -> length v ≡ length (sub P)
          -> (i : Nat) -> i < length (sub P)
          -> ⊢ (chi v) ⇒ (lit (nth (sub P) i ⊥) (bitAt v i))
chiProjPos v len i lt =
  ⋀Proj (litList (sub P) v) (litList-nth (sub P) v i lt len)

-- Projection signed by valOf, available without coherence.

chiProjVal : (v : Val)
          -> length v ≡ length (sub P)
          -> {X : Formula} (m : X ∈ sub P)
          -> ⊢ (chi v) ⇒ (lit X (valOf v X))
chiProjVal v len {X} m =
  subst (λ Y -> ⊢ (chi v) ⇒ (lit Y (bitAt v (indexOf (sub P) X))))
        (indexOf-nth (sub P) m)
        (chiProjPos v len (indexOf (sub P) X) (indexOf-lt (sub P) m))

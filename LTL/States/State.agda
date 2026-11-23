{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.State -- which valuations are states, St, the list of all
-- states, and the characteristic formulas chi and beta.
--
-- A state respects the connectives (S1) and satisfies  □ A in v  implies
-- A in v  (S2).  A third clause, coherence, requires duplicate entries of
-- sub P to carry the same bit, so that a state is a function on the SET of
-- subformulas (sub P repeats; see subBenAri-dup in LTL.Tests.Checks).
--
-- This module and the ones built on it (Step, Proj, ..., SccSeed) are
-- parameterised by P, the formula whose subformulas index the valuations.  They
-- open each other at P privately and re-export nothing: an importer outside
-- opens them unapplied, which gives every name P as its first argument.

open import LTL.Syntax.Formula using (Formula)

module LTL.States.State (P : Formula) where

open import LTL.Syntax.Val
open import LTL.Lib.Sets using (filter-sub)

------------------------------------------------------------------------
-- The characteristic formula chi v of a valuation, and beta vs, the
-- disjunction of chi over a list of valuations.

chi : Val -> Formula
chi v = ⋀ (litList (sub P) v)

beta : List Val -> Formula
beta vs = ⋁ (map chi vs)

------------------------------------------------------------------------
-- Lookup by first occurrence.  valOf v A is the bit v assigns to A at the
-- FIRST position of sub P carrying A.  Under coherence it agrees with every
-- position carrying A, so chi (built positionally) and the conditions below
-- (built by lookup) talk about the same bits.

valOf : Val -> Formula -> Bool
valOf v A = bitAt v (indexOf (sub P) A)

------------------------------------------------------------------------
-- (S1) and (S2), imposed at each member of sub P.  var and ○ carry no local
-- condition: ○ is handled by the transition relation (LTL.States.Step).

okAt : Val -> Formula -> Bool
okAt v (var n) = true
okAt v (¬ A)   = valOf v (¬ A) ⇔ᵇ ¬ᵇ valOf v A
okAt v (A ⇒ B) = valOf v (A ⇒ B) ⇔ᵇ valOf v A ⇒ᵇ valOf v B
okAt v (○ A)   = true
okAt v (□ A)   = valOf v (□ A) ⇒ᵇ valOf v A

allOk : Val -> List Formula -> Bool
allOk v = all (okAt v)

------------------------------------------------------------------------
-- Coherence on duplicates: every position agrees with the first occurrence
-- of its formula.  This is linear, and equivalent to pairwise agreement.

cohAt : Val -> Nat -> Bool
cohAt v i = bitAt v i ⇔ᵇ valOf v (nth (sub P) i ⊥)

allCoh : Val -> Nat -> Bool
allCoh v zero    = true
allCoh v (suc n) = cohAt v n ∧ᵇ allCoh v n

------------------------------------------------------------------------
-- States

isState : Val -> Bool
isState v = allOk v (sub P) ∧ᵇ
            allCoh v (length (sub P))

St : List Val
St = filter isState (allVecs (length (sub P)))

-- Every state has the length chi expects.

stLen : {v : Val} -> v ∈ St -> length v ≡ length (sub P)
stLen {v} m =
  allVecs-len (length (sub P)) v (filter-sub isState (allVecs (length (sub P))) m)

------------------------------------------------------------------------
-- Searching allCoh

allCoh-at : (v : Val) (n i : Nat) -> i < n
         -> allCoh v n ≡ true -> cohAt v i ≡ true
allCoh-at v zero    i ()  e
allCoh-at v (suc n) i lt  e =
  sumElim (λ eq -> subst (λ k -> cohAt v k ≡ true) (sym eq)
                         (∧ᵇ-trueˡ (cohAt v n) (allCoh v n) e))
          (λ l  -> allCoh-at v n i l (∧ᵇ-trueʳ (cohAt v n) (allCoh v n) e))
          (ltSucCase i n lt)

allCoh-false : (v : Val) (n : Nat)
            -> allCoh v n ≡ false
            -> Σ[ i ∈ Nat ] i < n × cohAt v i ≡ false
allCoh-false v zero    ()
allCoh-false v (suc n) e =
  sumElim (λ e1 -> n , ltNSucN n , e1)
          (λ e2 -> shift (allCoh-false v n e2))
          (∧ᵇ-false (cohAt v n) (allCoh v n) e)
  where
    shift : (Σ[ i ∈ Nat ] i < n × cohAt v i ≡ false)
         -> Σ[ i ∈ Nat ] i < suc n × cohAt v i ≡ false
    shift (i , l , q) = i , ltWeak l , q

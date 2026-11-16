{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.State -- G5 of FORMALISATION-PLAN.md.
--
-- Definition 2.2 of m4.tex: a valuation is a state when it respects the
-- connectives (S1) and satisfies  □ A in v  implies  A in v  (S2).
--
-- To these the formalisation adds a third clause, coherence on duplicates.
-- It has no counterpart in the note because there a state IS a function on the
-- set Sub(phi); here a valuation is a List Bool read positionally against a
-- list that repeats (LTL.Sub, subBenAri-dup).  The clause is exactly what makes
-- the vector represent a function on the set, so isState is the faithful
-- encoding of Definition 2.2 rather than a strengthening of it.

module LTL.State where

open import LTL.Val public

------------------------------------------------------------------------
-- Lookup by first occurrence.
--
-- valOf P v A is the bit v assigns to A, read at the FIRST position of sub P
-- carrying A.  Under coherence this agrees with the bit at every position
-- carrying A, which is what lets chi (built positionally) and the conditions
-- below (built by lookup) be about the same thing.

module _ (P : Formula) where

  valOf : Val -> Formula -> Bool
  valOf v A = bitAt v (indexOf (sub P) A)

  ------------------------------------------------------------------------
  -- (S1) and (S2), imposed at each member of sub P.
  --
  -- var and ○ carry no local condition: the behaviour of ○ lives entirely in
  -- the transition relation (LTL.Step), which is the point of Remark 2.1.

  okAt : Val -> Formula -> Bool
  okAt v (var n) = true
  okAt v (¬ A)   = valOf v (¬ A) ⇔ᵇ ¬ᵇ valOf v A
  okAt v (A ⇒ B) = valOf v (A ⇒ B) ⇔ᵇ valOf v A ⇒ᵇ valOf v B
  okAt v (○ A)   = true
  okAt v (□ A)   = valOf v (□ A) ⇒ᵇ valOf v A

  allOk : Val -> List Formula -> Bool
  allOk v = all (okAt v)

  ------------------------------------------------------------------------
  -- Coherence on duplicates.
  --
  -- Stated as "every position agrees with the first occurrence of its formula",
  -- which is linear rather than quadratic and equivalent by transitivity
  -- through that first occurrence.

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

  ------------------------------------------------------------------------
  -- Searching allCoh

  allCoh-at : (v : Val) (n i : Nat) -> i < n
           -> allCoh v n ≡ true -> cohAt v i ≡ true
  allCoh-at v zero    i ()  e
  allCoh-at v (suc n) i lt  e =
    sumElim (λ eq -> subst (λ k -> cohAt v k ≡ true) (sym eq)
                           (andTrueL (cohAt v n) (allCoh v n) e))
            (λ l  -> allCoh-at v n i l (andTrueR (cohAt v n) (allCoh v n) e))
            (ltSucCase i n lt)

  allCoh-false : (v : Val) (n : Nat)
              -> allCoh v n ≡ false
              -> Σ[ i ∈ Nat ] i < n × cohAt v i ≡ false
  allCoh-false v zero    ()
  allCoh-false v (suc n) e =
    sumElim (λ e1 -> n , ltNSucN n , e1)
            (λ e2 -> shift (allCoh-false v n e2))
            (andFalse (cohAt v n) (allCoh v n) e)
    where
      shift : (Σ[ i ∈ Nat ] i < n × cohAt v i ≡ false)
           -> Σ[ i ∈ Nat ] i < suc n × cohAt v i ≡ false
      shift (i , l , q) = i , ltWeak l , q

------------------------------------------------------------------------
-- Computational checks.
--
-- ◇ p is  ¬ □ ¬ p , so sub is
--   [ ¬ □ ¬ p , □ ¬ p , ¬ p , p ]
-- with no duplicates.  The constraints are v0 = not v1, v1 implies v2,
-- v2 = not v3, leaving three states -- the same three as Example 1 of
-- lecture15.pdf, where Sub(Fp) = {Fp, p} and the excluded combination is
-- Fp false with p true.

◇P : Formula
◇P = ◇ (var zero)

St-◇P : length (St ◇P) ≡ 3
St-◇P = refl

-- The negation of Ben-Ari's formula, the input the decision procedure is
-- actually run on.  Here sub has length 7 with □ p and p each duplicated,
-- so 128 valuations are filtered to 6 states.

¬BenAri : Formula
¬BenAri = ¬ benAri

St-¬BenAri : length (allVecs (length (sub ¬BenAri))) ≡ 128
St-¬BenAri = refl

St-¬BenAri-count : length (St ¬BenAri) ≡ 6
St-¬BenAri-count = refl

-- The duplicate-incoherent valuation of LTL.Val is rejected, as intended.

badVal-rejected : isState benAri badVal ≡ false
badVal-rejected = refl

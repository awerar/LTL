{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.State -- G5 of FORMALISATION-PLAN.md.
--
-- Definition 2.2 of m4.tex: a valuation is a state when it respects the
-- connectives (S1) and satisfies  □ A in v  implies  A in v  (S2).
--
-- To these the formalisation adds a third clause, coherence on duplicates.
-- It has no counterpart in the note because there a state IS a function on the
-- set Sub(phi); here a valuation is a List Bool read positionally against a
-- list that repeats (LTL.Sub, subBenAri_dup).  The clause is exactly what makes
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

valOf : Formula -> Val -> Formula -> Bool
valOf P v A = bitAt v (indexOf (sub P) A)

------------------------------------------------------------------------
-- (S1) and (S2), imposed at each member of sub P.
--
-- var and nxt carry no local condition: the behaviour of nxt lives entirely in
-- the transition relation (LTL.Step), which is the point of Remark 2.1.

okAt : Formula -> Val -> Formula -> Bool
okAt P v (var n)   = true
okAt P v (¬ A)   = valOf P v (¬ A) ⇔ᵇ ¬ᵇ valOf P v A
okAt P v (A ⇒ B) = valOf P v (A ⇒ B) ⇔ᵇ valOf P v A ⇒ᵇ valOf P v B
okAt P v (○ A)   = true
okAt P v (□ A)   = valOf P v (□ A) ⇒ᵇ valOf P v A

allOk : Formula -> Val -> List Formula -> Bool
allOk P v []       = true
allOk P v (A ∷ As) = okAt P v A ∧ᵇ allOk P v As

------------------------------------------------------------------------
-- Coherence on duplicates.
--
-- Stated as "every position agrees with the first occurrence of its formula",
-- which is linear rather than quadratic and equivalent by transitivity through
-- that first occurrence.

cohAt : Formula -> Val -> Nat -> Bool
cohAt P v i = bitAt v i ⇔ᵇ valOf P v (nth (sub P) i ⊥)

allCoh : Formula -> Val -> Nat -> Bool
allCoh P v zero    = true
allCoh P v (suc n) = cohAt P v n ∧ᵇ allCoh P v n

------------------------------------------------------------------------
-- States

isState : Formula -> Val -> Bool
isState P v = allOk P v (sub P) ∧ᵇ
              allCoh P v (length (sub P))

St : Formula -> List Val
St P = filter (isState P) (allVecs (length (sub P)))

------------------------------------------------------------------------
-- Searching allOk

allOk_at : (P : Formula) (v : Val) (As : List Formula) {A : Formula}
        -> A ∈ As -> allOk P v As ≡ true -> okAt P v A ≡ true
allOk_at P v []       ()        e
allOk_at P v (B ∷ Bs) here      e = andTrueL (okAt P v B) (allOk P v Bs) e
allOk_at P v (B ∷ Bs) (there m) e =
  allOk_at P v Bs m (andTrueR (okAt P v B) (allOk P v Bs) e)

allOk_false : (P : Formula) (v : Val) (As : List Formula)
           -> allOk P v As ≡ false
           -> Σ[ A ∈ Formula ] A ∈ As × okAt P v A ≡ false
allOk_false P v []       ()
allOk_false P v (B ∷ Bs) e =
  sumElim (λ e1 -> B , here , e1)
          (λ e2 -> shift (allOk_false P v Bs e2))
          (andFalse (okAt P v B) (allOk P v Bs) e)
  where
    shift : (Σ[ A ∈ Formula ] A ∈ Bs × okAt P v A ≡ false)
         -> Σ[ A ∈ Formula ] A ∈ B ∷ Bs × okAt P v A ≡ false
    shift (A , m , q) = A , there m , q

------------------------------------------------------------------------
-- Searching allCoh

allCoh_at : (P : Formula) (v : Val) (n i : Nat) -> i < n
         -> allCoh P v n ≡ true -> cohAt P v i ≡ true
allCoh_at P v zero    i ()  e
allCoh_at P v (suc n) i lt  e =
  sumElim (λ eq -> subst (λ k -> cohAt P v k ≡ true) (sym eq)
                         (andTrueL (cohAt P v n) (allCoh P v n) e))
          (λ l  -> allCoh_at P v n i l (andTrueR (cohAt P v n) (allCoh P v n) e))
          (ltSucCase i n lt)

allCoh_false : (P : Formula) (v : Val) (n : Nat)
            -> allCoh P v n ≡ false
            -> Σ[ i ∈ Nat ] i < n × cohAt P v i ≡ false
allCoh_false P v zero    ()
allCoh_false P v (suc n) e =
  sumElim (λ e1 -> n , ltNSucN n , e1)
          (λ e2 -> shift (allCoh_false P v n e2))
          (andFalse (cohAt P v n) (allCoh P v n) e)
  where
    shift : (Σ[ i ∈ Nat ] i < n × cohAt P v i ≡ false)
         -> Σ[ i ∈ Nat ] i < suc n × cohAt P v i ≡ false
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

St_◇P : length (St ◇P) ≡ 3
St_◇P = refl

-- The negation of Ben-Ari's formula, the input the decision procedure is
-- actually run on.  Here sub has length 7 with □ p and p each duplicated,
-- so 128 valuations are filtered to 6 states.

¬BenAri : Formula
¬BenAri = ¬ benAri

St_¬BenAri : length (allVecs (length (sub ¬BenAri))) ≡ 128
St_¬BenAri = refl

St_¬BenAri_count : length (St ¬BenAri) ≡ 6
St_¬BenAri_count = refl

-- The duplicate-incoherent valuation of LTL.Val is rejected, as intended.

badVal_rejected : isState benAri badVal ≡ false
badVal_rejected = refl

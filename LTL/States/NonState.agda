{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.NonState -- a valuation that is not a state is refutable:
-- ⊢ ¬ (chi v).
--
-- Each violation is a contradiction among finitely many conjuncts of chi v.
-- Coherence is examined first: if it fails the refutation is positional; if it
-- holds, every later projection may be signed by valOf.

open import LTL.Syntax.Formula using (Formula)

module LTL.States.NonState (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Proj P

------------------------------------------------------------------------
-- Non-states are refutable

nonState : (v : Val)
        -> length v ≡ length (sub P)
        -> isState v ≡ false
        -> ⊢ ¬ (chi v)
nonState v len e0 = byCoh e0
  where
    C : Formula
    C = chi v

    ----------------------------------------------------------------
    -- Coherence fails at position i: the formula there occurs twice with
    -- opposite bits, so chi carries both X and ¬ X.

    cohFail : (i : Nat) -> i < length (sub P) -> cohAt v i ≡ false
           -> ⊢ ¬ C
    cohFail i lt cf =
      refuteLit (valOf v X)
                (chiProjVal v len m)
                (subst (λ b -> ⊢ C ⇒ (lit X b)) flip
                       (chiProjPos v len i lt))
      where
        X : Formula
        X = nth (sub P) i ⊥

        m : X ∈ sub P
        m = nth-mem (sub P) i lt ⊥

        flip : bitAt v i ≡ ¬ᵇ valOf v X
        flip = ⇔ᵇ-false (bitAt v i) (valOf v X) cf

    ----------------------------------------------------------------
    -- Coherence holds; now (S1) or (S2) fails at some member of sub P.

    -- The literal of A that chi v contains, read off by chiProj.
    prAt : allCoh v (length (sub P)) ≡ true
        -> {A : Formula} -> A ∈ sub P -> (c : Bool)
        -> valOf v A ≡ c -> ⊢ C ⇒ (lit A c)
    prAt ch h c eq = subst (λ d -> ⊢ C ⇒ (lit _ d)) eq (chiProj v len ch h)

    okFail : allCoh v (length (sub P)) ≡ true
          -> {A : Formula} -> A ∈ sub P -> okAt v A ≡ false
          -> ⊢ ¬ C
    okFail ch {var n}   m ()
    okFail ch {○ B}   m ()
    okFail ch {¬ B}   m e = refute¬ b (prAt ch (sub-¬ P m) b refl)
                                      (prAt ch m b eq¬B)
      where
        b : Bool
        b = valOf v B

        eq¬B : valOf v (¬ B) ≡ b
        eq¬B = trans (⇔ᵇ-false (valOf v (¬ B))
                                          (¬ᵇ valOf v B) e)
                         (¬ᵇ-involutive (valOf v B))

    okFail ch {B ⇒ D} m e = aux (valOf v B) (valOf v D) refl refl eqI
      where
        mB : B ∈ sub P
        mB = sub-⇒L P m

        mD : D ∈ sub P
        mD = sub-⇒R P m

        eqI : valOf v (B ⇒ D) ≡
              ¬ᵇ (valOf v B ⇒ᵇ valOf v D)
        eqI = ⇔ᵇ-false (valOf v (B ⇒ D))
                       (valOf v B ⇒ᵇ valOf v D) e

        aux : (bB bD : Bool) -> valOf v B ≡ bB -> valOf v D ≡ bD
           -> valOf v (B ⇒ D) ≡ ¬ᵇ (bB ⇒ᵇ bD)
           -> ⊢ ¬ C
        -- v D = 1 forces imp = 1, but v (B ⇒ D) = 0
        aux true  true  eB eD eI =
          refute (⇒Trans (prAt ch mD true eD) p1) (prAt ch m false eI)
        -- v B = 1, v D = 0, v (B ⇒ D) = 1 : modus ponens under chi
        aux true  false eB eD eI =
          refute (mpU (prAt ch m true eI) (prAt ch mB true eB)) (prAt ch mD false eD)
        -- v B = 0 forces imp = 1, but v (B ⇒ D) = 0
        aux false bD    eB eD eI =
          refute (⇒Trans (prAt ch mB false eB) ¬Elim) (prAt ch m false eI)

    okFail ch {□ B}   m e = refute (⇒Trans (prAt ch m true e□) □Elim)
                                   (prAt ch (sub-□ P m) false eB)
      where
        pr2 : valOf v (□ B) ≡ true × valOf v B ≡ false
        pr2 = ⇒ᵇ-false (valOf v (□ B)) (valOf v B) e

        e□ : valOf v (□ B) ≡ true
        e□ = fst pr2

        eB : valOf v B ≡ false
        eB = snd pr2

    ----------------------------------------------------------------

    byCoh : isState v ≡ false -> ⊢ ¬ C
    byCoh e with allCoh v (length (sub P)) in ce
    ... | false =
      sigElim (allCoh-false v (length (sub P)) ce)
      where
        sigElim : (Σ[ i ∈ Nat ] i < length (sub P) ×
                                    cohAt v i ≡ false)
               -> ⊢ ¬ C
        sigElim (i , lt , cf) = cohFail i lt cf
    -- here e says  allOk v (sub P) ∧ᵇ true ≡ false
    ... | true  =
      sumElim (λ ef -> sigElim (all-false (okAt v) (sub P) ef))
              (λ bad -> emptyElim (true≢false bad))
              (∧ᵇ-false (allOk v (sub P)) true e)
      where
        sigElim : (∃[ A ∈ sub P ] okAt v A ≡ false)
               -> ⊢ ¬ C
        sigElim (A , m , q) = okFail ce m q

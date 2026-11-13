{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.NonState -- G16 of FORMALISATION-PLAN.md, Lemma 2.5 of m4.tex.
--
-- A valuation that is not a state is refutable.  Each violation is a
-- contradiction among finitely many conjuncts of chi P v, and each is a fixed
-- shape; nothing here needs a tautology checker.
--
-- Order of business matters: coherence is examined FIRST.  If it fails we
-- refute positionally, which is the one case where cohLookup is unavailable.
-- If it holds, isState reduces to allOk, and every later projection may be
-- signed by valOf.

module LTL.NonState where

open import LTL.Proj public

------------------------------------------------------------------------
-- Two ways of closing a refutation

refuteLit : {C X : Formula} (b : Bool)
         -> ⊢ C ⇒ (lit X b) -> ⊢ C ⇒ (lit X (¬ᵇ b))
         -> ⊢ ¬ C
refuteLit true  f g = refute f g
refuteLit false f g = refute g f

refute¬ : {C B : Formula} (b : Bool)
       -> ⊢ C ⇒ (lit B b) -> ⊢ C ⇒ (lit (¬ B) b)
       -> ⊢ ¬ C
refute¬ true  f g = refute f g
refute¬ false f g = refute f g

------------------------------------------------------------------------
-- Lemma 2.5

nonState : (P : Formula) (v : Val)
        -> length v ≡ length (sub P)
        -> isState P v ≡ false
        -> ⊢ ¬ (chi P v)
nonState P v len e0 = onCoh (allCoh P v (length (sub P))) refl e0
  where
    C : Formula
    C = chi P v

    ----------------------------------------------------------------
    -- Coherence fails at position i: the formula there occurs twice with
    -- opposite bits, so chi carries both X and ¬ X.

    cohFail : (i : Nat) -> i < length (sub P) -> cohAt P v i ≡ false
           -> ⊢ ¬ C
    cohFail i lt cf =
      refuteLit (valOf P v X)
                (chiProjVal P v len m)
                (subst (λ b -> ⊢ C ⇒ (lit X b)) flip
                       (chiProjPos P v len i lt))
      where
        X : Formula
        X = nth (sub P) i ⊥

        m : X ∈ sub P
        m = nth-mem (sub P) i lt ⊥

        flip : bitAt v i ≡ ¬ᵇ valOf P v X
        flip = ⇔ᵇ-false (bitAt v i) (valOf P v X) cf

    ----------------------------------------------------------------
    -- Coherence holds; now (S1) or (S2) fails at some member of sub P.

    -- The literal of A that chi P v contains, read off by chiProj.
    prAt : allCoh P v (length (sub P)) ≡ true
        -> {A : Formula} -> A ∈ sub P -> (c : Bool)
        -> valOf P v A ≡ c -> ⊢ C ⇒ (lit A c)
    prAt ch h c eq = subst (λ d -> ⊢ C ⇒ (lit _ d)) eq (chiProj P v len ch h)

    okFail : allCoh P v (length (sub P)) ≡ true
          -> {A : Formula} -> A ∈ sub P -> okAt P v A ≡ false
          -> ⊢ ¬ C
    okFail ch {var n}   m ()
    okFail ch {○ B}   m ()
    okFail ch {¬ B}   m e = refute¬ b (prAt ch (sub-¬ P m) b refl)
                                      (prAt ch m b eq¬B)
      where
        b : Bool
        b = valOf P v B

        eq¬B : valOf P v (¬ B) ≡ b
        eq¬B = trans (⇔ᵇ-false (valOf P v (¬ B))
                                          (¬ᵇ valOf P v B) e)
                         (¬ᵇ-involutive (valOf P v B))

    okFail ch {B ⇒ D} m e = aux (valOf P v B) (valOf P v D) refl refl eqI
      where
        mB : B ∈ sub P
        mB = sub-⇒L P m

        mD : D ∈ sub P
        mD = sub-⇒R P m

        eqI : valOf P v (B ⇒ D) ≡
              ¬ᵇ (valOf P v B ⇒ᵇ valOf P v D)
        eqI = ⇔ᵇ-false (valOf P v (B ⇒ D))
                       (valOf P v B ⇒ᵇ valOf P v D) e

        aux : (bB bD : Bool) -> valOf P v B ≡ bB -> valOf P v D ≡ bD
           -> valOf P v (B ⇒ D) ≡ ¬ᵇ (bB ⇒ᵇ bD)
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
        pr2 : valOf P v (□ B) ≡ true × valOf P v B ≡ false
        pr2 = ⇒ᵇ-false (valOf P v (□ B)) (valOf P v B) e

        e□ : valOf P v (□ B) ≡ true
        e□ = fst pr2

        eB : valOf P v B ≡ false
        eB = snd pr2

    ----------------------------------------------------------------

    onCoh : (c : Bool) -> allCoh P v (length (sub P)) ≡ c
         -> isState P v ≡ false -> ⊢ ¬ C
    onCoh false ce e =
      sigElim (allCoh-false P v (length (sub P)) ce)
      where
        sigElim : (Σ[ i ∈ Nat ] i < length (sub P) ×
                                    cohAt P v i ≡ false)
               -> ⊢ ¬ C
        sigElim (i , lt , cf) = cohFail i lt cf
    onCoh true  ce e =
      sumElim (λ ef -> sigElim (allOk-false P v (sub P) ef))
              (λ bad -> emptyElim (true≢false (trans (sym ce) bad)))
              (andFalse (allOk P v (sub P)) (allCoh P v (length (sub P))) e)
      where
        sigElim : (Σ[ A ∈ Formula ] A ∈ sub P ×
                                        okAt P v A ≡ false)
               -> ⊢ ¬ C
        sigElim (A , m , q) = okFail ce m q

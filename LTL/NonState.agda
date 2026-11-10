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
         -> Deriv (C ⇒ (lit X b)) -> Deriv (C ⇒ (lit X (boolNot b)))
         -> Deriv (¬ C)
refuteLit true  f g = refute f g
refuteLit false f g = refute g f

refute¬ : {C B : Formula} (b : Bool)
         -> Deriv (C ⇒ (lit B b)) -> Deriv (C ⇒ (lit (¬ B) b))
         -> Deriv (¬ C)
refute¬ true  f g = refute f g
refute¬ false f g = refute f g

------------------------------------------------------------------------
-- Lemma 2.5

nonState : (P : Formula) (v : Val)
        -> Eq (length v) (length (sub P))
        -> Eq (isState P v) false
        -> Deriv (¬ (chi P v))
nonState P v len e0 = onCoh (allCoh P v (length (sub P))) refl e0
  where
    C : Formula
    C = chi P v

    ----------------------------------------------------------------
    -- Coherence fails at position i: the formula there occurs twice with
    -- opposite bits, so chi carries both X and ¬ X.

    cohFail : (i : Nat) -> Lt i (length (sub P)) -> Eq (cohAt P v i) false
           -> Deriv (¬ C)
    cohFail i lt cf =
      refuteLit (valOf P v X)
                (chiProjVal P v len m)
                (eqSubst (\ b -> Deriv (C ⇒ (lit X b))) flip
                         (chiProjPos P v len i lt))
      where
        X : Formula
        X = nth (sub P) i ⊥

        m : Mem X (sub P)
        m = nth_mem (sub P) i lt ⊥

        flip : Eq (bitAt v i) (boolNot (valOf P v X))
        flip = boolEq_false_eq (bitAt v i) (valOf P v X) cf

    ----------------------------------------------------------------
    -- Coherence holds; now (S1) or (S2) fails at some member of sub P.

    okFail : Eq (allCoh P v (length (sub P))) true
          -> {A : Formula} -> Mem A (sub P) -> Eq (okAt P v A) false
          -> Deriv (¬ C)
    okFail ch {var n}   m ()
    okFail ch {○ B}   m ()
    okFail ch {¬ B}   m e = refute¬ b (prAt (sub_¬ P m) b refl)
                                          (prAt m b eq¬B)
      where
        prAt : {A : Formula} -> Mem A (sub P) -> (c : Bool)
            -> Eq (valOf P v A) c -> Deriv (C ⇒ (lit A c))
        prAt h c eq = eqSubst (\ d -> Deriv (C ⇒ (lit _ d))) eq
                              (chiProj P v len ch h)

        b : Bool
        b = valOf P v B

        eq¬B : Eq (valOf P v (¬ B)) b
        eq¬B = eqTrans (boolEq_false_eq (valOf P v (¬ B))
                                          (boolNot (valOf P v B)) e)
                         (boolNot_not (valOf P v B))

    okFail ch {B ⇒ D} m e = aux (valOf P v B) (valOf P v D) refl refl eqI
      where
        prAt : {A : Formula} -> Mem A (sub P) -> (c : Bool)
            -> Eq (valOf P v A) c -> Deriv (C ⇒ (lit A c))
        prAt h c eq = eqSubst (\ d -> Deriv (C ⇒ (lit _ d))) eq
                              (chiProj P v len ch h)

        mB : Mem B (sub P)
        mB = sub_⇒L P m

        mD : Mem D (sub P)
        mD = sub_⇒R P m

        eqI : Eq (valOf P v (B ⇒ D))
                 (boolNot (boolImp (valOf P v B) (valOf P v D)))
        eqI = boolEq_false_eq (valOf P v (B ⇒ D))
                              (boolImp (valOf P v B) (valOf P v D)) e

        aux : (bB bD : Bool) -> Eq (valOf P v B) bB -> Eq (valOf P v D) bD
           -> Eq (valOf P v (B ⇒ D)) (boolNot (boolImp bB bD))
           -> Deriv (¬ C)
        -- v D = 1 forces imp = 1, but v (B ⇒ D) = 0
        aux true  true  eB eD eI =
          refute (⇒Trans (prAt mD true eD) p1) (prAt m false eI)
        -- v B = 1, v D = 0, v (B ⇒ D) = 1 : modus ponens under chi
        aux true  false eB eD eI =
          refute (mpU (prAt m true eI) (prAt mB true eB)) (prAt mD false eD)
        -- v B = 0 forces imp = 1, but v (B ⇒ D) = 0
        aux false bD    eB eD eI =
          refute (⇒Trans (prAt mB false eB) ¬Elim) (prAt m false eI)

    okFail ch {□ B}   m e = refute (⇒Trans (prAt m true e□) □Elim)
                                     (prAt (sub_□ P m) false eB)
      where
        prAt : {A : Formula} -> Mem A (sub P) -> (c : Bool)
            -> Eq (valOf P v A) c -> Deriv (C ⇒ (lit A c))
        prAt h c eq = eqSubst (\ d -> Deriv (C ⇒ (lit _ d))) eq
                              (chiProj P v len ch h)

        pr2 : Prod (Eq (valOf P v (□ B)) true) (Eq (valOf P v B) false)
        pr2 = boolImp_false (valOf P v (□ B)) (valOf P v B) e

        e□ : Eq (valOf P v (□ B)) true
        e□ = prodFst pr2

        eB : Eq (valOf P v B) false
        eB = prodSnd pr2

    ----------------------------------------------------------------

    onCoh : (c : Bool) -> Eq (allCoh P v (length (sub P))) c
         -> Eq (isState P v) false -> Deriv (¬ C)
    onCoh false ce e =
      sigElim (allCoh_false P v (length (sub P)) ce)
      where
        sigElim : Sigma Nat (\ i -> Prod (Lt i (length (sub P)))
                                         (Eq (cohAt P v i) false))
               -> Deriv (¬ C)
        sigElim (sig i (prod lt cf)) = cohFail i lt cf
    onCoh true  ce e =
      sumElim (\ ef -> sigElim (allOk_false P v (sub P) ef))
              (\ bad -> emptyElim (tfAbs (eqTrans (eqSym ce) bad)))
              (andFalse (allOk P v (sub P)) (allCoh P v (length (sub P))) e)
      where
        sigElim : Sigma Formula (\ A -> Prod (Mem A (sub P))
                                             (Eq (okAt P v A) false))
               -> Deriv (¬ C)
        sigElim (sig A (prod m q)) = okFail ce m q

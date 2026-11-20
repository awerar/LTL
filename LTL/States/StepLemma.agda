{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.StepLemma -- the step lemma:
--
--   stepLemma : ⊢ (chi v) ⇒ ○ (beta (succs St v))
--
-- State completeness and (D1) give ⊢ ○ (beta St), hence a disjunction of
-- ○ chi_w by (D4); the w that are not successors of v are refuted and
-- dropped; (D4) carries the rest back under a single ○.  The refutations use
-- the conjunction  (chi v) ∧ ○ (chi w)  as antecedent, so every case sits
-- at one level where ∧Fst and ∧Snd give both halves.

open import LTL.Syntax.Formula using (Formula)

module LTL.States.StepLemma (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Step P
open import LTL.States.Proj P
open import LTL.States.Complete P

------------------------------------------------------------------------
-- Refuting a non-successor

notSucc : (v w : Val)
       -> length v ≡ length (sub P)
       -> length w ≡ length (sub P)
       -> step v w ≡ false
       -> ⊢ ¬ ((chi v) ∧ ○ (chi w))
notSucc v w lenv lenw e = sigElim (all-false (stepAt v w) (sub P) e)
  where
    R : Formula
    R = (chi v) ∧ ○ (chi w)

    pv : {A : Formula} -> A ∈ sub P -> ⊢ R ⇒ (lit A (valOf v A))
    pv m = ⇒Trans ∧Fst (chiProjVal v lenv m)

    pw : {A : Formula} -> A ∈ sub P -> ⊢ R ⇒ ○ (lit A (valOf w A))
    pw m = ⇒Trans ∧Snd (○Mono (chiProjVal w lenw m))

    pvAt : {A : Formula} -> A ∈ sub P -> (c : Bool) -> valOf v A ≡ c
        -> ⊢ R ⇒ (lit A c)
    pvAt m c eq = subst (λ d -> ⊢ R ⇒ (lit _ d)) eq (pv m)

    pwAt : {A : Formula} -> A ∈ sub P -> (c : Bool) -> valOf w A ≡ c
        -> ⊢ R ⇒ ○ (lit A c)
    pwAt m c eq = subst (λ d -> ⊢ R ⇒ ○ (lit _ d)) eq (pw m)

    ----------------------------------------------------------------
    -- (T1)

    case○ : {B : Formula} -> ○ B ∈ sub P
         -> valOf v (○ B) ⇔ᵇ valOf w B ≡ false
         -> ⊢ ¬ R
    case○ {B} m q =
      refute○ (valOf w B)
                (pvAt m (¬ᵇ valOf w B)
                      (⇔ᵇ-false (valOf v (○ B)) (valOf w B) q))
                (pwAt (sub-○ P m) (valOf w B) refl)

    ----------------------------------------------------------------
    -- (T2) and (T3)

    case□ : {B : Formula} -> □ B ∈ sub P
         -> (valOf v (□ B) ⇒ᵇ valOf w (□ B)) ∧ᵇ
            (¬ᵇ valOf v (□ B) ∧ᵇ valOf v B ⇒ᵇ ¬ᵇ valOf w (□ B)) ≡ false
         -> ⊢ ¬ R
    case□ {B} m q = sumElim t2 t3 (∧ᵇ-false _ _ q)
      where
        -- (T2): □ B holds at v, so it must hold at w; it does not.
        t2 : valOf v (□ B) ⇒ᵇ valOf w (□ B) ≡ false
          -> ⊢ ¬ R
        t2 q2 = refute (⇒Trans (pvAt m true (fst pr)) □○□)
                       (⇒Trans (pwAt m false (snd pr)) linFwd)
          where
            pr : valOf v (□ B) ≡ true × valOf w (□ B) ≡ false
            pr = ⇒ᵇ-false (valOf v (□ B)) (valOf w (□ B)) q2

        -- (T3): □ B fails at v while B holds, so □ B must fail at w;
        -- it holds, and (D6) turns B with ○ □ B back into □ B.
        t3 : ¬ᵇ valOf v (□ B) ∧ᵇ valOf v B ⇒ᵇ ¬ᵇ valOf w (□ B) ≡ false
          -> ⊢ ¬ R
        t3 q3 = refute (⇒Trans (∧Pair (pvAt (sub-□ P m) true eB)
                                          (pwAt m true eW))
                                 expConv)
                       (pvAt m false eV)
          where
            pr : ¬ᵇ valOf v (□ B) ∧ᵇ valOf v B ≡ true ×
                 ¬ᵇ valOf w (□ B) ≡ false
            pr = ⇒ᵇ-false _ _ q3

            eV : valOf v (□ B) ≡ false
            eV = ¬ᵇ-true (valOf v (□ B))
                         (∧ᵇ-trueˡ (¬ᵇ valOf v (□ B)) (valOf v B)
                                   (fst pr))

            eB : valOf v B ≡ true
            eB = ∧ᵇ-trueʳ (¬ᵇ valOf v (□ B)) (valOf v B) (fst pr)

            eW : valOf w (□ B) ≡ true
            eW = ¬ᵇ-false (valOf w (□ B)) (snd pr)

    ----------------------------------------------------------------

    byShape : {A : Formula} -> A ∈ sub P -> stepAt v w A ≡ false
           -> ⊢ ¬ R
    byShape {var n}   m ()
    byShape {¬ B}   m ()
    byShape {B ⇒ D} m ()
    byShape {○ B}   m q = case○ m q
    byShape {□ B}   m q = case□ m q

    sigElim : (∃[ A ∈ sub P ] stepAt v w A ≡ false)
           -> ⊢ ¬ R
    sigElim (A , m , q) = byShape m q

badSucc : (v w : Val)
       -> length v ≡ length (sub P)
       -> length w ≡ length (sub P)
       -> step v w ≡ false
       -> ⊢ (chi v) ⇒ ¬ ○ (chi w)
badSucc v w lenv lenw e = mp dne (notSucc v w lenv lenw e)

------------------------------------------------------------------------
-- Dropping the non-successors under the antecedent chi v

filter⇒ : (v : Val) (Q : Formula) (ws : List Val)
       -> (∀[ w ∈ ws ] length w ≡ length (sub P))
       -> ((w : Val) -> length w ≡ length (sub P) -> step v w ≡ false
             -> ⊢ Q ⇒ ¬ ○ (chi w))
       -> ⊢ Q ⇒ ⋁ (map ○_ (map chi ws))
                ⇒ ⋁ (map ○_ (map chi
                         (filter (step v) ws)))
filter⇒ v Q []       len bad = liftP ⇒Refl
filter⇒ v Q (w ∷ ws) len bad with step v w in e
-- kept: compose under the same antecedent ¬ ○ (chi w)
... | true  =
  mpU (liftP p2) (⇒Trans (filter⇒ v Q ws (λ u m -> len u (there m)) bad) p1)
-- dropped: ¬ ○ (chi w) is available, so that antecedent can be discharged
... | false =
  ⇒TransU (⇒Trans (bad w (len w here) e) (⇒Swap ⇒Refl))
          (filter⇒ v Q ws (λ u m -> len u (there m)) bad)

------------------------------------------------------------------------
-- The step lemma

stepLemma : (v : Val)
         -> length v ≡ length (sub P)
         -> ⊢ (chi v) ⇒ ○ (beta (succs St v))
stepLemma v lenv =
  ⇒Trans (mpU (filter⇒ v (chi v) St (λ w m -> stLen m) bad) start)
           (○⋁L2 (map chi (succs St v)))
  where
    bad : (w : Val) -> length w ≡ length (sub P) -> step v w ≡ false
       -> ⊢ (chi v) ⇒ ¬ ○ (chi w)
    bad w lenw e = badSucc v w lenv lenw e

    start : ⊢ (chi v) ⇒ ⋁ (map ○_ (map chi St))
    start = liftP (mp (○⋁L1 (map chi St))
                      (○Gen stateComplete))

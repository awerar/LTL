{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.StepLemma -- the step lemma:
--
--   stepLemma : ⊢ (chi v) ⇒ ○ (beta (succs St v))
--
-- State completeness and (D1) give ⊢ ○ (beta St), hence a disjunction of
-- ○ chi_w by (D4); the w that are not successors of v are refuted and
-- dropped; (D4) carries the rest back under a single ○.  The refutations use
-- the conjunction  (chi v) ∧ ○ (chi w)  as antecedent, so every case sits
-- at one level where ∧Fst and ∧Snd give both halves.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.StepLemma (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.CompletePC P

------------------------------------------------------------------------
-- Projection of a conjunct out of chi.  Every refutation of a state goes
-- through it: a Boolean condition fails, so chi carries two contradictory
-- literals.

chiProj : (v : Val) -> ∀ⁱ[ A ∈ sub P ] ⊢ (chi v) ⇒ (litOf v A)
chiProj v m = ⋀Proj (map (litOf v) subformulas) (∈-map⁺ (litOf v) (nub-mem (sub P) m))

------------------------------------------------------------------------
-- Refuting a non-successor

notSucc : (v w : Val)
       -> step v w ≡ false
       -> ⊢ ¬ ((chi v) ∧ ○ (chi w))
notSucc v w e = byCondition (stepFails v w e)
  where
    R : Formula
    R = (chi v) ∧ ○ (chi w)

    pv : ∀ⁱ[ A ∈ sub P ] ⊢ R ⇒ (lit A (valOf v A))
    pv m = ⇒Trans ∧Fst (chiProj v m)

    pw : ∀ⁱ[ A ∈ sub P ] ⊢ R ⇒ ○ (lit A (valOf w A))
    pw m = ⇒Trans ∧Snd (○Mono (chiProj w m))

    pvAt : {A : Formula} -> A ∈ sub P -> (c : Bool) -> valOf v A ≡ c
        -> ⊢ R ⇒ (lit A c)
    pvAt m c eq = subst (λ d -> ⊢ R ⇒ (lit _ d)) eq (pv m)

    pwAt : {A : Formula} -> A ∈ sub P -> (c : Bool) -> valOf w A ≡ c
        -> ⊢ R ⇒ ○ (lit A c)
    pwAt m c eq = subst (λ d -> ⊢ R ⇒ ○ (lit _ d)) eq (pw m)

    ----------------------------------------------------------------
    -- (T1): ○ B at v disagrees with B at w.

    case○ : {B : Formula} -> ○ B ∈ sub P -> t1At v w B ≡ false -> ⊢ ¬ R
    case○ {B} m q =
      refute○ (valOf w B)
                (pvAt m (¬ᵇ valOf w B)
                      (⇔ᵇ-false (valOf v (○ B)) (valOf w B) q))
                (pwAt (sub-○ P m) (valOf w B) refl)

    ----------------------------------------------------------------
    -- (T2): □ B holds at v, so it must hold at w; it does not.

    case□T2 : {B : Formula} -> □ B ∈ sub P -> t2At v w B ≡ false -> ⊢ ¬ R
    case□T2 {B} m q = refute (⇒Trans (pvAt m true (fst pr)) □○□)
                              (⇒Trans (pwAt m false (snd pr)) linFwd)
      where
        pr : valOf v (□ B) ≡ true × valOf w (□ B) ≡ false
        pr = ⇒ᵇ-false (valOf v (□ B)) (valOf w (□ B)) q

    ----------------------------------------------------------------
    -- (T3): □ B fails at v while B holds, so □ B must fail at w; it holds,
    -- and (D6) turns B with ○ □ B back into □ B.

    case□T3 : {B : Formula} -> □ B ∈ sub P -> t3At v w B ≡ false -> ⊢ ¬ R
    case□T3 {B} m q = refute (⇒Trans (∧Pair (pvAt (sub-□ P m) true eB)
                                              (pwAt m true eW))
                                       expConv)
                              (pvAt m false eV)
      where
        pr : ¬ᵇ valOf v (□ B) ∧ᵇ valOf v B ≡ true ×
             ¬ᵇ valOf w (□ B) ≡ false
        pr = ⇒ᵇ-false (¬ᵇ valOf v (□ B) ∧ᵇ valOf v B) (¬ᵇ valOf w (□ B)) q

        eV : valOf v (□ B) ≡ false
        eV = ¬ᵇ-true (valOf v (□ B))
                     (∧ᵇ-trueˡ (¬ᵇ valOf v (□ B)) (valOf v B) (fst pr))

        eB : valOf v B ≡ true
        eB = ∧ᵇ-trueʳ (¬ᵇ valOf v (□ B)) (valOf v B) (fst pr)

        eW : valOf w (□ B) ≡ true
        eW = ¬ᵇ-false (valOf w (□ B)) (snd pr)

    ----------------------------------------------------------------

    byCondition : StepFails v w -> ⊢ ¬ R
    byCondition (failsT1 B m q) = case○ (nextSub m) q
    byCondition (failsT2 A m q) = case□T2 (evSub m) q
    byCondition (failsT3 A m q) = case□T3 (evSub m) q

badSucc : (v w : Val)
       -> step v w ≡ false
       -> ⊢ (chi v) ⇒ ¬ ○ (chi w)
badSucc v w e = mp dne (notSucc v w e)

------------------------------------------------------------------------
-- Dropping the non-successors under the antecedent chi v

filter⇒ : (v : Val) (Q : Formula) (ws : List Val)
       -> ((w : Val) -> step v w ≡ false -> ⊢ Q ⇒ ¬ ○ (chi w))
       -> ⊢ Q ⇒ ⋁ (map ○_ (map chi ws))
                ⇒ ⋁ (map ○_ (map chi
                         (filter (step v) ws)))
filter⇒ v Q []       bad = liftP ⇒Refl
filter⇒ v Q (w ∷ ws) bad with step v w in e
-- kept: compose under the same antecedent ¬ ○ (chi w)
... | true  =
  mpU (liftP p2) (⇒Trans (filter⇒ v Q ws bad) p1)
-- dropped: ¬ ○ (chi w) is available, so that antecedent can be discharged
... | false =
  ⇒TransU (⇒Trans (bad w e) (⇒Swap ⇒Refl))
          (filter⇒ v Q ws bad)

------------------------------------------------------------------------
-- The step lemma

stepLemma : (v : Val) -> ⊢ (chi v) ⇒ ○ (beta (succs St v))
stepLemma v =
  ⇒Trans (mpU (filter⇒ v (chi v) St (badSucc v)) start)
           (○⋁L2 (map chi (succs St v)))
  where

    start : ⊢ (chi v) ⇒ ⋁ (map ○_ (map chi St))
    start = liftP (mp (○⋁L1 (map chi St))
                      (○Gen stateCompletePC))

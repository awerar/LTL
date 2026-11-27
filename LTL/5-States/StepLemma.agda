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
open import LTL.5-States.Valuation P
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.CompletePC P
open import LTL.5-States.Taut using (tautProj)

------------------------------------------------------------------------
-- The literal of any subformula, out of chi.  Every refutation of a state
-- goes through it: a Boolean condition fails, so chi implies two
-- contradictory literals.  chi has a literal per atom only, so this is one
-- pc node (tautProj) rather than a projection.

chiProj : (v : Val) -> ∀ⁱ[ A ∈ sub P ] ⊢ (chi v) ⇒ (litOf v A)
chiProj v m = pcTaut (tautProj P v m)

------------------------------------------------------------------------
-- Refuting a non-successor

notSucc : (v w : Val)
       -> step v w ≡ false
       -> ⊢ ¬ ((chi v) ∧ ○ (chi w))
notSucc v w e = byCondition (stepFails v w e)
  where
    R : Formula
    R = (chi v) ∧ ○ (chi w)

    pv : ∀ⁱ[ A ∈ sub P ] ⊢ R ⇒ (lit A (holdsIn v A))
    pv m = ⇒Trans ∧Fst (chiProj v m)

    pw : ∀ⁱ[ A ∈ sub P ] ⊢ R ⇒ ○ (lit A (holdsIn w A))
    pw m = ⇒Trans ∧Snd (○Mono (chiProj w m))

    pvAt : {A : Formula} -> A ∈ sub P -> (c : Bool) -> holdsIn v A ≡ c
        -> ⊢ R ⇒ (lit A c)
    pvAt m c eq = subst (λ d -> ⊢ R ⇒ (lit _ d)) eq (pv m)

    pwAt : {A : Formula} -> A ∈ sub P -> (c : Bool) -> holdsIn w A ≡ c
        -> ⊢ R ⇒ ○ (lit A c)
    pwAt m c eq = subst (λ d -> ⊢ R ⇒ ○ (lit _ d)) eq (pw m)

    ----------------------------------------------------------------
    -- (T1): ○ B at v disagrees with B at w.

    case○ : {B : Formula} -> ○ B ∈ sub P -> t1At v w B ≡ false -> ⊢ ¬ R
    case○ {B} m q =
      refute○ (holdsIn w B)
                (pvAt m (¬ᵇ holdsIn w B)
                      (⇔ᵇ-false (holdsIn v (○ B)) (holdsIn w B) q))
                (pwAt (sub-○ P m) (holdsIn w B) refl)

    ----------------------------------------------------------------
    -- (T2): □ B holds at v, so it must hold at w; it does not.

    case□T2 : {B : Formula} -> □ B ∈ sub P -> t2At v w B ≡ false -> ⊢ ¬ R
    case□T2 {B} m q = refute (⇒Trans (pvAt m true (fst pr)) □○□)
                              (⇒Trans (pwAt m false (snd pr)) linFwd)
      where
        pr : holdsIn v (□ B) ≡ true × holdsIn w (□ B) ≡ false
        pr = ⇒ᵇ-false (holdsIn v (□ B)) (holdsIn w (□ B)) q

    ----------------------------------------------------------------
    -- (T3): □ B fails at v while B holds, so □ B must fail at w; it holds,
    -- and (D6) turns B with ○ □ B back into □ B.

    case□T3 : {B : Formula} -> □ B ∈ sub P -> t3At v w B ≡ false -> ⊢ ¬ R
    case□T3 {B} m q = refute (⇒Trans (∧Pair (pvAt (sub-□ P m) true eB)
                                              (pwAt m true eW))
                                       expConv)
                              (pvAt m false eV)
      where
        pr : ¬ᵇ holdsIn v (□ B) ∧ᵇ holdsIn v B ≡ true ×
             ¬ᵇ holdsIn w (□ B) ≡ false
        pr = ⇒ᵇ-false (¬ᵇ holdsIn v (□ B) ∧ᵇ holdsIn v B) (¬ᵇ holdsIn w (□ B)) q

        eV : holdsIn v (□ B) ≡ false
        eV = ¬ᵇ-true (holdsIn v (□ B))
                     (∧ᵇ-trueˡ (¬ᵇ holdsIn v (□ B)) (holdsIn v B) (fst pr))

        eB : holdsIn v B ≡ true
        eB = ∧ᵇ-trueʳ (¬ᵇ holdsIn v (□ B)) (holdsIn v B) (fst pr)

        eW : holdsIn w (□ B) ≡ true
        eW = ¬ᵇ-false (holdsIn w (□ B)) (snd pr)

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

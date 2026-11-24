{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Step -- the transition relation step v w:
--
--   (T1)  for ○ B in sub P:  ○ B in v  iff  B in w
--   (T2)  for □ A in sub P:  □ A in v  implies  □ A in w
--   (T3)  for □ A in sub P:  □ A not in v and A in v  implies  □ A not in w
--
-- (T2) and (T3) are the two halves of  □ A ⇔ A ∧ ○ □ A  with ○ □ A read as
-- "□ A at the successor"; (S2) is the remaining half.  Keeping them here lets
-- sub P stand in for a closure, and makes persistence hold by definition.
-- Each condition runs over its own list (nexts, eventualities), so a failed
-- step names the condition and formula that failed (StepFails).

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.Step (P : Formula) where

open import LTL.2-Syntax.Deriv
open import LTL.5-States.State P

------------------------------------------------------------------------
-- The three conditions, each imposed at its own list: (T1) at the arguments
-- of ○, (T2) and (T3) at the eventualities.

t1At : Val -> Val -> Formula -> Bool
t1At v w B = valOf v (○ B) ⇔ᵇ valOf w B

t2At : Val -> Val -> Formula -> Bool
t2At v w A = valOf v (□ A) ⇒ᵇ valOf w (□ A)

t3At : Val -> Val -> Formula -> Bool
t3At v w A = ¬ᵇ valOf v (□ A) ∧ᵇ valOf v A ⇒ᵇ ¬ᵇ valOf w (□ A)

t1All t2All t3All : Val -> Val -> Bool
t1All v w = all (t1At v w) nexts
t2All v w = all (t2At v w) eventualities
t3All v w = all (t3At v w) eventualities

step : Val -> Val -> Bool
step v w = t1All v w ∧ᵇ t2All v w ∧ᵇ t3All v w

-- Reading each condition off a step, at a member of sub P.

rest23 : (v w : Val) -> step v w ≡ true -> t2All v w ∧ᵇ t3All v w ≡ true
rest23 v w st = snd (∧ᵇ-split (t1All v w) (t2All v w ∧ᵇ t3All v w) st)

stepT1 : (v w : Val) {B : Formula} -> step v w ≡ true -> ○ B ∈ sub P
      -> t1At v w B ≡ true
stepT1 v w {B} st m =
  all-true (t1At v w) nexts
           (fst (∧ᵇ-split (t1All v w) (t2All v w ∧ᵇ t3All v w) st)) B (nextIn m)

stepT2 : (v w : Val) {A : Formula} -> step v w ≡ true -> □ A ∈ sub P
      -> t2At v w A ≡ true
stepT2 v w {A} st m =
  all-true (t2At v w) eventualities
           (fst (∧ᵇ-split (t2All v w) (t3All v w) (rest23 v w st))) A (evIn m)

stepT3 : (v w : Val) {A : Formula} -> step v w ≡ true -> □ A ∈ sub P
      -> t3At v w A ≡ true
stepT3 v w {A} st m =
  all-true (t3At v w) eventualities
           (snd (∧ᵇ-split (t2All v w) (t3All v w) (rest23 v w st))) A (evIn m)

-- A failed step fails one condition at one formula.

data StepFails (v w : Val) : Set where
  failsT1 : (B : Formula) -> B ∈ nexts         -> t1At v w B ≡ false -> StepFails v w
  failsT2 : (A : Formula) -> A ∈ eventualities -> t2At v w A ≡ false -> StepFails v w
  failsT3 : (A : Formula) -> A ∈ eventualities -> t3At v w A ≡ false -> StepFails v w

stepFails : (v w : Val) -> step v w ≡ false -> StepFails v w
stepFails v w e =
  [ (λ e1 -> fromT1 (all-false (t1At v w) nexts e1))
  , (λ e23 -> [ (λ e2 -> fromT2 (all-false (t2At v w) eventualities e2))
              , (λ e3 -> fromT3 (all-false (t3At v w) eventualities e3))
              ] (∧ᵇ-false (t2All v w) (t3All v w) e23))
  ] (∧ᵇ-false (t1All v w) (t2All v w ∧ᵇ t3All v w) e)
  where
    fromT1 : (∃[ B ∈ nexts ] t1At v w B ≡ false) -> StepFails v w
    fromT1 (B , m , q) = failsT1 B m q

    fromT2 : (∃[ A ∈ eventualities ] t2At v w A ≡ false) -> StepFails v w
    fromT2 (A , m , q) = failsT2 A m q

    fromT3 : (∃[ A ∈ eventualities ] t3At v w A ≡ false) -> StepFails v w
    fromT3 (A , m , q) = failsT3 A m q

------------------------------------------------------------------------
-- Successors within a given set of states

succs : List Val -> Val -> List Val
succs us v = filter (step v) us

∈-succs⁻ : (us : List Val) (v : Val)
        -> ∀ⁱ[ w ∈ succs us v ] w ∈ us × step v w ≡ true
∈-succs⁻ us v m =
  ∈-filter⁻ (step v) us m , filter-prop (step v) us m

succsIn : (us : List Val) (v : Val) {w : Val}
       -> w ∈ us -> step v w ≡ true -> w ∈ succs us v
succsIn us v mw st = ∈-filter⁺ (step v) us mw st

------------------------------------------------------------------------
-- Persistence: a pending eventuality stays pending unless A fails.  It is
-- (T3), read off.

persist : (v w : Val) (A : Formula)
       -> □ A ∈ sub P
       -> step v w ≡ true
       -> valOf v (□ A) ≡ false
       -> valOf v A ≡ true
       -> valOf w (□ A) ≡ false
persist v w A h st bx a =
  ¬ᵇ-true (valOf w (□ A))
          (⇒ᵇ-mp (¬ᵇ valOf v (□ A) ∧ᵇ valOf v A) (¬ᵇ valOf w (□ A))
                 (stepT3 v w st h)
                 (∧ᵇ-intro (¬ᵇ valOf v (□ A)) (valOf v A) (cong ¬ᵇ_ bx) a))

------------------------------------------------------------------------
-- (T2), read off the same way.  The step lemma uses it to refute a
-- successor dropping a box, and Hintikka's lemma to carry  □ A  along a run.

carry : (v w : Val) (A : Formula)
     -> □ A ∈ sub P
     -> step v w ≡ true
     -> valOf v (□ A) ≡ true
     -> valOf w (□ A) ≡ true
carry v w A h st bx =
  ⇒ᵇ-mp (valOf v (□ A)) (valOf w (□ A)) (stepT2 v w st h) bx

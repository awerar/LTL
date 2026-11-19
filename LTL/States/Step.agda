{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Step -- the transition relation step P v w:
--
--   (T1)  for ○ B in sub P:  ○ B in v  iff  B in w
--   (T2)  for □ A in sub P:  □ A in v  implies  □ A in w
--   (T3)  for □ A in sub P:  □ A not in v and A in v  implies  □ A not in w
--
-- (T2) and (T3) are the two halves of  □ A ⇔ A ∧ ○ □ A  with ○ □ A read as
-- "□ A at the successor"; (S2) is the remaining half.  Keeping them here lets
-- sub P stand in for a closure, and makes persistence hold by definition.

module LTL.States.Step where

open import LTL.States.State public

------------------------------------------------------------------------
-- The three conditions, imposed at each member of sub P

module _ (P : Formula) where

  stepAt : Val -> Val -> Formula -> Bool
  stepAt v w (var n) = true
  stepAt v w (¬ A)   = true
  stepAt v w (A ⇒ B) = true
  stepAt v w (○ B)   = valOf P v (○ B) ⇔ᵇ valOf P w B
  stepAt v w (□ A)   =
    (valOf P v (□ A) ⇒ᵇ valOf P w (□ A)) ∧ᵇ
    (¬ᵇ valOf P v (□ A) ∧ᵇ valOf P v A ⇒ᵇ ¬ᵇ valOf P w (□ A))

  allStep : Val -> Val -> List Formula -> Bool
  allStep v w = all (stepAt v w)

  step : Val -> Val -> Bool
  step v w = allStep v w (sub P)

  ------------------------------------------------------------------------
  -- Successors within a given set of states

  succs : List Val -> Val -> List Val
  succs us v = filter (step v) us

  ------------------------------------------------------------------------
  -- Persistence: a pending eventuality stays pending unless A fails.  It is
  -- (T3), read off.

  persist : (v w : Val) (A : Formula)
         -> □ A ∈ sub P
         -> step v w ≡ true
         -> valOf P v (□ A) ≡ false
         -> valOf P v A ≡ true
         -> valOf P w (□ A) ≡ false
  persist v w A h st bx a =
    t3aux (valOf P v (□ A)) (valOf P v A) (valOf P w (□ A))
          (all-at (stepAt v w) (sub P) h st) bx a
    where
      -- x = □ A at v,  z = A at v,  y = □ A at w
      t3aux : (x z y : Bool)
           -> (x ⇒ᵇ y) ∧ᵇ (¬ᵇ x ∧ᵇ z ⇒ᵇ ¬ᵇ y) ≡ true
           -> x ≡ false -> z ≡ true -> y ≡ false
      t3aux true  z     y     e () c
      t3aux false false y     e b ()
      t3aux false true  false e b c = refl
      t3aux false true  true  () b c

  ------------------------------------------------------------------------
  -- (T2), read off the same way.  The step lemma uses it to refute a
  -- successor dropping a box, and Hintikka's lemma to carry  □ A  along a run.

  carry : (v w : Val) (A : Formula)
       -> □ A ∈ sub P
       -> step v w ≡ true
       -> valOf P v (□ A) ≡ true
       -> valOf P w (□ A) ≡ true
  carry v w A h st bx =
    t2aux (valOf P v (□ A)) (valOf P v A) (valOf P w (□ A))
          (all-at (stepAt v w) (sub P) h st) bx
    where
      t2aux : (x z y : Bool)
           -> (x ⇒ᵇ y) ∧ᵇ (¬ᵇ x ∧ᵇ z ⇒ᵇ ¬ᵇ y) ≡ true
           -> x ≡ true -> y ≡ true
      t2aux true  z true  e  b = refl
      t2aux true  z false () b
      t2aux false z y     e  ()

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Step -- G6 of FORMALISATION-PLAN.md.
--
-- Definition 2.3 of m4.tex, the transition relation:
--
--   (T1)  for ○ B in Sub(P):  ○ B in v  iff  B in w
--   (T2)  for □ A in Sub(P):  □ A in v  implies  □ A in w
--   (T3)  for □ A in Sub(P):  □ A not in v and A in v  implies
--                               □ A not in w
--
-- (T2) and (T3) are the two halves of  □ A ⇔ A ∧ ○ □ A  with
-- ○ □ A read as "□ A at the successor"; (S2) of LTL.State is the
-- remaining half.  Keeping them here rather than in the state condition is what
-- lets Sub replace a Fischer-Ladner closure (Remark 2.1), and it also makes
-- persistence (Lemma 2.8) true by definition rather than by proof.

module LTL.Step where

open import LTL.State public

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
  -- Persistence, Lemma 2.8 of m4.tex.
  --
  -- On paper this needs a line of proof; here it is (T3), read off.

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
  -- (T2), read off the same way.
  --
  -- The note uses it twice: in Lemma 2.7 to refute a successor dropping a box,
  -- and in Hintikka's lemma to carry  □ A  forward along the run.

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

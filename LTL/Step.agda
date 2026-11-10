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

stepAt : Formula -> Val -> Val -> Formula -> Bool
stepAt P v w (var n)   = true
stepAt P v w (¬ A)   = true
stepAt P v w (A ⇒ B) = true
stepAt P v w (○ B)   = boolEq (valOf P v (○ B)) (valOf P w B)
stepAt P v w (□ A)   =
  boolAnd (boolImp (valOf P v (□ A)) (valOf P w (□ A)))
          (boolImp (boolAnd (boolNot (valOf P v (□ A))) (valOf P v A))
                   (boolNot (valOf P w (□ A))))

allStep : Formula -> Val -> Val -> List Formula -> Bool
allStep P v w []        = true
allStep P v w (A :: As) = boolAnd (stepAt P v w A) (allStep P v w As)

step : Formula -> Val -> Val -> Bool
step P v w = allStep P v w (sub P)

------------------------------------------------------------------------
-- Successors within a given set of states

succs : Formula -> List Val -> Val -> List Val
succs P us v = filterL (step P v) us

------------------------------------------------------------------------
-- Reading one conjunct out of a true step

allStep_at : (P : Formula) (v w : Val) (As : List Formula) {X : Formula}
          -> Mem X As -> Eq (allStep P v w As) true -> Eq (stepAt P v w X) true
allStep_at P v w []        ()        e
allStep_at P v w (B :: Bs) memHd     e =
  andTrueL (stepAt P v w B) (allStep P v w Bs) e
allStep_at P v w (B :: Bs) (memTl m) e =
  allStep_at P v w Bs m (andTrueR (stepAt P v w B) (allStep P v w Bs) e)

------------------------------------------------------------------------
-- Persistence, Lemma 2.8 of m4.tex.
--
-- On paper this needs a line of proof; here it is (T3), read off.

persist : (P : Formula) (v w : Val) (A : Formula)
       -> Mem (□ A) (sub P)
       -> Eq (step P v w) true
       -> Eq (valOf P v (□ A)) false
       -> Eq (valOf P v A) true
       -> Eq (valOf P w (□ A)) false
persist P v w A h st bx a =
  t3aux (valOf P v (□ A)) (valOf P v A) (valOf P w (□ A))
        (allStep_at P v w (sub P) h st) bx a
  where
    -- x = □ A at v,  z = A at v,  y = □ A at w
    t3aux : (x z y : Bool)
         -> Eq (boolAnd (boolImp x y)
                        (boolImp (boolAnd (boolNot x) z) (boolNot y))) true
         -> Eq x false -> Eq z true -> Eq y false
    t3aux true  z     y     e () c
    t3aux false false y     e b ()
    t3aux false true  false e b c = refl
    t3aux false true  true  () b c

------------------------------------------------------------------------
-- (T2), read off the same way.
--
-- The note uses it twice: in Lemma 2.7 to refute a successor dropping a box,
-- and in Hintikka's lemma to carry  □ A  forward along the run.

carry : (P : Formula) (v w : Val) (A : Formula)
     -> Mem (□ A) (sub P)
     -> Eq (step P v w) true
     -> Eq (valOf P v (□ A)) true
     -> Eq (valOf P w (□ A)) true
carry P v w A h st bx =
  t2aux (valOf P v (□ A)) (valOf P v A) (valOf P w (□ A))
        (allStep_at P v w (sub P) h st) bx
  where
    t2aux : (x z y : Bool)
         -> Eq (boolAnd (boolImp x y)
                        (boolImp (boolAnd (boolNot x) z) (boolNot y))) true
         -> Eq x true -> Eq y true
    t2aux true  z true  e  b = refl
    t2aux true  z false () b
    t2aux false z y     e  ()

------------------------------------------------------------------------
-- Computational checks.
--
-- For ◇ p the three states of LTL.State are, writing the bits of
-- [ ¬ □ ¬ p , □ ¬ p , ¬ p , p ] :
--
--   s0 = 1 0 0 1   (p holds now)
--   s1 = 1 0 1 0   (p fails now, ◇ p still pending)
--   s2 = 0 1 1 0   (◇ p false, so p fails forever)
--
-- Every state has at least one successor, so no state is removed by (R1).

◇P_succ_counts : Eq (map (\ v -> length (succs ◇P (St ◇P) v)) (St ◇P))
                      (2 :: 3 :: 1 :: [])
◇P_succ_counts = refl

-- For ¬ benAri the six states are, in the order allVecs produces them
-- (true first, so lexicographic with 1 before 0), writing the bits of
-- [ ¬ I , I , □ p , p , ○ □ p , □ p , p ]  with I = □ p ⇒ ○ □ p:
--
--   E = 1 0 1 1 0 1 1     □ p true, ○ □ p false  -- the only state
--                                                        -- containing ¬ benAri
--   F = 0 1 1 1 1 1 1
--   D = 0 1 0 1 1 0 1
--   C = 0 1 0 1 0 0 1
--   B = 0 1 0 0 1 0 0
--   A = 0 1 0 0 0 0 0
--
-- E and D have NO successor, so both are removed by (R1) alone.

¬BenAri_succ_counts
  : Eq (map (\ v -> length (succs ¬BenAri (St ¬BenAri) v)) (St ¬BenAri))
       (0 :: 2 :: 0 :: 4 :: 2 :: 4 :: [])
¬BenAri_succ_counts = refl

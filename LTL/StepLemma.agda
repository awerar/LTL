{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.StepLemma -- G18 and G19 of FORMALISATION-PLAN.md,
-- Lemmas 2.7 and 2.8 of m4.tex.
--
--   stepLemma : Deriv ((chi P v) ⇒ ○ (beta P (succs P (St P) v)))
--
-- Following the note: state completeness and (D1) give |- ○ (beta St),
-- hence a disjunction of ○ chi_w by (D4); the w with v not-> w are dropped;
-- (D4) carries the survivors back under a single nxt.
--
-- The four refutation cases are done with the CONJUNCTION as antecedent,
--   R = (chi P v) ∧ ○ (chi P w) ,
-- deriving  Deriv (¬ R)  and converting at the end by dne.  That keeps every
-- case at one antecedent level, where ∧Fst and ∧Snd give both halves.
--
-- G19 (persistence, Lemma 2.8) is already discharged in LTL.Step as `persist`;
-- it is (T3) read off, so nothing is added here.

module LTL.StepLemma where

open import LTL.Complete public
open import LTL.Step     public

------------------------------------------------------------------------
-- Searching a false allStep

allStep_false : (P : Formula) (v w : Val) (As : List Formula)
             -> Eq (allStep P v w As) false
             -> Sigma Formula (\ A -> Prod (Mem A As) (Eq (stepAt P v w A) false))
allStep_false P v w []        ()
allStep_false P v w (B :: Bs) e =
  sumElim (\ e1 -> sig B (prod memHd e1))
          (\ e2 -> shift (allStep_false P v w Bs e2))
          (andFalse (stepAt P v w B) (allStep P v w Bs) e)
  where
    shift : Sigma Formula (\ A -> Prod (Mem A Bs) (Eq (stepAt P v w A) false))
         -> Sigma Formula (\ A -> Prod (Mem A (B :: Bs)) (Eq (stepAt P v w A) false))
    shift (sig A (prod m q)) = sig A (prod (memTl m) q)

------------------------------------------------------------------------
-- Closing the (T1) case, uniformly in the bit

refute○ : {R B : Formula} (c : Bool)
         -> Deriv (R ⇒ (lit (○ B) (boolNot c)))
         -> Deriv (R ⇒ ○ (lit B c))
         -> Deriv (¬ R)
refute○ true  f g = refute g f
refute○ false f g = refute f (⇒Trans g linF)

------------------------------------------------------------------------
-- Refuting a non-successor

notSucc : (P : Formula) (v w : Val)
       -> Eq (length v) (length (sub P))
       -> Eq (length w) (length (sub P))
       -> Eq (step P v w) false
       -> Deriv (¬ ((chi P v) ∧ ○ (chi P w)))
notSucc P v w lenv lenw e = sigElim (allStep_false P v w (sub P) e)
  where
    R : Formula
    R = (chi P v) ∧ ○ (chi P w)

    pv : {A : Formula} -> Mem A (sub P) -> Deriv (R ⇒ (lit A (valOf P v A)))
    pv m = ⇒Trans ∧Fst (chiProjVal P v lenv m)

    pw : {A : Formula} -> Mem A (sub P) -> Deriv (R ⇒ ○ (lit A (valOf P w A)))
    pw m = ⇒Trans ∧Snd (○Mono (chiProjVal P w lenw m))

    pvAt : {A : Formula} -> Mem A (sub P) -> (c : Bool) -> Eq (valOf P v A) c
        -> Deriv (R ⇒ (lit A c))
    pvAt m c eq = eqSubst (\ d -> Deriv (R ⇒ (lit _ d))) eq (pv m)

    pwAt : {A : Formula} -> Mem A (sub P) -> (c : Bool) -> Eq (valOf P w A) c
        -> Deriv (R ⇒ ○ (lit A c))
    pwAt m c eq = eqSubst (\ d -> Deriv (R ⇒ ○ (lit _ d))) eq (pw m)

    ----------------------------------------------------------------
    -- (T1)

    case○ : {B : Formula} -> Mem (○ B) (sub P)
           -> Eq (boolEq (valOf P v (○ B)) (valOf P w B)) false
           -> Deriv (¬ R)
    case○ {B} m q =
      refute○ (valOf P w B)
                (pvAt m (boolNot (valOf P w B))
                      (boolEq_false_eq (valOf P v (○ B)) (valOf P w B) q))
                (pwAt (sub_○ P m) (valOf P w B) refl)

    ----------------------------------------------------------------
    -- (T2) and (T3)

    case□ : {B : Formula} -> Mem (□ B) (sub P)
           -> Eq (boolAnd (boolImp (valOf P v (□ B)) (valOf P w (□ B)))
                          (boolImp (boolAnd (boolNot (valOf P v (□ B)))
                                            (valOf P v B))
                                   (boolNot (valOf P w (□ B))))) false
           -> Deriv (¬ R)
    case□ {B} m q = sumElim t2 t3 (andFalse _ _ q)
      where
        -- (T2): □ B holds at v, so it must hold at w; it does not.
        t2 : Eq (boolImp (valOf P v (□ B)) (valOf P w (□ B))) false
          -> Deriv (¬ R)
        t2 q2 = refute (⇒Trans (pvAt m true (prodFst pr)) □○□)
                       (⇒Trans (pwAt m false (prodSnd pr)) linF)
          where
            pr : Prod (Eq (valOf P v (□ B)) true) (Eq (valOf P w (□ B)) false)
            pr = boolImp_false (valOf P v (□ B)) (valOf P w (□ B)) q2

        -- (T3): □ B fails at v while B holds, so □ B must fail at w;
        -- it holds, and (D6) turns B with ○ □ B back into □ B.
        t3 : Eq (boolImp (boolAnd (boolNot (valOf P v (□ B))) (valOf P v B))
                         (boolNot (valOf P w (□ B)))) false
          -> Deriv (¬ R)
        t3 q3 = refute (⇒Trans (∧Pair (pvAt (sub_□ P m) true eB)
                                          (pwAt m true eW))
                                 expConv)
                       (pvAt m false eV)
          where
            pr : Prod (Eq (boolAnd (boolNot (valOf P v (□ B))) (valOf P v B)) true)
                      (Eq (boolNot (valOf P w (□ B))) false)
            pr = boolImp_false _ _ q3

            eV : Eq (valOf P v (□ B)) false
            eV = notTrue (valOf P v (□ B))
                         (andTrueL (boolNot (valOf P v (□ B))) (valOf P v B)
                                   (prodFst pr))
              where
                notTrue : (b : Bool) -> Eq (boolNot b) true -> Eq b false
                notTrue true  ()
                notTrue false e' = refl

            eB : Eq (valOf P v B) true
            eB = andTrueR (boolNot (valOf P v (□ B))) (valOf P v B) (prodFst pr)

            eW : Eq (valOf P w (□ B)) true
            eW = notFalse (valOf P w (□ B)) (prodSnd pr)
              where
                notFalse : (b : Bool) -> Eq (boolNot b) false -> Eq b true
                notFalse true  e' = refl
                notFalse false ()

    ----------------------------------------------------------------

    byShape : {A : Formula} -> Mem A (sub P) -> Eq (stepAt P v w A) false
           -> Deriv (¬ R)
    byShape {var n}   m ()
    byShape {¬ B}   m ()
    byShape {B ⇒ D} m ()
    byShape {○ B}   m q = case○ m q
    byShape {□ B}   m q = case□ m q

    sigElim : Sigma Formula (\ A -> Prod (Mem A (sub P))
                                         (Eq (stepAt P v w A) false))
           -> Deriv (¬ R)
    sigElim (sig A (prod m q)) = byShape m q

badSucc : (P : Formula) (v w : Val)
       -> Eq (length v) (length (sub P))
       -> Eq (length w) (length (sub P))
       -> Eq (step P v w) false
       -> Deriv ((chi P v) ⇒ ¬ ○ (chi P w))
badSucc P v w lenv lenw e = mp dne (notSucc P v w lenv lenw e)

------------------------------------------------------------------------
-- Dropping the non-successors under the antecedent chi P v

allLen_filter : {n : Nat} (p : Val -> Bool) {vs : List Val}
             -> AllLen n vs -> AllLen n (filterL p vs)
allLen_filter p alNil                 = alNil
allLen_filter p {v :: vs} (alCons e al) = aux (p v)
  where
    aux : (b : Bool) -> AllLen _ (filterCons b v (filterL p vs))
    aux true  = alCons e (allLen_filter p al)
    aux false = allLen_filter p al

map_filterCons2 : (P : Formula) (b : Bool) (w : Val) (L : List Val)
               -> Eq (map ○_ (map (chi P) (filterCons b w L)))
                     (filterCons b (○ (chi P w)) (map ○_ (map (chi P) L)))
map_filterCons2 P true  w L = refl
map_filterCons2 P false w L = refl

filter⇒ : (P : Formula) (v : Val) (Q : Formula) (ws : List Val)
         -> AllLen (length (sub P)) ws
         -> ((w : Val) -> Eq (length w) (length (sub P)) -> Eq (step P v w) false
               -> Deriv (Q ⇒ ¬ ○ (chi P w)))
         -> Deriv (Q ⇒ ⋁ (map ○_ (map (chi P) ws))
                       ⇒ ⋁ (map ○_ (map (chi P)
                                (filterL (step P v) ws))))
filter⇒ P v Q []        alNil           bad = liftP ⇒Refl
filter⇒ P v Q (w :: ws) (alCons lenw al) bad =
  eqSubst (\ L -> Deriv (Q ⇒ ⋁ (○ (chi P w) :: map ○_ (map (chi P) ws))
                             ⇒ ⋁ L))
          (eqSym (map_filterCons2 P (step P v w) w (filterL (step P v) ws)))
          (onStep (step P v w) refl)
  where
    ih : Deriv (Q ⇒ ⋁ (map ○_ (map (chi P) ws))
                    ⇒ ⋁ (map ○_ (map (chi P) (filterL (step P v) ws))))
    ih = filter⇒ P v Q ws al bad

    X : Formula
    X = ○ (chi P w)

    onStep : (b : Bool) -> Eq (step P v w) b
          -> Deriv (Q ⇒ ⋁ (X :: map ○_ (map (chi P) ws))
                        ⇒ ⋁ (filterCons b X
                                (map ○_ (map (chi P)
                                   (filterL (step P v) ws)))))
    -- kept: compose under the same antecedent ¬ X
    onStep true  e = mpU (liftP p2) (⇒Trans ih p1)
    -- dropped: ¬ X is available, so the antecedent ¬ X can be discharged
    onStep false e =
      ⇒TransU (⇒Trans (bad w lenw e) (⇒Swap ⇒Refl)) ih

------------------------------------------------------------------------
-- Lemma 2.7

stepLemma : (P : Formula) (v : Val)
         -> Eq (length v) (length (sub P))
         -> Deriv ((chi P v) ⇒ ○ (beta P (succs P (St P) v)))
stepLemma P v lenv =
  ⇒Trans (mpU (filter⇒ P v (chi P v) (St P) stLen bad) start)
           (○⋁L2 (map (chi P) (succs P (St P) v)))
  where
    stLen : AllLen (length (sub P)) (St P)
    stLen = allLen_filter (isState P) (allVecs_allLen (length (sub P)))

    bad : (w : Val) -> Eq (length w) (length (sub P)) -> Eq (step P v w) false
       -> Deriv ((chi P v) ⇒ ¬ ○ (chi P w))
    bad w lenw e = badSucc P v w lenv lenw e

    start : Deriv ((chi P v) ⇒ ⋁ (map ○_ (map (chi P) (St P))))
    start = liftP (mp (○⋁L1 (map (chi P) (St P)))
                      (○Gen (stateComplete P)))

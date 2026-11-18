{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.StepLemma -- G18 and G19 of FORMALISATION-PLAN.md,
-- Lemmas 2.7 and 2.8 of m4.tex.
--
--   stepLemma : ⊢ (chi P v) ⇒ ○ (beta P (succs P (St P) v))
--
-- Following the note: state completeness and (D1) give |- ○ (beta St),
-- hence a disjunction of ○ chi_w by (D4); the w with v not-> w are dropped;
-- (D4) carries the survivors back under a single ○.
--
-- The four refutation cases are done with the CONJUNCTION as antecedent,
--   R = (chi P v) ∧ ○ (chi P w) ,
-- deriving  ⊢ ¬ R  and converting at the end by dne.  That keeps every
-- case at one antecedent level, where ∧Fst and ∧Snd give both halves.
--
-- G19 (persistence, Lemma 2.8) is already discharged in LTL.States.Step as `persist`;
-- it is (T3) read off, so nothing is added here.

module LTL.States.StepLemma where

open import LTL.States.Complete public
open import LTL.States.Step     public

------------------------------------------------------------------------
-- Closing the (T1) case, uniformly in the bit

refute○ : {R B : Formula} (c : Bool)
       -> ⊢ R ⇒ (lit (○ B) (¬ᵇ c))
       -> ⊢ R ⇒ ○ (lit B c)
       -> ⊢ ¬ R
refute○ true  f g = refute g f
refute○ false f g = refute f (⇒Trans g linFwd)

------------------------------------------------------------------------
-- Refuting a non-successor

notSucc : (P : Formula) (v w : Val)
       -> length v ≡ length (sub P)
       -> length w ≡ length (sub P)
       -> step P v w ≡ false
       -> ⊢ ¬ ((chi P v) ∧ ○ (chi P w))
notSucc P v w lenv lenw e = sigElim (all-false (stepAt P v w) (sub P) e)
  where
    R : Formula
    R = (chi P v) ∧ ○ (chi P w)

    pv : {A : Formula} -> A ∈ sub P -> ⊢ R ⇒ (lit A (valOf P v A))
    pv m = ⇒Trans ∧Fst (chiProjVal P v lenv m)

    pw : {A : Formula} -> A ∈ sub P -> ⊢ R ⇒ ○ (lit A (valOf P w A))
    pw m = ⇒Trans ∧Snd (○Mono (chiProjVal P w lenw m))

    pvAt : {A : Formula} -> A ∈ sub P -> (c : Bool) -> valOf P v A ≡ c
        -> ⊢ R ⇒ (lit A c)
    pvAt m c eq = subst (λ d -> ⊢ R ⇒ (lit _ d)) eq (pv m)

    pwAt : {A : Formula} -> A ∈ sub P -> (c : Bool) -> valOf P w A ≡ c
        -> ⊢ R ⇒ ○ (lit A c)
    pwAt m c eq = subst (λ d -> ⊢ R ⇒ ○ (lit _ d)) eq (pw m)

    ----------------------------------------------------------------
    -- (T1)

    case○ : {B : Formula} -> ○ B ∈ sub P
         -> valOf P v (○ B) ⇔ᵇ valOf P w B ≡ false
         -> ⊢ ¬ R
    case○ {B} m q =
      refute○ (valOf P w B)
                (pvAt m (¬ᵇ valOf P w B)
                      (⇔ᵇ-false (valOf P v (○ B)) (valOf P w B) q))
                (pwAt (sub-○ P m) (valOf P w B) refl)

    ----------------------------------------------------------------
    -- (T2) and (T3)

    case□ : {B : Formula} -> □ B ∈ sub P
         -> (valOf P v (□ B) ⇒ᵇ valOf P w (□ B)) ∧ᵇ
            (¬ᵇ valOf P v (□ B) ∧ᵇ valOf P v B ⇒ᵇ ¬ᵇ valOf P w (□ B)) ≡ false
         -> ⊢ ¬ R
    case□ {B} m q = sumElim t2 t3 (∧ᵇ-false _ _ q)
      where
        -- (T2): □ B holds at v, so it must hold at w; it does not.
        t2 : valOf P v (□ B) ⇒ᵇ valOf P w (□ B) ≡ false
          -> ⊢ ¬ R
        t2 q2 = refute (⇒Trans (pvAt m true (fst pr)) □○□)
                       (⇒Trans (pwAt m false (snd pr)) linFwd)
          where
            pr : valOf P v (□ B) ≡ true × valOf P w (□ B) ≡ false
            pr = ⇒ᵇ-false (valOf P v (□ B)) (valOf P w (□ B)) q2

        -- (T3): □ B fails at v while B holds, so □ B must fail at w;
        -- it holds, and (D6) turns B with ○ □ B back into □ B.
        t3 : ¬ᵇ valOf P v (□ B) ∧ᵇ valOf P v B ⇒ᵇ ¬ᵇ valOf P w (□ B) ≡ false
          -> ⊢ ¬ R
        t3 q3 = refute (⇒Trans (∧Pair (pvAt (sub-□ P m) true eB)
                                          (pwAt m true eW))
                                 expConv)
                       (pvAt m false eV)
          where
            pr : ¬ᵇ valOf P v (□ B) ∧ᵇ valOf P v B ≡ true ×
                 ¬ᵇ valOf P w (□ B) ≡ false
            pr = ⇒ᵇ-false _ _ q3

            eV : valOf P v (□ B) ≡ false
            eV = ¬ᵇ-true (valOf P v (□ B))
                         (∧ᵇ-trueˡ (¬ᵇ valOf P v (□ B)) (valOf P v B)
                                   (fst pr))

            eB : valOf P v B ≡ true
            eB = ∧ᵇ-trueʳ (¬ᵇ valOf P v (□ B)) (valOf P v B) (fst pr)

            eW : valOf P w (□ B) ≡ true
            eW = ¬ᵇ-false (valOf P w (□ B)) (snd pr)

    ----------------------------------------------------------------

    byShape : {A : Formula} -> A ∈ sub P -> stepAt P v w A ≡ false
           -> ⊢ ¬ R
    byShape {var n}   m ()
    byShape {¬ B}   m ()
    byShape {B ⇒ D} m ()
    byShape {○ B}   m q = case○ m q
    byShape {□ B}   m q = case□ m q

    sigElim : (Σ[ A ∈ Formula ] A ∈ sub P ×
                                    stepAt P v w A ≡ false)
           -> ⊢ ¬ R
    sigElim (A , m , q) = byShape m q

badSucc : (P : Formula) (v w : Val)
       -> length v ≡ length (sub P)
       -> length w ≡ length (sub P)
       -> step P v w ≡ false
       -> ⊢ (chi P v) ⇒ ¬ ○ (chi P w)
badSucc P v w lenv lenw e = mp dne (notSucc P v w lenv lenw e)

------------------------------------------------------------------------
-- Dropping the non-successors under the antecedent chi P v

allLen-filter : {n : Nat} (p : Val -> Bool) {vs : List Val}
             -> AllLen n vs -> AllLen n (filter p vs)
allLen-filter p alNil                 = alNil
allLen-filter p {v ∷ vs} (alCons e al) = aux (p v)
  where
    aux : (b : Bool) -> AllLen _ (filterCons b v (filter p vs))
    aux true  = alCons e (allLen-filter p al)
    aux false = allLen-filter p al

filter⇒ : (P : Formula) (v : Val) (Q : Formula) (ws : List Val)
       -> AllLen (length (sub P)) ws
       -> ((w : Val) -> length w ≡ length (sub P) -> step P v w ≡ false
             -> ⊢ Q ⇒ ¬ ○ (chi P w))
       -> ⊢ Q ⇒ ⋁ (map ○_ (map (chi P) ws))
                ⇒ ⋁ (map ○_ (map (chi P)
                         (filter (step P v) ws)))
filter⇒ P v Q []       alNil           bad = liftP ⇒Refl
filter⇒ P v Q (w ∷ ws) (alCons lenw al) bad with step P v w in e
-- kept: compose under the same antecedent ¬ ○ (chi P w)
... | true  = mpU (liftP p2) (⇒Trans (filter⇒ P v Q ws al bad) p1)
-- dropped: ¬ ○ (chi P w) is available, so that antecedent can be discharged
... | false =
  ⇒TransU (⇒Trans (bad w lenw e) (⇒Swap ⇒Refl)) (filter⇒ P v Q ws al bad)

------------------------------------------------------------------------
-- Lemma 2.7

stepLemma : (P : Formula) (v : Val)
         -> length v ≡ length (sub P)
         -> ⊢ (chi P v) ⇒ ○ (beta P (succs P (St P) v))
stepLemma P v lenv =
  ⇒Trans (mpU (filter⇒ P v (chi P v) (St P) stLen bad) start)
           (○⋁L2 (map (chi P) (succs P (St P) v)))
  where
    stLen : AllLen (length (sub P)) (St P)
    stLen = allLen-filter (isState P) (allVecs-allLen (length (sub P)))

    bad : (w : Val) -> length w ≡ length (sub P) -> step P v w ≡ false
       -> ⊢ (chi P v) ⇒ ¬ ○ (chi P w)
    bad w lenw e = badSucc P v w lenv lenw e

    start : ⊢ (chi P v) ⇒ ⋁ (map ○_ (map (chi P) (St P)))
    start = liftP (mp (○⋁L1 (map (chi P) (St P)))
                      (○Gen (stateComplete P)))

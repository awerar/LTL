{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Complete -- G17 of FORMALISATION-PLAN.md, Lemma 2.6 of m4.tex.
--
--   stateComplete : ⊢ beta P (St P)
--
-- Two steps.  First the disjunction over ALL valuations, by structural
-- induction along sub P: each step splits on the next formula with splitD
-- (L6).  Then the non-states are dropped by ⋁Drop, using nonState (G16).
--
-- The work is in lining up the shapes: allVecs (suc n) is built by consing
-- true and false onto allVecs n and appending, while splitOn conjoins A and
-- ¬ A onto a list of formulas and appends.  stepEq says these agree once
-- chi is applied, and it holds because  ⋀ (litList (A ∷ As) (b ∷ w))
-- reduces to  (lit A b) ∧ ⋀ (litList As w).

module LTL.Complete where

open import LTL.NonState public

------------------------------------------------------------------------
-- chi against an arbitrary list of formulas

chiOf : List Formula -> Val -> Formula
chiOf As v = ⋀ (litList As v)

------------------------------------------------------------------------
-- Lining up allVecs with splitOn

appCong : {A : Set} {xs xs' ys ys' : List A}
       -> xs ≡ xs' -> ys ≡ ys' -> xs ++ ys ≡ xs' ++ ys'
appCong refl refl = refl

lemTrue : (A : Formula) (As : List Formula) (V : List Val)
       -> map (chiOf (A ∷ As)) (map (λ w -> true ∷ w) V) ≡
          map (A ∧_) (map (chiOf As) V)
lemTrue A As V = trans (map_map (chiOf (A ∷ As)) (λ w -> true ∷ w) V)
                       (sym (map_map (A ∧_) (chiOf As) V))

lemFalse : (A : Formula) (As : List Formula) (V : List Val)
        -> map (chiOf (A ∷ As)) (map (λ w -> false ∷ w) V) ≡
           map (¬ A ∧_) (map (chiOf As) V)
lemFalse A As V = trans (map_map (chiOf (A ∷ As)) (λ w -> false ∷ w) V)
                        (sym (map_map (¬ A ∧_) (chiOf As) V))

stepEq : (A : Formula) (As : List Formula)
      -> map (chiOf (A ∷ As)) (allVecs (suc (length As))) ≡
         splitOn A (map (chiOf As) (allVecs (length As)))
stepEq A As =
  trans (map_append (chiOf (A ∷ As))
                    (map (λ w -> true  ∷ w) (allVecs (length As)))
                    (map (λ w -> false ∷ w) (allVecs (length As))))
        (appCong (lemTrue  A As (allVecs (length As)))
                 (lemFalse A As (allVecs (length As))))

------------------------------------------------------------------------
-- The disjunction over all valuations

allComplete : (As : List Formula)
           -> ⊢ ⋁ (map (chiOf As) (allVecs (length As)))
allComplete []       = mp (⋁Intro (⊤ ∷ []) here) deriv⊤
allComplete (A ∷ As) =
  subst (λ L -> ⊢ ⋁ L) (sym (stepEq A As))
        (splitD (map (chiOf As) (allVecs (length As))) (allComplete As))

------------------------------------------------------------------------
-- Every vector produced by allVecs n has length n

data AllLen (n : Nat) : List Val -> Set where
  alNil  : AllLen n []
  alCons : {v : Val} {vs : List Val}
        -> length v ≡ n -> AllLen n vs -> AllLen n (v ∷ vs)

allLen_append : {n : Nat} {xs ys : List Val}
             -> AllLen n xs -> AllLen n ys -> AllLen n (xs ++ ys)
allLen_append alNil          ay = ay
allLen_append (alCons e ax)  ay = alCons e (allLen_append ax ay)

allLen_cons : (b : Bool) {n : Nat} {V : List Val}
           -> AllLen n V -> AllLen (suc n) (map (λ w -> b ∷ w) V)
allLen_cons b alNil         = alNil
allLen_cons b (alCons e ax) = alCons (cong suc e) (allLen_cons b ax)

allVecs_allLen : (n : Nat) -> AllLen n (allVecs n)
allVecs_allLen zero    = alCons refl alNil
allVecs_allLen (suc n) =
  allLen_append (allLen_cons true  (allVecs_allLen n))
                (allLen_cons false (allVecs_allLen n))

------------------------------------------------------------------------
-- Dropping the non-states

map_filterCons : (P : Formula) (b : Bool) (v : Val) (L : List Val)
              -> map (chi P) (filterCons b v L) ≡
                 filterCons b (chi P v) (map (chi P) L)
map_filterCons P true  v L = refl
map_filterCons P false v L = refl

⋁Filter : (P : Formula) (vs : List Val)
          -> AllLen (length (sub P)) vs
          -> ⊢ ⋁ (map (chi P) vs)
               ⇒ ⋁ (map (chi P) (filterL (isState P) vs))
⋁Filter P []       alNil          = ⇒Refl
⋁Filter P (v ∷ vs) (alCons len al) =
  subst (λ L -> ⊢ ⋁ (chi P v ∷ map (chi P) vs) ⇒ ⋁ L)
        (sym (map_filterCons P (isState P v) v (filterL (isState P) vs)))
        (onState (isState P v) refl)
  where
    ih : ⊢ ⋁ (map (chi P) vs) ⇒ ⋁ (map (chi P) (filterL (isState P) vs))
    ih = ⋁Filter P vs al

    onState : (b : Bool) -> isState P v ≡ b
           -> ⊢ ⋁ (chi P v ∷ map (chi P) vs)
                ⇒ ⋁ (filterCons b (chi P v)
                        (map (chi P) (filterL (isState P) vs)))
    onState true  e = ∨MonoR ih
    onState false e =
      ⇒Trans (⋁Drop (map (chi P) vs) (nonState P v len e)) ih

------------------------------------------------------------------------
-- Lemma 2.6

stateComplete : (P : Formula) -> ⊢ beta P (St P)
stateComplete P =
  mp (⋁Filter P (allVecs (length (sub P)))
                 (allVecs_allLen (length (sub P))))
     (allComplete (sub P))

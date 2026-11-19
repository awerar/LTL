{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Complete -- state completeness: ⊢ beta P (St P).
--
-- First the disjunction over ALL valuations, by induction along sub P,
-- splitting on the next formula with (L6) (splitD).  Then the non-states are
-- dropped with ⋁Drop and nonState.  stepEq lines up the shapes: allVecs
-- (suc n) and splitOn both cons onto a list and append, and agree once chi is
-- applied.  The proof is exponential in |sub P|; LTL.Procedures.CompletePC
-- proves the same formula with (PC).

module LTL.States.Complete where

open import LTL.States.NonState public

------------------------------------------------------------------------
-- chi against an arbitrary list of formulas

chiOf : List Formula -> Val -> Formula
chiOf As v = ⋀ (litList As v)

------------------------------------------------------------------------
-- Lining up allVecs with splitOn

appCong : {A : Set} {xs xs' ys ys' : List A}
       -> xs ≡ xs' -> ys ≡ ys' -> xs ++ ys ≡ xs' ++ ys'
appCong refl refl = refl

chiOfTrue : (A : Formula) (As : List Formula) (V : List Val)
         -> map (chiOf (A ∷ As)) (map (λ w -> true ∷ w) V) ≡
            map (A ∧_) (map (chiOf As) V)
chiOfTrue A As V = trans (map-map (chiOf (A ∷ As)) (λ w -> true ∷ w) V)
                         (sym (map-map (A ∧_) (chiOf As) V))

chiOfFalse : (A : Formula) (As : List Formula) (V : List Val)
          -> map (chiOf (A ∷ As)) (map (λ w -> false ∷ w) V) ≡
             map (¬ A ∧_) (map (chiOf As) V)
chiOfFalse A As V = trans (map-map (chiOf (A ∷ As)) (λ w -> false ∷ w) V)
                          (sym (map-map (¬ A ∧_) (chiOf As) V))

stepEq : (A : Formula) (As : List Formula)
      -> map (chiOf (A ∷ As)) (allVecs (suc (length As))) ≡
         splitOn A (map (chiOf As) (allVecs (length As)))
stepEq A As =
  trans (map-append (chiOf (A ∷ As))
                    (map (λ w -> true  ∷ w) (allVecs (length As)))
                    (map (λ w -> false ∷ w) (allVecs (length As))))
        (appCong (chiOfTrue  A As (allVecs (length As)))
                 (chiOfFalse A As (allVecs (length As))))

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

allLen-append : {n : Nat} {xs ys : List Val}
             -> AllLen n xs -> AllLen n ys -> AllLen n (xs ++ ys)
allLen-append alNil          ay = ay
allLen-append (alCons e ax)  ay = alCons e (allLen-append ax ay)

allLen-cons : (b : Bool) {n : Nat} {V : List Val}
           -> AllLen n V -> AllLen (suc n) (map (λ w -> b ∷ w) V)
allLen-cons b alNil         = alNil
allLen-cons b (alCons e ax) = alCons (cong suc e) (allLen-cons b ax)

allVecs-allLen : (n : Nat) -> AllLen n (allVecs n)
allVecs-allLen zero    = alCons refl alNil
allVecs-allLen (suc n) =
  allLen-append (allLen-cons true  (allVecs-allLen n))
                (allLen-cons false (allVecs-allLen n))

------------------------------------------------------------------------
-- Dropping the non-states

⋁Filter : (P : Formula) (vs : List Val)
       -> AllLen (length (sub P)) vs
       -> ⊢ ⋁ (map (chi P) vs)
            ⇒ ⋁ (map (chi P) (filter (isState P) vs))
⋁Filter P []       alNil          = ⇒Refl
⋁Filter P (v ∷ vs) (alCons len al) with isState P v in e
... | true  = ∨MonoR (⋁Filter P vs al)
... | false =
  ⇒Trans (⋁Drop (map (chi P) vs) (nonState P v len e)) (⋁Filter P vs al)

------------------------------------------------------------------------
-- State completeness

stateComplete : (P : Formula) -> ⊢ beta P (St P)
stateComplete P =
  mp (⋁Filter P (allVecs (length (sub P)))
                 (allVecs-allLen (length (sub P))))
     (allComplete (sub P))

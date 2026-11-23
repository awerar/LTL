{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Common -- the formula-independent base of the P-modules.
--
-- The modules from LTL.States.State to LTL.SCC.SccSeed are parameterised by
-- the formula P.  What they share that does not mention P lives here, so that
-- an importer who opens them unapplied does not see a spurious P argument:
-- the refutation lemmas, projections out of litList, and the disjunction over
-- all valuations.  It re-exports the derived rules, valuations as a set
-- (LTL.States.Reach) and positions (LTL.Semantics.Orbit at Val), so a
-- P-module opens this module and its P-modules.

module LTL.States.Common where

open import LTL.Rules.Temporal public
open import LTL.States.Reach   public

-- Positions and orbits of LTL.Semantics.Orbit, at valuations.
open import LTL.Semantics.Orbit Val public

------------------------------------------------------------------------
-- Refutation from a formula and its negation

refute : {C B : Formula} -> ⊢ C ⇒ B -> ⊢ C ⇒ ¬ B -> ⊢ ¬ C
refute f g = mp (¬IntroU (liftP f) (liftP g)) deriv⊤

-- Two ways of closing a refutation on a literal

refuteLit : {C X : Formula} (b : Bool)
         -> ⊢ C ⇒ (lit X b) -> ⊢ C ⇒ (lit X (¬ᵇ b))
         -> ⊢ ¬ C
refuteLit true  f g = refute f g
refuteLit false f g = refute g f

refute¬ : {C B : Formula} (b : Bool)
       -> ⊢ C ⇒ (lit B b) -> ⊢ C ⇒ (lit (¬ B) b)
       -> ⊢ ¬ C
refute¬ true  f g = refute f g
refute¬ false f g = refute f g

-- Closing the (T1) case of the step lemma, uniformly in the bit

refute○ : {R B : Formula} (c : Bool)
       -> ⊢ R ⇒ (lit (○ B) (¬ᵇ c))
       -> ⊢ R ⇒ ○ (lit B c)
       -> ⊢ ¬ R
refute○ true  f g = refute g f
refute○ false f g = refute f (⇒Trans g linFwd)

------------------------------------------------------------------------
-- Positional projection, for the case where coherence fails and cohLookup is
-- not available.

litList-nth : (As : List Formula) (v : Val) (i : Nat)
           -> i < length As -> length v ≡ length As
           -> lit (nth As i ⊥) (bitAt v i) ∈ litList As v
litList-nth []       v       i       ()        len
litList-nth (A ∷ As) []      i       lt        ()
litList-nth (A ∷ As) (b ∷ v) zero    lt        len = here
litList-nth (A ∷ As) (b ∷ v) (suc i) (ltSuc l) len =
  there (litList-nth As v i l (sucInj len))

------------------------------------------------------------------------
-- The first-occurrence index is a position in range that carries its formula.
-- This is what projecting the literal signed by valOf needs without
-- coherence.

indexOf-lt : (xs : List Formula) {X : Formula} -> X ∈ xs -> indexOf xs X < length xs
indexOf-lt []       ()
indexOf-lt (B ∷ Bs) here     = aux (B ≡ᶠ B) (≡ᶠ-refl B)
  where
    aux : (b : Bool) -> b ≡ true -> indexOfCons b (indexOf Bs B) < suc (length Bs)
    aux true  e  = ltZero
    aux false ()
indexOf-lt (B ∷ Bs) {X} (there m) = aux (B ≡ᶠ X)
  where
    aux : (b : Bool) -> indexOfCons b (indexOf Bs X) < suc (length Bs)
    aux true  = ltZero
    aux false = ltSuc (indexOf-lt Bs m)

indexOf-nth : (xs : List Formula) {X : Formula} -> X ∈ xs
           -> nth xs (indexOf xs X) ⊥ ≡ X
indexOf-nth []       ()
indexOf-nth (B ∷ Bs) here     = aux (B ≡ᶠ B) (≡ᶠ-refl B)
  where
    aux : (b : Bool) -> b ≡ true
       -> nth (B ∷ Bs) (indexOfCons b (indexOf Bs B)) ⊥ ≡ B
    aux true  e  = refl
    aux false ()
indexOf-nth (B ∷ Bs) {X} (there m) = aux (B ≡ᶠ X) (≡ᶠ-sound B X)
  where
    aux : (b : Bool) -> (b ≡ true -> B ≡ X)
       -> nth (B ∷ Bs) (indexOfCons b (indexOf Bs X)) ⊥ ≡ X
    aux true  f = f refl
    aux false f = indexOf-nth Bs m

------------------------------------------------------------------------
-- chi against an arbitrary list of formulas

chiOf : List Formula -> Val -> Formula
chiOf As v = ⋀ (litList As v)

-- Lining up allVecs with splitOn

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
        (cong₂ _++_ (chiOfTrue  A As (allVecs (length As)))
                    (chiOfFalse A As (allVecs (length As))))

-- The disjunction over all valuations: the first half of state completeness
-- (LTL.States.Complete), by induction along the list, splitting on the next
-- formula with (L6) (splitD).

allComplete : (As : List Formula)
           -> ⊢ ⋁ (map (chiOf As) (allVecs (length As)))
allComplete []       = mp (⋁Intro (⊤ ∷ []) here) deriv⊤
allComplete (A ∷ As) =
  subst (λ L -> ⊢ ⋁ L) (sym (stepEq A As))
        (splitD (map (chiOf As) (allVecs (length As))) (allComplete As))

------------------------------------------------------------------------
-- AllInto for a mapped list, one derivation of  f w ⇒ C  per w.

allIntoMap : {C : Formula} (f : Val -> Formula) (ws : List Val)
          -> (∀[ w ∈ ws ] ⊢ (f w) ⇒ C) -> AllInto C (map f ws)
allIntoMap f []       h = intoNil
allIntoMap f (w ∷ ws) h = intoCons (h w here) (allIntoMap f ws (λ z m -> h z (there m)))

------------------------------------------------------------------------
-- Extensionality for bit vectors

valExt : (v w : Val) -> length v ≡ length w
      -> ((i : Nat) -> i < length v -> bitAt v i ≡ bitAt w i) -> v ≡ w
valExt []      []      e  h = refl
valExt []      (c ∷ w) () h
valExt (b ∷ v) []      () h
valExt (b ∷ v) (c ∷ w) e  h =
  cong₂ _∷_ (h zero ltZero)
            (valExt v w (sucInj e) (λ i l -> h (suc i) (ltSuc l)))

------------------------------------------------------------------------
-- A state met from b is a state of a cycle that contains b

cycMem : {b z : Val} {qs : List Val} -> b ∈ qs -> z ∈ b ∷ qs -> z ∈ qs
cycMem mb here      = mb
cycMem mb (there m) = m

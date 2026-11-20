{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Syntax.Skel -- the propositional skeleton of a formula, and the
-- decidable tautology test isTaut that the (PC) rule of LTL.Syntax.Deriv uses.
--
-- A formula is a tautology of its skeleton when it is true in every row of the
-- truth table that treats its var, ○ and □ subformulas as atoms.  This is a
-- Boolean condition on the formula alone, so (PC) needs no substitution
-- relation.
--
-- valFrom reads a formula from an assignment to atoms; LTL.States.Closure uses
-- it to build states.  skelEval says it agrees with any reading that is
-- compositional on ¬ and ⇒: valOf at a state, and evalAt at a position of a
-- lasso.  That one lemma serves both state construction and the soundness of
-- (PC).

module LTL.Syntax.Skel where

open import LTL.Syntax.Sub public

------------------------------------------------------------------------
-- Valuations, as bit vectors, and their enumeration

Val : Set
Val = List Bool

bitAt : Val -> Nat -> Bool
bitAt v i = nth v i false

allVecs : Nat -> List Val
allVecs zero    = [] ∷ []
allVecs (suc n) = map (λ bs -> true ∷  bs) (allVecs n) ++
                  map (λ bs -> false ∷ bs) (allVecs n)

allVecs-complete : (n : Nat) (v : Val) -> length v ≡ n -> v ∈ allVecs n
allVecs-complete zero    []           e  = here
allVecs-complete zero    (b ∷ v)      ()
allVecs-complete (suc n) []           ()
allVecs-complete (suc n) (true  ∷ v)  e  =
  memAppL (map (λ bs -> true ∷ bs) (allVecs n))
          (map (λ bs -> false ∷ bs) (allVecs n))
          (memMap (λ bs -> true ∷ bs) (allVecs-complete n v (sucInj e)))
allVecs-complete (suc n) (false ∷ v)  e  =
  memAppR (map (λ bs -> true ∷ bs) (allVecs n))
          (map (λ bs -> false ∷ bs) (allVecs n))
          (memMap (λ bs -> false ∷ bs) (allVecs-complete n v (sucInj e)))

------------------------------------------------------------------------
-- Lookup by first occurrence

indexOfCons : Bool -> Nat -> Nat
indexOfCons true  n = zero
indexOfCons false n = suc n

indexOf : List Formula -> Formula -> Nat
indexOf []       A = zero
indexOf (B ∷ Bs) A = indexOfCons (B ≡ᶠ A) (indexOf Bs A)

------------------------------------------------------------------------
-- Formula membership as a boolean, and the index/nth round-trip for lookup by
-- formula.  indexOf finds the FIRST occurrence.

infix 4.5 _∈ᶠ_

_∈ᶠ_ : Formula -> List Formula -> Bool
A ∈ᶠ []       = false
A ∈ᶠ (B ∷ Bs) = (B ≡ᶠ A) ∨ᵇ (A ∈ᶠ Bs)

-- (The F in indexOf-nthF, indexOf-ltF: these start from the Boolean A ∈ᶠ As,
-- where indexOf-nth, indexOf-lt of LTL.States.Proj start from A ∈ As.)

indexOf-nthF : (As : List Formula) (A : Formula) -> A ∈ᶠ As ≡ true
            -> nth As (indexOf As A) ⊥ ≡ A
indexOf-nthF []       A ()
indexOf-nthF (B ∷ Bs) A e with B ≡ᶠ A in eb
... | true  = ≡ᶠ-sound B A eb
... | false = indexOf-nthF Bs A e

indexOf-ltF : (As : List Formula) (A : Formula) -> A ∈ᶠ As ≡ true
           -> indexOf As A < length As
indexOf-ltF []       A ()
indexOf-ltF (B ∷ Bs) A e with B ≡ᶠ A
... | true  = ltZero
... | false = ltSuc (indexOf-ltF Bs A e)

------------------------------------------------------------------------
-- The atoms of a list of formulas.  Insertion keeps the list free of
-- duplicates: sub P repeats, and a repeated atom would double the truth table.

isAtomB : Formula -> Bool
isAtomB (var n) = true
isAtomB (¬ A)   = false
isAtomB (A ⇒ B) = false
isAtomB (○ A)   = true
isAtomB (□ A)   = true

insF : Formula -> List Formula -> List Formula
insF A Bs = filterCons (¬ᵇ (A ∈ᶠ Bs)) A Bs

insF-self : (A : Formula) (Bs : List Formula) -> A ∈ᶠ insF A Bs ≡ true
insF-self A Bs with A ∈ᶠ Bs in e
... | true  = e
... | false = ∨ᵇ-introˡ (A ≡ᶠ A) _ (≡ᶠ-refl A)

insF-mono : (A : Formula) (Bs : List Formula) (X : Formula)
         -> X ∈ᶠ Bs ≡ true -> X ∈ᶠ insF A Bs ≡ true
insF-mono A Bs X e with A ∈ᶠ Bs
... | true  = e
... | false = ∨ᵇ-introʳ (A ≡ᶠ X) (X ∈ᶠ Bs) e

atoms : List Formula -> List Formula
atoms []           = []
atoms (var n ∷ As) = insF (var n) (atoms As)
atoms (¬ A   ∷ As) = atoms As
atoms (A ⇒ B ∷ As) = atoms As
atoms (○ A   ∷ As) = insF (○ A) (atoms As)
atoms (□ A   ∷ As) = insF (□ A) (atoms As)

atomMem : (As : List Formula) {A : Formula} -> A ∈ As -> isAtomB A ≡ true
       -> A ∈ᶠ atoms As ≡ true
atomMem []           ()        e
atomMem (var n ∷ As) here      e = insF-self (var n) (atoms As)
atomMem (var n ∷ As) (there m) e = insF-mono (var n) (atoms As) _ (atomMem As m e)
atomMem (¬ B   ∷ As) here      ()
atomMem (¬ B   ∷ As) (there m) e = atomMem As m e
atomMem (B ⇒ C ∷ As) here      ()
atomMem (B ⇒ C ∷ As) (there m) e = atomMem As m e
atomMem (○ B   ∷ As) here      e = insF-self (○ B) (atoms As)
atomMem (○ B   ∷ As) (there m) e = insF-mono (○ B) (atoms As) _ (atomMem As m e)
atomMem (□ B   ∷ As) here      e = insF-self (□ B) (atoms As)
atomMem (□ B   ∷ As) (there m) e = insF-mono (□ B) (atoms As) _ (atomMem As m e)

------------------------------------------------------------------------
-- The arguments of the box-subformulas.
--
-- □Args collects the A for which □ A occurs in the list: these are the
-- eventualities.  It lives here, below Deriv, because both the elimination and
-- LTL.Procedures.CompletePC need it.

□Args : List Formula -> List Formula
□Args []           = []
□Args (var n ∷ As) = □Args As
□Args (¬ A   ∷ As) = □Args As
□Args (A ⇒ B ∷ As) = □Args As
□Args (○ A   ∷ As) = □Args As
□Args (□ A   ∷ As) = A ∷ □Args As

□Args-of : (As : List Formula) {A : Formula}
        -> □ A ∈ As -> A ∈ □Args As
□Args-of []           ()
□Args-of (var n ∷ As) (there m) = □Args-of As m
□Args-of (¬ B   ∷ As) (there m) = □Args-of As m
□Args-of (B ⇒ C ∷ As) (there m) = □Args-of As m
□Args-of (○ B   ∷ As) (there m) = □Args-of As m
□Args-of (□ B   ∷ As) here      = here
□Args-of (□ B   ∷ As) (there m) = there (□Args-of As m)

-- and back: the eventualities really are box-subformulas.

□Args-mem : (As : List Formula) {A : Formula}
         -> A ∈ □Args As -> □ A ∈ As
□Args-mem []           ()
□Args-mem (var n ∷ As) m         = there (□Args-mem As m)
□Args-mem (¬ B   ∷ As) m         = there (□Args-mem As m)
□Args-mem (B ⇒ C ∷ As) m         = there (□Args-mem As m)
□Args-mem (○ B   ∷ As) m         = there (□Args-mem As m)
□Args-mem (□ B   ∷ As) here      = here
□Args-mem (□ B   ∷ As) (there m) = there (□Args-mem As m)

------------------------------------------------------------------------
-- The skeleton evaluation.  valFrom Ats a A reads A with the bits a assigned
-- to the atoms Ats: ¬ and ⇒ are interpreted, everything else is looked up.

valFrom : List Formula -> Val -> Formula -> Bool
valFrom Ats a (var n) = bitAt a (indexOf Ats (var n))
valFrom Ats a (¬ A)   = ¬ᵇ valFrom Ats a A
valFrom Ats a (A ⇒ B) = valFrom Ats a A ⇒ᵇ valFrom Ats a B
valFrom Ats a (○ A)   = bitAt a (indexOf Ats (○ A))
valFrom Ats a (□ A)   = bitAt a (indexOf Ats (□ A))

------------------------------------------------------------------------
-- The skeleton evaluation agrees with any reading f that respects ¬ and ⇒ on
-- the subformulas of P.  Two instances are used: valOf at a state, where the
-- hypotheses are (S1) (LTL.States.Closure), and evalAt at a position, where
-- they hold by definition (LTL.Countermodel.OrbitEval).

atomLook : (f : Formula -> Bool) (Ats : List Formula) (X : Formula)
        -> X ∈ᶠ Ats ≡ true
        -> bitAt (map f Ats) (indexOf Ats X) ≡ f X
atomLook f Ats X mX =
  trans (nth-map f Ats (indexOf Ats X) (indexOf-ltF Ats X mX) ⊥ false)
        (cong f (indexOf-nthF Ats X mX))

skelEval : (f : Formula -> Bool) (Ats : List Formula) (P : Formula)
        -> ((X : Formula) -> X ∈ sub P -> isAtomB X ≡ true
              -> X ∈ᶠ Ats ≡ true)
        -> ((X : Formula) -> ¬ X ∈ sub P
              -> f (¬ X) ≡ ¬ᵇ f X)
        -> ((X Y : Formula) -> X ⇒ Y ∈ sub P
              -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
        -> (A : Formula) -> A ∈ sub P
        -> valFrom Ats (map f Ats) A ≡ f A
skelEval f Ats P at fn fi (var n) m = atomLook f Ats (var n) (at (var n) m refl)
skelEval f Ats P at fn fi (○ A)   m = atomLook f Ats (○ A) (at (○ A) m refl)
skelEval f Ats P at fn fi (□ A)   m = atomLook f Ats (□ A) (at (□ A) m refl)
skelEval f Ats P at fn fi (¬ A)   m =
  trans (cong ¬ᵇ_ (skelEval f Ats P at fn fi A (sub-¬ P m)))
        (sym (fn A m))
skelEval f Ats P at fn fi (A ⇒ B) m =
  trans (cong₂ _⇒ᵇ_ (skelEval f Ats P at fn fi A (sub-⇒L P m))
                    (skelEval f Ats P at fn fi B (sub-⇒R P m)))
        (sym (fi A B m))

------------------------------------------------------------------------
-- (PC), as a decidable condition on A alone

atomsOf : Formula -> List Formula
atomsOf A = atoms (sub A)

isTaut : Formula -> Bool
isTaut A = all (λ a -> valFrom (atomsOf A) a A)
               (allVecs (length (atomsOf A)))

-- and its soundness: any compositional reading of a skeleton tautology is true

tautSound : (f : Formula -> Bool) (A : Formula)
         -> ((X : Formula) -> ¬ X ∈ sub A
               -> f (¬ X) ≡ ¬ᵇ f X)
         -> ((X Y : Formula) -> X ⇒ Y ∈ sub A
               -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
         -> isTaut A ≡ true -> f A ≡ true
tautSound f A fn fi e =
  trans (sym (skelEval f (atomsOf A) A
                       (λ X mX aX -> atomMem (sub A) mX aX) fn fi A
                       (sub-self A)))
        (all-at (λ a -> valFrom (atomsOf A) a A)
                (allVecs (length (atomsOf A)))
                (allVecs-complete (length (atomsOf A)) (map f (atomsOf A))
                                  (map-length f (atomsOf A)))
                e)

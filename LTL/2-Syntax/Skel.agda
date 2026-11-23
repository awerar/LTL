{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.2-Syntax.Skel -- the propositional skeleton of a formula, and the
-- decidable tautology test isTaut that the (PC) rule of LTL.2-Syntax.Deriv uses.
--
-- A formula is a tautology of its skeleton when it is true in every row of the
-- truth table that treats its var, ○ and □ subformulas as atoms.  This is a
-- Boolean condition on the formula alone, so (PC) needs no substitution
-- relation.
--
-- valFrom reads a formula from an assignment to atoms.  A state of
-- LTL.5-States.State is such an assignment to the atoms of sub P, and valOf is
-- valFrom.  skelEval says valFrom agrees with any reading that is
-- compositional on ¬ and ⇒; tautSound applies it at a lasso position for the
-- soundness of (PC), and LTL.5-States.Taut at a row of a tautology's table.

module LTL.2-Syntax.Skel where

open import LTL.2-Syntax.Formula public
open import LTL.1-Lib.Sets using (filter-sub)

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

-- and every member of allVecs n has length n

consAll-len : {n : Nat} (b : Bool) (vs : List Val)
           -> (∀[ w ∈ vs ] length w ≡ n)
           -> ∀[ v ∈ map (λ bs -> b ∷ bs) vs ] length v ≡ suc n
consAll-len b (w ∷ ws) h v here      = cong suc (h w here)
consAll-len b (w ∷ ws) h v (there m) =
  consAll-len b ws (λ u mu -> h u (there mu)) v m

allVecs-len : (n : Nat) -> ∀[ v ∈ allVecs n ] length v ≡ n
allVecs-len zero    v here       = refl
allVecs-len zero    v (there ())
allVecs-len (suc n) v m =
  sumElim (consAll-len true  (allVecs n) (allVecs-len n) v)
          (consAll-len false (allVecs n) (allVecs-len n) v)
          (memAppCase (map (λ bs -> true  ∷ bs) (allVecs n))
                      (map (λ bs -> false ∷ bs) (allVecs n)) m)

------------------------------------------------------------------------
-- Lookup by first occurrence.  A member's first index is in range and
-- carries it.

indexOfCons : Bool -> Nat -> Nat
indexOfCons true  n = zero
indexOfCons false n = suc n

indexOf : List Formula -> Formula -> Nat
indexOf []       A = zero
indexOf (B ∷ Bs) A = indexOfCons (B ≡ᶠ A) (indexOf Bs A)

indexOf-lt : (xs : List Formula) -> ∀ⁱ[ X ∈ xs ] indexOf xs X < length xs
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

indexOf-nth : (xs : List Formula)
           -> ∀ⁱ[ X ∈ xs ] nth xs (indexOf xs X) ⊥ ≡ X
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
-- A list of formulas without repetition, keeping first occurrences.  sub P
-- repeats formulas; nub gives the set it stands for.

nub : List Formula -> List Formula
nub []       = []
nub (A ∷ As) = A ∷ filter (λ B -> ¬ᵇ (A ≡ᶠ B)) (nub As)

nub-mem : (As : List Formula) -> ∀ⁱ[ X ∈ As ] X ∈ nub As
nub-mem []       ()
nub-mem (A ∷ As) here = here
nub-mem (A ∷ As) {X} (there m) with A ≡ᶠ X in e
... | true  = subst (λ Y -> Y ∈ nub (A ∷ As)) (≡ᶠ-sound A X e) here
... | false = there (filter-true (λ B -> ¬ᵇ (A ≡ᶠ B)) (nub As)
                                 (nub-mem As m) (cong ¬ᵇ_ e))

nub-sub : (As : List Formula) -> ∀ⁱ[ X ∈ nub As ] X ∈ As
nub-sub []       ()
nub-sub (A ∷ As) here      = here
nub-sub (A ∷ As) (there m) =
  there (nub-sub As (filter-sub (λ B -> ¬ᵇ (A ≡ᶠ B)) (nub As) m))

------------------------------------------------------------------------
-- The atoms of a list of formulas: its var, ○ and □ entries, each once (a
-- repeated atom would double the truth table).

isAtomB : Formula -> Bool
isAtomB (var n) = true
isAtomB (¬ A)   = false
isAtomB (A ⇒ B) = false
isAtomB (○ A)   = true
isAtomB (□ A)   = true

atoms : List Formula -> List Formula
atoms As = filter isAtomB (nub As)

atomMem : (As : List Formula) {A : Formula} -> A ∈ As -> isAtomB A ≡ true
       -> A ∈ atoms As
atomMem As m e = filter-true isAtomB (nub As) (nub-mem As m) e

atomSub : (As : List Formula) -> ∀ⁱ[ A ∈ atoms As ] A ∈ As
atomSub As m = nub-sub As (filter-sub isAtomB (nub As) m)

------------------------------------------------------------------------
-- The arguments of the box-subformulas.
--
-- □Args collects the A for which □ A occurs in the list: these are the
-- eventualities.  LTL.5-States.State reads it at the atoms of sub P, so each
-- eventuality is listed once.

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

□Args-mem : (As : List Formula)
         -> ∀ⁱ[ A ∈ □Args As ] □ A ∈ As
□Args-mem []           ()
□Args-mem (var n ∷ As) m         = there (□Args-mem As m)
□Args-mem (¬ B   ∷ As) m         = there (□Args-mem As m)
□Args-mem (B ⇒ C ∷ As) m         = there (□Args-mem As m)
□Args-mem (○ B   ∷ As) m         = there (□Args-mem As m)
□Args-mem (□ B   ∷ As) here      = here
□Args-mem (□ B   ∷ As) (there m) = there (□Args-mem As m)

-- The arguments of the next-subformulas, likewise: (T1) is imposed at each.

○Args : List Formula -> List Formula
○Args []           = []
○Args (var n ∷ As) = ○Args As
○Args (¬ A   ∷ As) = ○Args As
○Args (A ⇒ B ∷ As) = ○Args As
○Args (○ A   ∷ As) = A ∷ ○Args As
○Args (□ A   ∷ As) = ○Args As

○Args-of : (As : List Formula) {A : Formula}
        -> ○ A ∈ As -> A ∈ ○Args As
○Args-of []           ()
○Args-of (var n ∷ As) (there m) = ○Args-of As m
○Args-of (¬ B   ∷ As) (there m) = ○Args-of As m
○Args-of (B ⇒ C ∷ As) (there m) = ○Args-of As m
○Args-of (○ B   ∷ As) here      = here
○Args-of (○ B   ∷ As) (there m) = there (○Args-of As m)
○Args-of (□ B   ∷ As) (there m) = ○Args-of As m

○Args-mem : (As : List Formula)
         -> ∀ⁱ[ A ∈ ○Args As ] ○ A ∈ As
○Args-mem []           ()
○Args-mem (var n ∷ As) m         = there (○Args-mem As m)
○Args-mem (¬ B   ∷ As) m         = there (○Args-mem As m)
○Args-mem (B ⇒ C ∷ As) m         = there (○Args-mem As m)
○Args-mem (○ B   ∷ As) here      = here
○Args-mem (○ B   ∷ As) (there m) = there (○Args-mem As m)
○Args-mem (□ B   ∷ As) m         = there (○Args-mem As m)

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
-- the subformulas of P.  Its instances, evalAt at a position (through
-- tautSound) and valFrom at another row (LTL.5-States.Taut), respect them by
-- definition.

atomLook : (f : Formula -> Bool) (Ats : List Formula) (X : Formula)
        -> X ∈ Ats
        -> bitAt (map f Ats) (indexOf Ats X) ≡ f X
atomLook f Ats X mX =
  trans (nth-map f Ats (indexOf Ats X) (indexOf-lt Ats mX) ⊥ false)
        (cong f (indexOf-nth Ats mX))

skelEval : (f : Formula -> Bool) (Ats : List Formula) (P : Formula)
        -> ((X : Formula) -> X ∈ sub P -> isAtomB X ≡ true -> X ∈ Ats)
        -> ((X : Formula) -> ¬ X ∈ sub P
              -> f (¬ X) ≡ ¬ᵇ f X)
        -> ((X Y : Formula) -> X ⇒ Y ∈ sub P
              -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
        -> ∀[ A ∈ sub P ] valFrom Ats (map f Ats) A ≡ f A
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

-- A formula true in every row passes the test.

isTaut-intro : (A : Formula) -> ((a : Val) -> valFrom (atomsOf A) a A ≡ true)
            -> isTaut A ≡ true
isTaut-intro A h =
  all-intro (λ a -> valFrom (atomsOf A) a A) (allVecs (length (atomsOf A)))
            (λ a m -> h a)

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
        (all-true (λ a -> valFrom (atomsOf A) a A)
                  (allVecs (length (atomsOf A))) e (map f (atomsOf A))
                  (allVecs-complete (length (atomsOf A)) (map f (atomsOf A))
                                    (map-length f (atomsOf A))))

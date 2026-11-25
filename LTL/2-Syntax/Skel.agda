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

------------------------------------------------------------------------
-- Valuations, as bit vectors, and their enumeration

Val : Set
Val = List Bool

allVals : Nat -> List Val
allVals zero    = [] ∷ []
allVals (suc n) = map (λ bs -> true ∷  bs) (allVals n) ++
                  map (λ bs -> false ∷ bs) (allVals n)

allVals-complete : (n : Nat) (v : Val) -> length v ≡ n -> v ∈ allVals n
allVals-complete zero    []           e  = here
allVals-complete zero    (b ∷ v)      ()
allVals-complete (suc n) []           ()
allVals-complete (suc n) (true  ∷ v)  e  =
  ∈-++⁺ˡ (map (λ bs -> true ∷ bs) (allVals n))
         (map (λ bs -> false ∷ bs) (allVals n))
         (∈-map⁺ (λ bs -> true ∷ bs) (allVals-complete n v (suc-injective e)))
allVals-complete (suc n) (false ∷ v)  e  =
  ∈-++⁺ʳ (map (λ bs -> true ∷ bs) (allVals n))
         (map (λ bs -> false ∷ bs) (allVals n))
         (∈-map⁺ (λ bs -> false ∷ bs) (allVals-complete n v (suc-injective e)))

-- and every member of allVals n has length n

consAll-len : {n : Nat} (b : Bool) (vs : List Val)
           -> (∀[ w ∈ vs ] length w ≡ n)
           -> ∀[ v ∈ map (λ bs -> b ∷ bs) vs ] length v ≡ suc n
consAll-len b (w ∷ ws) h v here      = cong suc (h w here)
consAll-len b (w ∷ ws) h v (there m) =
  consAll-len b ws (λ u mu -> h u (there mu)) v m

allVals-len : (n : Nat) -> ∀[ v ∈ allVals n ] length v ≡ n
allVals-len zero    v here       = refl
allVals-len zero    v (there ())
allVals-len (suc n) v m =
  [ consAll-len true  (allVals n) (allVals-len n) v
  , consAll-len false (allVals n) (allVals-len n) v
  ] (∈-++⁻ (map (λ bs -> true  ∷ bs) (allVals n))
           (map (λ bs -> false ∷ bs) (allVals n)) m)

------------------------------------------------------------------------
-- Lookup by first occurrence.  A member's first index is in range and
-- carries it.

indexOf : List Formula -> Formula -> Nat
indexOf []       A = zero
indexOf (B ∷ Bs) A = if B ≡ᶠ A then zero else suc (indexOf Bs A)

indexOf-< : (xs : List Formula) -> ∀ⁱ[ X ∈ xs ] indexOf xs X < length xs
indexOf-< []       ()
indexOf-< (B ∷ Bs) here     = aux (B ≡ᶠ B) (≡ᶠ-refl B)
  where
    aux : (b : Bool) -> b ≡ true -> (if b then zero else suc (indexOf Bs B)) < suc (length Bs)
    aux true  e  = z<s
    aux false ()
indexOf-< (B ∷ Bs) {X} (there m) = aux (B ≡ᶠ X)
  where
    aux : (b : Bool) -> (if b then zero else suc (indexOf Bs X)) < suc (length Bs)
    aux true  = z<s
    aux false = s<s (indexOf-< Bs m)

indexOf-nth : (xs : List Formula)
           -> ∀ⁱ[ X ∈ xs ] nth xs (indexOf xs X) ⊥ ≡ X
indexOf-nth []       ()
indexOf-nth (B ∷ Bs) here     = aux (B ≡ᶠ B) (≡ᶠ-refl B)
  where
    aux : (b : Bool) -> b ≡ true
       -> nth (B ∷ Bs) (if b then zero else suc (indexOf Bs B)) ⊥ ≡ B
    aux true  e  = refl
    aux false ()
indexOf-nth (B ∷ Bs) {X} (there m) = aux (B ≡ᶠ X) (≡ᶠ-sound B X)
  where
    aux : (b : Bool) -> (b ≡ true -> B ≡ X)
       -> nth (B ∷ Bs) (if b then zero else suc (indexOf Bs X)) ⊥ ≡ X
    aux true  f = f refl
    aux false f = indexOf-nth Bs m

------------------------------------------------------------------------
-- A list of formulas without repetition, keeping first occurrences.  sub P
-- repeats formulas; nub gives the set it stands for.

nub : List Formula -> List Formula
nub []       = []
nub (A ∷ As) = A ∷ filter (λ B -> ¬ᵇ (A ≡ᶠ B)) (nub As)

∈-nub⁺ : (As : List Formula) -> ∀ⁱ[ X ∈ As ] X ∈ nub As
∈-nub⁺ []       ()
∈-nub⁺ (A ∷ As) here = here
∈-nub⁺ (A ∷ As) {X} (there m) with A ≡ᶠ X in e
... | true  = subst (λ Y -> Y ∈ nub (A ∷ As)) (≡ᶠ-sound A X e) here
... | false = there (∈-filter⁺ (λ B -> ¬ᵇ (A ≡ᶠ B)) (nub As)
                               (∈-nub⁺ As m) (cong ¬ᵇ_ e))

nub-sub : (As : List Formula) -> ∀ⁱ[ X ∈ nub As ] X ∈ As
nub-sub []       ()
nub-sub (A ∷ As) here      = here
nub-sub (A ∷ As) (there m) =
  there (nub-sub As (∈-filter⁻ (λ B -> ¬ᵇ (A ≡ᶠ B)) (nub As) m))

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

∈-atoms⁺ : (As : List Formula) {A : Formula} -> A ∈ As -> isAtomB A ≡ true
        -> A ∈ atoms As
∈-atoms⁺ As m e = ∈-filter⁺ isAtomB (nub As) (∈-nub⁺ As m) e

atomSub : (As : List Formula) -> ∀ⁱ[ A ∈ atoms As ] A ∈ As
atomSub As m = nub-sub As (∈-filter⁻ isAtomB (nub As) m)

------------------------------------------------------------------------
-- The arguments of the box- and next-subformulas.
--
-- argsOf c As collects the A for which c A occurs in As.  At c = □_ these
-- are the eventualities, at c = ○_ the arguments (T1) is imposed at;
-- LTL.5-States.State reads both at the atoms of sub P, so each is listed
-- once.  argsAt c X keeps the immediate subformulas A of X with c A = X, so
-- the one equality test ≡ᶠ serves every connective.

children : Formula -> List Formula
children (var n) = []
children (¬ A)   = A ∷ []
children (A ⇒ B) = A ∷ B ∷ []
children (○ A)   = A ∷ []
children (□ A)   = A ∷ []

argsAt : (Formula -> Formula) -> Formula -> List Formula
argsAt c X = filter (λ A -> c A ≡ᶠ X) (children X)

argsOf : (Formula -> Formula) -> List Formula -> List Formula
argsOf c = concatMap (argsAt c)

∈-argsOf⁺ : (c : Formula -> Formula) (As : List Formula) {A : Formula}
         -> A ∈ children (c A) -> c A ∈ As -> A ∈ argsOf c As
∈-argsOf⁺ c As {A} ch m =
  ∈-concatMap⁺ (argsAt c) m
    (∈-filter⁺ (λ B -> c B ≡ᶠ c A) (children (c A)) ch (≡ᶠ-refl (c A)))

∈-argsOf⁻ : (c : Formula -> Formula) (As : List Formula)
         -> ∀ⁱ[ A ∈ argsOf c As ] c A ∈ As
∈-argsOf⁻ c As {A} m with ∈-concatMap⁻ (argsAt c) As m
... | X , mX , k =
  subst (λ Y -> Y ∈ As)
        (sym (≡ᶠ-sound (c A) X (filter-prop (λ B -> c B ≡ᶠ X) (children X) k)))
        mX

------------------------------------------------------------------------
-- The skeleton evaluation.  valFrom Ats a A reads A with the bits a assigned
-- to the atoms Ats: ¬ and ⇒ are interpreted, everything else is looked up.

module _ (Ats : List Formula) (a : Val) where

  -- The bit of the atom X: the entry of a at X's index in Ats.

  atomBit : Formula -> Bool
  atomBit X = nth a (indexOf Ats X) false

  valFrom : Formula -> Bool
  valFrom (var n) = atomBit (var n)
  valFrom (¬ A)   = ¬ᵇ valFrom A
  valFrom (A ⇒ B) = valFrom A ⇒ᵇ valFrom B
  valFrom (○ A)   = atomBit (○ A)
  valFrom (□ A)   = atomBit (□ A)

------------------------------------------------------------------------
-- The skeleton evaluation agrees with any reading f that respects ¬ and ⇒ on
-- the subformulas of P.  Its instances, evalAt at a position (through
-- tautSound) and valFrom at another row (LTL.5-States.Taut), respect them by
-- definition.

module _ (f : Formula -> Bool) (Ats : List Formula) where

  atomLook : ∀[ X ∈ Ats ] atomBit Ats (map f Ats) X ≡ f X
  atomLook X mX =
    trans (nth-map f Ats (indexOf Ats X) (indexOf-< Ats mX) ⊥ false)
          (cong f (indexOf-nth Ats mX))

  module _ (P : Formula)
           (at : ∀[ X ∈ sub P ] (isAtomB X ≡ true -> X ∈ Ats))
           (fn : (X : Formula) -> ¬ X ∈ sub P -> f (¬ X) ≡ ¬ᵇ f X)
           (fi : (X Y : Formula) -> X ⇒ Y ∈ sub P -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
           where

    skelEval : ∀[ A ∈ sub P ] valFrom Ats (map f Ats) A ≡ f A
    skelEval (var n) m = atomLook (var n) (at (var n) m refl)
    skelEval (○ A)   m = atomLook (○ A) (at (○ A) m refl)
    skelEval (□ A)   m = atomLook (□ A) (at (□ A) m refl)
    skelEval (¬ A)   m =
      trans (cong ¬ᵇ_ (skelEval A (sub-¬ P m))) (sym (fn A m))
    skelEval (A ⇒ B) m =
      trans (cong₂ _⇒ᵇ_ (skelEval A (sub-⇒L P m)) (skelEval B (sub-⇒R P m)))
            (sym (fi A B m))

------------------------------------------------------------------------
-- (PC), as a decidable condition on A alone

atomsOf : Formula -> List Formula
atomsOf A = atoms (sub A)

isTaut : Formula -> Bool
isTaut A = all (λ a -> valFrom (atomsOf A) a A)
               (allVals (length (atomsOf A)))

-- A formula true in every row passes the test.

isTaut-intro : (A : Formula) -> ((a : Val) -> valFrom (atomsOf A) a A ≡ true)
            -> isTaut A ≡ true
isTaut-intro A h =
  all-intro (λ a -> valFrom (atomsOf A) a A) (allVals (length (atomsOf A)))
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
                       (λ X mX aX -> ∈-atoms⁺ (sub A) mX aX) fn fi A
                       (sub-self A)))
        (all-true (λ a -> valFrom (atomsOf A) a A)
                  (allVals (length (atomsOf A))) e (map f (atomsOf A))
                  (allVals-complete (length (atomsOf A)) (map f (atomsOf A))
                                    (map-length f (atomsOf A))))

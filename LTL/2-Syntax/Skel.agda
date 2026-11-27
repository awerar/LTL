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
-- LTL.5-States.State is such an assignment to the atoms of P, and valOf is
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

-- and every member of allVals n has length n: it is b ∷ w with w in
-- allVals n.

allVals-len : (n : Nat) -> ∀[ v ∈ allVals n ] length v ≡ n
allVals-len zero    v here       = refl
allVals-len zero    v (there ())
allVals-len (suc n) v m =
  [ consLen true , consLen false ]
    (∈-++⁻ (map (λ bs -> true  ∷ bs) (allVals n))
           (map (λ bs -> false ∷ bs) (allVals n)) m)
  where
    consLen : (b : Bool) -> v ∈ map (λ bs -> b ∷ bs) (allVals n) -> length v ≡ suc n
    consLen b k with ∈-map⁻ (λ bs -> b ∷ bs) (allVals n) k
    ... | w , mw , refl = cong suc (allVals-len n w mw)

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
-- The atoms of a formula: the var, ○ and □ formulas in sub B, each once (a
-- repeated atom would double the truth table).  They include the atoms
-- nested under ○ and □, which a state of LTL.5-States.State needs, since it
-- gives every subformula a bit.

isAtom : Formula -> Bool
isAtom (var n) = true
isAtom (¬ A)   = false
isAtom (A ⇒ B) = false
isAtom (○ A)   = true
isAtom (□ A)   = true

atoms : Formula -> List Formula
atoms B = filter isAtom (nub (sub B))

∈-atoms⁺ : (B : Formula) -> ∀[ A ∈ sub B ] (isAtom A ≡ true -> A ∈ atoms B)
∈-atoms⁺ B A m e = ∈-filter⁺ isAtom (nub (sub B)) (∈-nub⁺ (sub B) m) e

atomSub : (B : Formula) -> ∀ⁱ[ A ∈ atoms B ] A ∈ sub B
atomSub B m = nub-sub (sub B) (∈-filter⁻ isAtom (nub (sub B)) m)

------------------------------------------------------------------------
-- The arguments of the box- and next-subformulas.
--
-- argsOf c As collects the A for which c A occurs in As.  At c = □_ these
-- are the eventualities, at c = ○_ the arguments (T1) is imposed at;
-- LTL.5-States.State reads both at the atoms of P, so each is listed
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
        (sym (≡ᶠ-sound (c A) X (filter-prop (λ B -> c B ≡ᶠ X) (children X) A k)))
        mX

------------------------------------------------------------------------
-- The skeleton evaluation.  valFrom Ats a A reads A with the bits a assigned
-- to the atoms Ats: ¬ and ⇒ are interpreted, everything else is looked up.

-- The bit of the atom X: the bit of a beside X's first occurrence in Ats, or
-- false if X is not among them.

atomBit : List Formula -> Val -> Formula -> Bool
atomBit []       a        X = false
atomBit (B ∷ Bs) []       X = false
atomBit (B ∷ Bs) (b ∷ bs) X = if B ≡ᶠ X then b else atomBit Bs bs X

module _ (Ats : List Formula) (a : Val) where

  valFrom : Formula -> Bool
  valFrom (var n) = atomBit Ats a (var n)
  valFrom (¬ A)   = ¬ᵇ valFrom A
  valFrom (A ⇒ B) = valFrom A ⇒ᵇ valFrom B
  valFrom (○ A)   = atomBit Ats a (○ A)
  valFrom (□ A)   = atomBit Ats a (□ A)

-- At an atom, valFrom is the lookup itself.

valFrom-atom : (Ats : List Formula) (a : Val) (X : Formula) -> isAtom X ≡ true
            -> valFrom Ats a X ≡ atomBit Ats a X
valFrom-atom Ats a (var n) e  = refl
valFrom-atom Ats a (¬ A)   ()
valFrom-atom Ats a (A ⇒ B) ()
valFrom-atom Ats a (○ A)   e  = refl
valFrom-atom Ats a (□ A)   e  = refl

------------------------------------------------------------------------
-- The skeleton evaluation in row a agrees with any reading f that respects ¬
-- and ⇒ on the subformulas of P, once it agrees with f on P's atoms.  Its
-- instances: evalAt at a position (tautSound), valFrom at another row
-- (LTL.5-States.Taut), both at the row map f (atoms P) (rowAt); and a state
-- read against a row that makes its chi true (LTL.5-States.Taut's chiReads).

module _ (f : Formula -> Bool) (Ats : List Formula) (a : Val) (P : Formula)
         (at : ∀[ X ∈ sub P ] (isAtom X ≡ true -> atomBit Ats a X ≡ f X))
         (fn : (X : Formula) -> ¬ X ∈ sub P -> f (¬ X) ≡ ¬ᵇ f X)
         (fi : (X Y : Formula) -> X ⇒ Y ∈ sub P -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
         where

  skelEval : ∀[ A ∈ sub P ] valFrom Ats a A ≡ f A
  skelEval (var n) m = at (var n) m refl
  skelEval (○ A)   m = at (○ A) m refl
  skelEval (□ A)   m = at (□ A) m refl
  skelEval (¬ A)   m =
    trans (cong ¬ᵇ_ (skelEval A (sub-¬ P m))) (sym (fn A m))
  skelEval (A ⇒ B) m =
    trans (cong₂ _⇒ᵇ_ (skelEval A (sub-⇒L P m)) (skelEval B (sub-⇒R P m)))
          (sym (fi A B m))

-- Reading the row map f Ats gives f back at each atom.  The first B equal to
-- X is X itself, by ≡ᶠ-sound.

atomLook : (f : Formula -> Bool) (Ats : List Formula)
        -> ∀[ X ∈ Ats ] atomBit Ats (map f Ats) X ≡ f X
atomLook f (B ∷ Bs) X m with B ≡ᶠ X in e
atomLook f (B ∷ Bs) X m         | true  = cong f (≡ᶠ-sound B X e)
atomLook f (B ∷ Bs) X here      | false = emptyElim (true≢false (trans (sym (≡ᶠ-refl B)) e))
atomLook f (B ∷ Bs) X (there m) | false = atomLook f Bs X m

-- So the row map f (atoms P) meets skelEval's hypothesis at.

rowAt : (f : Formula -> Bool) (P : Formula)
     -> ∀[ X ∈ sub P ] (isAtom X ≡ true -> atomBit (atoms P) (map f (atoms P)) X ≡ f X)
rowAt f P X m e = atomLook f (atoms P) X (∈-atoms⁺ P X m e)

------------------------------------------------------------------------
-- (PC), as a decidable condition on A alone

isTaut : Formula -> Bool
isTaut A = all (λ a -> valFrom (atoms A) a A)
               (allVals (length (atoms A)))

-- A formula true in every row passes the test.

isTaut-intro : (A : Formula) -> ((a : Val) -> valFrom (atoms A) a A ≡ true)
            -> isTaut A ≡ true
isTaut-intro A h =
  all-intro (λ a -> valFrom (atoms A) a A) (allVals (length (atoms A)))
            (λ a m -> h a)

-- and its soundness: any compositional reading of a skeleton tautology is true

tautSound : (f : Formula -> Bool) (A : Formula)
         -> ((X : Formula) -> ¬ X ∈ sub A
               -> f (¬ X) ≡ ¬ᵇ f X)
         -> ((X Y : Formula) -> X ⇒ Y ∈ sub A
               -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
         -> isTaut A ≡ true -> f A ≡ true
tautSound f A fn fi e =
  trans (sym (skelEval f (atoms A) (map f (atoms A)) A (rowAt f A) fn fi A
                       (sub-self A)))
        (all-true (λ a -> valFrom (atoms A) a A)
                  (allVals (length (atoms A))) e (map f (atoms A))
                  (allVals-complete (length (atoms A)) (map f (atoms A))
                                    (map-length f (atoms A))))

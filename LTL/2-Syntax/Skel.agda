{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.2-Syntax.Skel -- the propositional skeleton of a formula: its atoms,
-- rows of bits over them, and the decidable tautology test isTaut that the
-- (PC) rule of LTL.2-Syntax.Deriv uses.
--
-- There is one propositional evaluation, Statement's propValue: given a
-- reading ρ of the atoms (the var, ○ and □ formulas), it interprets ¬ and ⇒.
-- Everything else is a choice of ρ.  A row r : Row As holds one bit per atom
-- of As, and atomBit r reads it; a state of LTL.5-States.State is a row over
-- the atoms of P, and isTaut runs over the rows over the atoms of A.
-- propValue-cong says two readings that agree on the atoms of P agree on all
-- of sub P, and propValue-agree that a reading compositional on ¬ and ⇒ is
-- its own propValue.

module LTL.2-Syntax.Skel where

open import LTL.2-Syntax.Formula public
import LTL.Statement as S
open S public using (propValue; Tautology)

------------------------------------------------------------------------
-- Rows: one bit per member of a list of formulas, so a row's type says what
-- its bits are about.  The row of bits 1 0 over [ A , B ] is  true ▸ false ▸ ∅ .

infixr 5 _▸_

data Row : List Formula -> Set where
  ∅   : Row []
  _▸_ : {X : Formula} {As : List Formula} -> Bool -> Row As -> Row (X ∷ As)

-- The bit of X: the one beside X's first occurrence in As, or false if X is
-- not among them.

atomBit : {As : List Formula} -> Row As -> Formula -> Bool
atomBit {[]}     ∅        X = false
atomBit {B ∷ Bs} (b ▸ bs) X = if B ≡ᶠ X then b else atomBit bs X

-- The row that a reading ρ gives As, and atomBit reads ρ back from it.  The
-- first B equal to X is X itself, by ≡ᶠ-sound.

rowOf : (ρ : Formula -> Bool) (As : List Formula) -> Row As
rowOf ρ []       = ∅
rowOf ρ (X ∷ As) = ρ X ▸ rowOf ρ As

atomBit-rowOf : (ρ : Formula -> Bool) (As : List Formula)
             -> ∀[ X ∈ As ] atomBit (rowOf ρ As) X ≡ ρ X
atomBit-rowOf ρ (B ∷ Bs) X m with B ≡ᶠ X in e
atomBit-rowOf ρ (B ∷ Bs) X m         | true  = cong ρ (≡ᶠ-sound B X e)
atomBit-rowOf ρ (B ∷ Bs) X here      | false =
  emptyElim (true≢false (trans (sym (≡ᶠ-refl B)) e))
atomBit-rowOf ρ (B ∷ Bs) X (there m) | false = atomBit-rowOf ρ Bs X m

-- All the rows over As, the true-headed ones first: the truth table.

rows : (As : List Formula) -> List (Row As)
rows []       = ∅ ∷ []
rows (X ∷ As) = map (λ r -> true ▸ r) (rows As) ++ map (λ r -> false ▸ r) (rows As)

rows-complete : (As : List Formula) (r : Row As) -> r ∈ rows As
rows-complete []       ∅           = here
rows-complete (X ∷ As) (true  ▸ r) =
  ∈-++⁺ˡ (map (λ r -> true ▸ r) (rows As)) (map (λ r -> false ▸ r) (rows As))
         (∈-map⁺ (λ r -> true ▸ r) (rows-complete As r))
rows-complete (X ∷ As) (false ▸ r) =
  ∈-++⁺ʳ (map (λ r -> true ▸ r) (rows As)) (map (λ r -> false ▸ r) (rows As))
         (∈-map⁺ (λ r -> false ▸ r) (rows-complete As r))

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

atomIsAtom : (B : Formula) -> ∀ⁱ[ A ∈ atoms B ] isAtom A ≡ true
atomIsAtom B {A} m = filter-prop isAtom (nub (sub B)) A m

------------------------------------------------------------------------
-- The arguments of the □- and ○-formulas.  □Arg X is [ A ] when X is
-- □ A and [] otherwise, so concatMap □Arg over a list collects the A with
-- □ A in it: LTL.5-States.State's eventualities, read at the atoms of P so
-- each is listed once.  ○Arg is the same at ○, for the arguments (T1) is
-- imposed at.  The inversion lemmas are by pattern matching.

□Arg : Formula -> List Formula
□Arg (var n) = []
□Arg (¬ A)   = []
□Arg (A ⇒ B) = []
□Arg (○ A)   = []
□Arg (□ A)   = A ∷ []

□Arg-inv : (X : Formula) -> ∀ⁱ[ A ∈ □Arg X ] X ≡ □ A
□Arg-inv (var n) ()
□Arg-inv (¬ B)   ()
□Arg-inv (B ⇒ C) ()
□Arg-inv (○ B)   ()
□Arg-inv (□ B)   here       = refl
□Arg-inv (□ B)   (there ())

○Arg : Formula -> List Formula
○Arg (var n) = []
○Arg (¬ A)   = []
○Arg (A ⇒ B) = []
○Arg (○ A)   = A ∷ []
○Arg (□ A)   = []

○Arg-inv : (X : Formula) -> ∀ⁱ[ A ∈ ○Arg X ] X ≡ ○ A
○Arg-inv (var n) ()
○Arg-inv (¬ B)   ()
○Arg-inv (B ⇒ C) ()
○Arg-inv (○ B)   here       = refl
○Arg-inv (○ B)   (there ())
○Arg-inv (□ B)   ()

------------------------------------------------------------------------
-- The skeleton evaluation is propValue (LTL.Statement): ρ reads the atoms,
-- and ¬ and ⇒ are ¬ᵇ and ⇒ᵇ.  At an atom it is ρ itself.

propValue-atom : (ρ : Formula -> Bool) (X : Formula) -> isAtom X ≡ true
              -> propValue ρ X ≡ ρ X
propValue-atom ρ (var n) e  = refl
propValue-atom ρ (¬ A)   ()
propValue-atom ρ (A ⇒ B) ()
propValue-atom ρ (○ A)   e  = refl
propValue-atom ρ (□ A)   e  = refl

-- Two readings that agree on the atoms of P read every subformula of P alike.

module _ (ρ ρ' : Formula -> Bool) (P : Formula)
         (at : ∀[ X ∈ atoms P ] ρ X ≡ ρ' X) where

  propValue-cong : ∀[ A ∈ sub P ] propValue ρ A ≡ propValue ρ' A
  propValue-cong (var n) m = at (var n) (∈-atoms⁺ P (var n) m refl)
  propValue-cong (○ A)   m = at (○ A) (∈-atoms⁺ P (○ A) m refl)
  propValue-cong (□ A)   m = at (□ A) (∈-atoms⁺ P (□ A) m refl)
  propValue-cong (¬ A)   m = cong ¬ᵇ_ (propValue-cong A (sub-¬ P m))
  propValue-cong (A ⇒ B) m =
    cong₂ _⇒ᵇ_ (propValue-cong A (sub-⇒L P m)) (propValue-cong B (sub-⇒R P m))

-- So the row of ρ over P's atoms reads sub P as ρ does.

rowOf-reads : (ρ : Formula -> Bool) (P : Formula)
           -> ∀[ A ∈ sub P ] propValue (atomBit (rowOf ρ (atoms P))) A ≡ propValue ρ A
rowOf-reads ρ P =
  propValue-cong (atomBit (rowOf ρ (atoms P))) ρ P (atomBit-rowOf ρ (atoms P))

-- A reading f that is compositional on ¬ and ⇒ is propValue of itself.

module _ (f : Formula -> Bool)
         (fn : (X : Formula) -> f (¬ X) ≡ ¬ᵇ f X)
         (fi : (X Y : Formula) -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y) where

  propValue-agree : (A : Formula) -> propValue f A ≡ f A
  propValue-agree (var x) = refl
  propValue-agree (¬ A)   = trans (cong ¬ᵇ_ (propValue-agree A)) (sym (fn A))
  propValue-agree (A ⇒ B) =
    trans (cong₂ _⇒ᵇ_ (propValue-agree A) (propValue-agree B)) (sym (fi A B))
  propValue-agree (○ A)   = refl
  propValue-agree (□ A)   = refl

------------------------------------------------------------------------
-- (PC), as a decidable condition on A alone: A is true in every row of the
-- truth table over its atoms.  It is equivalent to Statement's Tautology:
-- every reading ρ is, on sub A, the row of ρ (rowOf-reads).

isTaut : Formula -> Bool
isTaut A = all (λ r -> propValue (atomBit r) A) (rows (atoms A))

isTaut-sound : (A : Formula) -> isTaut A ≡ true -> Tautology A
isTaut-sound A e ρ =
  trans (sym (rowOf-reads ρ A A (sub-self A)))
        (all-true (λ r -> propValue (atomBit r) A) (rows (atoms A)) e
                  (rowOf ρ (atoms A)) (rows-complete (atoms A) (rowOf ρ (atoms A))))

isTaut-complete : (A : Formula) -> Tautology A -> isTaut A ≡ true
isTaut-complete A t =
  all-intro (λ r -> propValue (atomBit r) A) (rows (atoms A)) (λ r m -> t (atomBit r))

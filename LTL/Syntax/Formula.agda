{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Syntax.Formula -- G1 of FORMALISATION-PLAN.md.
--
-- The language of m4.tex section 1 (the datatype of LTL.Trusted): formulas
-- built from propositional variables (var n) by negation ¬, implication ⇒,
-- next ○ and always □.
-- Conjunction ∧, disjunction ∨, equivalence ⇔, eventually ◇ and the constants
-- ⊤ and ⊥ are abbreviations, exactly as in the note.  Implication is ⇒
-- rather than → because Agda reserves → for function types.
--
-- ≡ᶠ is decidable equality (Boolean-valued; the superscript names the type,
-- as in ≡ⁿ on Nat and ≡ᵛ on valuations).  It is used by the
-- duplicate-coherence clause of isState (G5) and by lookup (G4), so it is
-- proved sound and complete here once and for all.

module LTL.Syntax.Formula where

open import LTL.Lib.Prelude public

------------------------------------------------------------------------
-- Formulas
--
-- The datatype is LTL.Trusted's, so the decision procedures run on exactly the
-- formulas the trusted statement talks about and LTL.Correct needs no
-- translation.  Its constructors are re-exported with this development's
-- fixities, which place the abbreviations below between them: the prefix
-- operators bind tightest, then ∧, ∨, ⇒ and ⇔; so
-- □ A ⇒ A ∧ ○ □ A  is  (□ A) ⇒ (A ∧ (○ (□ A))).

open import LTL.Trusted public
  using (Formula; var)
  renaming (¬_ to infix 30 ¬_; _⇒_ to infixr 20 _⇒_;
            ○_ to infix 30 ○_; □_ to infix 30 □_)

infix  30 ◇_
infixr 22 _∧_
infixr 21 _∨_
infix  19 _⇔_

------------------------------------------------------------------------
-- Abbreviations (m4.tex section 1)

⊤ : Formula
⊤ = var zero ⇒ var zero

⊥ : Formula
⊥ = ¬ ⊤

_∨_ : Formula -> Formula -> Formula
A ∨ B = ¬ A ⇒ B

_∧_ : Formula -> Formula -> Formula
A ∧ B = ¬ (A ⇒ ¬ B)

_⇔_ : Formula -> Formula -> Formula
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)

◇_ : Formula -> Formula
◇ A = ¬ □ ¬ A

------------------------------------------------------------------------
-- Decidable equality.
--
-- All twenty-five cases are written out: --exact-split rejects a catch-all
-- clause overlapping the diagonal ones.

infix 4.5 _≡ᶠ_

_≡ᶠ_ : Formula -> Formula -> Bool
var n    ≡ᶠ var m   = n ≡ⁿ m
var n    ≡ᶠ ¬ B     = false
var n    ≡ᶠ (B ⇒ C) = false
var n    ≡ᶠ ○ B     = false
var n    ≡ᶠ □ B     = false

¬ A      ≡ᶠ var m   = false
¬ A      ≡ᶠ ¬ B     = A ≡ᶠ B
¬ A      ≡ᶠ (B ⇒ C) = false
¬ A      ≡ᶠ ○ B     = false
¬ A      ≡ᶠ □ B     = false

(A ⇒ A') ≡ᶠ var m   = false
(A ⇒ A') ≡ᶠ ¬ B     = false
(A ⇒ A') ≡ᶠ (B ⇒ C) = (A ≡ᶠ B) ∧ᵇ (A' ≡ᶠ C)
(A ⇒ A') ≡ᶠ ○ B     = false
(A ⇒ A') ≡ᶠ □ B     = false

○ A      ≡ᶠ var m   = false
○ A      ≡ᶠ ¬ B     = false
○ A      ≡ᶠ (B ⇒ C) = false
○ A      ≡ᶠ ○ B     = A ≡ᶠ B
○ A      ≡ᶠ □ B     = false

□ A      ≡ᶠ var m   = false
□ A      ≡ᶠ ¬ B     = false
□ A      ≡ᶠ (B ⇒ C) = false
□ A      ≡ᶠ ○ B     = false
□ A      ≡ᶠ □ B     = A ≡ᶠ B

------------------------------------------------------------------------
-- ≡ᶠ is reflexive, hence complete

≡ᶠ-refl : (A : Formula) -> A ≡ᶠ A ≡ true
≡ᶠ-refl (var n) = ≡ⁿ-refl n
≡ᶠ-refl (¬ A)   = ≡ᶠ-refl A
≡ᶠ-refl (A ⇒ B) = ∧ᵇ-intro (A ≡ᶠ A) (B ≡ᶠ B)
                           (≡ᶠ-refl A) (≡ᶠ-refl B)
≡ᶠ-refl (○ A)   = ≡ᶠ-refl A
≡ᶠ-refl (□ A)   = ≡ᶠ-refl A

≡ᶠ-complete : (A B : Formula) -> A ≡ B -> A ≡ᶠ B ≡ true
≡ᶠ-complete A B refl = ≡ᶠ-refl A

------------------------------------------------------------------------
-- ≡ᶠ is sound

≡ᶠ-sound : (A B : Formula) -> A ≡ᶠ B ≡ true -> A ≡ B
≡ᶠ-sound (var n)  (var m) p = cong var (≡ⁿ-sound n m p)
≡ᶠ-sound (var n)  (¬ B)   ()
≡ᶠ-sound (var n)  (B ⇒ C) ()
≡ᶠ-sound (var n)  (○ B)   ()
≡ᶠ-sound (var n)  (□ B)   ()

≡ᶠ-sound (¬ A)    (var m) ()
≡ᶠ-sound (¬ A)    (¬ B)   p = cong ¬_ (≡ᶠ-sound A B p)
≡ᶠ-sound (¬ A)    (B ⇒ C) ()
≡ᶠ-sound (¬ A)    (○ B)   ()
≡ᶠ-sound (¬ A)    (□ B)   ()

≡ᶠ-sound (A ⇒ A') (var m) ()
≡ᶠ-sound (A ⇒ A') (¬ B)   ()
≡ᶠ-sound (A ⇒ A') (B ⇒ C) p =
  ⇒Cong (≡ᶠ-sound A B (∧ᵇ-trueˡ (A ≡ᶠ B) (A' ≡ᶠ C) p))
        (≡ᶠ-sound A' C (∧ᵇ-trueʳ (A ≡ᶠ B) (A' ≡ᶠ C) p))
  where
    ⇒Cong : {X Y X' Y' : Formula} -> X ≡ Y -> X' ≡ Y' -> X ⇒ X' ≡ Y ⇒ Y'
    ⇒Cong refl refl = refl
≡ᶠ-sound (A ⇒ A') (○ B)   ()
≡ᶠ-sound (A ⇒ A') (□ B)   ()

≡ᶠ-sound (○ A)    (var m) ()
≡ᶠ-sound (○ A)    (¬ B)   ()
≡ᶠ-sound (○ A)    (B ⇒ C) ()
≡ᶠ-sound (○ A)    (○ B)   p = cong ○_ (≡ᶠ-sound A B p)
≡ᶠ-sound (○ A)    (□ B)   ()

≡ᶠ-sound (□ A)    (var m) ()
≡ᶠ-sound (□ A)    (¬ B)   ()
≡ᶠ-sound (□ A)    (B ⇒ C) ()
≡ᶠ-sound (□ A)    (○ B)   ()
≡ᶠ-sound (□ A)    (□ B)   p = cong □_ (≡ᶠ-sound A B p)

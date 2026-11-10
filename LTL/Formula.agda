{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Formula -- G1 of FORMALISATION-PLAN.md.
--
-- The language of m4.tex section 1: formulas built from propositional
-- variables (var n) by negation ¬, implication ⇒, next ○ and always □.
-- Conjunction ∧, disjunction ∨, equivalence ⇔, eventually ◇ and the constants
-- ⊤ and ⊥ are abbreviations, exactly as in the note.  Implication is ⇒
-- rather than → because Agda reserves → for function types.
--
-- formEq is decidable equality.  It is used by the duplicate-coherence clause
-- of isState (G5), by lookup (G4), and by the pigeonhole of G23, so it is
-- proved sound and complete here once and for all.

module LTL.Formula where

open import LTL.Prelude public

------------------------------------------------------------------------
-- Formulas

data Formula : Set where
  var : Nat -> Formula
  ¬_  : Formula -> Formula
  _⇒_ : Formula -> Formula -> Formula
  ○_  : Formula -> Formula
  □_  : Formula -> Formula

-- The prefix operators bind tightest, then ∧, ∨, ⇒ and ⇔; so
-- □ A ⇒ A ∧ ○ □ A  is  (□ A) ⇒ (A ∧ (○ (□ A))).
infix  30 ¬_ ○_ □_ ◇_
infixr 22 _∧_
infixr 21 _∨_
infixr 20 _⇒_
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

formEq : Formula -> Formula -> Bool
formEq (var n)  (var m) = natEq n m
formEq (var n)  (¬ B)   = false
formEq (var n)  (B ⇒ C) = false
formEq (var n)  (○ B)   = false
formEq (var n)  (□ B)   = false

formEq (¬ A)    (var m) = false
formEq (¬ A)    (¬ B)   = formEq A B
formEq (¬ A)    (B ⇒ C) = false
formEq (¬ A)    (○ B)   = false
formEq (¬ A)    (□ B)   = false

formEq (A ⇒ A') (var m) = false
formEq (A ⇒ A') (¬ B)   = false
formEq (A ⇒ A') (B ⇒ C) = boolAnd (formEq A B) (formEq A' C)
formEq (A ⇒ A') (○ B)   = false
formEq (A ⇒ A') (□ B)   = false

formEq (○ A)    (var m) = false
formEq (○ A)    (¬ B)   = false
formEq (○ A)    (B ⇒ C) = false
formEq (○ A)    (○ B)   = formEq A B
formEq (○ A)    (□ B)   = false

formEq (□ A)    (var m) = false
formEq (□ A)    (¬ B)   = false
formEq (□ A)    (B ⇒ C) = false
formEq (□ A)    (○ B)   = false
formEq (□ A)    (□ B)   = formEq A B

------------------------------------------------------------------------
-- formEq is reflexive, hence complete

formEq_refl : (A : Formula) -> Eq (formEq A A) true
formEq_refl (var n) = natEq_refl n
formEq_refl (¬ A)   = formEq_refl A
formEq_refl (A ⇒ B) = andIntro (formEq A A) (formEq B B)
                               (formEq_refl A) (formEq_refl B)
formEq_refl (○ A)   = formEq_refl A
formEq_refl (□ A)   = formEq_refl A

formEq_complete : (A B : Formula) -> Eq A B -> Eq (formEq A B) true
formEq_complete A B refl = formEq_refl A

------------------------------------------------------------------------
-- formEq is sound

formEq_sound : (A B : Formula) -> Eq (formEq A B) true -> Eq A B
formEq_sound (var n)  (var m) p = eqCong var (natEq_sound n m p)
formEq_sound (var n)  (¬ B)   ()
formEq_sound (var n)  (B ⇒ C) ()
formEq_sound (var n)  (○ B)   ()
formEq_sound (var n)  (□ B)   ()

formEq_sound (¬ A)    (var m) ()
formEq_sound (¬ A)    (¬ B)   p = eqCong ¬_ (formEq_sound A B p)
formEq_sound (¬ A)    (B ⇒ C) ()
formEq_sound (¬ A)    (○ B)   ()
formEq_sound (¬ A)    (□ B)   ()

formEq_sound (A ⇒ A') (var m) ()
formEq_sound (A ⇒ A') (¬ B)   ()
formEq_sound (A ⇒ A') (B ⇒ C) p =
  ⇒Cong (formEq_sound A B (andTrueL (formEq A B) (formEq A' C) p))
        (formEq_sound A' C (andTrueR (formEq A B) (formEq A' C) p))
  where
    ⇒Cong : {X Y X' Y' : Formula} -> Eq X Y -> Eq X' Y' -> Eq (X ⇒ X') (Y ⇒ Y')
    ⇒Cong refl refl = refl
formEq_sound (A ⇒ A') (○ B)   ()
formEq_sound (A ⇒ A') (□ B)   ()

formEq_sound (○ A)    (var m) ()
formEq_sound (○ A)    (¬ B)   ()
formEq_sound (○ A)    (B ⇒ C) ()
formEq_sound (○ A)    (○ B)   p = eqCong ○_ (formEq_sound A B p)
formEq_sound (○ A)    (□ B)   ()

formEq_sound (□ A)    (var m) ()
formEq_sound (□ A)    (¬ B)   ()
formEq_sound (□ A)    (B ⇒ C) ()
formEq_sound (□ A)    (○ B)   ()
formEq_sound (□ A)    (□ B)   p = eqCong □_ (formEq_sound A B p)

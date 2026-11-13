{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Deriv -- G3 of FORMALISATION-PLAN.md.
--
-- The system L of m4.tex section 1, as a plain inductive family: the eight
-- axiom schemes together with modus ponens and generalisation.  Replacing
-- Ben-Ari's (PC) by (P1)-(P3) is what makes that possible: no tautology checker
-- and no substitution relation are needed to say what a derivation is.
--
-- Phase 8 adds (PC) back as an ELEVENTH constructor, with a decidable side
-- condition on the formula itself and no substitution relation -- see below and
-- LTL.Skel.  Only LTL.CompletePC and LTL.ShortPC build pc nodes, so the
-- ten-constructor system is still what every lemma below them is proved in; pc
-- is there because it is what makes a certificate short, and LTL.Proofs
-- measures the difference.

module LTL.Deriv where

open import LTL.Skel public

-- ⊢ A  says that A is derivable in system L (⊢_L A in the note).  ⊢ binds
-- looser than every formula connective, so  ⊢ □ A ⇒ A  is  ⊢ (□ A ⇒ A).

infix 10 ⊢_

data ⊢_ : Formula -> Set where

  -- (P1)  A ⇒ (B ⇒ A)
  p1 : {A B : Formula}
    -> ⊢ A ⇒ B ⇒ A

  -- (P2)  (A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))
  p2 : {A B C : Formula}
    -> ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C

  -- (P3)  (¬ B ⇒ ¬ A) ⇒ (A ⇒ B)
  p3 : {A B : Formula}
    -> ⊢ (¬ B ⇒ ¬ A) ⇒ A ⇒ B

  -- (K □)  □ (A ⇒ B) ⇒ (□ A ⇒ □ B)
  k□ : {A B : Formula}
    -> ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B

  -- (K ○)  ○ (A ⇒ B) ⇒ (○ A ⇒ ○ B)
  k○ : {A B : Formula}
    -> ⊢ ○ (A ⇒ B) ⇒ ○ A ⇒ ○ B

  -- (Exp)  □ A ⇒ (A ∧ ○ A ∧ ○ □ A)
  exp : {A : Formula}
     -> ⊢ □ A ⇒ A ∧ ○ A ∧ ○ □ A

  -- (Ind)  □ (A ⇒ ○ A) ⇒ (A ⇒ □ A)
  ind : {A : Formula}
     -> ⊢ □ (A ⇒ ○ A) ⇒ A ⇒ □ A

  -- (Lin)  ○ ¬ A ⇔ ¬ ○ A
  lin : {A : Formula}
     -> ⊢ ○ ¬ A ⇔ ¬ ○ A

  -- (PC)  Ben-Ari's Axiom 0, without the substitution relation.
  --
  -- Definition 12.1 of benari.pdf takes "any substitution instance of a valid
  -- propositional formula".  m4.tex Remark 6.4 rejects that because it needs a
  -- tautology checker AND a substitution relation to say what a derivation is,
  -- and then a substitution lemma for soundness.  Only the first half is
  -- unavoidable: asking that A be a tautology OF ITS OWN SKELETON -- its var,
  -- ○ and □ subformulas taken as atoms -- picks out the same formulas, is a
  -- decidable condition on A alone, and keeps ⊢_ a plain inductive family.
  -- isTaut is that test (LTL.Skel), and soundness is tautSound.
  --
  -- Only LTL.CompletePC and LTL.ShortPC use it: (L0)-(L7) and everything above
  -- them are derived from (P1)-(P3) exactly as before, so the eleventh
  -- constructor is additive.  What it buys is the length of a certificate; see
  -- LTL.Proofs.
  pc : {A : Formula} -> isTaut A ≡ true -> ⊢ A

  -- modus ponens
  mp : {A B : Formula}
    -> ⊢ A ⇒ B -> ⊢ A -> ⊢ B

  -- generalisation
  gen : {A : Formula}
     -> ⊢ A -> ⊢ □ A

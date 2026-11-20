{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Syntax.Deriv -- derivability ⊢ A in the system L, as a plain inductive
-- family: eight axiom schemes, modus ponens, generalisation, and the optional
-- rule (PC).
--
-- Propositional reasoning uses (P1)-(P3), so everything in LTL.Rules is
-- derived without (PC).  (PC) is used only by LTL.Procedures.CompletePC and
-- LTL.Procedures.Decide, where it keeps the certificates short.

module LTL.Syntax.Deriv where

open import LTL.Syntax.Skel public

-- ⊢ A  says that A is derivable.  ⊢ binds looser than every formula
-- connective, so  ⊢ □ A ⇒ A  is  ⊢ (□ A ⇒ A).

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

  -- (PC)  any formula that is a tautology of its own skeleton: its var, ○ and
  -- □ subformulas taken as atoms (isTaut, LTL.Syntax.Skel).  The side
  -- condition is decidable and needs no substitution relation; soundness is
  -- tautSound.
  pc : {A : Formula} -> isTaut A ≡ true -> ⊢ A

  -- modus ponens
  mp : {A B : Formula}
    -> ⊢ A ⇒ B -> ⊢ A -> ⊢ B

  -- generalisation
  gen : {A : Formula}
     -> ⊢ A -> ⊢ □ A

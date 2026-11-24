{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.3-Rules.Temporal -- the derived temporal rules (D1)-(D6), and the list
-- forms of (D4) that the step lemma needs.
--
-- (D6) is the converse of the  □ A ⇒ A ∧ ○ □ A  half of (Exp).  The
-- refutation of non-states violating (S2) and the (T3) case of the step lemma
-- both rely on it.

module LTL.3-Rules.Temporal where

open import LTL.3-Rules.PropList public

-- The formulas the signatures below leave implicit.

private variable
  A B C : Formula

------------------------------------------------------------------------
-- Projecting the two biconditional axioms: linFwd and linBwd are the forward
-- and backward halves of (Lin).

linFwd : ⊢ ○ ¬ A ⇒ ¬ ○ A
linFwd = mp ∧Fst lin

linBwd : ⊢ ¬ ○ A ⇒ ○ ¬ A
linBwd = mp ∧Snd lin

□Elim : ⊢ □ A ⇒ A
□Elim = ⇒Trans exp ∧Fst

□○ : ⊢ □ A ⇒ ○ A
□○ = ⇒Trans exp (⇒Trans ∧Snd ∧Fst)

□○□ : ⊢ □ A ⇒ ○ □ A
□○□ = ⇒Trans exp (⇒Trans ∧Snd ∧Snd)

------------------------------------------------------------------------
-- (D1), (D2), (D3)

○Gen : ⊢ A -> ⊢ ○ A
○Gen d = mp □○ (gen d)

○Mono : ⊢ A ⇒ B -> ⊢ ○ A ⇒ ○ B
○Mono d = mp k○ (○Gen d)

□Mono : ⊢ A ⇒ B -> ⊢ □ A ⇒ □ B
□Mono d = mp k□ (gen d)

------------------------------------------------------------------------
-- ○ and ⊥

○⊤ : ⊢ ○ ⊤
○⊤ = ○Gen deriv⊤

○⊥ : ⊢ ○ ⊥ ⇒ ⊥
○⊥ = mpU (mpU (liftP (explode {○ ⊤} {⊥})) (liftP ○⊤)) linFwd

------------------------------------------------------------------------
-- (D4) for disjunction, binary.
--
-- A ∨ B is ¬ A ⇒ B, so the first direction is (K ○) composed with
-- the backward half of (Lin); the second is a case analysis on ○ A.

○∨1 : ⊢ ○ (A ∨ B) ⇒ ○ A ∨ ○ B
○∨1 = ⇒TransU (liftP linBwd) k○

○∨2 : ⊢ ○ A ∨ ○ B ⇒ ○ (A ∨ B)
○∨2 = caseU (liftP (○Mono explode)) (⇒TransU ⇒Refl (liftP (○Mono p1)))

------------------------------------------------------------------------
-- Monotonicity of ∨ in its second argument

∨MonoR : ⊢ A ⇒ B -> ⊢ C ∨ A ⇒ C ∨ B
∨MonoR d = mp p2 (liftP d)

------------------------------------------------------------------------
-- (D4) for disjunction, over a list.  The step lemma uses ○⋁L1 to pass from
-- ⊢ ○ (beta St) to ⊢ ⋁ (map ○_ (map chi St)), and ○⋁L2 to come back to
-- ⊢ chi v ⇒ ○ (beta (succs v)).

○⋁L1 : (As : List Formula)
    -> ⊢ ○ ⋁ As ⇒ ⋁ (map ○_ As)
○⋁L1 []       = ○⊥
○⋁L1 (A ∷ As) = ⇒Trans ○∨1 (∨MonoR (○⋁L1 As))

○⋁L2 : (As : List Formula)
    -> ⊢ ⋁ (map ○_ As) ⇒ ○ ⋁ As
○⋁L2 []       = exFalso
○⋁L2 (A ∷ As) = ⇒Trans (∨MonoR (○⋁L2 As)) ○∨2

------------------------------------------------------------------------
-- (D4) for conjunction, the direction (D6) needs.  ○ (A ∧ B) is ○ ¬ X with
-- X = A ⇒ ¬ B, which by (Lin) is ¬ ○ X; and ○ X with ○ A gives ○ ¬ B.

○∧Intro : {A B : Formula}
       -> ⊢ ○ A ∧ ○ B ⇒ ○ (A ∧ B)
○∧Intro {A} {B} = ⇒Trans (¬IntroU hB hNB) linBwd
  where
    P : Formula
    P = ○ A ∧ ○ B

    X : Formula
    X = A ⇒ ¬ B

    hB : ⊢ P ⇒ ○ X ⇒ ○ B
    hB = ⇒Trans ∧Snd p1

    hNB : ⊢ P ⇒ ○ X ⇒ ¬ ○ B
    hNB = ⇒TransU (mpU2 (liftP k○) (⇒Trans ∧Fst p1)) (liftP linFwd)

------------------------------------------------------------------------
-- (D5) and (D6)

indRule : ⊢ A ⇒ ○ A -> ⊢ A ⇒ □ A
indRule d = mp ind (gen d)

expConv : {A : Formula}
       -> ⊢ A ∧ ○ □ A ⇒ □ A
expConv {A} = ⇒Trans (indRule cTo○C) (□Mono ∧Fst)
  where
    cTo○C : ⊢ A ∧ ○ □ A ⇒ ○ (A ∧ ○ □ A)
    cTo○C = ⇒Trans (∧Pair (⇒Trans ∧Snd (○Mono □Elim))
                                (⇒Trans ∧Snd (○Mono □○□)))
                       ○∧Intro

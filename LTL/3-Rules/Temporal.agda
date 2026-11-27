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

-- Refuting a formula that implies a literal of ○ A and ○ of the opposite
-- literal of A, uniformly in the bit c.  It closes the (T1) case of the step
-- lemma.

refute○ : (c : Bool)
       -> ⊢ C ⇒ lit (○ A) (¬ᵇ c)
       -> ⊢ C ⇒ ○ (lit A c)
       -> ⊢ ¬ C
refute○ true  f g = refute g f
refute○ false f g = refute f (⇒Trans g linFwd)

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

○∨Split : ⊢ ○ (A ∨ B) ⇒ ○ A ∨ ○ B
○∨Split = ⇒TransU (liftP linBwd) k○

○∨Join : ⊢ ○ A ∨ ○ B ⇒ ○ (A ∨ B)
○∨Join = caseU (liftP (○Mono explode)) (⇒TransU ⇒Refl (liftP (○Mono p1)))

------------------------------------------------------------------------
-- (D4) for disjunction, over a list.  The step lemma uses ○⋁Split to pass from
-- ⊢ ○ (beta allStates) to ⊢ ⋁ (map ○_ (map chi allStates)), and ○⋁Join to
-- come back to ⊢ chi v ⇒ ○ (beta (succs v)).

○⋁Split : (As : List Formula)
    -> ⊢ ○ ⋁ As ⇒ ⋁ (map ○_ As)
○⋁Split []       = ○⊥
○⋁Split (A ∷ As) = ⇒Trans ○∨Split (∨MonoR (○⋁Split As))

○⋁Join : (As : List Formula)
    -> ⊢ ⋁ (map ○_ As) ⇒ ○ ⋁ As
○⋁Join []       = exFalso
○⋁Join (A ∷ As) = ⇒Trans (∨MonoR (○⋁Join As)) ○∨Join

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

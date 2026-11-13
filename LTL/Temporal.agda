{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Temporal -- G14 and G15 of FORMALISATION-PLAN.md.
--
-- Lemma 1.2 of m4.tex, the derived temporal rules (D1)-(D6), together with the
-- list forms of (D4) that Lemma 2.7 needs.
--
-- (D6) is the one to watch: it is the converse of the □ A ⇒ A ∧ ○ □ A
-- half of (Exp), and it is load-bearing twice over -- in Lemma 2.5, to refute
-- valuations violating (S2), and in Lemma 2.7, for the (T3) case.

module LTL.Temporal where

open import LTL.PropList public

------------------------------------------------------------------------
-- Projecting the two biconditional axioms: linFwd and linBwd are the forward
-- and backward halves of (Lin).

linFwd : {A : Formula} -> ⊢ ○ ¬ A ⇒ ¬ ○ A
linFwd = mp ∧Fst lin

linBwd : {A : Formula} -> ⊢ ¬ ○ A ⇒ ○ ¬ A
linBwd = mp ∧Snd lin

□Elim : {A : Formula} -> ⊢ □ A ⇒ A
□Elim = ⇒Trans exp ∧Fst

□○ : {A : Formula} -> ⊢ □ A ⇒ ○ A
□○ = ⇒Trans exp (⇒Trans ∧Snd ∧Fst)

□○□ : {A : Formula} -> ⊢ □ A ⇒ ○ □ A
□○□ = ⇒Trans exp (⇒Trans ∧Snd ∧Snd)

------------------------------------------------------------------------
-- (D1), (D2), (D3)

○Gen : {A : Formula} -> ⊢ A -> ⊢ ○ A
○Gen d = mp □○ (gen d)

○Mono : {A B : Formula} -> ⊢ A ⇒ B -> ⊢ ○ A ⇒ ○ B
○Mono d = mp k○ (○Gen d)

□Mono : {A B : Formula} -> ⊢ A ⇒ B -> ⊢ □ A ⇒ □ B
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

○∨1 : {A B : Formula}
   -> ⊢ ○ (A ∨ B) ⇒ ○ A ∨ ○ B
○∨1 = ⇒TransU (liftP linBwd) k○

○∨2 : {A B : Formula}
   -> ⊢ ○ A ∨ ○ B ⇒ ○ (A ∨ B)
○∨2 = caseU (liftP (○Mono explode)) (⇒TransU identP (liftP (○Mono p1)))

------------------------------------------------------------------------
-- Monotonicity of ∨ in its second argument

∨MonoR : {X Y Z : Formula}
      -> ⊢ X ⇒ Y -> ⊢ Z ∨ X ⇒ Z ∨ Y
∨MonoR d = mp p2 (liftP d)

------------------------------------------------------------------------
-- (D4) for disjunction, over a list.
--
-- These are what Lemma 2.7 uses at both ends: ○⋁L1 to pass from
-- |- ○ (beta St) to |- ⋁ (map ○_ (map chi St)), and ○⋁L2 to come
-- back to |- chi v ⇒ ○ (beta (succs v)).

○⋁L1 : (As : List Formula)
    -> ⊢ ○ ⋁ As ⇒ ⋁ (map ○_ As)
○⋁L1 []       = ○⊥
○⋁L1 (A ∷ As) = ⇒Trans ○∨1 (∨MonoR (○⋁L1 As))

○⋁L2 : (As : List Formula)
    -> ⊢ ⋁ (map ○_ As) ⇒ ○ ⋁ As
○⋁L2 []       = exFalso
○⋁L2 (A ∷ As) = ⇒Trans (∨MonoR (○⋁L2 As)) ○∨2

------------------------------------------------------------------------
-- (D4) for conjunction, the direction (D6) needs.
--
-- Derived without a formula-level conjunction introduction: ○ (A ∧ B) is
-- ○ ¬ X with X = A ⇒ ¬ B, which by (Lin) is ¬ ○ X, and
-- ○ X together with ○ A gives ○ ¬ B, hence ¬ ○ B.

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
-- G15 : (D5) and (D6)

indRule : {A : Formula}
       -> ⊢ A ⇒ ○ A -> ⊢ A ⇒ □ A
indRule d = mp ind (gen d)

expConv : {A : Formula}
       -> ⊢ A ∧ ○ □ A ⇒ □ A
expConv {A} = ⇒Trans (indRule cTo○C) (□Mono ∧Fst)
  where
    cTo○C : ⊢ A ∧ ○ □ A ⇒ ○ (A ∧ ○ □ A)
    cTo○C = ⇒Trans (∧Pair (⇒Trans ∧Snd (○Mono □Elim))
                                (⇒Trans ∧Snd (○Mono □○□)))
                       ○∧Intro

------------------------------------------------------------------------
-- The (S2) case of Lemma 2.5, now available.
--
-- A valuation with  □ A  in v but  A  not in v  is refuted by (Exp); this
-- completes the list of shapes begun in LTL.Prop.

□Case : {A C : Formula} -> ⊢ □ A ⇒ ¬ A ⇒ C
□Case = ⇒Trans □Elim explode

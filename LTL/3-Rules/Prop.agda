{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.3-Rules.Prop -- the derived propositional rules that need no lists:
-- (L1) identity and transitivity, (L7) ¬ A ⇒ A ⇒ B, (L3) explosion, (L0)
-- ⊥ ⇒ C, double negation and contraposition.
--
-- Everything comes from (P1)-(P3) by composition.  There is no deduction
-- theorem; hypothetical reasoning works under a fixed antecedent P with
--
--     ⇒Refl : ⊢ P ⇒ P
--     liftP : ⊢ A -> ⊢ P ⇒ A
--     mpU   : ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ A -> ⊢ P ⇒ B
--
-- A trailing U in a name (mpU, ⇒TransU, ¬IntroU, caseU, mpU2) marks a rule
-- that works under such an antecedent.

module LTL.3-Rules.Prop where

open import LTL.2-Syntax.Deriv public

-- The formulas the signatures below leave implicit.

private variable
  P A B C : Formula

------------------------------------------------------------------------
-- (L1)

-- I = SKK
⇒Refl : {A : Formula} -> ⊢ A ⇒ A
⇒Refl {A} = mp (mp p2 (p1 {A} {A ⇒ A})) (p1 {A} {A})

-- liftP puts a theorem under an antecedent: it is (P1) and modus ponens.
liftP : ⊢ A -> ⊢ P ⇒ A
liftP d = mp p1 d

⇒Trans : ⊢ A ⇒ B -> ⊢ B ⇒ C -> ⊢ A ⇒ C
⇒Trans f g = mp (mp p2 (liftP g)) f

------------------------------------------------------------------------
-- The imp-lifting combinators.  With ⇒Refl and liftP, mpU (modus ponens
-- under the antecedent P) replaces the deduction theorem.

mpU : ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ A -> ⊢ P ⇒ B
mpU f g = mp (mp p2 f) g

⇒TransU : ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ B ⇒ C
       -> ⊢ P ⇒ A ⇒ C
⇒TransU f g = mpU (mpU (liftP p2) (⇒Trans g p1)) f

⇒Swap : {A B C : Formula}
     -> ⊢ A ⇒ B ⇒ C -> ⊢ B ⇒ A ⇒ C
⇒Swap {A} {B} {C} f = mpU (liftP (mp p2 f)) (p1 {B} {A})

------------------------------------------------------------------------
-- (L7), then (L3)

-- (L7) first half; p1 is the second.  Non-states are refuted with it.
¬Elim : ⊢ ¬ A ⇒ A ⇒ B
¬Elim = ⇒Trans p1 p3

-- (L3): from A and ¬ A, anything (compare exFalso, from ⊥).
explode : ⊢ A ⇒ ¬ A ⇒ B
explode = ⇒Swap ¬Elim

------------------------------------------------------------------------
-- ⊤ and ⊥

deriv⊤ : ⊢ ⊤
deriv⊤ = ⇒Refl

-- Double negation: dne eliminates it, dni introduces it.  Under  ¬ ¬ A  we
-- have  ¬ A ⇒ ¬ ⊤  by ¬Elim, hence  ⊤ ⇒ A  by (P3), and ⊤ holds.

dne : {A : Formula} -> ⊢ ¬ ¬ A ⇒ A
dne {A} = mpU (⇒Trans (¬Elim {¬ A} {¬ ⊤}) (p3 {⊤} {A}))
              (liftP deriv⊤)

dni : {A : Formula} -> ⊢ A ⇒ ¬ ¬ A
dni {A} = mp (p3 {A} {¬ ¬ A}) (dne {¬ A})

-- (L0), second half: ⊥ is ¬ ⊤.
exFalso : ⊢ ⊥ ⇒ C
exFalso = mpU (¬Elim {⊤}) (liftP deriv⊤)

------------------------------------------------------------------------
-- Contraposition, used by caseU and ⋁Elim (LTL.3-Rules.PropList): pass
-- A ⇒ B  through double negation, then apply (P3).

contra : {A B : Formula} -> ⊢ (A ⇒ B) ⇒ ¬ B ⇒ ¬ A
contra {A} {B} = ⇒Trans dnMono (p3 {¬ B} {¬ A})
  where
    dnMono : ⊢ (A ⇒ B) ⇒ ¬ ¬ A ⇒ ¬ ¬ B
    dnMono = ⇒TransU (⇒TransU (liftP dne) ⇒Refl) (liftP dni)

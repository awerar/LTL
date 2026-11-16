{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Prop -- G9 and G10 of FORMALISATION-PLAN.md.
--
-- The list-free part of Lemma 1.1 of m4.tex: (L1), (L0), (L3), (L4), (L7).
--
-- Everything here comes from (P1), (P2), (P3) by composition.  There is no
-- deduction theorem and no tautology checker; hypothetical reasoning is done
-- by imp-lifting under a fixed antecedent P, with the three combinators
--
--     ⇒Refl : ⊢ P ⇒ P
--     liftP : ⊢ A -> ⊢ P ⇒ A
--     mpU   : ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ A -> ⊢ P ⇒ B
--
-- A trailing U in a name (mpU, ⇒TransU, ¬IntroU, caseU, mpU2) marks a rule that
-- works under such an antecedent.

module LTL.Prop where

open import LTL.Deriv public

------------------------------------------------------------------------
-- G9 : (L1)

-- I = SKK
⇒Refl : {A : Formula} -> ⊢ A ⇒ A
⇒Refl {A} = mp (mp p2 (p1 {A} {A ⇒ A})) (p1 {A} {A})

-- liftP puts a theorem under an antecedent: it is (P1) and modus ponens.
liftP : {P A : Formula} -> ⊢ A -> ⊢ P ⇒ A
liftP d = mp p1 d

⇒Trans : {A B C : Formula}
      -> ⊢ A ⇒ B -> ⊢ B ⇒ C -> ⊢ A ⇒ C
⇒Trans f g = mp (mp p2 (liftP g)) f

------------------------------------------------------------------------
-- The imp-lifting combinators.
--
-- With ⇒Refl and liftP, mpU -- modus ponens performed under the antecedent P
-- -- replaces the deduction theorem for every use below.

mpU : {P A B : Formula}
   -> ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ A -> ⊢ P ⇒ B
mpU f g = mp (mp p2 f) g

⇒TransU : {P A B C : Formula}
       -> ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ B ⇒ C
       -> ⊢ P ⇒ A ⇒ C
⇒TransU f g = mpU (mpU (liftP p2) (⇒Trans g p1)) f

⇒Swap : {A B C : Formula}
     -> ⊢ A ⇒ B ⇒ C -> ⊢ B ⇒ A ⇒ C
⇒Swap {A} {B} {C} f = mpU (liftP (mp p2 f)) (p1 {B} {A})

------------------------------------------------------------------------
-- G10 : (L7), then (L3), (L0), (L4)

-- (L7) first half.  This is what the  v (A ⇒ B) = 0  case of Lemma 2.5
-- needs, together with p1 as its second half.
¬Elim : {A B : Formula} -> ⊢ ¬ A ⇒ A ⇒ B
¬Elim = ⇒Trans p1 p3

-- (L3): from A and ¬ A, anything (compare exFalso, from ⊥).
explode : {A B : Formula} -> ⊢ A ⇒ ¬ A ⇒ B
explode = ⇒Swap ¬Elim

------------------------------------------------------------------------
-- ⊤ and ⊥

deriv⊤ : ⊢ ⊤
deriv⊤ = ⇒Refl

-- Double negation: dne eliminates it, dni introduces it.  dne comes first: under the antecedent  ¬ ¬ A  we
-- have  ¬ A ⇒ ¬ ⊤  by ¬Elim, hence  ⊤ ⇒ A  by (P3), and  ⊤  is
-- available, so A follows.

dne : {A : Formula} -> ⊢ ¬ ¬ A ⇒ A
dne {A} = mpU (⇒Trans (¬Elim {¬ A} {¬ ⊤}) (p3 {⊤} {A}))
              (liftP deriv⊤)

dni : {A : Formula} -> ⊢ A ⇒ ¬ ¬ A
dni {A} = mp (p3 {A} {¬ ¬ A}) (dne {¬ A})

-- (L0)
not⊥ : ⊢ ¬ ⊥
not⊥ = mp dni deriv⊤

exFalso : {C : Formula} -> ⊢ ⊥ ⇒ C
exFalso = mpU (¬Elim {⊤}) (liftP deriv⊤)

-- (L4).  Since  A ∨ B  is  ¬ A ⇒ B , excluded middle is reflexivity.
lem : {A : Formula} -> ⊢ A ∨ ¬ A
lem = ⇒Refl

------------------------------------------------------------------------
-- Contraposition, used by the disjunction lemmas of G12

dnMono : {A B : Formula}
      -> ⊢ (A ⇒ B) ⇒ ¬ ¬ A ⇒ ¬ ¬ B
dnMono = ⇒TransU (⇒TransU (liftP dne) ⇒Refl) (liftP dni)

contra : {A B : Formula} -> ⊢ (A ⇒ B) ⇒ ¬ B ⇒ ¬ A
contra {A} {B} = ⇒Trans dnMono (p3 {¬ B} {¬ A})

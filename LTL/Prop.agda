{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Prop -- G9 and G10 of FORMALISATION-PLAN.md.
--
-- The list-free part of Lemma 1.1 of m4.tex: (L1), (L0), (L3), (L4), (L7).
--
-- Everything here comes from (P1), (P2), (P3) by composition.  There is no
-- deduction theorem and no tautology checker; hypothetical reasoning is done
-- by imp-lifting under a fixed antecedent P, with the three combinators
--
--     identP : ⊢ P ⇒ P
--     liftP  : ⊢ A -> ⊢ P ⇒ A
--     mpU    : ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ A -> ⊢ P ⇒ B
--
-- which is the style of ~/CHWISTEK/T4/CARNEIRO-WITNESS-IMP-LIFTING.md.

module LTL.Prop where

open import LTL.Deriv public

------------------------------------------------------------------------
-- G9 : (L1)

-- I = SKK
⇒Refl : {A : Formula} -> ⊢ A ⇒ A
⇒Refl {A} = mp (mp p2 (p1 {A} {A ⇒ A})) (p1 {A} {A})

weaken : {A B : Formula} -> ⊢ B -> ⊢ A ⇒ B
weaken d = mp p1 d

⇒Trans : {A B C : Formula}
        -> ⊢ A ⇒ B -> ⊢ B ⇒ C -> ⊢ A ⇒ C
⇒Trans f g = mp (mp p2 (weaken g)) f

------------------------------------------------------------------------
-- The imp-lifting combinators.
--
-- identP and liftP are ⇒Refl and weaken under other names; mpU is modus
-- ponens performed under the antecedent P.  Together they replace the
-- deduction theorem for every use below.

identP : {P : Formula} -> ⊢ P ⇒ P
identP = ⇒Refl

liftP : {P A : Formula} -> ⊢ A -> ⊢ P ⇒ A
liftP = weaken

mpU : {P A B : Formula}
   -> ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ A -> ⊢ P ⇒ B
mpU f g = mp (mp p2 f) g

⇒TransU : {P A B C : Formula}
         -> ⊢ P ⇒ A ⇒ B -> ⊢ P ⇒ B ⇒ C
         -> ⊢ P ⇒ A ⇒ C
⇒TransU f g = mpU (mpU (liftP p2) (⇒Trans g p1)) f

⇒Swap : {A B C : Formula}
       -> ⊢ A ⇒ B ⇒ C -> ⊢ B ⇒ A ⇒ C
⇒Swap {A} {B} {C} f = mpU (weaken (mp p2 f)) (p1 {B} {A})

------------------------------------------------------------------------
-- G10 : (L7), then (L3), (L0), (L4)

-- (L7) first half.  This is what the  v (A ⇒ B) = 0  case of Lemma 2.5
-- needs, together with p1 as its second half.
¬Elim : {A B : Formula} -> ⊢ ¬ A ⇒ A ⇒ B
¬Elim = ⇒Trans p1 p3

⇒IntroL : {A B : Formula} -> ⊢ ¬ A ⇒ A ⇒ B
⇒IntroL = ¬Elim

⇒IntroR : {A B : Formula} -> ⊢ B ⇒ A ⇒ B
⇒IntroR = p1

-- (L3)
exf : {A B : Formula} -> ⊢ A ⇒ ¬ A ⇒ B
exf = ⇒Swap ¬Elim

------------------------------------------------------------------------
-- ⊤ and ⊥

deriv⊤ : ⊢ ⊤
deriv⊤ = ⇒Refl

-- Double negation.  dne comes first: under the antecedent  ¬ ¬ A  we
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
dnMono = ⇒TransU (⇒TransU (liftP dne) identP) (liftP dni)

contra : {A B : Formula} -> ⊢ (A ⇒ B) ⇒ ¬ B ⇒ ¬ A
contra {A} {B} = ⇒Trans dnMono (p3 {¬ B} {¬ A})

------------------------------------------------------------------------
-- Checkpoint C2.
--
-- Composition as a theorem rather than a rule -- a test that the three
-- combinators really do replace the deduction theorem.

⇒Comp : {A B C : Formula}
       -> ⊢ (A ⇒ B) ⇒ (B ⇒ C) ⇒ A ⇒ C
⇒Comp = ⇒Swap (⇒Trans p1 p2)

------------------------------------------------------------------------
-- The four propositional shapes required by Lemma 2.5 of m4.tex.
--
-- Lemma 2.5 refutes a valuation violating (S1) by exhibiting a contradiction
-- among finitely many conjuncts of chi_v.  Each violation has a fixed shape,
-- and each shape is a fixed scheme -- there is nothing here a tautology
-- checker would be needed for.  Listed with the violation they discharge:
--
--   ¬Case1  v (¬ A) = 1  and  v A = 1
--   ¬Case0  v (¬ A) = 0  and  v A = 0
--   ⇒Case1  v (A ⇒ B) = 1  but  v A = 1, v B = 0
--   ⇒Case0L v (A ⇒ B) = 0  but  v A = 0
--   ⇒Case0R v (A ⇒ B) = 0  but  v B = 1
--
-- The (S2) violation needs (Exp), so it belongs to Phase 3.

¬Case1 : {A C : Formula} -> ⊢ A ⇒ ¬ A ⇒ C
¬Case1 = exf

¬Case0 : {A C : Formula} -> ⊢ ¬ ¬ A ⇒ ¬ A ⇒ C
¬Case0 {A} {C} = ¬Elim {¬ A} {C}

⇒Case1 : {A B C : Formula}
        -> ⊢ (A ⇒ B) ⇒ A ⇒ ¬ B ⇒ C
⇒Case1 = ⇒TransU identP (liftP exf)

⇒Case0L : {A B C : Formula}
         -> ⊢ ¬ A ⇒ ¬ (A ⇒ B) ⇒ C
⇒Case0L = ⇒Trans ¬Elim exf

⇒Case0R : {A B C : Formula}
         -> ⊢ B ⇒ ¬ (A ⇒ B) ⇒ C
⇒Case0R = ⇒Trans p1 exf

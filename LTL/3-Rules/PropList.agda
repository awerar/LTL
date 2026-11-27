{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.3-Rules.PropList -- binary conjunction, case analysis, monotonicity
-- of ∨, and the list-indexed rules of (L5): ⋁ introduction and elimination.
--
-- ⋀ and ⋁ are from LTL.2-Syntax.Formula, with ⋀ [] = ⊤ and ⋁ [] = ⊥.  ⋁Elim
-- eliminates beta over a set of states (betaElim, LTL.5-States.Extract); its
-- step is caseU on the head disjunct.

module LTL.3-Rules.PropList where

open import LTL.3-Rules.Prop public

-- The formulas the signatures below leave implicit.

private variable
  P Q A B C : Formula
  X : Set

------------------------------------------------------------------------
-- Negation introduction under an antecedent: from  P ⇒ (C ⇒ B)  and
-- P ⇒ (C ⇒ ¬ B)  conclude  P ⇒ ¬ C.  Every refutation below uses it.

-- mpU2 is mpU under two antecedents P and Q.

mpU2 : ⊢ P ⇒ Q ⇒ A ⇒ B -> ⊢ P ⇒ Q ⇒ A
    -> ⊢ P ⇒ Q ⇒ B
mpU2 f g = mpU (mpU (liftP p2) f) g

¬IntroU : {P C B : Formula}
       -> ⊢ P ⇒ C ⇒ B -> ⊢ P ⇒ C ⇒ ¬ B
       -> ⊢ P ⇒ ¬ C
¬IntroU {P} {C} {B} f g =
  mpU (mpU (liftP (p3 {⊤} {¬ C}))
           (mpU2 (mpU2 (liftP (liftP (explode {B} {¬ ⊤})))
                       (⇒TransU (liftP dne) f))
                 (⇒TransU (liftP dne) g)))
      (liftP deriv⊤)

-- Refutation: a formula that implies both B and ¬ B is refuted.

refute : ⊢ C ⇒ B -> ⊢ C ⇒ ¬ B -> ⊢ ¬ C
refute f g = mp (¬IntroU (liftP f) (liftP g)) deriv⊤

------------------------------------------------------------------------
-- Binary conjunction.  A ∧ B is ¬ (A ⇒ ¬ B).

∧Fst : {A B : Formula} -> ⊢ A ∧ B ⇒ A
∧Fst {A} {B} = mp p3 (⇒Trans (¬Elim {A} {¬ B}) dni)

∧Snd : {A B : Formula} -> ⊢ A ∧ B ⇒ B
∧Snd {A} {B} = mp p3 (⇒Trans (p1 {¬ B} {A}) dni)

∧Pair : ⊢ C ⇒ A -> ⊢ C ⇒ B -> ⊢ C ⇒ A ∧ B
∧Pair f g = mp p3 (¬IntroU (liftP g) (⇒TransU (liftP f) dne))

-- Case analysis under an antecedent: from P ⇒ (X ⇒ Z) and P ⇒ (¬ X ⇒ Z)
-- conclude P ⇒ Z.  ⋁Elim and the (D4) disjunction lemmas of
-- LTL.3-Rules.Temporal use it.

caseU : {P X Z : Formula}
     -> ⊢ P ⇒ X ⇒ Z -> ⊢ P ⇒ ¬ X ⇒ Z
     -> ⊢ P ⇒ Z
caseU {P} {X} {Z} f g = ⇒Trans (¬IntroU h1 h2) dne
  where
    h1 : ⊢ P ⇒ ¬ Z ⇒ X
    h1 = ⇒TransU (mpU (liftP (contra {¬ X} {Z})) g) (liftP dne)

    h2 : ⊢ P ⇒ ¬ Z ⇒ ¬ X
    h2 = mpU (liftP (contra {X} {Z})) f

------------------------------------------------------------------------
-- Binary disjunction.  C ∨ A is ¬ C ⇒ A, so monotonicity in the second
-- disjunct is (P2) on a lifted derivation.

∨MonoR : ⊢ A ⇒ B -> ⊢ C ∨ A ⇒ C ∨ B
∨MonoR d = mp p2 (liftP d)

------------------------------------------------------------------------
-- (L5)

-- AllInto C As: every A in As implies C (⊢ A ⇒ C for each).

data AllInto (C : Formula) : List Formula -> Set where
  intoNil  : AllInto C []
  intoCons : {A : Formula} {As : List Formula}
          -> ⊢ A ⇒ C -> AllInto C As -> AllInto C (A ∷ As)

-- AllInto for a mapped list, one derivation of  f x ⇒ C  per x.  It walks
-- xs, so no inversion of  map f  is needed.

allInto-map : (f : X -> Formula) (xs : List X)
           -> (∀[ x ∈ xs ] ⊢ (f x) ⇒ C) -> AllInto C (map f xs)
allInto-map f []       h = intoNil
allInto-map f (x ∷ xs) h = intoCons (h x here) (allInto-map f xs (λ z m -> h z (there m)))

⋁Intro : (As : List Formula)
      -> A ∈ As -> ⊢ A ⇒ ⋁ As
⋁Intro []       ()
⋁Intro (B ∷ Bs) here      = explode
⋁Intro (B ∷ Bs) (there h) = ⇒Trans (⋁Intro Bs h) p1

-- ⋁ (A ∷ As) is  ¬ A ⇒ ⋁ As , so the cons case is caseU on A under that
-- antecedent: A gives C by the hypothesis, and ¬ A gives ⋁ As by ⇒Refl,
-- hence C by induction.

⋁Elim : (As : List Formula)
     -> AllInto C As -> ⊢ ⋁ As ⇒ C
⋁Elim []       intoNil         = exFalso
⋁Elim (A ∷ As) (intoCons d ds) =
  caseU (liftP d) (⇒TransU ⇒Refl (liftP (⋁Elim As ds)))

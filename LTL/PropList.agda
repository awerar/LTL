{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.PropList -- G11 and G12 of FORMALISATION-PLAN.md.
--
-- (L2) and (L5) of Lemma 1.1 of m4.tex: the only two schemes indexed by a
-- list.  ⋀ and ⋁ are from LTL.Val, with ⋀ [] = ⊤ and ⋁ [] = ⊥,
-- the convention fixed after Lemma 1.1 -- so the two clauses of (L5) at n = 0
-- are exactly the two clauses of (L0).
--
-- ⋁Elim is the workhorse of Phase 4: dropping refuted disjuncts, and taking
-- the disjunction over W in Theorem 4.1, are both instances of it.

module LTL.PropList where

open import LTL.Prop public
open import LTL.Val  public

------------------------------------------------------------------------
-- Negation introduction, lifted under an antecedent.
--
-- From  P ⇒ (C ⇒ B)  and  P ⇒ (C ⇒ ¬ B)  conclude  P ⇒ ¬ C.  Every
-- refutation below factors through this.

mpU2 : {P Q A B : Formula}
    -> ⊢ P ⇒ Q ⇒ A ⇒ B -> ⊢ P ⇒ Q ⇒ A
    -> ⊢ P ⇒ Q ⇒ B
mpU2 f g = mpU (mpU (liftP p2) f) g

¬IntroU : {P C B : Formula}
         -> ⊢ P ⇒ C ⇒ B -> ⊢ P ⇒ C ⇒ ¬ B
         -> ⊢ P ⇒ ¬ C
¬IntroU {P} {C} {B} f g =
  mpU (mpU (liftP (p3 {⊤} {¬ C}))
           (mpU2 (mpU2 (liftP (liftP (exf {B} {¬ ⊤})))
                       (⇒TransU (liftP dne) f))
                 (⇒TransU (liftP dne) g)))
      (liftP deriv⊤)

------------------------------------------------------------------------
-- Binary conjunction.  A ∧ B is ¬ (A ⇒ ¬ B).

∧Fst : {A B : Formula} -> ⊢ A ∧ B ⇒ A
∧Fst {A} {B} = mp p3 (⇒Trans (¬Elim {A} {¬ B}) dni)

∧Snd : {A B : Formula} -> ⊢ A ∧ B ⇒ B
∧Snd {A} {B} = mp p3 (⇒Trans (p1 {¬ B} {A}) dni)

∧Pair : {C A B : Formula}
       -> ⊢ C ⇒ A -> ⊢ C ⇒ B -> ⊢ C ⇒ A ∧ B
∧Pair f g = mp p3 (¬IntroU (liftP g) (⇒TransU (liftP f) dne))

-- Case analysis under an antecedent: from P ⇒ (X ⇒ Z) and P ⇒ (¬ X ⇒ Z)
-- conclude P ⇒ Z.  This is the cons case of ⋁Elim isolated, and it is what
-- the (D4) disjunction lemmas of Phase 3 need.

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
-- G11 : (L2)

data AllD (C : Formula) : List Formula -> Set where
  adNil  : AllD C []
  adCons : {A : Formula} {As : List Formula}
        -> ⊢ C ⇒ A -> AllD C As -> AllD C (A ∷ As)

allD_map : {C : Formula} (As : List Formula)
        -> ({A : Formula} -> A ∈ As -> ⊢ C ⇒ A) -> AllD C As
allD_map []       f = adNil
allD_map (A ∷ As) f = adCons (f here) (allD_map As (λ m -> f (there m)))

⋀Proj : {A : Formula} (As : List Formula)
        -> A ∈ As -> ⊢ ⋀ As ⇒ A
⋀Proj []       ()
⋀Proj (B ∷ Bs) here      = ∧Fst
⋀Proj (B ∷ Bs) (there h) = ⇒Trans ∧Snd (⋀Proj Bs h)

⋀Intro : {C : Formula} (As : List Formula)
         -> AllD C As -> ⊢ C ⇒ ⋀ As
⋀Intro []       adNil         = liftP deriv⊤
⋀Intro (A ∷ As) (adCons d ds) = ∧Pair d (⋀Intro As ds)

------------------------------------------------------------------------
-- G12 : (L5)

data AllI (C : Formula) : List Formula -> Set where
  aiNil  : AllI C []
  aiCons : {A : Formula} {As : List Formula}
        -> ⊢ A ⇒ C -> AllI C As -> AllI C (A ∷ As)

allI_map : {C : Formula} (As : List Formula)
        -> ({A : Formula} -> A ∈ As -> ⊢ A ⇒ C) -> AllI C As
allI_map []       f = aiNil
allI_map (A ∷ As) f = aiCons (f here) (allI_map As (λ m -> f (there m)))

⋁Intro : {A : Formula} (As : List Formula)
         -> A ∈ As -> ⊢ A ⇒ ⋁ As
⋁Intro []       ()
⋁Intro (B ∷ Bs) here      = exf
⋁Intro (B ∷ Bs) (there h) = ⇒Trans (⋁Intro Bs h) p1

-- The cons case is the classical one: under the antecedent
-- P = ¬ A ⇒ ⋁ As, contraposing the two hypotheses gives
-- ¬ C ⇒ A and ¬ C ⇒ ¬ A, hence ¬ ¬ C, hence C.

⋁Elim : {C : Formula} (As : List Formula)
        -> AllI C As -> ⊢ ⋁ As ⇒ C
⋁Elim []       aiNil         = exFalso
⋁Elim {C} (A ∷ As) (aiCons d ds) = ⇒Trans (¬IntroU h1 h2) dne
  where
    P : Formula
    P = ¬ A ⇒ ⋁ As

    hIH : ⊢ ⋁ As ⇒ C
    hIH = ⋁Elim As ds

    hNA : ⊢ P ⇒ ¬ A ⇒ C
    hNA = ⇒TransU identP (liftP hIH)

    h1 : ⊢ P ⇒ ¬ C ⇒ A
    h1 = ⇒TransU (mpU (liftP (contra {¬ A} {C})) hNA) (liftP dne)

    h2 : ⊢ P ⇒ ¬ C ⇒ ¬ A
    h2 = mpU (liftP (contra {A} {C})) (liftP d)

------------------------------------------------------------------------
-- Monotonicity of ⋁.
--
-- This is what "dropping the refuted disjuncts" comes to in Lemma 2.6 and
-- Lemma 2.7, and what step (ii) of Theorem 4.1 needs to pass from
-- beta (succs w) to B.

⋁Mono : (As Bs : List Formula)
        -> ({A : Formula} -> A ∈ As -> A ∈ Bs)
        -> ⊢ ⋁ As ⇒ ⋁ Bs
⋁Mono As Bs sb = ⋁Elim As (allI_map As (λ m -> ⋁Intro Bs (sb m)))

⋀Mono : (As Bs : List Formula)
        -> ({A : Formula} -> A ∈ Bs -> A ∈ As)
        -> ⊢ ⋀ As ⇒ ⋀ Bs
⋀Mono As Bs sb = ⋀Intro Bs (allD_map Bs (λ m -> ⋀Proj As (sb m)))

-- Dropping a single refuted disjunct.  Lemma 2.6 discharges the non-states
-- this way, and Lemma 2.7 the successors w with v not-> w.

⋁Drop : {A : Formula} (As : List Formula)
        -> ⊢ ¬ A -> ⊢ ⋁ (A ∷ As) ⇒ ⋁ As
⋁Drop {A} As d =
  ⋁Elim (A ∷ As)
           (aiCons (mp ¬Elim d) (allI_map As (λ m -> ⋁Intro As m)))

------------------------------------------------------------------------
-- G13 : (L6)
--
-- If  |- ⋁ Cs  then  |- ⋁ (splitOn A Cs) , where splitOn A Cs conjoins
-- each disjunct with A and, separately, with ¬ A.  This is the step of the
-- structural induction along Sub P in Lemma 2.6.

splitOn : Formula -> List Formula -> List Formula
splitOn A Cs = map (A ∧_) Cs ++ map (¬ A ∧_) Cs

-- From  ¬ (U ∧ C)  and C, conclude  ¬ U.  Both halves of splitD use it,
-- once at U := A and once at U := ¬ A.

∧¬L : {U C : Formula} -> ⊢ ¬ (U ∧ C) ⇒ C ⇒ ¬ U
∧¬L {U} {C} = ⇒TransU (liftP dni) (mpU (liftP (contra {U} {¬ C})) dne)

splitD : {A : Formula} (Cs : List Formula)
      -> ⊢ ⋁ Cs -> ⊢ ⋁ (splitOn A Cs)
splitD {A} Cs d = mp (⋁Elim Cs (allI_map Cs each)) d
  where
    Z : Formula
    Z = ⋁ (splitOn A Cs)

    each : {C : Formula} -> C ∈ Cs -> ⊢ C ⇒ Z
    each {C} m = ⇒Trans (¬IntroU h1 h2) dne
      where
        j1 : ⊢ A ∧ C ⇒ Z
        j1 = ⋁Intro (splitOn A Cs)
               (memAppL (map (A ∧_) Cs) (map (¬ A ∧_) Cs)
                        (memMap (A ∧_) m))

        j2 : ⊢ ¬ A ∧ C ⇒ Z
        j2 = ⋁Intro (splitOn A Cs)
               (memAppR (map (A ∧_) Cs) (map (¬ A ∧_) Cs)
                        (memMap (¬ A ∧_) m))

        -- ¬ Z gives ¬ (¬ A ∧ C), which with C gives ¬ ¬ A,
        -- hence A.
        h1 : ⊢ C ⇒ ¬ Z ⇒ A
        h1 = ⇒TransU (⇒TransU (liftP (mp contra j2))
                                  (⇒Swap (∧¬L {¬ A} {C})))
                       (liftP dne)

        -- ¬ Z gives ¬ (A ∧ C), which with C gives ¬ A.
        h2 : ⊢ C ⇒ ¬ Z ⇒ ¬ A
        h2 = ⇒TransU (liftP (mp contra j1))
                       (⇒Swap (∧¬L {A} {C}))

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Skel -- the propositional skeleton of a formula, and the decidable
-- tautology test that (PC) needs.
--
-- Ben-Ari's system (benari.pdf, Definition 12.1) takes as Axiom 0
--
--     PC     any substitution instance of a valid propositional formula
--
-- and then writes "PC" for every propositional step.  m4.tex Remark 6.4 rejects
-- it and uses (P1)-(P3) instead, on the ground that "substitution instance of a
-- propositional tautology" carries a side condition, so a formalisation would
-- have to define a tautology checker AND the substitution relation before it
-- can say what a derivation is, and then prove a substitution lemma to get
-- soundness.
--
-- Half of that objection is avoidable.  The substitution relation is not
-- needed: instead of asking whether A is an instance of a tautology, ask
-- whether A is a tautology OF ITS OWN SKELETON -- treat its var, nxt and box
-- subformulas as atoms and run the truth table.  That is the same class of
-- formulas, it is decidable, it is a boolean condition on A alone, and ⊢_
-- stays a plain inductive family.
--
-- The apparatus is already here.  atoms and valFrom were written for G30, where
-- mkV builds a state from an assignment to the atoms of Sub P; the skeleton
-- evaluation is that same function read as a truth-table row.  What this module
-- adds is skelEval, which says the skeleton evaluation agrees with ANY boolean
-- reading of formulas that is compositional on neg and imp -- and there are two
-- such readings in the development, valOf at a state (compositional by (S1))
-- and evalAt at a position (compositional by definition).  So one lemma serves
-- both LTL.Closure and the soundness of (PC).

module LTL.Skel where

open import LTL.Sub public

------------------------------------------------------------------------
-- Valuations, as bit vectors, and their enumeration

Val : Set
Val = List Bool

bitAt : Val -> Nat -> Bool
bitAt v i = nth v i false

allVecs : Nat -> List Val
allVecs zero    = [] ∷ []
allVecs (suc n) = map (λ bs -> true ∷  bs) (allVecs n) ++
                  map (λ bs -> false ∷ bs) (allVecs n)

allVecs_complete : (n : Nat) (v : Val) -> length v ≡ n -> v ∈ allVecs n
allVecs_complete zero    []           e  = here
allVecs_complete zero    (b ∷ v)      ()
allVecs_complete (suc n) []           ()
allVecs_complete (suc n) (true  ∷ v)  e  =
  memAppL (map (λ bs -> true ∷ bs) (allVecs n))
          (map (λ bs -> false ∷ bs) (allVecs n))
          (memMap (λ bs -> true ∷ bs) (allVecs_complete n v (sucInj e)))
allVecs_complete (suc n) (false ∷ v)  e  =
  memAppR (map (λ bs -> true ∷ bs) (allVecs n))
          (map (λ bs -> false ∷ bs) (allVecs n))
          (memMap (λ bs -> false ∷ bs) (allVecs_complete n v (sucInj e)))

------------------------------------------------------------------------
-- Lookup by first occurrence

idxCons : Bool -> Nat -> Nat
idxCons true  n = zero
idxCons false n = suc n

idx : List Formula -> Formula -> Nat
idx []       A = zero
idx (B ∷ Bs) A = idxCons (formEq B A) (idx Bs A)

------------------------------------------------------------------------
-- Conjunction over a list

allB : {A : Set} -> (A -> Bool) -> List A -> Bool
allB p []       = true
allB p (x ∷ xs) = p x ∧ᵇ allB p xs

allB_at : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
       -> x ∈ xs -> allB p xs ≡ true -> p x ≡ true
allB_at p []       ()        e
allB_at p (y ∷ ys) here      e = andTrueL (p y) (allB p ys) e
allB_at p (y ∷ ys) (there m) e = allB_at p ys m (andTrueR (p y) (allB p ys) e)

allB_intro : {A : Set} (p : A -> Bool) (xs : List A)
          -> ({x : A} -> x ∈ xs -> p x ≡ true) -> allB p xs ≡ true
allB_intro p []       f = refl
allB_intro p (y ∷ ys) f =
  andIntro (p y) (allB p ys) (f here) (allB_intro p ys (λ m -> f (there m)))

------------------------------------------------------------------------
-- Small list infrastructure

cong₂ : {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B}
      -> x ≡ x' -> y ≡ y' -> f x y ≡ f x' y'
cong₂ f refl refl = refl

map_length : {A B : Set} (f : A -> B) (xs : List A)
          -> length (map f xs) ≡ length xs
map_length f []       = refl
map_length f (x ∷ xs) = cong suc (map_length f xs)

nth_map : {A B : Set} (f : A -> B) (xs : List A) (i : Nat) -> i < length xs
       -> (d : A) (e : B) -> nth (map f xs) i e ≡ f (nth xs i d)
nth_map f []       i       ()        d e
nth_map f (x ∷ xs) zero    lt        d e = refl
nth_map f (x ∷ xs) (suc i) (ltSuc l) d e = nth_map f xs i l d e

------------------------------------------------------------------------
-- Formula membership as a boolean, and the idx/nth round-trip for it.
--
-- idx locates the FIRST occurrence of a formula by formEq, so this is the
-- round-trip of FORMALISATION-PLAN.md G2 once more, for lookup by formula
-- rather than by position.

memF : List Formula -> Formula -> Bool
memF []       A = false
memF (B ∷ Bs) A = formEq B A ∨ᵇ memF Bs A

memF_tail : (B : Formula) (Bs : List Formula) (A : Formula)
         -> memF (B ∷ Bs) A ≡ true -> formEq B A ≡ false
         -> memF Bs A ≡ true
memF_tail B Bs A e eb =
  sumElim (λ e1 -> emptyElim (tfAbs (trans (sym e1) eb)))
          (λ e2 -> e2) (orTrue (formEq B A) (memF Bs A) e)

idxF_nth : (As : List Formula) (A : Formula) -> memF As A ≡ true
        -> nth As (idx As A) ⊥ ≡ A
idxF_nth []       A ()
idxF_nth (B ∷ Bs) A e = go (formEq B A) refl
  where
    go : (b : Bool) -> formEq B A ≡ b
      -> nth (B ∷ Bs) (idxCons b (idx Bs A)) ⊥ ≡ A
    go true  eb = formEq_sound B A eb
    go false eb = idxF_nth Bs A (memF_tail B Bs A e eb)

idxF_lt : (As : List Formula) (A : Formula) -> memF As A ≡ true
       -> idx As A < length As
idxF_lt []       A ()
idxF_lt (B ∷ Bs) A e = go (formEq B A) refl
  where
    go : (b : Bool) -> formEq B A ≡ b
      -> idxCons b (idx Bs A) < suc (length Bs)
    go true  eb = ltZero
    go false eb = ltSuc (idxF_lt Bs A (memF_tail B Bs A e eb))

------------------------------------------------------------------------
-- The atoms of a list of formulas.
--
-- Insertion keeps the list free of formEq-duplicates: Sub P repeats (see
-- subBenAri_dup), and a repeated atom would double the truth table for nothing.

isAtomB : Formula -> Bool
isAtomB (var n)   = true
isAtomB (¬ A)   = false
isAtomB (A ⇒ B) = false
isAtomB (○ A)   = true
isAtomB (□ A)   = true

insF : Formula -> List Formula -> List Formula
insF A Bs = filterCons (¬ᵇ memF Bs A) A Bs

insF_self : (A : Formula) (Bs : List Formula) -> memF (insF A Bs) A ≡ true
insF_self A Bs = go (memF Bs A) refl
  where
    go : (b : Bool) -> memF Bs A ≡ b
      -> memF (filterCons (¬ᵇ b) A Bs) A ≡ true
    go true  e = e
    go false e = orL (formEq A A) (memF Bs A) (formEq_refl A)

insF_mono : (A : Formula) (Bs : List Formula) (X : Formula)
         -> memF Bs X ≡ true -> memF (insF A Bs) X ≡ true
insF_mono A Bs X e = go (memF Bs A) refl
  where
    go : (b : Bool) -> memF Bs A ≡ b
      -> memF (filterCons (¬ᵇ b) A Bs) X ≡ true
    go true  eb = e
    go false eb = orR (formEq A X) (memF Bs X) e

atoms : List Formula -> List Formula
atoms []             = []
atoms (var n   ∷ As) = insF (var n) (atoms As)
atoms (¬ A   ∷ As) = atoms As
atoms (A ⇒ B ∷ As) = atoms As
atoms (○ A   ∷ As) = insF (○ A) (atoms As)
atoms (□ A   ∷ As) = insF (□ A) (atoms As)

atomMem : (As : List Formula) {A : Formula} -> A ∈ As -> isAtomB A ≡ true
       -> memF (atoms As) A ≡ true
atomMem []             ()        e
atomMem (var n   ∷ As) here      e = insF_self (var n) (atoms As)
atomMem (var n   ∷ As) (there m) e = insF_mono (var n) (atoms As) _ (atomMem As m e)
atomMem (¬ B   ∷ As) here      ()
atomMem (¬ B   ∷ As) (there m) e = atomMem As m e
atomMem (B ⇒ C ∷ As) here      ()
atomMem (B ⇒ C ∷ As) (there m) e = atomMem As m e
atomMem (○ B   ∷ As) here      e = insF_self (○ B) (atoms As)
atomMem (○ B   ∷ As) (there m) e = insF_mono (○ B) (atoms As) _ (atomMem As m e)
atomMem (□ B   ∷ As) here      e = insF_self (□ B) (atoms As)
atomMem (□ B   ∷ As) (there m) e = insF_mono (□ B) (atoms As) _ (atomMem As m e)

------------------------------------------------------------------------
-- The arguments of the box-subformulas.
--
-- □Args collects the A for which □ A occurs in the list.  It lived in
-- LTL.Elim, which is where the eventualities are; it is here because Phase 9
-- needs it on the OTHER branch of the import graph -- the (S2) premise of the
-- short Lemma 2.6 (LTL.CompletePC) is a conjunction of  □ A -> A  over it,
-- and LTL.Complete cannot reach LTL.Elim.  It is a pure syntactic function of
-- a List Formula, so nothing but its position changes; □Args_mem stays in
-- LTL.Trace, which is the only place that needs it.

□Args : List Formula -> List Formula
□Args []             = []
□Args (var n   ∷ As) = □Args As
□Args (¬ A   ∷ As) = □Args As
□Args (A ⇒ B ∷ As) = □Args As
□Args (○ A   ∷ As) = □Args As
□Args (□ A   ∷ As) = A ∷ □Args As

□Args_of : (As : List Formula) {A : Formula}
          -> □ A ∈ As -> A ∈ □Args As
□Args_of []                ()
□Args_of (var n   ∷ As) (there m) = □Args_of As m
□Args_of (¬ B   ∷ As) (there m) = □Args_of As m
□Args_of (B ⇒ C ∷ As) (there m) = □Args_of As m
□Args_of (○ B   ∷ As) (there m) = □Args_of As m
□Args_of (□ B   ∷ As) here      = here
□Args_of (□ B   ∷ As) (there m) = there (□Args_of As m)

------------------------------------------------------------------------
-- The skeleton evaluation.
--
-- valFrom Ats a A reads A with the bits a assigned to the atoms Ats: neg and
-- imp are interpreted, everything else is looked up.  For G30 this builds a
-- state out of an assignment; here it is one row of a truth table.

valFrom : List Formula -> Val -> Formula -> Bool
valFrom Ats a (var n)   = bitAt a (idx Ats (var n))
valFrom Ats a (¬ A)   = ¬ᵇ valFrom Ats a A
valFrom Ats a (A ⇒ B) = valFrom Ats a A ⇒ᵇ valFrom Ats a B
valFrom Ats a (○ A)   = bitAt a (idx Ats (○ A))
valFrom Ats a (□ A)   = bitAt a (idx Ats (□ A))

------------------------------------------------------------------------
-- The skeleton evaluation agrees with any compositional reading.
--
-- f is an arbitrary assignment of booleans to formulas that respects neg and
-- imp on the subformulas of P.  Then reading A through f is the same as
-- reading it through the skeleton with the atoms interpreted by f.  Two
-- instances are used: valOf at a state, where the hypotheses are (S1) --
-- LTL.Closure -- and evalAt at a position, where they are refl, since evalAt is
-- DEFINED by ¬ᵇ and ⇒ᵇ at neg and imp -- LTL.Sound.

atomLook : (f : Formula -> Bool) (Ats : List Formula) (X : Formula)
        -> memF Ats X ≡ true
        -> bitAt (map f Ats) (idx Ats X) ≡ f X
atomLook f Ats X mX =
  trans (nth_map f Ats (idx Ats X) (idxF_lt Ats X mX) ⊥ false)
        (cong f (idxF_nth Ats X mX))

skelEval : (f : Formula -> Bool) (Ats : List Formula) (P : Formula)
        -> ((X : Formula) -> X ∈ sub P -> isAtomB X ≡ true
              -> memF Ats X ≡ true)
        -> ((X : Formula) -> ¬ X ∈ sub P
              -> f (¬ X) ≡ ¬ᵇ f X)
        -> ((X Y : Formula) -> X ⇒ Y ∈ sub P
              -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
        -> (A : Formula) -> A ∈ sub P
        -> valFrom Ats (map f Ats) A ≡ f A
skelEval f Ats P at fn fi (var n)   m = atomLook f Ats (var n) (at (var n) m refl)
skelEval f Ats P at fn fi (○ A)   m = atomLook f Ats (○ A) (at (○ A) m refl)
skelEval f Ats P at fn fi (□ A)   m = atomLook f Ats (□ A) (at (□ A) m refl)
skelEval f Ats P at fn fi (¬ A)   m =
  trans (cong ¬ᵇ_ (skelEval f Ats P at fn fi A (sub_¬ P m)))
        (sym (fn A m))
skelEval f Ats P at fn fi (A ⇒ B) m =
  trans (cong₂ _⇒ᵇ_ (skelEval f Ats P at fn fi A (sub_⇒L P m))
                    (skelEval f Ats P at fn fi B (sub_⇒R P m)))
        (sym (fi A B m))

------------------------------------------------------------------------
-- (PC), as a decidable condition on A alone

atomsOf : Formula -> List Formula
atomsOf A = atoms (sub A)

isTaut : Formula -> Bool
isTaut A = allB (λ a -> valFrom (atomsOf A) a A)
                (allVecs (length (atomsOf A)))

-- and its soundness: any compositional reading of a skeleton tautology is true

tautSound : (f : Formula -> Bool) (A : Formula)
         -> ((X : Formula) -> ¬ X ∈ sub A
               -> f (¬ X) ≡ ¬ᵇ f X)
         -> ((X Y : Formula) -> X ⇒ Y ∈ sub A
               -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
         -> isTaut A ≡ true -> f A ≡ true
tautSound f A fn fi e =
  trans (sym (skelEval f (atomsOf A) A
                       (λ X mX aX -> atomMem (sub A) mX aX) fn fi A
                       (sub_self A)))
        (allB_at (λ a -> valFrom (atomsOf A) a A)
                 (allVecs (length (atomsOf A)))
                 (allVecs_complete (length (atomsOf A)) (map f (atomsOf A))
                                   (map_length f (atomsOf A)))
                 e)

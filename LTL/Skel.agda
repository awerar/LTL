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

indexOfCons : Bool -> Nat -> Nat
indexOfCons true  n = zero
indexOfCons false n = suc n

indexOf : List Formula -> Formula -> Nat
indexOf []       A = zero
indexOf (B ∷ Bs) A = indexOfCons (B ≡ᶠ A) (indexOf Bs A)

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
-- indexOf locates the FIRST occurrence of a formula by ≡ᶠ, so this is the
-- round-trip of FORMALISATION-PLAN.md G2 once more, for lookup by formula
-- rather than by position.

infix 4.5 _∈ᶠ_

_∈ᶠ_ : Formula -> List Formula -> Bool
A ∈ᶠ      [] = false
A ∈ᶠ (B ∷ Bs) = (B ≡ᶠ A) ∨ᵇ (A ∈ᶠ Bs)

∈ᶠ-tail : (B : Formula) (Bs : List Formula) (A : Formula)
       -> A ∈ᶠ B ∷ Bs ≡ true -> B ≡ᶠ A ≡ false
       -> A ∈ᶠ Bs ≡ true
∈ᶠ-tail B Bs A e eb =
  sumElim (λ e1 -> emptyElim (true≢false (trans (sym e1) eb)))
          (λ e2 -> e2) (orTrue (B ≡ᶠ A) (A ∈ᶠ Bs) e)

-- (The F in indexOf_nthF, indexOf_ltF: from the Boolean A ∈ᶠ As, where
-- LTL.Proj's indexOf_nth, indexOf_lt start from a proof of A ∈ As.)

indexOf_nthF : (As : List Formula) (A : Formula) -> A ∈ᶠ As ≡ true
            -> nth As (indexOf As A) ⊥ ≡ A
indexOf_nthF []       A ()
indexOf_nthF (B ∷ Bs) A e = go (B ≡ᶠ A) refl
  where
    go : (b : Bool) -> B ≡ᶠ A ≡ b
      -> nth (B ∷ Bs) (indexOfCons b (indexOf Bs A)) ⊥ ≡ A
    go true  eb = ≡ᶠ-sound B A eb
    go false eb = indexOf_nthF Bs A (∈ᶠ-tail B Bs A e eb)

indexOf_ltF : (As : List Formula) (A : Formula) -> A ∈ᶠ As ≡ true
           -> indexOf As A < length As
indexOf_ltF []       A ()
indexOf_ltF (B ∷ Bs) A e = go (B ≡ᶠ A) refl
  where
    go : (b : Bool) -> B ≡ᶠ A ≡ b
      -> indexOfCons b (indexOf Bs A) < suc (length Bs)
    go true  eb = ltZero
    go false eb = ltSuc (indexOf_ltF Bs A (∈ᶠ-tail B Bs A e eb))

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
insF A Bs = filterCons (¬ᵇ (A ∈ᶠ Bs)) A Bs

insF_self : (A : Formula) (Bs : List Formula) -> A ∈ᶠ insF A Bs ≡ true
insF_self A Bs = go (A ∈ᶠ Bs) refl
  where
    go : (b : Bool) -> A ∈ᶠ Bs ≡ b
      -> A ∈ᶠ filterCons (¬ᵇ b) A Bs ≡ true
    go true  e = e
    go false e = orL (A ≡ᶠ A) (A ∈ᶠ Bs) (≡ᶠ-refl A)

insF_mono : (A : Formula) (Bs : List Formula) (X : Formula)
         -> X ∈ᶠ Bs ≡ true -> X ∈ᶠ insF A Bs ≡ true
insF_mono A Bs X e = go (A ∈ᶠ Bs) refl
  where
    go : (b : Bool) -> A ∈ᶠ Bs ≡ b
      -> X ∈ᶠ filterCons (¬ᵇ b) A Bs ≡ true
    go true  eb = e
    go false eb = orR (A ≡ᶠ X) (X ∈ᶠ Bs) e

atoms : List Formula -> List Formula
atoms []             = []
atoms (var n   ∷ As) = insF (var n) (atoms As)
atoms (¬ A   ∷ As) = atoms As
atoms (A ⇒ B ∷ As) = atoms As
atoms (○ A   ∷ As) = insF (○ A) (atoms As)
atoms (□ A   ∷ As) = insF (□ A) (atoms As)

atomMem : (As : List Formula) {A : Formula} -> A ∈ As -> isAtomB A ≡ true
       -> A ∈ᶠ atoms As ≡ true
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
valFrom Ats a (var n)   = bitAt a (indexOf Ats (var n))
valFrom Ats a (¬ A)   = ¬ᵇ valFrom Ats a A
valFrom Ats a (A ⇒ B) = valFrom Ats a A ⇒ᵇ valFrom Ats a B
valFrom Ats a (○ A)   = bitAt a (indexOf Ats (○ A))
valFrom Ats a (□ A)   = bitAt a (indexOf Ats (□ A))

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
        -> X ∈ᶠ Ats ≡ true
        -> bitAt (map f Ats) (indexOf Ats X) ≡ f X
atomLook f Ats X mX =
  trans (nth_map f Ats (indexOf Ats X) (indexOf_ltF Ats X mX) ⊥ false)
        (cong f (indexOf_nthF Ats X mX))

skelEval : (f : Formula -> Bool) (Ats : List Formula) (P : Formula)
        -> ((X : Formula) -> X ∈ sub P -> isAtomB X ≡ true
              -> X ∈ᶠ Ats ≡ true)
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
isTaut A = all (λ a -> valFrom (atomsOf A) a A)
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
        (all_at (λ a -> valFrom (atomsOf A) a A)
                (allVecs (length (atomsOf A)))
                (allVecs_complete (length (atomsOf A)) (map f (atomsOf A))
                                  (map_length f (atomsOf A)))
                e)

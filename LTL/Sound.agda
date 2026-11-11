{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sound -- G26 of FORMALISATION-PLAN.md.
--
--   "One checks by induction on derivations that |- C implies [[C]]_s = 1 at
--    every state of every lasso."                          -- m4.tex section 5
--
-- Ten constructors.  Six are Boolean tautologies of at most three variables,
-- written out by cases; (K ○) and (Lin) reduce to  z ⇒ᵇ z  because
-- evalAt commutes with nxt definitionally, both sides of (Lin) being
-- ¬ᵇ evalAt A (nextPos pos) on the nose.  That leaves four.
--
--   (K □)  is allB pointwise: the SAME orbit on both sides, so it is
--            allB_at then ⇒TrueB then allB_intro.
--
--   (Exp)    needs the orbit of pos to contain pos, its successor, and the
--            whole orbit of its successor.  All three are orbitIter, since
--            posIter 0, posIter 1 and posIter (suc t) all land in it.
--
--   (Ind)    is the only one with content, and it is the risk that section 3
--            of the plan ranked fourth.  Under  □ (A ⇒ ○ A)  and A at pos,
--            A holds at posIter t pos by induction on t -- the hypothesis is
--            available at posIter t pos because orbitIter puts it in the orbit
--            -- and every member of the orbit is a posIter t pos by
--            orbitOf_iter.  Twenty lines, no arithmetic.
--
--   (gen)    needs every position of an orbit to be VALID, so that the
--            induction hypothesis applies there.  That is orbitValid.
--
-- The evaluation is total on all formulas, not only on subformulas of P, which
-- is what lets this be stated for an arbitrary derivable C.

module LTL.Sound where

open import LTL.Eval public

------------------------------------------------------------------------
-- The Boolean tautologies behind (P1), (P2), (P3) and the identity

tp1 : (a b : Bool) -> a ⇒ᵇ b ⇒ᵇ a ≡ true
tp1 true  true  = refl
tp1 true  false = refl
tp1 false b     = refl

tp2 : (a b c : Bool)
   -> (a ⇒ᵇ b ⇒ᵇ c) ⇒ᵇ (a ⇒ᵇ b) ⇒ᵇ a ⇒ᵇ c ≡ true
tp2 true  true  true  = refl
tp2 true  true  false = refl
tp2 true  false true  = refl
tp2 true  false false = refl
tp2 false b     c     = refl

tp3 : (a b : Bool)
   -> (¬ᵇ b ⇒ᵇ ¬ᵇ a) ⇒ᵇ a ⇒ᵇ b ≡ true
tp3 true  true  = refl
tp3 true  false = refl
tp3 false true  = refl
tp3 false false = refl

tid : (a : Bool) -> a ⇒ᵇ a ≡ true
tid true  = refl
tid false = refl

------------------------------------------------------------------------
-- Conjunction, as (Exp) and (Lin) need it

∧True : (P : Formula) (c0 : Val) (c1 : List Val) (X Y : Formula) (pos : Pos)
       -> evalAt P c0 c1 X pos ≡ true -> evalAt P c0 c1 Y pos ≡ true
       -> evalAt P c0 c1 (X ∧ Y) pos ≡ true
∧True P c0 c1 X Y pos ex ey =
  aux (evalAt P c0 c1 X pos) (evalAt P c0 c1 Y pos) ex ey
  where
    aux : (x y : Bool) -> x ≡ true -> y ≡ true
       -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
    aux true  true  ex' ey' = refl
    aux true  false ex' ()
    aux false y     ()  ey'

------------------------------------------------------------------------
-- (K □)

□K : (P : Formula) (c0 : Val) (c1 : List Val) (A B : Formula) (pos : Pos)
    -> evalAt P c0 c1 (□ (A ⇒ B)) pos ≡ true
    -> evalAt P c0 c1 (□ A) pos ≡ true
    -> evalAt P c0 c1 (□ B) pos ≡ true
□K P c0 c1 A B pos e1 e2 =
  allB_intro (evalAt P c0 c1 B) (orbitOf c0 c1 pos)
    (λ {q} m -> ⇒TrueB (evalAt P c0 c1 A q) (evalAt P c0 c1 B q)
                         (allB_at (evalAt P c0 c1 (A ⇒ B)) (orbitOf c0 c1 pos) m e1)
                         (allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos) m e2))

------------------------------------------------------------------------
-- (Exp)

expSound : (P : Formula) (c0 : Val) (c1 : List Val) (A : Formula) (pos : Pos)
        -> evalAt P c0 c1 (□ A ⇒ A ∧ ○ A ∧ ○ □ A) pos ≡
           true
expSound P c0 c1 A pos =
  ⇒IntroB (evalAt P c0 c1 (□ A) pos)
            (evalAt P c0 c1 (A ∧ ○ A ∧ ○ □ A) pos) body
  where
    body : evalAt P c0 c1 (□ A) pos ≡ true
        -> evalAt P c0 c1 (A ∧ ○ A ∧ ○ □ A) pos ≡ true
    body eb =
      ∧True P c0 c1 A (○ A ∧ ○ □ A) pos
              (allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
                       (orbitIter c0 c1 zero pos) eb)
              (∧True P c0 c1 (○ A) (○ □ A) pos
                       (allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
                                (orbitIter c0 c1 (suc zero) pos) eb)
                       (allB_intro (evalAt P c0 c1 A)
                                   (orbitOf c0 c1 (nextPos c0 c1 pos))
                                   (λ {q} m ->
                                      allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
                                              (orbitSub c0 c1 pos q m) eb)))

------------------------------------------------------------------------
-- (Ind).
--
-- The forward induction the note leaves to "one checks": A propagates along
-- the run because the hypothesis is available at every stage of it, and the
-- orbit consists exactly of those stages.

indSound : (P : Formula) (c0 : Val) (c1 : List Val) (A : Formula) (pos : Pos)
        -> evalAt P c0 c1 (□ (A ⇒ ○ A) ⇒ A ⇒ □ A) pos ≡ true
indSound P c0 c1 A pos =
  ⇒IntroB (evalAt P c0 c1 (□ (A ⇒ ○ A)) pos)
            (evalAt P c0 c1 A pos ⇒ᵇ evalAt P c0 c1 (□ A) pos)
            (λ e1 -> ⇒IntroB (evalAt P c0 c1 A pos) (evalAt P c0 c1 (□ A) pos)
                               (body e1))
  where
    body : evalAt P c0 c1 (□ (A ⇒ ○ A)) pos ≡ true
        -> evalAt P c0 c1 A pos ≡ true
        -> evalAt P c0 c1 (□ A) pos ≡ true
    body e1 e2 =
      allB_intro (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
                 (λ {q} m -> fromIter q (orbitOf_iter c0 c1 pos q m))
      where
        along : (t : Nat) -> evalAt P c0 c1 A (posIter c0 c1 t pos) ≡ true
        along zero    = e2
        along (suc t) =
          subst (λ r -> evalAt P c0 c1 A r ≡ true)
                (sym (posIter_suc c0 c1 t pos))
                (⇒TrueB (evalAt P c0 c1 A (posIter c0 c1 t pos))
                          (evalAt P c0 c1 A
                                  (nextPos c0 c1 (posIter c0 c1 t pos)))
                          (allB_at (evalAt P c0 c1 (A ⇒ ○ A))
                                   (orbitOf c0 c1 pos)
                                   (orbitIter c0 c1 t pos) e1)
                          (along t))

        fromIter : (q : Pos) -> (Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q)
                -> evalAt P c0 c1 A q ≡ true
        fromIter q (t , et) =
          subst (λ r -> evalAt P c0 c1 A r ≡ true) et (along t)

------------------------------------------------------------------------
-- Soundness

sound : (P : Formula) (b c0 : Val) (c1 : List Val)
     -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
     -> {C : Formula} -> ⊢ C
     -> (pos : Pos) -> ValidPos P b pos
     -> evalAt P c0 c1 C pos ≡ true

sound P b c0 c1 mc0 wc stb (p1 {A} {B}) pos vp =
  tp1 (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos)

sound P b c0 c1 mc0 wc stb (p2 {A} {B} {C}) pos vp =
  tp2 (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos) (evalAt P c0 c1 C pos)

sound P b c0 c1 mc0 wc stb (p3 {A} {B}) pos vp =
  tp3 (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos)

sound P b c0 c1 mc0 wc stb (k□ {A} {B}) pos vp =
  ⇒IntroB (evalAt P c0 c1 (□ (A ⇒ B)) pos)
            (evalAt P c0 c1 (□ A) pos ⇒ᵇ evalAt P c0 c1 (□ B) pos)
            (λ e1 -> ⇒IntroB (evalAt P c0 c1 (□ A) pos)
                               (evalAt P c0 c1 (□ B) pos)
                               (λ e2 -> □K P c0 c1 A B pos e1 e2))

-- both sides are evalAt A (nextPos pos) ⇒ᵇ evalAt B (nextPos pos)
sound P b c0 c1 mc0 wc stb (k○ {A} {B}) pos vp =
  tid (evalAt P c0 c1 A (nextPos c0 c1 pos) ⇒ᵇ
       evalAt P c0 c1 B (nextPos c0 c1 pos))

sound P b c0 c1 mc0 wc stb (exp {A}) pos vp = expSound P c0 c1 A pos

sound P b c0 c1 mc0 wc stb (ind {A}) pos vp = indSound P c0 c1 A pos

-- ○ ¬ A and ¬ ○ A evaluate to the same Boolean, so both halves of
-- the biconditional are z ⇒ᵇ z
sound P b c0 c1 mc0 wc stb (lin {A}) pos vp =
  ∧True P c0 c1 (○ ¬ A ⇒ ¬ ○ A)
                  (¬ ○ A ⇒ ○ ¬ A) pos
          (tid (¬ᵇ evalAt P c0 c1 A (nextPos c0 c1 pos)))
          (tid (¬ᵇ evalAt P c0 c1 A (nextPos c0 c1 pos)))

-- (PC).  evalAt is DEFINED by ¬ᵇ at neg and by ⇒ᵇ at imp, so the two
-- compositionality hypotheses of tautSound are refl and the case is one line.
-- This is the whole of Ben-Ari's Axiom 0, and it is where the substitution
-- lemma that Remark 6.4 feared would have gone.
sound P b c0 c1 mc0 wc stb (pc {C} e) pos vp =
  tautSound (λ X -> evalAt P c0 c1 X pos) C (λ X m -> refl) (λ X Y m -> refl) e

sound P b c0 c1 mc0 wc stb (mp {A} {B} d e) pos vp =
  ⇒TrueB (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos)
           (sound P b c0 c1 mc0 wc stb d pos vp)
           (sound P b c0 c1 mc0 wc stb e pos vp)

sound P b c0 c1 mc0 wc stb (gen {A} d) pos vp =
  allB_intro (evalAt P c0 c1 A) (orbitOf c0 c1 pos)
             (λ {q} m -> sound P b c0 c1 mc0 wc stb d q
                               (orbitValid P b c0 c1 mc0 wc stb pos q vp m))

------------------------------------------------------------------------
-- Soundness on a run, at every stage

soundRun : (P : Formula) (v0 : Val) (r : Run P v0) {C : Formula} -> ⊢ C
        -> (i : Nat) -> eval P v0 r C i ≡ true
soundRun P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) d i =
  sound P b c0 c1 mc0 wc stb d
        (posIter c0 c1 i (v0 , rest))
        (posIterValid P b c0 c1 mc0 wc stb i (v0 , rest) (vpos v0 rest mv0 wr))

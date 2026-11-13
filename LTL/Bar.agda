{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Bar -- inductively finite sets, after Coquand and Siles, "A Decision
-- Procedure for Regular Expression Equivalence in Type Theory" (CPP 2011), §1.
--
--   Bar R E   holds when, starting from E and repeatedly picking an x and
--             passing to  E intersect (R x) , one always stops.
--
-- With R the complement of equality this says: one cannot go on choosing
-- DISTINCT elements of E forever.  That is exactly the principle the
-- development used to re-derive by hand, once per use, as a decreasing length.
-- Phase 8 (G29) replaces all of those by recursion on a Bar: shrinkGo
-- (LTL.Gfp), elimGo (LTL.Elim), lassoSearch (LTL.Lasso), and then closeGo
-- (LTL.Closure), which is G30 and which no length would have justified at all.
--
-- Subsets are taken DECIDABLE, as boolean predicates, rather than as
-- Prop-valued ones.  Everything this development quantifies over is decidable,
-- and it keeps Bar in Set rather than Set1.
--
-- This module is the generic half: Bar and its closure under union, product
-- and pullback, for any element type.  It imports only LTL.Sets, so the graph
-- layer (LTL.Graph) can use it at any node type.  The two suppliers of Bars
-- live elsewhere, and they are used for different things.
--
--   barOfList / listBar (LTL.Nodes) -- a Kuratowski finite list gives a
--     Bar.  Right when the search removes from a list that is already in hand
--     and whose length one is willing to pay for once: W_0 in LTL.Gfp, U_inf
--     in LTL.Lasso.
--
--   vecIFin / guardedVecBar (LTL.VecBar) -- the vectors of a given length
--     are inductively finite, by induction on the length, in O(n) rather than
--     2^n.  Right when there is no such list: the elimination, which is not to force
--     length (Ust P) merely to bound itself, and above all the closure of
--     LTL.Closure, which GROWS and so has no decreasing measure at all.
--
-- The second is the useful direction and the hard one: the paper notes that the
-- product lemma is essentially the proof that a product of well-quasi-orderings
-- is one.

module LTL.Bar where

open import LTL.Sets public

------------------------------------------------------------------------
-- Bar

data Bar {A : Set} (R : A -> A -> Bool) : (A -> Bool) -> Set where
  cBar : {E : A -> Bool}
      -> ((x : A) -> E x ≡ true
            -> Bar R (λ y -> E y ∧ᵇ R x y))
      -> Bar R E

-- The recursion principle.  Every "keep going until you run out" argument in
-- the development is this with a different C.
barRec : {A : Set} {R : A -> A -> Bool} (C : (A -> Bool) -> Set)
      -> ({E : A -> Bool}
            -> ((x : A) -> E x ≡ true -> C (λ y -> E y ∧ᵇ R x y))
            -> C E)
      -> {E : A -> Bool} -> Bar R E -> C E
barRec C f (cBar h) = f (λ x ex -> barRec C f (h x ex))

barStep : {A : Set} (R : A -> A -> Bool) (E F : A -> Bool)
       -> ((x : A) -> E x ≡ true -> F x ≡ true)
       -> (x y : A) -> E y ∧ᵇ R x y ≡ true
       -> F y ∧ᵇ R x y ≡ true
barStep R E F sb x y e =
  andIntro (F y) (R x y) (sb y (andTrueL (E y) (R x y) e))
                         (andTrueR (E y) (R x y) e)

barMono : {A : Set} {R : A -> A -> Bool} {E F : A -> Bool}
       -> ((x : A) -> E x ≡ true -> F x ≡ true)
       -> Bar R F -> Bar R E
barMono {R = R} {E = E} {F = F} sb (cBar h) =
  cBar (λ x ex -> barMono (barStep R E F sb x) (h x (sb x ex)))

------------------------------------------------------------------------
-- Boolean glue for the two closure lemmas

∧∨-distrib : (g h t : Bool) -> (g ∨ᵇ h) ∧ᵇ t ≡ true
          -> g ∧ᵇ t ∨ᵇ h ∧ᵇ t ≡ true
∧∨-distrib true  h true  e = refl
∧∨-distrib true  h false ()
∧∨-distrib false h t     e = e

∧∨-weaken : (g h t : Bool) -> (g ∨ᵇ h) ∧ᵇ t ≡ true
         -> g ∨ᵇ h ∧ᵇ t ≡ true
∧∨-weaken true  h t e = refl
∧∨-weaken false h t e = e

∧∨-split : (e f r s : Bool)
        -> (e ∧ᵇ f) ∧ᵇ (r ∨ᵇ s) ≡ true
        -> (e ∧ᵇ r) ∧ᵇ f ∨ᵇ e ∧ᵇ f ∧ᵇ s ≡ true
∧∨-split true  true  true  s h = refl
∧∨-split true  true  false s h = h
∧∨-split true  false r     s ()
∧∨-split false f     r     s ()

------------------------------------------------------------------------
-- Union.  Lemma 1, second bullet.
--
-- Double induction: on the first witness for the G-case, on the second for
-- the H-case.  barMono does the work that would otherwise need funext, since
-- Bar is indexed by the predicate and the two sides are only pointwise equal.

barUnion : {A : Set} {T : A -> A -> Bool} {G H : A -> Bool}
        -> Bar T G -> Bar T H -> Bar T (λ y -> G y ∨ᵇ H y)
barUnion {A} {T} {G} {H} (cBar hg) bh = inner H bh
  where
    inner : (H' : A -> Bool) -> Bar T H' -> Bar T (λ y -> G y ∨ᵇ H' y)
    inner H' (cBar hh) = cBar pick
      where
        pick : (x : A) -> G x ∨ᵇ H' x ≡ true
            -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
        pick x ex = sumElim fromG fromH (orTrue (G x) (H' x) ex)
          where
            fromG : G x ≡ true
                 -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
            fromG eg =
              barMono (λ y ey -> ∧∨-distrib (G y) (H' y) (T x y) ey)
                      (barUnion (hg x eg)
                                (barMono (λ y ey -> andTrueL (H' y) (T x y) ey)
                                         (cBar hh)))

            fromH : H' x ≡ true
                 -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
            fromH eh =
              barMono (λ y ey -> ∧∨-weaken (G y) (H' y) (T x y) ey)
                      (inner (λ y -> H' y ∧ᵇ T x y) (hh x eh))

------------------------------------------------------------------------
-- Product.  Lemma 1, fourth bullet -- the load-bearing one.

prodPred : {A B : Set} -> (A -> Bool) -> (B -> Bool) -> A × B -> Bool
prodPred E F (x , y) = E x ∧ᵇ F y

prodRel : {A B : Set} -> (A -> A -> Bool) -> (B -> B -> Bool)
       -> A × B -> A × B -> Bool
prodRel R S (x , y) (u , v) = R x u ∨ᵇ S y v

prodMono : {A B : Set} (R : A -> A -> Bool) (S : B -> B -> Bool)
           (E : A -> Bool) (F : B -> Bool) (x : A) (y : B) (q : A × B)
        -> prodPred E F q ∧ᵇ prodRel R S (x , y) q ≡ true
        -> prodPred (λ a -> E a ∧ᵇ R x a) F q ∨ᵇ
           prodPred E (λ b -> F b ∧ᵇ S y b) q ≡ true
prodMono R S E F x y (u , v) e = ∧∨-split (E u) (F v) (R x u) (S y v) e

barProd : {A B : Set} {R : A -> A -> Bool} {S : B -> B -> Bool}
       -> {E : A -> Bool} {F : B -> Bool}
       -> Bar R E -> Bar S F -> Bar (prodRel R S) (prodPred E F)
barProd {A} {B} {R} {S} {E} {F} (cBar he) bf = inner F bf
  where
    inner : (F' : B -> Bool) -> Bar S F'
         -> Bar (prodRel R S) (prodPred E F')
    inner F' (cBar hf) = cBar pick
      where
        pick : (p : A × B) -> prodPred E F' p ≡ true
            -> Bar (prodRel R S)
                   (λ q -> prodPred E F' q ∧ᵇ prodRel R S p q)
        pick (x , y) ep =
          barMono (prodMono R S E F' x y)
                  (barUnion (barProd (he x (andTrueL (E x) (F' y) ep)) (cBar hf))
                            (inner (λ b -> F' b ∧ᵇ S y b)
                                   (hf y (andTrueR (E x) (F' y) ep))))

------------------------------------------------------------------------
-- Pulling back along a map that reflects the relation on a domain D

barPull : {A B : Set} {R : A -> A -> Bool} {S : B -> B -> Bool}
       -> (f : B -> A) (D : B -> Bool)
       -> ((y z : B) -> D y ≡ true -> D z ≡ true -> S y z ≡ true
             -> R (f y) (f z) ≡ true)
       -> {E : A -> Bool} -> Bar R E
       -> Bar S (λ y -> D y ∧ᵇ E (f y))
barPull {A} {B} {R} {S} f D h {E} (cBar hE) = cBar pick
  where
    pick : (y : B) -> D y ∧ᵇ E (f y) ≡ true
        -> Bar S (λ z -> (D z ∧ᵇ E (f z)) ∧ᵇ S y z)
    pick y ey =
      barMono keep (barPull f D h (hE (f y) (andTrueR (D y) (E (f y)) ey)))
      where
        keep : (z : B) -> (D z ∧ᵇ E (f z)) ∧ᵇ S y z ≡ true
            -> D z ∧ᵇ E (f z) ∧ᵇ R (f y) (f z) ≡ true
        keep z ez =
          andIntro (D z) (E (f z) ∧ᵇ R (f y) (f z))
                   (andTrueL (D z) (E (f z))
                             (andTrueL (D z ∧ᵇ E (f z)) (S y z) ez))
                   (andIntro (E (f z)) (R (f y) (f z))
                             (andTrueR (D z) (E (f z))
                                       (andTrueL (D z ∧ᵇ E (f z)) (S y z) ez))
                             (h y z (andTrueL (D y) (E (f y)) ey)
                                    (andTrueL (D z) (E (f z))
                                              (andTrueL (D z ∧ᵇ E (f z))
                                                        (S y z) ez))
                                    (andTrueR (D z ∧ᵇ E (f z)) (S y z) ez)))

------------------------------------------------------------------------
-- Bool is inductively finite

infix 4.5 _≢ᵇ_

_≢ᵇ_ : Bool -> Bool -> Bool
a ≢ᵇ b = ¬ᵇ (a ⇔ᵇ b)

noThreeDistinct : (x y z : Bool) -> x ≢ᵇ y ≡ true -> x ≢ᵇ z ≡ true
               -> y ≢ᵇ z ≡ true -> Empty
noThreeDistinct true  true  z     () e2 e3
noThreeDistinct true  false true  e1 () e3
noThreeDistinct true  false false e1 e2 ()
noThreeDistinct false false z     () e2 e3
noThreeDistinct false true  false e1 () e3
noThreeDistinct false true  true  e1 e2 ()

boolIFin : Bar _≢ᵇ_ (λ b -> true)
boolIFin =
  cBar (λ x ex ->
  cBar (λ y ey ->
  cBar (λ z ez ->
    emptyElim (noThreeDistinct x y z ey
                 (andTrueL (x ≢ᵇ z) (y ≢ᵇ z) ez)
                 (andTrueR (x ≢ᵇ z) (y ≢ᵇ z) ez)))))

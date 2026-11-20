{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Lib.Bar -- inductively finite sets, after Coquand and Siles, "A Decision
-- Procedure for Regular Expression Equivalence in Type Theory" (CPP 2011).
--
--   Bar R E   holds when, starting from E and repeatedly picking an x and
--             passing to  E intersect (R x) , one always stops.
--
-- With R the complement of equality: one cannot choose distinct elements of E
-- forever.  Every search in the development recurses on a Bar, including
-- closure (LTL.SCC.Graph), whose accumulator grows and so has no
-- decreasing measure.  Subsets are Boolean predicates, which keeps Bar in Set.
--
-- This module is generic: Bar and its closure under union, product and
-- pullback.  Bars are supplied by listBar (LTL.Lib.Nodes, from a list in hand)
-- and guardedVecBar (LTL.States.VecBar, the vectors of a given length).

module LTL.Lib.Bar where

open import LTL.Lib.Sets public

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
  ∧ᵇ-intro (F y) (R x y) (sb y (∧ᵇ-trueˡ (E y) (R x y) e))
                         (∧ᵇ-trueʳ (E y) (R x y) e)

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
-- Union.  Double induction: on the first witness for the G-case, on the
-- second for the H-case.  barMono replaces funext, since the two sides are
-- only pointwise equal predicates.

barUnion : {A : Set} {T : A -> A -> Bool} {G H : A -> Bool}
        -> Bar T G -> Bar T H -> Bar T (λ y -> G y ∨ᵇ H y)
barUnion {A} {T} {G} {H} (cBar hg) bh = inner H bh
  where
    inner : (H' : A -> Bool) -> Bar T H' -> Bar T (λ y -> G y ∨ᵇ H' y)
    inner H' (cBar hh) = cBar pick
      where
        pick : (x : A) -> G x ∨ᵇ H' x ≡ true
            -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
        pick x ex = sumElim fromG fromH (∨ᵇ-true (G x) (H' x) ex)
          where
            fromG : G x ≡ true
                 -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
            fromG eg =
              barMono (λ y ey -> ∧∨-distrib (G y) (H' y) (T x y) ey)
                      (barUnion (hg x eg)
                                (barMono (λ y ey -> ∧ᵇ-trueˡ (H' y) (T x y) ey)
                                         (cBar hh)))

            fromH : H' x ≡ true
                 -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
            fromH eh =
              barMono (λ y ey -> ∧∨-weaken (G y) (H' y) (T x y) ey)
                      (inner (λ y -> H' y ∧ᵇ T x y) (hh x eh))

------------------------------------------------------------------------
-- Product: the load-bearing closure lemma.

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
                  (barUnion (barProd (he x (∧ᵇ-trueˡ (E x) (F' y) ep))
                                     (cBar hf))
                            (inner (λ b -> F' b ∧ᵇ S y b)
                                   (hf y (∧ᵇ-trueʳ (E x) (F' y) ep))))

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
      barMono keep (barPull f D h (hE (f y) (∧ᵇ-trueʳ (D y) (E (f y)) ey)))
      where
        keep : (z : B) -> (D z ∧ᵇ E (f z)) ∧ᵇ S y z ≡ true
            -> D z ∧ᵇ E (f z) ∧ᵇ R (f y) (f z) ≡ true
        keep z ez with ∧ᵇ-split (D z ∧ᵇ E (f z)) (S y z) ez
        ... | dez , syz with ∧ᵇ-split (D z) (E (f z)) dez
        ...   | dz , efz =
          ∧ᵇ-intro (D z) (E (f z) ∧ᵇ R (f y) (f z)) dz
                   (∧ᵇ-intro (E (f z)) (R (f y) (f z)) efz
                             (h y z (∧ᵇ-trueˡ (D y) (E (f y)) ey) dz syz))

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
                 (∧ᵇ-trueˡ (x ≢ᵇ z) (y ≢ᵇ z) ez)
                 (∧ᵇ-trueʳ (x ≢ᵇ z) (y ≢ᵇ z) ez)))))

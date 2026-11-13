{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Nodes -- finite sets of nodes, for a node type with a decidable equality.
--
-- Parameterised by the node type and its equality test, with the two facts
-- about the test the searches use: it is sound (true means equal) and
-- reflexive.  Everything here used to be stated for valuations, in LTL.Sets
-- and LTL.Bar; nothing in it ever read a bit of one, and the graph layer
-- (LTL.Graph) needs it for an arbitrary node type.  LTL.Reach instantiates it
-- at  Val  with  _≡ᵛ_ , and that instance is the one the rest of the
-- development sees, under the same names as before.
--
-- The superscript ᵛ reads "vertex": ∈ᵛ ≢ᵛ are the tests on nodes, and at the
-- Val instance they are the tests on valuations.  The parameter _≡ᵛ_ has
-- Agda's default precedence (fixity declarations for module parameters are
-- ignored); every use is parenthesised or compared with ≡, so it parses the
-- same as the  infix 4.5  of LTL.Reach.
--
-- This module imports LTL.Sets and LTL.Bar but does not re-export them, so that
-- two instances never bring two copies of their names into scope.  The prelude
-- is opened above the module header because the parameters' types need it.

open import LTL.Prelude

module LTL.Nodes {Node : Set}
                 (_≡ᵛ_     : Node -> Node -> Bool)
                 (≡ᵛ-sound : (v w : Node) -> v ≡ᵛ w ≡ true -> v ≡ w)
                 (≡ᵛ-refl  : (v : Node) -> v ≡ᵛ v ≡ true)
  where

open import LTL.Bar

------------------------------------------------------------------------
-- Nodes as a set

infix 4.5 _∈ᵛ_ _≢ᵛ_

_∈ᵛ_ : Node -> List Node -> Bool
v ∈ᵛ us = any (v ≡ᵛ_) us

_≢ᵛ_ : Node -> Node -> Bool
x ≢ᵛ y = ¬ᵇ (x ≡ᵛ y)

≢ᵛ-self : (x : Node) -> x ≢ᵛ x ≡ false
≢ᵛ-self x = cong ¬ᵇ_ (≡ᵛ-refl x)

∈ᵛ-sound : (v : Node) (us : List Node) -> v ∈ᵛ us ≡ true -> v ∈ us
∈ᵛ-sound v []       ()
∈ᵛ-sound v (u ∷ us) e =
  sumElim (λ e1 -> subst (λ z -> v ∈ z ∷ us) (≡ᵛ-sound v u e1) here)
          (λ e2 -> there (∈ᵛ-sound v us e2))
          (orTrue (v ≡ᵛ u) (any (v ≡ᵛ_) us) e)

∈ᵛ-complete : (v : Node) (us : List Node) -> v ∈ us -> v ∈ᵛ us ≡ true
∈ᵛ-complete v []       ()
∈ᵛ-complete v (u ∷ us) here     =
  orL (v ≡ᵛ v) (any (v ≡ᵛ_) us) (≡ᵛ-refl v)
∈ᵛ-complete v (u ∷ us) (there m) =
  orR (v ≡ᵛ u) (any (v ≡ᵛ_) us) (∈ᵛ-complete v us m)

∈ᵛ-false : (v : Node) (us : List Node) -> v ∈ᵛ us ≡ false -> v ∈ us -> Empty
∈ᵛ-false v us e m = true≢false (trans (sym (∈ᵛ-complete v us m)) e)

------------------------------------------------------------------------
-- Names for the hypotheses the graph searches keep repeating.
--
-- Each is only an abbreviation, definitionally equal to the Pi-type it names,
-- so a proof of the long form is a proof of the short one and no body changes.
--
--   Pred          a predicate on nodes: a fairness condition, or the
--                 predicate a Bar search runs on;
--   Edges         a graph on nodes, given as its edge test;
--   Closed ws G C   C is closed under G-successors that lie inside ws;
--   NoneSat f C     f is false at every member of C;
--   HoldsOutside R ws   R holds at every node outside ws -- the
--                 induction hypothesis of a removing iteration.

Pred : Set
Pred = Node -> Bool

Edges : Set
Edges = Node -> Node -> Bool

Closed : List Node -> Edges -> List Node -> Set
Closed ws G C = (z y : Node) -> z ∈ C -> y ∈ ws -> G z y ≡ true -> y ∈ C

NoneSat : Pred -> List Node -> Set
NoneSat f C = (z : Node) -> z ∈ C -> f z ≡ false

HoldsOutside : (Node -> Set) -> List Node -> Set
HoldsOutside R ws = (z : Node) -> z ∈ᵛ ws ≡ false -> R z
------------------------------------------------------------------------
-- Inductive finiteness for nodes

-- IFin E: E is inductively finite.  One cannot keep choosing pairwise distinct
-- nodes that satisfy E forever, so a search that always picks a new one
-- stops.

IFin : (Node -> Bool) -> Set
IFin E = Bar _≢ᵛ_ E

------------------------------------------------------------------------
-- Kuratowski implies inductively finite.
--
-- The ≤ measure of the development survives here and nowhere else: it is paid
-- once, when the Bar is built, and no search counts anything afterwards.

barOfList : {E : Pred} (n : Nat) (xs : List Node) -> length xs ≤ n
         -> ((x : Node) -> E x ≡ true -> x ∈ xs) -> IFin E
barOfList         zero    xs le sb =
  cBar (λ x ex -> emptyElim (leZeroNil xs le (sb x ex)))
barOfList {E = E} (suc n) xs le sb =
  cBar (λ x ex -> barOfList n (filter (x ≢ᵛ_) xs)
                    (lePred (leTrans (filter_lt (x ≢ᵛ_) xs (sb x ex)
                                                (≢ᵛ-self x)) le))
                    (λ z ez -> filter_true (x ≢ᵛ_) xs
                                 (sb z (andTrueL (E z) (x ≢ᵛ z) ez))
                                 (andTrueR (E z) (x ≢ᵛ z) ez)))

------------------------------------------------------------------------
-- The invariant the removing searches carry.
--
-- AllSat E xs says the list xs lies inside the predicate E.  A search that
-- removes an element x from xs passes to E intersect (R x), and that is
-- precisely the sub-Bar cBar hands over -- so the "pool" of section 4c of
-- FORMALISATION-PLAN.md is no longer a list carried alongside the search: it
-- is the Bar's own predicate.

-- Naming convention for the searches built on this (Closure, Gfp, Elim, Fix,
-- Graph, SccTrap):
--   sb    a subset proof: AllSat E xs, or xs ⊆ ys;
--   bar   the IFin E the search recurses on;
--   av    the "available" invariant of a growing search, Avail E ws acc:
--         every candidate in ws not yet in the accumulator acc still
--         satisfies the Bar's predicate E.
-- A search comes as a pair fooGo / fooFind: fooGo runs findFalse for one
-- round, and fooFind cases on its FindResult -- allTrue stops, found x
-- recurses on the smaller Bar that cBar hands over.

AllSat : Pred -> List Node -> Set
AllSat E xs = (x : Node) -> x ∈ xs -> E x ≡ true

Avail : Pred -> List Node -> List Node -> Set
Avail E ws acc = (z : Node) -> z ∈ ws -> z ∈ᵛ acc ≡ false -> E z ≡ true

memAllSat : (xs : List Node) -> AllSat (λ v -> v ∈ᵛ xs) xs
memAllSat xs x m = ∈ᵛ-complete x xs m

listBar : (xs : List Node) -> IFin (λ v -> v ∈ᵛ xs)
listBar xs = barOfList (length xs) xs (leRefl (length xs))
                       (λ x ex -> ∈ᵛ-sound x xs ex)

-- Dropping x from the list is dropping x from the predicate.  Both searches of
-- G29 that remove a member of the list they are searching use this.

dropAllSat : {E : Pred} (p : Pred) (xs : List Node) -> AllSat E xs
          -> (x : Node) -> p x ≡ false
          -> AllSat (λ y -> E y ∧ᵇ (x ≢ᵛ y)) (filter p xs)
dropAllSat {E} p xs sb x q z mz =
  andIntro (E z) (x ≢ᵛ z)
           (sb z (filter_sub p xs mz))
           (cong ¬ᵇ_ (onEq (x ≡ᵛ z) refl))
  where
    onEq : (b : Bool) -> x ≡ᵛ z ≡ b -> x ≡ᵛ z ≡ false
    onEq false e = e
    onEq true  e =
      emptyElim (true≢false (trans (sym (subst (λ u -> p u ≡ true)
                                               (sym (≡ᵛ-sound x z e))
                                               (filter_prop p xs mz)))
                                   q))

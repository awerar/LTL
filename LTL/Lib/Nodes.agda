{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Lib.Nodes -- finite sets of nodes, for a node type with a sound,
-- reflexive equality test _≡ᵛ_.
--
-- The graph layer (LTL.SCC.Graph) uses it at any node type; LTL.States.Reach
-- instantiates it at Val, and that instance is the one the rest of the
-- development sees.  The superscript ᵛ reads "vertex".  Module parameters
-- cannot carry fixity, so every use of _≡ᵛ_ here is parenthesised.
--
-- LTL.Lib.Sets and LTL.Lib.Bar are imported but not re-exported, so that two
-- instances never bring two copies of their names into scope.

open import LTL.Lib.Prelude

module LTL.Lib.Nodes {Node : Set}
                 (_≡ᵛ_     : Node -> Node -> Bool)
                 (≡ᵛ-sound : (v w : Node) -> v ≡ᵛ w ≡ true -> v ≡ w)
                 (≡ᵛ-refl  : (v : Node) -> v ≡ᵛ v ≡ true)
  where

open import LTL.Lib.Bar

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
          (∨ᵇ-true (v ≡ᵛ u) (any (v ≡ᵛ_) us) e)

∈ᵛ-complete : (v : Node) (us : List Node) -> v ∈ us -> v ∈ᵛ us ≡ true
∈ᵛ-complete v []       ()
∈ᵛ-complete v (u ∷ us) here     =
  ∨ᵇ-introˡ (v ≡ᵛ v) (any (v ≡ᵛ_) us) (≡ᵛ-refl v)
∈ᵛ-complete v (u ∷ us) (there m) =
  ∨ᵇ-introʳ (v ≡ᵛ u) (any (v ≡ᵛ_) us) (∈ᵛ-complete v us m)

∈ᵛ-false : (v : Node) (us : List Node) -> v ∈ᵛ us ≡ false -> v ∈ us -> Empty
∈ᵛ-false v us e m = true≢false (trans (sym (∈ᵛ-complete v us m)) e)

------------------------------------------------------------------------
-- Names for the hypotheses the graph searches keep repeating.  Each is an
-- abbreviation, definitionally equal to the Pi-type it names.
--
--   Pred                a predicate on nodes
--   Edges               a graph, given as its edge test
--   Closed ws G C       C is closed under G-successors that lie inside ws
--   NoneSat f C         f is false at every member of C
--   HoldsOutside R ws   R holds at every node outside ws -- the induction
--                       hypothesis of a removing search

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

-- IFin E: E is inductively finite, so a search that keeps picking new nodes
-- satisfying E stops.

IFin : Pred -> Set
IFin E = Bar _≢ᵛ_ E

------------------------------------------------------------------------
-- A list gives an inductively finite set.  The length bound is paid once, here,
-- and no search counts anything afterwards.

barOfList : {E : Pred} (n : Nat) (xs : List Node) -> length xs ≤ n
         -> ((x : Node) -> E x ≡ true -> x ∈ xs) -> IFin E
barOfList         zero    xs le sb =
  cBar (λ x ex -> emptyElim (leZeroNil xs le (sb x ex)))
barOfList {E = E} (suc n) xs le sb =
  cBar (λ x ex -> barOfList n (filter (x ≢ᵛ_) xs)
                    (lePred (leTrans (filter-lt (x ≢ᵛ_) xs (sb x ex)
                                                (≢ᵛ-self x)) le))
                    (λ z ez -> filter-true (x ≢ᵛ_) xs
                                 (sb z (∧ᵇ-trueˡ (E z) (x ≢ᵛ z) ez))
                                 (∧ᵇ-trueʳ (E z) (x ≢ᵛ z) ez)))

------------------------------------------------------------------------
-- The invariant the removing searches carry.  AllSat E xs says xs lies inside
-- E.  Removing x from xs passes to  E intersect (R x) , exactly the sub-Bar
-- that cBar hands over, so the pool of candidates is the Bar's own predicate.

-- Naming convention for the searches built on this (Closure, Graph,
-- SccSeed):
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

-- Dropping x from the list is dropping x from the predicate.

dropAllSat : {E : Pred} (p : Pred) (xs : List Node) -> AllSat E xs
          -> (x : Node) -> p x ≡ false
          -> AllSat (λ y -> E y ∧ᵇ (x ≢ᵛ y)) (filter p xs)
dropAllSat {E} p xs sb x q z mz =
  ∧ᵇ-intro (E z) (x ≢ᵛ z)
           (sb z (filter-sub p xs mz))
           (cong ¬ᵇ_ onEq)
  where
    onEq : x ≡ᵛ z ≡ false
    onEq = refuteTrue (x ≡ᵛ z) λ e ->
      true≢false (trans (sym (subst (λ u -> p u ≡ true)
                                    (sym (≡ᵛ-sound x z e))
                                    (filter-prop p xs mz)))
                        q)

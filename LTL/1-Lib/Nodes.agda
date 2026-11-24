{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Nodes -- finite sets of nodes, for a node type with an equality
-- test eq (LTL.1-Lib.DecEq): the names of the hypotheses the graph searches
-- repeat, inductive finiteness (IFin, listBar), and the invariant of the
-- removing searches.
--
-- The graph layer (LTL.1-Lib.Graph, LTL.1-Lib.FairGraph) uses it at any node
-- type; LTL.5-States.Reach instantiates it at Val, and that instance is the one
-- the rest of the development sees.  It re-exports Membership eq, so an
-- importer gets ≡ᵛ, ∈ᵛ, ≢ᵛ and their lemmas from the same application.
--
-- LTL.1-Lib.Sets and LTL.1-Lib.Bar are imported but not re-exported, so that two
-- instances never bring two copies of their names into scope.

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.DecEq using (DecEq; module Membership)

module LTL.1-Lib.Nodes {Node : Set} (eq : DecEq Node) where

open import LTL.1-Lib.Sets
open import LTL.1-Lib.Bar
open Membership eq public

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
NoneSat f C = ∀[ z ∈ C ] f z ≡ false

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
  cBar (λ x ex -> emptyElim (length-≤0-∈ xs le (sb x ex)))
barOfList {E = E} (suc n) xs le sb =
  cBar (λ x ex -> barOfList n (filter (x ≢ᵛ_) xs)
                    (≤-pred (≤-trans (filter-< (x ≢ᵛ_) xs
                                         (x , sb x ex , ≢ᵛ-self x)) le))
                    (λ z ez -> ∈-filter⁺ (x ≢ᵛ_) xs
                               (sb z (∧ᵇ-trueˡ (E z) (x ≢ᵛ z) ez))
                               (∧ᵇ-trueʳ (E z) (x ≢ᵛ z) ez)))

------------------------------------------------------------------------
-- The invariant the removing searches carry.  AllSat E xs says xs lies inside
-- E.  Removing x from xs passes to  E intersect (R x) , exactly the sub-Bar
-- that cBar hands over, so the pool of candidates is the Bar's own predicate.

-- Naming convention for the searches built on this (the growing closure of
-- LTL.1-Lib.Graph, the removing graphGo and findTerm of LTL.1-Lib.FairGraph):
--   sb    a subset proof: AllSat E xs, or xs ⊆ ys;
--   bar   the IFin E the search recurses on;
--   av    the "available" invariant of a growing search, Avail E ws acc:
--         every candidate in ws not yet in the accumulator acc still
--         satisfies the Bar's predicate E.
-- A search comes as a pair fooGo / fooFind: fooGo runs decideAll for one
-- round, and fooFind cases on its AllDecision -- allTrue stops,
-- counterexample x recurses on the smaller Bar that cBar hands over.

AllSat : Pred -> List Node -> Set
AllSat E xs = ∀[ x ∈ xs ] E x ≡ true

Avail : Pred -> List Node -> List Node -> Set
Avail E ws acc = (z : Node) -> z ∈ ws -> z ∈ᵛ acc ≡ false -> E z ≡ true

AllSat-∈ᵛ : (xs : List Node) -> AllSat (λ v -> v ∈ᵛ xs) xs
AllSat-∈ᵛ xs x m = ∈ᵛ-complete x xs m

listBar : (xs : List Node) -> IFin (λ v -> v ∈ᵛ xs)
listBar xs = barOfList (length xs) xs (≤-refl (length xs))
                       (λ x ex -> ∈ᵛ-sound x xs ex)

-- Dropping x from the list is dropping x from the predicate.

dropAllSat : {E : Pred} (p : Pred) (xs : List Node) -> AllSat E xs
          -> (x : Node) -> p x ≡ false
          -> AllSat (λ y -> E y ∧ᵇ (x ≢ᵛ y)) (filter p xs)
dropAllSat {E} p xs sb x q z mz =
  ∧ᵇ-intro (E z) (x ≢ᵛ z)
           (sb z (∈-filter⁻ p xs mz))
           (cong ¬ᵇ_ onEq)
  where
    onEq : x ≡ᵛ z ≡ false
    onEq = refuteTrue (x ≡ᵛ z) λ e ->
      true≢false (trans (sym (subst (λ u -> p u ≡ true)
                                    (sym (≡ᵛ-sound x z e))
                                    (filter-prop p xs mz)))
                        q)

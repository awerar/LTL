{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Nodes -- finite sets of nodes, for a node type with an equality
-- test eq (LTL.1-Lib.DecEq): the names of the hypotheses the graph searches
-- repeat, list difference (∖ᵛ, ∖), inductive finiteness (Finite, listFinite), and
-- the invariant of the searches.
--
-- The graph layer (LTL.1-Lib.Graph, LTL.1-Lib.FairGraph) uses it at any node
-- type; LTL.5-States.Reach instantiates it at Val, and that instance is the one
-- the rest of the development sees.  It re-exports Membership eq, so an
-- importer gets ≡ᵛ, ∈ᵛ, ≢ᵛ and their lemmas from the same application.
--
-- LTL.1-Lib.Sets and LTL.1-Lib.Exhaustible are imported but not re-exported,
-- so that two instances never bring two copies of their names into scope.

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.DecEq using (DecEq; module Membership)

module LTL.1-Lib.Nodes {Node : Set} (eq : DecEq Node) where

open import LTL.1-Lib.Sets
open import LTL.1-Lib.Exhaustible
open Membership eq public

------------------------------------------------------------------------
-- Names for the hypotheses the graph searches keep repeating.  Each is an
-- abbreviation, definitionally equal to the Pi-type it names.
--
--   Pred                a predicate on nodes
--   Edges               a graph, given as its edge test
--   C closed-under G within ws
--                       C is closed under G-successors that lie inside ws
--   NoneSat f C         f is false at every member of C
--   HoldsOutside R ws   R holds at every node outside ws -- the induction
--                       hypothesis of a removing search

Pred : Set
Pred = Node -> Bool

Edges : Set
Edges = Node -> Node -> Bool

infix 4 Closed

Closed : (ws : List Node) (G : Edges) (C : List Node) -> Set
Closed ws G C = ∀ⁱ[ z ∈ C ] ∀ⁱ[ y ∈ ws ] (G z y ≡ true -> y ∈ C)

syntax Closed ws G C = C closed-under G within ws

NoneSat : Pred -> List Node -> Set
NoneSat f C = ∀[ z ∈ C ] f z ≡ false

HoldsOutside : (Node -> Set) -> List Node -> Set
HoldsOutside R ws = (z : Node) -> z ∈ᵛ ws ≡ false -> R z

------------------------------------------------------------------------
-- Inductive finiteness for nodes

-- Finite Pool: Pool is inductively finite, so a search that keeps picking new
-- nodes from Pool stops.

Finite : Pred -> Set
Finite Pool = Exhaustible _≢ᵛ_ Pool

------------------------------------------------------------------------
-- A list gives an inductively finite set.  The length bound is paid once, here,
-- and no search counts anything afterwards.

finiteOfList : {Pool : Pred} (bound : Nat) (xs : List Node)
            -> length xs ≤ bound
            -> ((x : Node) -> Pool x ≡ true -> x ∈ xs) -> Finite Pool
finiteOfList               zero        xs short subset =
  everyPick (λ x x∈ -> emptyElim (length-≤0-∈ xs short (subset x x∈)))
finiteOfList {Pool = Pool} (suc bound) xs short subset =
  everyPick (λ x x∈ -> finiteOfList bound (filter (x ≢ᵛ_) xs)
    (≤-pred (≤-trans (filter-< (x ≢ᵛ_) xs (x , subset x x∈ , ≢ᵛ-self x))
                     short))
    (λ z z∈ -> ∈-filter⁺ (x ≢ᵛ_) xs
                 (subset z (∧ᵇ-trueˡ (Pool z) (x ≢ᵛ z) z∈))
                 (∧ᵇ-trueʳ (Pool z) (x ≢ᵛ z) z∈)))

------------------------------------------------------------------------
-- List difference.  ws ∖ C is what is left of ws once C is taken out; the
-- lemmas take both lists explicitly, as filter's do, since Agda cannot read
-- them back off the filter.

infixl 6 _∖ᵛ_ _∖_

_∖ᵛ_ : List Node -> Node -> List Node
ws ∖ᵛ x = filter (x ≢ᵛ_) ws

_∖_ : List Node -> List Node -> List Node
ws ∖ C = filter (λ z -> ¬ᵇ (z ∈ᵛ C)) ws

∖-⊆ : (ws C : List Node) -> ws ∖ C ⊆ ws
∖-⊆ ws C z m = ∈-filter⁻ (λ y -> ¬ᵇ (y ∈ᵛ C)) ws m

∈-∖⁺ : {ws : List Node} {z : Node} (C : List Node)
    -> z ∈ ws -> z ∈ᵛ C ≡ false -> z ∈ ws ∖ C
∈-∖⁺ {ws} C m e = ∈-filter⁺ (λ y -> ¬ᵇ (y ∈ᵛ C)) ws m (cong ¬ᵇ_ e)

∈-∖⁻ : (ws C : List Node) {z : Node} -> z ∈ ws ∖ C -> z ∈ᵛ C ≡ false
∈-∖⁻ ws C {z} m = ¬ᵇ-true (z ∈ᵛ C) (filter-prop (λ y -> ¬ᵇ (y ∈ᵛ C)) ws m)

------------------------------------------------------------------------
-- The invariant the searches carry.  AllSat Pool xs says xs lies inside Pool.
-- Taking x out of the candidates passes to  Pool ∩ (x ≢ᵛ_) , exactly the
-- smaller pool that next hands over, so the candidates are the pool
-- itself.  A removing search shrinks ws and keeps AllSat Pool ws; a growing one
-- grows an accumulator acc and keeps AllSat Pool (ws ∖ acc).

-- Naming convention for the searches built on this (the growing closure of
-- LTL.1-Lib.Graph, the removing graphGo and findTerminal of LTL.1-Lib.FairGraph):
--   subset  AllSat Pool xs, or xs ⊆ ys;
--   fin     the Finite Pool the search recurses on;
--   avail   the "available" invariant of a growing search,
--           AllSat Pool (ws ∖ acc): every candidate in ws not yet in the
--           accumulator acc is still in the pool;
--   next    the field of everyPick: next x x∈ proves the pool left
--           after picking x finite, where x∈ says x is in the pool.
-- A search comes as a pair fooGo / fooFind: fooGo runs decideAll for one
-- round, and fooFind cases on its AllDecision -- allTrue stops,
-- counterexample x recurses on the smaller pool that next hands over.  The
-- growing closure runs decideAny instead: noneTrue stops, witness x recurses.

AllSat : Pred -> List Node -> Set
AllSat Pool xs = ∀[ x ∈ xs ] Pool x ≡ true


AllSat-∈ᵛ : (xs : List Node) -> AllSat (λ v -> v ∈ᵛ xs) xs
AllSat-∈ᵛ xs x m = ∈ᵛ-complete x xs m

listFinite : (xs : List Node) -> Finite (λ v -> v ∈ᵛ xs)
listFinite xs = finiteOfList (length xs) xs (≤-refl (length xs))
                       (λ x x∈ -> ∈ᵛ-sound x xs x∈)

-- Dropping x from the list is dropping x from the predicate.

dropAllSat : {Pool : Pred} (p : Pred) (xs : List Node) -> AllSat Pool xs
          -> (x : Node) -> p x ≡ false
          -> AllSat (Pool ∩ (x ≢ᵛ_)) (filter p xs)
dropAllSat {Pool} p xs subset x q z mz =
  ∧ᵇ-intro (Pool z) (x ≢ᵛ z)
           (subset z (∈-filter⁻ p xs mz))
           (cong ¬ᵇ_ onEq)
  where
    onEq : x ≡ᵛ z ≡ false
    onEq = refuteTrue (x ≡ᵛ z) λ e ->
      true≢false (trans (sym (subst (λ u -> p u ≡ true)
                                    (sym (≡ᵛ-sound x z e))
                                    (filter-prop p xs mz)))
                        q)

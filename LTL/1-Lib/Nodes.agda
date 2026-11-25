{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Nodes -- finite sets of nodes, for a node type with an equality
-- test eq (LTL.1-Lib.DecEq): the names of the hypotheses the graph searches
-- repeat, inductive finiteness (Finiteᵛ, listFinite), and the invariant of the
-- searches, xs inside Pool.  That invariant is the bridge between the lists a
-- search walks and the predicate its pool is, and it gets the algebra
-- (inside-⊆, inside-∩, inside-apart) that Exhaustible gives ⊆ᵖ.  Lists as
-- sets on their own (∈ᵛ, ∖, ∩ˡ) are Membership's, in LTL.1-Lib.DecEq.
--
-- The graph layer (LTL.1-Lib.Graph, LTL.1-Lib.FairGraph) uses it at any node
-- type; LTL.5-States.Reach instantiates it at Val, and that instance is the one
-- the rest of the development sees.  It re-exports Membership eq, so an
-- importer gets ≡ᵛ, ∈ᵛ, ≢ᵛ and their lemmas from the same application.
--
-- LTL.1-Lib.Sets and LTL.1-Lib.Exhaustible are imported but not re-exported,
-- so that two instances never bring two copies of their names into scope.

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.DecEq using (DecEq; module Membership; Finite)

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
--   C avoids f          no member of C is in f
--   HoldsOutside R ws   R holds at every node outside ws -- the induction
--                       hypothesis of a removing search

Pred : Set
Pred = Node -> Bool

Edges : Set
Edges = Node -> Node -> Bool

infix 4 Closed Avoids

Closed : (ws : List Node) (G : Edges) (C : List Node) -> Set
Closed ws G C = ∀ⁱ[ z ∈ C ] ∀ⁱ[ y ∈ ws ] (G z y ≡ true -> y ∈ C)

syntax Closed ws G C = C closed-under G within ws

Avoids : List Node -> Pred -> Set
Avoids C f = ∀[ z ∈ C ] z ∉ᵖ f

syntax Avoids C f = C avoids f

HoldsOutside : (Node -> Set) -> List Node -> Set
HoldsOutside R ws = (z : Node) -> z ∈ᵛ ws ≡ false -> R z

------------------------------------------------------------------------
-- Inductive finiteness for nodes

-- Finiteᵛ Pool: Finite (LTL.1-Lib.DecEq) at eq, so a search that keeps
-- picking new nodes from Pool stops.  The superscript ᵛ marks the node
-- instance, as in ≡ᵛ and ∈ᵛ.

Finiteᵛ : Pred -> Set
Finiteᵛ Pool = Finite eq Pool

------------------------------------------------------------------------
-- A list gives an inductively finite set.  The length bound is paid once, here,
-- and no search counts anything afterwards.

finiteOfList : {Pool : Pred} (bound : Nat) (xs : List Node)
            -> length xs ≤ bound
            -> (∀[ x ∈ᵖ Pool ] x ∈ xs) -> Finiteᵛ Pool
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
-- The invariant the searches carry.  xs inside Pool says every member of xs
-- is in Pool.
-- Taking x out of the candidates passes to  Pool ∩ (x ≢ᵛ_) , exactly the
-- smaller pool that next hands over, so the candidates are the pool
-- itself.  A removing search shrinks ws and keeps ws inside Pool; a growing
-- one grows an accumulator acc and keeps (ws ∖ acc) inside Pool.

-- Naming convention for the searches built on this (the growing closure of
-- LTL.1-Lib.Graph, the removing graphGo and findTerminal of LTL.1-Lib.FairGraph):
--   subset  xs inside Pool, or xs ⊆ ys;
--   fin     the Finiteᵛ Pool the search recurses on;
--   avail   the "available" invariant of a growing search,
--           (ws ∖ acc) inside Pool: every candidate in ws not yet in the
--           accumulator acc is still in the pool;
--   next    the field of everyPick: next x x∈ proves the pool left
--           after picking x finite, where x∈ says x is in the pool.
-- A search comes as a pair fooGo / fooFind: fooGo runs decideAll for one
-- round, and fooFind cases on its AllDecision -- allTrue stops,
-- counterexample x recurses on the smaller pool that next hands over.  The
-- growing closure runs decideAny instead: noneTrue stops, witness x recurses.

infix 4 Inside

Inside : List Node -> Pred -> Set
Inside xs Pool = ∀[ x ∈ xs ] x ∈ᵖ Pool

syntax Inside xs Pool = xs inside Pool

-- Its algebra: xs inside E composes with ⊆ on the left and with ∩ on the
-- right, so the invariants of the searches are proved by set reasoning
-- rather than Boolean case analysis.

inside-∈ᵛ : (xs : List Node) -> xs inside (λ v -> v ∈ᵛ xs)
inside-∈ᵛ xs x m = ∈ᵛ-complete x xs m

inside-filter : (p : Pred) (xs : List Node) -> filter p xs inside p
inside-filter p xs z m = filter-prop p xs m

inside-⊆ : {xs ys : List Node} {E : Pred} -> xs ⊆ ys -> ys inside E -> xs inside E
inside-⊆ s h z m = h z (s z m)

inside-∩ : {xs : List Node} {E F : Pred} -> xs inside E -> xs inside F -> xs inside E ∩ F
inside-∩ {E = E} {F} h k z m = ∧ᵇ-intro (E z) (F z) (h z m) (k z m)

-- A list inside a test that x fails holds no x.
inside-apart : {xs : List Node} {x : Node} (p : Pred) -> x ∉ᵖ p -> xs inside p
            -> xs inside (x ≢ᵛ_)
inside-apart p q h z m = separate p q (h z m)

-- What is left once C is taken out holds no member of C.
∖-apart : (ws C : List Node) -> ∀ⁱ[ x ∈ C ] (ws ∖ C) inside (x ≢ᵛ_)
∖-apart ws C {x} m = inside-apart (λ z -> ¬ᵇ (z ∈ᵛ C)) (cong ¬ᵇ_ (∈ᵛ-complete x C m))
                                  (inside-filter _ ws)

-- Taking C, with x in it, out of the list takes x out of the pool: what is
-- left lies in the smaller pool that next hands over.

dropInside : {Pool : Pred} (ws C : List Node) {x : Node}
          -> ws inside Pool -> x ∈ C -> (ws ∖ C) inside Pool ∩ (x ≢ᵛ_)
dropInside ws C subset m =
  inside-∩ (inside-⊆ (∖-⊆ ws C) subset) (∖-apart ws C m)

------------------------------------------------------------------------
-- A list in hand is a finite pool.

listFinite : (xs : List Node) -> Finiteᵛ (λ v -> v ∈ᵛ xs)
listFinite xs = finiteOfList (length xs) xs (≤-refl (length xs))
                       (λ x x∈ -> ∈ᵛ-sound x xs x∈)

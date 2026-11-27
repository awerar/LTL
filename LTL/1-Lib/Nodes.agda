{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Nodes -- finite sets of nodes, for a node type with an equality
-- test eq (LTL.1-Lib.DecEq): the names of the hypotheses the graph searches
-- repeat, inductive finiteness (Finiteᵛ, listFinite), and the invariant of the
-- searches, All Pool xs.  That invariant is the bridge between the lists a
-- search walks and the predicate its pool is, and it gets the algebra
-- (All-⊆, All-∩, All-apart) that Exhaustible gives ⊆ᵖ.  Lists as
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
--   Subgraph            a vertex list, read as the subgraph it induces: the
--                       edges of the graph at hand between its members
--   Closed[ G ▷ ws ] C  C is closed under G-successors that lie in ws
--                       (▷ is Z's range restriction: G's edges into ws)
--   None f C            no member of C is in f (All's counterpart)
--   HoldsOutside R ws   R holds at every node outside ws -- the induction
--                       hypothesis of a removing search

Pred : Set
Pred = Node -> Bool

Edges : Set
Edges = Node -> Node -> Bool

-- A synonym, so a list a search computes (reachSet ws v, ws ∖ C) is a
-- subgraph as it stands.

Subgraph : Set
Subgraph = List Node

infix 4 Closed

Closed : (ws : Subgraph) (G : Edges) (C : List Node) -> Set
Closed ws G C = ∀ⁱ[ z ∈ C ] ∀ⁱ[ y ∈ ws ] (G z y ≡ true -> y ∈ C)

syntax Closed ws G C = Closed[ G ▷ ws ] C

None : Pred -> List Node -> Set
None f C = ∀[ z ∈ C ] z ∉ᵖ f

HoldsOutside : (Node -> Set) -> Subgraph -> Set
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
-- The invariant the searches carry.  All Pool xs says every member of xs
-- is in Pool (the standard library's All, at a Boolean predicate).
-- Taking x out of the candidates passes to  Pool ∩ (x ≢ᵛ_) , exactly the
-- smaller pool that next hands over, so the candidates are the pool
-- itself.  A removing search shrinks ws and keeps All Pool ws; a growing
-- one grows an accumulator acc and keeps All Pool (ws ∖ acc); a descending
-- one moves a vertex r and keeps All Pool (reachSet ws r).

-- Naming convention for the searches built on this (in LTL.1-Lib.Graph,
-- grow, the growing search behind closure; in LTL.1-Lib.FairGraph, the
-- removing fairOrCert and the descending descend):
--   subset  All Pool xs, or xs ⊆ ys;
--   fin     the Finiteᵛ Pool the search recurses on;
--   avail   the "available" invariant of a growing or descending search,
--           All Pool (ws ∖ acc): every candidate in ws not yet in the
--           accumulator acc is still in the pool, or All Pool (reachSet ws r):
--           everything r reaches is;
--   next    the field of everyPick: next x x∈ proves the pool left
--           after picking x finite, where x∈ says x is in the pool.
-- A search is one recursive function, named for what it does or returns: it
-- matches fin as everyPick next and cases on decideAll with a with-clause.
-- allTrue stops, counterexample x recurses on the smaller pool that next
-- hands over.  grow runs decideAny instead: noneTrue stops, witness x
-- recurses.  Each search
-- returns its correctness with its answer, so no lemma is proved about it.

All : Pred -> List Node -> Set
All Pool xs = ∀[ x ∈ xs ] x ∈ᵖ Pool

-- Its algebra: All E xs composes with ⊆ on the left and with ∩ on the
-- right, so the invariants of the searches are proved by set reasoning
-- rather than Boolean case analysis.

All-⊆ : {xs ys : List Node} {E : Pred} -> xs ⊆ ys -> All E ys -> All E xs
All-⊆ s h z m = h z (s z m)

All-∩ : {xs : List Node} {E F : Pred} -> All E xs -> All F xs -> All (E ∩ F) xs
All-∩ {E = E} {F} h k z m = ∧ᵇ-intro (E z) (F z) (h z m) (k z m)

-- A list inside a test that x fails holds no x.
All-apart : {xs : List Node} {x : Node} (p : Pred) -> x ∉ᵖ p -> All p xs
         -> All (x ≢ᵛ_) xs
All-apart p q h z m = separate p q (h z m)

-- Taking C, with x in it, out of the list takes x out of the pool: if what
-- is left lies inside a list xs in Pool, it lies in the smaller pool that
-- next hands over.  A removing search has xs = ws (∖-⊆), a growing one the
-- candidates of the round before (∖-antitone).

All-∖ : {Pool : Pred} {xs : List Node} (ws : Subgraph) (C : List Node)
     -> {x : Node} -> ws ∖ C ⊆ xs -> All Pool xs -> x ∈ C
     -> All (Pool ∩ (x ≢ᵛ_)) (ws ∖ C)
All-∖ ws C {x} s subset m =
  All-∩ (All-⊆ s subset)
        (All-apart (λ z -> ¬ᵇ (z ∈ᵛ C)) (cong ¬ᵇ_ (∈ᵛ-complete C x m))
                   (filter-prop _ ws))

------------------------------------------------------------------------
-- A list in hand is a finite pool.

listFinite : (xs : List Node) -> Finiteᵛ (λ v -> v ∈ᵛ xs)
listFinite xs = finiteOfList (length xs) xs (≤-refl (length xs))
                       (∈ᵛ-sound xs)

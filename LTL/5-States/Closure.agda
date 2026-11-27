{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Closure -- Ust P, the set of states the searches explore.
--
-- St (all states) is what the derivations quantify over: ⊢ beta St is state
-- completeness.  The searches are computed, so they run on a smaller set Ust
-- with three properties:
--
--   ustSt      every member is a state;
--   ustSeed    every state containing P is a member;
--   ustClosed  the successors of a member are members.
--
-- ustClosed lets a refutation of u use all state-successors of u; ustSeed lets
-- a state outside Ust be disposed of without the search, since it cannot
-- contain P.
--
-- Ust is the successor closure of the states containing P, by the growing
-- search of LTL.1-Lib.Graph over St.  That search GROWS its accumulator, so it
-- recurses on a Finiteᵛ proof (stateFinite) rather than a length.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.Closure (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.Valuation P
open import LTL.5-States.RowFinite using (guardedRowFinite)
open import LTL.5-States.State P
open import LTL.5-States.Step P

-- The growing search, at the edge test step.  LTL.6-Countermodel.Walk makes
-- the application the other P-modules see; this one stays private.
open import LTL.1-Lib.Graph valEq step
  using (closure; closureIn; closureSeed; closureClosed)

------------------------------------------------------------------------
-- The successor closure of the states containing P: the growing search
-- closure of LTL.1-Lib.Graph, seeded by "contains P", over St.  Each round
-- adds a new valuation, and stateFinite says that cannot go on forever.  Its
-- pool is every valuation, so St lies in it trivially (stInPool).

anyVal : Pred
anyVal v = true

stateFinite : Finiteᵛ anyVal
stateFinite = guardedRowFinite (atoms P) anyVal

containsP : Val -> Bool
containsP v = holdsIn v P

stInPool : All anyVal St
stInPool x m = refl

-- Ust P: the successor closure of the states that contain P.  Every search
-- runs on it.

Ust : Subgraph
Ust = closure containsP St stInPool stateFinite

ustSt : ∀ⁱ[ v ∈ Ust ] v ∈ St
ustSt {v} m = closureIn containsP St stInPool stateFinite v m

-- Named rather than applied inline: giving filter-prop its list argument
-- against the folded  St  keeps the elaborator from unfolding Ust.

stIsState : ∀ⁱ[ v ∈ St ] isState v ≡ true
stIsState {v} m = filter-prop isState (rows (atoms P)) v m

-- Every member is a state, so (S2) can be read off it.

ustState : ∀ⁱ[ v ∈ Ust ] isState v ≡ true
ustState m = stIsState (ustSt m)

ustSeed : {v : Val}
       -> v ∈ St -> holdsIn v P ≡ true -> v ∈ Ust
ustSeed m e = closureSeed containsP St stInPool stateFinite m e

ustClosed : Closed[ step ▷ St ] Ust
ustClosed mv mw st =
  closureClosed containsP St stInPool stateFinite mv mw st

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Closure -- Ust P, the set of states the searches explore.
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
-- search of LTL.Lib.Graph over St.  That search GROWS its accumulator, so it
-- recurses on a Bar (vecBar) rather than a length.

open import LTL.Syntax.Formula using (Formula)

module LTL.States.Closure (P : Formula) where

open import LTL.States.Common
open import LTL.States.VecBar
open import LTL.States.State P
open import LTL.States.Step P

-- The growing search, at the edge test step.  LTL.Countermodel.Walk makes
-- the application the other P-modules see; this one stays private.
open import LTL.Lib.Graph _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl step
  using (closure; closureIn; closureSeed; closureClosed)

------------------------------------------------------------------------
-- The successor closure of the states containing P: the growing search
-- closure of LTL.Lib.Graph, seeded by "contains P", over St.  Each round
-- adds a new vector of length |stateAtoms|, and vecBar says that cannot go on
-- forever.

vecBar : IFin (hasLength (length stateAtoms))
vecBar = guardedVecBar (length stateAtoms) (hasLength (length stateAtoms))
                       (λ v ev -> ev)

containsP : Val -> Bool
containsP v = valOf v P

stAllSat : AllSat (hasLength (length stateAtoms)) St
stAllSat x m = hasLength-intro (length stateAtoms) x (stLen m)

-- Ust P: the successor closure of the states that contain P.  Every search
-- runs on it.

Ust : List Val
Ust = closure containsP St stAllSat vecBar

ustSt : {v : Val} -> v ∈ Ust -> v ∈ St
ustSt {v} m = closureIn containsP St stAllSat vecBar v m

-- Named rather than applied inline: giving filter-prop its list argument
-- against the folded  St  keeps the elaborator from unfolding Ust.

stIsState : {v : Val} -> v ∈ St -> isState v ≡ true
stIsState m = filter-prop isState (allVecs (length stateAtoms)) m

-- Every member is a state, so (S2) can be read off it.

ustState : {v : Val} -> v ∈ Ust -> isState v ≡ true
ustState m = stIsState (ustSt m)

ustSeed : {v : Val}
       -> v ∈ St -> valOf v P ≡ true -> v ∈ Ust
ustSeed m e = closureSeed containsP St stAllSat vecBar m e

ustClosed : {v w : Val}
         -> v ∈ Ust -> w ∈ St -> step v w ≡ true -> w ∈ Ust
ustClosed mv mw st =
  closureClosed containsP St stAllSat vecBar mv mw st

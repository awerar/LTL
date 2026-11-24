{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.6-Countermodel.Lasso -- a fair lasso from v0, and its positions as those
-- of LTL.4-Semantics.Orbit at valuations.
--
-- A position (s , rest) is VALID when rest is a walk in Ust from s back to
-- b, the last state of the cycle.  Both the start (v0 , rest) and the
-- position loop the lasso loops back to are valid, and b steps to loop: this
-- is the whole invariant.  The successor preserves validity, and the step
-- proof falls out of consuming the Trail constructor: no arithmetic.
--
-- Every walk from a valid position passes through b, so fairness is only
-- asked of b: every eventuality pending there is fulfilled on the cycle.
-- sccLasso (LTL.7-SCC.SccLasso) builds a lasso from a fair loop of the state
-- graph.
--
-- The module also applies LTL.4-Semantics.OrbitEval at valuations and
-- re-exports it, so evalAt and eval read formulas on these lassos.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.6-Countermodel.Lasso (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.Closure P
open import LTL.6-Countermodel.Walk P
import LTL.4-Semantics.OrbitEval

------------------------------------------------------------------------
-- Valid positions

data ValidPos (b : Val) : Pos -> Set where
  vpos : (s : Val) (rest : List Val) -> s ∈ Ust
      -> Trail Ust s rest b -> ValidPos b (s , rest)

posIn : (b : Val) {pos : Pos}
     -> ValidPos b pos -> posState pos ∈ Ust
posIn b (vpos s rest ms wk) = ms

------------------------------------------------------------------------
-- The cycle: from loop, a walk to b, and b steps back to loop.  The cycle is
-- split at its head, as in LTL.Statement's Lasso, which makes nextPos total.

record Cycle : Set where
  constructor mkCycle
  field
    b           : Val   -- the last state of the cycle
    loop        : Pos   -- the position the cycle loops back to
    loopValid   : ValidPos b loop
    closingStep : step b (posState loop) ≡ true

-- Fairness: every eventuality pending at b is fulfilled on the cycle.

Fair : Cycle -> Set
Fair cy =
  (A : Formula) -> A ∈ eventualities -> valOf b (□ A) ≡ false
  -> Fulfil A b (stretchStates loop)
  where open Cycle cy

-- b is a state of the cycle.

endOnCycle : (cy : Cycle)
          -> Cycle.b cy ∈ stretchStates (Cycle.loop cy)
endOnCycle (mkCycle b (s , rest) (vpos s rest ms wk) stb) =
  trailEnd wk

------------------------------------------------------------------------
-- Validity is preserved along the lasso, hence throughout an orbit

module _ (cy : Cycle) where

  open Cycle cy

  posStep : {pos : Pos} -> ValidPos b pos
         -> ValidPos b (nextPos loop pos) ×
            step (posState pos) (posState (nextPos loop pos)) ≡ true
  posStep (vpos s []        ms tNil)             = loopValid , closingStep
  posStep (vpos s (w ∷ ws) ms (tCons mw st wk)) = vpos w ws mw wk , st

  posIterValid : (pos : Pos) (t : Nat) -> ValidPos b pos
              -> ValidPos b (posIter loop pos t)
  posIterValid pos zero    vp = vp
  posIterValid pos (suc t) vp = fst (posStep (posIterValid pos t vp))

  orbitValid : (pos q : Pos) -> ValidPos b pos -> q ∈ orbit loop pos
            -> ValidPos b q
  orbitValid pos q vp m =
    orbit-all loop (ValidPos b) pos (λ t -> posIterValid pos t vp) q m

------------------------------------------------------------------------
-- The lasso.  rest is everything after v0 up to the first return to b: the
-- stem followed by one turn of the cycle.

record Lasso (v0 : Val) : Set where
  constructor mkLasso
  field
    cycle      : Cycle
    fair       : Fair cycle
    rest       : List Val
    startValid : ValidPos (Cycle.b cycle) (v0 , rest)

  open Cycle cycle public

  startIn : v0 ∈ Ust
  startIn = posIn b startValid

-- the state at stage i of the run the lasso unwinds to
stateAt : (v0 : Val) -> Lasso v0 -> Nat -> Val
stateAt v0 l i = posState (posIter loop (v0 , rest) i)
  where open Lasso l

------------------------------------------------------------------------
-- The Boolean evaluation at a position
--
-- A variable is read off the state through valOf.  For a variable not in sub
-- P this gives false (indexOf runs off the end of the vector), so the
-- evaluation is total on all formulas, as soundness needs.

-- a valuation read as an assignment to the variables
readVal : Val -> Nat -> Bool
readVal v n = valOf v (var n)

open LTL.4-Semantics.OrbitEval Val readVal public
  using (evalAt; eval□-true; eval□-intro; eval□-false-intro)

------------------------------------------------------------------------
-- The evaluation on a lasso, at stage i, iterating the successor from the
-- start

eval : (v0 : Val) -> Lasso v0 -> Formula -> Nat -> Bool
eval v0 l A i = evalAt loop A (posIter loop (v0 , rest) i)
  where open Lasso l

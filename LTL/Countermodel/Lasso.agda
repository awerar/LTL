{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Lasso -- a fair lasso from v0, and its positions as those
-- of LTL.Countermodel.Orbit at valuations.
--
-- A position (s , rest) is VALID when rest is a walk in Uinf P from s back to
-- b, the last state of the cycle.  Both the start (v0 , rest) and the
-- position loop the lasso loops back to are valid, and b steps to loop: this
-- is the whole invariant.  The successor preserves validity, and the step
-- proof falls out of consuming the Walk constructor: no arithmetic.
--
-- Every walk from a valid position passes through b, so fairness is only
-- asked of b: every eventuality pending there is fulfilled on the cycle.
-- sccLasso (LTL.SCC.SccLasso) builds a lasso from a fair loop of the state
-- graph.

module LTL.Countermodel.Lasso where

open import LTL.Countermodel.Walk public
open import LTL.Countermodel.Orbit Val public

------------------------------------------------------------------------
-- Valid positions

data ValidPos (P : Formula) (b : Val) : Pos -> Set where
  vpos : (s : Val) (rest : List Val) -> s ∈ Uinf P
      -> Walk P (Uinf P) s rest b -> ValidPos P b (s , rest)

posIn : (P : Formula) (b : Val) {pos : Pos}
     -> ValidPos P b pos -> posState pos ∈ Uinf P
posIn P b (vpos s rest ms wk) = ms

------------------------------------------------------------------------
-- The cycle: from loop, a walk to b, and b steps back to loop.  The cycle is
-- split at its head, as in LTL.Trusted's Lasso, which makes nextPos total.

record Cycle (P : Formula) : Set where
  constructor mkCycle
  field
    b           : Val   -- the last state of the cycle
    loop        : Pos   -- the position the cycle loops back to
    loopValid   : ValidPos P b loop
    closingStep : step P b (posState loop) ≡ true

-- Fairness: every eventuality pending at b is fulfilled on the cycle.

Fair : (P : Formula) -> Cycle P -> Set
Fair P cy =
  (A : Formula) -> A ∈ □Args (sub P) -> valOf P b (□ A) ≡ false
  -> Fulfil P A b (stretchStates loop)
  where open Cycle cy

-- b is a state of the cycle.

endOnCycle : (P : Formula) (cy : Cycle P)
          -> Cycle.b cy ∈ stretchStates (Cycle.loop cy)
endOnCycle P (mkCycle b (s , rest) (vpos s rest ms wk) stb) =
  walkEnd P (Uinf P) wk

------------------------------------------------------------------------
-- Validity is preserved along the lasso, hence throughout an orbit

module _ (P : Formula) (cy : Cycle P) where

  open Cycle cy

  posStep : {pos : Pos} -> ValidPos P b pos
         -> ValidPos P b (nextPos loop pos) ×
            step P (posState pos) (posState (nextPos loop pos)) ≡ true
  posStep (vpos s []        ms wnil)             = loopValid , closingStep
  posStep (vpos s (w ∷ ws) ms (wcons mw st wk)) = vpos w ws mw wk , st

  posIterValid : (t : Nat) (pos : Pos) -> ValidPos P b pos
              -> ValidPos P b (posIter loop t pos)
  posIterValid zero    pos vp = vp
  posIterValid (suc t) pos vp =
    posIterValid t (nextPos loop pos) (fst (posStep vp))

  orbitValid : (pos q : Pos) -> ValidPos P b pos -> q ∈ orbit loop pos
            -> ValidPos P b q
  orbitValid pos q vp m = fromIter (∈orbit-iter loop pos q m)
    where
      fromIter : (Σ[ t ∈ Nat ] posIter loop t pos ≡ q) -> ValidPos P b q
      fromIter (t , et) =
        subst (λ r -> ValidPos P b r) et (posIterValid t pos vp)

------------------------------------------------------------------------
-- The lasso.  rest is everything after v0 up to the first return to b: the
-- stem followed by one turn of the cycle.

record Lasso (P : Formula) (v0 : Val) : Set where
  constructor mkLasso
  field
    cycle      : Cycle P
    fair       : Fair P cycle
    rest       : List Val
    startValid : ValidPos P (Cycle.b cycle) (v0 , rest)

  open Cycle cycle public

  startIn : v0 ∈ Uinf P
  startIn = posIn P b startValid

module _ (P : Formula) where

  -- the state at stage i of the run the lasso unwinds to
  stateAt : (v0 : Val) -> Lasso P v0 -> Nat -> Val
  stateAt v0 l i = posState (posIter loop i (v0 , rest))
    where open Lasso l

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Run -- a lasso unwound into a run: the positions of
-- LTL.Countermodel.Orbit at valuations, with the cycle (c0 , c1).
--
-- A position (s , rest) is VALID when rest is a walk from s back to the
-- cycle's end b.  The successor preserves validity, and the step proof falls
-- out of consuming the Walk constructor: no arithmetic.

module LTL.Countermodel.Run where

open import LTL.Countermodel.Lasso public
open import LTL.Countermodel.Orbit Val public

------------------------------------------------------------------------
-- Valid positions.  This is the whole invariant; that consecutive positions
-- are transitions follows from it.

data ValidPos (P : Formula) (b : Val) : Pos -> Set where
  vpos : (s : Val) (rest : List Val) -> s ∈ Uinf P
      -> Walk P (Uinf P) s rest b -> ValidPos P b (s , rest)

posStep : (P : Formula) (b c0 : Val) (c1 : List Val)
       -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
       -> {pos : Pos} -> ValidPos P b pos
       -> ValidPos P b (nextPos c0 c1 pos) ×
          step P (posState pos) (posState (nextPos c0 c1 pos)) ≡ true
posStep P b c0 c1 mc0 wc stb (vpos s []        ms wnil) =
  vpos c0 c1 mc0 wc , stb
posStep P b c0 c1 mc0 wc stb (vpos s (w ∷ ws) ms (wcons mw st wk)) =
  vpos w ws mw wk , st

posIn : (P : Formula) (b : Val) {pos : Pos}
     -> ValidPos P b pos -> posState pos ∈ Uinf P
posIn P b (vpos s rest ms wk) = ms

------------------------------------------------------------------------
-- The run of a lasso.  The cycle is split into its head c0 and tail c1, which
-- makes nextPos total; the lasso's cycleNonEmpty licenses the split.  rest is
-- everything after v0 up to the first return to b: the stem followed by one
-- turn of the cycle.  Where a Run is taken apart whole, its fields are bound
-- in order as  b c0 c1 mc0 wc stb mbc cyc rest mv0 wr .

record Run (P : Formula) (v0 : Val) : Set where
  constructor mkRun
  field
    b           : Val       -- the last state of the cycle
    c0          : Val       -- the head of the cycle
    c1          : List Val  -- the tail of the cycle, ending at b
    headIn      : c0 ∈ Uinf P
    cycleWalk   : Walk P (Uinf P) c0 c1 b
    closingStep : step P b c0 ≡ true
    endOnCycle  : b ∈ c0 ∷ c1
    fulfilled   : AllFulfilled P b (c0 ∷ c1) (b ∷ c0 ∷ c1)
    rest        : List Val
    startIn     : v0 ∈ Uinf P
    restWalk    : Walk P (Uinf P) v0 rest b

runOf : (P : Formula) (v0 : Val) -> v0 ∈ Uinf P -> Lasso P v0 -> Run P v0
runOf P v0 mv0 (mkLasso b mb ps wp []       wq () cyc)
runOf P v0 mv0 (mkLasso b mb ps wp (q ∷ qs) (wcons mq st wqs) nn cyc) =
  mkRun b q qs mq wqs st (walkEnd P (Uinf P) wqs) cyc
        (ps ++ q ∷ qs) mv0
        (walkApp P (Uinf P) wp (wcons mq st wqs))

------------------------------------------------------------------------
-- Validity is preserved along the run, hence throughout an orbit

module _ (P : Formula) where

  posIterValid : (b c0 : Val) (c1 : List Val)
              -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
              -> (t : Nat) (pos : Pos) -> ValidPos P b pos
              -> ValidPos P b (posIter c0 c1 t pos)
  posIterValid b c0 c1 mc0 wc stb zero    pos vp = vp
  posIterValid b c0 c1 mc0 wc stb (suc t) pos vp =
    posIterValid b c0 c1 mc0 wc stb t (nextPos c0 c1 pos)
                 (fst (posStep P b c0 c1 mc0 wc stb vp))

  orbitValid : (b c0 : Val) (c1 : List Val)
            -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
            -> (pos q : Pos) -> ValidPos P b pos -> q ∈ orbitOf c0 c1 pos
            -> ValidPos P b q
  orbitValid b c0 c1 mc0 wc stb pos q vp m =
    fromIter (orbitOf-iter c0 c1 pos q m)
    where
      fromIter : (Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q) -> ValidPos P b q
      fromIter (t , et) =
        subst (λ r -> ValidPos P b r) et
              (posIterValid b c0 c1 mc0 wc stb t pos vp)

  -- the state of the run at stage i
  stateAt : (v0 : Val) -> Run P v0 -> Nat -> Val
  stateAt v0 r i = posState (posIter c0 c1 i (v0 , rest))
    where open Run r

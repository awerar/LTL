{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Gfp -- the set W of Theorem 4.1, case (R2), and the only property of it
-- the proof uses: that it is CLOSED under ->-steps inside U_k.
--
-- m4.tex writes the invariant as B = beta_W with W = Reach_{U_k}(v).  The two
-- facts wanted are that every state of W leaves the j-th eventuality pending
-- (step (i)) and that W is closed under successors lying in U_k (step (ii)).
-- Taking W to be the reachable set makes closure a theorem about the fixed
-- point of an ACCUMULATING iteration: acc grows, and one has to know that
-- |U_k| rounds are enough, which is a pigeonhole argument over a duplicate-free
-- accumulator.
--
-- Take instead the largest ->-closed set of states at which A still holds:
--
--    W_0 := { w in U_k : A in w },     W_{i+1} := { w in W_i : succ_{U_k}(w) subset W_i }
--
-- and W := the first W_i that is already closed.  This is a REMOVING
-- iteration, so closure comes out with no counting at all.  The price is that
-- (R2) now reads "v lies in W" rather than "A holds throughout Reach_{U_k}(v)";
-- gfpSound and gfpComplete at the end of this file show the two are the same
-- condition, with Reach given by its proper definition, the inductive type Path
-- of ->-paths inside U_k.
--
-- G29 of FORMALISATION-PLAN.md: the iteration runs until a round finds
-- nothing to remove and STOPS THERE, with termination by recursion on a Bar.
-- So the search does one pass once it has converged, the closed case returns W
-- itself, and no fixed-point equation or ≤ measure is needed.

module LTL.Gfp where

open import LTL.Closure public

------------------------------------------------------------------------
-- The greatest closed set of states at which A still holds.
--
-- holdsAt P A w says that the eventuality  □ A  is NOT fulfilled at w, in the
-- terminology of m4.tex section 3: fulfilment is  A not in w .

module _ (P : Formula) where

  holdsAt : Formula -> Val -> Bool
  holdsAt A w = valOf P w A

  -- W_0 of the header: the states of us at which A holds.

  wZero : List Val -> Formula -> List Val
  wZero us A = filter (holdsAt A) us

  -- Every successor of w that lies in us also lies in W.  shrink keeps exactly
  -- the w of W for which this is true.

  succsInside : List Val -> List Val -> Val -> Bool
  succsInside us W w = all (λ w' -> step P w w' ⇒ᵇ (w' ∈ᵛ W)) us

  shrink : List Val -> List Val -> List Val
  shrink us W = filter (succsInside us W) W

  ------------------------------------------------------------------------
  -- The iteration, run until it stops.
  --
  -- findFalse asks the one question the round needs: is there a state of W with
  -- a successor in us that has already left W?  If there is not, W is closed
  -- and is the answer.  If there is, that state leaves W -- and it leaves the
  -- Bar's predicate with it, which is what dropAllSat says and what makes the
  -- recursive call structurally smaller.

  shrinkGo   : (us : List Val) {E : Pred} (W : List Val)
            -> AllSat E W -> IFin E -> List Val
  shrinkFind : (us : List Val) {E : Pred} (W : List Val)
            -> AllSat E W -> IFin E -> FindResult (succsInside us W) W
            -> List Val

  shrinkGo us W sb bar = shrinkFind us W sb bar (findFalse (succsInside us W) W)

  shrinkFind us W sb bar      (allTrue f)   = W
  shrinkFind us W sb (cBar h) (found x m q) =
    shrinkGo us (shrink us W) (dropAllSat (succsInside us W) W sb x q)
             (h x (sb x m))

  gfpW : List Val -> Formula -> List Val
  gfpW us A = shrinkGo us (wZero us A) (memAllSat (wZero us A))
                       (listBar (wZero us A))

  ------------------------------------------------------------------------
  -- Closure, which is what step (ii) of Theorem 4.1 needs

  ClosedIn : List Val -> List Val -> Set
  ClosedIn us W =
    (w w' : Val) -> w ∈ W -> w' ∈ us -> step P w w' ≡ true -> w' ∈ W

  -- The same for a family X : Val -> Set in place of the list W.

  ClosedFam : List Val -> (Val -> Set) -> Set
  ClosedFam us X =
    (w w' : Val) -> X w -> w' ∈ us -> step P w w' ≡ true -> X w'

  closedOfAll : (us W : List Val)
             -> ({x : Val} -> x ∈ W -> succsInside us W x ≡ true)
             -> ClosedIn us W
  closedOfAll us W f w w' mw mw' st =
    ∈ᵛ-sound w' W
      (⇒ᵇ-mp (step P w w') (w' ∈ᵛ W)
                (all-at (λ z -> step P w z ⇒ᵇ (z ∈ᵛ W)) us mw' (f mw))
                st)

  shrinkGoClosed   : (us : List Val) {E : Pred} (W : List Val)
                     (sb : AllSat E W) (bar : IFin E)
                  -> ClosedIn us (shrinkGo us W sb bar)
  shrinkFindClosed : (us : List Val) {E : Pred} (W : List Val)
                     (sb : AllSat E W) (bar : IFin E)
                  -> (fr : FindResult (succsInside us W) W)
                  -> ClosedIn us (shrinkFind us W sb bar fr)

  shrinkGoClosed us W sb bar =
    shrinkFindClosed us W sb bar (findFalse (succsInside us W) W)

  shrinkFindClosed us W sb bar      (allTrue f)   = closedOfAll us W f
  shrinkFindClosed us W sb (cBar h) (found x m q) =
    shrinkGoClosed us (shrink us W) (dropAllSat (succsInside us W) W sb x q)
                   (h x (sb x m))

  gfpClosed : (us : List Val) (A : Formula)
           -> ClosedIn us (gfpW us A)
  gfpClosed us A =
    shrinkGoClosed us (wZero us A) (memAllSat (wZero us A))
                   (listBar (wZero us A))

  ------------------------------------------------------------------------
  -- The other two properties: W sits inside U_k, and A holds throughout it

  shrinkGoSub   : (us : List Val) {E : Pred} (W : List Val)
                  (sb : AllSat E W) (bar : IFin E)
               -> {z : Val} -> z ∈ shrinkGo us W sb bar -> z ∈ W
  shrinkFindSub : (us : List Val) {E : Pred} (W : List Val)
                  (sb : AllSat E W) (bar : IFin E)
               -> (fr : FindResult (succsInside us W) W) {z : Val}
               -> z ∈ shrinkFind us W sb bar fr -> z ∈ W

  shrinkGoSub us W sb bar =
    shrinkFindSub us W sb bar (findFalse (succsInside us W) W)

  shrinkFindSub us W sb bar      (allTrue f)   mz = mz
  shrinkFindSub us W sb (cBar h) (found x m q) mz =
    filter-sub (succsInside us W) W
               (shrinkGoSub us (shrink us W)
                            (dropAllSat (succsInside us W) W sb x q)
                            (h x (sb x m)) mz)

  gfpWZero : (us : List Val) (A : Formula) {w : Val}
          -> w ∈ gfpW us A -> w ∈ wZero us A
  gfpWZero us A =
    shrinkGoSub us (wZero us A) (memAllSat (wZero us A))
                (listBar (wZero us A))

  gfpIn : (us : List Val) (A : Formula) {w : Val}
       -> w ∈ gfpW us A -> w ∈ us
  gfpIn us A m = filter-sub (holdsAt A) us (gfpWZero us A m)

  gfpHolds : (us : List Val) (A : Formula) {w : Val}
          -> w ∈ gfpW us A -> valOf P w A ≡ true
  gfpHolds us A m = filter-prop (holdsAt A) us (gfpWZero us A m)

------------------------------------------------------------------------
-- Greatest: any closed family of states at which A holds is inside gfpW.
--
-- Stated for a family X : Val -> Set rather than a list, which is what lets
-- gfpComplete below instantiate it at Path.

module _ (P : Formula) (us : List Val) where

  shrinkGoGreatest   : {E : Pred} (W : List Val) (sb : AllSat E W) (bar : IFin E) (X : Val -> Set)
                    -> ((w : Val) -> X w -> w ∈ W)
                    -> ClosedFam P us X
                    -> (w : Val) -> X w -> w ∈ shrinkGo P us W sb bar
  shrinkFindGreatest : {E : Pred} (W : List Val) (sb : AllSat E W) (bar : IFin E)
                    -> (fr : FindResult (succsInside P us W) W) (X : Val -> Set)
                    -> ((w : Val) -> X w -> w ∈ W)
                    -> ClosedFam P us X
                    -> (w : Val) -> X w -> w ∈ shrinkFind P us W sb bar fr

  shrinkGoGreatest W sb bar =
    shrinkFindGreatest W sb bar (findFalse (succsInside P us W) W)

  shrinkFindGreatest W sb bar      (allTrue f)      X inW cl w x = inW w x
  shrinkFindGreatest W sb (cBar h) (found x0 m q) X inW cl w x =
    shrinkGoGreatest (shrink P us W) (dropAllSat (succsInside P us W) W sb x0 q)
                     (h x0 (sb x0 m)) X inW' cl w x
    where
      inW' : (z : Val) -> X z -> z ∈ shrink P us W
      inW' z xz =
        filter-true (succsInside P us W) W (inW z xz)
                    (all-intro (λ w' -> step P z w' ⇒ᵇ (w' ∈ᵛ W)) us inner)
        where
          inner : {w' : Val} -> w' ∈ us
               -> step P z w' ⇒ᵇ (w' ∈ᵛ W) ≡ true
          inner {w'} mw' =
            ⇒ᵇ-intro (step P z w') (w' ∈ᵛ W)
                      (λ st -> ∈ᵛ-complete w' W (inW w' (cl z w' xz mw' st)))

gfpGreatest : (P : Formula) (us : List Val) (A : Formula) (X : Val -> Set)
           -> ((w : Val) -> X w -> w ∈ us)
           -> ((w : Val) -> X w -> valOf P w A ≡ true)
           -> ClosedFam P us X
           -> (w : Val) -> X w -> w ∈ gfpW P us A
gfpGreatest P us A X inUs hol cl =
  shrinkGoGreatest P us (wZero P us A) (memAllSat (wZero P us A))
                   (listBar (wZero P us A)) X
                   (λ w x -> filter-true (holdsAt P A) us (inUs w x) (hol w x)) cl

------------------------------------------------------------------------
-- Reach_U(v) of m4.tex section 3, as an inductive type of ->-paths inside U.

data Path (P : Formula) (us : List Val) : Val -> Val -> Set where
  pnil  : {v : Val} -> Path P us v v
  pcons : {v w x : Val} -> w ∈ us -> step P v w ≡ true
       -> Path P us w x -> Path P us v x

module _ (P : Formula) where

  pathEnd : (us : List Val) {v w : Val}
         -> v ∈ us -> Path P us v w -> w ∈ us
  pathEnd us mv pnil            = mv
  pathEnd us mv (pcons mw st p) = pathEnd us mw p

  pathSnoc : (us : List Val) {v w w' : Val}
          -> Path P us v w -> w' ∈ us -> step P w w' ≡ true -> Path P us v w'
  pathSnoc us pnil            mw' st' = pcons mw' st' pnil
  pathSnoc us (pcons mw st p) mw' st' = pcons mw st (pathSnoc us p mw' st')

  ------------------------------------------------------------------------
  -- (R2), the note's way and this one, are the same condition.

  gfpPath : (us : List Val) (A : Formula) {v w : Val}
         -> v ∈ gfpW P us A -> Path P us v w -> w ∈ gfpW P us A
  gfpPath us A m pnil            = m
  gfpPath us A m (pcons mw st p) =
    gfpPath us A (gfpClosed P us A _ _ m mw st) p

  -- v in gfpW  implies  no state reachable from v fulfils the eventuality
  gfpSound : (us : List Val) (A : Formula) (v : Val)
          -> v ∈ gfpW P us A
          -> (w : Val) -> Path P us v w -> valOf P w A ≡ true
  gfpSound us A v m w p = gfpHolds P us A (gfpPath us A m p)

  -- and conversely
  gfpComplete : (us : List Val) (A : Formula) (v : Val)
             -> v ∈ us
             -> ((w : Val) -> Path P us v w -> valOf P w A ≡ true)
             -> v ∈ gfpW P us A
  gfpComplete us A v mv h =
    gfpGreatest P us A (λ w -> Path P us v w)
                (λ w p -> pathEnd us mv p)
                h
                (λ w w' p mw' st -> pathSnoc us p mw' st)
                v pnil

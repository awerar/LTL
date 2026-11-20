{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SCC.Graph -- the finite fair-graph certificate theorem.
--
--   Given a finite graph, finitely many decidable fairness predicates, and a
--   vertex v, compute either
--     (a) a lasso from v whose cycle meets every predicate (FairLoop), or
--     (b) a well-founded certificate that every recurrent component reachable
--         from v misses some predicate (Cert).
--
-- That is fairGraph, at the end of the file; certAll is the induction
-- principle a Cert supplies.  The two answers are proved exclusive
-- (certNoCirc, fairNoLoop), so the negative answer is a decision.
--
-- There is no logic here: the module is parameterised by a node type with a
-- sound, reflexive equality test, and imports only the generic set layer.  The
-- graph is a vertex list with an edge test G : Edges, the fairness sets are
-- fs : List Pred.  LTL.SCC.SccLasso instantiates it at Val; LTL.Tests.
-- GraphExamples at Nat, for the computational checks.
--
-- Design choices:
--
-- 1. The reachable set is computed by a GROWING search that stops when a round
--    adds nothing; completeness comes from the stopping condition, not a bound.
-- 2. A component is a representative plus a filter (sccOf); the condensation
--    is never built, and "terminal" is a boolean.
-- 3. graphGo is a REMOVING iteration (refute a sink or a terminal component,
--    delete it), so a Bar covers termination; findTerm finds a terminal
--    component by following condensation edges, again by Bar recursion.
-- 4. Every Bar comes from listBar, which is blocked while the list is a
--    variable, so no guard is needed against normalisation blow-up.
--
-- Exclusivity needs no infinite paths: a vertex on a cycle has a successor,
-- so a sink lies on no cycle; and any vertex of a cycle reaches any other, so
-- a cycle that enters a successor-closed block never leaves it.  Both are
-- inductions on a finite trail.

open import LTL.Lib.Prelude

module LTL.SCC.Graph {Node : Set}
                 (_≡ᵛ_     : Node -> Node -> Bool)
                 (≡ᵛ-sound : (v w : Node) -> v ≡ᵛ w ≡ true -> v ≡ w)
                 (≡ᵛ-refl  : (v : Node) -> v ≡ᵛ v ≡ true)
  where

-- Not re-exported: an importer gets this module's own names only, and takes
-- the set layer from wherever it already has it (LTL.States.Reach, at Val).

open import LTL.Lib.Bar
open import LTL.Lib.Nodes _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl

------------------------------------------------------------------------
-- Glue

appNotNull : {A : Set} (xs ys : List A) -> null xs ≡ false
          -> null (xs ++ ys) ≡ false
appNotNull []       ys ()
appNotNull (x ∷ xs) ys e = refl

null-notMem : (ws : List Node) (z : Node) -> null ws ≡ true -> z ∈ᵛ ws ≡ false
null-notMem []       z e = refl
null-notMem (w ∷ ws) z ()

-- The out-neighbours of x inside ws.  For G = step P this is succs P ws x on
-- the nose.

outs : List Node -> Edges -> Node -> List Node
outs ws G x = filter (G x) ws

hasOut : List Node -> Edges -> Node -> Bool
hasOut ws G x = ¬ᵇ null (outs ws G x)

------------------------------------------------------------------------
-- Trails: finite paths inside ws, carrying the vertices visited and indexed by
-- the endpoint (LTL.Countermodel.Walk with step P replaced by G).  A cycle is a
-- trail from r to r with a non-empty list.

data Trail (ws : List Node) (G : Edges) : Node -> List Node -> Node -> Set where
  tNil  : {v : Node} -> Trail ws G v [] v
  tCons : {v x : Node} {zs : List Node} {w : Node}
       -> x ∈ ws -> G v x ≡ true -> Trail ws G x zs w
       -> Trail ws G v (x ∷ zs) w

module _ (ws : List Node) (G : Edges) where

  trailApp : {u v w : Node} {xs zs : List Node}
          -> Trail ws G u xs v -> Trail ws G v zs w -> Trail ws G u (xs ++ zs) w
  trailApp tNil           t2 = t2
  trailApp (tCons m e t1) t2 = tCons m e (trailApp t1 t2)

  trailEnd : {v : Node} {zs : List Node} {w : Node}
          -> Trail ws G v zs w -> w ∈ v ∷ zs
  trailEnd tNil          = here
  trailEnd (tCons m e t) = there (trailEnd t)

  -- A trail that takes at least one step ends at a vertex it visits.

  trailLast : {v : Node} {zs : List Node} {w : Node}
           -> Trail ws G v zs w -> null zs ≡ false -> w ∈ zs
  trailLast tNil          ()
  trailLast (tCons m e t) nn = trailEnd t

  trailIn : {v : Node} {zs : List Node} {w : Node}
         -> Trail ws G v zs w -> {z : Node} -> z ∈ zs -> z ∈ ws
  trailIn tNil          ()
  trailIn (tCons m e t) here      = m
  trailIn (tCons m e t) (there k) = trailIn t k

trailMono : (ws vs : List Node) (G : Edges)
         -> ws ⊆ vs
         -> {v : Node} {zs : List Node} {w : Node}
         -> Trail ws G v zs w -> Trail vs G v zs w
trailMono ws vs G sb tNil                  = tNil
trailMono ws vs G sb (tCons {x = x} m e t) =
  tCons (sb x m) e (trailMono ws vs G sb t)

data Reaches (ws : List Node) (G : Edges) (v w : Node) : Set where
  reachesBy : (zs : List Node) -> Trail ws G v zs w -> Reaches ws G v w

------------------------------------------------------------------------
-- The reachable set, as a growing search.  A round adds every vertex of ws
-- that is wanted -- is v, or is a G-successor of something already in acc --
-- and is not there yet; when a round adds nothing, acc contains every wanted
-- vertex, which is completeness.  (closeGo of LTL.States.Closure has the same
-- shape.)

reachWanted : Edges -> Node -> List Node -> Node -> Bool
reachWanted G v acc x = (v ≡ᵛ x) ∨ᵇ any (λ y -> G y x) acc

reachMissing : Edges -> Node -> List Node -> Node -> Bool
reachMissing G v acc x = reachWanted G v acc x ∧ᵇ ¬ᵇ (x ∈ᵛ acc)

reachSettled : Edges -> Node -> List Node -> Node -> Bool
reachSettled G v acc x = ¬ᵇ reachMissing G v acc x

reachRound : List Node -> Edges -> Node -> List Node -> List Node
reachRound ws G v acc = filter (reachMissing G v acc) ws ++ acc

reachMissingOf : (G : Edges) (v : Node) (acc : List Node) (x : Node)
              -> reachSettled G v acc x ≡ false -> reachMissing G v acc x ≡ true
reachMissingOf G v acc x q = ¬ᵇ-false (reachMissing G v acc x) q

reachNotInAcc : (G : Edges) (v : Node) (acc : List Node) (x : Node)
             -> reachSettled G v acc x ≡ false -> x ∈ᵛ acc ≡ false
reachNotInAcc G v acc x q =
  ¬ᵇ-true (x ∈ᵛ acc)
          (∧ᵇ-trueʳ (reachWanted G v acc x) (¬ᵇ (x ∈ᵛ acc))
                    (reachMissingOf G v acc x q))

module _ (ws : List Node) (G : Edges) (v : Node) where

  reachInRound : (acc : List Node) (x : Node)
              -> x ∈ ws -> reachSettled G v acc x ≡ false
              -> x ∈ reachRound ws G v acc
  reachInRound acc x m q =
    memAppL (filter (reachMissing G v acc) ws) acc
            (filter-true (reachMissing G v acc) ws m
                         (reachMissingOf G v acc x q))

  reachGo   : {E : Pred} (acc : List Node) -> Avail E ws acc
           -> IFin E -> List Node
  reachFind : {E : Pred} (acc : List Node) -> Avail E ws acc
           -> IFin E -> FindResult (reachSettled G v acc) ws -> List Node

  reachGo acc av bar =
    reachFind acc av bar (findFalse (reachSettled G v acc) ws)

  reachFind acc av bar          (allTrue f)   = acc
  reachFind {E} acc av (cBar h) (found x m q) =
    reachGo (reachRound ws G v acc) av'
            (h x (av x m (reachNotInAcc G v acc x q)))
    where
      av' : Avail (λ z -> E z ∧ᵇ (x ≢ᵛ z)) ws (reachRound ws G v acc)
      av' z mz e =
        ∧ᵇ-intro (E z) (x ≢ᵛ z)
                 (av z mz outAcc)
                 (cong ¬ᵇ_ outX)
        where
          outAcc : z ∈ᵛ acc ≡ false
          outAcc = refuteTrue (z ∈ᵛ acc) λ eb ->
            ∈ᵛ-false z (reachRound ws G v acc) e
             (memAppR (filter (reachMissing G v acc) ws) acc
                      (∈ᵛ-sound z acc eb))

          outX : x ≡ᵛ z ≡ false
          outX = refuteTrue (x ≡ᵛ z) λ eb ->
            ∈ᵛ-false z (reachRound ws G v acc) e
             (subst (λ y -> y ∈ reachRound ws G v acc)
                    (≡ᵛ-sound x z eb)
                    (reachInRound acc x m q))

  ------------------------------------------------------------------------
  -- Its four properties, each by the same recursion: the result lies in ws,
  -- its members are reached by trails, v is in it, and it is closed under
  -- G-successors inside ws.  The last two are the stopping condition read
  -- off.

  reachGoIn   : {E : Pred} (acc : List Node) (av : Avail E ws acc)
                (bar : IFin E)
             -> acc ⊆ ws
             -> {z : Node} -> z ∈ reachGo acc av bar -> z ∈ ws
  reachFindIn : {E : Pred} (acc : List Node) (av : Avail E ws acc)
                (bar : IFin E) (fr : FindResult (reachSettled G v acc) ws)
             -> acc ⊆ ws
             -> {z : Node} -> z ∈ reachFind acc av bar fr -> z ∈ ws

  reachGoIn acc av bar =
    reachFindIn acc av bar (findFalse (reachSettled G v acc) ws)

  reachFindIn acc av bar          (allTrue f)      sb {z} m = sb z m
  reachFindIn acc av (cBar h) (found x mx q) sb       m =
    reachGoIn (reachRound ws G v acc) _
              (h x (av x mx (reachNotInAcc G v acc x q))) sb' m
    where
      sb' : reachRound ws G v acc ⊆ ws
      sb' z mz = sumElim (λ m1 -> filter-sub (reachMissing G v acc) ws m1)
                         (λ m2 -> sb z m2)
                         (memAppCase (filter (reachMissing G v acc) ws) acc mz)

  -- Every vertex a round adds is reached by a trail: it is v, or a successor
  -- of a member of acc, whose trail grows by one step.

  addReaches : (acc : List Node)
            -> ((z : Node) -> z ∈ acc -> Reaches ws G v z)
            -> (z : Node) -> z ∈ reachRound ws G v acc -> Reaches ws G v z
  addReaches acc rc z m =
    sumElim fromNew (λ m2 -> rc z m2)
            (memAppCase (filter (reachMissing G v acc) ws) acc m)
    where
      fromNew : z ∈ filter (reachMissing G v acc) ws -> Reaches ws G v z
      fromNew m1 =
        sumElim isV viaY (∨ᵇ-true (v ≡ᵛ z) (any (λ y -> G y z) acc) want)
        where
          mzw : z ∈ ws
          mzw = filter-sub (reachMissing G v acc) ws m1

          want : reachWanted G v acc z ≡ true
          want = ∧ᵇ-trueˡ (reachWanted G v acc z) (¬ᵇ (z ∈ᵛ acc))
                          (filter-prop (reachMissing G v acc) ws m1)

          isV : v ≡ᵛ z ≡ true -> Reaches ws G v z
          isV ev = subst (λ y -> Reaches ws G v y) (≡ᵛ-sound v z ev)
                         (reachesBy [] tNil)

          viaY : any (λ y -> G y z) acc ≡ true -> Reaches ws G v z
          viaY ea = pick (any-true (λ y -> G y z) acc ea)
            where
              pick : (Σ[ y ∈ Node ] y ∈ acc × G y z ≡ true)
                  -> Reaches ws G v z
              pick (y , my , gy) = ext (rc y my)
                where
                  ext : Reaches ws G v y -> Reaches ws G v z
                  ext (reachesBy zs t) =
                    reachesBy (zs ++ z ∷ [])
                              (trailApp ws G t (tCons mzw gy tNil))

  reachGoTrail   : {E : Pred} (acc : List Node) (av : Avail E ws acc)
                   (bar : IFin E)
                -> ((z : Node) -> z ∈ acc -> Reaches ws G v z)
                -> {z : Node} -> z ∈ reachGo acc av bar -> Reaches ws G v z
  reachFindTrail : {E : Pred} (acc : List Node) (av : Avail E ws acc)
                   (bar : IFin E) (fr : FindResult (reachSettled G v acc) ws)
                -> ((z : Node) -> z ∈ acc -> Reaches ws G v z)
                -> {z : Node} -> z ∈ reachFind acc av bar fr -> Reaches ws G v z

  reachGoTrail acc av bar =
    reachFindTrail acc av bar (findFalse (reachSettled G v acc) ws)

  reachFindTrail acc av bar          (allTrue f)      rc {z} m = rc z m
  reachFindTrail acc av (cBar h) (found x mx q) rc       m =
    reachGoTrail (reachRound ws G v acc) _
                 (h x (av x mx (reachNotInAcc G v acc x q)))
                 (addReaches acc rc) m

  reachGoSeed   : {E : Pred} (acc : List Node) (av : Avail E ws acc)
                  (bar : IFin E)
               -> v ∈ ws -> v ∈ reachGo acc av bar
  reachFindSeed : {E : Pred} (acc : List Node) (av : Avail E ws acc)
                  (bar : IFin E) (fr : FindResult (reachSettled G v acc) ws)
               -> v ∈ ws -> v ∈ reachFind acc av bar fr

  reachGoSeed acc av bar =
    reachFindSeed acc av bar (findFalse (reachSettled G v acc) ws)

  reachFindSeed acc av bar          (allTrue f)      mv =
    ∈ᵛ-sound v acc
      (¬ᵇ-false (v ∈ᵛ acc)
                (¬ᵇ∧ᵇ-cancelˡ (reachWanted G v acc v) (¬ᵇ (v ∈ᵛ acc)) (f mv)
                   (∨ᵇ-introˡ (v ≡ᵛ v) (any (λ y -> G y v) acc) (≡ᵛ-refl v))))
  reachFindSeed acc av (cBar h) (found x mx q) mv =
    reachGoSeed (reachRound ws G v acc) _
                (h x (av x mx (reachNotInAcc G v acc x q))) mv

  reachGoClosed   : {E : Pred} (acc : List Node) (av : Avail E ws acc)
                    (bar : IFin E) {u w : Node}
                 -> u ∈ reachGo acc av bar -> w ∈ ws -> G u w ≡ true
                 -> w ∈ reachGo acc av bar
  reachFindClosed : {E : Pred} (acc : List Node) (av : Avail E ws acc)
                    (bar : IFin E) (fr : FindResult (reachSettled G v acc) ws)
                    {u w : Node}
                 -> u ∈ reachFind acc av bar fr -> w ∈ ws -> G u w ≡ true
                 -> w ∈ reachFind acc av bar fr

  reachGoClosed acc av bar =
    reachFindClosed acc av bar (findFalse (reachSettled G v acc) ws)

  reachFindClosed acc av bar      (allTrue f)      {u} {w} mu mw st =
    ∈ᵛ-sound w acc
      (¬ᵇ-false (w ∈ᵛ acc)
                (¬ᵇ∧ᵇ-cancelˡ (reachWanted G v acc w) (¬ᵇ (w ∈ᵛ acc)) (f mw)
                              (∨ᵇ-introʳ (v ≡ᵛ w) (any (λ y -> G y w) acc)
                                         (any-intro (λ y -> G y w) acc mu st))))
  reachFindClosed acc av (cBar h) (found x mx q) mu mw st =
    reachGoClosed (reachRound ws G v acc) _
                  (h x (av x mx (reachNotInAcc G v acc x q)))
                  mu mw st

------------------------------------------------------------------------
-- The reachable set itself

reachAvInit : (ws : List Node) (z : Node) -> z ∈ ws -> z ∈ᵛ [] ≡ false
           -> z ∈ᵛ ws ≡ true
reachAvInit ws z mz e = ∈ᵛ-complete z ws mz

emptyAccIn : (ws : List Node) (z : Node) -> z ∈ [] {A = Node} -> z ∈ ws
emptyAccIn ws z ()

emptyAccReaches : (ws : List Node) (G : Edges) (v : Node) (z : Node)
               -> z ∈ [] {A = Node} -> Reaches ws G v z
emptyAccReaches ws G v z ()

reachSet : List Node -> Edges -> Node -> List Node
reachSet ws G v = reachGo ws G v [] (reachAvInit ws) (listBar ws)

reachIn : (ws : List Node) (G : Edges) (v : Node) {z : Node}
       -> z ∈ reachSet ws G v -> z ∈ ws
reachIn ws G v =
  reachGoIn ws G v [] (reachAvInit ws) (listBar ws) (emptyAccIn ws)

reachTrail : (ws : List Node) (G : Edges) (v : Node) {z : Node}
          -> z ∈ reachSet ws G v -> Reaches ws G v z
reachTrail ws G v =
  reachGoTrail ws G v [] (reachAvInit ws) (listBar ws)
               (emptyAccReaches ws G v)

reachSeed : (ws : List Node) (G : Edges) (v : Node)
         -> v ∈ ws -> v ∈ reachSet ws G v
reachSeed ws G v = reachGoSeed ws G v [] (reachAvInit ws) (listBar ws)

reachClosed : (ws : List Node) (G : Edges) (v : Node) {u w : Node}
           -> u ∈ reachSet ws G v -> w ∈ ws -> G u w ≡ true
           -> w ∈ reachSet ws G v
reachClosed ws G v = reachGoClosed ws G v [] (reachAvInit ws) (listBar ws)

-- Completeness: a trail from a member of the set stays in the set, by
-- induction along the trail against the stopping condition.

reachTrailIn : (ws : List Node) (G : Edges) (v : Node)
               {u : Node} {zs : List Node} {w : Node}
            -> u ∈ reachSet ws G v -> Trail ws G u zs w -> w ∈ reachSet ws G v
reachTrailIn ws G v mu tNil                   = mu
reachTrailIn ws G v mu (tCons {x = x} mx e t) =
  reachTrailIn ws G v (reachClosed ws G v mu mx e) t

reachComplete : (ws : List Node) (G : Edges) (v : Node) -> v ∈ ws
             -> {zs : List Node} {w : Node} -> Trail ws G v zs w
             -> w ∈ reachSet ws G v
reachComplete ws G v mv t = reachTrailIn ws G v (reachSeed ws G v mv) t

reachTrans : (ws : List Node) (G : Edges) (v u w : Node)
          -> u ∈ reachSet ws G v -> w ∈ reachSet ws G u
          -> w ∈ reachSet ws G v
reachTrans ws G v u w mu mw = onR (reachTrail ws G u mw)
  where
    onR : Reaches ws G u w -> w ∈ reachSet ws G v
    onR (reachesBy zs t) = reachTrailIn ws G v mu t

------------------------------------------------------------------------
-- Components, without component objects: sccOf ws G r is the vertices r
-- reaches that reach r back.  A filter of a list, nothing more.

sccOf : List Node -> Edges -> Node -> List Node
sccOf ws G r = filter (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r)

sccReach : (ws : List Node) (G : Edges) (r : Node) (w : Node)
        -> w ∈ sccOf ws G r -> w ∈ reachSet ws G r
sccReach ws G r w m =
  filter-sub (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) m

sccIn : (ws : List Node) (G : Edges) (r : Node) (w : Node)
     -> w ∈ sccOf ws G r -> w ∈ ws
sccIn ws G r w m = reachIn ws G r (sccReach ws G r w m)

sccTo : (ws : List Node) (G : Edges) (r : Node) (w : Node)
     -> w ∈ sccOf ws G r -> Reaches ws G r w
sccTo ws G r w m = reachTrail ws G r (sccReach ws G r w m)

sccFrom : (ws : List Node) (G : Edges) (r : Node) (w : Node)
       -> w ∈ sccOf ws G r -> Reaches ws G w r
sccFrom ws G r w m =
  reachTrail ws G w
    (∈ᵛ-sound r (reachSet ws G w)
      (filter-prop (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) m))

sccRep : (ws : List Node) (G : Edges) (r : Node)
      -> r ∈ ws -> r ∈ sccOf ws G r
sccRep ws G r mr =
  filter-true (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r)
              (reachSeed ws G r mr)
              (∈ᵛ-complete r (reachSet ws G r) (reachSeed ws G r mr))

------------------------------------------------------------------------
-- r's component is terminal when everything r reaches reaches r back, i.e.
-- the reachable set of r IS its component.

isTerminal : List Node -> Edges -> Node -> Bool
isTerminal ws G r = all (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r)

termScc : (ws : List Node) (G : Edges) (r : Node)
       -> isTerminal ws G r ≡ true
       -> {w : Node} -> w ∈ reachSet ws G r -> w ∈ sccOf ws G r
termScc ws G r et {w} m =
  filter-true (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) m
              (all-at (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) m et)

-- A terminal component is closed under successors inside ws: the refutation
-- needs exactly this of it.

termClosed : (ws : List Node) (G : Edges) (r : Node)
          -> isTerminal ws G r ≡ true -> Closed ws G (sccOf ws G r)
termClosed ws G r et z y mz my e =
  termScc ws G r et (reachClosed ws G r (sccReach ws G r z mz) my e)

------------------------------------------------------------------------
-- A non-empty graph has a terminal component.  While r's component is not
-- terminal, there is a w that r reaches and that does not reach r; move the
-- representative to w.  This is a Bar search whose invariant is that every
-- vertex of the current reachable set still satisfies the Bar predicate;
-- giving up r is the sub-Bar cBar hands over, and the new reachable set
-- avoids r because w does not reach r.

-- A vertex whose component is terminal, found by the search above.

data Terminal (ws : List Node) (G : Edges) : Set where
  terminalAt : (r : Node) -> r ∈ ws -> isTerminal ws G r ≡ true -> Terminal ws G

module _ (ws : List Node) (G : Edges) where

  termGo   : (r : Node) -> r ∈ ws -> {E : Pred}
          -> AllSat E (reachSet ws G r) -> IFin E -> Terminal ws G
  termFind : (r : Node) -> r ∈ ws -> {E : Pred}
          -> AllSat E (reachSet ws G r) -> IFin E
          -> FindResult (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r)
          -> Terminal ws G

  termGo r mr av bar =
    termFind r mr av bar
             (findFalse (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r))

  termFind r mr av bar          (allTrue f)       =
    terminalAt r mr
               (all-intro (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r) f)
  termFind r mr {E} av (cBar h) (found w mw q) =
    termGo w (reachIn ws G r mw) av' (h r (av r (reachSeed ws G r mr)))
    where
      av' : (z : Node) -> z ∈ reachSet ws G w -> E z ∧ᵇ (r ≢ᵛ z) ≡ true
      av' z mz =
        ∧ᵇ-intro (E z) (r ≢ᵛ z)
                 (av z (reachTrans ws G r w z mw mz))
                 (cong ¬ᵇ_ notR)
        where
          notR : r ≡ᵛ z ≡ false
          notR = refuteTrue (r ≡ᵛ z) λ eb ->
            true≢false (trans (sym (rIn eb)) q)
            where
              rIn : r ≡ᵛ z ≡ true -> r ∈ᵛ reachSet ws G w ≡ true
              rIn eb = ∈ᵛ-complete r (reachSet ws G w)
                         (subst (λ y -> y ∈ reachSet ws G w)
                                (sym (≡ᵛ-sound r z eb)) mz)

  findTerm : (r : Node) -> r ∈ ws
          -> Terminal ws G
  findTerm r mr =
    termGo r mr (λ z mz -> ∈ᵛ-complete z ws (reachIn ws G r mz)) (listBar ws)

------------------------------------------------------------------------
-- The positive certificate: a fair circuit at r, a non-empty closed trail
-- through r with a witness on it for every fairness predicate.  It is built by
-- picking a witness for each predicate and joining them by trails inside the
-- component.

record Circuit (ws : List Node) (G : Edges) (fs : List Pred)
               (r : Node) : Set where
  constructor circuit
  field
    cycle    : List Node
    trail    : Trail ws G r cycle r
    nonEmpty : null cycle ≡ false
    meets    : (f : Pred) -> f ∈ fs -> Σ[ z ∈ Node ] z ∈ cycle × f z ≡ true

circMono : (ws vs : List Node) (G : Edges) (fs : List Pred)
           (r : Node) -> ws ⊆ vs
        -> Circuit ws G fs r -> Circuit vs G fs r
circMono ws vs G fs r sb (circuit cy t nn wit) =
  circuit cy (trailMono ws vs G sb t) nn wit

-- C meets every fairness predicate: each f in fs holds somewhere in C.

meetsAll : List Pred -> List Node -> Bool
meetsAll fs C = all (λ g -> any g C) fs

data Loop (ws : List Node) (G : Edges) (r : Node) : Set where
  loopBy : (cy : List Node) -> Trail ws G r cy r -> null cy ≡ false
        -> Loop ws G r

-- A terminal component of a vertex that has a successor is non-trivial: the
-- successor is reached, so terminality sends a trail back.  No separate cycle
-- detection is needed.

module _ (ws : List Node) (G : Edges) (r : Node) where

  loopAt : r ∈ ws
        -> isTerminal ws G r ≡ true -> hasOut ws G r ≡ true -> Loop ws G r
  loopAt mr et ho =
    pick (null-false (outs ws G r) (¬ᵇ-true (null (outs ws G r)) ho))
    where
      pick : (Σ[ x ∈ Node ] x ∈ outs ws G r) -> Loop ws G r
      pick (x , mx) = back (sccFrom ws G r x (termScc ws G r et inR))
        where
          mxw : x ∈ ws
          mxw = filter-sub (G r) ws mx

          grx : G r x ≡ true
          grx = filter-prop (G r) ws mx

          inR : x ∈ reachSet ws G r
          inR = reachClosed ws G r (reachSeed ws G r mr) mxw grx

          back : Reaches ws G x r -> Loop ws G r
          back (reachesBy zs t) = loopBy (x ∷ zs) (tCons mxw grx t) refl

  -- One fairness predicate added to a circuit.  The leg is  loop ++ (r to w)
  -- ++ (w to r) , with the loop in front so that the r-to-w half is non-empty
  -- and w is a vertex the leg VISITS.  trailApp is left-nested so that
  -- associativity never appears.

  consCirc : (cy0 : List Node) -> Trail ws G r cy0 r -> null cy0 ≡ false
          -> (f : Pred) (w : Node) -> f w ≡ true
          -> Reaches ws G r w -> Reaches ws G w r
          -> (fs : List Pred) -> Circuit ws G fs r
          -> Circuit ws G (f ∷ fs) r
  consCirc cy0 t0 nn f w fw (reachesBy as ta) (reachesBy bs tb) fs
           (circuit cy t nnc wit) =
    circuit (leg ++ cy) (trailApp ws G legT t) (appNotNull leg cy legNN) each
    where
      front : List Node
      front = cy0 ++ as

      frontT : Trail ws G r front w
      frontT = trailApp ws G t0 ta

      frontNN : null front ≡ false
      frontNN = appNotNull cy0 as nn

      leg : List Node
      leg = front ++ bs

      legT : Trail ws G r leg r
      legT = trailApp ws G frontT tb

      legNN : null leg ≡ false
      legNN = appNotNull front bs frontNN

      mw : w ∈ leg
      mw = memAppL front bs (trailLast ws G frontT frontNN)

      each : (g : Pred) -> g ∈ f ∷ fs
          -> Σ[ z ∈ Node ] z ∈ leg ++ cy × g z ≡ true
      each g here      = w , memAppL leg cy mw , fw
      each g (there m) = shift (wit g m)
        where
          shift : (Σ[ z ∈ Node ] z ∈ cy × g z ≡ true)
               -> Σ[ z ∈ Node ] z ∈ leg ++ cy × g z ≡ true
          shift (z , mz , gz) = z , memAppR leg cy mz , gz

  mkCirc : (cy0 : List Node) -> Trail ws G r cy0 r -> null cy0 ≡ false
        -> (C : List Node)
        -> ((u : Node) -> u ∈ C -> Reaches ws G r u)
        -> ((u : Node) -> u ∈ C -> Reaches ws G u r)
        -> (fs : List Pred) -> meetsAll fs C ≡ true
        -> Circuit ws G fs r
  mkCirc cy0 t0 nn C to from []        e = circuit cy0 t0 nn noF
    where
      noF : (f : Pred) -> f ∈ []
         -> Σ[ z ∈ Node ] z ∈ cy0 × f z ≡ true
      noF f ()
  mkCirc cy0 t0 nn C to from (f ∷ fs) e =
    pick (any-true f C (∧ᵇ-trueˡ (any f C) (meetsAll fs C) e))
    where
      rest : Circuit ws G fs r
      rest = mkCirc cy0 t0 nn C to from fs
                    (∧ᵇ-trueʳ (any f C) (meetsAll fs C) e)

      pick : (Σ[ w ∈ Node ] w ∈ C × f w ≡ true)
          -> Circuit ws G (f ∷ fs) r
      pick (w , mw , fw) =
        consCirc cy0 t0 nn f w fw (to w mw) (from w mw) fs rest

------------------------------------------------------------------------
-- One step of the outer iteration, decided: given that every vertex of ws has
-- an out-edge, ws is empty, or its terminal component is fair and a circuit is
-- built, or it misses some f and is a block to be refuted.  Nothing here
-- recurses.

data Block (ws : List Node) (G : Edges) (fs : List Pred) : Set where
  bEmpty  : null ws ≡ true -> Block ws G fs
  bFair   : (r : Node) -> r ∈ ws -> Circuit ws G fs r -> Block ws G fs
  bUnfair : (r : Node) -> r ∈ ws -> isTerminal ws G r ≡ true
         -> (f : Pred) -> f ∈ fs -> any f (sccOf ws G r) ≡ false
         -> Block ws G fs

blockOf : (ws : List Node) (G : Edges) (fs : List Pred)
       -> ({x : Node} -> x ∈ ws -> hasOut ws G x ≡ true)
       -> Terminal ws G -> Block ws G fs
blockOf ws G fs h (terminalAt r mr et) with meetsAll fs (sccOf ws G r) in eb
... | true  = fromLoop (loopAt ws G r mr et (h mr))
  where
    fromLoop : Loop ws G r -> Block ws G fs
    fromLoop (loopBy cy t nn) =
      bFair r mr (mkCirc ws G r cy t nn (sccOf ws G r)
                         (sccTo ws G r) (sccFrom ws G r) fs eb)
... | false = unf (all-false (λ g -> any g (sccOf ws G r)) fs eb)
  where
    unf : (Σ[ g ∈ Pred ] g ∈ fs × any g (sccOf ws G r) ≡ false)
       -> Block ws G fs
    unf (g , mg , eg) = bUnfair r mr et g mg eg

pickBlock : (ws : List Node) (G : Edges) (fs : List Pred)
         -> ({x : Node} -> x ∈ ws -> hasOut ws G x ≡ true) -> Block ws G fs
pickBlock []       G fs h = bEmpty refl
pickBlock (u ∷ ws) G fs h =
  blockOf (u ∷ ws) G fs h (findTerm (u ∷ ws) G u here)

------------------------------------------------------------------------
-- The negative certificate: a well-founded record of the removal order,
-- indexed by what is LEFT.  Each step removes a vertex with no out-edge inside
-- ws, or a block closed under out-edges inside ws that misses a fairness
-- predicate.  cNil says nothing is left.

infixl 6 _∖ᵛ_ _∖_

_∖ᵛ_ : List Node -> Node -> List Node
ws ∖ᵛ x = filter (x ≢ᵛ_) ws

_∖_ : List Node -> List Node -> List Node
ws ∖ C = filter (λ z -> ¬ᵇ (z ∈ᵛ C)) ws

data Cert (G : Edges) (fs : List Pred) : List Node -> Set where
  cNil   : (ws : List Node) -> null ws ≡ true -> Cert G fs ws
  cSink  : (ws : List Node) (x : Node) -> x ∈ ws
        -> null (outs ws G x) ≡ true
        -> Cert G fs (ws ∖ᵛ x) -> Cert G fs ws
  cBlock : (ws C : List Node) (f : Pred) -> f ∈ fs
        -> C ⊆ ws -> Closed ws G C -> NoneSat f C
        -> Cert G fs (ws ∖ C) -> Cert G fs ws

------------------------------------------------------------------------
-- The theorem, on a sub-list

data FairIn (ws : List Node) (G : Edges) (fs : List Pred) : Set where
  fairIn : (r : Node) -> r ∈ ws -> Circuit ws G fs r -> FairIn ws G fs

fairInMono : (ws vs : List Node) (G : Edges) (fs : List Pred)
          -> ws ⊆ vs
          -> FairIn ws G fs -> FairIn vs G fs
fairInMono ws vs G fs sb (fairIn r mr c) =
  fairIn r (sb r mr) (circMono ws vs G fs r sb c)

-- Terminal-component removal, a REMOVING iteration: whichever step applies,
-- the vertex it names (the sink x, or the block's representative r) leaves ws
-- and the Bar's predicate with it (dropAllSat).

module _ (G : Edges) (fs : List Pred) where

  graphGo    : {E : Pred} (ws : List Node) -> AllSat E ws -> IFin E
            -> FairIn ws G fs ⊎ Cert G fs ws
  graphFind  : {E : Pred} (ws : List Node) -> AllSat E ws -> IFin E
            -> FindResult (hasOut ws G) ws
            -> FairIn ws G fs ⊎ Cert G fs ws
  graphBlock : {E : Pred} (ws : List Node) -> AllSat E ws -> IFin E
            -> Block ws G fs -> FairIn ws G fs ⊎ Cert G fs ws

  graphGo ws sb bar = graphFind ws sb bar (findFalse (hasOut ws G) ws)

  graphFind ws sb bar      (allTrue f)       =
    graphBlock ws sb bar (pickBlock ws G fs f)
  graphFind ws sb (cBar h) (found x mx q) =
    sumElim (λ fi -> inl (fairInMono (ws ∖ᵛ x) ws G fs
                                     (λ z m -> filter-sub (x ≢ᵛ_) ws m) fi))
            (λ c  -> inr (cSink ws x mx (¬ᵇ-false (null (outs ws G x)) q) c))
            (graphGo (ws ∖ᵛ x) (dropAllSat (x ≢ᵛ_) ws sb x (≢ᵛ-self x))
                     (h x (sb x mx)))

  graphBlock ws sb bar      (bEmpty e)                 = inr (cNil ws e)
  graphBlock ws sb bar      (bFair r mr c)             = inl (fairIn r mr c)
  graphBlock ws sb (cBar h) (bUnfair r mr et g mg eg) =
    sumElim (λ fi -> inl (fairInMono (ws ∖ C) ws G fs
                                     (λ z m -> filter-sub notInC ws m) fi))
            (λ c  -> inr (cBlock ws C g mg (sccIn ws G r)
                                 (termClosed ws G r et) miss c))
            (graphGo (ws ∖ C)
                     (dropAllSat notInC ws sb r
                        (cong ¬ᵇ_ (∈ᵛ-complete r C (sccRep ws G r mr))))
                     (h r (sb r mr)))
    where
      C : List Node
      C = sccOf ws G r

      notInC : Pred
      notInC y = ¬ᵇ (y ∈ᵛ C)

      miss : (z : Node) -> z ∈ C -> g z ≡ false
      miss z mz = any-false g C eg mz

------------------------------------------------------------------------
-- The theorem

-- A fair lasso from v: a stem from v to r, then a fair circuit at r.

record FairLoop (vs : List Node) (G : Edges) (fs : List Pred)
                (v : Node) : Set where
  constructor fairLoop
  field
    r           : Node   -- where the cycle starts and ends
    stem        : Reaches vs G v r
    fairCircuit : Circuit vs G fs r

fairGraph : (vs : List Node) (G : Edges) (fs : List Pred)
            (v : Node) -> v ∈ vs
         -> FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v)
fairGraph vs G fs v mv =
  sumElim (λ fi -> inl (toLoop fi)) inr
          (graphGo G fs (reachSet vs G v) (memAllSat (reachSet vs G v))
                   (listBar (reachSet vs G v)))
  where
    into : (z : Node) -> z ∈ reachSet vs G v -> z ∈ vs
    into z m = reachIn vs G v m

    toLoop : FairIn (reachSet vs G v) G fs -> FairLoop vs G fs v
    toLoop (fairIn r mr c) =
      fairLoop r (reachTrail vs G v mr)
                 (circMono (reachSet vs G v) vs G fs r into c)

------------------------------------------------------------------------
-- What a certificate is for: an induction over the removal order.  R is the
-- property to establish of every vertex (for LTL.SCC.SccExtract, refutability
-- of chi), and the hypothesis carried is "R holds outside ws".  The sink and
-- block cases are the two hypotheses of certAll.

module _ (G : Edges) (fs : List Pred) (R : Node -> Set)
         (sinkCase  : (ws : List Node) (x : Node) -> x ∈ ws
                   -> null (outs ws G x) ≡ true
                   -> HoldsOutside R ws -> R x)
         (blockCase : (ws C : List Node) (f : Pred) -> f ∈ fs
                   -> C ⊆ ws -> Closed ws G C -> NoneSat f C
                   -> HoldsOutside R ws -> (z : Node) -> z ∈ C -> R z)
         where

  certAll : {ws : List Node} -> Cert G fs ws -> HoldsOutside R ws
         -> (z : Node) -> R z
  certAll (cNil ws e)          ih z = ih z (null-notMem ws z e)
  certAll (cSink ws x mx e c)  ih z = certAll c ih' z
    where
      ih' : HoldsOutside R (ws ∖ᵛ x)
      ih' y eo with y ∈ᵛ ws in eb
      ... | false = ih y eb
      ... | true with x ≡ᵛ y in ec
      ...   | true  = subst R (≡ᵛ-sound x y ec) (sinkCase ws x mx e ih)
      ...   | false =
        emptyElim (∈ᵛ-false y (ws ∖ᵛ x) eo
                    (filter-true (x ≢ᵛ_) ws (∈ᵛ-sound y ws eb) (cong ¬ᵇ_ ec)))
  certAll (cBlock ws C f mf sb cl mis c) ih z =
    certAll c ih' z
    where
      ih' : HoldsOutside R (ws ∖ C)
      ih' y eo with y ∈ᵛ ws in eb
      ... | false = ih y eb
      ... | true with y ∈ᵛ C in ec
      ...   | true  = blockCase ws C f mf sb cl mis ih y (∈ᵛ-sound y C ec)
      ...   | false =
        emptyElim (∈ᵛ-false y (ws ∖ C) eo
                    (filter-true (λ u -> ¬ᵇ (u ∈ᵛ C)) ws (∈ᵛ-sound y ws eb)
                                 (cong ¬ᵇ_ ec)))

------------------------------------------------------------------------
-- The two outputs are EXCLUSIVE, by two observations about a closed trail:
--
--   a vertex on a cycle has a successor,  so a sink is on no cycle;
--   any vertex of a cycle reaches any other,  so a cycle that enters a
--     successor-closed block never leaves it.

-- The suffix of a trail from any vertex it visits, and the prefix to one: all
-- the "rotation" of a cycle the argument needs.

module _ (ws : List Node) (G : Edges) where

  reachesCons : {v x s : Node}
             -> x ∈ ws -> G v x ≡ true -> Reaches ws G x s -> Reaches ws G v s
  reachesCons m e (reachesBy zs t) = reachesBy (_ ∷ zs) (tCons m e t)

  reachesApp : {u v w : Node}
            -> Reaches ws G u v -> Reaches ws G v w -> Reaches ws G u w
  reachesApp (reachesBy as ta) (reachesBy bs tb) =
    reachesBy (as ++ bs) (trailApp ws G ta tb)

  trailFrom : {v : Node} {zs : List Node} {w : Node}
           -> Trail ws G v zs w -> {s : Node} -> s ∈ v ∷ zs -> Reaches ws G s w
  trailFrom tNil          here      = reachesBy [] tNil
  trailFrom tNil          (there ())
  trailFrom (tCons m e t) here      = reachesBy _ (tCons m e t)
  trailFrom (tCons m e t) (there k) = trailFrom t k

  trailTo : {v : Node} {zs : List Node} {w : Node}
         -> Trail ws G v zs w -> {s : Node} -> s ∈ zs -> Reaches ws G v s
  trailTo tNil          ()
  trailTo (tCons m e t) here      = reachesBy (_ ∷ []) (tCons m e tNil)
  trailTo (tCons m e t) (there k) = reachesCons m e (trailTo t k)

-- Observation one: a vertex on a cycle has a successor inside ws.  Along a
-- trail every vertex visited has one provided the endpoint has, and for a
-- closed trail the endpoint is the start, whose successor is the first step.

data HasSucc (ws : List Node) (G : Edges) (x : Node) : Set where
  hasSucc : (y : Node) -> y ∈ ws -> G x y ≡ true -> HasSucc ws G x

module _ (ws : List Node) (G : Edges) where

  firstStep : {v : Node} {zs : List Node} {w : Node}
           -> Trail ws G v zs w -> null zs ≡ false -> HasSucc ws G v
  firstStep tNil                  ()
  firstStep (tCons {x = y} m e t) nn = hasSucc y m e

  headSucc : {v : Node} {zs : List Node} {w : Node}
          -> Trail ws G v zs w -> HasSucc ws G w -> HasSucc ws G v
  headSucc tNil                  hw = hw
  headSucc (tCons {x = y} m e t) hw = hasSucc y m e

  trailSucc : {v : Node} {zs : List Node} {w : Node}
           -> Trail ws G v zs w -> HasSucc ws G w
           -> {x : Node} -> x ∈ zs -> HasSucc ws G x
  trailSucc tNil          hw ()
  trailSucc (tCons m e t) hw here      = headSucc t hw
  trailSucc (tCons m e t) hw (there k) = trailSucc t hw k

  cycSucc : (r : Node) (cy : List Node)
         -> Trail ws G r cy r -> null cy ≡ false
         -> {x : Node} -> x ∈ cy -> HasSucc ws G x
  cycSucc r cy t nn mx = trailSucc t (firstStep t nn) mx

  -- Observation two: any vertex of a cycle reaches any other (suffix to the
  -- base point, then prefix out), and a successor-closed block that a trail
  -- starts in contains everything the trail reaches.

  cycConn : (r : Node) (cy : List Node)
         -> Trail ws G r cy r -> (u z : Node) -> u ∈ cy -> z ∈ cy
         -> Reaches ws G u z
  cycConn r cy t u z mu mz =
    reachesApp ws G (trailFrom ws G t (there mu)) (trailTo ws G t mz)

blockAlong : (ws C : List Node) (G : Edges) -> Closed ws G C
          -> {u : Node} {zs : List Node} {z : Node}
          -> Trail ws G u zs z -> u ∈ C -> z ∈ C
blockAlong ws C G cl tNil                       mu = mu
blockAlong ws C G cl (tCons {x = y} m e t)      mu =
  blockAlong ws C G cl t (cl _ y mu m e)

trailRestrict : (ws vs : List Node) (G : Edges)
                {v : Node} {zs : List Node} {w : Node}
             -> Trail ws G v zs w -> zs ⊆ vs
             -> Trail vs G v zs w
trailRestrict ws vs G tNil                 h = tNil
trailRestrict ws vs G (tCons {x = y} m e t) h =
  tCons (h y here) e (trailRestrict ws vs G t (λ z mz -> h z (there mz)))

-- A certificate for ws forbids a fair circuit inside ws.  By induction on the
-- certificate: each step leaves the cycle untouched, so it is still there when
-- nothing is left, which cNil forbids.

certNoCirc : (G : Edges) (fs : List Pred) {ws : List Node}
          -> Cert G fs ws -> (r : Node) -> Circuit ws G fs r -> Empty
certNoCirc G fs (cNil ws e)         r (circuit cy t nn wit) =
  null-mem ws e (trailIn ws G t (trailLast ws G t nn))
certNoCirc G fs (cSink ws x mx e c) r (circuit cy t nn wit) =
  certNoCirc G fs c r (circuit cy (trailRestrict ws (ws ∖ᵛ x) G t keep) nn wit)
  where
    offCycle : x ∈ cy -> Empty
    offCycle m = onS (cycSucc ws G r cy t nn m)
      where
        onS : HasSucc ws G x -> Empty
        onS (hasSucc y my gy) =
          null-mem (outs ws G x) e (filter-true (G x) ws my gy)

    keep : (z : Node) -> z ∈ cy -> z ∈ ws ∖ᵛ x
    keep z mz = filter-true (x ≢ᵛ_) ws (trailIn ws G t mz) (cong ¬ᵇ_ out)
      where
        out : x ≡ᵛ z ≡ false
        out = refuteTrue (x ≡ᵛ z) λ eb ->
          offCycle (subst (λ y -> y ∈ cy) (sym (≡ᵛ-sound x z eb)) mz)
certNoCirc G fs (cBlock ws C f mf sb cl mis c) r (circuit cy t nn wit) =
  certNoCirc G fs c r (circuit cy (trailRestrict ws (ws ∖ C) G t keep) nn wit)
  where
    inBlock : (z : Node) -> z ∈ cy -> z ∈ C -> Empty
    inBlock z mz mzc = onW (wit f mf)
      where
        onW : (Σ[ y ∈ Node ] y ∈ cy × f y ≡ true) -> Empty
        onW (y , my , fy) = true≢false (trans (sym fy) (mis y inC))
          where
            inC : y ∈ C
            inC = along (cycConn ws G r cy t z y mz my)
              where
                along : Reaches ws G z y -> y ∈ C
                along (reachesBy as ta) = blockAlong ws C G cl ta mzc

    keep : (z : Node) -> z ∈ cy -> z ∈ ws ∖ C
    keep z mz = filter-true (λ y -> ¬ᵇ (y ∈ᵛ C)) ws (trailIn ws G t mz)
                            (cong ¬ᵇ_ out)
      where
        out : z ∈ᵛ C ≡ false
        out = refuteTrue (z ∈ᵛ C) λ eb -> inBlock z mz (∈ᵛ-sound z C eb)

------------------------------------------------------------------------
-- The dichotomy at the top level: fairGraph's two answers cannot both hold, so
-- if a fair lasso from v exists, fairGraph returns one.  Restricting the
-- lasso's cycle to the reachable set uses reachComplete.

fairNoLoop : (vs : List Node) (G : Edges) (fs : List Pred)
             (v : Node) -> v ∈ vs
          -> Cert G fs (reachSet vs G v) -> FairLoop vs G fs v -> Empty
fairNoLoop vs G fs v mv c (fairLoop r stem (circuit cy t nn wit)) =
  certNoCirc G fs c r
             (circuit cy (trailRestrict vs (reachSet vs G v) G t keep) nn wit)
  where
    keep : (z : Node) -> z ∈ cy -> z ∈ reachSet vs G v
    keep z mz = onR (reachesApp vs G stem (trailTo vs G t mz))
      where
        onR : Reaches vs G v z -> z ∈ reachSet vs G v
        onR (reachesBy zs tz) = reachComplete vs G v mv tz

fairComplete : (vs : List Node) (G : Edges) (fs : List Pred)
               (v : Node) (mv : v ∈ vs)
            -> FairLoop vs G fs v -> isInl (fairGraph vs G fs v mv) ≡ true
fairComplete vs G fs v mv fl = onS (fairGraph vs G fs v mv) refl
  where
    onS : (s : FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v))
       -> fairGraph vs G fs v mv ≡ s
       -> isInl (fairGraph vs G fs v mv) ≡ true
    onS (inl l) es = cong isInl es
    onS (inr c) es = emptyElim (fairNoLoop vs G fs v mv c fl)

------------------------------------------------------------------------
-- The removal order as a list of step kinds, one per constructor of Cert.

data CertStep : Set where
  removedSink removedBlock emptied : CertStep

certShape : {G : Edges} {fs : List Pred} {ws : List Node}
         -> Cert G fs ws -> List CertStep
certShape (cNil ws e)                    = emptied ∷ []
certShape (cSink ws x mx e c)            = removedSink ∷ certShape c
certShape (cBlock ws C f mf sb cl mis c) = removedBlock ∷ certShape c

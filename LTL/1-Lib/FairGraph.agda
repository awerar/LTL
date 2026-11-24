{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.FairGraph -- the finite fair-graph certificate theorem.
--
--   Given a finite graph, finitely many decidable fairness predicates, and a
--   vertex v, compute either
--     (a) a lasso from v whose cycle meets every predicate (FairLoop), or
--     (b) a well-founded certificate that every recurrent component reachable
--         from v misses some predicate (Cert).
--
-- That is fairGraph; certAll is the induction principle a Cert supplies.  The
-- two answers are proved exclusive (certNoCirc, fairNoLoop), so the negative
-- answer is a decision.  The module is parameterised like LTL.1-Lib.Graph, whose
-- trails and reachable set it uses; the fairness sets are fs : List Pred.
--
-- Design choices:
--
-- 1. A component is a representative plus a filter (sccOf); the condensation
--    is never built, and "terminal" is a boolean.
-- 2. graphGo is a REMOVING iteration (refute a sink or a terminal component,
--    delete it), so a Bar covers termination; findTerm finds a terminal
--    component by following condensation edges, again by Bar recursion.  Both
--    take their Bar from listBar, so they need no guard.
--
-- Exclusivity needs no infinite paths: a vertex on a cycle has a successor,
-- so a sink lies on no cycle; and any vertex of a cycle reaches any other, so
-- a cycle that enters a successor-closed block never leaves it.  Both are
-- inductions on a finite trail.

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.DecEq using (DecEq)

module LTL.1-Lib.FairGraph {Node : Set} (eq : DecEq Node)
                           (G : Node -> Node -> Bool) where

-- Not re-exported: an importer gets this module's own names only, and opens
-- LTL.1-Lib.Graph and the set layer itself.

open import LTL.1-Lib.Sets
open import LTL.1-Lib.Bar
open import LTL.1-Lib.Nodes eq
open import LTL.1-Lib.Graph eq G
open import LTL.1-Lib.CertStep

-- The implicit arguments the signatures below leave out: the endpoints and
-- visited list of a trail, and the predicate of the Bar a search recurses on.

private variable
  u v w x s z : Node
  zs          : List Node
  E           : Pred

------------------------------------------------------------------------
-- Components, without component objects: sccOf ws r is the vertices r
-- reaches that reach r back.  A filter of a list, nothing more.

sccOf : List Node -> Node -> List Node
sccOf ws r = filter (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r)

sccReach : (ws : List Node) (r : Node) (w : Node)
        -> w ∈ sccOf ws r -> w ∈ reachSet ws r
sccReach ws r w m =
  ∈-filter⁻ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) m

sccTo : (ws : List Node) (r : Node) (w : Node)
     -> w ∈ sccOf ws r -> Reaches ws r w
sccTo ws r w m = reachTrail ws r (sccReach ws r w m)

sccFrom : (ws : List Node) (r : Node) (w : Node)
       -> w ∈ sccOf ws r -> Reaches ws w r
sccFrom ws r w m =
  reachTrail ws w
    (∈ᵛ-sound r (reachSet ws w)
      (filter-prop (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) m))

sccRep : (ws : List Node) (r : Node)
      -> r ∈ ws -> r ∈ sccOf ws r
sccRep ws r mr =
  ∈-filter⁺ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r)
            (reachSeed ws r mr)
            (∈ᵛ-complete r (reachSet ws r) (reachSeed ws r mr))

------------------------------------------------------------------------
-- r's component is terminal when everything r reaches reaches r back, i.e.
-- the reachable set of r IS its component.

isTerminal : List Node -> Node -> Bool
isTerminal ws r = all (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r)

termScc : (ws : List Node) (r : Node)
       -> isTerminal ws r ≡ true
       -> ∀ⁱ[ w ∈ reachSet ws r ] w ∈ sccOf ws r
termScc ws r et {w} m =
  ∈-filter⁺ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) m
            (all-true (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) et w m)

-- A terminal component is closed under successors inside ws: the refutation
-- needs exactly this of it.

termClosed : (ws : List Node) (r : Node)
          -> isTerminal ws r ≡ true -> sccOf ws r closed-under G within ws
termClosed ws r et {z} mz my e =
  termScc ws r et (reachClosed ws r (sccReach ws r z mz) my e)

------------------------------------------------------------------------
-- A non-empty graph has a terminal component.  While r's component is not
-- terminal, there is a w that r reaches and that does not reach r; move the
-- representative to w.  This is a Bar search whose invariant is that every
-- vertex of the current reachable set still satisfies the Bar predicate;
-- giving up r is the sub-Bar cBar hands over, and the new reachable set
-- avoids r because w does not reach r.

-- A vertex whose component is terminal, found by the search above.

record Terminal (ws : List Node) : Set where
  constructor terminalAt
  field
    r        : Node
    rIn      : r ∈ ws
    terminal : isTerminal ws r ≡ true

module _ (ws : List Node) where

  termGo   : (r : Node) -> r ∈ ws
          -> AllSat E (reachSet ws r) -> IFin E -> Terminal ws
  termFind : (r : Node) -> r ∈ ws
          -> AllSat E (reachSet ws r) -> IFin E
          -> AllDecision (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r)
          -> Terminal ws

  termGo r mr av bar =
    termFind r mr av bar
             (decideAll (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r))

  termFind r mr av bar          (allTrue f)             =
    terminalAt r mr
               (all-intro (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r)
                          (λ w m -> f m))
  termFind {E} r mr av (cBar h) (counterexample w mw q) =
    termGo w (reachIn ws r mw) av' (h r (av r (reachSeed ws r mr)))
    where
      av' : ∀[ z ∈ reachSet ws w ] E z ∧ᵇ (r ≢ᵛ z) ≡ true
      av' z mz =
        ∧ᵇ-intro (E z) (r ≢ᵛ z)
                 (av z (reachTrans ws r w z mw mz))
                 (cong ¬ᵇ_ notR)
        where
          notR : r ≡ᵛ z ≡ false
          notR = refuteTrue (r ≡ᵛ z) λ eb ->
            true≢false (trans (sym (rIn eb)) q)
            where
              rIn : r ≡ᵛ z ≡ true -> r ∈ᵛ reachSet ws w ≡ true
              rIn eb = ∈ᵛ-complete r (reachSet ws w)
                         (subst (λ y -> y ∈ reachSet ws w)
                                (sym (≡ᵛ-sound r z eb)) mz)

  findTerm : ∀[ r ∈ ws ] Terminal ws
  findTerm r mr =
    termGo r mr (λ z mz -> ∈ᵛ-complete z ws (reachIn ws r mz)) (listBar ws)

------------------------------------------------------------------------
-- The positive certificate: a fair circuit at r, a loop through r (a
-- non-empty closed trail) with a witness on it for every fairness predicate.
-- It is built by picking a witness for each predicate and joining them by
-- trails inside the component.

record Loop (ws : List Node) (r : Node) : Set where
  constructor loopBy
  field
    cycle    : List Node
    trail    : Trail ws r cycle r
    nonEmpty : null cycle ≡ false

record Circuit (ws : List Node) (fs : List Pred)
               (r : Node) : Set where
  constructor circuit
  field
    loop  : Loop ws r
    meets : ∀[ f ∈ fs ] ∃[ z ∈ Loop.cycle loop ] f z ≡ true

loopRestrict : (ws vs : List Node) {r : Node}
            -> (l : Loop ws r) -> Loop.cycle l ⊆ vs -> Loop vs r
loopRestrict ws vs (loopBy cy t nn) h = loopBy cy (trailRestrict ws vs t h) nn

circMono : (ws vs : List Node) (fs : List Pred)
           (r : Node) -> ws ⊆ vs
        -> Circuit ws fs r -> Circuit vs fs r
circMono ws vs fs r sb (circuit (loopBy cy t nn) wit) =
  circuit (loopBy cy (trailMono ws vs sb t) nn) wit

-- C meets every fairness predicate: each f in fs holds somewhere in C.

meetsAll : List Pred -> List Node -> Bool
meetsAll fs C = all (λ g -> any g C) fs

-- A terminal component of a vertex that has a successor is non-trivial: the
-- successor is reached, so terminality sends a trail back.  No separate cycle
-- detection is needed.

module _ (ws : List Node) (r : Node) where

  loopAt : r ∈ ws
        -> isTerminal ws r ≡ true -> hasOut ws r ≡ true -> Loop ws r
  loopAt mr et ho =
    pick (null-false (outs ws r) (¬ᵇ-true (null (outs ws r)) ho))
    where
      pick : (Σ[ x ∈ Node ] x ∈ outs ws r) -> Loop ws r
      pick (x , mx) = loopBy (x ∷ via) (tCons mxw grx trail) refl
        where
          mxw : x ∈ ws
          mxw = ∈-filter⁻ (G r) ws mx

          grx : G r x ≡ true
          grx = filter-prop (G r) ws mx

          inR : x ∈ reachSet ws r
          inR = reachClosed ws r (reachSeed ws r mr) mxw grx

          open Reaches (sccFrom ws r x (termScc ws r et inR))

  -- One fairness predicate added to a circuit.  The leg is  loop ++ (r to w)
  -- ++ (w to r) , with the loop in front so that the r-to-w half is non-empty
  -- and w is a vertex the leg VISITS.  trailApp is left-nested so that
  -- associativity never appears.

  consCirc : Loop ws r
          -> (f : Pred) (w : Node) -> f w ≡ true
          -> Reaches ws r w -> Reaches ws w r
          -> (fs : List Pred) -> Circuit ws fs r
          -> Circuit ws (f ∷ fs) r
  consCirc (loopBy cy0 t0 nn) f w fw (reachesBy as ta) (reachesBy bs tb) fs
           (circuit (loopBy cy t nnc) wit) =
    circuit (loopBy (leg ++ cy) (trailApp ws legT t) (null-++-false-introˡ leg cy legNN))
            each
    where
      front : List Node
      front = cy0 ++ as

      frontT : Trail ws r front w
      frontT = trailApp ws t0 ta

      frontNN : null front ≡ false
      frontNN = null-++-false-introˡ cy0 as nn

      leg : List Node
      leg = front ++ bs

      legT : Trail ws r leg r
      legT = trailApp ws frontT tb

      legNN : null leg ≡ false
      legNN = null-++-false-introˡ front bs frontNN

      mw : w ∈ leg
      mw = ∈-++⁺ˡ front bs (trailLast ws frontT frontNN)

      each : ∀[ g ∈ f ∷ fs ] ∃[ z ∈ leg ++ cy ] g z ≡ true
      each g here      = w , ∈-++⁺ˡ leg cy mw , fw
      each g (there m) = shift (wit g m)
        where
          shift : (∃[ z ∈ cy ] g z ≡ true)
               -> ∃[ z ∈ leg ++ cy ] g z ≡ true
          shift (z , mz , gz) = z , ∈-++⁺ʳ leg cy mz , gz

  mkCirc : Loop ws r
        -> (C : List Node)
        -> (∀[ u ∈ C ] Reaches ws r u)
        -> (∀[ u ∈ C ] Reaches ws u r)
        -> (fs : List Pred) -> meetsAll fs C ≡ true
        -> Circuit ws fs r
  mkCirc l0 C to from []        e = circuit l0 noF
    where
      noF : ∀[ f ∈ [] ] ∃[ z ∈ Loop.cycle l0 ] f z ≡ true
      noF f ()
  mkCirc l0 C to from (f ∷ fs) e =
    pick (any-true f C (∧ᵇ-trueˡ (any f C) (meetsAll fs C) e))
    where
      rest : Circuit ws fs r
      rest = mkCirc l0 C to from fs
                    (∧ᵇ-trueʳ (any f C) (meetsAll fs C) e)

      pick : (∃[ w ∈ C ] f w ≡ true)
          -> Circuit ws (f ∷ fs) r
      pick (w , mw , fw) =
        consCirc l0 f w fw (to w mw) (from w mw) fs rest

------------------------------------------------------------------------
-- One step of the outer iteration, decided: given that every vertex of ws has
-- an out-edge, ws is empty, or its terminal component is fair and a circuit is
-- built, or it misses some f and is a block to be refuted.  Nothing here
-- recurses.

data Block (ws : List Node) (fs : List Pred) : Set where
  bEmpty  : null ws ≡ true -> Block ws fs
  bFair   : (r : Node) -> r ∈ ws -> Circuit ws fs r -> Block ws fs
  bUnfair : (r : Node) -> r ∈ ws -> isTerminal ws r ≡ true
         -> (f : Pred) -> f ∈ fs -> any f (sccOf ws r) ≡ false
         -> Block ws fs

blockOf : (ws : List Node) (fs : List Pred)
       -> (∀ⁱ[ x ∈ ws ] hasOut ws x ≡ true)
       -> Terminal ws -> Block ws fs
blockOf ws fs h (terminalAt r mr et) with meetsAll fs (sccOf ws r) in eb
... | true  = bFair r mr (mkCirc ws r (loopAt ws r mr et (h mr)) (sccOf ws r)
                                 (sccTo ws r) (sccFrom ws r) fs eb)
... | false = unf (all-false (λ g -> any g (sccOf ws r)) fs eb)
  where
    unf : (∃[ g ∈ fs ] any g (sccOf ws r) ≡ false)
       -> Block ws fs
    unf (g , mg , eg) = bUnfair r mr et g mg eg

pickBlock : (ws : List Node) (fs : List Pred)
         -> (∀ⁱ[ x ∈ ws ] hasOut ws x ≡ true) -> Block ws fs
pickBlock []       fs h = bEmpty refl
pickBlock (u ∷ ws) fs h =
  blockOf (u ∷ ws) fs h (findTerm (u ∷ ws) u here)

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

data Cert (fs : List Pred) : List Node -> Set where
  cNil   : (ws : List Node) -> null ws ≡ true -> Cert fs ws
  cSink  : (ws : List Node) (x : Node) -> x ∈ ws
        -> null (outs ws x) ≡ true
        -> Cert fs (ws ∖ᵛ x) -> Cert fs ws
  cBlock : (ws C : List Node) (f : Pred) -> f ∈ fs
        -> C closed-under G within ws -> NoneSat f C
        -> Cert fs (ws ∖ C) -> Cert fs ws

------------------------------------------------------------------------
-- The theorem, on a sub-list

-- A fair circuit somewhere in ws, at the representative r.

record FairIn (ws : List Node) (fs : List Pred) : Set where
  constructor fairIn
  field
    r           : Node
    rIn         : r ∈ ws
    fairCircuit : Circuit ws fs r

fairInMono : (ws vs : List Node) (fs : List Pred)
          -> ws ⊆ vs
          -> FairIn ws fs -> FairIn vs fs
fairInMono ws vs fs sb (fairIn r mr c) =
  fairIn r (sb r mr) (circMono ws vs fs r sb c)

-- Terminal-component removal, a REMOVING iteration: whichever step applies,
-- the vertex it names (the sink x, or the block's representative r) leaves ws
-- and the Bar's predicate with it (dropAllSat).

module _ (fs : List Pred) where

  graphGo    : (ws : List Node) -> AllSat E ws -> IFin E
            -> FairIn ws fs ⊎ Cert fs ws
  graphFind  : (ws : List Node) -> AllSat E ws -> IFin E
            -> AllDecision (hasOut ws) ws
            -> FairIn ws fs ⊎ Cert fs ws
  graphBlock : (ws : List Node) -> AllSat E ws -> IFin E
            -> Block ws fs -> FairIn ws fs ⊎ Cert fs ws

  graphGo ws sb bar = graphFind ws sb bar (decideAll (hasOut ws) ws)

  graphFind ws sb bar      (allTrue f)              =
    graphBlock ws sb bar (pickBlock ws fs f)
  graphFind ws sb (cBar h) (counterexample x mx q) =
    [ (λ fi -> inl (fairInMono (ws ∖ᵛ x) ws fs
                               (λ z m -> ∈-filter⁻ (x ≢ᵛ_) ws m) fi))
    , (λ c  -> inr (cSink ws x mx (¬ᵇ-false (null (outs ws x)) q) c))
    ] (graphGo (ws ∖ᵛ x) (dropAllSat (x ≢ᵛ_) ws sb x (≢ᵛ-self x))
               (h x (sb x mx)))

  graphBlock ws sb bar      (bEmpty e)                 = inr (cNil ws e)
  graphBlock ws sb bar      (bFair r mr c)             = inl (fairIn r mr c)
  graphBlock ws sb (cBar h) (bUnfair r mr et g mg eg) =
    [ (λ fi -> inl (fairInMono (ws ∖ C) ws fs
                               (λ z m -> ∈-filter⁻ notInC ws m) fi))
    , (λ c  -> inr (cBlock ws C g mg (termClosed ws r et) miss c))
    ] (graphGo (ws ∖ C)
               (dropAllSat notInC ws sb r
                  (cong ¬ᵇ_ (∈ᵛ-complete r C (sccRep ws r mr))))
               (h r (sb r mr)))
    where
      C : List Node
      C = sccOf ws r

      notInC : Pred
      notInC y = ¬ᵇ (y ∈ᵛ C)

      miss : ∀[ z ∈ C ] g z ≡ false
      miss z mz = any-false g C eg mz

------------------------------------------------------------------------
-- The theorem

-- A fair lasso from v: a stem from v to r, then a fair circuit at r.

record FairLoop (vs : List Node) (fs : List Pred)
                (v : Node) : Set where
  constructor fairLoop
  field
    r           : Node   -- where the cycle starts and ends
    stem        : Reaches vs v r
    fairCircuit : Circuit vs fs r

fairGraph : (vs : List Node) (fs : List Pred)
            (v : Node) -> v ∈ vs
         -> FairLoop vs fs v ⊎ Cert fs (reachSet vs v)
fairGraph vs fs v mv =
  [ (λ fi -> inl (toLoop fi)) , inr ]
    (graphGo fs (reachSet vs v) (AllSat-∈ᵛ (reachSet vs v))
             (listBar (reachSet vs v)))
  where
    into : ∀[ z ∈ reachSet vs v ] z ∈ vs
    into z m = reachIn vs v m

    toLoop : FairIn (reachSet vs v) fs -> FairLoop vs fs v
    toLoop (fairIn r mr c) =
      fairLoop r (reachTrail vs v mr)
                 (circMono (reachSet vs v) vs fs r into c)

------------------------------------------------------------------------
-- What a certificate is for: an induction over the removal order.  R is the
-- property to establish of every vertex (for LTL.7-SCC.SccExtract, refutability
-- of chi), and the hypothesis carried is "R holds outside ws".  The sink and
-- block cases are the two hypotheses of certAll.

module _ (fs : List Pred) (R : Node -> Set)
         (sinkCase  : (ws : List Node) (x : Node) -> x ∈ ws
                   -> null (outs ws x) ≡ true
                   -> HoldsOutside R ws -> R x)
         (blockCase : (ws C : List Node) (f : Pred) -> f ∈ fs
                   -> C closed-under G within ws -> NoneSat f C
                   -> HoldsOutside R ws -> ∀[ z ∈ C ] R z)
         where

  -- One removal step: R holds outside what is left once it holds outside ws
  -- and at every removed vertex, the members of ws that fail p.

  dropOutside : (p : Pred) (ws : List Node) -> HoldsOutside R ws
             -> ((y : Node) -> y ∈ ws -> p y ≡ false -> R y)
             -> HoldsOutside R (filter p ws)
  dropOutside p ws ih removed y eo with y ∈ᵛ ws in eb
  ... | false = ih y eb
  ... | true with p y in ep
  ...   | false = removed y (∈ᵛ-sound y ws eb) ep
  ...   | true  =
    emptyElim (∈ᵛ-false y (filter p ws) eo
                (∈-filter⁺ p ws (∈ᵛ-sound y ws eb) ep))

  certAll : {ws : List Node} -> Cert fs ws -> HoldsOutside R ws
         -> (z : Node) -> R z
  certAll (cNil ws e)          ih z = ih z (null-∈ᵛ ws z e)
  certAll (cSink ws x mx e c)  ih z =
    certAll c (dropOutside (x ≢ᵛ_) ws ih isX) z
    where
      isX : (y : Node) -> y ∈ ws -> x ≢ᵛ y ≡ false -> R y
      isX y my ey = subst R (≡ᵛ-sound x y (¬ᵇ-false (x ≡ᵛ y) ey))
                          (sinkCase ws x mx e ih)
  certAll (cBlock ws C f mf cl mis c) ih z =
    certAll c (dropOutside (λ u -> ¬ᵇ (u ∈ᵛ C)) ws ih inC) z
    where
      inC : (y : Node) -> y ∈ ws -> ¬ᵇ (y ∈ᵛ C) ≡ false -> R y
      inC y my ey = blockCase ws C f mf cl mis ih y
                              (∈ᵛ-sound y C (¬ᵇ-false (y ∈ᵛ C) ey))

------------------------------------------------------------------------
-- The two outputs are EXCLUSIVE, by two observations about a closed trail:
--
--   a vertex on a cycle has a successor,  so a sink is on no cycle;
--   any vertex of a cycle reaches any other,  so a cycle that enters a
--     successor-closed block never leaves it.

-- The suffix of a trail from any vertex it visits, and the prefix to one: all
-- the "rotation" of a cycle the argument needs.

module _ (ws : List Node) where

  reachesCons : x ∈ ws -> G v x ≡ true -> Reaches ws x s -> Reaches ws v s
  reachesCons m e (reachesBy zs t) = reachesBy (_ ∷ zs) (tCons m e t)

  reachesApp : Reaches ws u v -> Reaches ws v w -> Reaches ws u w
  reachesApp (reachesBy as ta) (reachesBy bs tb) =
    reachesBy (as ++ bs) (trailApp ws ta tb)

  trailFrom : Trail ws v zs w -> ∀ⁱ[ s ∈ v ∷ zs ] Reaches ws s w
  trailFrom tNil          here      = reachesBy [] tNil
  trailFrom tNil          (there ())
  trailFrom (tCons m e t) here      = reachesBy _ (tCons m e t)
  trailFrom (tCons m e t) (there k) = trailFrom t k

  trailTo : Trail ws v zs w -> ∀ⁱ[ s ∈ zs ] Reaches ws v s
  trailTo tNil          ()
  trailTo (tCons m e t) here      = reachesBy (_ ∷ []) (tCons m e tNil)
  trailTo (tCons m e t) (there k) = reachesCons m e (trailTo t k)

-- Observation one: a vertex on a cycle has a successor inside ws.  Along a
-- trail every vertex visited has one provided the endpoint has, and for a
-- closed trail the endpoint is the start, whose successor is the first step.

record HasSucc (ws : List Node) (x : Node) : Set where
  constructor hasSucc
  field
    next   : Node
    nextIn : next ∈ ws
    edge   : G x next ≡ true

module _ (ws : List Node) where

  firstStep : Trail ws v zs w -> null zs ≡ false -> HasSucc ws v
  firstStep tNil                  ()
  firstStep (tCons {x = y} m e t) nn = hasSucc y m e

  headSucc : Trail ws v zs w -> HasSucc ws w -> HasSucc ws v
  headSucc tNil                  hw = hw
  headSucc (tCons {x = y} m e t) hw = hasSucc y m e

  trailSucc : Trail ws v zs w -> HasSucc ws w
           -> ∀ⁱ[ x ∈ zs ] HasSucc ws x
  trailSucc tNil          hw ()
  trailSucc (tCons m e t) hw here      = headSucc t hw
  trailSucc (tCons m e t) hw (there k) = trailSucc t hw k

  cycSucc : (r : Node) (cy : List Node)
         -> Trail ws r cy r -> null cy ≡ false
         -> ∀ⁱ[ x ∈ cy ] HasSucc ws x
  cycSucc r cy t nn mx = trailSucc t (firstStep t nn) mx

  -- Observation two: any vertex of a cycle reaches any other (suffix to the
  -- base point, then prefix out), and a successor-closed block that a trail
  -- starts in contains everything the trail reaches.

  cycConn : (r : Node) (cy : List Node)
         -> Trail ws r cy r -> (u z : Node) -> u ∈ cy -> z ∈ cy
         -> Reaches ws u z
  cycConn r cy t u z mu mz =
    reachesApp ws (trailFrom ws t (there mu)) (trailTo ws t mz)

blockAlong : (ws C : List Node) -> C closed-under G within ws
          -> Trail ws u zs z -> u ∈ C -> z ∈ C
blockAlong ws C cl tNil                       mu = mu
blockAlong ws C cl (tCons m e t)              mu =
  blockAlong ws C cl t (cl mu m e)

-- A trail whose visited vertices all pass p stays inside filter p ws: this is
-- how a cycle survives a removal step.

keepIn : (ws : List Node) (p : Pred)
      -> Trail ws v zs w -> (∀[ z ∈ zs ] p z ≡ true) -> zs ⊆ filter p ws
keepIn ws p t h z mz = ∈-filter⁺ p ws (trailIn ws t mz) (h z mz)

-- A certificate for ws forbids a fair circuit inside ws.  By induction on the
-- certificate: each step leaves the cycle untouched, so it is still there when
-- nothing is left, which cNil forbids.

certNoCirc : (fs : List Pred) {ws : List Node}
          -> Cert fs ws -> (r : Node) -> Circuit ws fs r -> Empty
certNoCirc fs (cNil ws e)         r (circuit (loopBy cy t nn) wit) =
  null-∈ ws e (trailIn ws t (trailLast ws t nn))
certNoCirc fs (cSink ws x mx e c) r (circuit l@(loopBy cy t nn) wit) =
  certNoCirc fs c r
    (circuit (loopRestrict ws (ws ∖ᵛ x) l (keepIn ws (x ≢ᵛ_) t keep)) wit)
  where
    offCycle : x ∈ cy -> Empty
    offCycle m = onS (cycSucc ws r cy t nn m)
      where
        onS : HasSucc ws x -> Empty
        onS (hasSucc y my gy) =
          null-∈ (outs ws x) e (∈-filter⁺ (G x) ws my gy)

    keep : ∀[ z ∈ cy ] x ≢ᵛ z ≡ true
    keep z mz = cong ¬ᵇ_ out
      where
        out : x ≡ᵛ z ≡ false
        out = refuteTrue (x ≡ᵛ z) λ eb ->
          offCycle (subst (λ y -> y ∈ cy) (sym (≡ᵛ-sound x z eb)) mz)
certNoCirc fs (cBlock ws C f mf cl mis c) r
           (circuit l@(loopBy cy t nn) wit) =
  certNoCirc fs c r
    (circuit (loopRestrict ws (ws ∖ C) l
                           (keepIn ws (λ y -> ¬ᵇ (y ∈ᵛ C)) t keep)) wit)
  where
    inBlock : (z : Node) -> z ∈ cy -> z ∈ C -> Empty
    inBlock z mz mzc = onW (wit f mf)
      where
        onW : (∃[ y ∈ cy ] f y ≡ true) -> Empty
        onW (y , my , fy) = true≢false (trans (sym fy) (mis y inC))
          where
            inC : y ∈ C
            inC = blockAlong ws C cl
                             (Reaches.trail (cycConn ws r cy t z y mz my)) mzc

    keep : ∀[ z ∈ cy ] ¬ᵇ (z ∈ᵛ C) ≡ true
    keep z mz = cong ¬ᵇ_ out
      where
        out : z ∈ᵛ C ≡ false
        out = refuteTrue (z ∈ᵛ C) λ eb -> inBlock z mz (∈ᵛ-sound z C eb)

------------------------------------------------------------------------
-- The dichotomy at the top level: fairGraph's two answers cannot both hold, so
-- if a fair lasso from v exists, fairGraph returns one.  Restricting the
-- lasso's cycle to the reachable set uses reachComplete.

fairNoLoop : (vs : List Node) (fs : List Pred)
             (v : Node) -> v ∈ vs
          -> Cert fs (reachSet vs v) -> FairLoop vs fs v -> Empty
fairNoLoop vs fs v mv c (fairLoop r stem (circuit l@(loopBy cy t nn) wit)) =
  certNoCirc fs c r (circuit (loopRestrict vs (reachSet vs v) l keep) wit)
  where
    keep : ∀[ z ∈ cy ] z ∈ reachSet vs v
    keep z mz = reachComplete vs v mv
                  (Reaches.trail (reachesApp vs stem (trailTo vs t mz)))

fairComplete : (vs : List Node) (fs : List Pred)
               (v : Node) (mv : v ∈ vs)
            -> FairLoop vs fs v -> isInl (fairGraph vs fs v mv) ≡ true
fairComplete vs fs v mv fl = onS (fairGraph vs fs v mv) refl
  where
    onS : (s : FairLoop vs fs v ⊎ Cert fs (reachSet vs v))
       -> fairGraph vs fs v mv ≡ s
       -> isInl (fairGraph vs fs v mv) ≡ true
    onS (inl l) es = cong isInl es
    onS (inr c) es = emptyElim (fairNoLoop vs fs v mv c fl)

------------------------------------------------------------------------
-- The removal order as a list of step kinds (LTL.1-Lib.CertStep), one per
-- constructor of Cert.

certShape : {fs : List Pred} {ws : List Node}
         -> Cert fs ws -> List CertStep
certShape (cNil ws e)                    = emptied ∷ []
certShape (cSink ws x mx e c)            = removedSink ∷ certShape c
certShape (cBlock ws C f mf cl mis c) = removedBlock ∷ certShape c

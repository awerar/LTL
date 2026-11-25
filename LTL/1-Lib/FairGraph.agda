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
--    delete it), so a finite pool covers termination; findTerminal finds a
--    terminal component by following condensation edges, again by recursion
--    on a Finiteᵛ proof.  Both take theirs from listFinite, so they need no
--    guard.
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
open import LTL.1-Lib.Exhaustible
open import LTL.1-Lib.Nodes eq
open import LTL.1-Lib.Graph eq G
open import LTL.1-Lib.CertStep

-- The implicit arguments the signatures below leave out: the endpoints and
-- visited list of a trail, and the pool a search recurses on.
-- As in LTL.1-Lib.Graph, so is ws wherever a trail, loop or circuit fixes
-- it; it stays explicit where it only occurs under a function (sccOf ws r).

private variable
  u v w x s z : Node
  ws vs zs    : List Node
  Pool        : Pred

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

terminalScc : (ws : List Node) (r : Node)
       -> isTerminal ws r ≡ true
       -> ∀ⁱ[ w ∈ reachSet ws r ] w ∈ sccOf ws r
terminalScc ws r et {w} m =
  ∈-filter⁺ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) m
            (all-true (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) et w m)

-- A terminal component is closed under successors inside ws: the refutation
-- needs exactly this of it.

terminalClosed : (ws : List Node) (r : Node)
          -> isTerminal ws r ≡ true -> sccOf ws r closed-under G within ws
terminalClosed ws r et {z} mz my e =
  terminalScc ws r et (reachClosed ws r (sccReach ws r z mz) my e)

------------------------------------------------------------------------
-- A non-empty graph has a terminal component.  While r's component is not
-- terminal, there is a w that r reaches and that does not reach r; move the
-- representative to w.  The search recurses on a Finiteᵛ proof, and its
-- invariant is that every vertex of the current reachable set is still in the
-- pool; giving up r is the smaller pool next hands over, and the new
-- reachable set avoids r because w does not reach r.

-- A vertex whose component is terminal, found by the search above.

record Terminal (ws : List Node) : Set where
  constructor terminalAt
  field
    r        : Node
    rIn      : r ∈ ws
    terminal : isTerminal ws r ≡ true

module _ (ws : List Node) where

  terminalGo   : (r : Node) -> r ∈ ws
              -> reachSet ws r inside Pool -> Finiteᵛ Pool -> Terminal ws
  terminalFind : (r : Node) -> r ∈ ws
              -> reachSet ws r inside Pool -> Finiteᵛ Pool
              -> AllDecision (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r)
              -> Terminal ws

  terminalGo r r∈ws avail fin =
    terminalFind r r∈ws avail fin
                 (decideAll (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r))

  terminalFind r r∈ws avail fin (allTrue f) =
    terminalAt r r∈ws
               (all-intro (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r)
                          (λ w m -> f m))
  terminalFind {Pool} r r∈ws avail (everyPick next)
               (counterexample w w∈reach noReturn) =
    terminalGo w (reachIn ws r w∈reach) avail'
               (next r (avail r (reachSeed ws r r∈ws)))
    where
      avail' : reachSet ws w inside Pool ∩ (r ≢ᵛ_)
      avail' = inside-∩ (inside-⊆ (λ z -> reachTrans ws r w z w∈reach) avail)
                        (inside-apart (_∈ᵛ reachSet ws w) noReturn
                                      (inside-∈ᵛ (reachSet ws w)))

  findTerminal : ∀[ r ∈ ws ] Terminal ws
  findTerminal r r∈ws =
    terminalGo r r∈ws (λ z mz -> ∈ᵛ-complete z ws (reachIn ws r mz))
               (listFinite ws)

------------------------------------------------------------------------
-- The positive certificate: a fair circuit at r, a loop through r (a
-- non-empty closed trail) with a witness on it for every fairness predicate.
-- It is built by picking a witness for each predicate and joining them by
-- trails inside the component.
--
-- A loop is non-empty by its index: it visits next first, then back on the
-- way round to r.  So every fact that rests on the first step holds by
-- computation.  The vertices it visits lie in ws; r among them, as the end.

record Loop (ws : List Node) (r : Node) : Set where
  constructor loopBy
  field
    next    : Node
    back    : List Node
    trail   : Trail r (next ∷ back) r
    staysIn : next ∷ back ⊆ ws

  cycle : List Node
  cycle = next ∷ back

record Circuit (ws : List Node) (fs : List Pred)
               (r : Node) : Set where
  constructor circuit
  field
    loop  : Loop ws r
    meets : ∀[ f ∈ fs ] ∃[ z ∈ Loop.cycle loop ] z ∈ᵖ f

module _ {ws vs : List Node} {r : Node} where

  loopRestrict : (l : Loop ws r) -> Loop.cycle l ⊆ vs -> Loop vs r
  loopRestrict (loopBy q qs t _) h = loopBy q qs t h

  circMono : {fs : List Pred} -> ws ⊆ vs -> Circuit ws fs r -> Circuit vs fs r
  circMono subset (circuit (loopBy q qs t h) wit) =
    circuit (loopBy q qs t (λ z mz -> subset z (h z mz))) wit

-- C meets every fairness predicate: each f in fs holds somewhere in C.

meetsAll : List Pred -> List Node -> Bool
meetsAll fs C = all (λ g -> any g C) fs

-- A terminal component of a vertex that has a successor is non-trivial: the
-- successor is reached, so terminality sends a trail back.  No separate cycle
-- detection is needed.

module _ {ws : List Node} {r : Node} where

  loopAt : r ∈ ws
        -> isTerminal ws r ≡ true -> hasOut ws r ≡ true -> Loop ws r
  loopAt mr et ho =
    pick (null-false (outs ws r) (¬ᵇ-true (null (outs ws r)) ho))
    where
      pick : (Σ[ x ∈ Node ] x ∈ outs ws r) -> Loop ws r
      pick (x , mx) = loopBy x via (tCons grx trail) (∷-⊆ mxw staysIn)
        where
          mxw : x ∈ ws
          mxw = ∈-filter⁻ (G r) ws mx

          grx : G r x ≡ true
          grx = filter-prop (G r) ws mx

          inR : x ∈ reachSet ws r
          inR = reachClosed ws r (reachSeed ws r mr) mxw grx

          open Reaches (sccFrom ws r x (terminalScc ws r et inR))

  -- One fairness predicate added to a circuit.  The leg is  loop ++ (r to w)
  -- ++ (w to r) , with the loop in front so that the r-to-w half is non-empty
  -- and w is a vertex the leg VISITS.  trailApp is left-nested so that
  -- associativity never appears.

  consCirc : Loop ws r
          -> (f : Pred) (w : Node) -> f w ≡ true
          -> Reaches ws r w -> Reaches ws w r
          -> (fs : List Pred) -> Circuit ws fs r
          -> Circuit ws (f ∷ fs) r
  consCirc (loopBy q0 qs0 (tCons g0 t0) s0) f w fw (reachesBy as ta sa)
           (reachesBy bs tb sbs) fs (circuit (loopBy q qs t scy) wit) =
    circuit (loopBy q0 (leg ++ cy) (trailApp legT t)
                    (++-⊆ (q0 ∷ leg) legIn scy))
            each
    where
      cy : List Node
      cy = q ∷ qs

      -- front and leg are the visited lists after q0, the loop's first vertex
      front : List Node
      front = qs0 ++ as

      frontT : Trail r (q0 ∷ front) w
      frontT = tCons g0 (trailApp t0 ta)

      leg : List Node
      leg = front ++ bs

      legT : Trail r (q0 ∷ leg) r
      legT = trailApp frontT tb

      legIn : q0 ∷ leg ⊆ ws
      legIn = ++-⊆ (q0 ∷ front) (++-⊆ (q0 ∷ qs0) s0 sa) sbs

      mw : w ∈ q0 ∷ leg
      mw = ∈-++⁺ˡ (q0 ∷ front) bs (trailEnd (trailApp t0 ta))

      each : ∀[ g ∈ f ∷ fs ] ∃[ z ∈ (q0 ∷ leg) ++ cy ] z ∈ᵖ g
      each g here      = w , ∈-++⁺ˡ (q0 ∷ leg) cy mw , fw
      each g (there m) = shift (wit g m)
        where
          shift : (∃[ z ∈ cy ] z ∈ᵖ g)
               -> ∃[ z ∈ (q0 ∷ leg) ++ cy ] z ∈ᵖ g
          shift (z , mz , gz) = z , ∈-++⁺ʳ (q0 ∷ leg) cy mz , gz

  mkCirc : Loop ws r
        -> (C : List Node)
        -> (∀[ u ∈ C ] Reaches ws r u)
        -> (∀[ u ∈ C ] Reaches ws u r)
        -> (fs : List Pred) -> meetsAll fs C ≡ true
        -> Circuit ws fs r
  mkCirc l0 C to from []        e = circuit l0 noF
    where
      noF : ∀[ f ∈ [] ] ∃[ z ∈ Loop.cycle l0 ] z ∈ᵖ f
      noF f ()
  mkCirc l0 C to from (f ∷ fs) e =
    pick (any-true f C (∧ᵇ-trueˡ (any f C) (meetsAll fs C) e))
    where
      rest : Circuit ws fs r
      rest = mkCirc l0 C to from fs
                    (∧ᵇ-trueʳ (any f C) (meetsAll fs C) e)

      pick : (∃[ w ∈ C ] w ∈ᵖ f)
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
       -> (∀ⁱ[ x ∈ ws ] x ∈ᵖ hasOut ws)
       -> Terminal ws -> Block ws fs
blockOf ws fs h (terminalAt r mr et) with meetsAll fs (sccOf ws r) in eb
... | true  = bFair r mr (mkCirc (loopAt mr et (h mr)) (sccOf ws r)
                                 (sccTo ws r) (sccFrom ws r) fs eb)
... | false = unf (all-false (λ g -> any g (sccOf ws r)) fs eb)
  where
    unf : (∃[ g ∈ fs ] any g (sccOf ws r) ≡ false)
       -> Block ws fs
    unf (g , mg , eg) = bUnfair r mr et g mg eg

pickBlock : (ws : List Node) (fs : List Pred)
         -> (∀ⁱ[ x ∈ ws ] x ∈ᵖ hasOut ws) -> Block ws fs
pickBlock []       fs h = bEmpty refl
pickBlock (u ∷ ws) fs h =
  blockOf (u ∷ ws) fs h (findTerminal (u ∷ ws) u here)

------------------------------------------------------------------------
-- The negative certificate: a well-founded record of the removal order,
-- indexed by what is LEFT.  Each step removes a vertex with no out-edge inside
-- ws, or a block closed under out-edges inside ws that misses a fairness
-- predicate.  cNil says nothing is left.

data Cert (fs : List Pred) : List Node -> Set where
  cNil   : (ws : List Node) -> null ws ≡ true -> Cert fs ws
  cSink  : (ws : List Node) (x : Node) -> x ∈ ws
        -> null (outs ws x) ≡ true
        -> Cert fs (ws ∖ᵛ x) -> Cert fs ws
  cBlock : (ws C : List Node) (f : Pred) -> f ∈ fs
        -> C closed-under G within ws -> C avoids f
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

fairInMono : {fs : List Pred}
          -> ws ⊆ vs -> FairIn ws fs -> FairIn vs fs
fairInMono subset (fairIn r mr c) = fairIn r (subset r mr) (circMono subset c)

-- Terminal-component removal, a REMOVING iteration: whichever step applies,
-- the vertex it names (the sink x, or the block's representative r) leaves ws
-- and the pool with it (dropInside).

module _ (fs : List Pred) where

  graphGo    : (ws : List Node) -> ws inside Pool -> Finiteᵛ Pool
            -> FairIn ws fs ⊎ Cert fs ws
  graphFind  : (ws : List Node) -> ws inside Pool -> Finiteᵛ Pool
            -> AllDecision (hasOut ws) ws
            -> FairIn ws fs ⊎ Cert fs ws
  graphBlock : (ws : List Node) -> ws inside Pool -> Finiteᵛ Pool
            -> Block ws fs -> FairIn ws fs ⊎ Cert fs ws

  graphGo ws subset fin = graphFind ws subset fin (decideAll (hasOut ws) ws)

  graphFind ws subset fin (allTrue f) =
    graphBlock ws subset fin (pickBlock ws fs f)
  graphFind ws subset (everyPick next) (counterexample x x∈ws noOut) =
    [ (λ fi -> inl (fairInMono (∖-⊆ ws (x ∷ [])) fi))
    , (λ c  -> inr (cSink ws x x∈ws (¬ᵇ-false (null (outs ws x)) noOut) c))
    ] (graphGo (ws ∖ᵛ x) (dropInside ws (x ∷ []) subset here)
               (next x (subset x x∈ws)))

  graphBlock ws subset fin (bEmpty e)       = inr (cNil ws e)
  graphBlock ws subset fin (bFair r r∈ws c) = inl (fairIn r r∈ws c)
  graphBlock ws subset (everyPick next)
             (bUnfair r r∈ws terminal g g∈fs gMissed) =
    [ (λ fi -> inl (fairInMono (∖-⊆ ws C) fi))
    , (λ c  -> inr (cBlock ws C g g∈fs (terminalClosed ws r terminal) miss c))
    ] (graphGo (ws ∖ C) (dropInside ws C subset (sccRep ws r r∈ws))
               (next r (subset r r∈ws)))
    where
      C : List Node
      C = sccOf ws r

      miss : ∀[ z ∈ C ] z ∉ᵖ g
      miss z mz = any-false g C gMissed mz

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
    (graphGo fs (reachSet vs v) (inside-∈ᵛ (reachSet vs v))
             (listFinite (reachSet vs v)))
  where
    into : ∀[ z ∈ reachSet vs v ] z ∈ vs
    into z m = reachIn vs v m

    toLoop : FairIn (reachSet vs v) fs -> FairLoop vs fs v
    toLoop (fairIn r mr c) =
      fairLoop r (reachTrail vs v mr)
                 (circMono into c)

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
                   -> C closed-under G within ws -> C avoids f
                   -> HoldsOutside R ws -> ∀[ z ∈ C ] R z)
         where

  -- One removal step: R holds outside ws ∖ C once it holds outside ws and
  -- on C.  A sink is the block x ∷ [].

  dropOutside : (ws C : List Node) -> HoldsOutside R ws -> (∀[ y ∈ C ] R y)
             -> HoldsOutside R (ws ∖ C)
  dropOutside ws C ih onC y eo with y ∈ᵛ C in ec
  ... | true  = onC y (∈ᵛ-sound y C ec)
  ... | false =
    ih y (∉ᵛ-intro y ws λ my -> ∈ᵛ-false y (ws ∖ C) eo (∈-∖⁺ C my ec))

  certAll : Cert fs ws -> HoldsOutside R ws
         -> (z : Node) -> R z
  certAll (cNil ws e)          ih z = ih z (null-∈ᵛ ws z e)
  certAll (cSink ws x mx e c)  ih z =
    certAll c (dropOutside ws (x ∷ []) ih onX) z
    where
      onX : ∀[ y ∈ x ∷ [] ] R y
      onX y here       = sinkCase ws x mx e ih
      onX y (there ())
  certAll (cBlock ws C f mf cl mis c) ih z =
    certAll c (dropOutside ws C ih (blockCase ws C f mf cl mis ih)) z

------------------------------------------------------------------------
-- The two outputs are EXCLUSIVE, by two observations about a closed trail:
--
--   a vertex on a cycle has a successor,  so a sink is on no cycle;
--   any vertex of a cycle reaches any other,  so a cycle that enters a
--     successor-closed block never leaves it.

-- The suffix of a trail from any vertex it visits, and the prefix to one: all
-- the "rotation" of a cycle the argument needs.

reachesCons : x ∈ ws -> G v x ≡ true -> Reaches ws x s -> Reaches ws v s
reachesCons m e (reachesBy zs t subset) = reachesBy (_ ∷ zs) (tCons e t) (∷-⊆ m subset)

reachesApp : Reaches ws u v -> Reaches ws v w -> Reaches ws u w
reachesApp (reachesBy as ta sa) (reachesBy bs tb sb) =
  reachesBy (as ++ bs) (trailApp ta tb) (++-⊆ as sa sb)

trailFrom : Trail v zs w -> zs ⊆ ws -> ∀ⁱ[ s ∈ v ∷ zs ] Reaches ws s w
trailFrom tNil        subset here      = reachesBy [] tNil (λ _ ())
trailFrom tNil        subset (there ())
trailFrom (tCons e t) subset here      = reachesBy _ (tCons e t) subset
trailFrom (tCons e t) subset (there k) = trailFrom t (⊆-tail subset) k

trailTo : Trail v zs w -> zs ⊆ ws -> ∀ⁱ[ s ∈ zs ] Reaches ws v s
trailTo tNil        subset ()
trailTo (tCons e t) subset here      =
  reachesBy (_ ∷ []) (tCons e tNil) (∷-⊆ (subset _ here) (λ _ ()))
trailTo (tCons e t) subset (there k) =
  reachesCons (subset _ here) e (trailTo t (⊆-tail subset) k)

-- Observation one: a vertex on a cycle has a successor inside ws.  Along a
-- trail every vertex visited has one provided the endpoint has, and for a
-- loop the endpoint is r, whose successor is the loop's first vertex.

record HasSucc (ws : List Node) (x : Node) : Set where
  constructor hasSucc
  field
    next   : Node
    nextIn : next ∈ ws
    edge   : G x next ≡ true

headSucc : Trail v zs w -> zs ⊆ ws -> HasSucc ws w -> HasSucc ws v
headSucc tNil                subset hw = hw
headSucc (tCons {x = y} e t) subset hw = hasSucc y (subset y here) e

trailSucc : Trail v zs w -> zs ⊆ ws -> HasSucc ws w
         -> ∀ⁱ[ x ∈ zs ] HasSucc ws x
trailSucc tNil        subset hw ()
trailSucc (tCons e t) subset hw here      =
  headSucc t (⊆-tail subset) hw
trailSucc (tCons e t) subset hw (there k) =
  trailSucc t (⊆-tail subset) hw k

loopSucc : {r : Node} (l : Loop ws r) -> ∀ⁱ[ x ∈ Loop.cycle l ] HasSucc ws x
loopSucc (loopBy q qs t@(tCons e _) h) = trailSucc t h (hasSucc q (h q here) e)

-- Observation two: any vertex of a cycle reaches any other (suffix to the
-- base point, then prefix out), and a successor-closed block that a trail
-- starts in contains everything the trail reaches (reachesEndIn, in
-- LTL.1-Lib.Graph).

cycConn : {r : Node} -> Trail r zs r -> zs ⊆ ws
       -> u ∈ zs -> z ∈ zs -> Reaches ws u z
cycConn t subset mu mz = reachesApp (trailFrom t subset (there mu)) (trailTo t subset mz)

-- A certificate for ws forbids a fair circuit inside ws.  By induction on the
-- certificate: each step leaves the cycle untouched, so it is still there when
-- nothing is left, which cNil forbids.

certNoCirc : (fs : List Pred)
          -> Cert fs ws -> (r : Node) -> Circuit ws fs r -> Empty
certNoCirc fs (cNil ws e)         r (circuit (loopBy q qs t h) wit) =
  null-∈ ws e (h q here)
certNoCirc fs (cSink ws x mx e c) r (circuit l@(loopBy q qs t h) wit) =
  certNoCirc fs c r
    (circuit (loopRestrict l (⊆-∖ (x ∷ []) h offX)) wit)
  where
    offCycle : x ∈ q ∷ qs -> Empty
    offCycle m = onS (loopSucc l m)
      where
        onS : HasSucc ws x -> Empty
        onS (hasSucc y my gy) =
          null-∈ (outs ws x) e (∈-filter⁺ (G x) ws my gy)

    offX : ∀[ z ∈ q ∷ qs ] (z ∈ x ∷ [] -> Empty)
    offX z mz here       = offCycle mz
    offX z mz (there ())
certNoCirc fs (cBlock ws C f mf cl mis c) r
           (circuit l@(loopBy q qs t h) wit) =
  certNoCirc fs c r
    (circuit (loopRestrict l (⊆-∖ C h inBlock)) wit)
  where
    inBlock : (z : Node) -> z ∈ q ∷ qs -> z ∈ C -> Empty
    inBlock z mz mzc = onW (wit f mf)
      where
        onW : (∃[ y ∈ q ∷ qs ] y ∈ᵖ f) -> Empty
        onW (y , my , fy) = true≢false (trans (sym fy) (mis y inC))
          where
            inC : y ∈ C
            inC = reachesEndIn cl mzc (cycConn t h mz my)

------------------------------------------------------------------------
-- The dichotomy at the top level: fairGraph's two answers cannot both hold, so
-- if a fair lasso from v exists, fairGraph returns one.  Restricting the
-- lasso's cycle to the reachable set uses reachComplete.

fairNoLoop : (vs : List Node) (fs : List Pred)
             (v : Node) -> v ∈ vs
          -> Cert fs (reachSet vs v) -> FairLoop vs fs v -> Empty
fairNoLoop vs fs v mv c (fairLoop r stem (circuit l@(loopBy q qs t h) wit)) =
  certNoCirc fs c r (circuit (loopRestrict l keep) wit)
  where
    keep : ∀[ z ∈ q ∷ qs ] z ∈ reachSet vs v
    keep z mz = reachComplete vs v mv (reachesApp stem (trailTo t h mz))

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

certShape : {fs : List Pred}
         -> Cert fs ws -> List CertStep
certShape (cNil ws e)                    = emptied ∷ []
certShape (cSink ws x mx e c)            = removedSink ∷ certShape c
certShape (cBlock ws C f mf cl mis c) = removedBlock ∷ certShape c

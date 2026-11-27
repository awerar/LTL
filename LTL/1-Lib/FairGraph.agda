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
--    is never built, and "terminal" is a boolean.  A terminal component is
--    the record TerminalIn, whose fields derive the component and its facts.
-- 2. fairOrCert is a REMOVING iteration (find a terminal component; unless
--    it is fair, delete it with its Reason: a sink, or missing a
--    predicate), so a finite pool covers termination; findTerminal finds a
--    terminal component by descending condensation edges, again by
--    recursion on a Finiteᵛ proof.  Both take theirs from listFinite, so
--    they need no guard.  Every step of a certificate therefore removes a
--    whole component.
--
-- Exclusivity needs no infinite paths: any vertex of a cycle reaches any
-- other, so a cycle that enters a successor-closed block lies inside it.  A
-- removed component is such a block, and it either is a sink, out of which
-- the cycle could not step, or misses a predicate the cycle meets.  This is
-- an induction on a finite trail.

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

sccReach : (ws : List Node) (r : Node) -> sccOf ws r ⊆ reachSet ws r
sccReach ws r w m =
  ∈-filter⁻ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) m

sccTo : (ws : List Node) (r : Node) -> ∀[ w ∈ sccOf ws r ] Reaches ws r w
sccTo ws r w m = reachTrail ws r (sccReach ws r w m)

sccFrom : (ws : List Node) (r : Node) -> ∀[ w ∈ sccOf ws r ] Reaches ws w r
sccFrom ws r w m =
  reachTrail ws w
    (∈ᵛ-sound (reachSet ws w) r
      (filter-prop (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) w m))

sccRep : (ws : List Node) -> ∀[ r ∈ ws ] r ∈ sccOf ws r
sccRep ws r mr =
  ∈-filter⁺ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r)
            (reachSeed ws r mr)
            (∈ᵛ-complete (reachSet ws r) r (reachSeed ws r mr))

------------------------------------------------------------------------
-- r's component is terminal when everything r reaches reaches r back, i.e.
-- the reachable set of r IS its component.  It is stated as decideAll's
-- allTrue gives it, so the search hands it over unchanged.

IsTerminal : List Node -> Node -> Set
IsTerminal ws r = ∀ⁱ[ w ∈ reachSet ws r ] r ∈ᵛ reachSet ws w ≡ true

terminalScc : (ws : List Node) (r : Node)
       -> IsTerminal ws r -> ∀ⁱ[ w ∈ reachSet ws r ] w ∈ sccOf ws r
terminalScc ws r et m =
  ∈-filter⁺ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) m (et m)

-- A terminal component is closed under successors inside ws: the refutation
-- needs exactly this of it.

terminalClosed : (ws : List Node) (r : Node)
          -> IsTerminal ws r -> Closed[ G ▷ ws ] (sccOf ws r)
terminalClosed ws r et {z} mz my e =
  terminalScc ws r et (reachClosed ws r (sccReach ws r z mz) my e)

-- A sink is a trivial terminal component: it reaches only itself, so its
-- component is {x}.  A trail out of x would start with an out-edge.

sinkOnly : (ws : List Node) (x : Node) -> Sink ws x
        -> ∀ⁱ[ w ∈ reachSet ws x ] w ≡ x
sinkOnly ws x e m = onTrail (reachTrail ws x m)
  where
    onTrail : Reaches ws x w -> w ≡ x
    onTrail (reachesBy _ tNil        subset) = refl
    onTrail (reachesBy _ (tCons g t) subset) =
      emptyElim (null-∈ (outs ws x) e (∈-filter⁺ (G x) ws (subset _ here) g))

sinkTerminal : (ws : List Node) (x : Node) -> x ∈ ws
            -> Sink ws x -> IsTerminal ws x
sinkTerminal ws x mx e m =
  subst (λ y -> x ∈ᵛ reachSet ws y ≡ true) (sym (sinkOnly ws x e m))
        (∈ᵛ-complete (reachSet ws x) x (reachSeed ws x mx))

------------------------------------------------------------------------
-- A terminal component of ws, as its representative r: found by
-- findTerminal below, decided by blockOf, removed by a certificate step.  The
-- component itself and what the steps use of it are derived from r.

record TerminalIn (ws : List Node) : Set where
  constructor terminalAt
  field
    r        : Node
    rIn      : r ∈ ws
    terminal : IsTerminal ws r

  component : List Node
  component = sccOf ws r

  rInComponent : r ∈ component
  rInComponent = sccRep ws r rIn

  componentClosed : Closed[ G ▷ ws ] component
  componentClosed = terminalClosed ws r terminal

  repReaches : ∀[ w ∈ component ] Reaches ws r w
  repReaches = sccTo ws r

  reachesRep : ∀[ w ∈ component ] Reaches ws w r
  reachesRep = sccFrom ws r

  -- If r is a sink, its component is r alone.

  sinkAlone : Sink ws r -> ∀[ y ∈ component ] y ≡ r
  sinkAlone e y my = sinkOnly ws r e (sccReach ws r y my)

open TerminalIn using (component; rInComponent; componentClosed;
                     repReaches; reachesRep; sinkAlone)

------------------------------------------------------------------------
-- A non-empty graph has a terminal component.  Start the search at any
-- vertex, r.  If r's component is not terminal, some w that r reaches does
-- not reach r back; move to w.  Then w reaches less than r did: everything w
-- reaches, r reaches, and r is not among it.  So no vertex the search leaves
-- is reached again, and it stops once the vertices run out.
--
-- For Agda, "reaches less" is a pool: Pool is the vertices the search may
-- still move to, avail says everything r reaches is in it, and each move
-- gives up r, which is the smaller pool next hands over.

module _ (ws : List Node) where

  -- One move, from r to a w that does not reach r: what w reaches is
  -- still in the pool once r is given up.

  reachesLess : (r w : Node) -> w ∈ reachSet ws r -> r ∈ᵛ reachSet ws w ≡ false
             -> All Pool (reachSet ws r) -> All (Pool ∩ (r ≢ᵛ_)) (reachSet ws w)
  reachesLess r w w∈reach noReturn avail =
    All-∩ (All-⊆ (λ z -> reachTrans ws r w z w∈reach) avail)
          (All-apart (_∈ᵛ reachSet ws w) noReturn (∈ᵛ-complete (reachSet ws w)))

  descend : (r : Node) -> r ∈ ws
         -> All Pool (reachSet ws r) -> Finiteᵛ Pool -> TerminalIn ws
  descend r r∈ws avail (everyPick next)
    with decideAll (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r)
  ... | allTrue reachBack = terminalAt r r∈ws reachBack
  ... | counterexample w w∈reach noReturn =
    descend w (reachIn ws r w∈reach) (reachesLess r w w∈reach noReturn avail)
            (next r (avail r (reachSeed ws r r∈ws)))

  -- A non-empty ws, one with a member x, has a terminal component.  The
  -- search starts at x, with all of ws in the pool.

  findTerminal : x ∈ ws -> TerminalIn ws
  findTerminal {x} x∈ws =
    descend x x∈ws (All-⊆ (λ z -> reachIn ws x) (∈ᵛ-complete ws))
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

-- A terminal component of a vertex that has a successor is non-trivial: the
-- successor is reached, so terminality sends a trail back.  No separate cycle
-- detection is needed.

module _ {ws : List Node} {r : Node} where

  loopAt : r ∈ ws
        -> IsTerminal ws r -> hasOut ws r ≡ true -> Loop ws r
  loopAt mr et ho =
    pick (null-false (outs ws r) (¬ᵇ-true (null (outs ws r)) ho))
    where
      pick : (Σ[ x ∈ Node ] x ∈ outs ws r) -> Loop ws r
      pick (x , mx) = loopBy x via (tCons grx trail) (∷-⊆ mxw staysIn)
        where
          mxw : x ∈ ws
          mxw = ∈-filter⁻ (G r) ws mx

          grx : G r x ≡ true
          grx = filter-prop (G r) ws x mx

          inR : x ∈ reachSet ws r
          inR = reachClosed ws r (reachSeed ws r mr) mxw grx

          open Reaches (sccFrom ws r x (terminalScc ws r et inR))

  -- One fairness predicate added to a circuit: the cycle, then a trail out
  -- to the witness w and one back to r.  The trail out starts at the cycle's
  -- first vertex q, so w is a vertex the new cycle VISITS.  trailApp is
  -- left-nested so that associativity never appears.

  consCirc : (f : Pred) (w : Node) -> f w ≡ true
          -> Reaches ws r w -> Reaches ws w r
          -> (fs : List Pred) -> Circuit ws fs r
          -> Circuit ws (f ∷ fs) r
  consCirc f w fw (reachesBy as ta sa) (reachesBy bs tb sb) fs
           (circuit (loopBy q qs t@(tCons e tq) scy) wit) =
    circuit (loopBy q ((qs ++ as) ++ bs) (trailApp (trailApp t ta) tb)
                    (++-⊆ out (++-⊆ cy scy sa) sb))
            each
    where
      cy out : List Node
      cy  = q ∷ qs
      out = cy ++ as

      each : ∀[ g ∈ f ∷ fs ] ∃[ z ∈ out ++ bs ] z ∈ᵖ g
      each g here      = w , ∈-++⁺ˡ out bs (trailEnd (trailApp tq ta)) , fw
      each g (there m) = shift (wit g m)
        where
          shift : (∃[ z ∈ cy ] z ∈ᵖ g) -> ∃[ z ∈ out ++ bs ] z ∈ᵖ g
          shift (z , mz , gz) = z , ∈-++⁺ˡ out bs (∈-++⁺ˡ cy as mz) , gz

  -- The circuit for fs: the loop l0, then one leg for each predicate, out
  -- to a witness in C and back.

  mkCirc : Loop ws r
        -> (C : List Node)
        -> (∀[ u ∈ C ] Reaches ws r u)
        -> (∀[ u ∈ C ] Reaches ws u r)
        -> (fs : List Pred) -> (∀ⁱ[ g ∈ fs ] any g C ≡ true)
        -> Circuit ws fs r
  mkCirc l0 C to from []        e = circuit l0 noF
    where
      noF : ∀[ f ∈ [] ] ∃[ z ∈ Loop.cycle l0 ] z ∈ᵖ f
      noF f ()
  mkCirc l0 C to from (f ∷ fs) e =
    pick (any-true f C (e here))
    where
      rest : Circuit ws fs r
      rest = mkCirc l0 C to from fs (λ m -> e (there m))

      pick : (∃[ w ∈ C ] w ∈ᵖ f)
          -> Circuit ws (f ∷ fs) r
      pick (w , mw , fw) =
        consCirc f w fw (to w mw) (from w mw) fs rest

------------------------------------------------------------------------
-- The negative certificate: a well-founded record of the removal order,
-- indexed by what is LEFT.  ws is the vertices still under consideration, and
-- every graph notion of a step (outs ws, IsTerminal ws, sccOf ws) is taken in
-- the subgraph on ws.  Each step (cRemove) removes a terminal component of it,
-- with the Reason it may go: it is trivial, a sink, or it misses a fairness
-- predicate.  The components are those of the starting graph, since removing
-- a closed union of components splits no other; only "terminal" is relative
-- to what is left.  cNil says nothing is left.

data Reason (fs : List Pred) {ws : List Node} (t : TerminalIn ws) : Set where
  sink   : Sink ws (TerminalIn.r t) -> Reason fs t
  unfair : (f : Pred) -> f ∈ fs -> None f (component t) -> Reason fs t

data Cert (fs : List Pred) : List Node -> Set where
  cNil    : Cert fs []
  cRemove : (t : TerminalIn ws) -> Reason fs t
         -> Cert fs (ws ∖ component t) -> Cert fs ws

------------------------------------------------------------------------
-- One step of the outer iteration, decided on a terminal component: if r has
-- no out-edge it is a sink; otherwise the component carries a loop, and it is
-- fair and a circuit is built, or it misses some f.  In the two cases that are
-- not fair the component is to be removed, and bRemove carries the Reason.
-- Nothing here recurses.

-- A fair circuit somewhere in ws, at the representative r.

record FairIn (ws : List Node) (fs : List Pred) : Set where
  constructor fairIn
  field
    r           : Node
    rIn         : r ∈ ws
    fairCircuit : Circuit ws fs r

data Block (ws : List Node) (fs : List Pred) : Set where
  bFair   : FairIn ws fs -> Block ws fs
  bRemove : (t : TerminalIn ws) -> Reason fs t -> Block ws fs

blockOf : (ws : List Node) (fs : List Pred) -> TerminalIn ws -> Block ws fs
blockOf ws fs t@(terminalAt r mr et) with hasOut ws r in eo
... | false = bRemove t (sink (¬ᵇ-false (null (outs ws r)) eo))
... | true with decideAll (λ g -> any g (component t)) fs
...   | allTrue e =
  bFair (fairIn r mr (mkCirc (loopAt mr et eo) (component t)
                             (repReaches t) (reachesRep t) fs e))
...   | counterexample g mg eg = bRemove t (unfair g mg miss)
  where
    miss : None g (component t)
    miss z mz = any-false g (component t) eg mz

------------------------------------------------------------------------
-- The theorem, on a sub-list

fairInMono : {fs : List Pred}
          -> ws ⊆ vs -> FairIn ws fs -> FairIn vs fs
fairInMono subset (fairIn r mr c) = fairIn r (subset r mr) (circMono subset c)

-- Terminal-component removal, a REMOVING iteration: while ws is non-empty,
-- find a terminal component and decide it; if it is not fair, its
-- representative r leaves ws with the rest of the component, and the pool
-- loses r (All-∖).

module _ (fs : List Pred) where

  fairOrCert : (ws : List Node) -> All Pool ws -> Finiteᵛ Pool
            -> FairIn ws fs ⊎ Cert fs ws
  fairOrCert []         subset fin              = inr cNil
  fairOrCert ws@(u ∷ _) subset (everyPick next)
    with blockOf ws fs (findTerminal ws here)
  ... | bFair fi       = inl fi
  ... | bRemove t why =
    [ (λ fi -> inl (fairInMono (∖-⊆ ws C) fi)) , (λ c -> inr (cRemove t why c)) ]
      (fairOrCert (ws ∖ C) (All-∖ ws C (∖-⊆ ws C) subset (rInComponent t))
                  (next r (subset r rIn)))
    where
      open TerminalIn t using (r; rIn)

      C : List Node
      C = component t


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
         -> ∀[ v ∈ vs ] (FairLoop vs fs v ⊎ Cert fs (reachSet vs v))
fairGraph vs fs v mv =
  [ (λ fi -> inl (toLoop fi)) , inr ]
    (fairOrCert fs (reachSet vs v) (∈ᵛ-complete (reachSet vs v))
                (listFinite (reachSet vs v)))
  where
    into : reachSet vs v ⊆ vs
    into z m = reachIn vs v m

    toLoop : FairIn (reachSet vs v) fs -> FairLoop vs fs v
    toLoop (fairIn r mr c) =
      fairLoop r (reachTrail vs v mr)
                 (circMono into c)

------------------------------------------------------------------------
-- What a certificate is for: an induction over the removal order.  R is the
-- property to establish of every vertex (for LTL.7-SCC.SccExtract, refutability
-- of chi), and the hypothesis carried is "R holds outside ws".  The sink and
-- block cases are the two hypotheses of certAll; they ask only for what each
-- refutation uses, a sink and a closed block, not for a component.

module _ (fs : List Pred) (R : Node -> Set)
         (sinkCase  : (ws : List Node) (x : Node) -> x ∈ ws
                   -> Sink ws x
                   -> HoldsOutside R ws -> R x)
         (blockCase : (ws C : List Node) (f : Pred) -> f ∈ fs
                   -> Closed[ G ▷ ws ] C -> None f C
                   -> HoldsOutside R ws -> ∀[ z ∈ C ] R z)
         where

  -- One removal step: R holds outside ws ∖ C once it holds outside ws and
  -- on C.

  dropOutside : (ws C : List Node) -> HoldsOutside R ws -> (∀[ y ∈ C ] R y)
             -> HoldsOutside R (ws ∖ C)
  dropOutside ws C ih onC y eo with y ∈ᵛ C in ec
  ... | true  = onC y (∈ᵛ-sound C y ec)
  ... | false =
    ih y (∉ᵛ-intro ws y λ my -> ∈ᵛ-false (ws ∖ C) y eo (∈-∖⁺ C my ec))

  -- A component removed for a reason: R holds on all of it, by sinkCase at
  -- its only vertex or by blockCase.

  removedHolds : (t : TerminalIn ws) -> Reason fs t -> HoldsOutside R ws
              -> ∀[ y ∈ component t ] R y
  removedHolds {ws} t (sink e) ih y my =
    subst R (sym (sinkAlone t e y my)) (sinkCase ws r rIn e ih)
    where open TerminalIn t using (r; rIn)
  removedHolds {ws} t (unfair f mf mis) ih =
    blockCase ws (component t) f mf (componentClosed t) mis ih

  certAll : Cert fs ws -> HoldsOutside R ws
         -> (z : Node) -> R z
  certAll       cNil              ih z = ih z refl
  certAll {ws} (cRemove t why c) ih z =
    certAll c (dropOutside ws (component t) ih (removedHolds t why ih)) z

------------------------------------------------------------------------
-- The two outputs are EXCLUSIVE, by one observation about a closed trail:
-- any vertex of a cycle reaches any other, so a cycle that enters a
-- successor-closed block lies inside it.

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

-- Any vertex of a cycle reaches any other: the suffix to the base point, then
-- the prefix out.

cycConn : {r : Node} -> Trail r zs r -> zs ⊆ ws
       -> u ∈ zs -> z ∈ zs -> Reaches ws u z
cycConn t subset mu mz = reachesApp (trailFrom t subset (there mu)) (trailTo t subset mz)

-- A closed set that a cycle enters contains the whole cycle, since it
-- contains everything a trail starting in it reaches (reachesEndIn, in
-- LTL.1-Lib.Graph).

cycleIn : {C : List Node} -> Closed[ G ▷ ws ] C -> Trail s zs s -> zs ⊆ ws
       -> z ∈ zs -> z ∈ C -> ∀ⁱ[ y ∈ zs ] y ∈ C
cycleIn cl t subset mz mzc my = reachesEndIn cl mzc (cycConn t subset mz my)

-- A circuit in ws misses every component removed for a reason, since the
-- component is closed: entered, it would contain the whole cycle.  For a sink
-- that puts the base point s, the end of the cycle, in {r}, and the loop's
-- first step leaves s; for an unfair component, the witness of the f it
-- misses.

avoids : {fs : List Pred} (t : TerminalIn ws) -> Reason fs t
      -> (c : Circuit ws fs s)
      -> ∀[ z ∈ Loop.cycle (Circuit.loop c) ] (z ∈ component t -> Empty)
avoids {ws} {s = s} t (sink e) (circuit (loopBy q qs tr@(tCons g tq) h) wit) z mz mzc =
  null-∈ (outs ws r) e
    (∈-filter⁺ (G r) ws (h q here) (subst (λ y -> G y q ≡ true) sIsR g))
  where
    open TerminalIn t using (r)

    sIsR : s ≡ r
    sIsR = sinkAlone t e _
             (cycleIn (componentClosed t) tr h mz mzc (trailEnd tq))
avoids t (unfair f mf mis) (circuit (loopBy q qs tr h) wit) z mz mzc =
  onW (wit f mf)
  where
    onW : (∃[ y ∈ q ∷ qs ] y ∈ᵖ f) -> Empty
    onW (y , my , fy) =
      true≢false
        (trans (sym fy) (mis y (cycleIn (componentClosed t) tr h mz mzc my)))

-- A certificate for ws forbids a fair circuit inside ws.  By induction on the
-- certificate: each step leaves the cycle untouched, so it is still there when
-- nothing is left, which cNil forbids.

certNoCirc : (fs : List Pred)
          -> Cert fs ws -> (r : Node) -> Circuit ws fs r -> Empty
certNoCirc fs cNil              s (circuit (loopBy q qs t h) wit) =
  null-∈ [] refl (h q here)
certNoCirc fs (cRemove t why c) s ci@(circuit l wit) =
  certNoCirc fs c s
    (circuit (loopRestrict l (⊆-∖ (component t) (Loop.staysIn l)
                                 (avoids t why ci)))
             wit)

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
    keep : q ∷ qs ⊆ reachSet vs v
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

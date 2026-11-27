{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.FairGraph -- the finite fair-graph certificate theorem.
--
--   Given a finite graph and finitely many decidable fairness predicates,
--   fairOrCert computes either
--     (a) a fair circuit in it, a cycle that meets every predicate (FairIn), or
--     (b) a well-founded certificate that removes the graph one terminal
--         component at a time, each a sink or missing some predicate (Cert).
--
-- fairGraph runs it on what a vertex v reaches, and turns (a) into a lasso
-- from v (FairLoop); certAll is the induction principle a Cert supplies.  The
-- module is parameterised like LTL.1-Lib.Graph, whose trails and reachable
-- set it uses; the fairness sets are fs : List Pred.
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
-- As in LTL.1-Lib.Graph, so is ws wherever a trail, loop, circuit, r ∈ ws or
-- TerminalIn ws fixes it; it stays explicit where it only occurs under a
-- function (sccOf ws r).

private variable
  u v w x z   : Node
  ws vs       : Subgraph
  zs          : List Node
  Pool        : Pred

------------------------------------------------------------------------
-- Components, without component objects: sccOf ws r is the vertices r
-- reaches that reach r back.  A filter of a list, nothing more.

sccOf : Subgraph -> Node -> List Node
sccOf ws r = filter (λ w -> r ∈ᵛ reachSet ws w) (reachSet ws r)

sccReach : (ws : Subgraph) (r : Node) -> sccOf ws r ⊆ reachSet ws r
sccReach ws r w m =
  ∈-filter⁻ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) m

sccTo : (ws : Subgraph) (r : Node) -> ∀[ w ∈ sccOf ws r ] Reaches ws r w
sccTo ws r w m = reachTrail ws r (sccReach ws r w m)

sccFrom : (ws : Subgraph) (r : Node) -> ∀[ w ∈ sccOf ws r ] Reaches ws w r
sccFrom ws r w m =
  reachTrail ws w
    (∈ᵛ-sound (reachSet ws w) r
      (filter-prop (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) w m))

sccRep : ∀[ r ∈ ws ] r ∈ sccOf ws r
sccRep {ws} r mr =
  ∈-filter⁺ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r)
            (reachSeed r mr)
            (∈ᵛ-complete (reachSet ws r) r (reachSeed r mr))

------------------------------------------------------------------------
-- r's component is terminal when everything r reaches reaches r back, i.e.
-- the reachable set of r IS its component.  It is stated as decideAll's
-- allTrue gives it, so the search hands it over unchanged.

IsTerminal : Subgraph -> Node -> Set
IsTerminal ws r = ∀ⁱ[ w ∈ reachSet ws r ] r ∈ᵛ reachSet ws w ≡ true

terminalScc : (ws : Subgraph) (r : Node)
       -> IsTerminal ws r -> ∀ⁱ[ w ∈ reachSet ws r ] w ∈ sccOf ws r
terminalScc ws r et m =
  ∈-filter⁺ (λ z -> r ∈ᵛ reachSet ws z) (reachSet ws r) m (et m)

-- A terminal component is closed under successors inside ws: the refutation
-- needs exactly this of it.

terminalClosed : (ws : Subgraph) (r : Node)
          -> IsTerminal ws r -> Closed[ G ▷ ws ] (sccOf ws r)
terminalClosed ws r et {z} mz my e =
  terminalScc ws r et (reachClosed ws r (sccReach ws r z mz) my e)

-- A sink reaches only itself, so its component is {x}: a trail out of x
-- would start with an out-edge.

sinkOnly : (ws : Subgraph) (x : Node) -> Sink ws x
        -> ∀ⁱ[ w ∈ reachSet ws x ] w ≡ x
sinkOnly ws x e m = onTrail (reachTrail ws x m)
  where
    onTrail : Reaches ws x w -> w ≡ x
    onTrail (reachesBy _ tNil        subset) = refl
    onTrail (reachesBy _ (tCons g t) subset) =
      emptyElim (null-∈ (outs ws x) e (∈-filter⁺ (G x) ws (subset _ here) g))

------------------------------------------------------------------------
-- A terminal component of ws, as its representative r: found by
-- findTerminal below, decided by decideTerminal, removed by a certificate
-- step.  The component itself and what the steps use of it are derived
-- from r.

record TerminalIn (ws : Subgraph) : Set where
  constructor terminalAt
  field
    r        : Node
    rIn      : r ∈ ws
    terminal : IsTerminal ws r

  component : List Node
  component = sccOf ws r

  rInComponent : r ∈ component
  rInComponent = sccRep r rIn

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

module _ (ws : Subgraph) where

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
            (next r (avail r (reachSeed r r∈ws)))

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

record Loop (ws : Subgraph) (r : Node) : Set where
  constructor loopBy
  field
    next    : Node
    back    : List Node
    trail   : Trail r (next ∷ back) r
    staysIn : next ∷ back ⊆ ws

  cycle : List Node
  cycle = next ∷ back

record Circuit (ws : Subgraph) (fs : List Pred)
               (r : Node) : Set where
  constructor circuit
  field
    loop  : Loop ws r
    meets : ∀[ f ∈ fs ] ∃[ z ∈ Loop.cycle loop ] z ∈ᵖ f

-- The base point r is the end of the loop's trail, so a vertex it visits.

loopBase : {r : Node} -> Loop ws r -> r ∈ ws
loopBase (loopBy q qs (tCons e t) h) = h _ (trailEnd t)

module _ {ws vs : Subgraph} {r : Node} where

  circMono : {fs : List Pred} -> ws ⊆ vs -> Circuit ws fs r -> Circuit vs fs r
  circMono subset (circuit (loopBy q qs t h) wit) =
    circuit (loopBy q qs t (λ z mz -> subset z (h z mz))) wit

-- A terminal component of a vertex that has a successor is non-trivial: the
-- successor is reached, so terminality sends a trail back.  No separate cycle
-- detection is needed.

module _ {ws : Subgraph} {r : Node} where

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
          inR = reachClosed ws r (reachSeed r mr) mxw grx

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

data Reason (fs : List Pred) {ws : Subgraph} (t : TerminalIn ws) : Set where
  sink   : Sink ws (TerminalIn.r t) -> Reason fs t
  unfair : (f : Pred) -> f ∈ fs -> None f (component t) -> Reason fs t

data Cert (fs : List Pred) : Subgraph -> Set where
  cNil    : Cert fs []
  cRemove : (t : TerminalIn ws) -> Reason fs t
         -> Cert fs (ws ∖ component t) -> Cert fs ws

------------------------------------------------------------------------
-- One step of the outer iteration, decided on a terminal component t: if r
-- has no out-edge it is a sink; otherwise the component carries a loop, and
-- it is fair and a circuit is built, or it misses some f.  In the two cases
-- that are not fair t is to be removed, and the answer is the Reason.
-- Nothing here recurses.

-- A fair circuit somewhere in ws, at r (which is in ws by loopBase).

record FairIn (ws : Subgraph) (fs : List Pred) : Set where
  constructor fairIn
  field
    r           : Node
    fairCircuit : Circuit ws fs r

decideTerminal : (fs : List Pred) (t : TerminalIn ws)
              -> FairIn ws fs ⊎ Reason fs t
decideTerminal {ws} fs t@(terminalAt r mr et) with hasOut ws r in eo
... | false = inr (sink (¬ᵇ-false (null (outs ws r)) eo))
... | true with decideAll (λ g -> any g (component t)) fs
...   | allTrue e =
  inl (fairIn r (mkCirc (loopAt mr et eo) (component t)
                        (repReaches t) (reachesRep t) fs e))
...   | counterexample g mg eg = inr (unfair g mg miss)
  where
    miss : None g (component t)
    miss z mz = any-false g (component t) eg mz

------------------------------------------------------------------------
-- The theorem, on a sub-list

fairInMono : {fs : List Pred}
          -> ws ⊆ vs -> FairIn ws fs -> FairIn vs fs
fairInMono subset (fairIn r c) = fairIn r (circMono subset c)

-- Terminal-component removal, a REMOVING iteration: while ws is non-empty,
-- find a terminal component and decide it; if it is not fair, its
-- representative r leaves ws with the rest of the component, and the pool
-- loses r (All-∖).

module _ (fs : List Pred) where

  fairOrCert : (ws : Subgraph) -> All Pool ws -> Finiteᵛ Pool
            -> FairIn ws fs ⊎ Cert fs ws
  fairOrCert []         subset fin              = inr cNil
  fairOrCert ws@(u ∷ _) subset (everyPick next)
    with findTerminal ws here
  ... | t with decideTerminal fs t
  ...   | inl fi  = inl fi
  ...   | inr why =
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

record FairLoop (vs : Subgraph) (fs : List Pred)
                (v : Node) : Set where
  constructor fairLoop
  field
    r           : Node   -- where the cycle starts and ends
    stem        : Reaches vs v r
    fairCircuit : Circuit vs fs r

fairGraph : (vs : Subgraph) (fs : List Pred)
         -> ∀[ v ∈ vs ] (FairLoop vs fs v ⊎ Cert fs (reachSet vs v))
fairGraph vs fs v mv =
  [ (λ fi -> inl (toLoop fi)) , inr ]
    (fairOrCert fs (reachSet vs v) (∈ᵛ-complete (reachSet vs v))
                (listFinite (reachSet vs v)))
  where
    into : reachSet vs v ⊆ vs
    into z m = reachIn vs v m

    toLoop : FairIn (reachSet vs v) fs -> FairLoop vs fs v
    toLoop (fairIn r c) =
      fairLoop r (reachTrail vs v (loopBase (Circuit.loop c)))
                 (circMono into c)

------------------------------------------------------------------------
-- What a certificate is for: an induction over the removal order.  R is the
-- property to establish of every vertex (for LTL.7-SCC.SccExtract, refutability
-- of chi), and the hypothesis carried is "R holds outside ws".  The sink and
-- block cases are the two hypotheses of certAll; they ask only for what each
-- refutation uses, a sink and a closed block, not for a component.

module _ (fs : List Pred) (R : Node -> Set)
         (sinkCase  : (ws : Subgraph) (x : Node) -> Sink ws x
                   -> HoldsOutside R ws -> R x)
         (blockCase : (ws : Subgraph) (C : List Node) (f : Pred) -> f ∈ fs
                   -> Closed[ G ▷ ws ] C -> None f C
                   -> HoldsOutside R ws -> ∀[ z ∈ C ] R z)
         where

  -- One removal step: R holds outside ws ∖ C once it holds outside ws and
  -- on C.

  dropOutside : (ws : Subgraph) (C : List Node)
             -> HoldsOutside R ws -> (∀[ y ∈ C ] R y)
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
    subst R (sym (sinkAlone t e y my)) (sinkCase ws (TerminalIn.r t) e ih)
  removedHolds {ws} t (unfair f mf mis) ih =
    blockCase ws (component t) f mf (componentClosed t) mis ih

  certAll : Cert fs ws -> HoldsOutside R ws
         -> (z : Node) -> R z
  certAll       cNil              ih z = ih z refl
  certAll {ws} (cRemove t why c) ih z =
    certAll c (dropOutside ws (component t) ih (removedHolds t why ih)) z

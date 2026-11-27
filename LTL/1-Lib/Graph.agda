{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Graph -- finite graphs given by an edge test: trails, the growing
-- search closure, and the reachable set.
--
-- There is no logic here: the module is parameterised by a node type with an
-- equality test eq (LTL.1-Lib.DecEq), and by the edge test G, which no definition
-- changes; it imports only the generic set layer.  A graph is a vertex list
-- ws with the edges of G.  LTL.1-Lib.FairGraph proves the fair-graph
-- certificate theorem on top of it.  LTL.6-Countermodel.Walk instantiates both
-- at Val with G = step P; LTL.9-Tests.GraphExamples at Nat.
--
-- The reachable set is a GROWING search (closure) that stops when a round
-- adds nothing; completeness comes from the stopping condition, not a bound.
-- The search is generic in its seeds, and LTL.5-States.Closure builds Ust with
-- it too.  closure takes its Finiteᵛ proof as an argument, so that Ust can use
-- the guarded stateFinite; reachSet takes listFinite, which is blocked while
-- the list is a variable, so it needs no guard against normalisation blow-up.

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.DecEq using (DecEq)

module LTL.1-Lib.Graph {Node : Set} (eq : DecEq Node)
                       (G : Node -> Node -> Bool) where

-- Not re-exported: an importer gets this module's own names only, and takes
-- the set layer from wherever it already has it (LTL.5-States.Reach, at Val).

open import LTL.1-Lib.Sets
open import LTL.1-Lib.Exhaustible
open import LTL.1-Lib.Nodes eq

-- G is fixed, so a Subgraph (LTL.1-Lib.Nodes), a vertex list, is the
-- subgraph of G induced on it.  Every graph notion below is taken inside one
-- (outs ws x, Reaches ws v w, reachSet ws v); other lists of nodes (the
-- vertices a trail visits, a component C) stay List Node.

-- The implicit arguments the signatures below leave out: the endpoints and
-- visited list of a trail, and the pool a search recurses on.
-- So is the subgraph ws wherever a Reaches, Closed or v ∈ ws hypothesis
-- fixes it; it stays explicit where it only occurs under a function, as in
-- reachSet ws v.

private variable
  u v w x s : Node
  ws        : Subgraph
  xs zs     : List Node
  Pool      : Pred

------------------------------------------------------------------------
-- Out-neighbours

-- The out-neighbours of x inside ws.  For G = step P this is succs P ws x on
-- the nose.

outs : Subgraph -> Node -> List Node
outs ws x = filter (G x) ws

hasOut : Subgraph -> Node -> Bool
hasOut ws x = ¬ᵇ null (outs ws x)

-- x is a sink in ws: it has no out-neighbour there.

Sink : Subgraph -> Node -> Set
Sink ws x = null (outs ws x) ≡ true

------------------------------------------------------------------------
-- Trails: finite G-paths, carrying the vertices visited and indexed by the
-- endpoint.  A trail knows nothing of a vertex list: that it stays inside ws
-- is the separate fact  zs ⊆ ws , kept beside it (Reaches below, Loop in
-- LTL.1-Lib.FairGraph).  At G = step P trails are the walks of
-- LTL.6-Countermodel.Walk.

data Trail : Node -> List Node -> Node -> Set where
  tNil  : {v : Node} -> Trail v [] v
  tCons : {v x : Node} {zs : List Node} {w : Node}
       -> G v x ≡ true -> Trail x zs w -> Trail v (x ∷ zs) w

trailApp : Trail u xs v -> Trail v zs w -> Trail u (xs ++ zs) w
trailApp tNil         t2 = t2
trailApp (tCons e t1) t2 = tCons e (trailApp t1 t2)

trailEnd : Trail v zs w -> w ∈ v ∷ zs
trailEnd tNil        = here
trailEnd (tCons e t) = there (trailEnd t)

-- w is reachable from v inside ws: a trail, and the vertices it visits, all
-- in ws.

record Reaches (ws : Subgraph) (v w : Node) : Set where
  constructor reachesBy
  field
    via     : List Node
    trail   : Trail v via w
    staysIn : via ⊆ ws

-- The prefix of a trail to any vertex it visits: LTL.7-SCC.SccLasso follows a
-- cycle's prefix to a fairness witness.

reachesCons : x ∈ ws -> G v x ≡ true -> Reaches ws x s -> Reaches ws v s
reachesCons m e (reachesBy zs t subset) = reachesBy (_ ∷ zs) (tCons e t) (∷-⊆ m subset)

trailTo : Trail v zs w -> zs ⊆ ws -> ∀ⁱ[ s ∈ zs ] Reaches ws v s
trailTo tNil        subset ()
trailTo (tCons e t) subset here      =
  reachesBy (_ ∷ []) (tCons e tNil) (∷-⊆ (subset _ here) (λ _ ()))
trailTo (tCons e t) subset (there k) =
  reachesCons (subset _ here) e (trailTo t (⊆-tail subset) k)

-- A set C closed under G inside ws keeps every trail inside ws that starts in
-- it: the trail lies in C, and so does its endpoint.

module _ {ws : Subgraph} {C : List Node} (cl : Closed[ G ▷ ws ] C) where

  private
    trailInto : u ∈ C -> Trail u zs w -> zs ⊆ ws -> zs ⊆ C
    trailInto mu tNil        subset z ()
    trailInto mu (tCons e t) subset _ here      = cl mu (subset _ here) e
    trailInto mu (tCons e t) subset z (there k) =
      trailInto (cl mu (subset _ here) e) t (⊆-tail subset) z k

    trailEndIn : u ∈ C -> Trail u zs w -> zs ⊆ ws -> w ∈ C
    trailEndIn mu tNil        subset = mu
    trailEndIn mu (tCons e t) subset =
      trailEndIn (cl mu (subset _ here) e) t (⊆-tail subset)

  reachesInto : u ∈ C -> Reaches ws u w -> Reaches C u w
  reachesInto mu (reachesBy zs t subset) = reachesBy zs t (trailInto mu t subset)

  reachesEndIn : u ∈ C -> Reaches ws u w -> w ∈ C
  reachesEndIn mu (reachesBy zs t subset) = trailEndIn mu t subset

------------------------------------------------------------------------
-- The growing search.  closure Seed ws is the least part of ws that contains
-- every member satisfying the seed test Seed and is closed under G-successors
-- inside ws.  A round adds every vertex of ws that is wanted -- satisfies Seed,
-- or is a G-successor of something already in acc -- and is not there yet;
-- when a round adds nothing, acc contains every wanted vertex, which is
-- completeness.  Both the reachable set below (Seed = v ≡ᵛ_) and Ust of
-- LTL.5-States.Closure (Seed = "contains P") are instances.

module _ (Seed : Pred) (ws : Subgraph) where

  wanted : List Node -> Node -> Bool
  wanted acc x = Seed x ∨ᵇ any (λ y -> G y x) acc

  -- x is missing when it is wanted and acc lacks it.  A round looks for a
  -- missing x with decideAny, and the search stops when none is missing.

  missing : List Node -> Node -> Bool
  missing acc x = wanted acc x ∧ᵇ ¬ᵇ (x ∈ᵛ acc)

  addRound : List Node -> List Node
  addRound acc = filter (missing acc) ws ++ acc

  notInAcc : (acc : List Node) (x : Node)
          -> missing acc x ≡ true -> x ∈ᵛ acc ≡ false
  notInAcc acc x xMissing =
    ¬ᵇ-true (x ∈ᵛ acc) (∧ᵇ-trueʳ (wanted acc x) (¬ᵇ (x ∈ᵛ acc)) xMissing)

  -- A wanted vertex that is not missing is already in.

  wantedIn : (acc : List Node) (x : Node)
          -> missing acc x ≡ false -> wanted acc x ≡ true -> x ∈ acc
  wantedIn acc x s w =
    ∈ᵛ-sound acc x
      (¬ᵇ-false (x ∈ᵛ acc)
                (¬ᵇ∧ᵇ-cancelˡ (wanted acc x) (¬ᵇ (x ∈ᵛ acc)) (cong ¬ᵇ_ s) w))

  -- A round adds the missing x, so x leaves the candidates still available
  -- and the pool with it.

  availRound : (acc : List Node) (x : Node)
            -> x ∈ ws -> missing acc x ≡ true -> All Pool (ws ∖ acc)
            -> All (Pool ∩ (x ≢ᵛ_)) (ws ∖ addRound acc)
  availRound acc x m xMissing avail =
    All-∖ ws (addRound acc)
          (∖-antitone ws (λ z -> ∈-++⁺ʳ (filter (missing acc) ws) acc)) avail
          (∈-++⁺ˡ (filter (missing acc) ws) acc
                  (∈-filter⁺ (missing acc) ws m xMissing))

  ------------------------------------------------------------------------
  -- The invariants: the accumulator lies in ws, and each member is reached
  -- from a seed.

  roundIn : (acc : List Node) -> acc ⊆ ws -> addRound acc ⊆ ws
  roundIn acc subset z mz =
    [ ∈-filter⁻ (missing acc) ws , subset z ]
      (∈-++⁻ (filter (missing acc) ws) acc mz)

-- z is reached inside ws from a seed: a member of ws satisfying Seed.

record Seeded (Seed : Pred) (ws : Subgraph) (z : Node) : Set where
  constructor seededBy
  field
    seed      : Node
    seedIn    : seed ∈ ws
    seedHolds : Seed seed ≡ true
    reaches   : Reaches ws seed z

-- Every vertex a round adds is seeded: it is a seed itself, or a successor of
-- a member of acc, whose trail grows by one step.

roundSeeded : (Seed : Pred) (ws : Subgraph) (acc : List Node)
           -> (∀[ z ∈ acc ] Seeded Seed ws z)
           -> ∀[ z ∈ addRound Seed ws acc ] Seeded Seed ws z
roundSeeded Seed ws acc sd z m =
  [ fromNew , sd z ] (∈-++⁻ (filter (missing Seed ws acc) ws) acc m)
  where
    fromNew : z ∈ filter (missing Seed ws acc) ws -> Seeded Seed ws z
    fromNew z∈new = [ isSeed , viaY ] (∨ᵇ-true (Seed z) (any (λ y -> G y z) acc) want)
      where
        z∈ws : z ∈ ws
        z∈ws = ∈-filter⁻ (missing Seed ws acc) ws z∈new

        want : wanted Seed ws acc z ≡ true
        want = ∧ᵇ-trueˡ (wanted Seed ws acc z) (¬ᵇ (z ∈ᵛ acc))
                        (filter-prop (missing Seed ws acc) ws z z∈new)

        isSeed : Seed z ≡ true -> Seeded Seed ws z
        isSeed e = seededBy z z∈ws e (reachesBy [] tNil (λ _ ()))

        viaY : any (λ y -> G y z) acc ≡ true -> Seeded Seed ws z
        viaY ea = pick (any-true (λ y -> G y z) acc ea)
          where
            pick : (∃[ y ∈ acc ] G y z ≡ true) -> Seeded Seed ws z
            pick (y , my , gy) =
              seededBy seed seedIn seedHolds
                       (reachesBy (via ++ z ∷ [])
                                  (trailApp trail (tCons gy tNil))
                                  (++-⊆ via staysIn (∷-⊆ z∈ws (λ _ ()))))
              where
                open Seeded (sd y my)
                open Reaches reaches

------------------------------------------------------------------------
-- The search itself, as a loop with an invariant.  GrowInv is what every
-- accumulator satisfies: it lies in ws, and each member is seeded.  The search
-- returns an accumulator that satisfies it and the stopping condition,
-- nothing missing, and the closure's properties are read off the two.  The
-- search also keeps All Pool (ws ∖ acc), which only makes it stop.

module _ (Seed : Pred) (ws : Subgraph) where

  record GrowInv (acc : List Node) : Set where
    constructor growInv
    field
      accIn     : acc ⊆ ws
      accSeeded : ∀[ z ∈ acc ] Seeded Seed ws z

  record Grown : Set where
    constructor grown
    field
      result   : List Node
      inv      : GrowInv result
      complete : ∀ⁱ[ x ∈ ws ] missing Seed ws result x ≡ false

  -- Stop when nothing is missing, else add the missing vertices and recurse.

  grow : (acc : List Node) -> All Pool (ws ∖ acc) -> GrowInv acc
      -> Finiteᵛ Pool -> Grown
  grow acc avail inv (everyPick next) with decideAny (missing Seed ws acc) ws
  ... | noneTrue f           = grown acc inv f
  ... | witness x m xMissing =
    grow (addRound Seed ws acc) (availRound Seed ws acc x m xMissing avail)
         (growInv (roundIn Seed ws acc accIn) (roundSeeded Seed ws acc accSeeded))
         (next x (avail x (∈-∖⁺ acc m (notInAcc Seed ws acc x xMissing))))
    where open GrowInv inv

-- The closure: the search from the empty accumulator, and its properties.
-- subset and fin say which pool the search recurses on: every vertex of ws
-- is in it, and it is finite.  Outside the block, closure takes all five
-- arguments.

module _ (Seed : Pred) (ws : Subgraph) {Pool : Pred} (subset : All Pool ws)
         (fin : Finiteᵛ Pool) where

  open Grown (grow Seed ws [] (λ z mz -> subset z (∖-⊆ ws [] z mz))
                   (growInv (λ _ ()) (λ _ ())) fin)
  open GrowInv inv

  closure : List Node
  closure = result

  closureIn : closure ⊆ ws
  closureIn = accIn

  closureSeeded : ∀[ z ∈ closure ] Seeded Seed ws z
  closureSeeded = accSeeded

  closureSeed : {z : Node} -> z ∈ ws -> Seed z ≡ true -> z ∈ closure
  closureSeed {z} mz e =
    wantedIn Seed ws result z (complete mz)
      (∨ᵇ-introˡ (Seed z) (any (λ y -> G y z) result) e)

  closureClosed : Closed[ G ▷ ws ] closure
  closureClosed mu {w} mw e =
    wantedIn Seed ws result w (complete mw)
      (∨ᵇ-introʳ (Seed w) (any (λ y -> G y w) result)
                 (any-intro (λ y -> G y w) result mu e))

------------------------------------------------------------------------
-- The reachable set: the closure of the single seed v, on listFinite ws.

reachSet : Subgraph -> Node -> List Node
reachSet ws v = closure (v ≡ᵛ_) ws (∈ᵛ-complete ws) (listFinite ws)

reachIn : (ws : Subgraph) (v : Node)
       -> ∀ⁱ[ z ∈ reachSet ws v ] z ∈ ws
reachIn ws v {z} = closureIn (v ≡ᵛ_) ws (∈ᵛ-complete ws) (listFinite ws) z

reachTrail : (ws : Subgraph) (v : Node)
          -> ∀ⁱ[ z ∈ reachSet ws v ] Reaches ws v z
reachTrail ws v {z} m =
  subst (λ y -> Reaches ws y z) (sym (≡ᵛ-sound v seed seedHolds)) reaches
  where open Seeded (closureSeeded (v ≡ᵛ_) ws (∈ᵛ-complete ws) (listFinite ws) z m)

reachSeed : ∀[ v ∈ ws ] v ∈ reachSet ws v
reachSeed {ws} v mv =
  closureSeed (v ≡ᵛ_) ws (∈ᵛ-complete ws) (listFinite ws) mv (≡ᵛ-refl v)

reachClosed : (ws : Subgraph) (v : Node)
           -> Closed[ G ▷ ws ] (reachSet ws v)
reachClosed ws v = closureClosed (v ≡ᵛ_) ws (∈ᵛ-complete ws) (listFinite ws)

reachTrans : (ws : Subgraph) (v u w : Node)
          -> u ∈ reachSet ws v -> w ∈ reachSet ws u
          -> w ∈ reachSet ws v
reachTrans ws v u w mu mw =
  reachesEndIn (reachClosed ws v) mu (reachTrail ws u mw)


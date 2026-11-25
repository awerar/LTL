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

-- The implicit arguments the signatures below leave out: the endpoints and
-- visited list of a trail, and the pool a search recurses on.
-- So is the vertex list ws wherever a Reaches or closed-under hypothesis fixes
-- it; it stays explicit where it only occurs under a function, as in
-- reachSet ws v.

private variable
  u v w    : Node
  ws xs zs : List Node
  Pool     : Pred

------------------------------------------------------------------------
-- Out-neighbours

-- The out-neighbours of x inside ws.  For G = step P this is succs P ws x on
-- the nose.

outs : List Node -> Node -> List Node
outs ws x = filter (G x) ws

hasOut : List Node -> Node -> Bool
hasOut ws x = ¬ᵇ null (outs ws x)

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

record Reaches (ws : List Node) (v w : Node) : Set where
  constructor reachesBy
  field
    via     : List Node
    trail   : Trail v via w
    staysIn : via ⊆ ws

-- A set C closed under G inside ws keeps every trail inside ws that starts in
-- it: the trail lies in C, and so does its endpoint.

module _ {ws C : List Node} (cl : C closed-under G within ws) where

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

module _ (Seed : Pred) (ws : List Node) where

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
    ∈ᵛ-sound x acc
      (¬ᵇ-false (x ∈ᵛ acc)
                (¬ᵇ∧ᵇ-cancelˡ (wanted acc x) (¬ᵇ (x ∈ᵛ acc)) (cong ¬ᵇ_ s) w))

  -- A round adds the missing x, so x leaves the candidates still available
  -- and the pool with it.

  availRound : (acc : List Node) (x : Node)
            -> x ∈ ws -> x ∈ᵖ missing acc -> (ws ∖ acc) inside Pool
            -> (ws ∖ addRound acc) inside Pool ∩ (x ≢ᵛ_)
  availRound acc x m xMissing avail =
    inside-∩ (inside-⊆ (∖-antitone ws (λ z -> ∈-++⁺ʳ (filter (missing acc) ws) acc))
                       avail)
             (∖-apart ws (addRound acc)
                      (∈-++⁺ˡ (filter (missing acc) ws) acc
                              (∈-filter⁺ (missing acc) ws m xMissing)))

  growGo   : (acc : List Node) -> (ws ∖ acc) inside Pool
          -> Finiteᵛ Pool -> List Node
  growFind : (acc : List Node) -> (ws ∖ acc) inside Pool
          -> Finiteᵛ Pool -> AnyDecision (missing acc) ws -> List Node

  growGo acc avail fin = growFind acc avail fin (decideAny (missing acc) ws)

  growFind acc avail fin              (noneTrue f)             = acc
  growFind acc avail (everyPick next) (witness x m xMissing) =
    growGo (addRound acc) (availRound acc x m xMissing avail)
           (next x (avail x (∈-∖⁺ acc m (notInAcc acc x xMissing))))

  ------------------------------------------------------------------------
  -- Induction on the search.  A property P acc r of the starting accumulator
  -- and the result holds if it holds where the search stops (no vertex of ws
  -- is missing from acc, and r is acc) and survives a round.  The stopping
  -- condition and the invariants of the closure are its instances.

  growElim : (P : List Node -> List Node -> Set)
          -> ((acc : List Node) -> (∀ⁱ[ x ∈ ws ] x ∉ᵖ missing acc)
                -> P acc acc)
          -> ((acc r : List Node) -> P (addRound acc) r -> P acc r)
          -> (acc : List Node) (avail : (ws ∖ acc) inside Pool) (fin : Finiteᵛ Pool)
          -> P acc (growGo acc avail fin)
  growElimFind : (P : List Node -> List Node -> Set)
              -> ((acc : List Node) -> (∀ⁱ[ x ∈ ws ] x ∉ᵖ missing acc)
                    -> P acc acc)
              -> ((acc r : List Node) -> P (addRound acc) r -> P acc r)
              -> (acc : List Node) (avail : (ws ∖ acc) inside Pool) (fin : Finiteᵛ Pool)
                 (fr : AnyDecision (missing acc) ws)
              -> P acc (growFind acc avail fin fr)

  growElim P stop round acc avail fin =
    growElimFind P stop round acc avail fin (decideAny (missing acc) ws)

  growElimFind P stop round acc avail fin (noneTrue f) = stop acc f
  growElimFind P stop round acc avail (everyPick next)
               (witness x m xMissing) =
    round acc _
          (growElim P stop round (addRound acc)
                    (availRound acc x m xMissing avail)
                    (next x (avail x (∈-∖⁺ acc m (notInAcc acc x xMissing)))))

  -- An invariant of the accumulator that every round preserves holds of the
  -- result.

  growInv : (I : List Node -> Set)
         -> ((acc : List Node) -> I acc -> I (addRound acc))
         -> (acc : List Node) (avail : (ws ∖ acc) inside Pool) (fin : Finiteᵛ Pool)
         -> I acc -> I (growGo acc avail fin)
  growInv I round =
    growElim (λ acc r -> I acc -> I r) (λ acc f i -> i)
             (λ acc r h i -> h (round acc i))

  ------------------------------------------------------------------------
  -- The invariants: the accumulator lies in ws, and each member is reached
  -- from a seed.

  roundIn : (acc : List Node) -> acc ⊆ ws -> addRound acc ⊆ ws
  roundIn acc subset z mz =
    [ ∈-filter⁻ (missing acc) ws , subset z ]
      (∈-++⁻ (filter (missing acc) ws) acc mz)

-- z is reached inside ws from a seed: a member of ws satisfying Seed.

record Seeded (Seed : Pred) (ws : List Node) (z : Node) : Set where
  constructor seededBy
  field
    seed      : Node
    seedIn    : seed ∈ ws
    seedHolds : Seed seed ≡ true
    reaches   : Reaches ws seed z

-- Every vertex a round adds is seeded: it is a seed itself, or a successor of
-- a member of acc, whose trail grows by one step.

roundSeeded : (Seed : Pred) (ws acc : List Node)
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
                        (filter-prop (missing Seed ws acc) ws z∈new)

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
-- The closure itself, and its four properties.  subset and fin say which pool
-- the search recurses on: every vertex of ws is in it, and it is finite.

closure : (Seed : Pred) (ws : List Node) -> ws inside Pool -> Finiteᵛ Pool
       -> List Node
closure Seed ws subset fin =
  growGo Seed ws [] (λ z mz -> subset z (∖-⊆ ws [] z mz)) fin

module _ (Seed : Pred) (ws : List Node) {Pool : Pred} (subset : ws inside Pool)
         (fin : Finiteᵛ Pool) where

  private
    avail0 : (ws ∖ []) inside Pool
    avail0 z mz = subset z (∖-⊆ ws [] z mz)

    done : ∀ⁱ[ x ∈ ws ] x ∉ᵖ missing Seed ws (closure Seed ws subset fin)
    done = growElim Seed ws (λ acc r -> ∀ⁱ[ x ∈ ws ] x ∉ᵖ missing Seed ws r)
                    (λ acc f -> f) (λ acc r d -> d) [] avail0 fin

  closureIn : ∀[ z ∈ closure Seed ws subset fin ] z ∈ ws
  closureIn = growInv Seed ws (λ acc -> acc ⊆ ws) (roundIn Seed ws) [] avail0 fin
                      (λ z ())

  closureSeeded : ∀[ z ∈ closure Seed ws subset fin ] Seeded Seed ws z
  closureSeeded = growInv Seed ws (λ acc -> ∀[ z ∈ acc ] Seeded Seed ws z)
                          (roundSeeded Seed ws) [] avail0 fin (λ z ())

  closureSeed : {z : Node} -> z ∈ ws -> Seed z ≡ true -> z ∈ closure Seed ws subset fin
  closureSeed {z} mz e =
    wantedIn Seed ws (closure Seed ws subset fin) z (done mz)
      (∨ᵇ-introˡ (Seed z) (any (λ y -> G y z) (closure Seed ws subset fin)) e)

  closureClosed : closure Seed ws subset fin closed-under G within ws
  closureClosed mu {w} mw e =
    wantedIn Seed ws (closure Seed ws subset fin) w (done mw)
      (∨ᵇ-introʳ (Seed w) (any (λ y -> G y w) (closure Seed ws subset fin))
                 (any-intro (λ y -> G y w) (closure Seed ws subset fin) mu e))

------------------------------------------------------------------------
-- The reachable set: the closure of the single seed v, on listFinite ws.

reachSet : List Node -> Node -> List Node
reachSet ws v = closure (v ≡ᵛ_) ws (inside-∈ᵛ ws) (listFinite ws)

reachIn : (ws : List Node) (v : Node)
       -> ∀ⁱ[ z ∈ reachSet ws v ] z ∈ ws
reachIn ws v {z} = closureIn (v ≡ᵛ_) ws (inside-∈ᵛ ws) (listFinite ws) z

reachTrail : (ws : List Node) (v : Node)
          -> ∀ⁱ[ z ∈ reachSet ws v ] Reaches ws v z
reachTrail ws v {z} m =
  subst (λ y -> Reaches ws y z) (sym (≡ᵛ-sound v seed seedHolds)) reaches
  where open Seeded (closureSeeded (v ≡ᵛ_) ws (inside-∈ᵛ ws) (listFinite ws) z m)

reachSeed : (ws : List Node) (v : Node)
         -> v ∈ ws -> v ∈ reachSet ws v
reachSeed ws v mv =
  closureSeed (v ≡ᵛ_) ws (inside-∈ᵛ ws) (listFinite ws) mv (≡ᵛ-refl v)

reachClosed : (ws : List Node) (v : Node)
           -> reachSet ws v closed-under G within ws
reachClosed ws v = closureClosed (v ≡ᵛ_) ws (inside-∈ᵛ ws) (listFinite ws)

-- Completeness: the set is closed under G inside ws, so a trail inside ws
-- from a member ends in it.

reachComplete : (ws : List Node) (v : Node) -> v ∈ ws
             -> Reaches ws v w
             -> w ∈ reachSet ws v
reachComplete ws v mv = reachesEndIn (reachClosed ws v) (reachSeed ws v mv)

reachTrans : (ws : List Node) (v u w : Node)
          -> u ∈ reachSet ws v -> w ∈ reachSet ws u
          -> w ∈ reachSet ws v
reachTrans ws v u w mu mw =
  reachesEndIn (reachClosed ws v) mu (reachTrail ws u mw)


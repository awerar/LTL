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
-- it too.  closure takes its Bar as an argument, so that Ust can use the
-- guarded vecBar; reachSet takes listBar, which is blocked while the list is
-- a variable, so it needs no guard against normalisation blow-up.

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.DecEq using (DecEq)

module LTL.1-Lib.Graph {Node : Set} (eq : DecEq Node)
                       (G : Node -> Node -> Bool) where

-- Not re-exported: an importer gets this module's own names only, and takes
-- the set layer from wherever it already has it (LTL.5-States.Reach, at Val).

open import LTL.1-Lib.Sets
open import LTL.1-Lib.Bar
open import LTL.1-Lib.Nodes eq

-- The implicit arguments the signatures below leave out: the endpoints and
-- visited list of a trail, and the predicate of the Bar a search recurses on.
-- So is the vertex list ws wherever a Reaches or closed-under hypothesis fixes
-- it; it stays explicit where it only occurs under a function, as in
-- reachSet ws v.

private variable
  u v w    : Node
  ws xs zs : List Node
  E        : Pred

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
    via    : List Node
    trail  : Trail v via w
    inside : via ⊆ ws

-- A set C closed under G inside ws keeps every trail inside ws that starts in
-- it: the trail lies in C, and so does its endpoint.

module _ {ws C : List Node} (cl : C closed-under G within ws) where

  private
    trailInto : u ∈ C -> Trail u zs w -> zs ⊆ ws -> zs ⊆ C
    trailInto mu tNil        sb z ()
    trailInto mu (tCons e t) sb _ here      = cl mu (sb _ here) e
    trailInto mu (tCons e t) sb z (there k) =
      trailInto (cl mu (sb _ here) e) t (λ y m -> sb y (there m)) z k

    trailEndIn : u ∈ C -> Trail u zs w -> zs ⊆ ws -> w ∈ C
    trailEndIn mu tNil        sb = mu
    trailEndIn mu (tCons e t) sb =
      trailEndIn (cl mu (sb _ here) e) t (λ y m -> sb y (there m))

  reachesInto : u ∈ C -> Reaches ws u w -> Reaches C u w
  reachesInto mu (reachesBy zs t sb) = reachesBy zs t (trailInto mu t sb)

  reachesEndIn : u ∈ C -> Reaches ws u w -> w ∈ C
  reachesEndIn mu (reachesBy zs t sb) = trailEndIn mu t sb

------------------------------------------------------------------------
-- The growing search.  closure S ws is the least part of ws that contains
-- every member satisfying the seed test S and is closed under G-successors
-- inside ws.  A round adds every vertex of ws that is wanted -- satisfies S,
-- or is a G-successor of something already in acc -- and is not there yet;
-- when a round adds nothing, acc contains every wanted vertex, which is
-- completeness.  Both the reachable set below (S = v ≡ᵛ_) and Ust of
-- LTL.5-States.Closure (S = "contains P") are instances.

module _ (S : Pred) (ws : List Node) where

  wanted : List Node -> Node -> Bool
  wanted acc x = S x ∨ᵇ any (λ y -> G y x) acc

  missing : List Node -> Node -> Bool
  missing acc x = wanted acc x ∧ᵇ ¬ᵇ (x ∈ᵛ acc)

  -- x is settled when it needs no adding: it is not wanted, or acc has it.
  -- A round looks for an unsettled x with decideAll.

  settled : List Node -> Node -> Bool
  settled acc x = ¬ᵇ missing acc x

  addRound : List Node -> List Node
  addRound acc = filter (missing acc) ws ++ acc

  notInAcc : (acc : List Node) (x : Node)
          -> settled acc x ≡ false -> x ∈ᵛ acc ≡ false
  notInAcc acc x q =
    ¬ᵇ-true (x ∈ᵛ acc)
            (∧ᵇ-trueʳ (wanted acc x) (¬ᵇ (x ∈ᵛ acc))
                      (¬ᵇ-false (missing acc x) q))

  -- A settled vertex that is wanted is already in.

  settledIn : (acc : List Node) (x : Node)
           -> settled acc x ≡ true -> wanted acc x ≡ true -> x ∈ acc
  settledIn acc x s w =
    ∈ᵛ-sound x acc
      (¬ᵇ-false (x ∈ᵛ acc) (¬ᵇ∧ᵇ-cancelˡ (wanted acc x) (¬ᵇ (x ∈ᵛ acc)) s w))

  -- A round adds the unsettled x, so x leaves the candidates still available
  -- and the Bar's predicate with it.

  availRound : (acc : List Node) (x : Node)
            -> x ∈ ws -> settled acc x ≡ false -> E holds-on ws except acc
            -> (λ z -> E z ∧ᵇ (x ≢ᵛ z)) holds-on ws except addRound acc
  availRound {E} acc x m q av {z} mz e =
    ∧ᵇ-intro (E z) (x ≢ᵛ z) (av mz outAcc) (cong ¬ᵇ_ outX)
    where
      outAcc : z ∈ᵛ acc ≡ false
      outAcc = refuteTrue (z ∈ᵛ acc) λ eb ->
        ∈ᵛ-false z (addRound acc) e
          (∈-++⁺ʳ (filter (missing acc) ws) acc (∈ᵛ-sound z acc eb))

      outX : x ≡ᵛ z ≡ false
      outX = refuteTrue (x ≡ᵛ z) λ eb ->
        ∈ᵛ-false z (addRound acc) e
          (subst (λ y -> y ∈ addRound acc) (≡ᵛ-sound x z eb)
                 (∈-++⁺ˡ (filter (missing acc) ws) acc
                         (∈-filter⁺ (missing acc) ws m
                                    (¬ᵇ-false (missing acc x) q))))

  growGo   : (acc : List Node) -> E holds-on ws except acc
          -> IFin E -> List Node
  growFind : (acc : List Node) -> E holds-on ws except acc
          -> IFin E -> AllDecision (settled acc) ws -> List Node

  growGo acc av bar = growFind acc av bar (decideAll (settled acc) ws)

  growFind acc av bar      (allTrue f)            = acc
  growFind acc av (cBar h) (counterexample x m q) =
    growGo (addRound acc) (availRound acc x m q av)
           (h x (av m (notInAcc acc x q)))

  ------------------------------------------------------------------------
  -- Two facts about the search, each by its recursion: an invariant of the
  -- accumulator that every round preserves holds of the result, and every
  -- vertex of ws is settled against the result (the stopping condition).

  growInv   : (I : List Node -> Set)
           -> ((acc : List Node) -> I acc -> I (addRound acc))
           -> (acc : List Node) (av : E holds-on ws except acc) (bar : IFin E)
           -> I acc -> I (growGo acc av bar)
  growInvFind : (I : List Node -> Set)
             -> ((acc : List Node) -> I acc -> I (addRound acc))
             -> (acc : List Node) (av : E holds-on ws except acc) (bar : IFin E)
                (fr : AllDecision (settled acc) ws)
             -> I acc -> I (growFind acc av bar fr)

  growInv I round acc av bar =
    growInvFind I round acc av bar (decideAll (settled acc) ws)

  growInvFind I round acc av bar      (allTrue f)            i = i
  growInvFind I round acc av (cBar h) (counterexample x m q) i =
    growInv I round (addRound acc) _ (h x (av m (notInAcc acc x q)))
            (round acc i)

  growDone     : (acc : List Node) (av : E holds-on ws except acc) (bar : IFin E)
              -> ∀ⁱ[ x ∈ ws ] settled (growGo acc av bar) x ≡ true
  growDoneFind : (acc : List Node) (av : E holds-on ws except acc) (bar : IFin E)
                 (fr : AllDecision (settled acc) ws)
              -> ∀ⁱ[ x ∈ ws ] settled (growFind acc av bar fr) x ≡ true

  growDone acc av bar = growDoneFind acc av bar (decideAll (settled acc) ws)

  growDoneFind acc av bar      (allTrue f)            = f
  growDoneFind acc av (cBar h) (counterexample x m q) =
    growDone (addRound acc) _ (h x (av m (notInAcc acc x q)))

  ------------------------------------------------------------------------
  -- The invariants: the accumulator lies in ws, and each member is reached
  -- from a seed.

  roundIn : (acc : List Node) -> acc ⊆ ws -> addRound acc ⊆ ws
  roundIn acc sb z mz =
    [ ∈-filter⁻ (missing acc) ws , sb z ]
      (∈-++⁻ (filter (missing acc) ws) acc mz)

-- z is reached inside ws from a seed: a member of ws satisfying S.

record Seeded (S : Pred) (ws : List Node) (z : Node) : Set where
  constructor seededBy
  field
    seed      : Node
    seedIn    : seed ∈ ws
    seedHolds : S seed ≡ true
    reaches   : Reaches ws seed z

-- Every vertex a round adds is seeded: it is a seed itself, or a successor of
-- a member of acc, whose trail grows by one step.

roundSeeded : (S : Pred) (ws acc : List Node)
           -> (∀[ z ∈ acc ] Seeded S ws z)
           -> ∀[ z ∈ addRound S ws acc ] Seeded S ws z
roundSeeded S ws acc sd z m =
  [ fromNew , sd z ] (∈-++⁻ (filter (missing S ws acc) ws) acc m)
  where
    fromNew : z ∈ filter (missing S ws acc) ws -> Seeded S ws z
    fromNew m1 = [ isSeed , viaY ] (∨ᵇ-true (S z) (any (λ y -> G y z) acc) want)
      where
        mzw : z ∈ ws
        mzw = ∈-filter⁻ (missing S ws acc) ws m1

        want : wanted S ws acc z ≡ true
        want = ∧ᵇ-trueˡ (wanted S ws acc z) (¬ᵇ (z ∈ᵛ acc))
                        (filter-prop (missing S ws acc) ws m1)

        isSeed : S z ≡ true -> Seeded S ws z
        isSeed e = seededBy z mzw e (reachesBy [] tNil (λ _ ()))

        viaY : any (λ y -> G y z) acc ≡ true -> Seeded S ws z
        viaY ea = pick (any-true (λ y -> G y z) acc ea)
          where
            pick : (∃[ y ∈ acc ] G y z ≡ true) -> Seeded S ws z
            pick (y , my , gy) =
              seededBy seed seedIn seedHolds
                       (reachesBy (via ++ z ∷ [])
                                  (trailApp trail (tCons gy tNil))
                                  (++-⊆ via inside (∷-⊆ mzw (λ _ ()))))
              where
                open Seeded (sd y my)
                open Reaches reaches

------------------------------------------------------------------------
-- The closure itself, and its four properties.  sb and bar say which Bar the
-- search recurses on: every vertex of ws satisfies the Bar's predicate E.

closure : (S : Pred) (ws : List Node) -> AllSat E ws -> IFin E
       -> List Node
closure S ws sb bar = growGo S ws [] (λ mz _ -> sb _ mz) bar

module _ (S : Pred) (ws : List Node) {E : Pred} (sb : AllSat E ws)
         (bar : IFin E) where

  private
    av0 : E holds-on ws except []
    av0 mz _ = sb _ mz

    done : ∀ⁱ[ x ∈ ws ] settled S ws (closure S ws sb bar) x ≡ true
    done = growDone S ws [] av0 bar

  closureIn : ∀[ z ∈ closure S ws sb bar ] z ∈ ws
  closureIn = growInv S ws (λ acc -> acc ⊆ ws) (roundIn S ws) [] av0 bar
                      (λ z ())

  closureSeeded : ∀[ z ∈ closure S ws sb bar ] Seeded S ws z
  closureSeeded = growInv S ws (λ acc -> ∀[ z ∈ acc ] Seeded S ws z)
                          (roundSeeded S ws) [] av0 bar (λ z ())

  closureSeed : {z : Node} -> z ∈ ws -> S z ≡ true -> z ∈ closure S ws sb bar
  closureSeed {z} mz e =
    settledIn S ws (closure S ws sb bar) z (done mz)
      (∨ᵇ-introˡ (S z) (any (λ y -> G y z) (closure S ws sb bar)) e)

  closureClosed : closure S ws sb bar closed-under G within ws
  closureClosed mu {w} mw e =
    settledIn S ws (closure S ws sb bar) w (done mw)
      (∨ᵇ-introʳ (S w) (any (λ y -> G y w) (closure S ws sb bar))
                 (any-intro (λ y -> G y w) (closure S ws sb bar) mu e))

------------------------------------------------------------------------
-- The reachable set: the closure of the single seed v, on the Bar listBar ws.

reachSet : List Node -> Node -> List Node
reachSet ws v = closure (v ≡ᵛ_) ws (AllSat-∈ᵛ ws) (listBar ws)

reachIn : (ws : List Node) (v : Node)
       -> ∀ⁱ[ z ∈ reachSet ws v ] z ∈ ws
reachIn ws v {z} = closureIn (v ≡ᵛ_) ws (AllSat-∈ᵛ ws) (listBar ws) z

reachTrail : (ws : List Node) (v : Node)
          -> ∀ⁱ[ z ∈ reachSet ws v ] Reaches ws v z
reachTrail ws v {z} m =
  subst (λ y -> Reaches ws y z) (sym (≡ᵛ-sound v seed seedHolds)) reaches
  where open Seeded (closureSeeded (v ≡ᵛ_) ws (AllSat-∈ᵛ ws) (listBar ws) z m)

reachSeed : (ws : List Node) (v : Node)
         -> v ∈ ws -> v ∈ reachSet ws v
reachSeed ws v mv =
  closureSeed (v ≡ᵛ_) ws (AllSat-∈ᵛ ws) (listBar ws) mv (≡ᵛ-refl v)

reachClosed : (ws : List Node) (v : Node)
           -> reachSet ws v closed-under G within ws
reachClosed ws v = closureClosed (v ≡ᵛ_) ws (AllSat-∈ᵛ ws) (listBar ws)

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


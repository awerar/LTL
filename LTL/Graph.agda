{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Graph -- G37 of PHASE11-PLAN.md: the finite fair-graph certificate
-- theorem, and nothing else.
--
--   Finite fair-graph certificate theorem.
--   Given a finite graph, finitely many decidable fairness predicates F_i, and
--   a vertex v, compute either
--     (a) a lasso from v whose cycle meets every relevant F_i, or
--     (b) a well-founded certificate that every recurrent component reachable
--         from v misses some F_i.
--
-- That is  fairGraph , at the bottom of the file.  (a) is FairLoop, (b) is Cert,
-- and certAll is the induction principle Cert exists to supply.
--
-- THERE IS NO LOGIC IN THIS MODULE.  No Formula occurs anywhere in it; the
-- graph is a list of vertices  vs : List Val  with an edge test
-- G : Val -> Val -> Bool  (abbreviated Edges), and the fairness sets are
-- boolean predicates  fs : List (Val -> Bool)  (abbreviated List Pred).  Val is
-- used only because LTL.Bar's inductive finiteness is stated for it; nothing
-- here reads a bit of a valuation.  The repeated hypotheses have names from
-- LTL.Sets and LTL.Bar (Closed, NoneSat, HoldsOutside, Avail), and each run of
-- lemmas that shares its leading arguments sits in a  module _  over them.
--
-- Where "relevant" went.  The informal statement quantifies over the fairness
-- sets RELEVANT in a component, which is well defined only because the pending
-- eventuality is uniform on a component (walkPersist).  Here relevance is
-- absorbed into the predicate: the caller passes, for the eventuality  □ A ,
-- the predicate "□ A is not pending, or A fails", so a component in which the
-- eventuality is not pending meets it for free and a component in which it is
-- pending meets it exactly by fulfilling it.  The graph layer therefore knows
-- only "C meets every f in fs", and the LTL reading of fs is G38 and G39.
--
-- The four things PHASE11-PLAN.md warns about, and what happened to each.
--
-- 1. Mutual reachability is reachability COMPLETELY, which is what LTL/Reach.agda
--    abandoned.  It is paid the way G30 paid: reachGo is a GROWING search whose
--    stopping condition is that a round adds nothing -- closeGo of LTL.Closure
--    with the seed changed from "contains P" to "is v" -- and completeness comes
--    from the stopping condition (reachSeed, reachClosed) rather than from a
--    bound.  There is no fuel and no claim that  length vs  rounds suffice.
--
-- 2. No component objects and no quotients.  A component is a representative
--    plus filter:  sccOf vs G r = the w in reach(r) that reach r back.  The
--    condensation is never built; "r's component is terminal" is the boolean
--    isTerminal, and a condensation edge is followed by moving the
--    representative.
--
-- 3. No rank function and no topological sort.  graphGo is a REMOVING iteration
--    -- pick a sink or a terminal component, refute it, delete it -- so barRec
--    covers termination.  What needed proof is only that a non-empty graph has
--    a terminal component, and that is findTerm: follow condensation edges,
--    which is a third Bar search, terminating because the reachable set of the
--    new representative avoids every representative already visited.  The
--    invariant that says so is a single hypothesis, not a history list.
--
-- 4. The guardBar heap trap of section 4g.  Every Bar here comes from listBar,
--    i.e. from barOfList, which recurses on  length xs  and is blocked while
--    the list is a variable; guardBar is not used at all, so the 2^k unfolding
--    cannot happen.  Terminal and Block do mention reachSet and isTerminal in
--    their constructor types -- and Agda normalises those -- but reachGo is
--    blocked at findFalse on a variable list, so nothing expands.  A growing
--    search on vectors would have needed the guard; a search over a list in
--    hand does not.
--
-- The two answers are proved EXCLUSIVE, and that is the second half of the file.
-- certNoCirc: a Cert for ws forbids a fair circuit inside ws; fairNoLoop and
-- fairComplete carry it to the top, so the negative answer is a decision and not
-- merely an output.  This is the lecture's "key insight" done finitely.  The
-- lecture says an INFINITE path eventually stays inside one SCC, which needs
-- coinduction and a classical step; what is actually needed is the same thing
-- about a FINITE cycle, and that is two inductions on a trail --
--
--   a vertex on a cycle has a successor,  so a sink lies on no cycle;
--   any vertex of a cycle reaches any other,  so a cycle that enters a
--     successor-closed block never leaves it.
--
-- So no infinite path is constructed, nothing is coinductive, and no pigeonhole
-- is used, which are the same three absences section 4f claims for the rest of
-- the development.  Both sides are inhabited and neither theorem is vacuous:
-- cycle_QS exhibits a Circuit and cert_P a Cert, at the bottom.
--
-- What this still does NOT do.  It decides nothing about formulas and builds no
-- derivation; the LTL reading of (b) is G39, where certAll's two hypotheses are
-- extractR1's and extractR2's on the nose -- null (outs ws G x) ≡ true IS
-- r1 P ws x ≡ true definitionally, and the block case supplies the closed set
-- and the unfulfilled eventuality that (Ind) needs.  Nor does it claim to be
-- cheaper than gfpW.
--
-- It is, in short, the factoring the current development has nowhere: Gfp, Elim,
-- Trace, Round and Lasso all mention formulas, and this file does not.

module LTL.Graph where

open import LTL.Bar public

------------------------------------------------------------------------
-- Glue

appNotNull : {A : Set} (xs ys : List A) -> null xs ≡ false
          -> null (xs ++ ys) ≡ false
appNotNull []       ys ()
appNotNull (x ∷ xs) ys e = refl

null_notMem : (ws : List Val) (z : Val) -> null ws ≡ true -> z ∈ᵛ ws ≡ false
null_notMem []       z e = refl
null_notMem (w ∷ ws) z ()

-- The out-neighbours of x inside ws.  For G = step P this is succs P ws x on
-- the nose, which is what G39 needs of it.

outs : List Val -> Edges -> Val -> List Val
outs ws G x = filter (G x) ws

hasOut : List Val -> Edges -> Val -> Bool
hasOut ws G x = ¬ᵇ null (outs ws G x)

------------------------------------------------------------------------
-- Trails: finite paths inside ws, carrying the list of vertices visited and
-- indexed by the endpoint.  LTL.Walk with  step P  replaced by G, and for the
-- same reason -- indexing by the endpoint keeps every concatenation free of
-- equational bookkeeping.  Reflexive-transitive; a cycle is a trail from r to r
-- whose list is non-empty, and that is the only place non-emptiness is needed.

data Trail (ws : List Val) (G : Edges) : Val -> List Val -> Val -> Set where
  tNil  : {v : Val} -> Trail ws G v [] v
  tCons : {v x : Val} {zs : List Val} {w : Val}
       -> x ∈ ws -> G v x ≡ true -> Trail ws G x zs w
       -> Trail ws G v (x ∷ zs) w

module _ (ws : List Val) (G : Edges) where

  trailApp : {u v w : Val} {xs zs : List Val}
          -> Trail ws G u xs v -> Trail ws G v zs w -> Trail ws G u (xs ++ zs) w
  trailApp tNil           t2 = t2
  trailApp (tCons m e t1) t2 = tCons m e (trailApp t1 t2)

  trailEnd : {v : Val} {zs : List Val} {w : Val}
          -> Trail ws G v zs w -> w ∈ v ∷ zs
  trailEnd tNil          = here
  trailEnd (tCons m e t) = there (trailEnd t)

  -- A trail that takes at least one step ends at a vertex it visits.

  trailLast : {v : Val} {zs : List Val} {w : Val}
           -> Trail ws G v zs w -> null zs ≡ false -> w ∈ zs
  trailLast tNil          ()
  trailLast (tCons m e t) nn = trailEnd t

  trailIn : {v : Val} {zs : List Val} {w : Val}
         -> Trail ws G v zs w -> {z : Val} -> z ∈ zs -> z ∈ ws
  trailIn tNil          ()
  trailIn (tCons m e t) here      = m
  trailIn (tCons m e t) (there k) = trailIn t k

trailMono : (ws vs : List Val) (G : Edges)
         -> ws ⊆ vs
         -> {v : Val} {zs : List Val} {w : Val}
         -> Trail ws G v zs w -> Trail vs G v zs w
trailMono ws vs G sb tNil                  = tNil
trailMono ws vs G sb (tCons {x = x} m e t) =
  tCons (sb x m) e (trailMono ws vs G sb t)

data Reaches (ws : List Val) (G : Edges) (v w : Val) : Set where
  reachesBy : (zs : List Val) -> Trail ws G v zs w -> Reaches ws G v w

------------------------------------------------------------------------
-- The reachable set, as a growing search.
--
-- closeGo of LTL.Closure with two changes: the seed is "is v" instead of
-- "contains P", and the ambient candidate list is the vertex list rather than
-- StCand P.  A round adds every vertex of ws that is wanted -- is v, or is a
-- G-successor of something already in acc -- and is not there yet; when a round
-- adds nothing, acc contains every wanted vertex, and THAT is completeness.
-- No round is counted.
--
-- reachWanted, reachMissing, reachSettled, reachRound, ... are the wanted,
-- missing, settled, addAll, ... of LTL.Closure, for reachability in ws.

reachWanted : Edges -> Val -> List Val -> Val -> Bool
reachWanted G v acc x = (v ≡ᵛ x) ∨ᵇ any (λ y -> G y x) acc

reachMissing : Edges -> Val -> List Val -> Val -> Bool
reachMissing G v acc x = reachWanted G v acc x ∧ᵇ ¬ᵇ (x ∈ᵛ acc)

reachSettled : Edges -> Val -> List Val -> Val -> Bool
reachSettled G v acc x = ¬ᵇ reachMissing G v acc x

reachRound : List Val -> Edges -> Val -> List Val -> List Val
reachRound ws G v acc = filter (reachMissing G v acc) ws ++ acc

reachMissingOf : (G : Edges) (v : Val) (acc : List Val) (x : Val)
              -> reachSettled G v acc x ≡ false -> reachMissing G v acc x ≡ true
reachMissingOf G v acc x q = notFalse (reachMissing G v acc x) q

reachNotInAcc : (G : Edges) (v : Val) (acc : List Val) (x : Val)
             -> reachSettled G v acc x ≡ false -> x ∈ᵛ acc ≡ false
reachNotInAcc G v acc x q =
  notTrue (x ∈ᵛ acc)
          (andTrueR (reachWanted G v acc x) (¬ᵇ (x ∈ᵛ acc)) (reachMissingOf G v acc x q))

module _ (ws : List Val) (G : Edges) (v : Val) where

  reachInRound : (acc : List Val) (x : Val)
              -> x ∈ ws -> reachSettled G v acc x ≡ false -> x ∈ reachRound ws G v acc
  reachInRound acc x m q =
    memAppL (filter (reachMissing G v acc) ws) acc
            (filter_true (reachMissing G v acc) ws m (reachMissingOf G v acc x q))

  reachGo   : {E : Pred} (acc : List Val) -> Avail E ws acc -> IFin E -> List Val
  reachFind : {E : Pred} (acc : List Val) -> Avail E ws acc
           -> IFin E -> FindResult (reachSettled G v acc) ws -> List Val

  reachGo acc av bar = reachFind acc av bar (findFalse (reachSettled G v acc) ws)

  reachFind acc av bar          (allTrue f)   = acc
  reachFind {E} acc av (cBar h) (found x m q) =
    reachGo (reachRound ws G v acc) av' (h x (av x m (reachNotInAcc G v acc x q)))
    where
      av' : Avail (λ z -> E z ∧ᵇ (x ≢ᵛ z)) ws (reachRound ws G v acc)
      av' z mz e =
        andIntro (E z) (x ≢ᵛ z)
                 (av z mz (outAcc (z ∈ᵛ acc) refl))
                 (cong ¬ᵇ_ (outX (x ≡ᵛ z) refl))
        where
          outAcc : (b : Bool) -> z ∈ᵛ acc ≡ b -> z ∈ᵛ acc ≡ false
          outAcc false eb = eb
          outAcc true  eb =
            emptyElim (∈ᵛ-false z (reachRound ws G v acc) e
                        (memAppR (filter (reachMissing G v acc) ws) acc
                                 (∈ᵛ-sound z acc eb)))

          outX : (b : Bool) -> x ≡ᵛ z ≡ b -> x ≡ᵛ z ≡ false
          outX false eb = eb
          outX true  eb =
            emptyElim (∈ᵛ-false z (reachRound ws G v acc) e
                        (subst (λ y -> y ∈ reachRound ws G v acc) (≡ᵛ-sound x z eb)
                               (reachInRound acc x m q)))

  ------------------------------------------------------------------------
  -- Its four properties, each by the same recursion.
  --
  -- The result lies in ws; every member of it is reached by a trail; v is in it;
  -- and it is closed under G-successors inside ws.  The last two are the stopping
  -- condition read off, and together they are completeness.

  reachGoIn   : {E : Pred} (acc : List Val) (av : Avail E ws acc) (bar : IFin E)
             -> acc ⊆ ws
             -> {z : Val} -> z ∈ reachGo acc av bar -> z ∈ ws
  reachFindIn : {E : Pred} (acc : List Val) (av : Avail E ws acc)
                (bar : IFin E) (fr : FindResult (reachSettled G v acc) ws)
             -> acc ⊆ ws
             -> {z : Val} -> z ∈ reachFind acc av bar fr -> z ∈ ws

  reachGoIn acc av bar = reachFindIn acc av bar (findFalse (reachSettled G v acc) ws)

  reachFindIn acc av bar          (allTrue f)      sb {z} m = sb z m
  reachFindIn acc av (cBar h) (found x mx q) sb       m =
    reachGoIn (reachRound ws G v acc) _ (h x (av x mx (reachNotInAcc G v acc x q))) sb' m
    where
      sb' : reachRound ws G v acc ⊆ ws
      sb' z mz = sumElim (λ m1 -> filter_sub (reachMissing G v acc) ws m1)
                         (λ m2 -> sb z m2)
                         (memAppCase (filter (reachMissing G v acc) ws) acc mz)

  -- Every vertex a round adds is reached by a trail: it is v, or it is a
  -- successor of a member of acc, and then the trail of that member grows by one
  -- step.

  addReaches : (acc : List Val)
            -> ((z : Val) -> z ∈ acc -> Reaches ws G v z)
            -> (z : Val) -> z ∈ reachRound ws G v acc -> Reaches ws G v z
  addReaches acc rc z m =
    sumElim fromNew (λ m2 -> rc z m2)
            (memAppCase (filter (reachMissing G v acc) ws) acc m)
    where
      fromNew : z ∈ filter (reachMissing G v acc) ws -> Reaches ws G v z
      fromNew m1 = sumElim isV viaY (orTrue (v ≡ᵛ z) (any (λ y -> G y z) acc) want)
        where
          mzw : z ∈ ws
          mzw = filter_sub (reachMissing G v acc) ws m1

          want : reachWanted G v acc z ≡ true
          want = andTrueL (reachWanted G v acc z) (¬ᵇ (z ∈ᵛ acc))
                          (filter_prop (reachMissing G v acc) ws m1)

          isV : v ≡ᵛ z ≡ true -> Reaches ws G v z
          isV ev = subst (λ y -> Reaches ws G v y) (≡ᵛ-sound v z ev)
                         (reachesBy [] tNil)

          viaY : any (λ y -> G y z) acc ≡ true -> Reaches ws G v z
          viaY ea = pick (any_true (λ y -> G y z) acc ea)
            where
              pick : (Σ[ y ∈ Val ] y ∈ acc × G y z ≡ true)
                  -> Reaches ws G v z
              pick (y , my , gy) = ext (rc y my)
                where
                  ext : Reaches ws G v y -> Reaches ws G v z
                  ext (reachesBy zs t) =
                    reachesBy (zs ++ z ∷ []) (trailApp ws G t (tCons mzw gy tNil))

  reachGoTrail   : {E : Pred} (acc : List Val) (av : Avail E ws acc) (bar : IFin E)
                -> ((z : Val) -> z ∈ acc -> Reaches ws G v z)
                -> {z : Val} -> z ∈ reachGo acc av bar -> Reaches ws G v z
  reachFindTrail : {E : Pred} (acc : List Val) (av : Avail E ws acc)
                   (bar : IFin E) (fr : FindResult (reachSettled G v acc) ws)
                -> ((z : Val) -> z ∈ acc -> Reaches ws G v z)
                -> {z : Val} -> z ∈ reachFind acc av bar fr -> Reaches ws G v z

  reachGoTrail acc av bar =
    reachFindTrail acc av bar (findFalse (reachSettled G v acc) ws)

  reachFindTrail acc av bar          (allTrue f)      rc {z} m = rc z m
  reachFindTrail acc av (cBar h) (found x mx q) rc       m =
    reachGoTrail (reachRound ws G v acc) _ (h x (av x mx (reachNotInAcc G v acc x q)))
                 (addReaches acc rc) m

  reachGoSeed   : {E : Pred} (acc : List Val) (av : Avail E ws acc) (bar : IFin E)
               -> v ∈ ws -> v ∈ reachGo acc av bar
  reachFindSeed : {E : Pred} (acc : List Val) (av : Avail E ws acc)
                  (bar : IFin E) (fr : FindResult (reachSettled G v acc) ws)
               -> v ∈ ws -> v ∈ reachFind acc av bar fr

  reachGoSeed acc av bar =
    reachFindSeed acc av bar (findFalse (reachSettled G v acc) ws)

  reachFindSeed acc av bar          (allTrue f)      mv =
    ∈ᵛ-sound v acc
      (notFalse (v ∈ᵛ acc)
                (nandTrueL (reachWanted G v acc v) (¬ᵇ (v ∈ᵛ acc)) (f mv)
                           (orL (v ≡ᵛ v) (any (λ y -> G y v) acc) (≡ᵛ-refl v))))
  reachFindSeed acc av (cBar h) (found x mx q) mv =
    reachGoSeed (reachRound ws G v acc) _ (h x (av x mx (reachNotInAcc G v acc x q))) mv

  reachGoClosed   : {E : Pred} (acc : List Val) (av : Avail E ws acc)
                    (bar : IFin E) {u w : Val}
                 -> u ∈ reachGo acc av bar -> w ∈ ws -> G u w ≡ true
                 -> w ∈ reachGo acc av bar
  reachFindClosed : {E : Pred} (acc : List Val) (av : Avail E ws acc)
                    (bar : IFin E) (fr : FindResult (reachSettled G v acc) ws) {u w : Val}
                 -> u ∈ reachFind acc av bar fr -> w ∈ ws -> G u w ≡ true
                 -> w ∈ reachFind acc av bar fr

  reachGoClosed acc av bar =
    reachFindClosed acc av bar (findFalse (reachSettled G v acc) ws)

  reachFindClosed acc av bar      (allTrue f)      {u} {w} mu mw st =
    ∈ᵛ-sound w acc
      (notFalse (w ∈ᵛ acc)
                (nandTrueL (reachWanted G v acc w) (¬ᵇ (w ∈ᵛ acc)) (f mw)
                           (orR (v ≡ᵛ w) (any (λ y -> G y w) acc)
                                (any_intro (λ y -> G y w) acc mu st))))
  reachFindClosed acc av (cBar h) (found x mx q) mu mw st =
    reachGoClosed (reachRound ws G v acc) _ (h x (av x mx (reachNotInAcc G v acc x q)))
                  mu mw st

------------------------------------------------------------------------
-- The reachable set itself

reachAvInit : (ws : List Val) (z : Val) -> z ∈ ws -> z ∈ᵛ [] ≡ false
           -> z ∈ᵛ ws ≡ true
reachAvInit ws z mz e = ∈ᵛ-complete z ws mz

emptyAccIn : (ws : List Val) (z : Val) -> z ∈ [] {A = Val} -> z ∈ ws
emptyAccIn ws z ()

emptyAccReaches : (ws : List Val) (G : Edges) (v : Val) (z : Val)
               -> z ∈ [] {A = Val} -> Reaches ws G v z
emptyAccReaches ws G v z ()

reachSet : List Val -> Edges -> Val -> List Val
reachSet ws G v = reachGo ws G v [] (reachAvInit ws) (listBar ws)

reachIn : (ws : List Val) (G : Edges) (v : Val) {z : Val}
       -> z ∈ reachSet ws G v -> z ∈ ws
reachIn ws G v = reachGoIn ws G v [] (reachAvInit ws) (listBar ws) (emptyAccIn ws)

reachTrail : (ws : List Val) (G : Edges) (v : Val) {z : Val}
          -> z ∈ reachSet ws G v -> Reaches ws G v z
reachTrail ws G v = reachGoTrail ws G v [] (reachAvInit ws) (listBar ws) (emptyAccReaches ws G v)

reachSeed : (ws : List Val) (G : Edges) (v : Val)
         -> v ∈ ws -> v ∈ reachSet ws G v
reachSeed ws G v = reachGoSeed ws G v [] (reachAvInit ws) (listBar ws)

reachClosed : (ws : List Val) (G : Edges) (v : Val) {u w : Val}
           -> u ∈ reachSet ws G v -> w ∈ ws -> G u w ≡ true
           -> w ∈ reachSet ws G v
reachClosed ws G v = reachGoClosed ws G v [] (reachAvInit ws) (listBar ws)

-- Completeness: a trail from a member of the set stays in the set.  This is the
-- half that would have needed the pigeonhole if the search had been run for a
-- fixed number of rounds; here it is an induction along the trail against the
-- stopping condition.

reachTrailIn : (ws : List Val) (G : Edges) (v : Val)
               {u : Val} {zs : List Val} {w : Val}
            -> u ∈ reachSet ws G v -> Trail ws G u zs w -> w ∈ reachSet ws G v
reachTrailIn ws G v mu tNil                   = mu
reachTrailIn ws G v mu (tCons {x = x} mx e t) =
  reachTrailIn ws G v (reachClosed ws G v mu mx e) t

reachComplete : (ws : List Val) (G : Edges) (v : Val) -> v ∈ ws
             -> {zs : List Val} {w : Val} -> Trail ws G v zs w
             -> w ∈ reachSet ws G v
reachComplete ws G v mv t = reachTrailIn ws G v (reachSeed ws G v mv) t

reachTrans : (ws : List Val) (G : Edges) (v u w : Val)
          -> u ∈ reachSet ws G v -> w ∈ reachSet ws G u
          -> w ∈ reachSet ws G v
reachTrans ws G v u w mu mw = onR (reachTrail ws G u mw)
  where
    onR : Reaches ws G u w -> w ∈ reachSet ws G v
    onR (reachesBy zs t) = reachTrailIn ws G v mu t

------------------------------------------------------------------------
-- Components, without component objects.
--
-- sccOf ws G r is the strongly connected component of r: the vertices r reaches
-- that reach r back.  It is a filter of a list, nothing more; there is no
-- quotient, no set of sets, and no equality of components anywhere below.

sccOf : List Val -> Edges -> Val -> List Val
sccOf ws G r = filter (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r)

sccReach : (ws : List Val) (G : Edges) (r : Val) (w : Val)
        -> w ∈ sccOf ws G r -> w ∈ reachSet ws G r
sccReach ws G r w m = filter_sub (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) m

sccIn : (ws : List Val) (G : Edges) (r : Val) (w : Val)
     -> w ∈ sccOf ws G r -> w ∈ ws
sccIn ws G r w m = reachIn ws G r (sccReach ws G r w m)

sccTo : (ws : List Val) (G : Edges) (r : Val) (w : Val)
     -> w ∈ sccOf ws G r -> Reaches ws G r w
sccTo ws G r w m = reachTrail ws G r (sccReach ws G r w m)

sccFrom : (ws : List Val) (G : Edges) (r : Val) (w : Val)
       -> w ∈ sccOf ws G r -> Reaches ws G w r
sccFrom ws G r w m =
  reachTrail ws G w
    (∈ᵛ-sound r (reachSet ws G w)
      (filter_prop (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) m))

sccRep : (ws : List Val) (G : Edges) (r : Val)
      -> r ∈ ws -> r ∈ sccOf ws G r
sccRep ws G r mr =
  filter_true (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) (reachSeed ws G r mr)
              (∈ᵛ-complete r (reachSet ws G r) (reachSeed ws G r mr))

------------------------------------------------------------------------
-- Terminal components.
--
-- r's component is terminal when everything r reaches reaches r back, i.e. when
-- the reachable set of r IS its component.  That is one boolean, and it is the
-- only thing said about the condensation: no edge of it is ever built.

isTerminal : List Val -> Edges -> Val -> Bool
isTerminal ws G r = all (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r)

termScc : (ws : List Val) (G : Edges) (r : Val)
       -> isTerminal ws G r ≡ true
       -> {w : Val} -> w ∈ reachSet ws G r -> w ∈ sccOf ws G r
termScc ws G r et {w} m =
  filter_true (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) m
              (all_at (λ z -> r ∈ᵛ reachSet ws G z) (reachSet ws G r) m et)

-- A terminal component is closed under successors inside ws.  This is what the
-- refutation branch needs of it, and it is the whole use of terminality.

termClosed : (ws : List Val) (G : Edges) (r : Val)
          -> isTerminal ws G r ≡ true -> Closed ws G (sccOf ws G r)
termClosed ws G r et z y mz my e =
  termScc ws G r et (reachClosed ws G r (sccReach ws G r z mz) my e)

------------------------------------------------------------------------
-- A non-empty graph has a terminal component.
--
-- Follow condensation edges: while r's component is not terminal there is a w
-- that r reaches and that does not reach r, so w's component is strictly later,
-- and one moves the representative to w.  The plan's "acyclicity makes the
-- components visited distinct" is here a Bar search, and the invariant that
-- makes it one is a single hypothesis --
--
--   every vertex of the current reachable set still satisfies the Bar predicate
--
-- -- with no list of visited representatives.  Giving up r is the sub-Bar cBar
-- hands over, and the new reachable set avoids r because w does not reach r.

-- A vertex whose component is terminal, found by the search above.

data Terminal (ws : List Val) (G : Edges) : Set where
  terminalAt : (r : Val) -> r ∈ ws -> isTerminal ws G r ≡ true -> Terminal ws G

module _ (ws : List Val) (G : Edges) where

  termGo   : (r : Val) -> r ∈ ws -> {E : Pred}
          -> AllSat E (reachSet ws G r) -> IFin E -> Terminal ws G
  termFind : (r : Val) -> r ∈ ws -> {E : Pred}
          -> AllSat E (reachSet ws G r) -> IFin E
          -> FindResult (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r)
          -> Terminal ws G

  termGo r mr av bar =
    termFind r mr av bar (findFalse (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r))

  termFind r mr av bar          (allTrue f)       =
    terminalAt r mr (all_intro (λ w -> r ∈ᵛ reachSet ws G w) (reachSet ws G r) f)
  termFind r mr {E} av (cBar h) (found w mw q) =
    termGo w (reachIn ws G r mw) av' (h r (av r (reachSeed ws G r mr)))
    where
      av' : (z : Val) -> z ∈ reachSet ws G w -> E z ∧ᵇ (r ≢ᵛ z) ≡ true
      av' z mz =
        andIntro (E z) (r ≢ᵛ z)
                 (av z (reachTrans ws G r w z mw mz))
                 (cong ¬ᵇ_ (notR (r ≡ᵛ z) refl))
        where
          notR : (b : Bool) -> r ≡ᵛ z ≡ b -> r ≡ᵛ z ≡ false
          notR false eb = eb
          notR true  eb = emptyElim (true≢false (trans (sym rIn) q))
            where
              rIn : r ∈ᵛ reachSet ws G w ≡ true
              rIn = ∈ᵛ-complete r (reachSet ws G w)
                      (subst (λ y -> y ∈ reachSet ws G w)
                             (sym (≡ᵛ-sound r z eb)) mz)

  findTerm : (r : Val) -> r ∈ ws
          -> Terminal ws G
  findTerm r mr =
    termGo r mr (λ z mz -> ∈ᵛ-complete z ws (reachIn ws G r mz)) (listBar ws)

------------------------------------------------------------------------
-- The positive certificate: a fair circuit.
--
-- A circuit at r is a non-empty closed trail through r together with, for every
-- fairness predicate, a witness on it.  This is the constructive half of the
-- lecture's argument -- pick a witness in each F_i and join them by paths inside
-- the component -- and it is done here rather than in G38, so that G38 has only
-- to reread a Trail as a Walk.

data Circuit (ws : List Val) (G : Edges) (fs : List Pred)
             (r : Val) : Set where
  circuit : (cy : List Val) -> Trail ws G r cy r -> null cy ≡ false
         -> ((f : Pred) -> f ∈ fs
               -> Σ[ z ∈ Val ] z ∈ cy × f z ≡ true)
         -> Circuit ws G fs r

circMono : (ws vs : List Val) (G : Edges) (fs : List Pred)
           (r : Val) -> ws ⊆ vs
        -> Circuit ws G fs r -> Circuit vs G fs r
circMono ws vs G fs r sb (circuit cy t nn wit) =
  circuit cy (trailMono ws vs G sb t) nn wit

-- C meets every fairness predicate: each f in fs holds somewhere in C.

meetsAll : List Pred -> List Val -> Bool
meetsAll fs C = all (λ g -> any g C) fs

data Loop (ws : List Val) (G : Edges) (r : Val) : Set where
  loopBy : (cy : List Val) -> Trail ws G r cy r -> null cy ≡ false -> Loop ws G r

-- A terminal component of a vertex that has a successor is non-trivial.  This
-- is the only place the "every vertex has an out-edge" branch is used, and it
-- is why no separate cycle detection is needed: the successor is reached, so
-- terminality sends a trail back.

module _ (ws : List Val) (G : Edges) (r : Val) where

  loopAt : r ∈ ws
        -> isTerminal ws G r ≡ true -> hasOut ws G r ≡ true -> Loop ws G r
  loopAt mr et ho =
    pick (null_false (outs ws G r) (notTrue (null (outs ws G r)) ho))
    where
      pick : (Σ[ x ∈ Val ] x ∈ outs ws G r) -> Loop ws G r
      pick (x , mx) = back (sccFrom ws G r x (termScc ws G r et inR))
        where
          mxw : x ∈ ws
          mxw = filter_sub (G r) ws mx

          grx : G r x ≡ true
          grx = filter_prop (G r) ws mx

          inR : x ∈ reachSet ws G r
          inR = reachClosed ws G r (reachSeed ws G r mr) mxw grx

          back : Reaches ws G x r -> Loop ws G r
          back (reachesBy zs t) = loopBy (x ∷ zs) (tCons mxw grx t) refl

  -- One fairness predicate added to a circuit.  The leg is  loop ++ (r to w) ++
  -- (w to r) , with the loop in front so that the r-to-w half is non-empty and w
  -- is therefore a vertex the leg VISITS, not merely an endpoint.  trailApp is
  -- left-nested for the same reason associativity never appears.

  consCirc : (cy0 : List Val) -> Trail ws G r cy0 r -> null cy0 ≡ false
          -> (f : Pred) (w : Val) -> f w ≡ true
          -> Reaches ws G r w -> Reaches ws G w r
          -> (fs : List Pred) -> Circuit ws G fs r
          -> Circuit ws G (f ∷ fs) r
  consCirc cy0 t0 nn f w fw (reachesBy as ta) (reachesBy bs tb) fs
           (circuit cy t nnc wit) =
    circuit (leg ++ cy) (trailApp ws G legT t) (appNotNull leg cy legNN) each
    where
      front : List Val
      front = cy0 ++ as

      frontT : Trail ws G r front w
      frontT = trailApp ws G t0 ta

      frontNN : null front ≡ false
      frontNN = appNotNull cy0 as nn

      leg : List Val
      leg = front ++ bs

      legT : Trail ws G r leg r
      legT = trailApp ws G frontT tb

      legNN : null leg ≡ false
      legNN = appNotNull front bs frontNN

      mw : w ∈ leg
      mw = memAppL front bs (trailLast ws G frontT frontNN)

      each : (g : Pred) -> g ∈ f ∷ fs
          -> Σ[ z ∈ Val ] z ∈ leg ++ cy × g z ≡ true
      each g here      = w , memAppL leg cy mw , fw
      each g (there m) = shift (wit g m)
        where
          shift : (Σ[ z ∈ Val ] z ∈ cy × g z ≡ true)
               -> Σ[ z ∈ Val ] z ∈ leg ++ cy × g z ≡ true
          shift (z , mz , gz) = z , memAppR leg cy mz , gz

  mkCirc : (cy0 : List Val) -> Trail ws G r cy0 r -> null cy0 ≡ false
        -> (C : List Val)
        -> ((u : Val) -> u ∈ C -> Reaches ws G r u)
        -> ((u : Val) -> u ∈ C -> Reaches ws G u r)
        -> (fs : List Pred) -> meetsAll fs C ≡ true
        -> Circuit ws G fs r
  mkCirc cy0 t0 nn C to from []        e = circuit cy0 t0 nn noF
    where
      noF : (f : Pred) -> f ∈ []
         -> Σ[ z ∈ Val ] z ∈ cy0 × f z ≡ true
      noF f ()
  mkCirc cy0 t0 nn C to from (f ∷ fs) e =
    pick (any_true f C (andTrueL (any f C) (meetsAll fs C) e))
    where
      rest : Circuit ws G fs r
      rest = mkCirc cy0 t0 nn C to from fs (andTrueR (any f C) (meetsAll fs C) e)

      pick : (Σ[ w ∈ Val ] w ∈ C × f w ≡ true)
          -> Circuit ws G (f ∷ fs) r
      pick (w , mw , fw) =
        consCirc cy0 t0 nn f w fw (to w mw) (from w mw) fs rest

------------------------------------------------------------------------
-- One step of the outer iteration, decided.
--
-- Given that every vertex of ws has an out-edge: ws is empty, or its terminal
-- component is fair and a circuit is built, or it misses some f and is a block
-- to be refuted.  Nothing here recurses, which is what keeps the outer
-- recursion below down to the shape of elimGo.

data Block (ws : List Val) (G : Edges) (fs : List Pred) : Set where
  bEmpty  : null ws ≡ true -> Block ws G fs
  bFair   : (r : Val) -> r ∈ ws -> Circuit ws G fs r -> Block ws G fs
  bUnfair : (r : Val) -> r ∈ ws -> isTerminal ws G r ≡ true
         -> (f : Pred) -> f ∈ fs -> any f (sccOf ws G r) ≡ false
         -> Block ws G fs

blockOf : (ws : List Val) (G : Edges) (fs : List Pred)
       -> ({x : Val} -> x ∈ ws -> hasOut ws G x ≡ true)
       -> Terminal ws G -> Block ws G fs
blockOf ws G fs h (terminalAt r mr et) = onFair (meetsAll fs (sccOf ws G r)) refl
  where
    onFair : (b : Bool) -> meetsAll fs (sccOf ws G r) ≡ b -> Block ws G fs
    onFair true  eb = fromLoop (loopAt ws G r mr et (h mr))
      where
        fromLoop : Loop ws G r -> Block ws G fs
        fromLoop (loopBy cy t nn) =
          bFair r mr (mkCirc ws G r cy t nn (sccOf ws G r)
                             (sccTo ws G r) (sccFrom ws G r) fs eb)
    onFair false eb = unf (all_false (λ g -> any g (sccOf ws G r)) fs eb)
      where
        unf : (Σ[ g ∈ Pred ] g ∈ fs × any g (sccOf ws G r) ≡ false)
           -> Block ws G fs
        unf (g , mg , eg) = bUnfair r mr et g mg eg

pickBlock : (ws : List Val) (G : Edges) (fs : List Pred)
         -> ({x : Val} -> x ∈ ws -> hasOut ws G x ≡ true) -> Block ws G fs
pickBlock []       G fs h = bEmpty refl
pickBlock (u ∷ ws) G fs h =
  blockOf (u ∷ ws) G fs h (findTerm (u ∷ ws) G u here)

------------------------------------------------------------------------
-- The negative certificate.
--
-- A well-founded record of the removal order, indexed by what is LEFT.  Two
-- kinds of step, and they are the two cases of Theorem 4.1 of m4.tex with the
-- formulas taken out: a vertex with no out-edge inside ws, and a block closed
-- under out-edges inside ws that misses a fairness predicate.  cNil says
-- nothing is left, so certAll below concludes about every vertex.

infixl 6 _∖ᵛ_ _∖_

_∖ᵛ_ : List Val -> Val -> List Val
ws ∖ᵛ x = filter (x ≢ᵛ_) ws

_∖_ : List Val -> List Val -> List Val
ws ∖ C = filter (λ z -> ¬ᵇ (z ∈ᵛ C)) ws

data Cert (G : Edges) (fs : List Pred) : List Val -> Set where
  cNil   : (ws : List Val) -> null ws ≡ true -> Cert G fs ws
  cSink  : (ws : List Val) (x : Val) -> x ∈ ws
        -> null (outs ws G x) ≡ true
        -> Cert G fs (ws ∖ᵛ x) -> Cert G fs ws
  cBlock : (ws C : List Val) (f : Pred) -> f ∈ fs
        -> C ⊆ ws -> Closed ws G C -> NoneSat f C
        -> Cert G fs (ws ∖ C) -> Cert G fs ws

------------------------------------------------------------------------
-- The theorem, on a sub-list

data FairIn (ws : List Val) (G : Edges) (fs : List Pred) : Set where
  fairIn : (r : Val) -> r ∈ ws -> Circuit ws G fs r -> FairIn ws G fs

fairInMono : (ws vs : List Val) (G : Edges) (fs : List Pred)
          -> ws ⊆ vs
          -> FairIn ws G fs -> FairIn vs G fs
fairInMono ws vs G fs sb (fairIn r mr c) =
  fairIn r (sb r mr) (circMono ws vs G fs r sb c)

-- Terminal-component removal.  A REMOVING iteration, so barRec covers it and
-- there is no rank and no topological sort: whichever of the two steps applies,
-- the vertex it names leaves ws and leaves the Bar's predicate with it, which is
-- what dropAllSat says.  For the sink that vertex is x; for a block it is the
-- representative r, which lies in its own component by sccRep.

module _ (G : Edges) (fs : List Pred) where

  graphGo    : {E : Pred} (ws : List Val) -> AllSat E ws -> IFin E
            -> FairIn ws G fs ⊎ Cert G fs ws
  graphFind  : {E : Pred} (ws : List Val) -> AllSat E ws -> IFin E
            -> FindResult (hasOut ws G) ws
            -> FairIn ws G fs ⊎ Cert G fs ws
  graphBlock : {E : Pred} (ws : List Val) -> AllSat E ws -> IFin E
            -> Block ws G fs -> FairIn ws G fs ⊎ Cert G fs ws

  graphGo ws sb bar = graphFind ws sb bar (findFalse (hasOut ws G) ws)

  graphFind ws sb bar      (allTrue f)       =
    graphBlock ws sb bar (pickBlock ws G fs f)
  graphFind ws sb (cBar h) (found x mx q) =
    sumElim (λ fi -> inl (fairInMono (ws ∖ᵛ x) ws G fs
                                     (λ z m -> filter_sub (x ≢ᵛ_) ws m) fi))
            (λ c  -> inr (cSink ws x mx (notFalse (null (outs ws G x)) q) c))
            (graphGo (ws ∖ᵛ x) (dropAllSat (x ≢ᵛ_) ws sb x (≢ᵛ-self x))
                     (h x (sb x mx)))

  graphBlock ws sb bar      (bEmpty e)                 = inr (cNil ws e)
  graphBlock ws sb bar      (bFair r mr c)             = inl (fairIn r mr c)
  graphBlock ws sb (cBar h) (bUnfair r mr et g mg eg) =
    sumElim (λ fi -> inl (fairInMono (ws ∖ C) ws G fs
                                     (λ z m -> filter_sub (λ y -> ¬ᵇ (y ∈ᵛ C)) ws m)
                                     fi))
            (λ c  -> inr (cBlock ws C g mg (sccIn ws G r) (termClosed ws G r et) miss c))
            (graphGo (ws ∖ C)
                     (dropAllSat (λ y -> ¬ᵇ (y ∈ᵛ C)) ws sb r
                                 (cong ¬ᵇ_ (∈ᵛ-complete r C (sccRep ws G r mr))))
                     (h r (sb r mr)))
    where
      C : List Val
      C = sccOf ws G r

      miss : (z : Val) -> z ∈ C -> g z ≡ false
      miss z mz = any_false g C eg mz

------------------------------------------------------------------------
-- The theorem

data FairLoop (vs : List Val) (G : Edges) (fs : List Pred)
              (v : Val) : Set where
  fairLoop : (r : Val) (st cy : List Val)
          -> Trail vs G v st r -> Trail vs G r cy r -> null cy ≡ false
          -> ((f : Pred) -> f ∈ fs
                -> Σ[ z ∈ Val ] z ∈ cy × f z ≡ true)
          -> FairLoop vs G fs v

fairGraph : (vs : List Val) (G : Edges) (fs : List Pred)
            (v : Val) -> v ∈ vs
         -> FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v)
fairGraph vs G fs v mv =
  sumElim (λ fi -> inl (toLoop fi)) inr
          (graphGo G fs (reachSet vs G v) (memAllSat (reachSet vs G v))
                   (listBar (reachSet vs G v)))
  where
    into : (z : Val) -> z ∈ reachSet vs G v -> z ∈ vs
    into z m = reachIn vs G v m

    toLoop : FairIn (reachSet vs G v) G fs -> FairLoop vs G fs v
    toLoop (fairIn r mr c) =
      withStem (reachTrail vs G v mr) (circMono (reachSet vs G v) vs G fs r into c)
      where
        withStem : Reaches vs G v r -> Circuit vs G fs r -> FairLoop vs G fs v
        withStem (reachesBy st ts) (circuit cy t nn wit) = fairLoop r st cy ts t nn wit

------------------------------------------------------------------------
-- What a certificate is FOR.
--
-- Reading the removal order as a well-founded induction.  R is the property to
-- be established of every vertex -- for G39 it is  Deriv (¬ (chi P u)) -- and
-- the hypothesis carried is "R holds outside ws", which is Refuted of
-- LTL.Extract verbatim.  The sink case is what extractR1 consumes and the block
-- case is what extractR2 consumes; no formula has to appear for that to be
-- decided here.

module _ (G : Edges) (fs : List Pred) (R : Val -> Set)
         (sinkCase  : (ws : List Val) (x : Val) -> x ∈ ws
                   -> null (outs ws G x) ≡ true
                   -> HoldsOutside R ws -> R x)
         (blockCase : (ws C : List Val) (f : Pred) -> f ∈ fs
                   -> C ⊆ ws -> Closed ws G C -> NoneSat f C
                   -> HoldsOutside R ws -> (z : Val) -> z ∈ C -> R z)
         where

  certAll : {ws : List Val} -> Cert G fs ws -> HoldsOutside R ws -> (z : Val) -> R z
  certAll (cNil ws e)          ih z = ih z (null_notMem ws z e)
  certAll (cSink ws x mx e c)  ih z = certAll c ih' z
    where
      ih' : HoldsOutside R (ws ∖ᵛ x)
      ih' y eo = onWs (y ∈ᵛ ws) refl
        where
          onWs : (b : Bool) -> y ∈ᵛ ws ≡ b -> R y
          onWs false eb = ih y eb
          onWs true  eb = onX (x ≡ᵛ y) refl
            where
              my : y ∈ ws
              my = ∈ᵛ-sound y ws eb

              onX : (c' : Bool) -> x ≡ᵛ y ≡ c' -> R y
              onX true  ec = subst R (≡ᵛ-sound x y ec) (sinkCase ws x mx e ih)
              onX false ec =
                emptyElim (∈ᵛ-false y (ws ∖ᵛ x) eo
                            (filter_true (x ≢ᵛ_) ws my (cong ¬ᵇ_ ec)))
  certAll (cBlock ws C f mf sb cl mis c) ih z =
    certAll c ih' z
    where
      ih' : HoldsOutside R (ws ∖ C)
      ih' y eo = onWs (y ∈ᵛ ws) refl
        where
          onWs : (b : Bool) -> y ∈ᵛ ws ≡ b -> R y
          onWs false eb = ih y eb
          onWs true  eb = onC (y ∈ᵛ C) refl
            where
              my : y ∈ ws
              my = ∈ᵛ-sound y ws eb

              onC : (c' : Bool) -> y ∈ᵛ C ≡ c' -> R y
              onC true  ec = blockCase ws C f mf sb cl mis ih y (∈ᵛ-sound y C ec)
              onC false ec =
                emptyElim (∈ᵛ-false y (ws ∖ C) eo
                            (filter_true (λ u -> ¬ᵇ (u ∈ᵛ C)) ws my
                                         (cong ¬ᵇ_ ec)))

------------------------------------------------------------------------
-- The two outputs are EXCLUSIVE.
--
-- This is the intuitive half of the lecture's argument, and the point is that it
-- comes out FINITARY.  The lecture says "an infinite path eventually stays
-- inside one SCC", which needs an infinite path and a classical step; what is
-- actually needed is the contrapositive about a FINITE cycle, and that is two
-- observations about a closed trail:
--
--   a vertex on a cycle has a successor,  so a sink is on no cycle;
--   any vertex of a cycle reaches any other,  so a cycle that enters a
--     successor-closed block never leaves it.
--
-- Both are inductions on a trail of the length it happens to have.  No infinite
-- path is mentioned, nothing is coinductive, and no pigeonhole is used -- which
-- is the same three absences FORMALISATION-PLAN.md section 4f claims for the
-- rest of the development.

-- The suffix of a trail from any vertex it visits, and the prefix to one.  This
-- is walkFrom of LTL.Walk, in both directions, and it is all the "rotate the
-- cycle" the argument needs.

module _ (ws : List Val) (G : Edges) where

  reachesCons : {v x s : Val}
             -> x ∈ ws -> G v x ≡ true -> Reaches ws G x s -> Reaches ws G v s
  reachesCons m e (reachesBy zs t) = reachesBy (_ ∷ zs) (tCons m e t)

  reachesApp : {u v w : Val}
            -> Reaches ws G u v -> Reaches ws G v w -> Reaches ws G u w
  reachesApp (reachesBy as ta) (reachesBy bs tb) =
    reachesBy (as ++ bs) (trailApp ws G ta tb)

  trailFrom : {v : Val} {zs : List Val} {w : Val}
           -> Trail ws G v zs w -> {s : Val} -> s ∈ v ∷ zs -> Reaches ws G s w
  trailFrom tNil          here      = reachesBy [] tNil
  trailFrom tNil          (there ())
  trailFrom (tCons m e t) here      = reachesBy _ (tCons m e t)
  trailFrom (tCons m e t) (there k) = trailFrom t k

  trailTo : {v : Val} {zs : List Val} {w : Val}
         -> Trail ws G v zs w -> {s : Val} -> s ∈ zs -> Reaches ws G v s
  trailTo tNil          ()
  trailTo (tCons m e t) here      = reachesBy (_ ∷ []) (tCons m e tNil)
  trailTo (tCons m e t) (there k) = reachesCons m e (trailTo t k)

-- Observation one: a vertex on a cycle has a successor inside ws.  Along a
-- trail, every vertex visited has a successor provided the ENDPOINT has, and for
-- a closed trail the endpoint is the start, whose successor is the trail's own
-- first step.

data HasSucc (ws : List Val) (G : Edges) (x : Val) : Set where
  hasSucc : (y : Val) -> y ∈ ws -> G x y ≡ true -> HasSucc ws G x

module _ (ws : List Val) (G : Edges) where

  firstStep : {v : Val} {zs : List Val} {w : Val}
           -> Trail ws G v zs w -> null zs ≡ false -> HasSucc ws G v
  firstStep tNil                  ()
  firstStep (tCons {x = y} m e t) nn = hasSucc y m e

  headSucc : {v : Val} {zs : List Val} {w : Val}
          -> Trail ws G v zs w -> HasSucc ws G w -> HasSucc ws G v
  headSucc tNil                  hw = hw
  headSucc (tCons {x = y} m e t) hw = hasSucc y m e

  trailSucc : {v : Val} {zs : List Val} {w : Val}
           -> Trail ws G v zs w -> HasSucc ws G w -> {x : Val} -> x ∈ zs -> HasSucc ws G x
  trailSucc tNil          hw ()
  trailSucc (tCons m e t) hw here      = headSucc t hw
  trailSucc (tCons m e t) hw (there k) = trailSucc t hw k

  cycSucc : (r : Val) (cy : List Val)
         -> Trail ws G r cy r -> null cy ≡ false
         -> {x : Val} -> x ∈ cy -> HasSucc ws G x
  cycSucc r cy t nn mx = trailSucc t (firstStep t nn) mx

  -- Observation two: any vertex of a cycle reaches any other -- suffix to the
  -- base point, then prefix out again -- and a successor-closed block that a
  -- trail starts in contains everything the trail reaches.

  cycConn : (r : Val) (cy : List Val)
         -> Trail ws G r cy r -> (u z : Val) -> u ∈ cy -> z ∈ cy -> Reaches ws G u z
  cycConn r cy t u z mu mz =
    reachesApp ws G (trailFrom ws G t (there mu)) (trailTo ws G t mz)

blockAlong : (ws C : List Val) (G : Edges) -> Closed ws G C
          -> {u : Val} {zs : List Val} {z : Val}
          -> Trail ws G u zs z -> u ∈ C -> z ∈ C
blockAlong ws C G cl tNil                       mu = mu
blockAlong ws C G cl (tCons {x = y} m e t)      mu =
  blockAlong ws C G cl t (cl _ y mu m e)

trailRestrict : (ws vs : List Val) (G : Edges)
                {v : Val} {zs : List Val} {w : Val}
             -> Trail ws G v zs w -> zs ⊆ vs
             -> Trail vs G v zs w
trailRestrict ws vs G tNil                 h = tNil
trailRestrict ws vs G (tCons {x = y} m e t) h =
  tCons (h y here) e (trailRestrict ws vs G t (λ z mz -> h z (there mz)))

-- The theorem: a certificate for ws forbids a fair circuit inside ws.
--
-- Induction on the certificate, and each step says the cycle SURVIVES the
-- removal -- it never touched what was removed -- so the cycle is still there
-- when nothing is left, which cNil forbids.  That is the whole content of "an
-- infinite path eventually stays inside one SCC", finitely.

certNoCirc : (G : Edges) (fs : List Pred) {ws : List Val}
          -> Cert G fs ws -> (r : Val) -> Circuit ws G fs r -> Empty
certNoCirc G fs (cNil ws e)         r (circuit cy t nn wit) =
  null_mem ws e (trailIn ws G t (trailLast ws G t nn))
certNoCirc G fs (cSink ws x mx e c) r (circuit cy t nn wit) =
  certNoCirc G fs c r (circuit cy (trailRestrict ws (ws ∖ᵛ x) G t keep) nn wit)
  where
    offCycle : x ∈ cy -> Empty
    offCycle m = onS (cycSucc ws G r cy t nn m)
      where
        onS : HasSucc ws G x -> Empty
        onS (hasSucc y my gy) = null_mem (outs ws G x) e (filter_true (G x) ws my gy)

    keep : (z : Val) -> z ∈ cy -> z ∈ ws ∖ᵛ x
    keep z mz = filter_true (x ≢ᵛ_) ws (trailIn ws G t mz) (out (x ≡ᵛ z) refl)
      where
        out : (b : Bool) -> x ≡ᵛ z ≡ b -> x ≢ᵛ z ≡ true
        out false eb = cong ¬ᵇ_ eb
        out true  eb =
          emptyElim (offCycle (subst (λ y -> y ∈ cy)
                                     (sym (≡ᵛ-sound x z eb)) mz))
certNoCirc G fs (cBlock ws C f mf sb cl mis c) r (circuit cy t nn wit) =
  certNoCirc G fs c r (circuit cy (trailRestrict ws (ws ∖ C) G t keep) nn wit)
  where
    inBlock : (z : Val) -> z ∈ cy -> z ∈ C -> Empty
    inBlock z mz mzc = onW (wit f mf)
      where
        onW : (Σ[ y ∈ Val ] y ∈ cy × f y ≡ true) -> Empty
        onW (y , my , fy) = true≢false (trans (sym fy) (mis y inC))
          where
            inC : y ∈ C
            inC = along (cycConn ws G r cy t z y mz my)
              where
                along : Reaches ws G z y -> y ∈ C
                along (reachesBy as ta) = blockAlong ws C G cl ta mzc

    keep : (z : Val) -> z ∈ cy -> z ∈ ws ∖ C
    keep z mz = filter_true (λ y -> ¬ᵇ (y ∈ᵛ C)) ws (trailIn ws G t mz)
                            (out (z ∈ᵛ C) refl)
      where
        out : (b : Bool) -> z ∈ᵛ C ≡ b -> ¬ᵇ (z ∈ᵛ C) ≡ true
        out false eb = cong ¬ᵇ_ eb
        out true  eb = emptyElim (inBlock z mz (∈ᵛ-sound z C eb))

------------------------------------------------------------------------
-- The dichotomy, at the top level.
--
-- fairGraph's two answers cannot both be right, and therefore the negative
-- answer is a DECISION: if a fair lasso from v exists at all, fairGraph returns
-- one.  Restricting the lasso's cycle to the reachable set is reachComplete,
-- which is where the growing search of the first half pays off.

fairNoLoop : (vs : List Val) (G : Edges) (fs : List Pred)
             (v : Val) -> v ∈ vs
          -> Cert G fs (reachSet vs G v) -> FairLoop vs G fs v -> Empty
fairNoLoop vs G fs v mv c (fairLoop r st cy ts t nn wit) =
  certNoCirc G fs c r
             (circuit cy (trailRestrict vs (reachSet vs G v) G t keep) nn wit)
  where
    keep : (z : Val) -> z ∈ cy -> z ∈ reachSet vs G v
    keep z mz = onR (reachesApp vs G (reachesBy st ts) (trailTo vs G t mz))
      where
        onR : Reaches vs G v z -> z ∈ reachSet vs G v
        onR (reachesBy zs tz) = reachComplete vs G v mv tz

fairComplete : (vs : List Val) (G : Edges) (fs : List Pred)
               (v : Val) (mv : v ∈ vs)
            -> FairLoop vs G fs v -> isInl (fairGraph vs G fs v mv) ≡ true
fairComplete vs G fs v mv fl = onS (fairGraph vs G fs v mv) refl
  where
    onS : (s : FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v))
       -> fairGraph vs G fs v mv ≡ s
       -> isInl (fairGraph vs G fs v mv) ≡ true
    onS (inl l) es = cong isInl es
    onS (inr c) es = emptyElim (fairNoLoop vs G fs v mv c fl)

------------------------------------------------------------------------
-- Computational checks.
--
-- Two vertices,  a = 1  and  b = 0 , with every edge pointing at b: a -> b and
-- b -> b.  So b's component is terminal and non-trivial, a's is not terminal,
-- and the answer depends only on which vertex the fairness predicate asks for.
-- The g in gA, gB, gVs, gE, ... stands for "graph"; they are test data only.

gA : Val
gA = true ∷ []

gB : Val
gB = false ∷ []

gVs : List Val
gVs = gA ∷ gB ∷ []

gE : Edges
gE v w = w ≡ᵛ gB

reach_gA : reachSet gVs gE gA ≡ gB ∷ gA ∷ []
reach_gA = refl

term_gA : isTerminal gVs gE gA ≡ false
term_gA = refl

term_gB : isTerminal gVs gE gB ≡ true
term_gB = refl

scc_gB : sccOf gVs gE gB ≡ gB ∷ []
scc_gB = refl

-- Asking for b is fair: the cycle b -> b meets it.

fair_gB : isInl (fairGraph gVs gE ((λ v -> v ≡ᵛ gB) ∷ []) gA here) ≡ true
fair_gB = refl

-- Asking for a is not: a is transient, so the only recurrent component misses
-- the predicate and the certificate branch is taken.

fair_gA : isInl (fairGraph gVs gE ((λ v -> v ≡ᵛ gA) ∷ []) gA here) ≡ false
fair_gA = refl

------------------------------------------------------------------------
-- A second graph, which exercises everything the first does not.
--
--   p -> q ,  q -> s ,  s -> q
--
-- p is transient and {q,s} is a two-vertex recurrent component, so: findTerm
-- has to move the representative once (p's component is not terminal), the
-- circuit has two legs to concatenate rather than none, and on the unfair side
-- the certificate uses all three of its constructors -- cBlock removes {q,s},
-- then cSink removes p, which only becomes a sink once the component is gone,
-- then cNil.

gP : Val
gP = true ∷ true ∷ []

gQ : Val
gQ = true ∷ false ∷ []

gS : Val
gS = false ∷ false ∷ []

gVs2 : List Val
gVs2 = gP ∷ gQ ∷ gS ∷ []

gE2 : Edges
gE2 v w = (v ≡ᵛ gP) ∧ᵇ (w ≡ᵛ gQ) ∨ᵇ
          (v ≡ᵛ gQ) ∧ᵇ (w ≡ᵛ gS) ∨ᵇ
          (v ≡ᵛ gS) ∧ᵇ (w ≡ᵛ gQ)

term_gP : isTerminal gVs2 gE2 gP ≡ false
term_gP = refl

term_gQ : isTerminal gVs2 gE2 gQ ≡ true
term_gQ = refl

scc_gQ : map (λ z -> z ∈ᵛ sccOf gVs2 gE2 gQ) gVs2 ≡ false ∷ true ∷ true ∷ []
scc_gQ = refl

-- The lasso the fair branch returns, read off in full.
--
-- findTerm settles on s as the representative, so the stem is  p -> q -> s  and
-- the loop is  s -> q -> s .  Two fairness predicates, "is q" and "is s"; the
-- cycle is one leg per predicate followed by the bare loop, each leg being the
-- loop again then out to the witness and back --
--
--   q s q s   for "is q" ,   q s   for "is s" ,   q s   the loop
--
-- and the leg carries the loop in FRONT precisely so that the out-half is
-- non-empty and the witness is therefore a vertex the leg VISITS, not merely an
-- endpoint; for "is s" the out-half and the back-half are both empty, since the
-- witness is the representative, and only the leading loop makes that leg a
-- cycle through s at all.  This is the SCC construction choosing witnesses in
-- its own order, and it is not the shortest fair cycle -- q s would do.

loopCycle : {vs : List Val} {G : Edges} {fs : List Pred} {v : Val}
         -> FairLoop vs G fs v -> List Val
loopCycle (fairLoop r st cy ts t nn wit) = cy

cycleOf : {vs : List Val} {G : Edges} {fs : List Pred} {v : Val}
       -> FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v) -> List Val
cycleOf (inl l) = loopCycle l
cycleOf (inr c) = []

stemOf : {vs : List Val} {G : Edges} {fs : List Pred} {v : Val}
      -> FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v) -> List Val
stemOf (inl (fairLoop r st cy ts t nn wit)) = st
stemOf (inr c)                              = []

fairQS : FairLoop gVs2 gE2 ((λ v -> v ≡ᵛ gQ) ∷ (λ v -> v ≡ᵛ gS) ∷ []) gP ⊎
         Cert gE2 ((λ v -> v ≡ᵛ gQ) ∷ (λ v -> v ≡ᵛ gS) ∷ [])
              (reachSet gVs2 gE2 gP)
fairQS = fairGraph gVs2 gE2 ((λ v -> v ≡ᵛ gQ) ∷ (λ v -> v ≡ᵛ gS) ∷ []) gP here

fair_QS : isInl fairQS ≡ true
fair_QS = refl

stem_QS : stemOf fairQS ≡ gQ ∷ gS ∷ []
stem_QS = refl

cycle_QS : cycleOf fairQS ≡ gQ ∷ gS ∷ gQ ∷ gS ∷ gQ ∷ gS ∷ gQ ∷ gS ∷ []
cycle_QS = refl

-- And the unfair side: nothing recurrent meets "is p".

fair_P : isInl (fairGraph gVs2 gE2 ((λ v -> v ≡ᵛ gP) ∷ []) gP here) ≡ false
fair_P = refl

-- The certificate it returns instead, as the list of its steps: 2 for cBlock,
-- 1 for cSink, 0 for cNil.  It is  cBlock, cSink, cNil  -- the component {q,s}
-- is refuted first because it misses "is p", and only then is p a sink, which is
-- the whole point of the backwards induction: p is refuted BECAUSE its successor
-- already was.  Reading this off is what certAll does with a formula attached.

certShape : {G : Edges} {fs : List Pred} {ws : List Val}
         -> Cert G fs ws -> List Nat
certShape (cNil ws e)                    = 0 ∷ []
certShape (cSink ws x mx e c)            = 1 ∷ certShape c
certShape (cBlock ws C f mf sb cl mis c) = 2 ∷ certShape c

certSteps : {vs : List Val} {G : Edges} {fs : List Pred} {v : Val}
       -> FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v) -> List Nat
certSteps (inl l) = []
certSteps (inr c) = certShape c

cert_P : certSteps (fairGraph gVs2 gE2 ((λ v -> v ≡ᵛ gP) ∷ []) gP here) ≡
         2 ∷ 1 ∷ 0 ∷ []
cert_P = refl

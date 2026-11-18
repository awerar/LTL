{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SCC.SccLasso -- G38 of PHASE11-PLAN.md: an accepting component gives a lasso.
--
-- LTL.SCC.Graph proves the finite fair-graph certificate theorem with no formula in
-- it.  This file is one half of the translation layer: it reads the POSITIVE
-- answer of that theorem -- a FairLoop, i.e. a stem, a non-empty cycle and a
-- witness on the cycle for every fairness predicate -- as a Lasso of
-- Proposition 5.3, and hence as a Run.  The negative answer is G39 and is not
-- touched here.
--
-- There is little to it, and that is the point of G37 having been done first.
--
-- 1. Trail becomes Walk.  LTL.Graph's Trail is LTL.Walk's Walk with  step P
--    replaced by the abstract edge test G; at  G = step P  the two are the same
--    three fields, so trailWalk and walkTrail are two-clause inductions and not
--    constructions.  Nothing else is needed of the graph layer's paths.
--
-- 2. The fairness predicates are fixed.  For the eventuality  □ A ,
--
--        evPred P A z  =  valOf P z (□ A)  or  not (valOf P z A)
--
--    "□ A is not pending at z, or A already fails at z", and evPreds P is one
--    of these for each A in  □Args (sub P) .  A cycle meeting evPred P A
--    either visits a state where the eventuality is not pending -- and then
--    persistence walks that back and it is pending nowhere on the cycle -- or
--    visits a state where A fails, which is fulfilment.  So RELEVANCE, which
--    the informal argument has to define ("the fairness sets relevant in C",
--    well defined only because a pending eventuality is uniform on a component)
--    is absorbed into the disjunction and the graph layer never hears of it.
--    That is why LTL.SCC.Graph knows only "C meets every f in fs".
--
-- 3. The cycle-fulfilment field of mkLasso is matched to those witnesses.  This
--    is the only real proof in the file and it is closeLasso's argument run
--    TWICE rather than once.  Given  □ A  pending at a state s of the cycle:
--
--      walkPersist from s round to the base point r  --  either A is fulfilled
--        on the way, and we are done, or □ A is still pending at r;
--      persistTo from r out to the witness z  --  either A is fulfilled on the
--        way, and we are done, or □ A is still pending at z, and then
--        evPred's first disjunct is false at z, so its second is true, so A
--        fails at z, which is fulfilment at a state the cycle visits.
--
--    LTL.Countermodel.Walk has walkPersist, which reaches the ENDPOINT of a walk; the second
--    step needs it at a state VISITED, because the witness the graph layer
--    chooses is somewhere on the cycle and not at its base point.  persistTo
--    below is walkPersist with the target state carried along, and it is the
--    only new induction in the file.
--
-- The design decision, and it is the only one.
--
-- mkLasso's side conditions are all against  Uinf P :  b ∈ Uinf P , and
-- both walks are  Walk P (Uinf P) .  LTL.Graph's vertices are whatever list it
-- is handed.  So the graph search has to be run somewhere inside Uinf P, and
-- sccLasso is stated for an arbitrary vertex list vs together with
--
--     (z : Val) -> z ∈ vs -> z ∈ Uinf P
--
-- so that "somewhere inside" is a parameter rather than a commitment.  The
-- instance taken here is  vs = Uinf P  with the identity inclusion.
--
-- At that instance the certificate branch is DEAD, and the second half of the
-- file proves it rather than asserting it: lassoFair turns the lasso
-- Proposition 5.3 already supplies into a FairLoop -- the converse translation,
-- and the place where the polarity of evPred is checked in the other direction
-- -- and then fairNoLoop, LTL.Graph's exclusivity theorem, refutes the
-- certificate.  So sccLassoOf has exactly the type of  lasso ,
--
--     (P : Formula) (v0 : Val) -> v0 ∈ Uinf P -> Lasso P v0
--
-- and G38 is a second proof of Proposition 5.3 rather than a conditional one.
-- Note that this costs nothing to run: fairGraph returns inl, so the branch
-- calling  lasso  is never evaluated, and sccAt below is computed by the SCC
-- search alone.
--
-- Running the search instead at  Ust P , which is what G39's extraction will
-- want (Refuted quantifies over Ust P), would make the certificate branch live
-- and the LASSO branch the one needing work: a fair cycle in Ust P has a
-- successor at every state and fulfils every pending eventuality along itself,
-- so it survives every elimination round and lies in Uinf P -- but that
-- inclusion is a greatest-fixed-point induction over elimGo and is not G38.
-- Stating sccLasso with the inclusion as a hypothesis is exactly what leaves
-- that door open: G40 can supply it, or can keep the elimination and use the
-- identity.
--
-- Nothing in LTL.Elimination.Extract, LTL.Elimination.Elim or LTL.Countermodel.Lasso is touched, and the existing
-- positive tail -- runOf, Hintikka, buildCM -- consumes the result unchanged.

module LTL.SCC.SccLasso where

open import LTL.Countermodel.Run   public
open import LTL.SCC.Graph _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl public

------------------------------------------------------------------------
-- Trails are walks, and walks are trails.
--
-- Trail us (step P) v zs w  is  Walk P us v zs w : same three fields, and
-- step P v x ≡ true is Trail's edge field at  G = step P  on the nose.  The
-- graph layer's abstraction costs one induction to undo, in either direction.

module _ (P : Formula) where

  trailWalk : (us : List Val) {v : Val} {zs : List Val} {w : Val}
           -> Trail us (step P) v zs w -> Walk P us v zs w
  trailWalk us tNil          = wnil
  trailWalk us (tCons m e t) = wcons m e (trailWalk us t)

  walkTrail : (us : List Val) {v : Val} {zs : List Val} {w : Val}
           -> Walk P us v zs w -> Trail us (step P) v zs w
  walkTrail us wnil            = tNil
  walkTrail us (wcons m e wk)  = tCons m e (walkTrail us wk)

  -- The base point of a non-empty cycle is a state the cycle visits.  Used in
  -- both directions: to place the base point among mkLasso's states, and to see
  -- that it lies in the vertex list.

  walkLast : (us : List Val) {v : Val} {zs : List Val} {w : Val}
          -> Walk P us v zs w -> null zs ≡ false -> w ∈ zs
  walkLast us wk nn = trailLast us (step P) (walkTrail us wk) nn

  ------------------------------------------------------------------------
  -- The fairness predicates.
  --
  -- One per eventuality of  □Args (sub P) .  Its FALSITY at z is exactly the
  -- pair of hypotheses the refutation branch consumes -- □ A pending at z, and
  -- A holding at z -- which is why the same list of predicates will serve G39;
  -- here only its truth at a witness is used, which is the disjunction read the
  -- other way.

  evPred : Formula -> Val -> Bool
  evPred A z = valOf P z (□ A) ∨ᵇ ¬ᵇ valOf P z A

  evPreds : List Pred
  evPreds = map evPred (□Args (sub P))

  evPredsMem : {A : Formula} -> A ∈ □Args (sub P)
            -> evPred A ∈ evPreds
  evPredsMem m = memMap evPred m

  evPredsInv : {g : Pred} -> g ∈ evPreds
            -> Σ[ A ∈ Formula ] A ∈ □Args (sub P) × g ≡ evPred A
  evPredsInv m = map-mem-inv evPred (□Args (sub P)) m

  -- Reading a witness: the predicate holds at z and the eventuality is still
  -- pending there, so the first disjunct is out and the second says A fails.

  evWitness : (A : Formula) (z : Val)
           -> evPred A z ≡ true -> valOf P z (□ A) ≡ false
           -> valOf P z A ≡ false
  evWitness A z ez pd =
    sumElim (λ e1 -> emptyElim (true≢false (trans (sym e1) pd)))
            (λ e2 -> ¬ᵇ-true (valOf P z A) e2)
            (∨ᵇ-true (valOf P z (□ A)) (¬ᵇ valOf P z A) ez)

  -- and building one, from either disjunct.

  evNotPending : (A : Formula) (z : Val)
              -> valOf P z (□ A) ≡ true -> evPred A z ≡ true
  evNotPending A z e = ∨ᵇ-introˡ (valOf P z (□ A)) (¬ᵇ valOf P z A) e

  evFails : (A : Formula) (z : Val)
         -> valOf P z A ≡ false -> evPred A z ≡ true
  evFails A z e =
    ∨ᵇ-introʳ (valOf P z (□ A)) (¬ᵇ valOf P z A) (cong ¬ᵇ_ e)

  ------------------------------------------------------------------------
  -- Persistence to a state VISITED, not to the endpoint.
  --
  -- walkPersist (LTL/Countermodel/Walk.agda:127) says: along a walk with □ A pending at the
  -- start, either A is fulfilled at a state visited or □ A is still pending at
  -- the END.  Here the second alternative is wanted at an arbitrary visited
  -- state.  The induction is walkPersist's own -- the step is persist, i.e.
  -- (T3) -- with the target carried along and the walk cut short when it is
  -- reached.

  persistTo : (us : List Val) (A : Formula) -> □ A ∈ sub P
           -> {v : Val} {ws : List Val} {x : Val} -> Walk P us v ws x
           -> valOf P v (□ A) ≡ false
           -> {z : Val} -> z ∈ ws
           -> Fulfil P A v ws ⊎ valOf P z (□ A) ≡ false
  persistTo us A mb wnil e ()
  persistTo us A mb (wcons {v} {w} {ws} {x} mw st wk) e {z} mz =
    onA z mz
    where
      onA : (y : Val) -> y ∈ w ∷ ws
         -> Fulfil P A v (w ∷ ws) ⊎ valOf P y (□ A) ≡ false
      onA y my with valOf P v A in ea
      ... | false = inl (ful v here ea)
      onA y here      | true = inr (persist P v w A mb st e ea)
      onA y (there k) | true =
        sumElim (λ f -> inl (fulfilCons f)) inr
                (persistTo us A mb wk (persist P v w A mb st e ea) k)

  ------------------------------------------------------------------------
  -- G38.
  --
  -- A FairLoop of LTL.SCC.Graph, inside any vertex list contained in Uinf P, is a
  -- Lasso of Proposition 5.3.

  sccLasso : (vs : List Val)
          -> vs ⊆ Uinf P
          -> (v0 : Val) -> FairLoop vs (step P) evPreds v0 -> Lasso P v0
  sccLasso vs sb v0 (fairLoop r st cy ts tc nn wit) =
    mkLasso r mr st wst cy wcy nn cyc
    where
      -- The cycle is non-empty, so its base point is a state it visits, and
      -- every state it visits lies in the vertex list.
      mr : r ∈ Uinf P
      mr = sb r (trailIn vs (step P) tc (trailLast vs (step P) tc nn))

      wst : Walk P (Uinf P) v0 st r
      wst = trailWalk (Uinf P) (trailMono vs (Uinf P) (step P) sb ts)

      wcy : Walk P (Uinf P) r cy r
      wcy = trailWalk (Uinf P) (trailMono vs (Uinf P) (step P) sb tc)

      cyc : AllFulfilled P r cy (r ∷ cy)
      cyc s ms A mA pd = fromSub (walkFrom P (Uinf P) wcy ms)
        where
          mbx : □ A ∈ sub P
          mbx = □Args-mem (sub P) mA

          -- Still pending at the base point: go out to the witness the graph
          -- layer chose for evPred P A.
          atR : valOf P r (□ A) ≡ false -> Fulfil P A r cy
          atR pr = onW (wit (evPred A) (evPredsMem mA))
            where
              onW : (Σ[ z ∈ Val ] z ∈ cy × evPred A z ≡ true)
                 -> Fulfil P A r cy
              onW (z , mz , ez) =
                sumElim (λ f -> f)
                        (λ pz -> ful z (there mz) (evWitness A z ez pz))
                        (persistTo (Uinf P) A mbx wcy pr mz)

          -- Travelling along the cycle from s, as Proposition 5.3 does.
          fromSub : SubWalk P (Uinf P) s r r cy -> Fulfil P A r cy
          fromSub (subWalk zs wz f) =
            sumElim mapFul atR (walkPersist P (Uinf P) A mbx wz pd)
            where
              mapFul : Fulfil P A s zs -> Fulfil P A r cy
              mapFul (ful z m q) = ful z (f m) q

  -- and hence a Run: the existing positive tail, unchanged.

  sccRun : (vs : List Val)
        -> vs ⊆ Uinf P
        -> (v0 : Val) -> v0 ∈ Uinf P
        -> FairLoop vs (step P) evPreds v0 -> Run P v0
  sccRun vs sb v0 mv0 fl = runOf P v0 mv0 (sccLasso vs sb v0 fl)

  ------------------------------------------------------------------------
  -- The converse, which is what makes the instance at Uinf P total.
  --
  -- A fulfilling lasso IS a fair loop for evPreds P.  For each eventuality: if
  -- it is not pending at the base point, the base point is its own witness --
  -- and it lies ON the cycle because the cycle is non-empty; if it is pending
  -- there, the lasso's own cycle-fulfilment field supplies a state of the cycle
  -- where A fails, which is the other disjunct.  This is the polarity of evPred
  -- checked from the other side.

  lassoFair : (v0 : Val) -> Lasso P v0
           -> FairLoop (Uinf P) (step P) evPreds v0
  lassoFair v0 (mkLasso b mb ps wp qs wq nn cyc) =
    fairLoop b ps qs (walkTrail (Uinf P) wp) (walkTrail (Uinf P) wq) nn each
    where
      mbq : b ∈ qs
      mbq = walkLast (Uinf P) wq nn

      forA : (A : Formula) -> A ∈ □Args (sub P)
          -> Σ[ z ∈ Val ] z ∈ qs × evPred A z ≡ true
      forA A mA with valOf P b (□ A) in ep
      ... | true  = b , mbq , evNotPending A b ep
      ... | false = onFul (cyc b here A mA ep)
        where
          onFul : Fulfil P A b qs
               -> Σ[ z ∈ Val ] z ∈ qs × evPred A z ≡ true
          onFul (ful z m q) = z , onMem m , evFails A z q
            where
              onMem : z ∈ b ∷ qs -> z ∈ qs
              onMem here      = mbq
              onMem (there k) = k

      each : (g : Pred) -> g ∈ evPreds
          -> Σ[ z ∈ Val ] z ∈ qs × g z ≡ true
      each g mg = onInv (evPredsInv mg)
        where
          onInv : (Σ[ A ∈ Formula ] A ∈ □Args (sub P) × g ≡ evPred A)
               -> Σ[ z ∈ Val ] z ∈ qs × g z ≡ true
          onInv (A , mA , eg) =
            subst (λ h -> Σ[ z ∈ Val ] z ∈ qs × h z ≡ true)
                  (sym eg) (forA A mA)

  ------------------------------------------------------------------------
  -- The instance: the search run on Uinf P itself, which always finds a loop.

  uinfFair : (v0 : Val) -> v0 ∈ Uinf P
          -> FairLoop (Uinf P) (step P) evPreds v0 ⊎
             Cert (step P) evPreds (reachSet (Uinf P) (step P) v0)
  uinfFair v0 mv0 = fairGraph (Uinf P) (step P) evPreds v0 mv0

  -- Proposition 5.3, again.  The certificate branch is refuted by fairNoLoop
  -- against the loop  lasso  already supplies; since fairGraph in fact returns
  -- inl, that branch is never evaluated and  lasso  is never run.

  sccLassoOf : (v0 : Val) -> v0 ∈ Uinf P -> Lasso P v0
  sccLassoOf v0 mv0 = sumElim yes no (uinfFair v0 mv0)
    where
      yes : FairLoop (Uinf P) (step P) evPreds v0 -> Lasso P v0
      yes fl = sccLasso (Uinf P) (λ z m -> m) v0 fl

      no : Cert (step P) evPreds (reachSet (Uinf P) (step P) v0) -> Lasso P v0
      no c = emptyElim (fairNoLoop (Uinf P) (step P) evPreds v0 mv0 c
                                   (lassoFair v0 (lasso P v0 mv0)))

  sccRunOf : (v0 : Val) -> v0 ∈ Uinf P -> Run P v0
  sccRunOf v0 mv0 = runOf P v0 mv0 (sccLassoOf v0 mv0)

  ------------------------------------------------------------------------
  -- Projections, so that the two procedures can be set side by side.  lassoAt
  -- of LTL.Countermodel.Lasso reads the round-based search the same way, so sccAt and
  -- lassoAt are two List Val × List Val to be compared.

  sccAt : (v : Val) -> v ∈ᵛ Uinf P ≡ true
       -> List Val × List Val
  sccAt v e = lassoStem P v l , lassoCycle P v l
    where
      l : Lasso P v
      l = sccLassoOf v (∈ᵛ-sound v (Uinf P) e)

  sccState : (v0 : Val) -> v0 ∈ᵛ Uinf P ≡ true -> Nat -> Val
  sccState v0 e i = stateAt P v0 (sccRunOf v0 m) i
    where
      m : v0 ∈ Uinf P
      m = ∈ᵛ-sound v0 (Uinf P) e

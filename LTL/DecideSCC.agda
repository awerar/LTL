{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.DecideSCC -- G40 of PHASE11-PLAN.md: the two branches joined.
--
--   decideSCC : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
--
-- the same type as decide (LTL.Decide, Theorem 6.1), decided by a different
-- question.  decide asks a BOOLEAN of the elimination,
--
--     satB (¬ Q)  --  does some surviving state contain ¬ Q?
--
-- and decideSCC asks which way the graph search went,
--
--     sccGraph (¬ Q)  --  is there a fair component in Ust (¬ Q)?
--
-- Neither branch is obtained by refuting the other, exactly as in decide: the
-- certificate branch returns a derivation built by G39 and never mentions a
-- lasso, and the fair branch returns a lasso built by G38 and mentions a
-- derivation only to consume one.
--
-- Why the search is run on all of Ust P and not from a vertex.  fairGraph is
-- v-centred and certifies only  reachSet vs G v ; the refutation branch has to
-- account for every state at once, so graphGo over Ust P is what G39 consumes.
-- Asking the question there is legitimate BECAUSE of the first lemma of
-- LTL.SccTrap: every state of Ust P is reached from a state containing P, so a
-- fair component anywhere in Ust P is a fair component reachable from a seed,
-- and the seed is what a countermodel needs.  Without that lemma the fair
-- branch would exhibit a loop that is a countermodel to nothing.
--
-- The route from a fair component to a countermodel, in four steps.
--
--   1. ustSeedTo -- the component's representative r is reached by a trail from
--      a state s with  ¬ Q  in it.  Stem and cycle together are a FairLoop
--      from s (LTL.Graph), still inside Ust P.
--   2. The loop is restricted to the list of vertices it actually uses,
--      C = s ∷ stem ++ cycle .  This is where the Trap is built: every vertex
--      of C has a successor in C -- the next one along, and for the cycle's
--      base point its own first step -- and every eventuality pending at a
--      vertex of C fails somewhere reachable inside C, by walking to the
--      witness the graph layer chose and reading evPred there.  Those are the
--      negations of (R1) and (R2).
--   3. uinfTrap -- so C survives the elimination and lies in Uinf P.  This is
--      the step that lets the existing positive tail be used unchanged: sccLasso
--      of G38 takes exactly the inclusion  C subset Uinf P  as its hypothesis,
--      which is why it was stated with that hypothesis rather than at Uinf P.
--   4. sccRun, then buildCMFrom -- Hintikka's lemma at stage 0 and soundness,
--      verbatim from buildCM, with the run supplied rather than built by lasso.
--
-- So the elimination is still COMPUTED in the fair branch -- uinfTrap runs
-- elimGo -- but it is not what decides, and it produces no lasso: the lasso is
-- the SCC construction's.  In the certificate branch the elimination is not
-- computed at all.  That asymmetry is the honest summary of what the phase
-- bought, and checkpoint C8 measures it.

module LTL.DecideSCC where

open import LTL.SccTrap public
open import LTL.Decide  public

------------------------------------------------------------------------
-- Paths out of trails, for the Trap's second field.

trailPath : (P : Formula) (C : List Val) {v : Val} {zs : List Val} {w : Val}
         -> Trail C (step P) v zs w -> Path P C v w
trailPath P C tNil          = pnil
trailPath P C (tCons m e t) = pcons m e (trailPath P C t)

reachPath : (P : Formula) (C : List Val) {v w : Val}
         -> Reaches C (step P) v w -> Path P C v w
reachPath P C (reachesBy zs t) = trailPath P C t

-- Walking from a pending eventuality to a state where it fails.  Along the way
-- either it is already fulfilled -- and the prefix of the trail to that state
-- is the path -- or it is still pending at the far end, where the caller's
-- hypothesis (for us, evWitness at the graph layer's witness) says it fails.

trapFail : (P : Formula) (C : List Val) (A : Formula) -> □ A ∈ sub P
        -> (z w : Val) -> Reaches C (step P) z w
        -> valOf P z (□ A) ≡ false
        -> (valOf P w (□ A) ≡ false -> valOf P w A ≡ false)
        -> Σ[ y ∈ Val ] Path P C z y × valOf P y A ≡ false
trapFail P C A mbx z w (reachesBy as t) pd atW =
  sumElim onFul (λ pw -> w , trailPath P C t , atW pw)
          (walkPersist P C A mbx (trailWalk P C t) pd)
  where
    onFul : Fulfil P A z as
         -> Σ[ y ∈ Val ] Path P C z y × valOf P y A ≡ false
    onFul (ful u mu eu) = pathTo u mu eu
      where
        pathTo : (x : Val) -> x ∈ z ∷ as -> valOf P x A ≡ false
              -> Σ[ y ∈ Val ] Path P C z y × valOf P y A ≡ false
        pathTo x here      e = x , pnil , e
        pathTo x (there m) e =
          x , reachPath P C (trailTo C (step P) t m) , e

------------------------------------------------------------------------
-- A fair loop, cut down to the vertices it uses, with its Trap.

data ScLasso (P : Formula) (v0 : Val) : Set where
  scLasso : (C : List Val) -> v0 ∈ C
         -> ((z : Val) -> z ∈ C -> z ∈ Ust P)
         -> Trap P C -> FairLoop C (step P) (evPreds P) v0 -> ScLasso P v0

fairScLasso : (P : Formula) (v0 : Val) -> v0 ∈ Ust P
           -> FairLoop (Ust P) (step P) (evPreds P) v0 -> ScLasso P v0
fairScLasso P v0 mv0 (fairLoop r st cy ts tc nn wit) =
  scLasso C here inC (mkTrap succC fulC) (fairLoop r st cy tsC tcC nn wit)
  where
    C : List Val
    C = v0 ∷ st ++ cy

    stC : (z : Val) -> z ∈ st -> z ∈ C
    stC z m = there (memAppL st cy m)

    cyC : (z : Val) -> z ∈ cy -> z ∈ C
    cyC z m = there (memAppR st cy m)

    inC : (z : Val) -> z ∈ C -> z ∈ Ust P
    inC z here      = mv0
    inC z (there m) = sumElim (λ m1 -> trailIn (Ust P) (step P) ts m1)
                              (λ m2 -> trailIn (Ust P) (step P) tc m2)
                              (memAppCase st cy m)

    tsC : Trail C (step P) v0 st r
    tsC = trailRestrict (Ust P) C (step P) ts stC

    tcC : Trail C (step P) r cy r
    tcC = trailRestrict (Ust P) C (step P) tc cyC

    -- (R1) fails on C: the base point steps onto its own cycle, everything on
    -- the cycle inherits that, and everything on the stem steps forward.
    hr : HasSucc C (step P) r
    hr = firstStep C (step P) tcC nn

    toSig : (x : Val) -> HasSucc C (step P) x
         -> Σ[ y ∈ Val ] y ∈ C × step P x y ≡ true
    toSig x (hasSucc y my e) = y , my , e

    succC : (z : Val) -> z ∈ C
         -> Σ[ y ∈ Val ] y ∈ C × step P z y ≡ true
    succC z here      = toSig z (headSucc C (step P) tsC hr)
    succC z (there m) =
      sumElim (λ m1 -> toSig z (trailSucc C (step P) tsC hr m1))
              (λ m2 -> toSig z (cycSucc C (step P) r cy tcC nn m2))
              (memAppCase st cy m)

    -- every vertex reaches every vertex of the cycle, inside C
    reachW : (z : Val) -> z ∈ C -> (w : Val) -> w ∈ cy
          -> Reaches C (step P) z w
    reachW z here     w mw =
      reachesApp C (step P) (trailFrom C (step P) tsC here)
                            (trailTo C (step P) tcC mw)
    reachW z (there m) w mw =
      sumElim (λ m1 -> reachesApp C (step P) (trailFrom C (step P) tsC (there m1))
                                             (trailTo C (step P) tcC mw))
              (λ m2 -> cycConn C (step P) r cy tcC z w m2 mw)
              (memAppCase st cy m)

    -- (R2) fails on C: walk to the witness and read evPred there.
    fulC : (z : Val) -> z ∈ C -> (A : Formula) -> A ∈ □Args (sub P)
        -> valOf P z (□ A) ≡ false
        -> Σ[ y ∈ Val ] Path P C z y × valOf P y A ≡ false
    fulC z mz A mA pd = onW (wit (evPred P A) (evPredsMem P mA))
      where
        onW : (Σ[ w ∈ Val ] w ∈ cy × evPred P A w ≡ true)
           -> Σ[ y ∈ Val ] Path P C z y × valOf P y A ≡ false
        onW (w , mw , ew) =
          trapFail P C A (□Args_mem (sub P) mA) z w (reachW z mz w mw) pd
                   (evWitness P A w ew)

-- and then the trap survives the elimination, so G38 applies.

scRun : (P : Formula) (v0 : Val) -> ScLasso P v0
     -> v0 ∈ Uinf P × Run P v0
scRun P v0 (scLasso C mv0 inU tr flC) =
  mv0U , sccRun P C intoU v0 mv0U flC
  where
    intoU : (z : Val) -> z ∈ C -> z ∈ Uinf P
    intoU = uinfTrap P C tr inU

    mv0U : v0 ∈ Uinf P
    mv0U = intoU v0 mv0

------------------------------------------------------------------------
-- buildCM with the run supplied.
--
-- Verbatim from LTL.Decide's buildCM except that the run is a parameter rather
-- than  runOf ... (lasso ...) .  Everything else -- (S1) at ¬ Q, Hintikka's
-- lemma at stage 0, soundness -- is the same three lines, and buildCM itself is
-- untouched: C8 needs both procedures in the development at once.

buildCMFrom : (Q : Formula) (v0 : Val) -> v0 ∈ Uinf (¬ Q)
           -> Run (¬ Q) v0 -> valOf (¬ Q) v0 (¬ Q) ≡ true
           -> LassoCountermodel Q
buildCMFrom Q v0 m r ev = countermodel v0 r m evalFalse noDeriv
  where
    valQ : valOf (¬ Q) v0 Q ≡ false
    valQ =
      notTrue (valOf (¬ Q) v0 Q)
        (trans (sym (boolEq_sound (valOf (¬ Q) v0 (¬ Q))
                                  (¬ᵇ valOf (¬ Q) v0 Q)
                                  (stateOk (¬ Q) v0 m (sub_self (¬ Q)))))
               ev)

    evalFalse : eval (¬ Q) v0 r Q 0 ≡ false
    evalFalse =
      trans (sym (hintStart (¬ Q) v0 r Q (there (sub_self Q)))) valQ

    noDeriv : ⊢ Q -> Empty
    noDeriv d = tfAbs (trans (sym (soundRun (¬ Q) v0 r d 0)) evalFalse)

------------------------------------------------------------------------
-- Theorem 6.1, by the SCC route.

decideSCC : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
decideSCC Q = sumElim onFair (λ c -> inl (provableSCC Q c)) (sccGraph (¬ Q))
  where
    R : Formula
    R = ¬ Q

    fromRun : (s : Val) -> valOf R s R ≡ true
           -> s ∈ Uinf R × Run R s
           -> ⊢ Q ⊎ LassoCountermodel Q
    fromRun s es (mu , rn) = inr (buildCMFrom Q s mu rn es)

    onFair : FairIn (Ust R) (step R) (evPreds R)
          -> ⊢ Q ⊎ LassoCountermodel Q
    onFair (fairIn r mr c) = onCirc c
      where
        onCirc : Circuit (Ust R) (step R) (evPreds R) r
              -> ⊢ Q ⊎ LassoCountermodel Q
        onCirc (circuit cy tc nn wit) = onSeed (ustSeedTo R r mr)
          where
            onSeed : SeedTo R r -> ⊢ Q ⊎ LassoCountermodel Q
            onSeed (seedTo s st ms es ts) =
              fromRun s es
                      (scRun R s (fairScLasso R s ms
                                              (fairLoop r st cy ts tc nn wit)))

------------------------------------------------------------------------
-- Checkpoints.
--
-- The two examples LTL.Extract ends with, and the two LTL.Lasso ends with:
-- the valid ones come back as proofs and the invalid ones as countermodels,
-- through the SCC branch each time.  The full agreement with decide, on all
-- forty-six statements of LTL.Examples, is checkpoint C8 and lives in
-- LTL.Compare, so that it is clear which side of the timing rule it is on.

decideSCC_benAri : isProof (decideSCC benAri) ≡ true
decideSCC_benAri = refl

decideSCC_bnb : isProof (decideSCC bnb) ≡ true
decideSCC_bnb = refl

decideSCC_◇P : isProof (decideSCC ◇P) ≡ false
decideSCC_◇P = refl

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Procedures.DecideSCC -- the decision procedure:
--
--   decideSCC : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
--
-- It searches Ust (¬ Q) for a fair component (sccGraph).  A certificate gives
-- a derivation (provableSCC, LTL.SCC.SccExtract).  A fair component gives a
-- countermodel, in four steps:
--
--   1. ustSeedTo: the component's representative is reached by a trail from a
--      state s containing ¬ Q.  Stem and cycle form a FairLoop from s.
--   2. The loop is cut down to the vertices it uses, C = s ∷ stem ++ cycle,
--      and C is a Trap: every vertex has a successor in C, and every pending
--      eventuality fails somewhere reachable in C (walk to the witness the
--      graph search chose, and read evPred there).
--   3. uinfTrap: C survives the elimination, so C lies in Uinf (¬ Q), as
--      sccLasso requires.
--   4. sccLasso, then buildCM: Hintikka's lemma at stage 0.
--
-- The search runs on all of Ust (¬ Q), not from one vertex, because the
-- certificate has to cover every state.  The elimination is computed only in
-- the fair branch.

module LTL.Procedures.DecideSCC where

open import LTL.SCC.SccTrap public
open import LTL.Procedures.Answer public

------------------------------------------------------------------------
-- Paths out of trails, for the Trap's second field.

module _ (P : Formula) where

  trailPath : (C : List Val) {v : Val} {zs : List Val} {w : Val}
           -> Trail C (step P) v zs w -> Path P C v w
  trailPath C tNil          = pnil
  trailPath C (tCons m e t) = pcons m e (trailPath C t)

  reachPath : (C : List Val) {v w : Val}
           -> Reaches C (step P) v w -> Path P C v w
  reachPath C (reachesBy zs t) = trailPath C t

  -- Walking from a pending eventuality to a state where it fails.  Either it
  -- is fulfilled on the way, and the prefix of the trail is the path, or it is
  -- still pending at the far end, where the caller's hypothesis (evWitness at
  -- the chosen witness) says it fails.

  trapFail : (C : List Val) (A : Formula) -> □ A ∈ sub P
          -> (z w : Val) -> Reaches C (step P) z w
          -> valOf P z (□ A) ≡ false
          -> (valOf P w (□ A) ≡ false -> valOf P w A ≡ false)
          -> Σ[ y ∈ Val ] Path P C z y × valOf P y A ≡ false
  trapFail C A mbx z w (reachesBy as t) pd atW =
    sumElim onFul (λ pw -> w , trailPath C t , atW pw)
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
            x , reachPath C (trailTo C (step P) t m) , e

------------------------------------------------------------------------
-- A fair loop, cut down to the vertices it uses, with its Trap: a TrapLoop.

record TrapLoop (P : Formula) (v0 : Val) : Set where
  constructor trapLoop
  field
    C       : List Val
    startIn : v0 ∈ C
    inUst   : C ⊆ Ust P
    trap    : Trap P C
    loop    : FairLoop C (step P) (evPreds P) v0

fairTrapLoop : (P : Formula) (v0 : Val) -> v0 ∈ Ust P
            -> FairLoop (Ust P) (step P) (evPreds P) v0 -> TrapLoop P v0
fairTrapLoop P v0 mv0 (fairLoop r st cy ts tc nn wit) =
  trapLoop C here inC (mkTrap succC fulC) (fairLoop r st cy tsC tcC nn wit)
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
    rSucc : HasSucc C (step P) r
    rSucc = firstStep C (step P) tcC nn

    toSig : (x : Val) -> HasSucc C (step P) x
         -> Σ[ y ∈ Val ] y ∈ C × step P x y ≡ true
    toSig x (hasSucc y my e) = y , my , e

    succC : (z : Val) -> z ∈ C
         -> Σ[ y ∈ Val ] y ∈ C × step P z y ≡ true
    succC z here      = toSig z (headSucc C (step P) tsC rSucc)
    succC z (there m) =
      sumElim (λ m1 -> toSig z (trailSucc C (step P) tsC rSucc m1))
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
          trapFail P C A (□Args-mem (sub P) mA) z w (reachW z mz w mw) pd
                   (evWitness P A w ew)

-- and then the trap survives the elimination, so sccLasso applies.

trapLoopLasso : (P : Formula) (v0 : Val) -> TrapLoop P v0 -> Lasso P v0
trapLoopLasso P v0 (trapLoop C mv0 inU tr flC) =
  sccLasso P C intoU v0 (intoU v0 mv0) flC
  where
    intoU : (z : Val) -> z ∈ C -> z ∈ Uinf P
    intoU = uinfTrap P C tr inU

------------------------------------------------------------------------
-- A countermodel from a lasso.
--
-- v0 contains ¬ Q and is a state, so by (S1) it does not contain Q;
-- Hintikka's lemma at stage 0 transfers that to the evaluation.

buildCM : (Q : Formula) (v0 : Val)
       -> Lasso (¬ Q) v0 -> valOf (¬ Q) v0 (¬ Q) ≡ true
       -> LassoCountermodel Q
buildCM Q v0 l ev = countermodel v0 l evalFalse
  where
    valQ : valOf (¬ Q) v0 Q ≡ false
    valQ =
      ¬ᵇ-true (valOf (¬ Q) v0 Q)
        (trans (sym (⇔ᵇ-sound (valOf (¬ Q) v0 (¬ Q))
                              (¬ᵇ valOf (¬ Q) v0 Q)
                                  (stateOk (¬ Q) v0 (Lasso.startIn l) (sub-self (¬ Q)))))
               ev)

    evalFalse : eval (¬ Q) v0 l Q 0 ≡ false
    evalFalse =
      trans (sym (hintStart (¬ Q) v0 l Q (there (sub-self Q)))) valQ

------------------------------------------------------------------------
-- The decision

decideSCC : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
decideSCC Q = sumElim onFair (λ c -> inl (provableSCC Q c)) (sccGraph (¬ Q))
  where
    R : Formula
    R = ¬ Q

    fromLasso : (s : Val) -> valOf R s R ≡ true -> Lasso R s
             -> ⊢ Q ⊎ LassoCountermodel Q
    fromLasso s es l = inr (buildCM Q s l es)

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
              fromLasso s es
                (trapLoopLasso R s
                   (fairTrapLoop R s ms (fairLoop r st cy ts tc nn wit)))

------------------------------------------------------------------------
-- Reading the answer of decideSCC.

-- The truth values of A at stages 0,...,n-1 of the countermodel to Q, or the
-- empty list if Q turned out to be provable and there is no countermodel.

traceOf : (Q : Formula) -> Formula -> Nat -> List Bool
traceOf Q A n = onDec (decideSCC Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> List Bool
    onDec (inl d) = []
    onDec (inr c) = cmFrom Q c A zero n

-- and the shape of the lasso: its run is v0 followed by cmRest, whose tail is
-- the cycle, so it is periodic from stage  1 + |cmRest| - |cmCycle|  on, with
-- period |cmCycle|.

shapeOf : (Q : Formula) -> Nat × Nat
shapeOf Q = onDec (decideSCC Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> Nat × Nat
    onDec (inl d) = zero , zero
    onDec (inr c) = length (cmRest Q c) , length (cmCycle Q c)

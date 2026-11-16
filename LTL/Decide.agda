{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Decide -- G28 of FORMALISATION-PLAN.md, Theorem 6.1 of m4.tex.
--
--   decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
--
-- Run the elimination on Sub(¬ Q) and ask whether some surviving state
-- contains ¬ Q.  That is one boolean, satB (¬ Q), and it decides which
-- branch applies; both branches were already complete before this module.
--
--   satB (¬ Q) = false.  Every state containing ¬ Q was removed, so is
--     refutable by Theorem 4.1; every survivor contains Q.  State completeness
--     closes it.  This is `provable` in LTL.Extract, and the certificate is a
--     derivation.
--
--   satB (¬ Q) = true.  Proposition 5.3 gives a fulfilling lasso through such
--     a state, Hintikka's lemma evaluates ¬ Q to 1 there, hence Q to 0, and
--     soundness says a derivation of Q would evaluate it to 1.  The certificate
--     is the lasso, together with the function turning any derivation of Q into
--     Empty.
--
-- The asymmetry the note insists on is visible in the types.  Neither branch is
-- obtained by refuting the other: `provable` never mentions a lasso, and
-- `countermodel` never mentions a derivation except to consume one.  In
-- particular the false branch returns a DERIVATION rather than an assertion of
-- unsatisfiability, which is what removes the classical step.

module LTL.Decide where

open import LTL.Hintikka public

------------------------------------------------------------------------
-- What a countermodel is

record LassoCountermodel (Q : Formula) : Set where
  constructor countermodel
  field
    start        : Val
    run          : Run (¬ Q) start
    startIn      : start ∈ Uinf (¬ Q)
    falseAtStart : eval (¬ Q) start run Q 0 ≡ false
    underivable  : ⊢ Q -> Empty

------------------------------------------------------------------------
-- Building one.  Names starting with cm (buildCM, cmEval, cmFrom, ...) are
-- about countermodels.
--
-- v0 contains ¬ Q and is a state, so by (S1) it does not contain Q;
-- Hintikka's lemma at stage 0 transfers that to the evaluation.

buildCM : (Q : Formula) (v0 : Val) -> v0 ∈ Uinf (¬ Q)
       -> valOf (¬ Q) v0 (¬ Q) ≡ true -> LassoCountermodel Q
buildCM Q v0 m ev = countermodel v0 r m evalFalse noDeriv
  where
    r : Run (¬ Q) v0
    r = runOf (¬ Q) v0 m (lasso (¬ Q) v0 m)

    -- (S1) at ¬ Q, the head of sub (¬ Q)
    valQ : valOf (¬ Q) v0 Q ≡ false
    valQ =
      ¬ᵇ-true (valOf (¬ Q) v0 Q)
        (trans (sym (⇔ᵇ-sound (valOf (¬ Q) v0 (¬ Q))
                              (¬ᵇ valOf (¬ Q) v0 Q)
                                  (stateOk (¬ Q) v0 m (sub-self (¬ Q)))))
               ev)

    evalFalse : eval (¬ Q) v0 r Q 0 ≡ false
    evalFalse =
      trans (sym (hintStart (¬ Q) v0 r Q (there (sub-self Q)))) valQ

    noDeriv : ⊢ Q -> Empty
    noDeriv d = true≢false (trans (sym (soundRun (¬ Q) v0 r d 0)) evalFalse)

------------------------------------------------------------------------
-- Theorem 6.1

decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
decide Q with satB (¬ Q) in e
... | false = inl (provable Q e)
... | true  =
  fromSig (any-true (λ v -> valOf (¬ Q) v (¬ Q)) (Uinf (¬ Q)) e)
  where
    fromSig : (Σ[ v ∈ Val ] v ∈ Uinf (¬ Q) ×
                                valOf (¬ Q) v (¬ Q) ≡ true)
           -> ⊢ Q ⊎ LassoCountermodel Q
    fromSig (v0 , m , ev) = inr (buildCM Q v0 m ev)

------------------------------------------------------------------------
-- Reading the answer

isProof : {A B : Set} -> A ⊎ B -> Bool
isProof = isInl

-- The run stores the states still to come before the cycle restarts, which is
-- the lasso's stem followed by its cycle; so the stem has length
-- length (cmRest Q c) - length (cmCycle Q c), and is empty exactly when the two
-- agree.
cmRest : (Q : Formula) -> LassoCountermodel Q -> List Val
cmRest Q c = Run.rest (LassoCountermodel.run c)

cmCycle : (Q : Formula) -> LassoCountermodel Q -> List Val
cmCycle Q c = Run.c0 r ∷ Run.c1 r
  where r = LassoCountermodel.run c

cmStart : (Q : Formula) -> LassoCountermodel Q -> Val
cmStart Q c = LassoCountermodel.start c

lassoOfDecide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
             -> Val × List Val × List Val
lassoOfDecide Q (inl d) = [] , [] , []
lassoOfDecide Q (inr c) = cmStart Q c , cmRest Q c , cmCycle Q c

------------------------------------------------------------------------
-- Looking at a derivation.
--
-- A derivation is a finite tree -- eleven constructors, of which only pc
-- carries a side condition, and that one a decidable boolean -- so one can
-- simply count it.  This is the inl branch's counterpart to traceOf
-- below: what decide returns on a provable formula is not the assertion that it
-- is provable but the proof, and this is how one looks at it.

-- One pass over the tree counts everything at once: the number of nodes, and
-- how many of them are modus ponens, generalisation, (Ind) and (PC).  (Ind)
-- is the interesting axiom: it is the one case of Theorem 4.1 that the loop
-- invariant needs, so counting it says whether the refutation went through
-- extractR2 at all.  (PC) only occurs in the certificates of LTL.ShortPC.

record DerivCounts : Set where
  constructor counts
  field
    size mps gens inds pcs : Nat

derivCounts : {A : Formula} -> ⊢ A -> DerivCounts
derivCounts p1       = counts 1 0 0 0 0
derivCounts p2       = counts 1 0 0 0 0
derivCounts p3       = counts 1 0 0 0 0
derivCounts k□       = counts 1 0 0 0 0
derivCounts k○       = counts 1 0 0 0 0
derivCounts exp      = counts 1 0 0 0 0
derivCounts ind      = counts 1 0 0 1 0
derivCounts lin      = counts 1 0 0 0 0
derivCounts (pc e)   = counts 1 0 0 0 1
derivCounts (mp d e) =
  counts (suc (size a + size b)) (suc (mps a + mps b)) (gens a + gens b)
         (inds a + inds b) (pcs a + pcs b)
  where
    open DerivCounts
    a = derivCounts d
    b = derivCounts e
derivCounts (gen d)  = counts (suc size) mps (suc gens) inds pcs
  where open DerivCounts (derivCounts d)

derivSize derivMP derivGen derivInd derivPC : {A : Formula} -> ⊢ A -> Nat
derivSize d = DerivCounts.size (derivCounts d)
derivMP   d = DerivCounts.mps  (derivCounts d)
derivGen  d = DerivCounts.gens (derivCounts d)
derivInd  d = DerivCounts.inds (derivCounts d)
derivPC   d = DerivCounts.pcs  (derivCounts d)

-- size, modus ponens steps, generalisations, (Ind) instances

countOf : (Q : Formula) -> Nat × Nat × Nat × Nat
countOf Q = onDec (decide Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> Nat × Nat × Nat × Nat
    onDec (inl d) = derivSize d , derivMP d , derivGen d , derivInd d
    onDec (inr c) = zero , zero , zero , zero

------------------------------------------------------------------------
-- Looking at a countermodel.
--
-- The bit vectors above are the states as the procedure stores them, read
-- against sub (¬ Q); they say everything but say it unreadably.  What one
-- actually wants to see is the truth value of a chosen formula at each stage of
-- the run, and the record already carries the run, so this is eval of LTL.Eval
-- applied at the successive stages.
--
-- Note the formula being evaluated is arbitrary: evalAt is total on all of
-- Formula, not only on sub (¬ Q) (see section 4d of FORMALISATION-PLAN.md),
-- so one may ask about a variable, about Q itself, or about anything else.

cmEval : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> Bool
cmEval Q c A i = eval (¬ Q) start run A i
  where open LassoCountermodel c

-- The values of A at the n stages i, i+1, ..., i+n-1.

cmFrom : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> Nat -> List Bool
cmFrom Q c A i zero    = []
cmFrom Q c A i (suc n) = cmEval Q c A i ∷ cmFrom Q c A (suc i) n

-- The truth values of A at stages 0,...,n-1 of the countermodel to Q, or the
-- empty list if Q turned out to be provable and there is no countermodel.

traceOf : (Q : Formula) -> Formula -> Nat -> List Bool
traceOf Q A n = onDec (decide Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> List Bool
    onDec (inl d) = []
    onDec (inr c) = cmFrom Q c A zero n

-- and the shape of the lasso: the run is  v0  followed by cmRest, whose tail is
-- the cycle, so it is periodic from stage  1 + |cmRest| - |cmCycle|  on, with
-- period |cmCycle|.

shapeOf : (Q : Formula) -> Nat × Nat
shapeOf Q = onDec (decide Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> Nat × Nat
    onDec (inl d) = zero , zero
    onDec (inr c) = length (cmRest Q c) , length (cmCycle Q c)

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Procedures.Answer -- what a decision procedure returns, Theorem 6.1 of
-- m4.tex.
--
--   ⊢ Q ⊎ LassoCountermodel Q
--
-- Either a derivation of Q, or a lasso countermodel: a run through states that
-- survive the elimination, on which Q evaluates to 0 at stage 0, together with
-- the function turning any derivation of Q into Empty.  Neither branch is
-- obtained by refuting the other: the derivation never mentions a lasso, and
-- the countermodel mentions a derivation only to consume one.  In particular
-- the provable branch returns a DERIVATION rather than an assertion of
-- unsatisfiability, which is what removes the classical step.
--
-- This module holds the record and the functions that read an answer: which
-- branch it is, the shape of the lasso, the truth values of a formula along the
-- run, and the size of a derivation.  LTL.Procedures.DecideSCC builds answers,
-- and LTL.Semantics reads them against LTL.Trusted.

module LTL.Procedures.Answer where

open import LTL.Countermodel.Hintikka public

------------------------------------------------------------------------
-- What a countermodel is.  Names starting with cm (cmEval, cmFrom, ...) are
-- about countermodels.

record LassoCountermodel (Q : Formula) : Set where
  constructor countermodel
  field
    start        : Val
    run          : Run (¬ Q) start
    startIn      : start ∈ Uinf (¬ Q)
    falseAtStart : eval (¬ Q) start run Q 0 ≡ false
    underivable  : ⊢ Q -> Empty

------------------------------------------------------------------------
-- Reading the answer

isProof : {A B : Set} -> A ⊎ B -> Bool
isProof = isInl

-- The countermodel, on the strength of the computed boolean: refl for the
-- second argument says the procedure was actually run.
countermodelFrom : {Q : Formula} (s : ⊢ Q ⊎ LassoCountermodel Q)
                -> isProof s ≡ false -> LassoCountermodel Q
countermodelFrom (inl d) ()
countermodelFrom (inr c) e = c

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

-- (start , rest , cycle) of the countermodel, or three empty lists for a proof.
lassoOf : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
       -> Val × List Val × List Val
lassoOf Q (inl d) = [] , [] , []
lassoOf Q (inr c) = cmStart Q c , cmRest Q c , cmCycle Q c

------------------------------------------------------------------------
-- Looking at a derivation.
--
-- A derivation is a finite tree -- eleven constructors, of which only pc
-- carries a side condition, and that one a decidable boolean -- so one can
-- simply count it.  What a procedure returns on a provable formula is not the
-- assertion that it is provable but the proof, and this is how one looks at
-- it.
--
-- One pass over the tree counts everything at once: the number of nodes, and
-- how many of them are modus ponens, generalisation, (Ind) and (PC).  (Ind)
-- is the interesting axiom: it is the one place the temporal argument enters
-- (extractBlock of LTL.SCC.SccExtract), so counting it says whether a
-- certificate needed the loop invariant at all.

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

------------------------------------------------------------------------
-- Looking at a countermodel.
--
-- The states are bit vectors read against sub (¬ Q); they say everything but
-- say it unreadably.  What one actually wants to see is the truth value of a
-- chosen formula at each stage of the run, and the record already carries the
-- run, so this is eval of LTL.Countermodel.Eval applied at the successive
-- stages.
--
-- The formula being evaluated is arbitrary: evalAt is total on all of Formula,
-- not only on sub (¬ Q), so one may ask about a variable, about Q itself, or
-- about anything else.

cmEval : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> Bool
cmEval Q c A i = eval (¬ Q) start run A i
  where open LassoCountermodel c

-- The values of A at the n stages i, i+1, ..., i+n-1.

cmFrom : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> Nat -> List Bool
cmFrom Q c A i zero    = []
cmFrom Q c A i (suc n) = cmEval Q c A i ∷ cmFrom Q c A (suc i) n

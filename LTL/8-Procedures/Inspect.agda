{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.8-Procedures.Inspect -- looking inside an answer of the decision
-- procedure: the shape of a lasso countermodel, the truth values of a formula
-- along its run, and the size of a derivation.
--
-- None of this is on the proof of decideCorrect; LTL.Pretty, the tests and
-- the benchmarks use it.  Names starting with cm (cmRest, cmTrace, ...) are
-- about countermodels.

module LTL.8-Procedures.Inspect where

open import LTL.8-Procedures.Answer
open import LTL.6-Countermodel.Lasso

------------------------------------------------------------------------
-- The states of a countermodel

-- The states after the start: the stem followed by the cycle (see cmShape).
cmRest : (Q : Formula) -> LassoCountermodel Q -> List Val
cmRest Q c = Lasso.rest (LassoCountermodel.lasso c)

-- The states of the cycle, which the run repeats forever.
cmCycle : (Q : Formula) -> LassoCountermodel Q -> List Val
cmCycle Q c = stretchStates (Lasso.loop (LassoCountermodel.lasso c))

------------------------------------------------------------------------
-- Looking at a derivation.  One pass over the tree counts the nodes, and how
-- many are modus ponens, generalisation, (Ind) and (PC).  (Ind) only enters
-- through extractBlock, so its count says whether a certificate needed a loop
-- invariant at all.

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
-- Looking at a countermodel: the truth value of a chosen formula at each stage
-- of the run, by eval of LTL.6-Countermodel.Lasso.  The formula is arbitrary,
-- since evalAt is total on all formulas.

cmEval : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> Bool
cmEval Q c A i = eval (¬ Q) start lasso A i
  where open LassoCountermodel c

-- The values of A at the n stages i, i+1, ..., i+n-1.

cmFrom : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> Nat -> List Bool
cmFrom Q c A i zero    = []
cmFrom Q c A i (suc n) = cmEval Q c A i ∷ cmFrom Q c A (suc i) n

-- The values of A at stages 0, ..., n-1 of the run.

cmTrace : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> List Bool
cmTrace Q c A = cmFrom Q c A zero

-- The shape of the lasso: its run is the start followed by cmRest, whose tail
-- is the cycle, so the stem has |cmRest| - |cmCycle| states (none when the two
-- agree) and the run is periodic from stage  1 + |cmRest| - |cmCycle|  on,
-- with period |cmCycle|.

cmShape : (Q : Formula) -> LassoCountermodel Q -> Nat × Nat
cmShape Q c = length (cmRest Q c) , length (cmCycle Q c)

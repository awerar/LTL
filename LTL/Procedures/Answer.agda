{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Procedures.Answer -- what the decision procedure returns,
--
--   ⊢ Q ⊎ LassoCountermodel Q
--
-- a derivation of Q, or a lasso countermodel: a lasso through states of Ust
-- (¬ Q) on which Q evaluates to false at stage 0.  LTL.Correct shows that
-- this rules out a derivation of Q (cmUnderivable).  Neither branch is
-- obtained by refuting the other, so no classical step is involved.
--
-- Also the functions that read an answer: which branch it is, the shape of
-- the lasso, the truth values of a formula along the run, and the size of a
-- derivation.

module LTL.Procedures.Answer where

open import LTL.States.Common public
open import LTL.Countermodel.Lasso
open import LTL.Countermodel.Eval

------------------------------------------------------------------------
-- What a countermodel is.  Names starting with cm (cmEval, cmFrom, ...) are
-- about countermodels.

record LassoCountermodel (Q : Formula) : Set where
  constructor countermodel
  field
    start        : Val
    lasso        : Lasso (¬ Q) start
    falseAtStart : eval (¬ Q) start lasso Q 0 ≡ false

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

-- The derivation, the same way, from an answer of decide or sccProof.
proofFrom : {A : Set} {Q : Formula}
         -> (s : A ⊎ ⊢ Q) -> isInl s ≡ false -> ⊢ Q
proofFrom (inl a) ()
proofFrom (inr d) e = d

-- The lasso stores the states still to come before the cycle restarts, which
-- is its stem followed by its cycle; so the stem has length
-- length (cmRest Q c) - length (cmCycle Q c), and is empty exactly when the two
-- agree.
cmRest : (Q : Formula) -> LassoCountermodel Q -> List Val
cmRest Q c = Lasso.rest (LassoCountermodel.lasso c)

cmCycle : (Q : Formula) -> LassoCountermodel Q -> List Val
cmCycle Q c = stretchStates (Lasso.loop (LassoCountermodel.lasso c))

cmStart : (Q : Formula) -> LassoCountermodel Q -> Val
cmStart Q c = LassoCountermodel.start c

-- (start , rest , cycle) of the countermodel.
cmLasso : (Q : Formula) -> LassoCountermodel Q -> Val × List Val × List Val
cmLasso Q c = cmStart Q c , cmRest Q c , cmCycle Q c

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
-- of the run, by eval of LTL.Countermodel.Eval.  The formula is arbitrary,
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
-- is the cycle, so it is periodic from stage  1 + |cmRest| - |cmCycle|  on,
-- with period |cmCycle|.

cmShape : (Q : Formula) -> LassoCountermodel Q -> Nat × Nat
cmShape Q c = length (cmRest Q c) , length (cmCycle Q c)

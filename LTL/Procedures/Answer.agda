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
-- Also which branch an answer is, as the Boolean LTL.Correct needs.  This
-- module holds only what decideCorrect depends on; the functions for looking
-- inside an answer are in LTL.Procedures.Inspect.

module LTL.Procedures.Answer where

open import LTL.States.Common public
open import LTL.Countermodel.Lasso

------------------------------------------------------------------------
-- What a countermodel is.

record LassoCountermodel (Q : Formula) : Set where
  constructor countermodel
  field
    start        : Val
    lasso        : Lasso (¬ Q) start
    falseAtStart : eval (¬ Q) start lasso Q 0 ≡ false

------------------------------------------------------------------------
-- Reading the answer

-- Did the procedure answer with a derivation?  This is the Boolean that
-- LTL.Correct hands to Statement as decideValid.
isProof : {Q : Formula} -> ⊢ Q ⊎ LassoCountermodel Q -> Bool
isProof = isInl

-- The countermodel, given that isProof says the answer is one.  On a closed
-- answer, such as decide Q for a concrete Q, the equation is refl.
countermodelFrom : {Q : Formula} (s : ⊢ Q ⊎ LassoCountermodel Q)
                -> isProof s ≡ false -> LassoCountermodel Q
countermodelFrom (inl d) ()
countermodelFrom (inr c) e = c

-- The derivation, given that isProof says the answer is one.
proofFrom : {Q : Formula} (s : ⊢ Q ⊎ LassoCountermodel Q)
         -> isProof s ≡ true -> ⊢ Q
proofFrom (inl d) e = d
proofFrom (inr c) ()

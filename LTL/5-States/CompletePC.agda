{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.CompletePC -- state completeness and (L5) with the
-- propositional bookkeeping discharged by (PC).
--
--   stateCompletePC = mpChain eventualities (pcTaut tautState)
--
-- proves ⊢ beta allStates in  1 + 46 |eventualities|  constructors: one pc
-- node, and one modus ponens against an instance of (S) per eventuality.
-- The step lemma (LTL.5-States.StepLemma) and provableSCC
-- (LTL.8-Procedures.Decide) use it.  betaElimPC does the same for the
-- elimination of beta over its disjuncts, which closes provableSCC.
--
-- The tautology is proved by BUILDING the witness state from the reading of
-- the atoms (skelRow, LTL.5-States.Taut), not by selecting it from the
-- disjunction over all valuations, which keeps the side condition small
-- enough to check by refl.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.5-States.CompletePC (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.Taut
open import LTL.5-States.Valuation P
open import LTL.5-States.State P

------------------------------------------------------------------------
-- The (S2) premise: □ A ⇒ A for every box-subformula of P, as the premises of
-- an implication chain (cheaper than a conjunction; see LTL.5-States.Taut).
-- mpChain (LTL.5-States.Taut) discharges each premise by an instance of (S).
-- (S2) is the one state condition a truth-table row does not satisfy for
-- free, since the skeleton reads □ A and A as unrelated atoms.

s2List : List Formula
s2List = map s2Formula eventualities

------------------------------------------------------------------------
-- State completeness.  Fix any reading ρ of the atoms.  The premises say
-- □ B ⇒ B holds under ρ for every □ B in sub P (S2At), so skelRow is a state
-- and its chi is a true disjunct of beta allStates.  No valuation is
-- enumerated: the reading IS the state.

-- The tautology: the (S2) premises of s2List imply beta allStates.

stateFormula : Formula
stateFormula = ⇒List s2List (beta allStates)

tautState : isTaut stateFormula ≡ true
tautState =
  isTaut-complete stateFormula λ ρ ->
    □Chain ρ eventualities (beta allStates) (betaSkel ρ P)

stateCompletePC : ⊢ beta allStates
stateCompletePC = mpChain eventualities (pcTaut tautState)

------------------------------------------------------------------------
-- (L5) the same way.  ⋁Elim costs 426 constructors per disjunct.  The
-- implication
--
--     (C1 ⇒ C) ⇒ ... ⇒ (Cn ⇒ C) ⇒ ((C1 ∨ ... ∨ Cn) ⇒ C)
--
-- is a tautology of its skeleton (taut⋁Elim), so betaElimPC is one pc node
-- and n modus ponens.  mpVals walks the valuations rather than the disjuncts,
-- so no inversion of  map chi  is needed.

mpVals : {C : Formula} (ws : List Val) {Z : Formula}
      -> (∀[ w ∈ ws ] ⊢ (chi w) ⇒ C)
      -> ⊢ ⇒List (map (C ⇐_) (map chi ws)) Z -> ⊢ Z
mpVals []       h d = d
mpVals (w ∷ ws) h d =
  mpVals ws (λ z m -> h z (there m)) (mp d (h w here))

betaElimPC : {C : Formula} (ws : List Val)
          -> (∀[ w ∈ ws ] ⊢ (chi w) ⇒ C)
          -> ⊢ (beta ws) ⇒ C
betaElimPC {C} ws h = mpVals ws h (pcTaut (taut⋁Elim (map chi ws) C))

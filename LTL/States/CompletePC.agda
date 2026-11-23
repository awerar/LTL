{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.CompletePC -- state completeness and (L5) with the
-- propositional bookkeeping discharged by (PC).
--
--   stateCompletePC = mpChain eventualities (pc tautState)
--
-- proves ⊢ beta St in  1 + 46 |eventualities|  constructors: one pc
-- node, and one modus ponens against an instance of (T) per eventuality.
-- The step lemma (LTL.States.StepLemma) and provableSCC
-- (LTL.Procedures.Decide) use it.  betaElimPC does the same for the
-- elimination of beta over its disjuncts, which closes provableSCC.
--
-- The tautology is proved by BUILDING the witness state from the truth-table
-- row (skelVec, LTL.States.Taut), not by selecting it from the disjunction
-- over all valuations, which keeps the side condition small enough to check
-- by refl.

open import LTL.Syntax.Formula using (Formula)

module LTL.States.CompletePC (P : Formula) where

open import LTL.States.Common
open import LTL.States.Taut
open import LTL.States.State P

------------------------------------------------------------------------
-- The (S2) premise: □ A ⇒ A for every box-subformula of P, as the premises of
-- an implication chain (cheaper than a conjunction; see LTL.States.Taut).
-- mpChain (LTL.States.Taut) discharges each premise by an instance of (T).
-- (S2) is the one state condition a truth-table row does not satisfy for
-- free, since the skeleton reads □ A and A as unrelated atoms.

s2List : List Formula
s2List = map s2Fml eventualities

------------------------------------------------------------------------
-- State completeness.  Fix the atom list of the implication and any row a of
-- its truth table.  The premises say □ B ⇒ B holds in row a for every □ B in
-- sub P (S2At), so skelVec is a state and its chi is a true disjunct of
-- beta St.  No valuation is enumerated: the row IS the state.

-- The tautology: the (S2) premises of s2List imply beta St.

stateFml : Formula
stateFml = ⇒List s2List (beta St)

tautState : isTaut stateFml ≡ true
tautState =
  isTaut-intro stateFml λ a ->
    □Chain (atomsOf stateFml) a eventualities (beta St)
           (betaSkel (atomsOf stateFml) a P)

stateCompletePC : ⊢ beta St
stateCompletePC = mpChain eventualities (pc tautState)

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
betaElimPC {C} ws h = mpVals ws h (pc (taut⋁Elim (map chi ws) C))

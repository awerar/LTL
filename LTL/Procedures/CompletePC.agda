{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Procedures.CompletePC -- state completeness and (L5) with the
-- propositional bookkeeping discharged by (PC).
--
--   stateCompletePC P = mpChain (□Args (sub P)) (pc (tautState P))
--
-- proves ⊢ beta P (St P) in  1 + 46 |□Args (sub P)|  constructors: one pc
-- node, and one modus ponens against an instance of (T) per eventuality.
-- stateComplete (LTL.States.Complete), which splits over all 2^|sub P|
-- valuations, has 296839 for □ p ⇒ p.  betaElimPC does the same for the
-- elimination of beta over its disjuncts.  Both close the derivation of
-- provableSCC (LTL.SCC.SccExtract).
--
-- The tautology is proved by BUILDING the witness state from the truth-table
-- row (skelVec, LTL.States.Taut), not by selecting it from the disjunction
-- over all valuations, which keeps the side condition small enough to check
-- by refl.

module LTL.Procedures.CompletePC where

open import LTL.States.Complete public
open import LTL.States.Taut     public

------------------------------------------------------------------------
-- The (S2) premise: □ A ⇒ A for every box-subformula of P, as the premises of
-- an implication chain (cheaper than a conjunction; see LTL.States.Taut).  Each
-- premise is discharged by an instance of (T), □Elim of LTL.Rules.Temporal.
-- (S2) is the one state condition a truth-table row does not satisfy for
-- free, since the skeleton reads □ A and A as unrelated atoms.

s2List : Formula -> List Formula
s2List P = map s2Fml (□Args (sub P))

-- The derivation half of □Chain: one modus ponens against one instance of
-- (T) per premise, left to right.

mpChain : (As : List Formula) {C : Formula}
       -> ⊢ ⇒List (map s2Fml As) C -> ⊢ C
mpChain []       d = d
mpChain (A ∷ As) d = mpChain As (mp d □Elim)

------------------------------------------------------------------------
-- State completeness.  Fix the atom list of the implication and any row a of
-- its truth table.  The premises say □ B ⇒ B holds in row a for every □ B in
-- sub P (□Ok), so skelVec is a state and its chi is a true disjunct of
-- beta P (St P).  No valuation is enumerated: the row IS the state.

-- The tautology: the (S2) premises of s2List imply beta P (St P).

module _ (P : Formula) where

  stateFml : Formula
  stateFml = ⇒List (s2List P) (beta P (St P))

  tautState : isTaut stateFml ≡ true
  tautState =
    all-intro (λ a -> valFrom (atomsOf stateFml) a stateFml)
              (allVecs (length (atomsOf stateFml)))
              row
    where
      Ats : List Formula
      Ats = atomsOf stateFml

      row : {a : Val} -> a ∈ allVecs (length Ats)
         -> valFrom Ats a stateFml ≡ true
      row {a} m =
        □Chain Ats a (□Args (sub P)) (beta P (St P))
                 (λ g -> betaSkel Ats a P (λ B mb -> g B (□Args-of (sub P) mb)))

  stateCompletePC : ⊢ beta P (St P)
  stateCompletePC = mpChain (□Args (sub P)) (pc tautState)

------------------------------------------------------------------------
-- (L5) the same way.  ⋁Elim costs 426 constructors per disjunct.  The
-- implication
--
--     (C1 ⇒ C) ⇒ ... ⇒ (Cn ⇒ C) ⇒ ((C1 ∨ ... ∨ Cn) ⇒ C)
--
-- is a tautology of its skeleton (taut⋁Elim), so betaElimPC is one pc node
-- and n modus ponens.  mpVals walks the valuations rather than the disjuncts,
-- so no inversion of  map (chi P)  is needed.

⋁⇒Fml : List Formula -> Formula -> Formula
⋁⇒Fml Cs C = ⇒List (map (C ⇐_) Cs) (⋁ Cs ⇒ C)

taut⋁Elim : (Cs : List Formula) (C : Formula)
         -> isTaut (⋁⇒Fml Cs C) ≡ true
taut⋁Elim Cs C =
  all-intro (λ a -> valFrom (atomsOf (⋁⇒Fml Cs C)) a (⋁⇒Fml Cs C))
            (allVecs (length (atomsOf (⋁⇒Fml Cs C))))
            row
  where
    Ats : List Formula
    Ats = atomsOf (⋁⇒Fml Cs C)

    row : {a : Val} -> a ∈ allVecs (length Ats)
       -> valFrom Ats a (⋁⇒Fml Cs C) ≡ true
    row {a} m =
      ⇒Chain Ats a (map (C ⇐_) Cs) (⋁ Cs ⇒ C)
               (λ g -> ⋁ElimTrue Ats a Cs C (λ mD -> g (memMap (C ⇐_) mD)))

mpVals : (P : Formula) {C : Formula} (ws : List Val) {Z : Formula}
      -> ((w : Val) -> w ∈ ws -> ⊢ (chi P w) ⇒ C)
      -> ⊢ ⇒List (map (C ⇐_) (map (chi P) ws)) Z -> ⊢ Z
mpVals P []       h d = d
mpVals P (w ∷ ws) h d =
  mpVals P ws (λ z m -> h z (there m)) (mp d (h w here))

betaElimPC : (P : Formula) {C : Formula} (ws : List Val)
          -> ((w : Val) -> w ∈ ws -> ⊢ (chi P w) ⇒ C)
          -> ⊢ (beta P ws) ⇒ C
betaElimPC P {C} ws h = mpVals P ws h (pc (taut⋁Elim (map (chi P) ws) C))

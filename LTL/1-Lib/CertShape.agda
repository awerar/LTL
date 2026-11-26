{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.CertShape -- the shape of a certificate of LTL.1-Lib.FairGraph:
-- the kinds of its steps, in removal order: one per Reason, then emptied.
--
-- Off the proof path: the decision procedure never looks at a certificate's
-- shape.  The tests do, at Nat in LTL.9-Tests.GraphExamples and at the state
-- graph through sccShape of LTL.8-Procedures.Inspect.
--
-- FairGraph is opened unapplied, so certShape reads its graph off the Cert
-- and CertStep does not depend on it: the shapes of two graphs have the same
-- type.

module LTL.1-Lib.CertShape where

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.DecEq using (DecEq)
open import LTL.1-Lib.FairGraph using (Cert; cNil; cRemove; sink; unfair)

private variable
  Node : Set
  eq   : DecEq Node
  G    : Node -> Node -> Bool
  fs   : List (Node -> Bool)
  ws   : List Node

data CertStep : Set where
  removedSink removedUnfair emptied : CertStep

certShape : Cert eq G fs ws -> List CertStep
certShape cNil                         = emptied ∷ []
certShape (cRemove _ (sink _) c)       = removedSink ∷ certShape c
certShape (cRemove _ (unfair _ _ _) c) = removedUnfair ∷ certShape c

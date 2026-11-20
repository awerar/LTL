{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Walk -- walks of the state graph, and persistence along
-- them.
--
-- A walk is LTL.SCC.Graph's Trail at the edge test step P:
--
--   Trail us v ws x   --  v -> ws_1 -> ... -> ws_n = x, every ws_i in us
--
-- This module is the one application of LTL.SCC.Graph, and re-exports it, so
-- the lassos and the graph search share one path type.  A P-module gets
-- Trail us v zs w, Cert fs ws, ... from here; an importer outside, opening it
-- unapplied, gets Trail P us v zs w, Cert P fs ws, ...
--
-- The main lemma is trailPersist: along a walk, an eventuality pending at the
-- start is either fulfilled at a state visited, or still pending at the end.

open import LTL.Syntax.Formula using (Formula)

module LTL.Countermodel.Walk (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Step P
open import LTL.States.Closure P
import LTL.SCC.Graph as Graph

open Graph _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl step public

------------------------------------------------------------------------
-- Fulfilment along a walk

-- A fails at a state the walk v ∷ ws visits.

record Fulfil (A : Formula) (v : Val) (ws : List Val) : Set where
  constructor ful
  field
    at      : Val
    visited : at ∈ v ∷ ws
    fails   : valOf at A ≡ false

-- A Fulfil proof carries over to a walk with one more state in front.

fulfilCons : {A : Formula} {v w : Val} {ws : List Val}
          -> Fulfil A w ws -> Fulfil A v (w ∷ ws)
fulfilCons (ful z m q) = ful z (there m) q

------------------------------------------------------------------------
-- Persistence along a walk.  If □ A is pending at v then, walking to x,
-- either A fails somewhere on the way (the eventuality is fulfilled) or □ A
-- is still pending at x.  Each step is `persist`, i.e. (T3).

trailPersist : (us : List Val) (A : Formula) -> □ A ∈ sub P
            -> {v : Val} {ws : List Val} {x : Val} -> Trail us v ws x
            -> valOf v (□ A) ≡ false
            -> Fulfil A v ws ⊎ valOf x (□ A) ≡ false
trailPersist us A mb tNil e = inr e
trailPersist us A mb (tCons {v} {w} {ws} {x} mw st wk) e with valOf v A in ea
... | false = inl (ful v here ea)
... | true  =
  sumElim (λ f -> inl (fulfilCons f)) inr
          (trailPersist us A mb wk (persist v w A mb st e ea))

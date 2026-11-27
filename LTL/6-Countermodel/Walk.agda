{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.6-Countermodel.Walk -- walks of the state graph, and persistence along
-- them.
--
-- A walk is LTL.1-Lib.Graph's Trail at the edge test step P:
--
--   Trail v zs x   --  v -> zs_1 -> ... -> zs_n = x
--
-- and that its states lie in a set us is the separate fact  zs ⊆ us .
--
-- This module is the one application of LTL.1-Lib.Graph and LTL.1-Lib.FairGraph,
-- and re-exports both, so the lassos and the graph search share one path
-- type.  A P-module gets Trail v zs w, Cert fs ws, ... from here; an importer
-- outside, opening it unapplied, gets Trail P v zs w, Cert P fs ws, ...
--
-- The main lemma is trailPersist: along a walk, an eventuality pending at the
-- start is either fulfilled at a state visited, or still pending at the end.

open import LTL.2-Syntax.Formula using (Formula)

module LTL.6-Countermodel.Walk (P : Formula) where

open import LTL.5-States.Common
open import LTL.5-States.State P
open import LTL.5-States.Step P
open import LTL.5-States.Closure P
import LTL.1-Lib.Graph as Graph
import LTL.1-Lib.FairGraph as FairGraph

open Graph valEq step public
open FairGraph valEq step public

------------------------------------------------------------------------
-- Fulfilment along a walk

-- A fails at a state the walk v ∷ zs visits.

record Fulfil (A : Formula) (v : Val) (zs : List Val) : Set where
  constructor ful
  field
    at      : Val
    visited : at ∈ v ∷ zs
    fails   : valOf at A ≡ false

-- A Fulfil proof carries over to a walk with one more state in front.

fulfilCons : {A : Formula} {v w : Val} {zs : List Val}
          -> Fulfil A w zs -> Fulfil A v (w ∷ zs)
fulfilCons (ful z m q) = ful z (there m) q

-- ... and to a walk that visits more.

fulfilWiden : {A : Formula} {v : Val} {xs ys : List Val}
           -> xs ⊆ ys -> Fulfil A v xs -> Fulfil A v ys
fulfilWiden subset (ful z here      q) = ful z here q
fulfilWiden subset (ful z (there m) q) = ful z (there (subset z m)) q

------------------------------------------------------------------------
-- Persistence along a walk.  If □ A is pending at v then, walking to x,
-- either A fails somewhere on the way (the eventuality is fulfilled) or □ A
-- is still pending at x.  Each step is `persist`, i.e. (T3).

trailPersist : (A : Formula) -> □ A ∈ sub P
            -> {v : Val} {zs : List Val} {x : Val} -> Trail v zs x
            -> valOf v (□ A) ≡ false
            -> Fulfil A v zs ⊎ valOf x (□ A) ≡ false
trailPersist A mb tNil e = inr e
trailPersist A mb (tCons {v} {w} {zs} {x} st wk) e with valOf v A in ea
... | false = inl (ful v here ea)
... | true  =
  [ (λ f -> inl (fulfilCons f)) , inr ]
    (trailPersist A mb wk (persist v w A mb st e ea))

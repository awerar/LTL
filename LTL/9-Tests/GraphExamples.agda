{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.9-Tests.GraphExamples -- the computational checks of LTL.1-Lib.Graph and
-- LTL.1-Lib.FairGraph, at Node = Nat with _≡ⁿ_.
--
-- Both are parameterised by their node type, so their checks live here.
-- Nothing in the graph layer reads a node except through the equality test,
-- so the same fairGraph that runs on valuations runs here on numbers.  The
-- edge test is left as a parameter, so every name takes the graph first.

module LTL.9-Tests.GraphExamples where

open import LTL.1-Lib.Prelude
open import LTL.1-Lib.DecEq using (DecEq)

natEq : DecEq Nat
natEq = record { _≡ᵛ_ = _≡ⁿ_ ; ≡ᵛ-sound = ≡ⁿ-sound ; ≡ᵛ-refl = ≡ⁿ-refl }

open import LTL.1-Lib.Graph natEq
open import LTL.1-Lib.FairGraph natEq
open import LTL.1-Lib.Nodes natEq using (_∈ᵛ_; Edges; Pred)
open import LTL.1-Lib.CertShape

------------------------------------------------------------------------
-- The first graph: a = 0 and b = 1, with a -> b and b -> b.  b's component
-- is terminal and non-trivial, a's is not, so the answer depends only on which
-- vertex the fairness predicate asks for.

gA : Nat
gA = 0

gB : Nat
gB = 1

gVs : List Nat
gVs = gA ∷ gB ∷ []

gE : Edges
gE v w = w ≡ⁿ gB

reach-gA : reachSet gE gVs gA ≡ gB ∷ gA ∷ []
reach-gA = refl

-- findTerminal moves from a to b, and stays at b.

term-gA : TerminalIn.r (findTerminal gE gVs {gA} here) ≡ gB
term-gA = refl

term-gB : TerminalIn.r (findTerminal gE gVs {gB} (there here)) ≡ gB
term-gB = refl

scc-gB : sccOf gE gVs gB ≡ gB ∷ []
scc-gB = refl

-- Asking for b is fair: the cycle b -> b meets it.

fair-gB : isInl (fairGraph gE gVs ((λ v -> v ≡ⁿ gB) ∷ []) gA here) ≡ true
fair-gB = refl

-- Asking for a is not: a is transient, so the only recurrent component misses
-- the predicate and the certificate branch is taken.

fair-gA : isInl (fairGraph gE gVs ((λ v -> v ≡ⁿ gA) ∷ []) gA here) ≡ false
fair-gA = refl

------------------------------------------------------------------------
-- A second graph:  p -> q ,  q -> s ,  s -> q .
--
-- p is transient and {q,s} is recurrent, so findTerminal moves the representative
-- once, the circuit has two legs, and the certificate uses both reasons: it
-- removes {q,s} as unfair, then p as a sink, and ends in cNil.

gP : Nat
gP = 0

gQ : Nat
gQ = 1

gS : Nat
gS = 2

gVs2 : List Nat
gVs2 = gP ∷ gQ ∷ gS ∷ []

gE2 : Edges
gE2 v w = (v ≡ⁿ gP) ∧ᵇ (w ≡ⁿ gQ) ∨ᵇ
          (v ≡ⁿ gQ) ∧ᵇ (w ≡ⁿ gS) ∨ᵇ
          (v ≡ⁿ gS) ∧ᵇ (w ≡ⁿ gQ)

-- findTerminal moves from p to s, in the terminal component {q,s}, and
-- stays at q.

term-gP : TerminalIn.r (findTerminal gE2 gVs2 {gP} here) ≡ gS
term-gP = refl

term-gQ : TerminalIn.r (findTerminal gE2 gVs2 {gQ} (there here)) ≡ gQ
term-gQ = refl

scc-gQ : map (λ z -> z ∈ᵛ sccOf gE2 gVs2 gQ) gVs2 ≡ false ∷ true ∷ true ∷ []
scc-gQ = refl

-- Once {q,s} is removed, p is a sink, and its component is p alone (sinkOnly).

scc-sinkP : sccOf gE2 (gP ∷ []) gP ≡ gP ∷ []
scc-sinkP = refl

-- The lasso the fair branch returns.  findTerminal settles on s, so the stem is
-- p -> q -> s and the loop is s -> q -> s.  With the predicates "is q" and "is
-- s", the cycle is one leg per predicate followed by the bare loop, each leg
-- the loop again then out to the witness and back:
--
--   q s q s   for "is q" ,   q s   for "is s" ,   q s   the loop
--
-- The loop goes in FRONT so that the witness is a vertex the leg visits.  It
-- is not the shortest fair cycle; q s would do.

loopCycle : {G : Edges} {vs : List Nat} {fs : List Pred} {v : Nat}
         -> FairLoop G vs fs v -> List Nat
loopCycle {G} l = Loop.cycle G (Circuit.loop (FairLoop.fairCircuit l))

cycleOf : {G : Edges} {vs : List Nat} {fs : List Pred} {v : Nat}
       -> FairLoop G vs fs v ⊎ Cert G fs (reachSet G vs v) -> List Nat
cycleOf (inl l) = loopCycle l
cycleOf (inr c) = []

stemOf : {G : Edges} {vs : List Nat} {fs : List Pred} {v : Nat}
      -> FairLoop G vs fs v ⊎ Cert G fs (reachSet G vs v) -> List Nat
stemOf (inl l) = Reaches.via (FairLoop.stem l)
stemOf (inr c) = []

fairQS : FairLoop gE2 gVs2 ((λ v -> v ≡ⁿ gQ) ∷ (λ v -> v ≡ⁿ gS) ∷ []) gP ⊎
         Cert gE2 ((λ v -> v ≡ⁿ gQ) ∷ (λ v -> v ≡ⁿ gS) ∷ [])
              (reachSet gE2 gVs2 gP)
fairQS = fairGraph gE2 gVs2 ((λ v -> v ≡ⁿ gQ) ∷ (λ v -> v ≡ⁿ gS) ∷ []) gP here

fair-QS : isInl fairQS ≡ true
fair-QS = refl

stem-QS : stemOf fairQS ≡ gQ ∷ gS ∷ []
stem-QS = refl

cycle-QS : cycleOf fairQS ≡ gQ ∷ gS ∷ gQ ∷ gS ∷ gQ ∷ gS ∷ gQ ∷ gS ∷ []
cycle-QS = refl

-- And the unfair side: nothing recurrent meets "is p".

fair-P : isInl (fairGraph gE2 gVs2 ((λ v -> v ≡ⁿ gP) ∷ []) gP here) ≡ false
fair-P = refl

-- The certificate it returns instead, as the list of its steps:  unfair,
-- sink, cNil .  The component {q,s} misses "is p" and is refuted first, and
-- only then is p a sink: p is refuted because its successor already was.

certSteps : {G : Edges} {vs : List Nat} {fs : List Pred} {v : Nat}
         -> FairLoop G vs fs v ⊎ Cert G fs (reachSet G vs v) -> List CertStep
certSteps (inl l) = []
certSteps (inr c) = certShape c

cert-P : certSteps (fairGraph gE2 gVs2 ((λ v -> v ≡ⁿ gP) ∷ []) gP here) ≡
         removedUnfair ∷ removedSink ∷ emptied ∷ []
cert-P = refl

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.GraphExamples -- the computational checks of LTL.Graph, run on natural
-- numbers.
--
-- LTL.Graph is parameterised by its node type, so it cannot run its own
-- checks; they live here, at  Node = Nat  with  _≡ⁿ_ .  That is also the point
-- of the module: the same fairGraph that LTL.SccLasso runs on valuations runs
-- here on numbers, with the same answers, because nothing in the graph layer
-- reads a node except through the equality test.  The vertices were one- and
-- two-bit valuations before the graph layer was made generic; the lists below
-- are unchanged, since the searches depend only on the order of the vertex
-- list.
--
-- Fast; nothing else imports it.

module LTL.GraphExamples where

open import LTL.Prelude
open import LTL.Graph _≡ⁿ_ ≡ⁿ-sound ≡ⁿ-refl
open import LTL.Nodes _≡ⁿ_ ≡ⁿ-sound ≡ⁿ-refl using (_∈ᵛ_; Edges; Pred)

------------------------------------------------------------------------
-- The first graph.
--
-- Two vertices,  a = 0  and  b = 1 , with every edge pointing at b: a -> b and
-- b -> b.  So b's component is terminal and non-trivial, a's is not terminal,
-- and the answer depends only on which vertex the fairness predicate asks for.
-- The g in gA, gB, gVs, gE, ... stands for "graph"; they are test data only.

gA : Nat
gA = 0

gB : Nat
gB = 1

gVs : List Nat
gVs = gA ∷ gB ∷ []

gE : Edges
gE v w = w ≡ⁿ gB

reach-gA : reachSet gVs gE gA ≡ gB ∷ gA ∷ []
reach-gA = refl

term-gA : isTerminal gVs gE gA ≡ false
term-gA = refl

term-gB : isTerminal gVs gE gB ≡ true
term-gB = refl

scc-gB : sccOf gVs gE gB ≡ gB ∷ []
scc-gB = refl

-- Asking for b is fair: the cycle b -> b meets it.

fair-gB : isInl (fairGraph gVs gE ((λ v -> v ≡ⁿ gB) ∷ []) gA here) ≡ true
fair-gB = refl

-- Asking for a is not: a is transient, so the only recurrent component misses
-- the predicate and the certificate branch is taken.

fair-gA : isInl (fairGraph gVs gE ((λ v -> v ≡ⁿ gA) ∷ []) gA here) ≡ false
fair-gA = refl

------------------------------------------------------------------------
-- A second graph, which exercises everything the first does not.
--
--   p -> q ,  q -> s ,  s -> q
--
-- p is transient and {q,s} is a two-vertex recurrent component, so: findTerm
-- has to move the representative once (p's component is not terminal), the
-- circuit has two legs to concatenate rather than none, and on the unfair side
-- the certificate uses all three of its constructors -- cBlock removes {q,s},
-- then cSink removes p, which only becomes a sink once the component is gone,
-- then cNil.

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

term-gP : isTerminal gVs2 gE2 gP ≡ false
term-gP = refl

term-gQ : isTerminal gVs2 gE2 gQ ≡ true
term-gQ = refl

scc-gQ : map (λ z -> z ∈ᵛ sccOf gVs2 gE2 gQ) gVs2 ≡ false ∷ true ∷ true ∷ []
scc-gQ = refl

-- The lasso the fair branch returns, read off in full.
--
-- findTerm settles on s as the representative, so the stem is  p -> q -> s  and
-- the loop is  s -> q -> s .  Two fairness predicates, "is q" and "is s"; the
-- cycle is one leg per predicate followed by the bare loop, each leg being the
-- loop again then out to the witness and back --
--
--   q s q s   for "is q" ,   q s   for "is s" ,   q s   the loop
--
-- and the leg carries the loop in FRONT precisely so that the out-half is
-- non-empty and the witness is therefore a vertex the leg VISITS, not merely an
-- endpoint; for "is s" the out-half and the back-half are both empty, since the
-- witness is the representative, and only the leading loop makes that leg a
-- cycle through s at all.  This is the SCC construction choosing witnesses in
-- its own order, and it is not the shortest fair cycle -- q s would do.

loopCycle : {vs : List Nat} {G : Edges} {fs : List Pred} {v : Nat}
         -> FairLoop vs G fs v -> List Nat
loopCycle (fairLoop r st cy ts t nn wit) = cy

cycleOf : {vs : List Nat} {G : Edges} {fs : List Pred} {v : Nat}
       -> FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v) -> List Nat
cycleOf (inl l) = loopCycle l
cycleOf (inr c) = []

stemOf : {vs : List Nat} {G : Edges} {fs : List Pred} {v : Nat}
      -> FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v) -> List Nat
stemOf (inl (fairLoop r st cy ts t nn wit)) = st
stemOf (inr c)                              = []

fairQS : FairLoop gVs2 gE2 ((λ v -> v ≡ⁿ gQ) ∷ (λ v -> v ≡ⁿ gS) ∷ []) gP ⊎
         Cert gE2 ((λ v -> v ≡ⁿ gQ) ∷ (λ v -> v ≡ⁿ gS) ∷ [])
              (reachSet gVs2 gE2 gP)
fairQS = fairGraph gVs2 gE2 ((λ v -> v ≡ⁿ gQ) ∷ (λ v -> v ≡ⁿ gS) ∷ []) gP here

fair-QS : isInl fairQS ≡ true
fair-QS = refl

stem-QS : stemOf fairQS ≡ gQ ∷ gS ∷ []
stem-QS = refl

cycle-QS : cycleOf fairQS ≡ gQ ∷ gS ∷ gQ ∷ gS ∷ gQ ∷ gS ∷ gQ ∷ gS ∷ []
cycle-QS = refl

-- And the unfair side: nothing recurrent meets "is p".

fair-P : isInl (fairGraph gVs2 gE2 ((λ v -> v ≡ⁿ gP) ∷ []) gP here) ≡ false
fair-P = refl

-- The certificate it returns instead, as the list of its steps: 2 for cBlock,
-- 1 for cSink, 0 for cNil.  It is  cBlock, cSink, cNil  -- the component {q,s}
-- is refuted first because it misses "is p", and only then is p a sink, which is
-- the whole point of the backwards induction: p is refuted BECAUSE its successor
-- already was.  Reading this off is what certAll does with a formula attached.
-- certShape is LTL.Graph's, since LTL.SccExtract reads certificates the same
-- way.

certSteps : {vs : List Nat} {G : Edges} {fs : List Pred} {v : Nat}
         -> FairLoop vs G fs v ⊎ Cert G fs (reachSet vs G v) -> List Nat
certSteps (inl l) = []
certSteps (inr c) = certShape c

cert-P : certSteps (fairGraph gVs2 gE2 ((λ v -> v ≡ⁿ gP) ∷ []) gP here) ≡
         2 ∷ 1 ∷ 0 ∷ []
cert-P = refl

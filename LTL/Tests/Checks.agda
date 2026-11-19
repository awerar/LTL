{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Tests.Checks -- the computational checks of the core modules, by refl.
--
-- Each section is headed by the module whose definitions it exercises, in
-- dependency order, and holds what used to be that module's trailing check
-- section: small example formulas (benAri, ◇P, bnb, c5, ...), the states and
-- lassos the procedure computes for them, and the answers of decideSCC.
-- Keeping them here keeps the proof modules short and
-- their typechecking fast; this module is checked on its own, like
-- LTL.Tests.GraphExamples, which holds the checks of LTL.SCC.Graph.

module LTL.Tests.Checks where

open import LTL.Pretty    public
open import LTL.Procedures.DecideSCC public
open import LTL.Correct   public
import LTL.Trusted as T

------------------------------------------------------------------------
-- LTL.Syntax.Sub

-- sub produces duplicates.
--
-- This is the point recorded in FORMALISATION-PLAN.md section 0.  Ben-Ari's own
-- example is already an instance: for  □ p ⇒ ○ □ p  we get
--
--   [ □ p ⇒ ○ □ p , □ p , p , ○ □ p , □ p , p ]
--
-- of length 6, with  □ p  and  p  each occurring twice.  A valuation as a
-- List Bool of length 6 therefore assigns them independent bits, which is why
-- isState (G5) carries a duplicate-coherence clause.

benAri : Formula
benAri = □ (var zero) ⇒ ○ □ (var zero)

subBenAri-length : length (sub benAri) ≡ 6
subBenAri-length = refl

subBenAri-dup : nth (sub benAri) 1 ⊥ ≡ nth (sub benAri) 4 ⊥
subBenAri-dup = refl

------------------------------------------------------------------------
-- LTL.States.Val

-- Sanity checks by computation.
--
-- sub benAri has length 6 (LTL.Syntax.Sub), so there are 2^6 = 64 valuations to
-- filter in G5.

allVecs-three : length (allVecs 3) ≡ 8
allVecs-three = refl

allVecs-benAri : length (allVecs (length (sub benAri))) ≡ 64
allVecs-benAri = refl

-- Positions 1 and 4 of sub benAri are the same formula (□ p), so a valuation
-- disagreeing there yields a chi containing both □ p and ¬ □ p.  This
-- is exactly what the coherence clause of G5 will exclude.

badVal : Val
badVal = true ∷ true ∷ true ∷ true ∷ false ∷ true ∷ []

badVal-length : length badVal ≡ length (sub benAri)
badVal-length = refl

------------------------------------------------------------------------
-- LTL.States.State

-- Computational checks.
--
-- ◇ p is  ¬ □ ¬ p , so sub is
--   [ ¬ □ ¬ p , □ ¬ p , ¬ p , p ]
-- with no duplicates.  The constraints are v0 = not v1, v1 implies v2,
-- v2 = not v3, leaving three states -- the same three as Example 1 of
-- the lecture 15 notes (see LTL.Benchmarks.Lecture), where Sub(Fp) = {Fp, p} and the
-- excluded combination is Fp false with p true.

◇P : Formula
◇P = ◇ (var zero)

St-◇P : length (St ◇P) ≡ 3
St-◇P = refl

-- The negation of Ben-Ari's formula, the input the decision procedure is
-- actually run on.  Here sub has length 7 with □ p and p each duplicated,
-- so 128 valuations are filtered to 6 states.

¬BenAri : Formula
¬BenAri = ¬ benAri

St-¬BenAri : length (allVecs (length (sub ¬BenAri))) ≡ 128
St-¬BenAri = refl

St-¬BenAri-count : length (St ¬BenAri) ≡ 6
St-¬BenAri-count = refl

-- The duplicate-incoherent valuation of LTL.States.Val is rejected, as intended.

badVal-rejected : isState benAri badVal ≡ false
badVal-rejected = refl

------------------------------------------------------------------------
-- LTL.States.Step

-- Computational checks.
--
-- For ◇ p the three states of LTL.States.State are, writing the bits of
-- [ ¬ □ ¬ p , □ ¬ p , ¬ p , p ] :
--
--   sPending = 1 0 1 0   (p fails now, ◇ p still pending)
--   sFulfil  = 1 0 0 1   (p holds now)
--   sSink    = 0 1 1 0   (◇ p false, so p fails forever)
--
-- in the order of St ◇P.
--
-- Every state has at least one successor, so no state is removed by (R1).

◇P-succ-counts : map (λ v -> length (succs ◇P (St ◇P) v)) (St ◇P) ≡
                      2 ∷ 3 ∷ 1 ∷ []
◇P-succ-counts = refl

-- For ¬ benAri the six states are, in the order allVecs produces them
-- (true first, so lexicographic with 1 before 0), writing the bits of
-- [ ¬ I , I , □ p , p , ○ □ p , □ p , p ]  with I = □ p ⇒ ○ □ p:
--
--   E = 1 0 1 1 0 1 1     □ p true, ○ □ p false  -- the only state
--                                                        -- containing ¬ benAri
--   F = 0 1 1 1 1 1 1
--   D = 0 1 0 1 1 0 1
--   C = 0 1 0 1 0 0 1
--   B = 0 1 0 0 1 0 0
--   A = 0 1 0 0 0 0 0
--
-- E and D have NO successor, so both are removed by (R1) alone.

¬BenAri-succ-counts
  : map (λ v -> length (succs ¬BenAri (St ¬BenAri) v)) (St ¬BenAri) ≡
    0 ∷ 2 ∷ 0 ∷ 4 ∷ 2 ∷ 4 ∷ []
¬BenAri-succ-counts = refl

------------------------------------------------------------------------
-- LTL.Elimination.Elim

-- Checkpoint C1.
--
-- ◇ p is satisfiable: all three states survive.

Uinf-◇P : length (Uinf ◇P) ≡ 3
Uinf-◇P = refl

-- ¬ benAri is unsatisfiable.  The procedure explores Ust, the closure of the
-- states containing its input (G30), not St: of the six states of
-- LTL.States.Step only E contains ¬ benAri, and E has no successor, so the
-- closure stops there and the first round removes it by (R1).  Ben-Ari's own
-- example therefore never reaches (R2) in this formulation: (T2) makes  □ p
-- together with  ¬ ○ □ p  contradict in a single step, where his tableau
-- needed the loop invariant because it carried  ○ □ p  as an explicit member
-- of the closure.

Ust-¬BenAri : length (Ust ¬BenAri) ≡ 1
Ust-¬BenAri = refl

Uinf-¬BenAri : length (Uinf ¬BenAri) ≡ 0
Uinf-¬BenAri = refl

------------------------------------------------------------------------
-- A small example that does exercise (R2).
--
--   bnb  =  □ p ⇒ □ ○ p
--
-- is provable, and unlike benAri its refutation genuinely needs the loop
-- invariant.  The closure of the states containing ¬ bnb has just two
-- members: □ p and ¬ □ ○ p force p, and (T2) and (T3) carry both along every
-- step, so the only freedom left is the bit at ○ p.  The state with ○ p false
-- has no successor and goes by (R1) in the first round; the other one loops to
-- itself, and once its (R1)-victim is gone the eventuality that □ ○ p leaves
-- pending is fulfilled at no reachable state, so it goes by (R2) in the
-- second.  Nothing survives.
--
-- The SCC certificate of LTL.SCC.SccExtract removes the two states in the same
-- order (shape-bnb below), and its block step, extractBlock, is the copy of
-- (R2): the loop invariant, (Ind) and all.

bnb : Formula
bnb = □ (var zero) ⇒ □ ○ (var zero)

¬Bnb : Formula
¬Bnb = ¬ bnb

Ust-¬Bnb : length (Ust ¬Bnb) ≡ 2
Ust-¬Bnb = refl

round1-¬Bnb : length (elimRound ¬Bnb (Ust ¬Bnb)) ≡ 1
round1-¬Bnb = refl

round2-¬Bnb : length (elimRound ¬Bnb (elimRound ¬Bnb (Ust ¬Bnb))) ≡ 0
round2-¬Bnb = refl

Uinf-¬Bnb : length (Uinf ¬Bnb) ≡ 0
Uinf-¬Bnb = refl

------------------------------------------------------------------------
-- LTL.SCC.SccExtract

-- Checkpoints.
--
-- Ben-Ari's formula and  □ p ⇒ □ ○ p , decided by the SCC route.  These are
-- the real test: both derivations are produced, so the graph search, certAll,
-- extractR1 and extractBlock all run.

scc-benAri : isInl (sccProof benAri) ≡ false
scc-benAri = refl

benAriProofSCC : ⊢ benAri
benAriProofSCC = proofFrom (sccProof benAri) refl

scc-bnb : isInl (sccProof bnb) ≡ false
scc-bnb = refl

bnbProofSCC : ⊢ bnb
bnbProofSCC = proofFrom (sccProof bnb) refl

-- The certificates themselves, read as their removal orders.  For Ben-Ari's
-- formula Ust has one state, it is a sink, and the certificate is  cSink, cNil
-- -- only extractR1 runs.
--
-- For  □ p ⇒ □ ○ p  Ust has two states and the certificate is
-- cSink, cBlock, cNil : one state has no successor inside the set and leaves
-- first, and only then is what remains a component whose eventuality is
-- unfulfillable, refuted by extractBlock in a single use of (Ind).  That is the
-- same order as the elimination's (round1-¬Bnb, round2-¬Bnb above), reached by
-- a different route, and it is why bnb is the example that matters:
-- extractBlock, the copy of (R2), is on the path from here to bnbProofSCC.

shape-benAri : sccShape benAri ≡ removedSink ∷ emptied ∷ []
shape-benAri = refl

shape-bnb : sccShape bnb ≡ removedSink ∷ removedBlock ∷ emptied ∷ []
shape-bnb = refl

-- and the positive side, to show the search is not simply always certifying:
-- ◇ p is satisfiable, so its state set has a fair component.

scc-◇P : isInl (sccGraph ◇P) ≡ true
scc-◇P = refl

------------------------------------------------------------------------
-- LTL.Procedures.DecideSCC

-- Checkpoint C4.
--
-- Ben-Ari's formula and  □ p ⇒ □ ○ p  are decided in the affirmative: the
-- certificate is a derivation in the system L.

decideSCC-benAri : isProof (decideSCC benAri) ≡ true
decideSCC-benAri = refl

decideSCC-bnb : isProof (decideSCC bnb) ≡ true
decideSCC-bnb = refl

-- The certificates are short.  For (T),  □ p ⇒ p , the derivation has 55
-- constructors, 5 of them pc nodes: Lemma 2.6 is one pc node and one modus
-- ponens per eventuality (stateCompletePC), (L5) over the states is one more
-- (betaElimPC), and each state is one pc node or a refutation.  The derivation
-- of Lemma 2.6 alone by case split (stateComplete) has 296839.

axT-size : derivSize (proofFrom (sccProof (□ var zero ⇒ var zero)) refl)
           ∷ derivPC (proofFrom (sccProof (□ var zero ⇒ var zero)) refl)
           ∷ [] ≡ 55 ∷ 5 ∷ []
axT-size = refl

-- ◇ p is decided in the negative, and the certificate is a lasso.
--
-- The procedure runs on  ¬ ◇ p = ¬ ¬ □ ¬ p , whose five subformulas are
--
--    ¬ ◇ p ,  ◇ p ,  □ ¬ p ,  ¬ p ,  p
--
-- and the countermodel starts at the state  1 0 1 1 0 : ◇ p fails, □ ¬ p
-- holds, p does not.  That state loops to itself, so the countermodel is the
-- obvious one, p false forever.  The cycle is recorded as two copies of the
-- loop: the SCC construction starts from the bare loop and prepends one leg
-- per eventuality, and here the leg is the loop again.

◇P-cmState : Val
◇P-cmState = true ∷ false ∷ true ∷ true ∷ false ∷ []

decideSCC-◇P : isProof (decideSCC ◇P) ≡ false
decideSCC-◇P = refl

decideSCC-◇P-lasso : lassoOf ◇P (decideSCC ◇P) ≡
                     (◇P-cmState , ◇P-cmState ∷ ◇P-cmState ∷ [] ,
                                   ◇P-cmState ∷ ◇P-cmState ∷ [])
decideSCC-◇P-lasso = refl

◇P-shape : shapeOf ◇P ≡ (2 , 2)
◇P-shape = refl

-- p fails at every stage, and so does ◇ p, the formula decided.  traceOf goes
-- through eval of LTL.Countermodel.Eval, the semantics soundness is proved
-- against, so "◇ p is false at stage 0" and the ⊢ Q -> Empty field of the
-- record are the same fact seen from the two ends -- Hintikka's lemma at stage
-- 0 against soundness.

◇P-trace : traceOf ◇P (var zero) 4 ≡ false ∷ false ∷ false ∷ false ∷ []
◇P-trace = refl

◇P-input : traceOf ◇P ◇P 2 ≡ false ∷ false ∷ []
◇P-input = refl

◇P-underivable : ⊢ ◇P -> Empty
◇P-underivable =
  LassoCountermodel.underivable (countermodelFrom (decideSCC ◇P) refl)

------------------------------------------------------------------------
-- Checkpoint C5.
--
--   □ (p ∨ q) ⇒ □ p ∨ □ q
--
-- is NOT valid, and decideSCC says so with a lasso.  Sub of its negation has
-- length 13, so the state space is nominally 8192 vectors; the five atoms are
-- □ (p ∨ q), p, q, □ p, □ q, so 32 assignments are built, 17 of them are
-- states, and the closure of those containing the negation has 8 members.
--
-- The countermodel it returns is the expected one.  Writing a state as the
-- pair (p , q) -- the other eleven bits are determined -- the run is
--
--   (0,1)  ->  (1,0)  ->  (1,1)  ->  (1,1)  ->  ...
--
-- so p or q holds at every stage, while p fails at stage 0 and q at stage 1.
-- Hence □ (p ∨ q) holds and neither □ p nor □ q does.  The cycle is the
-- single state at which both hold forever, recorded four times (the loop and
-- one leg for each of the three eventualities), and the stem is the first two
-- states and one copy of the cycle.

-- The atoms p and q of C5 (c for C5).

cp : Formula
cp = var zero

cq : Formula
cq = var (suc zero)

c5 : Formula
c5 = □ (cp ∨ cq) ⇒ □ cp ∨ □ cq

-- q, not p
c5q : Val
c5q = true  ∷ false ∷ true ∷ true ∷ true  ∷ false ∷ true
   ∷ false ∷ true  ∷ false ∷ false ∷ false ∷ true ∷ []

-- p, not q
c5p : Val
c5p = false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ false
   ∷ true  ∷ false ∷ true  ∷ true  ∷ false ∷ false ∷ []

-- p and q, both forever
c5pq : Val
c5pq = false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ true
    ∷ true  ∷ false ∷ true ∷ true ∷ true  ∷ true ∷ []

decideSCC-c5 : isProof (decideSCC c5) ≡ false
decideSCC-c5 = refl

decideSCC-c5-lasso : lassoOf c5 (decideSCC c5) ≡
                     (c5q , c5p ∷ c5pq ∷ c5pq ∷ c5pq ∷ c5pq ∷ c5pq ∷ [] ,
                            c5pq ∷ c5pq ∷ c5pq ∷ c5pq ∷ [])
decideSCC-c5-lasso = refl

c5-p : traceOf c5 cp 4 ≡ false ∷ true ∷ true ∷ true ∷ []
c5-p = refl

c5-q : traceOf c5 cq 4 ≡ true ∷ false ∷ true ∷ true ∷ []
c5-q = refl

------------------------------------------------------------------------
-- LTL.Pretty

-- Checks: the printer on the identity (L1), the abbreviations, and a
-- countermodel.

pretty-identity : renderDeriv (⇒Refl {var zero}) ≡
  "⊢ p ⇒ p\n\n1  P2       (p ⇒ (p ⇒ p) ⇒ p) ⇒ (p ⇒ p ⇒ p) ⇒ p ⇒ p\n2  P1       p ⇒ (p ⇒ p) ⇒ p\n3  MP 1, 2  (p ⇒ p ⇒ p) ⇒ p ⇒ p\n4  P1       p ⇒ p ⇒ p\n5  MP 3, 4  p ⇒ p\n"
pretty-identity = refl

pretty-sugar :
  showFormula (□ var 0 ⇒ var 0 ∧ ○ var 0 ∧ ○ □ var 0)
   ∷ showFormula (◇ var 0 ∧ ◇ var 1 ⇒ ◇ (var 0 ∧ var 1))
   ∷ showFormula (○ ¬ var 0 ⇔ ¬ ○ var 0)
   ∷ showFormula (¬ var 0 ⇒ var 1)
   ∷ showFormula (¬ (var 0 ⇒ var 1))
   ∷ showFormulaRaw (◇ var 0)
   ∷ [] ≡
     "□ p ⇒ p ∧ ○ p ∧ ○ □ p"
   ∷ "◇ p ∧ ◇ q ⇒ ◇ (p ∧ q)"
   ∷ "○ ¬ p ⇔ ¬ ○ p"
   ∷ "¬ p ⇒ q"
   ∷ "¬ (p ⇒ q)"
   ∷ "¬ □ ¬ p"
   ∷ []
pretty-sugar = refl

pretty-countermodel : prove (var 0 ⇒ □ var 0) ≡
  "⊬ p ⇒ □ p\n\nCountermodel: the formula is false at time 0.  Variables true at each time:\n    0  {p}\n    1  {}\n    2  {p}\n    3  {p}\n    4  {p}\nthen repeating forever:\n    5  {p}\n    6  {p}\n  (back to time 5)\n"
pretty-countermodel = refl

------------------------------------------------------------------------
-- LTL.Correct

-- The Boolean answer of the DecisionProcedure: (Exp)'s first conjunct is
-- valid, ◇ p is not.

correct-answers :
  T.DecisionProcedure.decideValid decideSCCCorrect (□ var 0 ⇒ var 0)
  ∷ T.DecisionProcedure.decideValid decideSCCCorrect (◇ var 0)
  ∷ [] ≡ true ∷ false ∷ []
correct-answers = refl

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Tests.Checks -- the computational checks of the core modules, by refl.
--
-- One section per module, in dependency order, with small example formulas
-- (benAri, ◇P, bnb, c5, ...), the states and lassos computed for them, and the
-- answers of decideSCC.  LTL.Tests.GraphExamples holds the checks of
-- LTL.SCC.Graph.

module LTL.Tests.Checks where

open import LTL.Pretty    public
open import LTL.Procedures.DecideSCC public
open import LTL.Correct   public
import LTL.Trusted as T

------------------------------------------------------------------------
-- LTL.Syntax.Sub

-- sub produces duplicates.  For Ben-Ari's  □ p ⇒ ○ □ p  it is
--
--   [ □ p ⇒ ○ □ p , □ p , p , ○ □ p , □ p , p ]
--
-- with □ p and p each twice, which is why isState has a coherence clause.

benAri : Formula
benAri = □ (var zero) ⇒ ○ □ (var zero)

subBenAri-length : length (sub benAri) ≡ 6
subBenAri-length = refl

subBenAri-dup : nth (sub benAri) 1 ⊥ ≡ nth (sub benAri) 4 ⊥
subBenAri-dup = refl

------------------------------------------------------------------------
-- LTL.States.Val

-- sub benAri has length 6, so there are 64 valuations to filter.

allVecs-three : length (allVecs 3) ≡ 8
allVecs-three = refl

allVecs-benAri : length (allVecs (length (sub benAri))) ≡ 64
allVecs-benAri = refl

-- Positions 1 and 4 of sub benAri are both □ p, so a valuation disagreeing
-- there gives a chi containing both □ p and ¬ □ p.  Coherence excludes it.

badVal : Val
badVal = true ∷ true ∷ true ∷ true ∷ false ∷ true ∷ []

badVal-length : length badVal ≡ length (sub benAri)
badVal-length = refl

------------------------------------------------------------------------
-- LTL.States.State

-- ◇ p is  ¬ □ ¬ p , so sub is  [ ¬ □ ¬ p , □ ¬ p , ¬ p , p ]  with no
-- duplicates.  The constraints v0 = not v1, v1 implies v2, v2 = not v3 leave
-- three states.

◇P : Formula
◇P = ◇ (var zero)

St-◇P : length (St ◇P) ≡ 3
St-◇P = refl

-- The negation of Ben-Ari's formula, the input the procedure runs on: sub has
-- length 7, and 128 valuations are filtered to 6 states.

¬BenAri : Formula
¬BenAri = ¬ benAri

St-¬BenAri : length (allVecs (length (sub ¬BenAri))) ≡ 128
St-¬BenAri = refl

St-¬BenAri-count : length (St ¬BenAri) ≡ 6
St-¬BenAri-count = refl

-- The incoherent valuation is rejected.

badVal-rejected : isState benAri badVal ≡ false
badVal-rejected = refl

------------------------------------------------------------------------
-- LTL.States.Step

-- For ◇ p the three states, writing the bits of  [ ¬ □ ¬ p , □ ¬ p , ¬ p , p ] ,
-- are, in the order of St ◇P:
--
--   1 0 1 0   p fails now, ◇ p still pending
--   1 0 0 1   p holds now
--   0 1 1 0   ◇ p false, so p fails forever
--
-- Every state has a successor.

◇P-succ-counts : map (λ v -> length (succs ◇P (St ◇P) v)) (St ◇P) ≡
                      2 ∷ 3 ∷ 1 ∷ []
◇P-succ-counts = refl

-- For ¬ benAri the six states are, in the order allVecs produces them, writing
-- the bits of  [ ¬ I , I , □ p , p , ○ □ p , □ p , p ]  with I = □ p ⇒ ○ □ p:
--
--   E = 1 0 1 1 0 1 1     □ p true, ○ □ p false: the only state containing
--                         ¬ benAri
--   F = 0 1 1 1 1 1 1
--   D = 0 1 0 1 1 0 1
--   C = 0 1 0 1 0 0 1
--   B = 0 1 0 0 1 0 0
--   A = 0 1 0 0 0 0 0
--
-- E and D have no successor.

¬BenAri-succ-counts
  : map (λ v -> length (succs ¬BenAri (St ¬BenAri) v)) (St ¬BenAri) ≡
    0 ∷ 2 ∷ 0 ∷ 4 ∷ 2 ∷ 4 ∷ []
¬BenAri-succ-counts = refl

------------------------------------------------------------------------
-- LTL.Elimination.Elim

-- ◇ p is satisfiable: all three states survive.

Uinf-◇P : length (Uinf ◇P) ≡ 3
Uinf-◇P = refl

-- ¬ benAri is unsatisfiable.  Ust holds only E, the one state containing
-- ¬ benAri; E has no successor, so the first round removes it by (R1).  (T2)
-- makes  □ p  and  ¬ ○ □ p  contradict in a single step, so no loop
-- invariant is needed.

Ust-¬BenAri : length (Ust ¬BenAri) ≡ 1
Ust-¬BenAri = refl

Uinf-¬BenAri : length (Uinf ¬BenAri) ≡ 0
Uinf-¬BenAri = refl

------------------------------------------------------------------------
-- A small example that does exercise (R2):
--
--   bnb  =  □ p ⇒ □ ○ p
--
-- The closure of the states containing ¬ bnb has two members, differing only
-- at ○ p.  The one with ○ p false has no successor and goes by (R1) in the
-- first round; the other loops to itself, and then the eventuality □ ○ p
-- leaves pending is fulfilled nowhere, so it goes by (R2) in the second.  The
-- SCC certificate removes them in the same order (shape-bnb below).

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

-- Ben-Ari's formula and  □ p ⇒ □ ○ p , decided by the graph search.  Both
-- derivations are produced, so the search, certAll, extractR1 and
-- extractBlock all run.

scc-benAri : isInl (sccProof benAri) ≡ false
scc-benAri = refl

benAriProofSCC : ⊢ benAri
benAriProofSCC = proofFrom (sccProof benAri) refl

scc-bnb : isInl (sccProof bnb) ≡ false
scc-bnb = refl

bnbProofSCC : ⊢ bnb
bnbProofSCC = proofFrom (sccProof bnb) refl

-- The certificates, as removal orders.  For Ben-Ari's formula Ust has one
-- state, a sink, so only extractR1 runs.  For  □ p ⇒ □ ○ p  one state is a
-- sink and leaves first; what remains is a block whose eventuality is
-- unfulfillable, refuted by extractBlock with one use of (Ind).

shape-benAri : sccShape benAri ≡ removedSink ∷ emptied ∷ []
shape-benAri = refl

shape-bnb : sccShape bnb ≡ removedSink ∷ removedBlock ∷ emptied ∷ []
shape-bnb = refl

-- and the positive side: ◇ p is satisfiable, so its state set has a fair
-- component.

scc-◇P : isInl (sccGraph ◇P) ≡ true
scc-◇P = refl

------------------------------------------------------------------------
-- LTL.Procedures.DecideSCC

-- Ben-Ari's formula and  □ p ⇒ □ ○ p  are valid: the answer is a derivation.

decideSCC-benAri : isProof (decideSCC benAri) ≡ true
decideSCC-benAri = refl

decideSCC-bnb : isProof (decideSCC bnb) ≡ true
decideSCC-bnb = refl

-- The certificates are short.  For (T),  □ p ⇒ p , the derivation has 55
-- constructors, 5 of them pc nodes: state completeness is one pc node and one
-- modus ponens per eventuality (stateCompletePC), (L5) over the states one
-- more (betaElimPC), and each state is one pc node or a refutation.
-- stateComplete alone, by case split, has 296839.

axT-size : derivSize (proofFrom (sccProof (□ var zero ⇒ var zero)) refl)
           ∷ derivPC (proofFrom (sccProof (□ var zero ⇒ var zero)) refl)
           ∷ [] ≡ 55 ∷ 5 ∷ []
axT-size = refl

-- ◇ p is not valid, and the answer is a lasso.  The procedure runs on
-- ¬ ◇ p = ¬ ¬ □ ¬ p , with subformulas  ¬ ◇ p , ◇ p , □ ¬ p , ¬ p , p .
-- The countermodel is the state  1 0 1 1 0  (◇ p fails, □ ¬ p holds) looping
-- to itself: p false forever.  The cycle holds two copies of the loop, since
-- the SCC construction prepends one leg per eventuality to the bare loop.

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

-- p fails at every stage, and so does ◇ p, the formula decided.  traceOf uses
-- the evaluation soundness is proved against, so this and the ⊢ Q -> Empty
-- field of the record are the same fact from two ends.

◇P-trace : traceOf ◇P (var zero) 4 ≡ false ∷ false ∷ false ∷ false ∷ []
◇P-trace = refl

◇P-input : traceOf ◇P ◇P 2 ≡ false ∷ false ∷ []
◇P-input = refl

◇P-underivable : ⊢ ◇P -> Empty
◇P-underivable =
  LassoCountermodel.underivable (countermodelFrom (decideSCC ◇P) refl)

------------------------------------------------------------------------
-- c5 = □ (p ∨ q) ⇒ □ p ∨ □ q  is not valid.  sub of its negation has length
-- 13 (8192 vectors); its five atoms give 32 candidates, 17 of them states, and
-- the closure of those containing the negation has 8 members.
--
-- Writing a state as the pair (p , q) (the other bits are determined), the
-- run is
--
--   (0,1)  ->  (1,0)  ->  (1,1)  ->  (1,1)  ->  ...
--
-- so p or q holds at every stage, while p fails at stage 0 and q at stage 1.
-- The cycle is the state where both hold, recorded four times (the loop and
-- one leg per eventuality).

-- The atoms p and q of c5.

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

-- The printer on the identity (L1), on the abbreviations, and on a
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

-- The Boolean answer of the DecisionProcedure: (T) is valid, ◇ p is not.

correct-answers :
  T.DecisionProcedure.decideValid decideSCCCorrect (□ var 0 ⇒ var 0)
  ∷ T.DecisionProcedure.decideValid decideSCCCorrect (◇ var 0)
  ∷ [] ≡ true ∷ false ∷ []
correct-answers = refl

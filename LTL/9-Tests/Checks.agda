{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.9-Tests.Checks -- the computational checks of the core modules, by refl.
--
-- One section per module, in dependency order, with small example formulas
-- (benAri, ◇P, bnb, c5, ...), the states and lassos computed for them, and the
-- answers of decide.  LTL.9-Tests.GraphExamples holds the checks of
-- LTL.1-Lib.Graph and LTL.1-Lib.FairGraph.

module LTL.9-Tests.Checks where

open import LTL.Pretty    public
open import LTL.8-Procedures.Everything public
open import LTL.8-Procedures.Correct public
import LTL.Statement as S

------------------------------------------------------------------------
-- LTL.2-Syntax.Formula (subformulas)

-- sub produces duplicates.  For Ben-Ari's  □ p ⇒ ○ □ p  it is
--
--   [ □ p ⇒ ○ □ p , □ p , p , ○ □ p , □ p , p ]
--
-- with □ p and p each twice.  A state is a row over the atoms, which have no
-- repetition, so the duplicates only repeat literals of chi.

benAri : Formula
benAri = □ (var zero) ⇒ ○ □ (var zero)

subBenAri-length : length (sub benAri) ≡ 6
subBenAri-length = refl

subBenAri-dup : nth (sub benAri) 1 ⊥ ≡ nth (sub benAri) 4 ⊥
subBenAri-dup = refl

------------------------------------------------------------------------
-- LTL.2-Syntax.Skel (atoms)

-- The atoms of sub benAri, in order of first occurrence, are the positions of
-- its states: 8 rows, not the 64 vectors over sub benAri.  Its one
-- eventuality p is listed once, though □ p occurs twice.

atomsBenAri : stateAtoms benAri ≡ □ var zero ∷ var zero ∷ ○ □ var zero ∷ []
atomsBenAri = refl

allVecs-three : length (allVecs 3) ≡ 8
allVecs-three = refl

evBenAri : eventualities benAri ≡ var zero ∷ []
evBenAri = refl

------------------------------------------------------------------------
-- LTL.5-States.State

-- ◇ p is  ¬ □ ¬ p , whose atoms are  [ □ ¬ p , p ] .  (S2) excludes the row
-- with □ ¬ p and p both true, leaving three states.

◇P : Formula
◇P = ◇ (var zero)

St-◇P : length (St ◇P) ≡ 3
St-◇P = refl

-- The negation of Ben-Ari's formula, the input the procedure runs on: its 3
-- atoms give 8 rows, and (S2) filters them to 6 states.

¬BenAri : Formula
¬BenAri = ¬ benAri

St-¬BenAri : length (allVecs (length (stateAtoms ¬BenAri))) ≡ 8
St-¬BenAri = refl

St-¬BenAri-count : length (St ¬BenAri) ≡ 6
St-¬BenAri-count = refl

------------------------------------------------------------------------
-- LTL.5-States.Step

-- For ◇ p the three states, writing the bits of  [ □ ¬ p , p ] , are, in the
-- order of St ◇P:
--
--   1 0   ◇ p false, so p fails forever
--   0 1   p holds now
--   0 0   p fails now, ◇ p still pending
--
-- Every state has a successor.

◇P-succ-counts : map (λ v -> length (succs ◇P (St ◇P) v)) (St ◇P) ≡
                      1 ∷ 3 ∷ 2 ∷ []
◇P-succ-counts = refl

-- For ¬ benAri the six states are, in the order allVecs produces them, writing
-- the bits of the atoms  [ □ p , p , ○ □ p ] :
--
--   F = 1 1 1
--   E = 1 1 0     □ p true, ○ □ p false: the only state containing ¬ benAri
--   D = 0 1 1
--   C = 0 1 0
--   B = 0 0 1
--   A = 0 0 0
--
-- E and D have no successor.

¬BenAri-succ-counts
  : map (λ v -> length (succs ¬BenAri (St ¬BenAri) v)) (St ¬BenAri) ≡
    2 ∷ 0 ∷ 0 ∷ 4 ∷ 2 ∷ 4 ∷ []
¬BenAri-succ-counts = refl

------------------------------------------------------------------------
-- LTL.5-States.Closure

-- ¬ benAri is unsatisfiable.  Ust holds only E, the one state containing
-- ¬ benAri, and E has no successor.  (T2) makes  □ p  and  ¬ ○ □ p
-- contradict in a single step, so no loop invariant is needed.

Ust-¬BenAri : length (Ust ¬BenAri) ≡ 1
Ust-¬BenAri = refl

-- A small example with an unfulfillable eventuality:
--
--   bnb  =  □ p ⇒ □ ○ p
--
-- The closure of the states containing ¬ bnb has two members, differing only
-- at ○ p.  The one with ○ p false has no successor; the other loops to
-- itself, and the eventuality □ ○ p leaves pending is fulfilled nowhere
-- (shape-bnb below).

bnb : Formula
bnb = □ (var zero) ⇒ □ ○ (var zero)

¬Bnb : Formula
¬Bnb = ¬ bnb

Ust-¬Bnb : length (Ust ¬Bnb) ≡ 2
Ust-¬Bnb = refl

------------------------------------------------------------------------
-- LTL.8-Procedures.Decide: the graph search

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
-- LTL.8-Procedures.Decide

-- Ben-Ari's formula and  □ p ⇒ □ ○ p  are valid: the answer is a derivation.
-- Both derivations are produced, so the search, certAll, extractR1 and
-- extractBlock all run.

decide-benAri : isProof (decide benAri) ≡ true
decide-benAri = refl

benAriProof : ⊢ benAri
benAriProof = proofFrom (decide benAri) refl

decide-bnb : isProof (decide bnb) ≡ true
decide-bnb = refl

bnbProof : ⊢ bnb
bnbProof = proofFrom (decide bnb) refl

-- The certificates are short.  For (S),  □ p ⇒ p , the derivation has 55
-- constructors, 5 of them pc nodes: state completeness is one pc node and one
-- modus ponens per eventuality (stateCompletePC), (L5) over the states one
-- more (betaElimPC), and each state is one pc node or a refutation.

axT-size : derivSize (proofFrom (decide (□ var zero ⇒ var zero)) refl)
           ∷ derivPC (proofFrom (decide (□ var zero ⇒ var zero)) refl)
           ∷ [] ≡ 55 ∷ 5 ∷ []
axT-size = refl

-- ◇ p is not valid, and the answer is a lasso.  The procedure runs on
-- ¬ ◇ p = ¬ ¬ □ ¬ p , whose atoms are  □ ¬ p , p .  The countermodel is the
-- state  1 0  (□ ¬ p holds, p fails) looping to itself: p false forever.  The cycle holds two copies of the loop, since
-- the SCC construction prepends one leg per eventuality to the bare loop.

◇P-cmState : Val
◇P-cmState = true ∷ false ∷ []

decide-◇P : isProof (decide ◇P) ≡ false
decide-◇P = refl

-- The countermodel itself; refl says the procedure answered with one.

◇P-cm : LassoCountermodel ◇P
◇P-cm = countermodelFrom (decide ◇P) refl

-- (start , rest , cycle) of a countermodel, so one refl checks the whole lasso.
cmLasso : (Q : Formula) -> LassoCountermodel Q -> Val × List Val × List Val
cmLasso Q c = LassoCountermodel.start c , cmRest Q c , cmCycle Q c

decide-◇P-lasso : cmLasso ◇P ◇P-cm ≡
                  (◇P-cmState , ◇P-cmState ∷ ◇P-cmState ∷ [] ,
                                ◇P-cmState ∷ ◇P-cmState ∷ [])
decide-◇P-lasso = refl

◇P-shape : cmShape ◇P ◇P-cm ≡ (2 , 2)
◇P-shape = refl

-- p fails at every stage, and so does ◇ p, the formula decided.  cmTrace uses
-- the evaluation that LTL.8-Procedures.Correct carries over to Statement's
-- semantics, so this and cmUnderivable are the same fact from two ends.

◇P-trace : cmTrace ◇P ◇P-cm (var zero) 4 ≡ false ∷ false ∷ false ∷ false ∷ []
◇P-trace = refl

◇P-input : cmTrace ◇P ◇P-cm ◇P 2 ≡ false ∷ false ∷ []
◇P-input = refl

◇P-underivable : ⊢ ◇P -> Empty
◇P-underivable =
  cmUnderivable ◇P ◇P-cm

------------------------------------------------------------------------
-- c5 = □ (p ∨ q) ⇒ □ p ∨ □ q  is not valid.  sub of its negation has length
-- 13, but only five atoms,  [ □ (p ∨ q) , p , q , □ p , □ q ] : 32 rows, 17
-- of them states, and the closure of those containing the negation has 8
-- members.
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
c5q = true ∷ false ∷ true ∷ false ∷ false ∷ []

-- p, not q, and p forever
c5p : Val
c5p = true ∷ true ∷ false ∷ true ∷ false ∷ []

-- p and q, both forever
c5pq : Val
c5pq = true ∷ true ∷ true ∷ true ∷ true ∷ []

decide-c5 : isProof (decide c5) ≡ false
decide-c5 = refl

c5-cm : LassoCountermodel c5
c5-cm = countermodelFrom (decide c5) refl

decide-c5-lasso : cmLasso c5 c5-cm ≡
                  (c5q , c5p ∷ c5pq ∷ c5pq ∷ c5pq ∷ c5pq ∷ c5pq ∷ [] ,
                         c5pq ∷ c5pq ∷ c5pq ∷ c5pq ∷ [])
decide-c5-lasso = refl

c5-p : cmTrace c5 c5-cm cp 4 ≡ false ∷ true ∷ true ∷ true ∷ []
c5-p = refl

c5-q : cmTrace c5 c5-cm cq 4 ≡ true ∷ false ∷ true ∷ true ∷ []
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
-- LTL.8-Procedures.Correct

-- The Boolean answer of the DecisionProcedure: (S) is valid, ◇ p is not.

correct-answers :
  S.DecisionProcedure.decideValid decideCorrect (□ var 0 ⇒ var 0)
  ∷ S.DecisionProcedure.decideValid decideCorrect (◇ var 0)
  ∷ [] ≡ true ∷ false ∷ []
correct-answers = refl

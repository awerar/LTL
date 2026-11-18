{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Checks -- the computational checks of the core modules, by refl.
--
-- Each section is headed by the module whose definitions it exercises, in
-- dependency order, and holds what used to be that module's trailing check
-- section: small example formulas (benAri, ◇P, bnb, c5, ...), the states and
-- lassos the procedures compute for them, and the answers of decide,
-- decideSCC and decidePC.  Keeping them here keeps the proof modules short and
-- their typechecking fast; this module is checked on its own, like
-- LTL.GraphExamples, which holds the checks of LTL.Graph.

module LTL.Checks where

open import LTL.Pretty    public
open import LTL.DecideSCC public
open import LTL.Correct   public
import LTL.Trusted as T

------------------------------------------------------------------------
-- LTL.Sub

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
-- LTL.Val

-- Sanity checks by computation.
--
-- sub benAri has length 6 (LTL.Sub), so there are 2^6 = 64 valuations to
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
-- LTL.State

-- Computational checks.
--
-- ◇ p is  ¬ □ ¬ p , so sub is
--   [ ¬ □ ¬ p , □ ¬ p , ¬ p , p ]
-- with no duplicates.  The constraints are v0 = not v1, v1 implies v2,
-- v2 = not v3, leaving three states -- the same three as Example 1 of
-- the lecture 15 notes (see LTL.Lecture), where Sub(Fp) = {Fp, p} and the
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

-- The duplicate-incoherent valuation of LTL.Val is rejected, as intended.

badVal-rejected : isState benAri badVal ≡ false
badVal-rejected = refl

------------------------------------------------------------------------
-- LTL.Step

-- Computational checks.
--
-- For ◇ p the three states of LTL.State are, writing the bits of
-- [ ¬ □ ¬ p , □ ¬ p , ¬ p , p ] :
--
--   sPending = 1 0 1 0   (p fails now, ◇ p still pending)
--   sFulfil  = 1 0 0 1   (p holds now)
--   sSink    = 0 1 1 0   (◇ p false, so p fails forever)
--
-- in the order of St ◇P, and with the names LTL.Lasso gives them.
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
-- LTL.Elim

-- Checkpoint C1.
--
-- ◇ p is satisfiable: all three states survive, and one of them makes
-- ◇ p true.

Uinf-◇P : length (Uinf ◇P) ≡ 3
Uinf-◇P = refl

satB-◇P : satB ◇P ≡ true
satB-◇P = refl

-- ¬ benAri is unsatisfiable, so □ p ⇒ ○ □ p is provable.
--
-- Of the six states, E and D are removed in the first round by (R1) alone --
-- neither has a successor -- and E is the only state containing ¬ benAri.
-- Ben-Ari's own worked example therefore never reaches (R2) in this
-- formulation: (T2) makes  □ p  together with  ¬ ○ □ p  contradict
-- in a single step, where his tableau needed the loop invariant because it
-- carried  ○ □ p  as an explicit member of the closure.

Uinf-¬BenAri : length (Uinf ¬BenAri) ≡ 0
Uinf-¬BenAri = refl

removed-¬BenAri : length (removed ¬BenAri) ≡ 1
removed-¬BenAri = refl

satB-¬BenAri : satB ¬BenAri ≡ false
satB-¬BenAri = refl

------------------------------------------------------------------------
-- An example that does exercise (R2), recorded but not checked here.
--
-- Since benAri is settled by (R1) alone, it is not an adequate end-to-end test
-- of the extraction theorem.  The induction axiom is:
--
--   indAx  = □ (p ⇒ ○ p) ⇒ p ⇒ □ p
--
-- Running the procedure on  ¬ indAx  gives, measured:
--
--   length (sub negInd)   = 11        (so 2048 valuations to filter)
--   length (St negInd)    = 10
--   length (Uinf negInd)  =  7
--   satB negInd           = false     -- hence  indAx  is provable
--   (R1) fires on 1 state of U_0, (R2) fires on 1 state of U_0
--
-- So (R2) does fire, and the loop-invariant branch of Theorem 4.1 is genuinely
-- reached.  A smaller example with the same property is bnb in LTL.Trace, and
-- that is the one checkpoint C4 uses.

------------------------------------------------------------------------
-- LTL.Trace

-- Observation.
--
-- The observations are made on Ust, the demand-driven state set of G30, which
-- is what the procedure actually explores; St still has the six states of the
-- comment in LTL.Elim, but four of them are never reached from a state
-- containing ¬ benAri and the procedure never looks at them.
--
-- Only ONE state of ¬ benAri contains it, namely E, and E has no successor,
-- so the closure stops there and the single round removes it by (R1).
-- Ben-Ari's own example therefore never exercises (R2) in this formulation.

trace-¬BenAri : reasons ¬BenAri (Ust ¬BenAri) ≡ true ∷ []
trace-¬BenAri = refl

-- and the second round removes nothing, so the procedure has converged.

trace-¬BenAri2 : reasons ¬BenAri (elimRound ¬BenAri (Ust ¬BenAri)) ≡ []
trace-¬BenAri2 = refl

-- ◇ p loses no state at all.

trace-◇P : reasons ◇P (Ust ◇P) ≡ []
trace-◇P = refl

------------------------------------------------------------------------
-- A small example that does exercise (R2).
--
--   bnb  =  □ p ⇒ □ ○ p
--
-- is provable, and unlike benAri its refutation genuinely needs the loop
-- invariant.  The state with □ p true and □ ○ p false has successors,
-- so (R1) does not apply; but (T2) carries □ p along every path, (S2) then
-- gives p and (T1) gives ○ p at every state reached, so the eventuality that
-- □ ○ p leaves pending is fulfilled nowhere.  That is case (R2), and it
-- fires in the first round -- the false entry below.
--
-- The closure of the states containing ¬ bnb has just two members: □ p and
-- ¬ □ ○ p force p, and (T2) and (T3) carry both along every step, so
-- the only freedom left is the bit at ○ p.  The state with ○ p false has no
-- successor and goes by (R1) in the first round; the other one loops to itself,
-- and once its (R1)-victim is gone the eventuality that □ ○ p leaves
-- pending is fulfilled at no reachable state, so it goes by (R2) in the second.
-- Nothing survives, and in particular no survivor contains ¬ bnb.
--
-- The (R2) round is the one that matters: extractR2 -- the loop invariant,
-- (Ind) and all -- is on the path from satB-¬Bnb to bnbProof in LTL.Extract.

bnb : Formula
bnb = □ (var zero) ⇒ □ ○ (var zero)

¬Bnb : Formula
¬Bnb = ¬ bnb

Ust-¬Bnb : length (Ust ¬Bnb) ≡ 2
Ust-¬Bnb = refl

trace-¬Bnb : reasons ¬Bnb (Ust ¬Bnb) ≡ true ∷ []
trace-¬Bnb = refl

trace-¬Bnb2 : reasons ¬Bnb (elimRound ¬Bnb (Ust ¬Bnb)) ≡ false ∷ []
trace-¬Bnb2 = refl

Uinf-¬Bnb : length (Uinf ¬Bnb) ≡ 0
Uinf-¬Bnb = refl

satB-¬Bnb : satB ¬Bnb ≡ false
satB-¬Bnb = refl

-- and the converse, which Hintikka's lemma needs: a box-subformula names an
-- eventuality.  That is □Args-of, and it followed □Args down to LTL.Skel
-- in Phase 9, where the (S2) premise of LTL.CompletePC needs it.

------------------------------------------------------------------------
-- LTL.Extract

-- Checkpoint.
--
-- Ben-Ari's formula, decided.  The procedure removes both states containing
-- ¬ benAri, so provable returns a derivation of  □ p ⇒ ○ □ p  in the
-- system L.  This is the first half of C4, reached without Phase 6: the
-- refutation branch of Theorem 6.1 is complete on its own.

benAriProof : ⊢ benAri
benAriProof = provable benAri satB-¬BenAri

-- The same for  □ p ⇒ □ ○ p .  This is the example that matters as a
-- test: by trace-¬Bnb of LTL.Trace its refutation passes through case (R2),
-- so extractR2 -- the loop invariant, (Ind) and all -- is on the path from
-- satB-¬Bnb to this derivation, where for benAri only extractR1 is.

bnbProof : ⊢ bnb
bnbProof = provable bnb satB-¬Bnb

------------------------------------------------------------------------
-- LTL.Lasso

-- The lasso, computed.
--
-- For ◇ p the four positions of sub (◇ p) are
--
--    ¬ □ ¬ p ,  □ ¬ p ,  ¬ p ,  p
--
-- and Uinf has the three states of Example 1 of the lecture 15 notes:
--
--    sPending = 1 0 1 0   ◇ p holds, p does not: the eventuality is pending
--    sFulfil  = 1 0 0 1   p holds: the eventuality is fulfilled
--    sSink    = 0 1 1 0   ◇ p is false, so p fails forever
--
-- Starting at sPending, lassoAt below finds the stem  sFulfil, sSink  (the
-- walk from the start to the cycle) and the cycle  sSink , of length one:
--
--    1 0 1 0  ->  1 0 0 1  ->  0 1 1 0  ->  0 1 1 0  ->  ...
--
-- The eventuality pending at the start is fulfilled at the second state, and
-- nothing is pending on the cycle, which is what Proposition 5.3 promises and
-- what the type of cyc above records.  This run satisfies ◇ p at stage 0, so
-- it is a countermodel to ¬ ◇ p (see the checkpoint in LTL.Eval).

sPending : Val
sPending = true ∷ false ∷ true ∷ false ∷ []
sFulfil : Val
sFulfil = true ∷ false ∷ false ∷ true ∷ []
sSink : Val
sSink = false ∷ true ∷ true ∷ false ∷ []

◇P-lasso : lassoAt ◇P sPending refl ≡ (sFulfil ∷ sSink ∷ [] , sSink ∷ [])
◇P-lasso = refl


-- A degenerate but instructive second case.  For  □ p  the demand-driven
-- state set has a single member: □ p forces p by (S2) and carries itself
-- along every step by (T2), so the closure of the states containing □ p is
-- the one state  1 1  looping to itself.  Nothing is pending there, every round
-- is the one forced step, and the cycle has length one.  That the cycle is
-- nonempty is not automatic; it is what the extra step appended by roundOf
-- buys, and null qs ≡ false in mkLasso records it.

□P : Formula
□P = □ (var zero)

s□ : Val
s□ = true ∷ true ∷ []

□P-lasso : lassoAt □P s□ refl ≡ ([] , s□ ∷ [])
□P-lasso = refl

------------------------------------------------------------------------
-- LTL.Eval

-- Checkpoint.
--
-- For ◇ p, started at the state sPending = 1 0 1 0 of LTL.Lasso, the run is
--
--    1 0 1 0  ->  1 0 0 1  ->  0 1 1 0  ->  0 1 1 0  ->  ...
--
-- so p fails at stage 0, holds at stage 1, and fails from stage 2 on, the sink
-- being the state where ◇ p itself is false.  So
--
--   ◇ p    holds at stage 0 -- the eventuality is fulfilled at stage 1
--   p        fails at stage 0 and holds at stage 1
--   □ p    fails, and so does □ ○ p
--   ○ p    holds at stage 0
--   ◇ p    holds at stages 0 and 1, so this is a genuine countermodel to
--            ¬ ◇ p, which is what Theorem 6.1 will read off.

eval-◇ : evalOn ◇P sPending refl ◇P 0 ≡ true
eval-◇ = refl

eval-p0 : evalOn ◇P sPending refl (var zero) 0 ≡ false
eval-p0 = refl

eval-p1 : evalOn ◇P sPending refl (var zero) 1 ≡ true
eval-p1 = refl

eval-p2 : evalOn ◇P sPending refl (var zero) 2 ≡ false
eval-p2 = refl

eval-○-p : evalOn ◇P sPending refl (○ (var zero)) 0 ≡ true
eval-○-p = refl

eval-□-p : evalOn ◇P sPending refl (□ (var zero)) 0 ≡ false
eval-□-p = refl

eval-◇1 : evalOn ◇P sPending refl ◇P 1 ≡ true
eval-◇1 = refl

-- and the formula the procedure was run on holds at stage 0, as Hintikka's
-- lemma (G27) will say in general

eval-input : evalOn ◇P sPending refl ◇P 0 ≡ true
eval-input = refl

eval-□-○-p : evalOn ◇P sPending refl (□ ○ (var zero)) 0 ≡ false
eval-□-○-p = refl

-- The contrast, in the two forms G30 gives it.
--
-- For  □ p  the lasso is the single state of LTL.Lasso at which p holds
-- forever, so □ p is TRUE there and the lasso IS a countermodel to
-- ¬ □ p.

eval-□P-p : evalOn □P s□ refl (var zero) 3 ≡ true
eval-□P-p = refl

eval-□P-input : evalOn □P s□ refl □P 0 ≡ true
eval-□P-input = refl

-- For ¬ bnb there is no lasso at all: nothing containing ¬ bnb survives,
-- and since G30 explores only the closure of the states that do contain it,
-- U_infinity is empty rather than merely free of them (Uinf-¬Bnb in
-- LTL.Trace).  That is the branch where the certificate is a derivation, and
-- provable supplies it -- see bnbProof in LTL.Extract.

eval-¬Bnb-empty : null (Uinf ¬Bnb) ≡ true
eval-¬Bnb-empty = refl

------------------------------------------------------------------------
-- LTL.Hintikka

-- Checkpoint.
--
-- ◇ p is consistent: ¬ ◇ p has no derivation in L.  This is a THEOREM,
-- not a computation -- the certificate is the lasso of LTL.Lasso, and
-- the proof is Hintikka's lemma at stage 0 against soundness.

◇P-consistent : ⊢ ¬ ◇P -> Empty
◇P-consistent = notRefutableSat ◇P satB-◇P

------------------------------------------------------------------------
-- LTL.Decide

-- Checkpoint C4.
--
-- Ben-Ari's formula is decided in the affirmative: decide returns inl, so the
-- certificate is a derivation of  □ p ⇒ ○ □ p  in the system L.  The
-- same for  □ p ⇒ □ ○ p , whose derivation goes through case (R2) of
-- Theorem 4.1 -- see bnbProof in LTL.Extract.

decide-benAri : isProof (decide benAri) ≡ true
decide-benAri = refl

decide-bnb : isProof (decide bnb) ≡ true
decide-bnb = refl

-- ◇ p is decided in the negative, and the certificate is a lasso.
--
-- The procedure runs on  ¬ ◇ p = ¬ ¬ □ ¬ p , whose five
-- subformulas are
--
--    ¬ ◇ p ,  ◇ p ,  □ ¬ p ,  ¬ p ,  p
--
-- and the surviving state it starts from is  1 0 1 1 0 : ◇ p fails, □ ¬ p
-- holds, p does not.  The stem is empty -- rest and cycle coincide -- and the
-- cycle is that state looping to itself.  So the countermodel is the obvious
-- one, p false forever, and by the ⊢ Q -> Empty field of the record,
-- ◇ p has no derivation in L.

◇P-cmState : Val
◇P-cmState = true ∷ false ∷ true ∷ true ∷ false ∷ []

decide-◇P : isProof (decide ◇P) ≡ false
decide-◇P = refl

decide-◇P-lasso : lassoOfDecide ◇P (decide ◇P) ≡
                       (◇P-cmState , ◇P-cmState ∷ [] , ◇P-cmState ∷ [])
decide-◇P-lasso = refl

------------------------------------------------------------------------
-- Checkpoint C5, the target of Phase 8.
--
--   □ (p ∨ q) ⇒ □ p ∨ □ q
--
-- is NOT valid, and decide says so with a lasso.  Sub of its negation has
-- length 13, so the state space is nominally 8192 vectors; the five atoms are
-- □ (p ∨ q), p, q, □ p, □ q, so 32 assignments are built, 17 of them are
-- states, and the closure of those containing the negation has 8 members, none
-- of which is eliminated.  This is the measurement Phase 8 exists for: 34.6 s
-- before G29, 1.4 s after it, and 0.9 s after G30 -- for the whole
-- countermodel, not just the branch.
--
-- The countermodel it returns is the expected one.  Writing a state as the
-- pair (p , q) -- the other eleven bits are determined -- the run is
--
--   (1,1)  ->  (0,1)  ->  (1,0)  ->  (1,1)  ->  (1,1)  ->  ...
--
-- so p or q holds at every stage, while p fails at stage 1 and q at stage 2.
-- Hence □ (p ∨ q) holds and neither □ p nor □ q does.  The stem is
-- three states and the cycle is the single state at which both hold forever.

-- The atoms p and q of C5 (c for C5).

cp : Formula
cp = var zero

cq : Formula
cq = var (suc zero)

c5 : Formula
c5 = □ (cp ∨ cq) ⇒ □ cp ∨ □ cq

-- p and q, but neither forever
c5pqNow : Val
c5pqNow = true  ∷ false ∷ true ∷ true ∷ false ∷ true ∷ true
      ∷ false ∷ true  ∷ false ∷ true  ∷ false ∷ true ∷ []

-- q, not p
c5q : Val
c5q = true  ∷ false ∷ true ∷ true ∷ true  ∷ false ∷ true
   ∷ false ∷ true  ∷ false ∷ false ∷ false ∷ true ∷ []

-- p, not q
c5p : Val
c5p = false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ false
   ∷ true  ∷ false ∷ true  ∷ true  ∷ false ∷ false ∷ []

-- p and q, both forever
c5pqForever : Val
c5pqForever = false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ true
    ∷ true  ∷ false ∷ true ∷ true ∷ true  ∷ true ∷ []

decide-c5 : isProof (decide c5) ≡ false
decide-c5 = refl

decide-c5-lasso : lassoOfDecide c5 (decide c5) ≡
                  (c5pqNow , c5q ∷ c5p ∷ c5pqForever ∷ c5pqForever ∷ [] ,
                             c5pqForever ∷ [])
decide-c5-lasso = refl

------------------------------------------------------------------------
-- LTL.ShortPC

-- Checkpoints.
--
-- The two formulas of C4 are still decided in the affirmative, and by the same
-- boolean: what changed is the size of the answer, not the answer.

decidePC-benAri : isProof (decidePC benAri) ≡ true
decidePC-benAri = refl

decidePC-bnb : isProof (decidePC bnb) ≡ true
decidePC-bnb = refl

decidePC-◇P : isProof (decidePC ◇P) ≡ false
decidePC-◇P = refl

------------------------------------------------------------------------
-- LTL.SccLasso

-- The lassos, computed, beside the ones LTL.Lasso records.
--
-- For  ◇ p  the stem is the same and the cycle is the base point twice where
-- lassoSearch has it once.  That is not an accident of this example: mkCirc
-- always starts from the bare loop found by loopAt and prepends one LEG per
-- fairness predicate, each leg being the loop again followed by the trip out to
-- the witness and back.  Here there is one eventuality, its witness in the
-- terminal component {sSink} is sSink itself, so both halves of the trip are
-- empty and the leg is the bare loop over again.  The SCC construction chooses
-- its witnesses in its own order and does not produce the shortest fair cycle
-- -- which is the observation checkpoint C8 is to make, not a defect.

scc◇P : sccAt ◇P sPending refl ≡ (sFulfil ∷ sSink ∷ [] , sSink ∷ sSink ∷ [])
scc◇P = refl

lasso◇P : lassoAt ◇P sPending refl ≡ (sFulfil ∷ sSink ∷ [] , sSink ∷ [])
lasso◇P = refl

-- and the same doubling in the degenerate case, where the state set is one
-- state looping to itself.

scc□P : sccAt □P s□ refl ≡ ([] , s□ ∷ s□ ∷ [])
scc□P = refl

lasso□P : lassoAt □P s□ refl ≡ ([] , s□ ∷ [])
lasso□P = refl

-- The run, unwound, to show that runOf accepts the result unchanged: the stem
-- of ◇ p walked out, then the cycle forever.

scc◇P-run : map (sccState ◇P sPending refl) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡
                 sPending ∷ sFulfil ∷ sSink ∷ sSink ∷ sSink ∷ sSink ∷ []
scc◇P-run = refl

------------------------------------------------------------------------
-- LTL.SccExtract

-- Checkpoints.
--
-- Ben-Ari's formula and  □ p ⇒ □ ○ p , the two examples LTL.Extract
-- ends with, decided again by the SCC route.  These are the real test: both
-- derivations are produced, so the graph search, certAll, extractR1 and
-- extractBlock all run, and the answers agree with benAriProof and bnbProof.

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
-- -- only extractR1 runs, which is what LTL.Extract records of benAriProof.
--
-- For  □ p ⇒ □ ○ p  Ust has two states and the certificate is
-- cSink, cBlock, cNil : one state has no successor inside the set and leaves
-- first, and only then is what remains a component whose eventuality is
-- unfulfillable, refuted by extractBlock in a single use of (Ind).  That is the
-- same order as the elimination's -- G30's note "bnb still exercises (R2), now
-- in the second round rather than the first, because the (R1)-victim has to
-- leave before the eventuality is unfulfillable" -- reached by a different
-- route, and it is why bnb is the example that matters: extractBlock, the copy
-- of (R2), is on the path from here to bnbProofSCC.

shape-benAri : sccShape benAri ≡ removedSink ∷ emptied ∷ []
shape-benAri = refl

shape-bnb : sccShape bnb ≡ removedSink ∷ removedBlock ∷ emptied ∷ []
shape-bnb = refl

-- and the positive side, to show the search is not simply always certifying:
-- ◇ p is satisfiable, so its state set has a fair component.

scc-◇P : isInl (sccGraph ◇P) ≡ true
scc-◇P = refl

------------------------------------------------------------------------
-- LTL.DecideSCC

-- Checkpoints.
--
-- The two examples LTL.Extract ends with, and the two LTL.Lasso ends with:
-- the valid ones come back as proofs and the invalid ones as countermodels,
-- through the SCC branch each time.  The full agreement with decide, on all
-- forty-six statements of LTL.Examples, is checkpoint C8 and lives in
-- LTL.Compare, so that it is clear which side of the timing rule it is on.

decideSCC-benAri : isProof (decideSCC benAri) ≡ true
decideSCC-benAri = refl

decideSCC-bnb : isProof (decideSCC bnb) ≡ true
decideSCC-bnb = refl

decideSCC-◇P : isProof (decideSCC ◇P) ≡ false
decideSCC-◇P = refl

------------------------------------------------------------------------
-- LTL.Pretty

-- Checks: the printer on the identity (L1), the abbreviations, and a
-- countermodel.  The first is ⇒Refl-full of LTL.Proofs, as text.

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
  "⊬ p ⇒ □ p\n\nCountermodel: the formula is false at time 0.  Variables true at each time:\n    0  {p}\n    1  {}\n    2  {p}\n    3  {p}\nthen repeating forever:\n    4  {p}\n  (back to time 4)\n"
pretty-countermodel = refl

------------------------------------------------------------------------
-- LTL.Correct

-- The Boolean answer of each DecisionProcedure: (Exp)'s first conjunct is
-- valid, ◇ p is not.

correct-answers :
  map (λ D -> T.DecisionProcedure.decideValid D (□ var 0 ⇒ var 0))
      (decideCorrect ∷ decideSCCCorrect ∷ decidePCCorrect ∷ [])
  ++ map (λ D -> T.DecisionProcedure.decideValid D (◇ var 0))
         (decideCorrect ∷ decideSCCCorrect ∷ decidePCCorrect ∷ [])
  ≡ true ∷ true ∷ true ∷ false ∷ false ∷ false ∷ []
correct-answers = refl

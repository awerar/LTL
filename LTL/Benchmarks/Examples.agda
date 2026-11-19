{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Benchmarks.Examples -- Figure 11 of Schmitt and Goubault-Larrecq, "Linear Temporal
-- Logic" (page 14), run through decideSCC.
--
-- Forty-six named modal and temporal statements, in the box/diamond fragment
-- -- no ○ occurs in any of them.  The figure's last column marks the ones its
-- procedure reports valid; here each is a checked equation instead, and the
-- checkmark is the BRANCH decideSCC takes:
--
--   isProof (decideSCC X) = true    decideSCC returned inl, a derivation of X
--                                   in L
--   isProof (decideSCC X) = false   decideSCC returned inr, a lasso
--                                   countermodel together with  ⊢ X -> Empty
--
-- So the file is not a comparison of two programs' outputs.  Every line below
-- is a theorem: the true ones assert that a derivation exists, the false ones
-- that none does, and both are certified by the type of decideSCC
-- (LTL.Procedures.DecideSCC).
--
-- The twenty-two marked in the figure are T, G, pb5, lin1, Dum, Dum1, Dum2,
-- Dum3, Dum4, D, 4, 4M, G0, H, H+, L, L+, L++, X, K3, K4, K5, and those are
-- exactly the twenty-two that come out true here.
--
-- The names are the figure's, with ax- prefixed where the figure's name is not
-- an Agda identifier (4, 5, 4M, 5M, +, ++).
--
-- The file is slow because it is forty-six decision problems, not because of
-- any one proof: the 5 s rule of FORMALISATION-PLAN.md section 4a is a detector for
-- proofs that have drifted from the note, and does not apply to a benchmark.
-- The figure's own times are 0.017-0.083 s per formula for a procedure written
-- in ML; these run inside Agda's evaluator, on the decision procedure as a
-- type-theoretic boolean function, with no extraction anywhere.

module LTL.Benchmarks.Examples where

open import LTL.Procedures.DecideSCC public

------------------------------------------------------------------------
-- The two variables

pv : Formula
pv = var zero

qv : Formula
qv = var (suc zero)

------------------------------------------------------------------------
-- The statements, in the figure's order

axT : Formula
axT = □ pv ⇒ pv

pb2 : Formula
pb2 = pv ⇒ □ pv

axG : Formula
axG = ◇ □ pv ⇒ □ ◇ pv

axM : Formula
axM = □ ◇ pv ⇒ ◇ □ pv

axM2 : Formula
axM2 = ◇ □ (pv ⇒ □ pv)

axM3 : Formula
axM3 = □ ◇ pv ∧ □ ◇ qv ⇒ ◇ (pv ∧ qv)

pb5 : Formula
pb5 = pv ⇒ ◇ pv

lin1 : Formula
lin1 = ◇ pv ∧ ◇ qv ⇒ ◇ (pv ∧ ◇ qv) ∨ ◇ (qv ∧ ◇ pv)

-- Dummett's axiom and its four variants
dumL : Formula
dumL = □ (□ (pv ⇒ □ pv) ⇒ pv)

dumLb : Formula
dumLb = □ (□ (pv ⇒ □ pv) ⇒ □ pv)

dumR : Formula
dumR = ◇ □ pv

axDum : Formula
axDum = dumL ⇒ dumR ⇒ pv

axDum1 : Formula
axDum1 = dumL ⇒ dumR ⇒ □ pv

axDum2 : Formula
axDum2 = dumLb ⇒ dumR ⇒ pv

axDum3 : Formula
axDum3 = dumLb ⇒ dumR ⇒ □ pv

axDum4 : Formula
axDum4 = dumL ⇒ dumR ⇒ pv ∨ □ pv

axD : Formula
axD = □ pv ⇒ ◇ pv

ax4 : Formula
ax4 = □ pv ⇒ □ □ pv

ax4M : Formula
ax4M = □ pv ∧ ◇ qv ⇒ ◇ (□ pv ∧ qv)

ax5 : Formula
ax5 = ◇ pv ⇒ □ ◇ pv

ax5M : Formula
ax5M = ◇ pv ∧ ◇ qv ⇒ ◇ (◇ pv ∧ qv)

axB : Formula
axB = pv ⇒ □ ◇ pv

axBM : Formula
axBM = pv ∧ ◇ qv ⇒ ◇ (◇ pv ∧ qv)

axG0 : Formula
axG0 = ◇ (pv ∧ □ qv) ⇒ □ (pv ∨ ◇ qv)

axH : Formula
axH = □ (pv ∨ qv) ∧ □ (□ pv ∨ qv) ∧ □ (pv ∨ □ qv) ⇒ □ pv ∨ □ qv

axHplus : Formula
axHplus = □ (□ pv ∨ qv) ∧ □ (pv ∨ □ qv) ⇒ □ pv ∨ □ qv

axL : Formula
axL = □ (pv ∧ □ pv ⇒ qv) ∨ □ (qv ∧ □ qv ⇒ pv)

axLplus : Formula
axLplus = □ (□ pv ⇒ qv) ∨ □ (□ qv ⇒ pv)

axLplusplus : Formula
axLplusplus = □ (□ pv ⇒ □ qv) ∨ □ (□ qv ⇒ □ pv)

axPt : Formula
axPt = □ (pv ∨ ◇ pv) ⇒ ◇ (pv ∧ □ pv)

axW : Formula
axW = □ (□ pv ⇒ pv) ⇒ □ pv

axZ : Formula
axZ = □ (□ pv ⇒ pv) ⇒ ◇ □ pv ⇒ □ pv

axGrz : Formula
axGrz = dumL ⇒ pv

axGrz1 : Formula
axGrz1 = dumL ⇒ □ pv

axGrz2 : Formula
axGrz2 = dumLb ⇒ pv

axGrz3 : Formula
axGrz3 = dumLb ⇒ □ pv

axGrz4 : Formula
axGrz4 = dumL ⇒ pv ∨ □ pv

axGrz5 : Formula
axGrz5 = □ (□ (pv ⇒ □ qv) ⇒ □ qv) ∧ □ (□ (¬ pv ⇒ □ qv) ⇒ □ qv) ⇒ □ qv

axF : Formula
axF = (◇ □ pv ⇒ qv) ∨ □ (□ qv ⇒ pv)

axHs : Formula
axHs = pv ⇒ □ (◇ pv ⇒ pv)

axP : Formula
axP = ◇ □ ◇ pv ⇒ pv ⇒ □ pv

axR : Formula
axR = ◇ □ pv ⇒ pv ⇒ □ pv

axX : Formula
axX = □ □ pv ⇒ □ pv

axZem : Formula
axZem = □ ◇ □ pv ⇒ pv ⇒ □ pv

axK1 : Formula
axK1 = ◇ pv ⇒ □ pv

axK2 : Formula
axK2 = □ (pv ∨ qv) ⇒ □ pv ∨ □ qv

axK3 : Formula
axK3 = ◇ □ ◇ pv ⇔ □ ◇ pv

axK4 : Formula
axK4 = □ ◇ □ pv ⇔ ◇ □ pv

axK5 : Formula
axK5 = □ ◇ (pv ∨ qv) ⇔ □ ◇ pv ∨ □ ◇ qv

------------------------------------------------------------------------
-- The results

check-T : isProof (decideSCC axT) ≡ true
check-T = refl

check-pb2 : isProof (decideSCC pb2) ≡ false
check-pb2 = refl

check-G : isProof (decideSCC axG) ≡ true
check-G = refl

check-M : isProof (decideSCC axM) ≡ false
check-M = refl

check-M2 : isProof (decideSCC axM2) ≡ false
check-M2 = refl

check-M3 : isProof (decideSCC axM3) ≡ false
check-M3 = refl

check-pb5 : isProof (decideSCC pb5) ≡ true
check-pb5 = refl

check-lin1 : isProof (decideSCC lin1) ≡ true
check-lin1 = refl

check-Dum : isProof (decideSCC axDum) ≡ true
check-Dum = refl

check-Dum1 : isProof (decideSCC axDum1) ≡ true
check-Dum1 = refl

check-Dum2 : isProof (decideSCC axDum2) ≡ true
check-Dum2 = refl

check-Dum3 : isProof (decideSCC axDum3) ≡ true
check-Dum3 = refl

check-Dum4 : isProof (decideSCC axDum4) ≡ true
check-Dum4 = refl

check-D : isProof (decideSCC axD) ≡ true
check-D = refl

check-ax4 : isProof (decideSCC ax4) ≡ true
check-ax4 = refl

check-ax4M : isProof (decideSCC ax4M) ≡ true
check-ax4M = refl

check-ax5 : isProof (decideSCC ax5) ≡ false
check-ax5 = refl

check-ax5M : isProof (decideSCC ax5M) ≡ false
check-ax5M = refl

check-B : isProof (decideSCC axB) ≡ false
check-B = refl

check-BM : isProof (decideSCC axBM) ≡ false
check-BM = refl

check-G0 : isProof (decideSCC axG0) ≡ true
check-G0 = refl

check-H : isProof (decideSCC axH) ≡ true
check-H = refl

check-Hplus : isProof (decideSCC axHplus) ≡ true
check-Hplus = refl

check-L : isProof (decideSCC axL) ≡ true
check-L = refl

check-Lplus : isProof (decideSCC axLplus) ≡ true
check-Lplus = refl

check-Lplusplus : isProof (decideSCC axLplusplus) ≡ true
check-Lplusplus = refl

check-Pt : isProof (decideSCC axPt) ≡ false
check-Pt = refl

check-W : isProof (decideSCC axW) ≡ false
check-W = refl

check-Z : isProof (decideSCC axZ) ≡ false
check-Z = refl

check-Grz : isProof (decideSCC axGrz) ≡ false
check-Grz = refl

check-Grz1 : isProof (decideSCC axGrz1) ≡ false
check-Grz1 = refl

check-Grz2 : isProof (decideSCC axGrz2) ≡ false
check-Grz2 = refl

check-Grz3 : isProof (decideSCC axGrz3) ≡ false
check-Grz3 = refl

check-Grz4 : isProof (decideSCC axGrz4) ≡ false
check-Grz4 = refl

check-Grz5 : isProof (decideSCC axGrz5) ≡ false
check-Grz5 = refl

check-F : isProof (decideSCC axF) ≡ false
check-F = refl

check-Hs : isProof (decideSCC axHs) ≡ false
check-Hs = refl

check-P : isProof (decideSCC axP) ≡ false
check-P = refl

check-R : isProof (decideSCC axR) ≡ false
check-R = refl

check-X : isProof (decideSCC axX) ≡ true
check-X = refl

check-Zem : isProof (decideSCC axZem) ≡ false
check-Zem = refl

check-K1 : isProof (decideSCC axK1) ≡ false
check-K1 = refl

check-K2 : isProof (decideSCC axK2) ≡ false
check-K2 = refl

check-K3 : isProof (decideSCC axK3) ≡ true
check-K3 = refl

check-K4 : isProof (decideSCC axK4) ≡ true
check-K4 = refl

check-K5 : isProof (decideSCC axK5) ≡ true
check-K5 = refl

------------------------------------------------------------------------
-- Two of the countermodels, read off.
--
-- decideSCC returns the lasso as a record; cmStart, cmRest and cmCycle give the
-- states as the procedure stores them, but a bit vector read against
-- sub (¬ Q) is not something one wants to look at.  traceOf evaluates a
-- chosen formula at the successive stages of the run instead, and shapeOf says
-- where the run starts repeating: with shapeOf Q = r , c the run is
--
--    v0 , rest_0 , ... , rest_{r-1} , then the last c of those, forever
--
-- so it is periodic from stage  1 + r - c  on, with period c.
--
-- Nothing here is an extra assumption.  traceOf goes through eval of LTL.Countermodel.Eval,
-- which is the semantics soundness (G26) is proved against, so
-- "traceOf Q Q 1 = false ∷ []" below and the ⊢ Q -> Empty field of the
-- record are the same fact seen from the two ends.

------------------------------------------------------------------------
-- pb2 = p ⇒ □ p.
--
-- shapeOf pb2 = 4 , 2: four states after the start, the last two of them the
-- cycle, so the run is periodic from stage 3 with period 2 --
--
--    p       1  0  1  1  1  1  1  1  ...
--    □ p   0  0  1  1
--    pb2     0  1  1  1
--
-- p holds now and fails at the next stage, which refutes □ p now; from
-- stage 2 on p holds forever, so □ p holds and pb2 holds at every stage but
-- the first.  That single false at stage 0 is the countermodel.  The cycle
-- has two states where one would do: the SCC construction starts from the
-- bare loop and prepends a leg for each eventuality (LTL.SCC.Graph), and does
-- not look for the shortest fair cycle.

pb2-shape : shapeOf pb2 ≡ (4 , 2)
pb2-shape = refl

pb2-p : traceOf pb2 pv 8 ≡
        true ∷ false ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
pb2-p = refl

pb2-□ : traceOf pb2 (□ pv) 4 ≡ false ∷ false ∷ true ∷ true ∷ []
pb2-□ = refl

pb2-input : traceOf pb2 pb2 4 ≡ false ∷ true ∷ true ∷ true ∷ []
pb2-input = refl

------------------------------------------------------------------------
-- axM2 = ◇ □ (p ⇒ □ p).
--
-- shapeOf axM2 = 8 , 8: the cycle has eight states and the stem is empty, so
-- the run is periodic from stage 1 with period 8 --
--
--    p            1  1  0  1  1  1  0  1  ...
--    p ⇒ □ p      0  0  1  0  0  0  1  0
--    axM2         0  0  0  0
--
-- p fails at stages 2, 6, 10, ... and holds everywhere else, so □ p is false
-- at every stage, so p ⇒ □ p fails at exactly the stages where p holds --
-- infinitely often.  Hence
-- □ (p ⇒ □ p) holds nowhere and its diamond is false at every stage: the
-- alternating run refutes axM2 not just at stage 0 but everywhere, which is
-- what an eventuality being unfulfillable on a cycle looks like.

axM2-shape : shapeOf axM2 ≡ (8 , 8)
axM2-shape = refl

axM2-p : traceOf axM2 pv 8 ≡
         true ∷ true ∷ false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ []
axM2-p = refl

axM2-step : traceOf axM2 (pv ⇒ □ pv) 8 ≡
            false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ []
axM2-step = refl

axM2-input : traceOf axM2 axM2 4 ≡ false ∷ false ∷ false ∷ false ∷ []
axM2-input = refl

------------------------------------------------------------------------
-- The half of K5 that carries the content.
--
--   □ ◇ (p ∨ q)  ⇒  □ ◇ p  ∨  □ ◇ q
--
-- The figure lists K5 as the equivalence; this is its left-to-right half, and
-- it is the only half that is not immediate.  Semantically it is the statement
-- that if p or q holds infinitely often then one of the two does, which on
-- paper is a pigeonhole argument about an infinite run.  Formally there is no
-- infinite run and no pigeonhole: nothing here is coinductive, and the argument
-- is the SCC certificate of m5.tex followed by the extraction of Theorem 4.1.
--
-- Measured.  Sub of the negation has length 22, so the naive state space is
-- 2^22 = 4194304 vectors.  The atoms are p, q and the six box-subformulas
--
--    □ ¬ (p ∨ q) , □ ◇ (p ∨ q) , □ ¬ p , □ ◇ p ,
--    □ ¬ q , □ ◇ q
--
-- so 2^8 = 256 assignments are built, 59 of them are states, and the closure of
-- the ones containing the negation has 9 members.  The elimination of
-- Definition 3.1 would run
--
--    9  ->  8  ->  4  ->  0
--
-- and EVERY removal goes by (R2).  Not one state is dropped for want of a
-- successor: the whole refutation is the loop-invariant case, which is what one
-- would expect of a formula that says an eventuality recurring forever must
-- recur in one of two ways.  The SCC certificate (LTL.SCC.SccExtract) agrees:
-- it removes the nine states in four blocks and no sinks, so every step of the
-- refutation is extractBlock -- the invariant B = beta of the block, (Ind)
-- through indRule -- where bnb exercises it once.  It is the atom generator
-- of G30 that makes the example reachable at all: the naive state list would
-- be 2^22 vectors filtered one at a time.

axK5fwd : Formula
axK5fwd = □ ◇ (pv ∨ qv) ⇒ □ ◇ pv ∨ □ ◇ qv

K5fwd-sub : length (sub (¬ axK5fwd)) ≡ 22
K5fwd-sub = refl

K5fwd-atoms : length (atoms (sub (¬ axK5fwd))) ≡ 8
K5fwd-atoms = refl

K5fwd-cands : length (cands (¬ axK5fwd)) ≡ 256
K5fwd-cands = refl

K5fwd-states : length (StCand (¬ axK5fwd)) ≡ 59
K5fwd-states = refl

K5fwd-closure : length (Ust (¬ axK5fwd)) ≡ 9
K5fwd-closure = refl

-- the certificate: four blocks, then nothing is left

K5fwd-cert : sccShape axK5fwd ≡
             removedBlock ∷ removedBlock ∷ removedBlock ∷ removedBlock ∷ emptied ∷ []
K5fwd-cert = refl

check-K5fwd : isProof (decideSCC axK5fwd) ≡ true
check-K5fwd = refl

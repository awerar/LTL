{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.9-Benchmarks.Examples -- Figure 11 of Schmitt and Goubault-Larrecq, "Linear
-- Temporal Logic" (page 14), run through decide.
--
-- Forty-six named modal and temporal statements in the box/diamond fragment.
-- Each check states the branch decide takes: isProof = true means it
-- returned a derivation, false a lasso countermodel with  ⊢ X -> Empty.  So
-- every line is a theorem, certified by the type of decide.  The
-- twenty-two marked valid in the figure (T, G, pb5, lin1, Dum, Dum1-4, D, 4,
-- 4M, G0, H, H+, L, L+, L++, X, K3, K4, K5) are exactly the twenty-two that
-- come out true here.
--
-- Names are the figure's, prefixed with ax- where the figure's name is not an
-- Agda identifier (4, 5, 4M, 5M, +, ++).  The file takes about 26 s to check;
-- the figure reports 0.017-0.083 s per formula for a procedure written in ML,
-- while these run in Agda's evaluator with no extraction.

module LTL.9-Benchmarks.Examples where

open import LTL.8-Procedures.Everything public

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

check-T : isProof (decide axT) ≡ true
check-T = refl

check-pb2 : isProof (decide pb2) ≡ false
check-pb2 = refl

check-G : isProof (decide axG) ≡ true
check-G = refl

check-M : isProof (decide axM) ≡ false
check-M = refl

check-M2 : isProof (decide axM2) ≡ false
check-M2 = refl

check-M3 : isProof (decide axM3) ≡ false
check-M3 = refl

check-pb5 : isProof (decide pb5) ≡ true
check-pb5 = refl

check-lin1 : isProof (decide lin1) ≡ true
check-lin1 = refl

check-Dum : isProof (decide axDum) ≡ true
check-Dum = refl

check-Dum1 : isProof (decide axDum1) ≡ true
check-Dum1 = refl

check-Dum2 : isProof (decide axDum2) ≡ true
check-Dum2 = refl

check-Dum3 : isProof (decide axDum3) ≡ true
check-Dum3 = refl

check-Dum4 : isProof (decide axDum4) ≡ true
check-Dum4 = refl

check-D : isProof (decide axD) ≡ true
check-D = refl

check-ax4 : isProof (decide ax4) ≡ true
check-ax4 = refl

check-ax4M : isProof (decide ax4M) ≡ true
check-ax4M = refl

check-ax5 : isProof (decide ax5) ≡ false
check-ax5 = refl

check-ax5M : isProof (decide ax5M) ≡ false
check-ax5M = refl

check-B : isProof (decide axB) ≡ false
check-B = refl

check-BM : isProof (decide axBM) ≡ false
check-BM = refl

check-G0 : isProof (decide axG0) ≡ true
check-G0 = refl

check-H : isProof (decide axH) ≡ true
check-H = refl

check-Hplus : isProof (decide axHplus) ≡ true
check-Hplus = refl

check-L : isProof (decide axL) ≡ true
check-L = refl

check-Lplus : isProof (decide axLplus) ≡ true
check-Lplus = refl

check-Lplusplus : isProof (decide axLplusplus) ≡ true
check-Lplusplus = refl

check-Pt : isProof (decide axPt) ≡ false
check-Pt = refl

check-W : isProof (decide axW) ≡ false
check-W = refl

check-Z : isProof (decide axZ) ≡ false
check-Z = refl

check-Grz : isProof (decide axGrz) ≡ false
check-Grz = refl

check-Grz1 : isProof (decide axGrz1) ≡ false
check-Grz1 = refl

check-Grz2 : isProof (decide axGrz2) ≡ false
check-Grz2 = refl

check-Grz3 : isProof (decide axGrz3) ≡ false
check-Grz3 = refl

check-Grz4 : isProof (decide axGrz4) ≡ false
check-Grz4 = refl

check-Grz5 : isProof (decide axGrz5) ≡ false
check-Grz5 = refl

check-F : isProof (decide axF) ≡ false
check-F = refl

check-Hs : isProof (decide axHs) ≡ false
check-Hs = refl

check-P : isProof (decide axP) ≡ false
check-P = refl

check-R : isProof (decide axR) ≡ false
check-R = refl

check-X : isProof (decide axX) ≡ true
check-X = refl

check-Zem : isProof (decide axZem) ≡ false
check-Zem = refl

check-K1 : isProof (decide axK1) ≡ false
check-K1 = refl

check-K2 : isProof (decide axK2) ≡ false
check-K2 = refl

check-K3 : isProof (decide axK3) ≡ true
check-K3 = refl

check-K4 : isProof (decide axK4) ≡ true
check-K4 = refl

check-K5 : isProof (decide axK5) ≡ true
check-K5 = refl

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Two of the countermodels, read off.
--
-- cmTrace evaluates a chosen formula at the successive stages of the run, and
-- cmShape says where the run starts repeating: with cmShape Q c = r , n the
-- run is  v0 , rest_0 , ... , rest_{r-1} , then the last n of those forever,
-- so it is periodic from stage  1 + r - n  with period n.  cmTrace uses the
-- evaluation that LTL.Correct carries over to Statement's semantics, so
-- "cmTrace Q c Q 1 = false ∷ []" and cmUnderivable are the same fact.

------------------------------------------------------------------------
-- pb2 = p ⇒ □ p.  Its lasso has shape 4 , 2, so the run is periodic from stage 3
-- with period 2:
--
--    p       1  0  1  1  1  1  1  1  ...
--    □ p     0  0  1  1
--    pb2     0  1  1  1
--
-- p holds now and fails next, which refutes □ p now; from stage 2 on p holds
-- forever.  The single false at stage 0 is the countermodel.  The cycle has
-- two states where one would do: the SCC construction prepends a leg per
-- eventuality to the bare loop.

pb2-cm : LassoCountermodel pb2
pb2-cm = countermodelFrom (decide pb2) refl

pb2-shape : cmShape pb2 pb2-cm ≡ (4 , 2)
pb2-shape = refl

pb2-p : cmTrace pb2 pb2-cm pv 8 ≡
        true ∷ false ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
pb2-p = refl

pb2-□ : cmTrace pb2 pb2-cm (□ pv) 4 ≡ false ∷ false ∷ true ∷ true ∷ []
pb2-□ = refl

pb2-input : cmTrace pb2 pb2-cm pb2 4 ≡ false ∷ true ∷ true ∷ true ∷ []
pb2-input = refl

------------------------------------------------------------------------
-- axM2 = ◇ □ (p ⇒ □ p).  Its lasso has shape 8 , 8: the stem is empty and the run
-- is periodic from stage 1 with period 8:
--
--    p            1  1  0  1  1  1  0  1  ...
--    p ⇒ □ p      0  0  1  0  0  0  1  0
--    axM2         0  0  0  0
--
-- p fails at stages 2, 6, 10, ..., so □ p is false everywhere and p ⇒ □ p
-- fails wherever p holds, infinitely often.  So □ (p ⇒ □ p) holds nowhere and
-- axM2 is false at every stage, not just at stage 0.

axM2-cm : LassoCountermodel axM2
axM2-cm = countermodelFrom (decide axM2) refl

axM2-shape : cmShape axM2 axM2-cm ≡ (8 , 8)
axM2-shape = refl

axM2-p : cmTrace axM2 axM2-cm pv 8 ≡
         true ∷ true ∷ false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ []
axM2-p = refl

axM2-step : cmTrace axM2 axM2-cm (pv ⇒ □ pv) 8 ≡
            false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ []
axM2-step = refl

axM2-input : cmTrace axM2 axM2-cm axM2 4 ≡ false ∷ false ∷ false ∷ false ∷ []
axM2-input = refl

------------------------------------------------------------------------
-- The half of K5 that carries the content:
--
--   □ ◇ (p ∨ q)  ⇒  □ ◇ p  ∨  □ ◇ q
--
-- if p or q holds infinitely often, then one of them does.  On paper this is a
-- pigeonhole argument about an infinite run; here nothing is coinductive.
--
-- sub of the negation has length 22, so the naive state space is 2^22 vectors.
-- The atoms are p, q and the six box-subformulas
--
--    □ ¬ (p ∨ q) , □ ◇ (p ∨ q) , □ ¬ p , □ ◇ p , □ ¬ q , □ ◇ q
--
-- so there are 256 rows, 59 of them states, and the closure of those
-- containing the negation has 9 members.  The certificate removes them in four
-- blocks and no sinks, so every step of the refutation is extractBlock.

axK5fwd : Formula
axK5fwd = □ ◇ (pv ∨ qv) ⇒ □ ◇ pv ∨ □ ◇ qv

K5fwd-sub : length (sub (¬ axK5fwd)) ≡ 22
K5fwd-sub = refl

K5fwd-atoms : length (stateAtoms (¬ axK5fwd)) ≡ 8
K5fwd-atoms = refl

K5fwd-rows : length (allVecs (length (stateAtoms (¬ axK5fwd)))) ≡ 256
K5fwd-rows = refl

K5fwd-states : length (St (¬ axK5fwd)) ≡ 59
K5fwd-states = refl

K5fwd-closure : length (Ust (¬ axK5fwd)) ≡ 9
K5fwd-closure = refl

-- the certificate: four blocks, then nothing is left

K5fwd-cert : sccShape axK5fwd ≡
             removedBlock ∷ removedBlock ∷ removedBlock ∷ removedBlock ∷ emptied ∷ []
K5fwd-cert = refl

check-K5fwd : isProof (decide axK5fwd) ≡ true
check-K5fwd = refl

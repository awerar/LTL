{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Examples -- Figure 11 of exLTL.pdf (Schmitt and Goubault-Larrecq,
-- "Linear Temporal Logic", page 14) run through decide.
--
-- Forty-six named modal and temporal statements, in the box/diamond fragment
-- -- no nxt occurs in any of them.  The figure's last column marks the ones its
-- procedure reports valid; here each is a checked equation instead, and the
-- checkmark is the BRANCH decide takes:
--
--   isProof (decide X) = true    decide returned inl, a derivation of X in L
--   isProof (decide X) = false   decide returned inr, a lasso countermodel
--                                together with  ⊢ X -> Empty
--
-- So the file is not a comparison of two programs' outputs.  Every line below
-- is a theorem: the true ones assert that a derivation exists, the false ones
-- that none does, and both are certified by the type of decide (LTL.Decide).
--
-- The twenty-two marked in the figure are T, G, pb5, lin1, Dum, Dum1, Dum2,
-- Dum3, Dum4, D, 4, 4M, G0, H, H+, L, L+, L++, X, K3, K4, K5, and those are
-- exactly the twenty-two that come out true here.
--
-- The names are the figure's, with ax- prefixed where the figure's name is not
-- an Agda identifier (4, 5, 4M, 5M, +, ++).
--
-- The file takes about 17 s, which is forty-six decision problems and not one
-- proof: the 5 s rule of FORMALISATION-PLAN.md section 4a is a detector for
-- proofs that have drifted from the note, and does not apply to a benchmark.
-- The figure's own times are 0.017-0.083 s per formula for a procedure written
-- in ML; these run inside Agda's evaluator, on the decision procedure as a
-- type-theoretic boolean function, with no extraction anywhere.

module LTL.Examples where

open import LTL.Decide public

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

check_T : isProof (decide axT) ≡ true
check_T = refl

check_pb2 : isProof (decide pb2) ≡ false
check_pb2 = refl

check_G : isProof (decide axG) ≡ true
check_G = refl

check_M : isProof (decide axM) ≡ false
check_M = refl

check_M2 : isProof (decide axM2) ≡ false
check_M2 = refl

check_M3 : isProof (decide axM3) ≡ false
check_M3 = refl

check_pb5 : isProof (decide pb5) ≡ true
check_pb5 = refl

check_lin1 : isProof (decide lin1) ≡ true
check_lin1 = refl

check_Dum : isProof (decide axDum) ≡ true
check_Dum = refl

check_Dum1 : isProof (decide axDum1) ≡ true
check_Dum1 = refl

check_Dum2 : isProof (decide axDum2) ≡ true
check_Dum2 = refl

check_Dum3 : isProof (decide axDum3) ≡ true
check_Dum3 = refl

check_Dum4 : isProof (decide axDum4) ≡ true
check_Dum4 = refl

check_D : isProof (decide axD) ≡ true
check_D = refl

check_ax4 : isProof (decide ax4) ≡ true
check_ax4 = refl

check_ax4M : isProof (decide ax4M) ≡ true
check_ax4M = refl

check_ax5 : isProof (decide ax5) ≡ false
check_ax5 = refl

check_ax5M : isProof (decide ax5M) ≡ false
check_ax5M = refl

check_B : isProof (decide axB) ≡ false
check_B = refl

check_BM : isProof (decide axBM) ≡ false
check_BM = refl

check_G0 : isProof (decide axG0) ≡ true
check_G0 = refl

check_H : isProof (decide axH) ≡ true
check_H = refl

check_Hplus : isProof (decide axHplus) ≡ true
check_Hplus = refl

check_L : isProof (decide axL) ≡ true
check_L = refl

check_Lplus : isProof (decide axLplus) ≡ true
check_Lplus = refl

check_Lplusplus : isProof (decide axLplusplus) ≡ true
check_Lplusplus = refl

check_Pt : isProof (decide axPt) ≡ false
check_Pt = refl

check_W : isProof (decide axW) ≡ false
check_W = refl

check_Z : isProof (decide axZ) ≡ false
check_Z = refl

check_Grz : isProof (decide axGrz) ≡ false
check_Grz = refl

check_Grz1 : isProof (decide axGrz1) ≡ false
check_Grz1 = refl

check_Grz2 : isProof (decide axGrz2) ≡ false
check_Grz2 = refl

check_Grz3 : isProof (decide axGrz3) ≡ false
check_Grz3 = refl

check_Grz4 : isProof (decide axGrz4) ≡ false
check_Grz4 = refl

check_Grz5 : isProof (decide axGrz5) ≡ false
check_Grz5 = refl

check_F : isProof (decide axF) ≡ false
check_F = refl

check_Hs : isProof (decide axHs) ≡ false
check_Hs = refl

check_P : isProof (decide axP) ≡ false
check_P = refl

check_R : isProof (decide axR) ≡ false
check_R = refl

check_X : isProof (decide axX) ≡ true
check_X = refl

check_Zem : isProof (decide axZem) ≡ false
check_Zem = refl

check_K1 : isProof (decide axK1) ≡ false
check_K1 = refl

check_K2 : isProof (decide axK2) ≡ false
check_K2 = refl

check_K3 : isProof (decide axK3) ≡ true
check_K3 = refl

check_K4 : isProof (decide axK4) ≡ true
check_K4 = refl

check_K5 : isProof (decide axK5) ≡ true
check_K5 = refl

------------------------------------------------------------------------
-- Two of the countermodels, read off.
--
-- decide returns the lasso as a record; cmStart, cmRest and cmCycle give the
-- states as the procedure stores them, but a bit vector read against
-- sub (¬ Q) is not something one wants to look at.  traceOf evaluates a
-- chosen formula at the successive stages of the run instead, and shapeOf says
-- where the run starts repeating: with shapeOf Q = r , c the run is
--
--    v0 , rest_0 , ... , rest_{r-1} , then the last c of those, forever
--
-- so it is periodic from stage  1 + r - c  on, with period c.
--
-- Nothing here is an extra assumption.  traceOf goes through eval of LTL.Eval,
-- which is the semantics soundness (G26) is proved against, so
-- "traceOf Q Q 1 = false ∷ []" below and the ⊢ Q -> Empty field of the
-- record are the same fact seen from the two ends.

------------------------------------------------------------------------
-- pb2 = p ⇒ □ p.
--
-- shapeOf pb2 = 3 , 1: three states then a fixed point, so the run is
--
--    p       1  0  1  1  1  1  1  1  ...
--    □ p   0  0  1  1
--    pb2     0  1  1  1
--
-- p holds now and fails at the next stage, which refutes □ p now; from
-- stage 2 on p holds forever, so □ p holds and pb2 holds at every stage but
-- the first.  That single false at stage 0 is the countermodel.

pb2_shape : shapeOf pb2 ≡ (3 , 1)
pb2_shape = refl

pb2_p : traceOf pb2 pv 8 ≡
        true ∷ false ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
pb2_p = refl

pb2_□ : traceOf pb2 (□ pv) 4 ≡ false ∷ false ∷ true ∷ true ∷ []
pb2_□ = refl

pb2_input : traceOf pb2 pb2 4 ≡ false ∷ true ∷ true ∷ true ∷ []
pb2_input = refl

------------------------------------------------------------------------
-- axM2 = ◇ □ (p ⇒ □ p).
--
-- shapeOf axM2 = 2 , 2: the cycle has two states and the stem is empty, so
-- the run is periodic from stage 1 with period 2 --
--
--    p            1  0  1  0  1  0  1  0  ...
--    p ⇒ □ p      0  1  0  1  0  1  0  1
--    axM2         0  0  0  0
--
-- p alternates forever, so □ p is false at every stage, so p ⇒ □ p fails
-- at exactly the stages where p holds -- infinitely often.  Hence
-- □ (p ⇒ □ p) holds nowhere and its diamond is false at every stage: the
-- alternating run refutes axM2 not just at stage 0 but everywhere, which is
-- what an eventuality being unfulfillable on a cycle looks like.

axM2_shape : shapeOf axM2 ≡ (2 , 2)
axM2_shape = refl

axM2_p : traceOf axM2 pv 8 ≡
         true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ []
axM2_p = refl

axM2_step : traceOf axM2 (pv ⇒ □ pv) 8 ≡
            false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ []
axM2_step = refl

axM2_input : traceOf axM2 axM2 4 ≡ false ∷ false ∷ false ∷ false ∷ []
axM2_input = refl

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
-- is the elimination of Definition 3.1 followed by Theorem 4.1.
--
-- Measured.  Sub of the negation has length 22, so the naive state space is
-- 2^22 = 4194304 vectors.  The atoms are p, q and the six box-subformulas
--
--    □ ¬ (p ∨ q) , □ ◇ (p ∨ q) , □ ¬ p , □ ◇ p ,
--    □ ¬ q , □ ◇ q
--
-- so 2^8 = 256 assignments are built, 59 of them are states, and the closure of
-- the ones containing the negation has 9 members.  The elimination then runs
--
--    9  ->  8  ->  4  ->  0
--
-- and EVERY removal goes by (R2).  Not one state is dropped for want of a
-- successor: the whole refutation is the loop-invariant case, which is what one
-- would expect of a formula that says an eventuality recurring forever must
-- recur in one of two ways.  So this example exercises extractR2 -- the
-- invariant B = beta_W, (Ind) through indRule, the greatest fixed point of
-- LTL.Gfp -- nine states deep, where bnb exercises it once.
--
-- decide returns inl in 0.9 s.  Before Phase 8 the state list alone would have
-- been 2^22 vectors filtered one at a time; it is the atom generator of G30
-- that makes the example reachable at all.

axK5fwd : Formula
axK5fwd = □ ◇ (pv ∨ qv) ⇒ □ ◇ pv ∨ □ ◇ qv

K5fwd_sub : length (sub (¬ axK5fwd)) ≡ 22
K5fwd_sub = refl

K5fwd_atoms : length (atoms (sub (¬ axK5fwd))) ≡ 8
K5fwd_atoms = refl

K5fwd_cands : length (cands (¬ axK5fwd)) ≡ 256
K5fwd_cands = refl

K5fwd_states : length (StC (¬ axK5fwd)) ≡ 59
K5fwd_states = refl

K5fwd_closure : length (Ust (¬ axK5fwd)) ≡ 9
K5fwd_closure = refl

-- the first round removes one state, and by (R2)

K5fwd_round1 : reasons (¬ axK5fwd) (Ust (¬ axK5fwd)) ≡ false ∷ []
K5fwd_round1 = refl

K5fwd_uinf : length (Uinf (¬ axK5fwd)) ≡ 0
K5fwd_uinf = refl

check_K5fwd : isProof (decide axK5fwd) ≡ true
check_K5fwd = refl

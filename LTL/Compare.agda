{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Compare -- checkpoint C8 of PHASE11-PLAN.md: the three procedures set
-- against each other.
--
-- Kept out of LTL.Proofs deliberately.  This file is a BENCHMARK -- it runs
-- forty-seven decision problems through a second decision procedure -- and the
-- 5 s rule of FORMALISATION-PLAN.md section 4a is a detector for proofs that
-- have drifted from the note, not a budget for measurements.  LTL.Examples is
-- on the same side of that line and for the same reason.
--
-- C8 asks three things.
--
-- 1. AGREEMENT.  isProof (decideSCC X) = isProof (decide X) for every statement
--    of LTL.Examples.  Each agree-X below is that equation, and it is a theorem
--    about the two PROCEDURES, not a comparison of two printouts: both sides
--    are closed booleans and refl checks them.  It is proved as scc-X composed
--    with LTL.Examples' own check-X rather than by one refl on the pair, so
--    that decide is not run a second time -- agreeOn is the composition and it
--    is the only inference in the file.
--
--    All forty-seven agree.  Twenty-two are proofs and twenty-five are
--    countermodels, exactly as the figure and LTL.Examples record.
--
-- 2. THE LASSO ON THE C5 FORMULA,  □ (p ∨ q) ⇒ □ p ∨ □ q .  The two
--    procedures return DIFFERENT countermodels, which is what the plan
--    anticipated and called the interesting observation:
--
--                    start          stem   cycle
--        decide      c5pqNow          3      1
--        decideSCC   c5q              2      4
--
--    (the run stores stem ++ cycle, so the recorded rest lengths are 4 and 6).
--    decide starts where satB finds the first surviving state containing the
--    negation and closes the loop at the first repeated round boundary, giving
--    the single state at which p and q hold forever.  decideSCC starts where
--    ustSeedTo finds a seed reaching the terminal component and takes mkCirc's
--    cycle, which is one leg per eventuality prepended to the bare loop -- and
--    sub (¬ c5) has three eventualities, so the cycle is four times round.
--    Both are countermodels and each carries its own  ⊢ c5 -> Empty ; that
--    they differ is a fact about the two constructions and not a discrepancy.
--
-- 3. WALL CLOCK.  Measured on the machine of section 4g, cold, with the import
--    baseline (0.19 s) subtracted:
--
--                          decide     decideSCC
--        c5                 0.19 s      0.18 s      countermodel branch
--        axK5fwd            0.78 s      1.24 s      proof branch
--
--    The plan predicted SCC would be slower, "because mutual reachability is
--    quadratic in the component where gfpW is one removing pass".  Confirmed on
--    the proof branch, where it is 1.6x; refuted on the countermodel branch,
--    where the two are level.  The reason is visible in the code rather than in
--    the numbers.  On the proof branch decideSCC pays for reachSet and sccOf
--    over the whole of Ust P and pays nothing for the elimination, which it
--    never runs; on the countermodel branch it pays for BOTH -- the graph search
--    to find the component and uinfTrap to put the loop inside Uinf P -- but
--    saves the round construction and the boundary search of Proposition 5.3,
--    and on c5 those cancel.
--
--    So the phase's own summary stands: the SCC proof is the better explanation
--    and, on the branch where it is the whole story, the worse implementation.
--
--    Across the whole suite the two are level, and neither figure is a clean
--    per-procedure time: LTL.Examples is 23.1 s for decide's forty-seven plus
--    its structural checks (state counts, closures, two countermodels read
--    off), and this file is 20.8 s for decideSCC's forty-seven plus the C5
--    lassos.  The controlled comparison is the two-line table above.
--
-- What the file does NOT claim.  Nothing here says the two procedures agree on
-- every formula -- that would be soundness and completeness of both, which is
-- what their TYPES already say, since each returns ⊢ Q or a countermodel
-- carrying ⊢ Q -> Empty.  Agreement on a list is a check that both are
-- actually running, not the reason to believe either.

module LTL.Compare where

open import LTL.DecideSCC public
open import LTL.Examples  public

------------------------------------------------------------------------
-- The only inference in the file.

agreeOn : (X : Formula) (b : Bool)
       -> isProof (decideSCC X) ≡ b -> isProof (decide X) ≡ b
       -> isProof (decideSCC X) ≡ isProof (decide X)
agreeOn X b e1 e2 = trans e1 (sym e2)

------------------------------------------------------------------------
-- 1a. The forty-seven answers of decideSCC

scc-T : isProof (decideSCC axT) ≡ true
scc-T = refl

scc-pb2 : isProof (decideSCC pb2) ≡ false
scc-pb2 = refl

scc-G : isProof (decideSCC axG) ≡ true
scc-G = refl

scc-M : isProof (decideSCC axM) ≡ false
scc-M = refl

scc-M2 : isProof (decideSCC axM2) ≡ false
scc-M2 = refl

scc-M3 : isProof (decideSCC axM3) ≡ false
scc-M3 = refl

scc-pb5 : isProof (decideSCC pb5) ≡ true
scc-pb5 = refl

scc-lin1 : isProof (decideSCC lin1) ≡ true
scc-lin1 = refl

scc-Dum : isProof (decideSCC axDum) ≡ true
scc-Dum = refl

scc-Dum1 : isProof (decideSCC axDum1) ≡ true
scc-Dum1 = refl

scc-Dum2 : isProof (decideSCC axDum2) ≡ true
scc-Dum2 = refl

scc-Dum3 : isProof (decideSCC axDum3) ≡ true
scc-Dum3 = refl

scc-Dum4 : isProof (decideSCC axDum4) ≡ true
scc-Dum4 = refl

scc-D : isProof (decideSCC axD) ≡ true
scc-D = refl

scc-ax4 : isProof (decideSCC ax4) ≡ true
scc-ax4 = refl

scc-ax4M : isProof (decideSCC ax4M) ≡ true
scc-ax4M = refl

scc-ax5 : isProof (decideSCC ax5) ≡ false
scc-ax5 = refl

scc-ax5M : isProof (decideSCC ax5M) ≡ false
scc-ax5M = refl

scc-B : isProof (decideSCC axB) ≡ false
scc-B = refl

scc-BM : isProof (decideSCC axBM) ≡ false
scc-BM = refl

scc-G0 : isProof (decideSCC axG0) ≡ true
scc-G0 = refl

scc-H : isProof (decideSCC axH) ≡ true
scc-H = refl

scc-Hplus : isProof (decideSCC axHplus) ≡ true
scc-Hplus = refl

scc-L : isProof (decideSCC axL) ≡ true
scc-L = refl

scc-Lplus : isProof (decideSCC axLplus) ≡ true
scc-Lplus = refl

scc-Lplusplus : isProof (decideSCC axLplusplus) ≡ true
scc-Lplusplus = refl

scc-Pt : isProof (decideSCC axPt) ≡ false
scc-Pt = refl

scc-W : isProof (decideSCC axW) ≡ false
scc-W = refl

scc-Z : isProof (decideSCC axZ) ≡ false
scc-Z = refl

scc-Grz : isProof (decideSCC axGrz) ≡ false
scc-Grz = refl

scc-Grz1 : isProof (decideSCC axGrz1) ≡ false
scc-Grz1 = refl

scc-Grz2 : isProof (decideSCC axGrz2) ≡ false
scc-Grz2 = refl

scc-Grz3 : isProof (decideSCC axGrz3) ≡ false
scc-Grz3 = refl

scc-Grz4 : isProof (decideSCC axGrz4) ≡ false
scc-Grz4 = refl

scc-Grz5 : isProof (decideSCC axGrz5) ≡ false
scc-Grz5 = refl

scc-F : isProof (decideSCC axF) ≡ false
scc-F = refl

scc-Hs : isProof (decideSCC axHs) ≡ false
scc-Hs = refl

scc-P : isProof (decideSCC axP) ≡ false
scc-P = refl

scc-R : isProof (decideSCC axR) ≡ false
scc-R = refl

scc-X : isProof (decideSCC axX) ≡ true
scc-X = refl

scc-Zem : isProof (decideSCC axZem) ≡ false
scc-Zem = refl

scc-K1 : isProof (decideSCC axK1) ≡ false
scc-K1 = refl

scc-K2 : isProof (decideSCC axK2) ≡ false
scc-K2 = refl

scc-K3 : isProof (decideSCC axK3) ≡ true
scc-K3 = refl

scc-K4 : isProof (decideSCC axK4) ≡ true
scc-K4 = refl

scc-K5 : isProof (decideSCC axK5) ≡ true
scc-K5 = refl

scc-K5fwd : isProof (decideSCC axK5fwd) ≡ true
scc-K5fwd = refl

------------------------------------------------------------------------
-- 1b. and that they are the answers of decide

agree-T : isProof (decideSCC axT) ≡ isProof (decide axT)
agree-T = agreeOn axT true scc-T check-T

agree-pb2 : isProof (decideSCC pb2) ≡ isProof (decide pb2)
agree-pb2 = agreeOn pb2 false scc-pb2 check-pb2

agree-G : isProof (decideSCC axG) ≡ isProof (decide axG)
agree-G = agreeOn axG true scc-G check-G

agree-M : isProof (decideSCC axM) ≡ isProof (decide axM)
agree-M = agreeOn axM false scc-M check-M

agree-M2 : isProof (decideSCC axM2) ≡ isProof (decide axM2)
agree-M2 = agreeOn axM2 false scc-M2 check-M2

agree-M3 : isProof (decideSCC axM3) ≡ isProof (decide axM3)
agree-M3 = agreeOn axM3 false scc-M3 check-M3

agree-pb5 : isProof (decideSCC pb5) ≡ isProof (decide pb5)
agree-pb5 = agreeOn pb5 true scc-pb5 check-pb5

agree-lin1 : isProof (decideSCC lin1) ≡ isProof (decide lin1)
agree-lin1 = agreeOn lin1 true scc-lin1 check-lin1

agree-Dum : isProof (decideSCC axDum) ≡ isProof (decide axDum)
agree-Dum = agreeOn axDum true scc-Dum check-Dum

agree-Dum1 : isProof (decideSCC axDum1) ≡ isProof (decide axDum1)
agree-Dum1 = agreeOn axDum1 true scc-Dum1 check-Dum1

agree-Dum2 : isProof (decideSCC axDum2) ≡ isProof (decide axDum2)
agree-Dum2 = agreeOn axDum2 true scc-Dum2 check-Dum2

agree-Dum3 : isProof (decideSCC axDum3) ≡ isProof (decide axDum3)
agree-Dum3 = agreeOn axDum3 true scc-Dum3 check-Dum3

agree-Dum4 : isProof (decideSCC axDum4) ≡ isProof (decide axDum4)
agree-Dum4 = agreeOn axDum4 true scc-Dum4 check-Dum4

agree-D : isProof (decideSCC axD) ≡ isProof (decide axD)
agree-D = agreeOn axD true scc-D check-D

agree-ax4 : isProof (decideSCC ax4) ≡ isProof (decide ax4)
agree-ax4 = agreeOn ax4 true scc-ax4 check-ax4

agree-ax4M : isProof (decideSCC ax4M) ≡ isProof (decide ax4M)
agree-ax4M = agreeOn ax4M true scc-ax4M check-ax4M

agree-ax5 : isProof (decideSCC ax5) ≡ isProof (decide ax5)
agree-ax5 = agreeOn ax5 false scc-ax5 check-ax5

agree-ax5M : isProof (decideSCC ax5M) ≡ isProof (decide ax5M)
agree-ax5M = agreeOn ax5M false scc-ax5M check-ax5M

agree-B : isProof (decideSCC axB) ≡ isProof (decide axB)
agree-B = agreeOn axB false scc-B check-B

agree-BM : isProof (decideSCC axBM) ≡ isProof (decide axBM)
agree-BM = agreeOn axBM false scc-BM check-BM

agree-G0 : isProof (decideSCC axG0) ≡ isProof (decide axG0)
agree-G0 = agreeOn axG0 true scc-G0 check-G0

agree-H : isProof (decideSCC axH) ≡ isProof (decide axH)
agree-H = agreeOn axH true scc-H check-H

agree-Hplus : isProof (decideSCC axHplus) ≡ isProof (decide axHplus)
agree-Hplus = agreeOn axHplus true scc-Hplus check-Hplus

agree-L : isProof (decideSCC axL) ≡ isProof (decide axL)
agree-L = agreeOn axL true scc-L check-L

agree-Lplus : isProof (decideSCC axLplus) ≡ isProof (decide axLplus)
agree-Lplus = agreeOn axLplus true scc-Lplus check-Lplus

agree-Lplusplus : isProof (decideSCC axLplusplus) ≡ isProof (decide axLplusplus)
agree-Lplusplus = agreeOn axLplusplus true scc-Lplusplus check-Lplusplus

agree-Pt : isProof (decideSCC axPt) ≡ isProof (decide axPt)
agree-Pt = agreeOn axPt false scc-Pt check-Pt

agree-W : isProof (decideSCC axW) ≡ isProof (decide axW)
agree-W = agreeOn axW false scc-W check-W

agree-Z : isProof (decideSCC axZ) ≡ isProof (decide axZ)
agree-Z = agreeOn axZ false scc-Z check-Z

agree-Grz : isProof (decideSCC axGrz) ≡ isProof (decide axGrz)
agree-Grz = agreeOn axGrz false scc-Grz check-Grz

agree-Grz1 : isProof (decideSCC axGrz1) ≡ isProof (decide axGrz1)
agree-Grz1 = agreeOn axGrz1 false scc-Grz1 check-Grz1

agree-Grz2 : isProof (decideSCC axGrz2) ≡ isProof (decide axGrz2)
agree-Grz2 = agreeOn axGrz2 false scc-Grz2 check-Grz2

agree-Grz3 : isProof (decideSCC axGrz3) ≡ isProof (decide axGrz3)
agree-Grz3 = agreeOn axGrz3 false scc-Grz3 check-Grz3

agree-Grz4 : isProof (decideSCC axGrz4) ≡ isProof (decide axGrz4)
agree-Grz4 = agreeOn axGrz4 false scc-Grz4 check-Grz4

agree-Grz5 : isProof (decideSCC axGrz5) ≡ isProof (decide axGrz5)
agree-Grz5 = agreeOn axGrz5 false scc-Grz5 check-Grz5

agree-F : isProof (decideSCC axF) ≡ isProof (decide axF)
agree-F = agreeOn axF false scc-F check-F

agree-Hs : isProof (decideSCC axHs) ≡ isProof (decide axHs)
agree-Hs = agreeOn axHs false scc-Hs check-Hs

agree-P : isProof (decideSCC axP) ≡ isProof (decide axP)
agree-P = agreeOn axP false scc-P check-P

agree-R : isProof (decideSCC axR) ≡ isProof (decide axR)
agree-R = agreeOn axR false scc-R check-R

agree-X : isProof (decideSCC axX) ≡ isProof (decide axX)
agree-X = agreeOn axX true scc-X check-X

agree-Zem : isProof (decideSCC axZem) ≡ isProof (decide axZem)
agree-Zem = agreeOn axZem false scc-Zem check-Zem

agree-K1 : isProof (decideSCC axK1) ≡ isProof (decide axK1)
agree-K1 = agreeOn axK1 false scc-K1 check-K1

agree-K2 : isProof (decideSCC axK2) ≡ isProof (decide axK2)
agree-K2 = agreeOn axK2 false scc-K2 check-K2

agree-K3 : isProof (decideSCC axK3) ≡ isProof (decide axK3)
agree-K3 = agreeOn axK3 true scc-K3 check-K3

agree-K4 : isProof (decideSCC axK4) ≡ isProof (decide axK4)
agree-K4 = agreeOn axK4 true scc-K4 check-K4

agree-K5 : isProof (decideSCC axK5) ≡ isProof (decide axK5)
agree-K5 = agreeOn axK5 true scc-K5 check-K5

agree-K5fwd : isProof (decideSCC axK5fwd) ≡ isProof (decide axK5fwd)
agree-K5fwd = agreeOn axK5fwd true scc-K5fwd check-K5fwd

------------------------------------------------------------------------
-- 2. The two lassos on the C5 formula.
--
-- lassoOfDecide reads a countermodel as (start , rest , cycle), where rest is
-- the run's stored remainder -- the stem followed by the cycle.

lassoLen : Val × List Val × List Val -> Nat × Nat
lassoLen (v , a , b) = length a , length b

c5Decide : Val × List Val × List Val
c5Decide = lassoOfDecide c5 (decide c5)

c5Scc : Val × List Val × List Val
c5Scc = lassoOfDecide c5 (decideSCC c5)

c5-decide-start : fst c5Decide ≡ᵛ c5pqNow ≡ true
c5-decide-start = refl

c5-scc-start : fst c5Scc ≡ᵛ c5q ≡ true
c5-scc-start = refl

c5-decide-len : lassoLen c5Decide ≡ (4 , 1)
c5-decide-len = refl

c5-scc-len : lassoLen c5Scc ≡ (6 , 4)
c5-scc-len = refl

-- and the observation itself: the two countermodels do not even start at the
-- same state.

c5-differ : fst c5Decide ≡ᵛ fst c5Scc ≡ false
c5-differ = refl

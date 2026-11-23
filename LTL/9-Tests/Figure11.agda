{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.9-Tests.Figure11 -- the forty-six statements of Figure 11 of Schmitt
-- and Goubault-Larrecq, "Linear Temporal Logic" (page 14), as formulas.
--
-- Only the definitions: LTL.9-Benchmarks.Examples runs decide on them, which
-- is slow.  Kept apart so that tools/show-proof can offer these names without
-- checking the benchmarks.  Names are the figure's, prefixed with ax- where
-- the figure's name is not an Agda identifier (4, 5, 4M, 5M, +, ++).

module LTL.9-Tests.Figure11 where

open import LTL.1-Lib.Base
open import LTL.2-Syntax.Formula

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

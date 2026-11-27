{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.9-Benchmarks.Lecture -- the worked example of the course's lecture 15
-- notes (not in the repository), run through decide:
--
--     F a ∧ F b  ⇒  F (a ∧ b)
--
-- The notes analyse it by hand (appendix, pages 139-141): Sub, the locally
-- consistent states with F(a and b) = 0, their edges, and a countermodel.
--
-- THE GRAPH IS THE SAME.  Writing a state as  8a + 4b + 2 Fa + Fb , the
-- lecture's s0..s7 are 0, 1, 2, 3, 5, 7, 10, 11, and Ust of the negation is
-- exactly those eight, with the same twenty-four edges.  The lecture ASSUMES
-- F(a and b) = 0; here it follows, since the negation forces it and the
-- closure propagates it.
--
-- THE COUNTERMODEL IS NOT.  The lecture gives  s3 -> s5 -> s7 -> s7 -> ... ,
-- which is not fair: at s7, Fb = 1 and b = 0, so looping there promises b and
-- never delivers it.  (It presumably meant  s3 -> s5 -> s7 -> s5 -> ... .)
-- decide returns
--
--     s7 -> s4 -> s0 -> s0 -> ...          (loop at s0)
--
-- with a at stage 0, b at stage 1 and everything false from stage 2 on.  Its
-- cycle holds four copies of the loop at s0, one per eventuality plus the
-- loop itself.  lec-fair checks the objection against the fairness predicate
-- evPred of LTL.7-SCC.SccLasso: s7 is outside F_Fb, s0 inside it, and s7 inside
-- F_Fa.

module LTL.9-Benchmarks.Lecture where

open import LTL.8-Procedures.Everything public

------------------------------------------------------------------------
-- The formula, in the box-only syntax.

pa : Formula
pa = var zero

pb : Formula
pb = var (suc zero)

fab : Formula
fab = ◇ pa ∧ ◇ pb ⇒ ◇ (pa ∧ pb)

R : Formula
R = ¬ fab

------------------------------------------------------------------------
-- The state space: 21 positions of sub, but only 5 atoms (a, b and the boxes
-- behind the three F's), so 32 rows and 17 states.  The closure is 8.

lec-sizes : length (sub R) ∷ length (stateAtoms R)
             ∷ length (rows (stateAtoms R))
             ∷ length (St R) ∷ length (Ust R)
             ∷ length (eventualities R) ∷ [] ≡
               21 ∷ 5 ∷ 32 ∷ 17 ∷ 8 ∷ 3 ∷ []
lec-sizes = refl

------------------------------------------------------------------------
-- The eight states, in the lecture's own encoding.

bitV : Bool -> Nat -> Nat
bitV true  n = n
bitV false n = 0

num : Val R -> Nat
num v = bitV (valOf R v pa) 8 + bitV (valOf R v pb) 4
        + bitV (valOf R v (◇ pa)) 2 + bitV (valOf R v (◇ pb)) 1

-- s0 = 0, s1 = 1, s2 = 2, s3 = 3, s4 = 5, s5 = 7, s6 = 10, s7 = 11, in the
-- order the closure produces them.

lec-states : map num (Ust R) ≡ 0 ∷ 5 ∷ 1 ∷ 10 ∷ 2 ∷ 11 ∷ 7 ∷ 3 ∷ []
lec-states = refl

-- and the same profile: a and b true at two states each, Fa and Fb at five
-- each, F(a and b) at none.

lec-profile : length (filter (λ v -> valOf R v pa) (Ust R))
               ∷ length (filter (λ v -> valOf R v pb) (Ust R))
               ∷ length (filter (λ v -> valOf R v (◇ pa)) (Ust R))
               ∷ length (filter (λ v -> valOf R v (◇ pb)) (Ust R))
               ∷ length (filter (λ v -> valOf R v (◇ (pa ∧ pb))) (Ust R))
               ∷ [] ≡ 2 ∷ 2 ∷ 5 ∷ 5 ∷ 0 ∷ []
lec-profile = refl

------------------------------------------------------------------------
-- The twenty-four edges.  The lecture lists  s0:1 s1:2 s2:2 s3:3 s4:3 s5:5
-- s6:3 s7:5 ; here they come in the closure's order, s0 s4 s1 s6 s2 s7 s5 s3.

lec-outdeg : map (λ v -> length (succs R (Ust R) v)) (Ust R) ≡
             1 ∷ 3 ∷ 2 ∷ 3 ∷ 2 ∷ 5 ∷ 5 ∷ 3 ∷ []
lec-outdeg = refl

lec-edges : length (concat (map (λ v -> succs R (Ust R) v) (Ust R))) ≡ 24
lec-edges = refl

------------------------------------------------------------------------
-- The decision, and the lasso, read as (start , rest , cycle), where rest is
-- the stem followed by the cycle.

lec-notValid : isProof (decide fab) ≡ false
lec-notValid = refl

lec-cm : LassoCountermodel fab
lec-cm = countermodelFrom (decide fab) refl

lo : Val R × List (Val R) × List (Val R)
lo = LassoCountermodel.start lec-cm , cmRest fab lec-cm , cmCycle fab lec-cm

-- Start, stem-and-cycle, cycle: s7, then s4 and the loop at s0.  One equation,
-- because every mention of lo re-runs the countermodel branch.  The file takes
-- about 11 s to check.

-- The triple gets its own typed definition: written inline on the left of ≡,
-- inferring the type of the Σ pair forces lo and takes over half an hour.

lec-shape : Nat × List Nat × List Nat
lec-shape = num (fst lo) , map num (fst (snd lo)) , map num (snd (snd lo))

lec-run : lec-shape ≡ (11 , 5 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [] , 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
lec-run = refl

------------------------------------------------------------------------
-- Why the lecture's path is not a countermodel.  s7 is the start of the run,
-- s0 its cycle.  evPred R A z says the eventuality with box-argument A is not
-- pending at z or already fails there; for F b this is the lecture's own
-- F_Fb = { v | v (Fb) = 0 or v (b) = 1 } .

s7 : Val R
s7 = fst lo

s0 : Val R
s0 = nth (snd (snd lo)) zero (rowOf (λ A -> false) (stateAtoms R))

-- s7 is outside F_Fb, so the lecture's loop at s7 cannot be fair;
-- s0 is inside it, so the loop decide returns can be;
-- and s7 IS inside F_Fa, exactly as the lecture says, since a holds there.

lec-fair : evPred R (¬ pb) s7 ∷ evPred R (¬ pb) s0
            ∷ evPred R (¬ pa) s7 ∷ [] ≡ false ∷ true ∷ true ∷ []
lec-fair = refl

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Elim -- G8 of FORMALISATION-PLAN.md.
--
-- Definition 3.1 of m4.tex.  Starting from U_0 = St(P), remove every state to
-- which one of the following applies, and repeat:
--
--   (R1)  v has no ->-successor in U_k;
--   (R2)  for some j, the j-th eventuality is pending at v and is fulfilled at
--         no state of Reach_{U_k}(v).
--
-- The eventualities are indexed by the box-subformulas of P: □ A is pending
-- at v when □ A is not in v, and fulfilled at w when A is not in w.
--
-- (R2) is stated through gfpW of LTL.Gfp rather than through reach: "the j-th
-- eventuality is fulfilled at no state of Reach_{U_k}(v)" is written "v belongs
-- to the largest ->-closed set of states of U_k at which A_j still holds".
-- gfpSound and gfpComplete of LTL.Gfp show the two are the same condition, with
-- Reach taken in its exact sense (the inductive type Path of ->-paths inside
-- U_k).  The reason for the change is Theorem 4.1: its case (R2) needs the set
-- to be closed under successors, and for a greatest fixed point that is free,
-- where for the reachable set it is a pigeonhole argument.
--
-- Two things are new in Phase 8, and both are G29.
--
-- The iteration stops when a round removes nothing, by recursion on a Bar,
-- instead of being run  length (St P)  times and shown afterwards to have
-- reached a fixed point.  There is no fuel and no ≤ measure here at all.
--
-- The gfp sets are computed ONCE PER ROUND rather than once per state.  W_j
-- does not depend on the state being tested, but written as  v ∈ᵛ gfpW P us A
-- under the binder for v it was rebuilt for every pending state of the
-- round, which is where most of the 34.6 s of checkpoint C5 was going.  evList
-- pairs each eventuality with its set, the pair list is the argument the round
-- filters against, and badEv reads the set out of the pair.  Laziness keeps the
-- cost down further: the set in a pair is forced only if the eventuality is
-- actually pending at the state being tested.

module LTL.Elim where

open import LTL.Gfp public

------------------------------------------------------------------------
-- The eventualities.
--
-- □Args -- the A for which □ A occurs in sub P -- was defined here until
-- Phase 9 moved it to LTL.Skel, which is below Deriv and so reachable from
-- LTL.Complete as well; see the comment there.

------------------------------------------------------------------------
-- (R1)

r1 : Formula -> List Val -> Val -> Bool
r1 P us v = null (succs P us v)

pending : Formula -> Val -> Formula -> Bool
pending P v A = ¬ᵇ valOf P v (□ A)

------------------------------------------------------------------------
-- (R2), with the sets hoisted out of the state loop

-- An eventuality □A of Sub P, given by its argument A, paired with its gfp set
-- W_A = gfpW P us A.

Ev : Set
Ev = Formula × List Val

evList : Formula -> List Val -> List Ev
evList P us = map (λ A -> A , gfpW P us A) (□Args (sub P))

evList-mem : (P : Formula) (us : List Val) {A : Formula}
          -> A ∈ □Args (sub P) -> (A , gfpW P us A) ∈ evList P us
evList-mem P us m = memMap (λ A -> A , gfpW P us A) m

evList-of : (P : Formula) (us : List Val) {A : Formula} {W : List Val}
         -> (A , W) ∈ evList P us
         -> A ∈ □Args (sub P) × W ≡ gfpW P us A
evList-of P us {A} {W} m =
  fromSig (map-mem-inv (λ B -> B , gfpW P us B) (□Args (sub P)) m)
  where
    fromSig : (Σ[ B ∈ Formula ] B ∈ □Args (sub P) ×
                                (A , W) ≡ (B , gfpW P us B))
           -> A ∈ □Args (sub P) × W ≡ gfpW P us A
    fromSig (B , mB , e) =
      subst (λ C -> C ∈ □Args (sub P) × W ≡ gfpW P us C)
            (sym (cong fst e))
            (mB , cong snd e)

-- (R2) fires at v for this eventuality: □A is pending at v and v ∈ W_A.

badEv : Formula -> Val -> Ev -> Bool
badEv P v (A , W) = pending P v A ∧ᵇ (v ∈ᵛ W)

r2 : Formula -> List Ev -> Val -> Bool
r2 P gs v = any (badEv P v) gs

------------------------------------------------------------------------
-- One round

keep : Formula -> List Val -> List Ev -> Val -> Bool
keep P us gs v = ¬ᵇ (r1 P us v ∨ᵇ r2 P gs v)

elimRound : Formula -> List Val -> List Val
elimRound P us = filter (keep P us (evList P us)) us

------------------------------------------------------------------------
-- The elimination, run until a round removes nothing.
--
-- findFalse asks whether any state of us fails keep.  If none does, us is the
-- answer: that is Definition 3.1's stopping condition, read directly rather
-- than recovered from a fixed-point equation.  If one does, it is dropped from
-- the Bar's predicate along with the round, which is what makes the recursive
-- call structurally smaller.

elimGo   : (P : Formula) {E : Pred} (us : List Val)
        -> AllSat E us -> IFin E -> List Val
elimFind : (P : Formula) {E : Pred} (us : List Val)
        -> AllSat E us -> IFin E
        -> FindResult (keep P us (evList P us)) us -> List Val

elimGo P us sb bar =
  elimFind P us sb bar (findFalse (keep P us (evList P us)) us)

elimFind P us sb bar      (allTrue f)   = us
elimFind P us sb (cBar h) (found x m q) =
  elimGo P (elimRound P us)
         (dropAllSat (keep P us (evList P us)) us sb x q) (h x (sb x m))

------------------------------------------------------------------------
-- U_infinity.
--
-- The elimination starts from Ust P, the set LTL.Closure gives the search, not
-- from the complete state list St P, which is left to the derivations (G30).
-- Its Bar is guardedVecBar: the states have length |sub P|, and the vectors of
-- a given length are inductively finite by induction on the length, so nothing
-- here needs the enumeration allVecs -- nor even  length (Ust P) , which the
-- fuel of the old elimIter forced.  guardBar (siles.pdf section 5) is what
-- keeps the finiteness proof from being forced as the search runs.

-- Uinf P is U_inf of m4.tex: what is left of Ust P when (R1) and (R2) no
-- longer remove anything.

Uinf : Formula -> List Val
Uinf P = elimGo P (Ust P) (ustAllSat P) (ustBar P)

-- The states the elimination removed: R = U_st minus U_inf (m4.tex section 4).

removed : Formula -> List Val
removed P = filter (λ v -> ¬ᵇ (v ∈ᵛ Uinf P)) (Ust P)

------------------------------------------------------------------------
-- The decision, as a boolean.
--
-- This is the test of Theorem 6.1: is there a surviving state in which the
-- input formula holds?  Run on ¬ P, "no" means P is provable.

satB : Formula -> Bool
satB P = any (λ v -> valOf P v P) (Uinf P)

------------------------------------------------------------------------
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

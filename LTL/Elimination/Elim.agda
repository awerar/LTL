{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Elimination.Elim -- G8 of FORMALISATION-PLAN.md.
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
-- (R2) is stated through gfpW of LTL.Elimination.Gfp rather than through reach: "the j-th
-- eventuality is fulfilled at no state of Reach_{U_k}(v)" is written "v belongs
-- to the largest ->-closed set of states of U_k at which A_j still holds".
-- gfpSound and gfpComplete of LTL.Elimination.Gfp show the two are the same condition, with
-- Reach taken in its exact sense (the inductive type Path of ->-paths inside
-- U_k).  The reason for the change is Theorem 4.1: its case (R2) needs the set
-- to be closed under successors, and for a greatest fixed point that is free,
-- where for the reachable set it is a pigeonhole argument.
--
-- Two implementation choices (G29).
--
-- The iteration stops when a round removes nothing, by recursion on a Bar.
-- There is no fuel and no ≤ measure here at all.
--
-- The gfp sets are computed ONCE PER ROUND rather than once per state.  W_j
-- does not depend on the state being tested, but written as  v ∈ᵛ gfpW P us A
-- under the binder for v it would be rebuilt for every pending state of the
-- round, which made checkpoint C5 several times slower.  evList pairs each
-- eventuality with its set, the pair list is the argument the round filters
-- against, and badEv reads the set out of the pair.  Laziness keeps the
-- cost down further: the set in a pair is forced only if the eventuality is
-- actually pending at the state being tested.

module LTL.Elimination.Elim where

open import LTL.Elimination.Gfp public

------------------------------------------------------------------------
-- The eventualities are the A for which □ A occurs in sub P: □Args (LTL.Syntax.Skel).

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

module _ (P : Formula) where

  evList : List Val -> List Ev
  evList us = map (λ A -> A , gfpW P us A) (□Args (sub P))

  evList-of : (us : List Val) {A : Formula} {W : List Val}
           -> (A , W) ∈ evList us
           -> A ∈ □Args (sub P) × W ≡ gfpW P us A
  evList-of us {A} {W} m =
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

  badEv : Val -> Ev -> Bool
  badEv v (A , W) = pending P v A ∧ᵇ (v ∈ᵛ W)

  r2 : List Ev -> Val -> Bool
  r2 gs v = any (badEv v) gs

  ------------------------------------------------------------------------
  -- One round

  keep : List Val -> List Ev -> Val -> Bool
  keep us gs v = ¬ᵇ (r1 P us v ∨ᵇ r2 gs v)

  elimRound : List Val -> List Val
  elimRound us = filter (keep us (evList us)) us

  ------------------------------------------------------------------------
  -- The elimination, run until a round removes nothing.
  --
  -- findFalse asks whether any state of us fails keep.  If none does, us is the
  -- answer: that is Definition 3.1's stopping condition, read directly rather
  -- than recovered from a fixed-point equation.  If one does, it is dropped
  -- from the Bar's predicate along with the round, which is what makes the
  -- recursive call structurally smaller.

  elimGo   : {E : Pred} (us : List Val)
          -> AllSat E us -> IFin E -> List Val
  elimFind : {E : Pred} (us : List Val)
          -> AllSat E us -> IFin E
          -> FindResult (keep us (evList us)) us -> List Val

  elimGo us sb bar =
    elimFind us sb bar (findFalse (keep us (evList us)) us)

  elimFind us sb bar      (allTrue f)   = us
  elimFind us sb (cBar h) (found x m q) =
    elimGo (elimRound us)
           (dropAllSat (keep us (evList us)) us sb x q) (h x (sb x m))

  ------------------------------------------------------------------------
  -- U_infinity.
  --
  -- The elimination starts from Ust P, the set LTL.States.Closure gives the search,
  -- not from the complete state list St P, which is left to the derivations
  -- (G30).  Its Bar is guardedVecBar: the states have length |sub P|, and the
  -- vectors of a given length are inductively finite by induction on the
  -- length, so nothing here needs the enumeration allVecs -- nor even
  -- length (Ust P) .  guardBar
  -- (Coquand and Siles, section 5) is what keeps the finiteness proof from
  -- being forced as the search runs.

  -- Uinf P is U_inf of m4.tex: what is left of Ust P when (R1) and (R2) no
  -- longer remove anything.

  Uinf : List Val
  Uinf = elimGo (Ust P) (ustAllSat P) (ustBar P)

------------------------------------------------------------------------
-- Survivors are states.
--
-- Each round only filters, so U_inf is contained in St P.  Hintikka's lemma
-- needs this to read (S1) and (S2) off a state of the run.

module _ (P : Formula) where

  elimGoSub   : {E : Pred} (us : List Val)
             -> (sb : AllSat E us) (bar : IFin E) {x : Val}
             -> x ∈ elimGo P us sb bar -> x ∈ us
  elimFindSub : {E : Pred} (us : List Val)
             -> (sb : AllSat E us) (bar : IFin E)
             -> (fr : FindResult (keep P us (evList P us)) us) {x : Val}
             -> x ∈ elimFind P us sb bar fr -> x ∈ us

  elimGoSub us sb bar =
    elimFindSub us sb bar (findFalse (keep P us (evList P us)) us)

  elimFindSub us sb bar      (allTrue f)    m = m
  elimFindSub us sb (cBar h) (found x mx q) m =
    filter-sub (keep P us (evList P us)) us
               (elimGoSub (elimRound P us)
                          (dropAllSat (keep P us (evList P us)) us sb x q)
                          (h x (sb x mx)) m)

  uinfUst : (x : Val) -> x ∈ Uinf P -> x ∈ Ust P
  uinfUst x m = elimGoSub (Ust P) (ustAllSat P) (ustBar P) m

  uinfSub : (x : Val) -> x ∈ Uinf P -> x ∈ St P
  uinfSub x m = ustSt P (uinfUst x m)

  -- The projection is named rather than applied inline: giving filter-prop its
  -- list argument against the folded  St P  is what keeps the elaborator from
  -- unfolding Uinf while it solves the implicit.

  stIsState : {x : Val} -> x ∈ St P -> isState P x ≡ true
  stIsState m = filter-prop (isState P) (allVecs (length (sub P))) m

  uinfState : (x : Val) -> x ∈ Uinf P -> isState P x ≡ true
  uinfState x m = stIsState (uinfSub x m)

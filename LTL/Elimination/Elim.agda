{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Elimination.Elim -- the state elimination and its result Uinf P.
--
-- Starting from Ust P, remove every state to which one of the following
-- applies, and repeat until a round removes nothing:
--
--   (R1)  v has no successor in the current set U;
--   (R2)  some eventuality is pending at v and is fulfilled at no state
--         reachable from v inside U.
--
-- The eventualities are the A with □ A in sub P: □ A is pending at v when it
-- is not in v, and fulfilled at w when A is not in w.  (R2) is "v lies in gfpW
-- P U A" (LTL.Elimination.Gfp).  decideSCC runs the elimination only in its
-- fair branch, to place the countermodel's loop inside Uinf (uinfTrap).
--
-- The gfp sets are computed once per round, not once per state: evList pairs
-- each eventuality with its set, and laziness forces a set only if the
-- eventuality is pending at the state being tested.

module LTL.Elimination.Elim where

open import LTL.Elimination.Gfp public

------------------------------------------------------------------------
-- The eventualities are the A for which □ A occurs in sub P: □Args.

------------------------------------------------------------------------
-- (R1)

r1 : Formula -> List Val -> Val -> Bool
r1 P us v = null (succs P us v)

pending : Formula -> Val -> Formula -> Bool
pending P v A = ¬ᵇ valOf P v (□ A)

------------------------------------------------------------------------
-- (R2), with the sets hoisted out of the state loop

-- An eventuality, given by its argument A, paired with its gfp set
-- gfpW P us A.

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
  -- The elimination, run until a round removes nothing.  findFalse asks
  -- whether any state of us fails keep; if none does, us is the answer.  If
  -- one does, it is dropped from the Bar's predicate, which makes the
  -- recursive call smaller.

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
  -- U_inf.  The elimination starts from Ust P, and its Bar is guardedVecBar:
  -- the states have length |sub P|, so neither allVecs nor length (Ust P) is
  -- ever computed.

  -- Uinf P: what is left of Ust P when (R1) and (R2) remove nothing.

  Uinf : List Val
  Uinf = elimGo (Ust P) (ustAllSat P) (ustBar P)

------------------------------------------------------------------------
-- Survivors are states.  Each round only filters, so Uinf P lies inside
-- St P.  Hintikka's lemma reads (S1) and (S2) off a state of the run with
-- this.

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

  -- Named rather than applied inline: giving filter-prop its list argument
  -- against the folded  St P  keeps the elaborator from unfolding Uinf.

  stIsState : {x : Val} -> x ∈ St P -> isState P x ≡ true
  stIsState m = filter-prop (isState P) (allVecs (length (sub P))) m

  uinfState : (x : Val) -> x ∈ Uinf P -> isState P x ≡ true
  uinfState x m = stIsState (uinfSub x m)

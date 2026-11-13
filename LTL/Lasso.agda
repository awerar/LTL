{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Lasso -- G23 of FORMALISATION-PLAN.md, Proposition 5.3 of m4.tex.
--
--   If U_inf is nonempty then from every v_0 in U_inf there is a fulfilling
--   lasso: a finite path v_0 -> ... -> v_p followed by a cycle
--   v_p -> ... -> v_q = v_p such that every eventuality pending at a state of
--   the cycle is fulfilled at a state of the cycle.
--
-- The note concatenates rounds, giving boundaries b_0 = v_0, b_1, b_2, ...,
-- and says that two of b_0,...,b_{|U_inf|} coincide "by the pigeonhole
-- principle for an explicitly given finite list, so the indices are found by
-- inspection".  That last clause is taken literally here: rather than proving
-- a pigeonhole lemma and then applying it, the search below carries the states
-- not yet used as a boundary and gives one up at each step.  A new boundary is
-- either one already seen -- and the cycle closes -- or a fresh one, which is
-- then given up.
--
-- Until Phase 8 those states were an explicit pool, with |U_inf| as fuel and a
-- ≤ measure saying the pool shortens; at fuel zero the pool was empty, so the
-- fresh case could not arise.  G29 replaces all of that by a Bar: the states
-- still available ARE the Bar's predicate E, giving one up is exactly the sub-
-- Bar  cBar  hands over, and the search terminates because Bar is well founded.
-- So the pool, the fuel, the measure and the base case all disappear together,
-- and what is left is the invariant  z in U_inf and z not yet a boundary
-- implies E z  -- which is the pigeonhole, still not a lemma.
--
-- The bookkeeping the note leaves implicit -- which prefix is the stem, which
-- suffix is the cycle -- is kept by recording, for each boundary b already
-- passed, a walk v_0 -> b AND a walk b -> current.  Both are extended as the
-- search advances, so when the current boundary turns out to equal b the two
-- halves are already in hand and nothing has to be split.
--
-- The cycle-fulfilment property is the note's argument verbatim: an eventuality
-- pending at a state s of the cycle is, by walkPersist along the cycle from s,
-- either fulfilled before the cycle closes or still pending at b -- and b's own
-- round is a prefix of the cycle, so it is fulfilled there.

module LTL.Lasso where

open import LTL.Round public

------------------------------------------------------------------------
-- A boundary already passed, with both halves of the eventual lasso

data Seen (P : Formula) (v0 cur b : Val) : Set where
  mkSeen : b ∈ Uinf P
        -> (ps : List Val) -> Walk P (Uinf P) v0 ps b
        -> (qs : List Val) -> Walk P (Uinf P) b qs cur
        -> null qs ≡ false -> FulfilledAt P b qs b
        -> Seen P v0 cur b

seenExt : (P : Formula) (v0 cur nx b : Val) (rs : List Val)
       -> Walk P (Uinf P) cur rs nx -> Seen P v0 cur b -> Seen P v0 nx b
seenExt P v0 cur nx b rs wr (mkSeen mb ps wp qs wq nn h) =
  mkSeen mb ps wp (qs ++ rs) (walkApp P (Uinf P) wq wr)
         (null_appL qs rs nn)
         (λ A mA pd -> fulfilPrefix qs rs (h A mA pd))

------------------------------------------------------------------------
-- The lasso

data Lasso (P : Formula) (v0 : Val) : Set where
  mkLasso : (b : Val) -> b ∈ Uinf P
         -> (ps : List Val) -> Walk P (Uinf P) v0 ps b
         -> (qs : List Val) -> Walk P (Uinf P) b qs b
         -> null qs ≡ false -> AllFulfilled P b qs (b ∷ qs)
         -> Lasso P v0

-- Closing the loop.  This is where the cycle-fulfilment property is proved.

closeLasso : (P : Formula) (v0 cur : Val) -> Seen P v0 cur cur -> Lasso P v0
closeLasso P v0 cur (mkSeen mb ps wp qs wq nn h) =
  mkLasso cur mb ps wp qs wq nn cyc
  where
    cyc : AllFulfilled P cur qs (cur ∷ qs)
    cyc s ms A mA pd = fromSub (walkFrom P (Uinf P) wq ms)
      where
        fromSub : SubWalk P (Uinf P) s cur cur qs -> Fulfil P A cur qs
        fromSub (subWalk zs wz f) =
          sumElim mapFul (λ pd2 -> h A mA pd2)
                  (walkPersist P (Uinf P) A (□Args_mem (sub P) mA) wz pd)
          where
            mapFul : Fulfil P A s zs -> Fulfil P A cur qs
            mapFul (ful z m q) = ful z (f m) q

------------------------------------------------------------------------
-- The search.
--
-- Invariants: cur is reachable from v0 by the walk ps; bs lists the boundaries
-- already passed, each with its Seen record relative to the current position;
-- and every state of U_inf that is not yet a boundary still satisfies E, the
-- Bar's predicate.  That last one is  Avail E (Uinf P) bs  (LTL.Nodes), and it
-- is the pigeonhole.

-- Giving cur up: a state of U_inf outside cur ∷ bs is outside bs, hence
-- satisfies E, and is distinct from cur, hence survives the intersection with
-- (cur ≢ᵛ_).

availCons : (P : Formula) {E : Pred} (bs : List Val) -> Avail E (Uinf P) bs
         -> (cur : Val) -> Avail (λ y -> E y ∧ᵇ (cur ≢ᵛ y)) (Uinf P) (cur ∷ bs)
availCons P {E} bs av cur z mz e =
  andIntro (E z) (cur ≢ᵛ z)
           (av z mz (orFalseR (z ≡ᵛ cur) (any (z ≡ᵛ_) bs) e))
           (cong ¬ᵇ_ (onEq (cur ≡ᵛ z) refl))
  where
    onEq : (c : Bool) -> cur ≡ᵛ z ≡ c -> cur ≡ᵛ z ≡ false
    onEq false ec = ec
    onEq true  ec =
      emptyElim (true≢false (trans (sym (subst (λ u -> u ≡ᵛ cur ≡ true)
                                               (≡ᵛ-sound cur z ec)
                                               (≡ᵛ-refl cur)))
                                   (orFalseL (z ≡ᵛ cur) (any (z ≡ᵛ_) bs) e)))

module _ (P : Formula) (v0 : Val) where

  lassoSearch : {E : Pred} -> IFin E
             -> (cur : Val) -> cur ∈ Uinf P
             -> (ps : List Val) -> Walk P (Uinf P) v0 ps cur
             -> (bs : List Val) -> ((b : Val) -> b ∈ bs -> Seen P v0 cur b)
             -> Avail E (Uinf P) bs
             -> Lasso P v0
  -- lassoSearch, after the case split on whether cur is already in bs.

  lassoOn : {E : Pred} -> IFin E
         -> (cur : Val) -> cur ∈ Uinf P
         -> (ps : List Val) -> Walk P (Uinf P) v0 ps cur
         -> (bs : List Val) -> ((b : Val) -> b ∈ bs -> Seen P v0 cur b)
         -> Avail E (Uinf P) bs
         -> (c : Bool) -> cur ∈ᵛ bs ≡ c
         -> Lasso P v0

  lassoSearch bar cur mcur ps wps bs seenf av =
    lassoOn bar cur mcur ps wps bs seenf av (cur ∈ᵛ bs) refl

  lassoOn bar cur mcur ps wps bs seenf av true  ec =
    closeLasso P v0 cur (seenf cur (∈ᵛ-sound cur bs ec))
  lassoOn (cBar h) cur mcur ps wps bs seenf av false ec =
    fromRound (roundOf P cur mcur)
    where
      fromRound : Round P cur -> Lasso P v0
      fromRound (mkRound rs nx wr mnx nn hf) =
        lassoSearch (h cur (av cur mcur ec))
                    nx mnx (ps ++ rs) (walkApp P (Uinf P) wps wr)
                    (cur ∷ bs) seenf' (availCons P bs av cur)
        where
          seenf' : (b : Val) -> b ∈ cur ∷ bs -> Seen P v0 nx b
          seenf' b here      = mkSeen mcur ps wps rs wr nn hf
          seenf' b (there m) = seenExt P v0 cur nx b rs wr (seenf b m)

------------------------------------------------------------------------
-- Proposition 5.3

lasso : (P : Formula) (v0 : Val) -> v0 ∈ Uinf P -> Lasso P v0
lasso P v0 m =
  lassoSearch P v0 (listBar (Uinf P)) v0 m [] wnil [] noSeen
              (λ z mz e -> ∈ᵛ-complete z (Uinf P) mz)
  where
    noSeen : (b : Val) -> b ∈ [] {A = Val} -> Seen P v0 v0 b
    noSeen b ()

------------------------------------------------------------------------
-- Projections, so that a lasso can be looked at

lassoStem : (P : Formula) (v0 : Val) -> Lasso P v0 -> List Val
lassoStem P v0 (mkLasso b mb ps wp qs wq nn cyc) = ps

lassoCycle : (P : Formula) (v0 : Val) -> Lasso P v0 -> List Val
lassoCycle P v0 (mkLasso b mb ps wp qs wq nn cyc) = qs

-- The lasso from a NAMED surviving state.  Taking whichever state U_inf happens
-- to list first is no use as an illustration once the state set is generated
-- from atom assignments and closed up from a seed (G30): the order is not the
-- order of allVecs, and the interesting state need not be the first one.

lassoAt : (P : Formula) (v : Val) -> v ∈ᵛ Uinf P ≡ true
       -> List Val × List Val
lassoAt P v e = lassoStem P v (lasso P v m) , lassoCycle P v (lasso P v m)
  where
    m : v ∈ Uinf P
    m = ∈ᵛ-sound v (Uinf P) e

------------------------------------------------------------------------
-- The lasso, computed.
--
-- For ◇ p the four positions of sub (◇ p) are
--
--    ¬ □ ¬ p ,  □ ¬ p ,  ¬ p ,  p
--
-- and Uinf has the three states of Example 1 of lecture15.pdf:
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

◇P_lasso : lassoAt ◇P sPending refl ≡ (sFulfil ∷ sSink ∷ [] , sSink ∷ [])
◇P_lasso = refl


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

□P_lasso : lassoAt □P s□ refl ≡ ([] , s□ ∷ [])
□P_lasso = refl

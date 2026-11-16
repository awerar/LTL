{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Extract -- G21 of FORMALISATION-PLAN.md, Theorem 4.1 of m4.tex.
--
--   extract : v ∈ removed P -> ⊢ ¬ (chi P v)
--
-- The note argues by induction on the round at which v is removed, with the
-- induction hypothesis "every state outside U_k is refutable".  Here that
-- hypothesis is named,
--
--   Refuted P us = every state of Ust P outside us is refutable,
--
-- and the induction is the obvious one along the elimination: Refuted holds of
-- Ust P for nothing, is carried across one round by roundRefuted, hence holds
-- of Uinf P.  It runs on the Bar that elimGo recurses on (goRefuted below).
-- No round numbering appears.
--
-- The two cases of roundRefuted are the note's.  (R1) drops all successors by
-- the hypothesis and closes with (D1) and (Lin).  (R2) builds the loop
-- invariant B = beta_W and refutes the pending eventuality with a single use of
-- (Ind), through indRule; W is the closed set of LTL.Gfp, and step (ii) is
-- exactly its closure property.

module LTL.Extract where

open import LTL.Trace     public
open import LTL.StepLemma public

------------------------------------------------------------------------
-- Every state has the length chi expects

allLen-mem : {n : Nat} {vs : List Val} -> AllLen n vs -> {v : Val}
          -> v ∈ vs -> length v ≡ n
allLen-mem alNil         ()
allLen-mem (alCons e al) here      = e
allLen-mem (alCons e al) (there m) = allLen-mem al m

stAllLen : (P : Formula) -> AllLen (length (sub P)) (St P)
stAllLen P = allLen-filter (isState P) (allVecs-allLen (length (sub P)))

stLen : (P : Formula) {v : Val} -> v ∈ St P
     -> length v ≡ length (sub P)
stLen P m = allLen-mem (stAllLen P) m

------------------------------------------------------------------------
-- beta_U as a disjunction indexed by states.
--
-- (L5) in the form the theorem uses: introduction at one state, elimination
-- over all of them, and the refutation of a beta all of whose disjuncts are
-- refuted -- which is (L0) when the list is empty, since beta [] is ⊥ and
-- ⋁Elim [] is exFalso.

-- AllInto for a mapped list, one derivation of  f w ⇒ C  per w.

allIntoMap : {C : Formula} (f : Val -> Formula) (ws : List Val)
          -> ((w : Val) -> w ∈ ws -> ⊢ (f w) ⇒ C) -> AllInto C (map f ws)
allIntoMap f []       h = intoNil
allIntoMap f (w ∷ ws) h = intoCons (h w here) (allIntoMap f ws (λ z m -> h z (there m)))

module _ (P : Formula) where

  betaElim : {C : Formula} (ws : List Val)
          -> ((w : Val) -> w ∈ ws -> ⊢ (chi P w) ⇒ C)
          -> ⊢ (beta P ws) ⇒ C
  betaElim ws h = ⋁Elim (map (chi P) ws) (allIntoMap (chi P) ws h)

  betaIntro : (ws : List Val) {w : Val}
           -> w ∈ ws -> ⊢ (chi P w) ⇒ (beta P ws)
  betaIntro ws m = ⋁Intro (map (chi P) ws) (memMap (chi P) m)

  ¬Beta : (ws : List Val)
       -> ((w : Val) -> w ∈ ws -> ⊢ ¬ (chi P w))
       -> ⊢ ¬ (beta P ws)
  ¬Beta ws h =
    refute {beta P ws} {⊤}
           (liftP deriv⊤)
           (betaElim ws (λ w m -> mp ¬Elim (h w m)))

  ------------------------------------------------------------------------
  -- The induction hypothesis of the theorem

  -- The induction hypothesis ranges over Ust P, the set the search explores,
  -- not over St P: a state outside Ust P is never removed and never has to be
  -- refuted -- the provable branch disposes of it by (S1) instead.  What makes
  -- the change possible is ustClosed, used in both cases below: the step lemma
  -- offers ALL state-successors of u, and forward-closure puts each of them
  -- back inside Ust P, where the hypothesis applies.

  Refuted : List Val -> Set
  Refuted us =
    (u : Val) -> u ∈ Ust P -> u ∈ᵛ us ≡ false -> ⊢ ¬ (chi P u)

  ------------------------------------------------------------------------
  -- Case (R1).
  --
  -- stepLemma gives the successors of u inside St P, while (R1) speaks of U_k;
  -- but a successor lying in U_k would be a member of succs P us u, which (R1)
  -- says is empty.  So every disjunct of beta_S is refuted by the hypothesis,
  -- (D1) puts the refutation under ○, and (Lin) brings the negation out.

  extractR1 : (us : List Val) (u : Val)
           -> u ∈ Ust P -> Refuted us -> r1 P us u ≡ true
           -> ⊢ ¬ (chi P u)
  extractR1 us u mu ih e1 =
    refute (stepLemma P u (stLen P (ustSt P mu)))
           (liftP (mp linFwd (○Gen (¬Beta (succs P (St P) u) each))))
    where
      outside : (w : Val) -> w ∈ succs P (St P) u -> w ∈ᵛ us ≡ false
      outside w m = refuteTrue (w ∈ᵛ us) λ eb ->
        null-mem (succs P us u) e1
         (succsIn P us u (∈ᵛ-sound w us eb)
                  (snd (succsMem P (St P) u m)))

      each : (w : Val) -> w ∈ succs P (St P) u -> ⊢ ¬ (chi P w)
      each w m = ih w (ustClosed P mu (fst (succsMem P (St P) u m))
                                 (snd (succsMem P (St P) u m)))
                   (outside w m)

  ------------------------------------------------------------------------
  -- Case (R2).
  --
  -- B := beta_W is the loop invariant, W the closed set of LTL.Gfp.  The three
  -- steps of the note, in order: (i) B ⇒ A by (L2) and (L5), since A holds
  -- throughout W; (ii) B ⇒ ○ B by the step lemma, dropping the successors
  -- that left U_k by the induction hypothesis and keeping the rest by closure
  -- of W; (iii) B ⇒ □ A by (Ind) through indRule and (D3) through □Mono.
  -- Then u lies in W, so chi_u ⇒ □ A, while the eventuality is pending at u,
  -- so chi_u ⇒ ¬ □ A.

  extractR2 : (us : List Val) (u : Val)
           -> u ∈ Ust P -> us ⊆ Ust P -> Refuted us
           -> (A : Formula) -> □ A ∈ sub P
           -> valOf P u (□ A) ≡ false -> u ∈ gfpW P us A
           -> ⊢ ¬ (chi P u)
  extractR2 us u mu sb ih A mbox pend mgfp = refute chi□ chi¬□
    where
      W : List Val
      W = gfpW P us A

      lenW : (w : Val) -> w ∈ W -> length w ≡ length (sub P)
      lenW w m = stLen P (ustSt P (sb w (gfpIn P us A m)))

      -- (i)
      bA : ⊢ (beta P W) ⇒ A
      bA = betaElim W eachA
        where
          eachA : (w : Val) -> w ∈ W -> ⊢ (chi P w) ⇒ A
          eachA w m = subst (λ b -> ⊢ (chi P w) ⇒ (lit A b))
                            (gfpHolds P us A m)
                            (chiProjVal P w (lenW w m) (sub-□ P mbox))

      -- (ii)
      toW : (w : Val) -> w ∈ W
         -> ⊢ (beta P (succs P (St P) w)) ⇒ (beta P W)
      toW w m = betaElim (succs P (St P) w) eachS
        where
          eachS : (w' : Val) -> w' ∈ succs P (St P) w
               -> ⊢ (chi P w') ⇒ (beta P W)
          eachS w' m' = byMem
            where
              pr : w' ∈ St P × step P w w' ≡ true
              pr = succsMem P (St P) w m'

              byMem : ⊢ (chi P w') ⇒ (beta P W)
              byMem with w' ∈ᵛ us in eb
              ... | false =
                mp ¬Elim (ih w' (ustClosed P (sb w (gfpIn P us A m))
                                             (fst pr) (snd pr)) eb)
              ... | true  = betaIntro W (gfpClosed P us A w w' m
                                                   (∈ᵛ-sound w' us eb)
                                                     (snd pr))

      bNext : ⊢ (beta P W) ⇒ ○ (beta P W)
      bNext = betaElim W eachN
        where
          eachN : (w : Val) -> w ∈ W -> ⊢ (chi P w) ⇒ ○ (beta P W)
          eachN w m = ⇒Trans (stepLemma P w (lenW w m)) (○Mono (toW w m))

      -- (iii)
      chi□ : ⊢ (chi P u) ⇒ □ A
      chi□ = ⇒Trans (betaIntro W mgfp)
                        (⇒Trans (indRule bNext) (□Mono bA))

      chi¬□ : ⊢ (chi P u) ⇒ ¬ □ A
      chi¬□ = subst (λ b -> ⊢ (chi P u) ⇒ (lit (□ A) b)) pend
                          (chiProjVal P u (stLen P (ustSt P mu)) mbox)

  ------------------------------------------------------------------------
  -- One round of the elimination preserves the hypothesis

  roundRefuted : (us : List Val)
              -> us ⊆ Ust P -> Refuted us -> Refuted (elimRound P us)
  roundRefuted us sb ih u mu e with u ∈ᵛ us in eb
  ... | false = ih u mu eb
  ... | true  = byReason (dropped P us u kf)
    where
      gs : List Ev
      gs = evList P us

      mus : u ∈ us
      mus = ∈ᵛ-sound u us eb

      -- u was in us but is not in the next round, so keep is false at u
      kf : keep P us gs u ≡ false
      kf = refuteTrue (keep P us gs u) λ ek ->
        ∈ᵛ-false u (elimRound P us) e
                 (filter-true (keep P us gs) us mus ek)

      byReason : Reason P us u -> ⊢ ¬ (chi P u)
      byReason (byR1 e1)               = extractR1 us u mu ih e1
      byReason (byR2 A mbox pend mgfp) =
        extractR2 us u mu sb ih A mbox pend mgfp

  ------------------------------------------------------------------------
  -- Theorem 4.1

  elimRoundSub : (us : List Val)
              -> us ⊆ Ust P -> elimRound P us ⊆ Ust P
  elimRoundSub us sb x m = sb x (filter-sub (keep P us (evList P us)) us m)

  ustRefuted : Refuted (Ust P)
  ustRefuted u mu e = emptyElim (∈ᵛ-false u (Ust P) e mu)

  -- The induction runs along the Bar that elimGo runs on: the hypothesis is
  -- carried across one round by roundRefuted in the branch where a round
  -- removes something, and returned unchanged in the branch where none does.

  goRefuted   : {E : Pred} (us : List Val)
             -> (sb : AllSat E us) (bar : IFin E)
             -> us ⊆ Ust P -> Refuted us -> Refuted (elimGo P us sb bar)
  findRefuted : {E : Pred} (us : List Val)
             -> (sb : AllSat E us) (bar : IFin E)
             -> (fr : FindResult (keep P us (evList P us)) us)
             -> us ⊆ Ust P -> Refuted us -> Refuted (elimFind P us sb bar fr)

  goRefuted us sb bar =
    findRefuted us sb bar (findFalse (keep P us (evList P us)) us)

  findRefuted us sb bar      (allTrue f)    ss r = r
  findRefuted us sb (cBar h) (found x mx q) ss r =
    goRefuted (elimRound P us)
              (dropAllSat (keep P us (evList P us)) us sb x q) (h x (sb x mx))
              (elimRoundSub us ss) (roundRefuted us ss r)

  uinfRefuted : Refuted (Uinf P)
  uinfRefuted =
    goRefuted (Ust P) (ustAllSat P) (ustBar P) (λ x m -> m) ustRefuted

  extract : {v : Val} -> v ∈ removed P -> ⊢ ¬ (chi P v)
  extract {v} m =
    uinfRefuted v
                (filter-sub (λ z -> ¬ᵇ (z ∈ᵛ Uinf P)) (Ust P) m)
                (¬ᵇ-true (v ∈ᵛ Uinf P)
                         (filter-prop (λ z -> ¬ᵇ (z ∈ᵛ Uinf P)) (Ust P) m))

------------------------------------------------------------------------
-- The provable branch of Theorem 6.1.
--
-- Every state of St (¬ Q) is now in one of three positions, and the first is
-- what G30 added.  It never enters the search at all: a state outside Ust R
-- cannot contain R, by the contrapositive of ustSeed, so chi_w carries
-- ¬ R = ¬ ¬ Q outright.  Of the states inside Ust R, the removed ones
-- are refuted by extraction and the survivors do not contain R either, because
-- satB says so.  All three end at the same place, and state completeness --
-- which quantifies over ALL of St R, and is why St R stays what it is -- gives
-- Q.  This is one of the two branches of G28; the other needs the lasso.

-- The three cases are a top-level function rather than a where-block of
-- provable, so that the short certificate of LTL.ShortPC can reuse them: what
-- provablePC (LTL.ShortPC) changes is the OTHER half of the modus ponens, the
-- state completeness, and nothing here.

provableEach : (Q : Formula) -> satB (¬ Q) ≡ false
            -> (w : Val) -> w ∈ St (¬ Q)
            -> ⊢ (chi (¬ Q) w) ⇒ Q
provableEach Q e w m = byPosition
  where
    R : Formula
    R = ¬ Q

    -- w does not contain R, however that was found out
    fromR : valOf R w R ≡ false -> ⊢ (chi R w) ⇒ Q
    fromR ev =
      ⇒Trans (subst (λ c -> ⊢ (chi R w) ⇒ (lit R c)) ev
                        (chiProjVal R w (stLen R m) (sub-self R)))
               dne

    byPosition : ⊢ (chi R w) ⇒ Q
    byPosition with w ∈ᵛ Ust R in ec
    -- w never joined the search, so by ustSeed it does not contain R
    ... | false =
      fromR (refuteTrue (valOf R w R) λ ed ->
               ∈ᵛ-false w (Ust R) ec (ustSeed R m ed))
    ... | true with w ∈ᵛ Uinf R in eb
    -- w survived, so satB says it does not contain R either
    ...   | true =
      fromR (any-false (λ z -> valOf R z R) (Uinf R) e
                       (∈ᵛ-sound w (Uinf R) eb))
    -- w was removed, so chi_w is refutable
    ...   | false =
      mp ¬Elim
         (extract R (filter-true (λ z -> ¬ᵇ (z ∈ᵛ Uinf R)) (Ust R)
                                 (∈ᵛ-sound w (Ust R) ec) (cong ¬ᵇ_ eb)))

provable : (Q : Formula) -> satB (¬ Q) ≡ false -> ⊢ Q
provable Q e =
  mp (betaElim (¬ Q) (St (¬ Q)) (provableEach Q e)) (stateComplete (¬ Q))

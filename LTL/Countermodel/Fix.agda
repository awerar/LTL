{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Fix -- Lemma 5.1 of m4.tex.
--
--   Every v in U_inf has a ->-successor in U_inf, and for every v in U_inf and
--   every j pending at v, some state of Reach_{U_inf}(v) fulfils the j-th
--   eventuality.
--
-- The note's proof is one line: "otherwise (R1) or (R2) would apply and the
-- procedure would not have stopped."  Formally that is two things.
--
-- First, that the procedure really has stopped -- uinfStable.  This is not an
-- argument at all: elimGo returns us exactly in the branch where findFalse
-- reports that every state of us passes keep, so the witness that the
-- procedure has stopped is the branch's own hypothesis, applied.
--
-- Second, and this is the work, that the failure of (R2) yields a WITNESS.
-- (R2) fails at v when v is outside gfpW, and gfpComplete only gives the
-- contrapositive, which is not enough: we need an actual fulfilling state, and
-- an actual walk to it.  gfpEscape produces both, by induction along the
-- shrinking iteration -- v left W_i either because it was never in W_0, so A
-- already fails at v, or because some successor had left W_{i-1}, so prepend
-- that step to the successor's escape.  That induction is now on the same Bar
-- the iteration itself runs on.

module LTL.Countermodel.Fix where

open import LTL.Countermodel.Walk public

------------------------------------------------------------------------
-- The elimination has stopped

module _ (P : Formula) where

  elimGoStable   : {E : Pred} (us : List Val)
                -> (sb : AllSat E us) (bar : IFin E) {v : Val}
                -> v ∈ elimGo P us sb bar
                -> keep P (elimGo P us sb bar)
                          (evList P (elimGo P us sb bar)) v ≡ true
  elimFindStable : {E : Pred} (us : List Val)
                -> (sb : AllSat E us) (bar : IFin E)
                -> (fr : FindResult (keep P us (evList P us)) us) {v : Val}
                -> v ∈ elimFind P us sb bar fr
                -> keep P (elimFind P us sb bar fr)
                          (evList P (elimFind P us sb bar fr)) v ≡ true

  elimGoStable us sb bar =
    elimFindStable us sb bar (findFalse (keep P us (evList P us)) us)

  elimFindStable us sb bar      (allTrue f)       m = f m
  elimFindStable us sb (cBar h) (found x mx q)      =
    elimGoStable (elimRound P us)
                 (dropAllSat (keep P us (evList P us)) us sb x q)
                 (h x (sb x mx))

  uinfStable : {v : Val} -> v ∈ Uinf P
            -> keep P (Uinf P) (evList P (Uinf P)) v ≡ true
  uinfStable = elimGoStable (Ust P) (ustAllSat P) (ustBar P)

  ------------------------------------------------------------------------
  -- so neither clause of Definition 3.1 applies to a survivor

  uinfNotR1 : {v : Val} -> v ∈ Uinf P -> r1 P (Uinf P) v ≡ false
  uinfNotR1 {v} m =
    ∨ᵇ-falseˡ (r1 P (Uinf P) v) (r2 P (evList P (Uinf P)) v)
              (¬ᵇ-true (r1 P (Uinf P) v ∨ᵇ r2 P (evList P (Uinf P)) v)
                       (uinfStable m))

  uinfNotR2 : {v : Val} -> v ∈ Uinf P
           -> r2 P (evList P (Uinf P)) v ≡ false
  uinfNotR2 {v} m =
    ∨ᵇ-falseʳ (r1 P (Uinf P) v) (r2 P (evList P (Uinf P)) v)
              (¬ᵇ-true (r1 P (Uinf P) v ∨ᵇ r2 P (evList P (Uinf P)) v)
                       (uinfStable m))

------------------------------------------------------------------------
-- First half of Lemma 5.1: a successor exists

data SuccInUinf (P : Formula) (v : Val) : Set where
  succInUinf : (w : Val) -> w ∈ Uinf P -> step P v w ≡ true -> SuccInUinf P v

uinfSucc : (P : Formula) (v : Val) -> v ∈ Uinf P -> SuccInUinf P v
uinfSucc P v m = fromSig (null-false (succs P (Uinf P) v) (uinfNotR1 P m))
  where
    fromSig : (Σ[ w ∈ Val ] w ∈ succs P (Uinf P) v) -> SuccInUinf P v
    fromSig (w , mw) = succInUinf w (fst (succsMem P (Uinf P) v mw))
                                    (snd (succsMem P (Uinf P) v mw))

------------------------------------------------------------------------
-- Escaping gfpW, constructively.
--
-- v ∈ us and v outside W give a walk inside us from v to a state at which A
-- fails.  Induction along the shrinking iteration of LTL.Elimination.Gfp.

record Escape (P : Formula) (us : List Val) (A : Formula) (v : Val) : Set where
  constructor esc
  field
    visited  : List Val
    target   : Val
    walk     : Walk P us v visited target
    targetIn : target ∈ us
    fails    : valOf P target A ≡ false

module _ (P : Formula) where

  Escapes : List Val -> Formula -> List Val -> Set
  Escapes us A W =
    (z : Val) -> z ∈ us -> z ∈ᵛ W ≡ false -> Escape P us A z

  escBase : (us : List Val) (A : Formula) -> Escapes us A (wZero P us A)
  escBase us A z mz e with valOf P z A in eh
  ... | false = esc [] z wnil mz eh
  ... | true  =
    emptyElim (∈ᵛ-false z (wZero P us A) e (filter-true (holdsAt P A) us mz eh))

  escStep : (us : List Val) (A : Formula) (W : List Val)
         -> Escapes us A W -> Escapes us A (shrink P us W)
  escStep us A W h z mz e with z ∈ᵛ W in eb
  ... | false = h z mz eb
  ... | true  =
    fromSig (all-false (λ w -> step P z w ⇒ᵇ (w ∈ᵛ W)) us notIn)
    where
      -- z survived into W but not into shrink P us W, so it has a successor
      -- in us that had already left W.
      notIn : succsInside P us W z ≡ false
      notIn = refuteTrue (succsInside P us W z) λ ec ->
        ∈ᵛ-false z (shrink P us W) e
         (filter-true (succsInside P us W) W (∈ᵛ-sound z W eb) ec)

      fromSig : (Σ[ w ∈ Val ] w ∈ us × step P z w ⇒ᵇ (w ∈ᵛ W) ≡ false)
             -> Escape P us A z
      fromSig (w , mw , q) =
        escCons (h w mw (snd (⇒ᵇ-false (step P z w) (w ∈ᵛ W) q)))
        where
          escCons : Escape P us A w -> Escape P us A z
          escCons (esc ws x wk mx ex) =
            esc (w ∷ ws) x
                (wcons mw (fst (⇒ᵇ-false (step P z w) (w ∈ᵛ W) q)) wk)
                    mx ex

  escGo   : (us : List Val) (A : Formula) {E : Pred}
         -> (W : List Val) (sb : AllSat E W) (bar : IFin E)
         -> Escapes us A W -> Escapes us A (shrinkGo P us W sb bar)
  escFind : (us : List Val) (A : Formula) {E : Pred}
         -> (W : List Val) (sb : AllSat E W) (bar : IFin E)
         -> (fr : FindResult (succsInside P us W) W)
         -> Escapes us A W -> Escapes us A (shrinkFind P us W sb bar fr)

  escGo us A W sb bar = escFind us A W sb bar (findFalse (succsInside P us W) W)

  escFind us A W sb bar      (allTrue f)   e = e
  escFind us A W sb (cBar h) (found x m q) e =
    escGo us A (shrink P us W) (dropAllSat (succsInside P us W) W sb x q)
          (h x (sb x m)) (escStep us A W e)

  gfpEscape : (us : List Val) (A : Formula) -> Escapes us A (gfpW P us A)
  gfpEscape us A =
    escGo us A (wZero P us A) (memAllSat (wZero P us A))
          (listBar (wZero P us A)) (escBase us A)

  ------------------------------------------------------------------------
  -- Second half of Lemma 5.1: a pending eventuality is fulfilled somewhere
  -- reachable

  uinfFulfil : (v : Val) -> v ∈ Uinf P
            -> (A : Formula) -> A ∈ □Args (sub P)
            -> valOf P v (□ A) ≡ false
            -> Escape P (Uinf P) A v
  uinfFulfil v m A mA pend =
    gfpEscape (Uinf P) A v m
      (∧ᵇ-false-cancelˡ (pending P v A) (v ∈ᵛ gfpW P (Uinf P) A)
         (any-false (badEv P v) (evList P (Uinf P)) (uinfNotR2 P m)
                    (evList-mem P (Uinf P) mA))
         (cong ¬ᵇ_ pend))

  ------------------------------------------------------------------------
  -- Survivors are states.
  --
  -- Each round only filters, so U_inf is contained in St P.  Hintikka's lemma
  -- needs this to read (S1) and (S2) off a state of the run.

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

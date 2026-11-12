{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Fix -- Lemma 5.1 of m4.tex.
--
--   Every v in U_inf has a ->-successor in U_inf, and for every v in U_inf and
--   every j pending at v, some state of Reach_{U_inf}(v) fulfils the j-th
--   eventuality.
--
-- The note's proof is one line: "otherwise (R1) or (R2) would apply and the
-- procedure would not have stopped."  Formally that is two things.
--
-- First, that the procedure really has stopped -- uinfStable.  Since G29 this
-- is not an argument at all: elimGo returns us exactly in the branch where
-- findFalse reports that every state of us passes keep, so the witness that
-- the procedure has stopped is the branch's own hypothesis, applied.  The
-- fixed-point equation and the ≤ measure it used to need are both gone.
--
-- Second, and this is the work, that the failure of (R2) yields a WITNESS.
-- (R2) fails at v when v is outside gfpW, and gfpComplete only gives the
-- contrapositive, which is not enough: we need an actual fulfilling state, and
-- an actual walk to it.  gfpEscape produces both, by induction along the
-- shrinking iteration -- v left W_i either because it was never in W_0, so A
-- already fails at v, or because some successor had left W_{i-1}, so prepend
-- that step to the successor's escape.  That induction is now on the same Bar
-- the iteration itself runs on.

module LTL.Fix where

open import LTL.Walk public

------------------------------------------------------------------------
-- The elimination has stopped

elimGoStable   : (P : Formula) {E : Val -> Bool} (us : List Val)
              -> (sb : AllSat E us) (bar : IFin E) {v : Val}
              -> v ∈ elimGo P us sb bar
              -> keep P (elimGo P us sb bar)
                        (evList P (elimGo P us sb bar)) v ≡ true
elimFindStable : (P : Formula) {E : Val -> Bool} (us : List Val)
              -> (sb : AllSat E us) (bar : IFin E)
              -> (fr : FindResult (keep P us (evList P us)) us) {v : Val}
              -> v ∈ elimFind P us sb bar fr
              -> keep P (elimFind P us sb bar fr)
                        (evList P (elimFind P us sb bar fr)) v ≡ true

elimGoStable P us sb bar =
  elimFindStable P us sb bar (findFalse (keep P us (evList P us)) us)

elimFindStable P us sb bar      (allTrue f)       m = f m
elimFindStable P us sb (cBar h) (found x mx q)      =
  elimGoStable P (elimRound P us)
               (dropAllSat (keep P us (evList P us)) us sb x q) (h x (sb x mx))

uinfStable : (P : Formula) {v : Val} -> v ∈ Uinf P
          -> keep P (Uinf P) (evList P (Uinf P)) v ≡ true
uinfStable P = elimGoStable P (Ust P) (ustAllSat P) (ustBar P)

------------------------------------------------------------------------
-- so neither clause of Definition 3.1 applies to a survivor

uinfNotR1 : (P : Formula) {v : Val} -> v ∈ Uinf P -> r1 P (Uinf P) v ≡ false
uinfNotR1 P {v} m =
  orFalseL (r1 P (Uinf P) v) (r2 P (evList P (Uinf P)) v)
           (notTrue (r1 P (Uinf P) v ∨ᵇ r2 P (evList P (Uinf P)) v)
                    (uinfStable P m))

uinfNotR2 : (P : Formula) {v : Val} -> v ∈ Uinf P
         -> r2 P (evList P (Uinf P)) v ≡ false
uinfNotR2 P {v} m =
  orFalseR (r1 P (Uinf P) v) (r2 P (evList P (Uinf P)) v)
           (notTrue (r1 P (Uinf P) v ∨ᵇ r2 P (evList P (Uinf P)) v)
                    (uinfStable P m))

------------------------------------------------------------------------
-- First half of Lemma 5.1: a successor exists

data SuccInUinf (P : Formula) (v : Val) : Set where
  succInUinf : (w : Val) -> w ∈ Uinf P -> step P v w ≡ true -> SuccInUinf P v

uinfSucc : (P : Formula) (v : Val) -> v ∈ Uinf P -> SuccInUinf P v
uinfSucc P v m = fromSig (null_false (succs P (Uinf P) v) (uinfNotR1 P m))
  where
    fromSig : (Σ[ w ∈ Val ] w ∈ succs P (Uinf P) v) -> SuccInUinf P v
    fromSig (w , mw) = succInUinf w (fst (succsMem P (Uinf P) v mw))
                                    (snd (succsMem P (Uinf P) v mw))

------------------------------------------------------------------------
-- Escaping gfpW, constructively.
--
-- v ∈ us and v outside W give a walk inside us from v to a state at which A
-- fails.  Induction along the shrinking iteration of LTL.Gfp.

data Escape (P : Formula) (us : List Val) (A : Formula) (v : Val) : Set where
  esc : (ws : List Val) (w : Val) -> Walk P us v ws w -> w ∈ us
     -> valOf P w A ≡ false -> Escape P us A v

Escapes : Formula -> List Val -> Formula -> List Val -> Set
Escapes P us A W =
  (z : Val) -> z ∈ us -> z ∈ᵛ W ≡ false -> Escape P us A z

escBase : (P : Formula) (us : List Val) (A : Formula) -> Escapes P us A (wZero P us A)
escBase P us A z mz e = onHolds (valOf P z A) refl
  where
    onHolds : (b : Bool) -> valOf P z A ≡ b -> Escape P us A z
    onHolds false eh = esc [] z wnil mz eh
    onHolds true  eh =
      emptyElim (∈ᵛ-false z (wZero P us A) e
                          (filter_true (holdsAt P A) us mz eh))

escStep : (P : Formula) (us : List Val) (A : Formula) (W : List Val)
       -> Escapes P us A W -> Escapes P us A (shrink P us W)
escStep P us A W h z mz e = onIn (z ∈ᵛ W) refl
  where
    onIn : (b : Bool) -> z ∈ᵛ W ≡ b -> Escape P us A z
    onIn false eb = h z mz eb
    onIn true  eb = fromSig (all_false (λ w -> step P z w ⇒ᵇ (w ∈ᵛ W))
                                        us (notIn (succsInside P us W z) refl))
      where
        -- z survived into W but not into shrink P us W, so it has a successor
        -- in us that had already left W.
        notIn : (c : Bool) -> succsInside P us W z ≡ c -> succsInside P us W z ≡ false
        notIn false ec = ec
        notIn true  ec =
          emptyElim (∈ᵛ-false z (shrink P us W) e
                      (filter_true (succsInside P us W) W (∈ᵛ-sound z W eb) ec))

        fromSig : (Σ[ w ∈ Val ] w ∈ us ×
                                  step P z w ⇒ᵇ (w ∈ᵛ W) ≡ false)
               -> Escape P us A z
        fromSig (w , mw , q) =
          escCons (h w mw (snd (⇒ᵇ-false (step P z w) (w ∈ᵛ W) q)))
          where
            escCons : Escape P us A w -> Escape P us A z
            escCons (esc ws x wk mx ex) =
              esc (w ∷ ws) x
                  (wcons mw (fst (⇒ᵇ-false (step P z w) (w ∈ᵛ W) q)) wk)
                  mx ex

escGo   : (P : Formula) (us : List Val) (A : Formula) {E : Val -> Bool}
       -> (W : List Val) (sb : AllSat E W) (bar : IFin E)
       -> Escapes P us A W -> Escapes P us A (shrinkGo P us W sb bar)
escFind : (P : Formula) (us : List Val) (A : Formula) {E : Val -> Bool}
       -> (W : List Val) (sb : AllSat E W) (bar : IFin E)
       -> (fr : FindResult (succsInside P us W) W)
       -> Escapes P us A W -> Escapes P us A (shrinkFind P us W sb bar fr)

escGo P us A W sb bar = escFind P us A W sb bar (findFalse (succsInside P us W) W)

escFind P us A W sb bar      (allTrue f)   e = e
escFind P us A W sb (cBar h) (found x m q) e =
  escGo P us A (shrink P us W) (dropAllSat (succsInside P us W) W sb x q) (h x (sb x m))
        (escStep P us A W e)

gfpEscape : (P : Formula) (us : List Val) (A : Formula) -> Escapes P us A (gfpW P us A)
gfpEscape P us A =
  escGo P us A (wZero P us A) (memAllSat (wZero P us A)) (listBar (wZero P us A))
        (escBase P us A)

------------------------------------------------------------------------
-- Second half of Lemma 5.1: a pending eventuality is fulfilled somewhere
-- reachable

uinfFulfil : (P : Formula) (v : Val) -> v ∈ Uinf P
          -> (A : Formula) -> A ∈ □Args (sub P)
          -> valOf P v (□ A) ≡ false
          -> Escape P (Uinf P) A v
uinfFulfil P v m A mA pend =
  gfpEscape P (Uinf P) A v m
    (andFalseTrueL (pending P v A) (v ∈ᵛ gfpW P (Uinf P) A)
                   (any_false (badEv P v) (evList P (Uinf P)) (uinfNotR2 P m)
                              (evList_mem P (Uinf P) mA))
                   (cong ¬ᵇ_ pend))

------------------------------------------------------------------------
-- Survivors are states.
--
-- Each round only filters, so U_inf is contained in St P.  Hintikka's lemma
-- needs this to read (S1) and (S2) off a state of the run.

elimGoSub   : (P : Formula) {E : Val -> Bool} (us : List Val)
           -> (sb : AllSat E us) (bar : IFin E) {x : Val}
           -> x ∈ elimGo P us sb bar -> x ∈ us
elimFindSub : (P : Formula) {E : Val -> Bool} (us : List Val)
           -> (sb : AllSat E us) (bar : IFin E)
           -> (fr : FindResult (keep P us (evList P us)) us) {x : Val}
           -> x ∈ elimFind P us sb bar fr -> x ∈ us

elimGoSub P us sb bar =
  elimFindSub P us sb bar (findFalse (keep P us (evList P us)) us)

elimFindSub P us sb bar      (allTrue f)    m = m
elimFindSub P us sb (cBar h) (found x mx q) m =
  filter_sub (keep P us (evList P us)) us
             (elimGoSub P (elimRound P us)
                        (dropAllSat (keep P us (evList P us)) us sb x q)
                        (h x (sb x mx)) m)

uinfUst : (P : Formula) (x : Val) -> x ∈ Uinf P -> x ∈ Ust P
uinfUst P x m = elimGoSub P (Ust P) (ustAllSat P) (ustBar P) m

uinfSub : (P : Formula) (x : Val) -> x ∈ Uinf P -> x ∈ St P
uinfSub P x m = ustSt P (uinfUst P x m)

-- The projection is named rather than applied inline: giving filter_prop its
-- list argument against the folded  St P  is what keeps the elaborator from
-- unfolding Uinf while it solves the implicit.

stIsState : (P : Formula) {x : Val} -> x ∈ St P -> isState P x ≡ true
stIsState P m = filter_prop (isState P) (allVecs (length (sub P))) m

uinfState : (P : Formula) (x : Val) -> x ∈ Uinf P -> isState P x ≡ true
uinfState P x m = stIsState P (uinfSub P x m)

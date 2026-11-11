{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Trace -- G20 of FORMALISATION-PLAN.md: why each state was removed.
--
-- The elimination procedure of LTL.Elim drops a state by a single boolean,
-- keep P us v.  Theorem 4.1 proceeds by cases on the REASON, so the trace this
-- goal asks for is the inversion of that boolean into the two clauses of
-- Definition 3.1, carrying the witnesses each clause provides:
--
--   (R1)  v has no ->-successor in U_k;
--   (R2)  □ A is a subformula of P, is pending at v, and v belongs to the
--         set W of LTL.Gfp -- equivalently, by gfpSound, the eventuality is
--         fulfilled at no state reachable from v inside U_k.
--
-- Recording the reason as a proof-carrying value rather than as a printed list
-- is what makes it usable in G21: byR2 hands over exactly the A, the
-- membership □ A in Sub(P), and the two facts that case (R2) of the theorem
-- consumes.  A printed form is given at the end for observation.

module LTL.Trace where

open import LTL.Elim public

------------------------------------------------------------------------
-- The eventualities really are box-subformulas

□Args_mem : (As : List Formula) {A : Formula}
           -> A ∈ □Args As -> □ A ∈ As
□Args_mem []             ()
□Args_mem (var n   ∷ As) m         = there (□Args_mem As m)
□Args_mem (¬ B   ∷ As) m         = there (□Args_mem As m)
□Args_mem (B ⇒ C ∷ As) m         = there (□Args_mem As m)
□Args_mem (○ B   ∷ As) m         = there (□Args_mem As m)
□Args_mem (□ B   ∷ As) here      = here
□Args_mem (□ B   ∷ As) (there m) = there (□Args_mem As m)

------------------------------------------------------------------------
-- The reason a state is dropped

data Reason (P : Formula) (us : List Val) (v : Val) : Set where
  byR1 : r1 P us v ≡ true -> Reason P us v
  byR2 : (A : Formula) -> □ A ∈ sub P
      -> valOf P v (□ A) ≡ false
      -> v ∈ gfpW P us A
      -> Reason P us v

-- Inverting r2 now goes through evList_of: the disjunct that fired names a
-- PAIR, and evList_of says the pair is an eventuality of P together with its
-- own gfp set.  That is the only trace of the hoisting of LTL.Elim in the
-- proofs.

dropped : (P : Formula) (us : List Val) (v : Val)
       -> keep P us (evList P us) v ≡ false -> Reason P us v
dropped P us v e =
  sumElim byR1 fromR2
          (orTrue (r1 P us v) (r2 P (evList P us) v)
                  (notFalse (r1 P us v ∨ᵇ r2 P (evList P us) v) e))
  where
    fromPair : (g : Ev) -> g ∈ evList P us -> badEv P v g ≡ true
            -> Reason P us v
    fromPair (A , W) mg q =
      byR2 A (□Args_mem (sub P) (fst (evList_of P us mg)))
           (notTrue (valOf P v (□ A)) (andTrueL (pending P v A) (memB v W) q))
           (subst (λ Z -> v ∈ Z) (snd (evList_of P us mg))
                  (memB_sound v W (andTrueR (pending P v A) (memB v W) q)))

    fromSig : (Σ[ g ∈ Ev ] g ∈ evList P us × badEv P v g ≡ true)
           -> Reason P us v
    fromSig (g , m , q) = fromPair g m q

    fromR2 : r2 P (evList P us) v ≡ true -> Reason P us v
    fromR2 e2 = fromSig (anyL_true (badEv P v) (evList P us) e2)

------------------------------------------------------------------------
-- The printed form.
--
-- One entry per state removed in the round, paired with the boolean r1: true
-- means the state went by (R1), false that (R1) did not fire and so (R2) did.

elimTrace : Formula -> List Val -> List (Val × Bool)
elimTrace P us =
  map (λ v -> v , r1 P us v)
      (filterL (λ v -> ¬ᵇ keep P us (evList P us) v) us)

reasons : Formula -> List Val -> List Bool
reasons P us = map snd (elimTrace P us)

------------------------------------------------------------------------
-- Observation.
--
-- The observations are made on Ust, the demand-driven state set of G30, which
-- is what the procedure actually explores; St still has the six states of the
-- comment in LTL.Elim, but four of them are never reached from a state
-- containing ¬ benAri and the procedure never looks at them.
--
-- Only ONE state of ¬ benAri contains it, namely E, and E has no successor,
-- so the closure stops there and the single round removes it by (R1).  Ben-Ari's
-- own example therefore never exercises (R2) in this formulation.

trace_¬BenAri : reasons ¬BenAri (Ust ¬BenAri) ≡ true ∷ []
trace_¬BenAri = refl

-- and the second round removes nothing, so the procedure has converged.

trace_¬BenAri2 : reasons ¬BenAri (elimRound ¬BenAri (Ust ¬BenAri)) ≡ []
trace_¬BenAri2 = refl

-- ◇ p loses no state at all.

trace_◇P : reasons ◇P (Ust ◇P) ≡ []
trace_◇P = refl

------------------------------------------------------------------------
-- A small example that does exercise (R2).
--
--   bnb  =  □ p ⇒ □ ○ p
--
-- is provable, and unlike benAri its refutation genuinely needs the loop
-- invariant.  The state with □ p true and □ ○ p false has successors,
-- so (R1) does not apply; but (T2) carries □ p along every path, (S2) then
-- gives p and (T1) gives ○ p at every state reached, so the eventuality that
-- □ ○ p leaves pending is fulfilled nowhere.  That is case (R2), and it
-- fires in the first round -- the false entry below.
--
-- The closure of the states containing ¬ bnb has just two members: □ p and
-- ¬ □ ○ p force p, and (T2) and (T3) carry both along every step, so
-- the only freedom left is the bit at ○ p.  The state with ○ p false has no
-- successor and goes by (R1) in the first round; the other one loops to itself,
-- and once its (R1)-victim is gone the eventuality that □ ○ p leaves
-- pending is fulfilled at no reachable state, so it goes by (R2) in the second.
-- Nothing survives, and in particular no survivor contains ¬ bnb.
--
-- The (R2) round is the one that matters: extractR2 -- the loop invariant,
-- (Ind) and all -- is on the path from satB_¬Bnb to bnbProof in LTL.Extract.

bnb : Formula
bnb = □ (var zero) ⇒ □ ○ (var zero)

¬Bnb : Formula
¬Bnb = ¬ bnb

Ust_¬Bnb : length (Ust ¬Bnb) ≡ 2
Ust_¬Bnb = refl

trace_¬Bnb : reasons ¬Bnb (Ust ¬Bnb) ≡ true ∷ []
trace_¬Bnb = refl

trace_¬Bnb2 : reasons ¬Bnb (elimRound ¬Bnb (Ust ¬Bnb)) ≡ false ∷ []
trace_¬Bnb2 = refl

Uinf_¬Bnb : length (Uinf ¬Bnb) ≡ 0
Uinf_¬Bnb = refl

satB_¬Bnb : satB ¬Bnb ≡ false
satB_¬Bnb = refl

-- and the converse, which Hintikka's lemma needs: a box-subformula names an
-- eventuality.  That is □Args_of, and it followed □Args down to LTL.Skel
-- in Phase 9, where the (S2) premise of LTL.CompletePC needs it.

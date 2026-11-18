{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Elimination.Trace -- G20 of FORMALISATION-PLAN.md: why each state was removed.
--
-- The elimination procedure of LTL.Elimination.Elim drops a state by a single boolean,
-- keep P us v.  Theorem 4.1 proceeds by cases on the REASON, so the trace this
-- goal asks for is the inversion of that boolean into the two clauses of
-- Definition 3.1, carrying the witnesses each clause provides:
--
--   (R1)  v has no ->-successor in U_k;
--   (R2)  □ A is a subformula of P, is pending at v, and v belongs to the
--         set W of LTL.Elimination.Gfp -- equivalently, by gfpSound, the eventuality is
--         fulfilled at no state reachable from v inside U_k.
--
-- Recording the reason as a proof-carrying value rather than as a printed list
-- is what makes it usable in G21: byR2 hands over exactly the A, the
-- membership □ A in Sub(P), and the two facts that case (R2) of the theorem
-- consumes.  A printed form is given at the end for observation.

module LTL.Elimination.Trace where

open import LTL.Elimination.Elim public

------------------------------------------------------------------------
-- The eventualities really are box-subformulas

□Args-mem : (As : List Formula) {A : Formula}
         -> A ∈ □Args As -> □ A ∈ As
□Args-mem []           ()
□Args-mem (var n ∷ As) m         = there (□Args-mem As m)
□Args-mem (¬ B   ∷ As) m         = there (□Args-mem As m)
□Args-mem (B ⇒ C ∷ As) m         = there (□Args-mem As m)
□Args-mem (○ B   ∷ As) m         = there (□Args-mem As m)
□Args-mem (□ B   ∷ As) here      = here
□Args-mem (□ B   ∷ As) (there m) = there (□Args-mem As m)

------------------------------------------------------------------------
-- The reason a state is dropped

data Reason (P : Formula) (us : List Val) (v : Val) : Set where
  byR1 : r1 P us v ≡ true -> Reason P us v
  byR2 : (A : Formula) -> □ A ∈ sub P
      -> valOf P v (□ A) ≡ false
      -> v ∈ gfpW P us A
      -> Reason P us v

-- Inverting r2 now goes through evList-of: the disjunct that fired names a
-- PAIR, and evList-of says the pair is an eventuality of P together with its
-- own gfp set.  That is the only trace of the hoisting of LTL.Elimination.Elim in the
-- proofs.

module _ (P : Formula) where

  dropped : (us : List Val) (v : Val)
         -> keep P us (evList P us) v ≡ false -> Reason P us v
  dropped us v e =
    sumElim byR1 fromR2
            (∨ᵇ-true (r1 P us v) (r2 P (evList P us) v)
                     (¬ᵇ-false (r1 P us v ∨ᵇ r2 P (evList P us) v) e))
    where
      fromPair : (g : Ev) -> g ∈ evList P us -> badEv P v g ≡ true
              -> Reason P us v
      fromPair (A , W) mg q =
        byR2 A (□Args-mem (sub P) (fst (evList-of P us mg)))
             (¬ᵇ-true (valOf P v (□ A)) (∧ᵇ-trueˡ (pending P v A) (v ∈ᵛ W) q))
             (subst (λ Z -> v ∈ Z) (snd (evList-of P us mg))
                    (∈ᵛ-sound v W (∧ᵇ-trueʳ (pending P v A) (v ∈ᵛ W) q)))

      fromSig : (Σ[ g ∈ Ev ] g ∈ evList P us × badEv P v g ≡ true)
             -> Reason P us v
      fromSig (g , m , q) = fromPair g m q

      fromR2 : r2 P (evList P us) v ≡ true -> Reason P us v
      fromR2 e2 = fromSig (any-true (badEv P v) (evList P us) e2)

  ------------------------------------------------------------------------
  -- The printed form.
  --
  -- One entry per state removed in the round, paired with the boolean r1: true
  -- means the state went by (R1), false that (R1) did not fire and so (R2) did.

  elimTrace : List Val -> List (Val × Bool)
  elimTrace us =
    map (λ v -> v , r1 P us v)
        (filter (λ v -> ¬ᵇ keep P us (evList P us) v) us)

  reasons : List Val -> List Bool
  reasons us = map snd (elimTrace us)

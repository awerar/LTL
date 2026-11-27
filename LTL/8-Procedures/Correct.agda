{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.8-Procedures.Correct -- decide meets LTL.Statement's specification.
--
-- A DecisionProcedure answers true only for formulas valid on every lasso, and
-- false only with a lasso on which the formula fails.  decide answers with
-- ⊢ Q ⊎ LassoCountermodel Q , and the two branches meet Statement through one
-- bridge: when a Statement lasso L starts at pos0 and loops back to loop, the
-- Boolean evaluation of LTL.4-Semantics.OrbitEval at stage n IS truth at time
-- n of S.interpret L (evalAt-holds, holds-evalAt, by induction on the
-- formula).  The □ case uses the finite forward orbit: every iterate of a
-- position is in its orbit, and every member of the orbit is an iterate.
--
-- ⊢-valid uses the bridge on an arbitrary Statement lasso, toCountermodel on the
-- lasso a countermodel reads off; together they give cmUnderivable.  With
-- decide they also give Statement's two corollaries, deriveComplete and
-- countermodelComplete.  Formula and ⊢ are LTL.Statement's own, so the
-- statement is about the formulas and derivations the procedure works with.

module LTL.8-Procedures.Correct where

open import LTL.8-Procedures.Everything public
import LTL.Statement as S
open S using (_,_⊨_; _↔_; iff)
import LTL.4-Semantics.Orbit
import LTL.4-Semantics.OrbitEval

------------------------------------------------------------------------
-- The bridge.  States have any type S, and read gives the instant of a state;
-- toPosition reads a position the same way.

module _ {S : Set} (read : S -> S.Instant) where

  private
    module O = LTL.4-Semantics.Orbit S
    module E = LTL.4-Semantics.OrbitEval S read

  toPosition : O.Pos -> S.Position
  toPosition (s , ws) = S.at (read s) (map read ws)

  -- L agrees with the lasso of loop from pos0 when it starts at pos0 and loops
  -- back to loop.  Then S.step is nextPos, and so the positions of L are the
  -- iterates of nextPos from pos0.

  module _ (loop : O.Pos) (L : S.Lasso) (pos0 : O.Pos)
           (loopAgree    : S.Lasso.loop L ≡ toPosition loop)
           (initialAgree : S.initial L ≡ toPosition pos0) where

    stepAgree : (q : O.Pos) -> S.step L (toPosition q) ≡ toPosition (O.nextPos loop q)
    stepAgree (s , [])     = loopAgree
    stepAgree (s , w ∷ ws) = refl

    private
      stage : Nat -> O.Pos
      stage n = O.posIter loop pos0 n

      EvalsTrue : Formula -> O.Pos -> Set
      EvalsTrue A q = E.evalAt loop A q ≡ true

      nowAgree : (q : O.Pos) -> S.Position.now (toPosition q) ≡ read (O.posState q)
      nowAgree (s , ws) = refl

    positionAgree : (n : Nat) -> S.position L n ≡ toPosition (stage n)
    positionAgree zero    = initialAgree
    positionAgree (suc n) =
      trans (cong (S.step L) (positionAgree n)) (stepAgree (stage n))

    interpretAgree : (n : Nat) -> S.interpret L n ≡ read (O.posState (stage n))
    interpretAgree n =
      trans (cong S.Position.now (positionAgree n)) (nowAgree (stage n))

    ----------------------------------------------------------------------
    -- The Boolean evaluation is the semantics.  Both directions are proved
    -- together, since ¬ and ⇒ are contravariant in their first argument.

    evalAt-holds : (A : Formula) (n : Nat) -> EvalsTrue A (stage n) -> S.interpret L , n ⊨ A
    holds-evalAt : (A : Formula) (n : Nat) -> S.interpret L , n ⊨ A -> EvalsTrue A (stage n)

    evalAt-holds (var x) n e = subst (λ i -> i x ≡ true) (sym (interpretAgree n)) e

    evalAt-holds (¬ A) n e h =
      true≢false (trans (sym (holds-evalAt A n h))
                        (¬ᵇ-true (E.evalAt loop A (stage n)) e))

    evalAt-holds (A ⇒ B) n e h =
      evalAt-holds B n
        (⇒ᵇ-mp (E.evalAt loop A (stage n)) (E.evalAt loop B (stage n))
               e (holds-evalAt A n h))

    evalAt-holds (○ A) n e = evalAt-holds A (suc n) e

    evalAt-holds (□ A) n e k =
      evalAt-holds A (k + n)
        (subst (EvalsTrue A) (sym (O.posIter-+ loop pos0 k n))
               (E.eval□-true loop A (stage n) e (O.posIter loop (stage n) k)
                             (O.iter∈orbit loop (stage n) k)))

    holds-evalAt (var x) n h = subst (λ i -> i x ≡ true) (interpretAgree n) h

    holds-evalAt (¬ A) n h with E.evalAt loop A (stage n) in ea
    ... | true  = emptyElim (h (evalAt-holds A n ea))
    ... | false = refl

    holds-evalAt (A ⇒ B) n h =
      ⇒ᵇ-intro (E.evalAt loop A (stage n)) (E.evalAt loop B (stage n))
               (λ ea -> holds-evalAt B n (h (evalAt-holds A n ea)))

    holds-evalAt (○ A) n h = holds-evalAt A (suc n) h

    holds-evalAt (□ A) n h =
      E.eval□-intro loop A (stage n)
        (O.orbit-all loop (EvalsTrue A) (stage n)
           (λ t -> subst (EvalsTrue A) (O.posIter-+ loop pos0 t n)
                         (holds-evalAt A (t + n) (h t))))

------------------------------------------------------------------------
-- Soundness: a derivable formula is valid.  A Statement lasso l is a lasso of
-- instants, read by the identity, from S.initial l back to S.Lasso.loop l;
-- OrbitEval's soundness holds there.

⊢-valid : {A : Formula} -> ⊢ A -> S.Valid A
⊢-valid {A} d l =
  evalAt-holds read loop l pos0
    (cong (S.at _) (sym (map-id (S.Position.rest (S.Lasso.loop l)))))
    (cong (S.at _) (sym (map-id (S.Position.rest (S.initial l)))))
    A zero (LTL.4-Semantics.OrbitEval.sound S.Instant read loop d pos0)
  where
    read : S.Instant -> S.Instant
    read i = i

    loop pos0 : S.Instant × List S.Instant
    loop = S.Position.now (S.Lasso.loop l) , S.Position.rest (S.Lasso.loop l)
    pos0 = S.Position.now (S.initial l) , S.Position.rest (S.initial l)

------------------------------------------------------------------------
-- A countermodel is a Statement countermodel.  Its lasso, read through
-- assignment (¬ Q), is a Statement lasso: start followed by rest, then the
-- cycle from loop for ever.  Q is false at stage 0 (falseAtStart), so it is not true at
-- time 0.

toCountermodel : (Q : Formula) -> LassoCountermodel Q -> S.LassoCountermodel Q
toCountermodel Q c = S.counter L qFalse
  where
    open LassoCountermodel c
    open Lasso lasso using (loop; rest)

    read : Val (¬ Q) -> S.Instant
    read = assignment (¬ Q)

    L : S.Lasso
    L = record { start = map read (start ∷ rest)
               ; loop  = toPosition read loop }

    qFalse : S.interpret L , zero ⊨ ¬ Q
    qFalse h =
      true≢false
        (trans (sym (holds-evalAt read loop L (start , rest) refl refl Q zero h))
               falseAtStart)

-- So a countermodel rules out a derivation: the derivation would be valid,
-- in particular on the countermodel's own lasso.

cmUnderivable : (Q : Formula) -> LassoCountermodel Q -> ⊢ Q -> Empty
cmUnderivable Q c d with toCountermodel Q c
... | S.counter L notQ = notQ (⊢-valid d L)

------------------------------------------------------------------------
-- decide as a Statement DecisionProcedure.  The test is which branch it took
-- (isProof), and proofFrom / countermodelFrom read that branch off: a
-- derivation is valid by ⊢-valid, and a countermodel translates by
-- toCountermodel.

decideCorrect : S.DecisionProcedure
decideCorrect = record
  { decideValid    = λ Q -> isProof (decide Q)
  ; validIfTrue    = validIfTrue
  ; counterIfFalse = counterIfFalse
  }
  where
    validIfTrue : (Q : Formula) -> isProof (decide Q) ≡ true -> S.Valid Q
    validIfTrue Q e = ⊢-valid (proofFrom (decide Q) e)

    counterIfFalse : (Q : Formula) -> isProof (decide Q) ≡ false
                  -> S.LassoCountermodel Q
    counterIfFalse Q e = toCountermodel Q (countermodelFrom (decide Q) e)

------------------------------------------------------------------------
-- The corollaries: a formula is derivable exactly when it is valid, and has a
-- countermodel exactly when it is not.  A countermodel refutes validity on its
-- own lasso.  The converse directions consult decide, whose answer is a
-- derivation or a countermodel: validity rules out the second, and
-- invalidity the first.

cmInvalid : (Q : Formula) -> S.LassoCountermodel Q -> S.Valid Q -> Empty
cmInvalid Q (S.counter L notQ) v = notQ (v L)

deriveComplete : (Q : Formula) -> ⊢ Q ↔ S.Valid Q
deriveComplete Q = iff ⊢-valid complete
  where
    complete : S.Valid Q -> ⊢ Q
    complete v with decide Q
    ... | inl d = d
    ... | inr c = emptyElim (cmInvalid Q (toCountermodel Q c) v)

countermodelComplete : (Q : Formula) -> S.LassoCountermodel Q ↔ (S.Valid Q -> Empty)
countermodelComplete Q = iff (cmInvalid Q) fromInvalid
  where
    fromInvalid : (S.Valid Q -> Empty) -> S.LassoCountermodel Q
    fromInvalid nv with decide Q
    ... | inl d = emptyElim (nv (⊢-valid d))
    ... | inr c = toCountermodel Q c

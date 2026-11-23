{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Correct -- decide meets the specification of LTL.Statement.
--
-- A DecisionProcedure answers true only for formulas valid on every lasso, and
-- false only with a lasso on which the formula fails.  decide answers with
-- ⊢ Q ⊎ LassoCountermodel Q , and the two branches meet Statement through one
-- bridge: when a Statement lasso L starts at pos0 and loops back to loop, the
-- Boolean evaluation of LTL.Semantics.OrbitEval at stage n IS truth at time
-- n of T.interpret L (evalAt-holds, holds-evalAt, by induction on the
-- formula).  The □ case uses the finite forward orbit: every iterate of a
-- position is in its orbit, and every member of the orbit is an iterate.
--
-- ⊢-valid uses the bridge on an arbitrary Statement lasso, toCountermodel on the
-- lasso a countermodel reads off; together they give cmUnderivable.  Formula
-- is LTL.Statement's own datatype, so the statement is about the formulas the
-- procedure runs on.

module LTL.Correct where

open import LTL.Procedures.Everything public
import LTL.Statement as T
open T using (_,_⊨_)
import LTL.Semantics.Orbit
import LTL.Semantics.OrbitEval

------------------------------------------------------------------------
-- The bridge.  States have any type S, and read gives the instant of a state;
-- toPosition reads a position the same way.

module _ {S : Set} (read : S -> T.Instant) where

  private
    module O = LTL.Semantics.Orbit S
    module E = LTL.Semantics.OrbitEval S read

  toPosition : O.Pos -> T.Position
  toPosition (s , ws) = T.at (read s) (map read ws)

  -- L agrees with the lasso of loop from pos0 when it starts at pos0 and loops
  -- back to loop.  Then T.step is nextPos, and so the positions of L are the
  -- iterates of nextPos from pos0.

  module _ (loop : O.Pos) (L : T.Lasso) (pos0 : O.Pos)
           (loopAgree    : T.Lasso.loop L ≡ toPosition loop)
           (initialAgree : T.initial L ≡ toPosition pos0) where

    stepAgree : (q : O.Pos) -> T.step L (toPosition q) ≡ toPosition (O.nextPos loop q)
    stepAgree (s , [])     = loopAgree
    stepAgree (s , w ∷ ws) = refl

    private
      stage : Nat -> O.Pos
      stage n = O.posIter loop n pos0

      EvalsTrue : Formula -> O.Pos -> Set
      EvalsTrue A q = E.evalAt loop A q ≡ true

      nowAgree : (q : O.Pos) -> T.Position.now (toPosition q) ≡ read (O.posState q)
      nowAgree (s , ws) = refl

    positionAgree : (n : Nat) -> T.position L n ≡ toPosition (stage n)
    positionAgree zero    = initialAgree
    positionAgree (suc n) =
      trans (cong (T.step L) (positionAgree n))
            (trans (stepAgree (stage n))
                   (cong toPosition (sym (O.posIter-suc loop n pos0))))

    interpretAgree : (n : Nat) -> T.interpret L n ≡ read (O.posState (stage n))
    interpretAgree n =
      trans (cong T.Position.now (positionAgree n)) (nowAgree (stage n))

    ----------------------------------------------------------------------
    -- The Boolean evaluation is the semantics.  Both directions are proved
    -- together, since ¬ and ⇒ are contravariant in their first argument.

    evalAt-holds : (A : Formula) (n : Nat) -> EvalsTrue A (stage n) -> T.interpret L , n ⊨ A
    holds-evalAt : (A : Formula) (n : Nat) -> T.interpret L , n ⊨ A -> EvalsTrue A (stage n)

    evalAt-holds (var x) n e = subst (λ i -> i x ≡ true) (sym (interpretAgree n)) e

    evalAt-holds (¬ A) n e h =
      true≢false (trans (sym (holds-evalAt A n h))
                        (¬ᵇ-true (E.evalAt loop A (stage n)) e))

    evalAt-holds (A ⇒ B) n e h =
      evalAt-holds B n
        (⇒ᵇ-mp (E.evalAt loop A (stage n)) (E.evalAt loop B (stage n))
               e (holds-evalAt A n h))

    evalAt-holds (○ A) n e =
      evalAt-holds A (suc n)
        (subst (EvalsTrue A) (sym (O.posIter-suc loop n pos0)) e)

    evalAt-holds (□ A) n e k =
      evalAt-holds A (k + n)
        (subst (EvalsTrue A) (sym (O.posIter-+ʳ loop k n pos0))
               (E.eval□-at loop A (stage n) (O.posIter loop k (stage n)) e
                           (O.iter∈orbit loop k (stage n))))

    holds-evalAt (var x) n h = subst (λ i -> i x ≡ true) (interpretAgree n) h

    holds-evalAt (¬ A) n h with E.evalAt loop A (stage n) in ea
    ... | true  = emptyElim (h (evalAt-holds A n ea))
    ... | false = refl

    holds-evalAt (A ⇒ B) n h =
      ⇒ᵇ-intro (E.evalAt loop A (stage n)) (E.evalAt loop B (stage n))
               (λ ea -> holds-evalAt B n (h (evalAt-holds A n ea)))

    holds-evalAt (○ A) n h =
      subst (EvalsTrue A) (O.posIter-suc loop n pos0) (holds-evalAt A (suc n) h)

    holds-evalAt (□ A) n h =
      E.eval□-intro loop A (stage n)
        (O.orbit-all loop (EvalsTrue A) (stage n)
           (λ t -> subst (EvalsTrue A) (O.posIter-+ʳ loop t n pos0)
                         (holds-evalAt A (t + n) (h t))))

------------------------------------------------------------------------
-- Soundness: a derivable formula is valid.  A Statement lasso l is a lasso of
-- instants, read by the identity, from T.initial l back to T.Lasso.loop l;
-- OrbitEval's soundness holds there.

⊢-valid : {A : Formula} -> ⊢ A -> T.valid A
⊢-valid {A} d l =
  evalAt-holds read loop l pos0
    (cong (T.at _) (sym (map-id (T.Position.rest (T.Lasso.loop l)))))
    (cong (T.at _) (sym (map-id (T.Position.rest (T.initial l)))))
    A zero (LTL.Semantics.OrbitEval.sound T.Instant read loop d pos0)
  where
    read : T.Instant -> T.Instant
    read i = i

    loop pos0 : T.Instant × List T.Instant
    loop = T.Position.now (T.Lasso.loop l) , T.Position.rest (T.Lasso.loop l)
    pos0 = T.Position.now (T.initial l) , T.Position.rest (T.initial l)

------------------------------------------------------------------------
-- A countermodel is a Statement countermodel.  Its lasso, read through readVal
-- (¬ Q), is a Statement lasso: start followed by rest, then the cycle from loop
-- for ever.  Q is false at stage 0 (falseAtStart), so it is not true at
-- time 0.

toCountermodel : (Q : Formula) -> LassoCountermodel Q -> T.LassoCountermodel Q
toCountermodel Q c = T.counter L qFalse
  where
    open LassoCountermodel c
    open Lasso lasso using (loop; rest)

    read : Val -> T.Instant
    read = readVal (¬ Q)

    L : T.Lasso
    L = record { start = map read (start ∷ rest)
               ; loop  = toPosition read loop }

    qFalse : T.interpret L , zero ⊨ ¬ Q
    qFalse h =
      true≢false
        (trans (sym (holds-evalAt read loop L (start , rest) refl refl Q zero h))
               falseAtStart)

-- So a countermodel rules out a derivation: the derivation would be valid,
-- in particular on the countermodel's own lasso.

cmUnderivable : (Q : Formula) -> LassoCountermodel Q -> ⊢ Q -> Empty
cmUnderivable Q c d with toCountermodel Q c
... | T.counter L notQ = notQ (⊢-valid d L)

------------------------------------------------------------------------
-- decide as a Statement DecisionProcedure.  The test is which branch it took:
-- a derivation is valid by ⊢-valid, and a countermodel translates by
-- toCountermodel.

decideCorrect : T.DecisionProcedure
decideCorrect = record
  { decideValid    = λ Q -> isProof (decide Q)
  ; validIfTrue    = validIfTrue
  ; counterIfFalse = counterIfFalse
  }
  where
    validIfTrue : (Q : Formula) -> isProof (decide Q) ≡ true -> T.valid Q
    validIfTrue Q e with decide Q
    ... | inl d = ⊢-valid d
    ... | inr c = emptyElim (true≢false (sym e))

    counterIfFalse : (Q : Formula) -> isProof (decide Q) ≡ false
                  -> T.LassoCountermodel Q
    counterIfFalse Q e with decide Q
    ... | inl d = emptyElim (true≢false e)
    ... | inr c = toCountermodel Q c

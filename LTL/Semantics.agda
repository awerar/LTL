{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Semantics -- the Boolean evaluation agrees with the semantics of
-- LTL.Trusted, and so the procedure meets the trusted specification.
--
-- LTL.Trusted defines truth  σ , n ⊨ A , validity (truth at time 0 of every
-- lasso), and a DecisionProcedure.  The procedure answers with  ⊢ Q ⊎
-- LassoCountermodel Q , connected to it by
--
--   ⊢-valid         a derivable formula is valid, and
--   toCounterModel  the lasso of a LassoCountermodel is a Trusted lasso on
--                   which Q is false at time 0;
--
-- and fromDecider packages the two.  Both go through the evaluation of
-- LTL.Countermodel.LassoEval; what this module adds is that evalAt IS ⊨
-- (evalAt-holds, holds-evalAt), by induction on the formula.  The □ case uses
-- the finite forward orbit: every iterate of a position is in its orbit, and
-- every member of the orbit is an iterate.
--
-- LTL.Trusted is imported qualified as T, since its names clash with this
-- development's.

module LTL.Semantics where

open import LTL.Procedures.Answer public
import LTL.Trusted as T
import LTL.Countermodel.Orbit
import LTL.Countermodel.LassoEval

------------------------------------------------------------------------
-- Truth in LTL.Trusted, written prefix

Holds : T.Interpretation -> Nat -> Formula -> Set
Holds σ n A = T._,_⊨_ σ n A

emptyElimT : {X : Set} -> T.Empty -> X
emptyElimT ()

------------------------------------------------------------------------
-- A lasso with states of type S, the position loop it loops back to, and read
-- giving the instant of a state.

module _ {S : Set} (read : S -> T.Instant) (loop : S × List S) where

  private
    module O = LTL.Countermodel.Orbit S
    module E = LTL.Countermodel.LassoEval S read

  -- The positions of a Trusted lasso L are the iterates of nextPos, once f
  -- turns nextPos into T.step and the start into T.initial.

  positionAgree : (L : T.Lasso) (f : O.Pos -> T.Position) (pos0 : O.Pos)
               -> ((q : O.Pos) -> T.step L (f q) ≡ f (O.nextPos loop q))
               -> T.initial L ≡ f pos0
               -> (n : Nat) -> T.position L n ≡ f (O.posIter loop n pos0)
  positionAgree L f pos0 st ini zero    = ini
  positionAgree L f pos0 st ini (suc n) =
    trans (cong (T.step L) (positionAgree L f pos0 st ini n))
          (trans (st (O.posIter loop n pos0))
                 (cong f (sym (O.posIter-suc loop n pos0))))

  ------------------------------------------------------------------------
  -- The Boolean evaluation is the semantics.  σ agrees with the lasso from
  -- pos0 when its instant at time n is the one read off stage n.  Both
  -- directions are proved together, since ¬ and ⇒ are contravariant in their
  -- first argument.

  module _ (pos0 : O.Pos) (σ : T.Interpretation)
           (agree : (n : Nat) -> σ n ≡ read (O.posState (O.posIter loop n pos0)))
           where

    private
      stage : Nat -> O.Pos
      stage n = O.posIter loop n pos0

      True : Formula -> O.Pos -> Set
      True A q = E.evalAt loop A q ≡ true

    evalAt-holds : (A : Formula) (n : Nat) -> True A (stage n) -> Holds σ n A
    holds-evalAt : (A : Formula) (n : Nat) -> Holds σ n A -> True A (stage n)

    evalAt-holds (var x) n e = subst (λ i -> i x ≡ true) (sym (agree n)) e

    evalAt-holds (¬ A) n e h =
      emptyElim (true≢false
                   (trans (sym (holds-evalAt A n h))
                          (¬ᵇ-true (E.evalAt loop A (stage n)) e)))

    evalAt-holds (A ⇒ B) n e h =
      evalAt-holds B n
        (⇒ᵇ-mp (E.evalAt loop A (stage n)) (E.evalAt loop B (stage n))
               e (holds-evalAt A n h))

    evalAt-holds (○ A) n e =
      evalAt-holds A (suc n)
        (subst (True A) (sym (O.posIter-suc loop n pos0)) e)

    evalAt-holds (□ A) n e k =
      evalAt-holds A (k + n)
        (subst (True A) (sym (O.posIter-+ʳ loop k n pos0))
               (E.eval□-at loop A (stage n) (O.posIter loop k (stage n)) e
                           (O.iter∈orbit loop k (stage n))))

    holds-evalAt (var x) n h = subst (λ i -> i x ≡ true) (agree n) h

    holds-evalAt (¬ A) n h with E.evalAt loop A (stage n) in ea
    ... | true  = emptyElimT (h (evalAt-holds A n ea))
    ... | false = refl

    holds-evalAt (A ⇒ B) n h =
      ⇒ᵇ-intro (E.evalAt loop A (stage n)) (E.evalAt loop B (stage n))
               (λ ea -> holds-evalAt B n (h (evalAt-holds A n ea)))

    holds-evalAt (○ A) n h =
      subst (True A) (O.posIter-suc loop n pos0) (holds-evalAt A (suc n) h)

    holds-evalAt (□ A) n h =
      E.eval□-intro loop A (stage n)
        (λ q m -> fromIter q (O.∈orbit-iter loop (stage n) q m))
      where
        fromIter : (q : O.Pos) -> Σ[ t ∈ Nat ] O.posIter loop t (stage n) ≡ q
                -> True A q
        fromIter q (t , et) =
          subst (True A) (trans (O.posIter-+ʳ loop t n pos0) et)
                (holds-evalAt A (t + n) (h t))

------------------------------------------------------------------------
-- Soundness: a derivable formula is valid.  A Trusted lasso is a lasso of
-- LTL.Countermodel.Orbit at S = Instant, from the position T.initial l;
-- LassoEval's soundness holds there, and the evaluation is the semantics.

⊢-valid : {A : Formula} -> ⊢ A -> T.valid A
⊢-valid {A} d l =
  evalAt-holds read loop pos0 (T.interpret l) agree A zero
               (LTL.Countermodel.LassoEval.sound T.Instant read loop d pos0)
  where
    module O = LTL.Countermodel.Orbit T.Instant

    read : T.Instant -> T.Instant
    read i = i

    loop : O.Pos
    loop = T.Lasso.loopHead l , T.Lasso.loopTail l

    pos0 : O.Pos
    pos0 = T.Position.now (T.initial l) , T.Position.rest (T.initial l)

    f : O.Pos -> T.Position
    f (s , ws) = T.at s ws

    st : (q : O.Pos) -> T.step l (f q) ≡ f (O.nextPos loop q)
    st (s , [])     = refl
    st (s , w ∷ ws) = refl

    nowF : (q : O.Pos) -> T.Position.now (f q) ≡ O.posState q
    nowF (s , ws) = refl

    agree : (n : Nat) -> T.interpret l n ≡ O.posState (O.posIter loop n pos0)
    agree n = trans (cong T.Position.now (positionAgree read loop l f pos0 st refl n))
                    (nowF (O.posIter loop n pos0))

------------------------------------------------------------------------
-- A countermodel is a Trusted countermodel.  Its lasso, read through readVal
-- (¬ Q), is a Trusted lasso: v0 followed by rest, then the cycle c0 ∷ c1 for
-- ever, where loop = c0 , c1 .  Q is false at stage 0 (falseAtStart), so it is
-- not true at time 0.

toCounterModel : (Q : Formula) -> LassoCountermodel Q -> T.LassoCounterModel Q
toCounterModel Q
  (countermodel v0 (mkLasso (mkCycle b (c0 , c1) lv stb) fair rest sv) falseQ) =
  T.counter L qFalse
  where
    loop : Pos
    loop = c0 , c1

    rd : Val -> T.Instant
    rd = readVal (¬ Q)

    L : T.Lasso
    L = record { start = rd v0 ∷ map rd rest
               ; loopHead = rd c0
               ; loopTail = map rd c1 }

    f : Pos -> T.Position
    f (s , ws) = T.at (rd s) (map rd ws)

    st : (q : Pos) -> T.step L (f q) ≡ f (nextPos loop q)
    st (s , [])     = refl
    st (s , w ∷ ws) = refl

    nowF : (q : Pos) -> T.Position.now (f q) ≡ rd (posState q)
    nowF (s , ws) = refl

    agree : (n : Nat) -> T.interpret L n ≡ rd (posState (posIter loop n (v0 , rest)))
    agree n = trans (cong T.Position.now (positionAgree rd loop L f (v0 , rest) st refl n))
                    (nowF (posIter loop n (v0 , rest)))

    qFalse : Holds (T.interpret L) zero (¬ Q)
    qFalse h =
      emptyElim (true≢false
                   (trans (sym (holds-evalAt rd loop (v0 , rest) (T.interpret L)
                                             agree Q zero h))
                          falseQ))

------------------------------------------------------------------------
-- Every procedure of the type of decideSCC is a Trusted DecisionProcedure.  The
-- test is which branch it took: a derivation is valid by ⊢-valid, and a
-- countermodel translates by toCounterModel.

fromDecider : ((Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q)
           -> T.DecisionProcedure
fromDecider dec = record
  { decideValid    = λ Q -> isProof (dec Q)
  ; validIfTrue    = validIfTrue
  ; counterIfFalse = counterIfFalse
  }
  where
    validIfTrue : (Q : Formula) -> isProof (dec Q) ≡ true -> T.valid Q
    validIfTrue Q e with dec Q
    ... | inl d = ⊢-valid d
    ... | inr c = emptyElim (true≢false (sym e))

    counterIfFalse : (Q : Formula) -> isProof (dec Q) ≡ false
                  -> T.LassoCounterModel Q
    counterIfFalse Q e with dec Q
    ... | inl d = emptyElim (true≢false e)
    ... | inr c = toCounterModel Q c

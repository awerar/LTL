{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Orbit -- positions on a lasso and their forward orbits, for
-- any type S of states.
--
-- A position is a pair (s , rest): the current state, and the states still to
-- come before the lasso loops back.  Given the position loop it loops back
-- to, the successor is
--
--    (s , w ∷ ws)  |->  (w , ws)          walk on
--    (s , [])      |->  loop              loop back
--
-- which is Position, step and loopBack of LTL.Trusted.  This avoids index
-- arithmetic: the forward orbit of pos is literally  stretch pos ++ loopStretch
-- (orbit-split), and everything about orbits follows from that equation.
--
-- Positions and stretches do not depend on the lasso; everything else sits in
-- a block parameterised by loop, which callers pass first.  Σ has no eta
-- rule, so definitions that inspect a Pos match it as a pair.
--
-- LTL.Countermodel.Lasso instantiates S at valuations, and LTL.Semantics at
-- LTL.Trusted's Instant; LTL.Countermodel.LassoEval evaluates formulas on
-- either.

module LTL.Countermodel.Orbit (S : Set) where

open import LTL.Lib.Prelude

------------------------------------------------------------------------
-- Positions and stretches

Pos : Set
Pos = S × List S

posState : Pos -> S
posState (s , rest) = s

-- The states met walking from pos to the end of its stretch.

stretchStates : Pos -> List S
stretchStates (s , rest) = s ∷ rest

-- The positions met walking from pos to the end of its stretch.  The
-- recursion is on the list, since (w , ws) is not structurally smaller than
-- (s , w ∷ ws).

stretch : Pos -> List Pos
stretch (s , rest) = go s rest
  where
    go : S -> List S -> List Pos
    go s []       = (s , []) ∷ []
    go s (w ∷ ws) = (s , w ∷ ws) ∷ go w ws

stretch-head : (pos : Pos) -> pos ∈ stretch pos
stretch-head (s , [])     = here
stretch-head (s , w ∷ ws) = here

-- A state visited on a stretch is the state of a position on it.

stretch-mem : (pos : Pos) {z : S} -> z ∈ stretchStates pos
           -> Σ[ q ∈ Pos ] q ∈ stretch pos × posState q ≡ z
stretch-mem (s , [])     here      = (s , []) , here , refl
stretch-mem (s , [])     (there ())
stretch-mem (s , w ∷ ws) here      = (s , w ∷ ws) , here , refl
stretch-mem (s , w ∷ ws) (there m) with stretch-mem (w , ws) m
... | q , mq , eq = q , there mq , eq

------------------------------------------------------------------------
-- The successor function and its iterates, on the lasso that loops back to
-- the position loop

module _ (loop : Pos) where

  nextPos : Pos -> Pos
  nextPos (s , [])     = loop
  nextPos (s , w ∷ ws) = w , ws

  posIter : Nat -> Pos -> Pos
  posIter zero    pos = pos
  posIter (suc i) pos = posIter i (nextPos pos)

  -- Iterating i + t times is iterating i times and then t more.

  posIter-+ˡ : (i t : Nat) (pos : Pos)
            -> posIter (i + t) pos ≡ posIter t (posIter i pos)
  posIter-+ˡ zero    t pos = refl
  posIter-+ˡ (suc i) t pos = posIter-+ˡ i t (nextPos pos)

  posIter-suc : (t : Nat) (pos : Pos)
             -> posIter (suc t) pos ≡ nextPos (posIter t pos)
  posIter-suc zero    pos = refl
  posIter-suc (suc t) pos = posIter-suc t (nextPos pos)

  -- Iterating k + n times is iterating n times and then k more.

  posIter-+ʳ : (k n : Nat) (pos : Pos)
            -> posIter (k + n) pos ≡ posIter k (posIter n pos)
  posIter-+ʳ zero    n pos = refl
  posIter-+ʳ (suc k) n pos =
    trans (posIter-suc (k + n) pos)
          (trans (cong nextPos (posIter-+ʳ k n pos))
                 (sym (posIter-suc k (posIter n pos))))

  ------------------------------------------------------------------------
  -- The forward orbit

  -- One turn of the cycle, from loop.

  loopStretch : List Pos
  loopStretch = stretch loop

  -- The first n positions of the orbit from pos.

  orbitN : Nat -> Pos -> List Pos
  orbitN zero    pos = []
  orbitN (suc n) pos = pos ∷ orbitN n (nextPos pos)

  -- The equation everything rests on: walking past the end of a stretch
  -- lands on loop.
  orbitN-split : (pos : Pos) (n : Nat)
              -> orbitN (length (stretch pos) + n) pos ≡
                 stretch pos ++ orbitN n loop
  orbitN-split (s , rest) n = go s rest
    where
      go : (s : S) (rest : List S)
        -> orbitN (length (stretch (s , rest)) + n) (s , rest) ≡
           stretch (s , rest) ++ orbitN n loop
      go s []       = refl
      go s (w ∷ ws) = cong (λ L -> (s , w ∷ ws) ∷ L) (go w ws)

  orbitN-loopStretch : orbitN (length loopStretch) loop ≡ loopStretch ++ []
  orbitN-loopStretch =
    subst (λ k -> orbitN k loop ≡ loopStretch ++ [])
          (+-identityʳ (length loopStretch))
          (orbitN-split loop zero)

  -- The rest of the stretch from pos, then one turn of the cycle.

  orbit : Pos -> List Pos
  orbit pos = orbitN (length (stretch pos) + length loopStretch) pos

  -- Every position of an orbit is reached from its start by iterating.

  ∈orbitN-iter : (n : Nat) (pos q : Pos)
              -> q ∈ orbitN n pos
              -> Σ[ t ∈ Nat ] posIter t pos ≡ q
  ∈orbitN-iter zero    pos q ()
  ∈orbitN-iter (suc n) pos q here      = zero , refl
  ∈orbitN-iter (suc n) pos q (there m) with ∈orbitN-iter n (nextPos pos) q m
  ... | t , e = suc t , e

  ∈orbit-iter : (pos q : Pos)
             -> q ∈ orbit pos
             -> Σ[ t ∈ Nat ] posIter t pos ≡ q
  ∈orbit-iter pos q m =
    ∈orbitN-iter (length (stretch pos) + length loopStretch) pos q m

  ------------------------------------------------------------------------
  -- The orbit as a plain concatenation: the rest of the stretch, then one
  -- turn of the cycle.  Everything below is read off this equation.

  orbit-split : (pos : Pos) -> orbit pos ≡ stretch pos ++ loopStretch
  orbit-split pos =
    trans (orbitN-split pos (length loopStretch))
          (cong (λ L -> stretch pos ++ L)
                (trans orbitN-loopStretch (++-identityʳ loopStretch)))

  stretch⊆orbit : (pos : Pos) -> stretch pos ⊆ orbit pos
  stretch⊆orbit pos q m =
    subst (λ L -> q ∈ L) (sym (orbit-split pos))
          (memAppL (stretch pos) loopStretch m)

  loopStretch⊆orbit : (pos : Pos) -> loopStretch ⊆ orbit pos
  loopStretch⊆orbit pos q m =
    subst (λ L -> q ∈ L) (sym (orbit-split pos))
          (memAppR (stretch pos) loopStretch m)

  orbitHead : (pos : Pos) -> pos ∈ orbit pos
  orbitHead pos = stretch⊆orbit pos pos (stretch-head pos)

  ------------------------------------------------------------------------
  -- The orbit is closed under the successor: walking on stays in the same
  -- stretch until it runs out, then lands on loop.

  stretch-next : (pos q : Pos)
              -> q ∈ stretch pos
              -> nextPos q ∈ stretch pos ⊎ nextPos q ≡ loop
  stretch-next (s , [])     q here      = inr refl
  stretch-next (s , [])     q (there ())
  stretch-next (s , w ∷ ws) q here      = inl (there (stretch-head (w , ws)))
  stretch-next (s , w ∷ ws) q (there m) =
    sumElim (λ mm -> inl (there mm)) inr (stretch-next (w , ws) q m)

  orbitClosed : (pos q : Pos)
             -> q ∈ orbit pos -> nextPos q ∈ orbit pos
  orbitClosed pos q m =
    subst (λ L -> nextPos q ∈ L) (sym (orbit-split pos))
          (sumElim onStretch onCycle
                   (memAppCase (stretch pos) loopStretch
                               (subst (λ L -> q ∈ L) (orbit-split pos) m)))
    where
      intoCycle : nextPos q ≡ loop -> nextPos q ∈ stretch pos ++ loopStretch
      intoCycle e =
        subst (λ r -> r ∈ stretch pos ++ loopStretch) (sym e)
              (memAppR (stretch pos) loopStretch (stretch-head loop))

      onStretch : q ∈ stretch pos -> nextPos q ∈ stretch pos ++ loopStretch
      onStretch mq = sumElim (λ mm -> memAppL (stretch pos) loopStretch mm)
                             intoCycle (stretch-next pos q mq)

      onCycle : q ∈ loopStretch -> nextPos q ∈ stretch pos ++ loopStretch
      onCycle mq = sumElim (λ mm -> memAppR (stretch pos) loopStretch mm)
                           intoCycle (stretch-next loop q mq)

  iter∈orbit : (t : Nat) (pos : Pos) -> posIter t pos ∈ orbit pos
  iter∈orbit zero    pos = orbitHead pos
  iter∈orbit (suc t) pos =
    subst (λ r -> r ∈ orbit pos) (sym (posIter-suc t pos))
          (orbitClosed pos (posIter t pos) (iter∈orbit t pos))

  -- so the orbit of a successor is contained in the orbit
  nextOrbit⊆orbit : (pos : Pos) -> orbit (nextPos pos) ⊆ orbit pos
  nextOrbit⊆orbit pos q m with ∈orbit-iter (nextPos pos) q m
  ... | t , et = subst (λ r -> r ∈ orbit pos) et (iter∈orbit (suc t) pos)

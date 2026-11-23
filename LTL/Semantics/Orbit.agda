{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Semantics.Orbit -- positions on a lasso and their forward orbits, for
-- any type S of states.
--
-- A position is a pair (s , rest): the current state, and the states still to
-- come before the lasso loops back.  Given the position loop it loops back
-- to, the successor is
--
--    (s , w ∷ ws)  |->  (w , ws)          walk on
--    (s , [])      |->  loop              loop back
--
-- which is Position, step and Lasso.loop of LTL.Statement.  This avoids index
-- arithmetic: the forward orbit of pos is literally  stretch pos ++ loopStretch
-- (orbit-split), and everything about orbits follows from that equation.
--
-- Positions and stretches do not depend on the lasso; everything else sits in
-- a block parameterised by loop, which callers pass first.  Σ has no eta
-- rule, so definitions that inspect a Pos match it as a pair.
--
-- LTL.Countermodel.Lasso instantiates S at valuations, and LTL.Correct at
-- LTL.Statement's Instant; LTL.Semantics.OrbitEval evaluates formulas on
-- either.

module LTL.Semantics.Orbit (S : Set) where

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

stretch-mem : (pos : Pos)
           -> ∀ⁱ[ z ∈ stretchStates pos ] ∃[ q ∈ stretch pos ] posState q ≡ z
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

  -- The position after t steps.  The last step is taken outermost, as in
  -- LTL.Statement's position, so posIter pos (suc t) is nextPos (posIter pos t)
  -- by definition.

  posIter : Pos -> Nat -> Pos
  posIter pos zero    = pos
  posIter pos (suc t) = nextPos (posIter pos t)

  -- Iterating k + n times is iterating n times and then k more.

  posIter-+ : (pos : Pos) (k n : Nat)
           -> posIter pos (k + n) ≡ posIter (posIter pos n) k
  posIter-+ pos zero    n = refl
  posIter-+ pos (suc k) n = cong nextPos (posIter-+ pos k n)

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

  -- Every position of an orbit is reached from its start by iterating.  The
  -- search starts at the j-th iterate and counts j up as it walks on.

  ∈orbitN-iter : (pos : Pos) (n j : Nat) (q : Pos)
              -> q ∈ orbitN n (posIter pos j)
              -> Σ[ t ∈ Nat ] posIter pos t ≡ q
  ∈orbitN-iter pos zero    j q ()
  ∈orbitN-iter pos (suc n) j q here      = j , refl
  ∈orbitN-iter pos (suc n) j q (there m) = ∈orbitN-iter pos n (suc j) q m

  ∈orbit-iter : (pos q : Pos)
             -> q ∈ orbit pos
             -> Σ[ t ∈ Nat ] posIter pos t ≡ q
  ∈orbit-iter pos q m =
    ∈orbitN-iter pos (length (stretch pos) + length loopStretch) zero q m

  -- So what holds at every iterate holds on the whole orbit.

  orbit-all : (R : Pos -> Set) (pos : Pos)
           -> ((t : Nat) -> R (posIter pos t))
           -> ∀[ q ∈ orbit pos ] R q
  orbit-all R pos h q m with ∈orbit-iter pos q m
  ... | t , et = subst R et (h t)

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

  iter∈orbit : (pos : Pos) (t : Nat) -> posIter pos t ∈ orbit pos
  iter∈orbit pos zero    = orbitHead pos
  iter∈orbit pos (suc t) = orbitClosed pos (posIter pos t) (iter∈orbit pos t)

  -- so the orbit of a successor is contained in the orbit
  nextOrbit⊆orbit : (pos : Pos) -> orbit (nextPos pos) ⊆ orbit pos
  nextOrbit⊆orbit pos = orbit-all (λ r -> r ∈ orbit pos) (nextPos pos) along
    where
      along : (t : Nat) -> posIter (nextPos pos) t ∈ orbit pos
      along zero    = orbitClosed pos pos (orbitHead pos)
      along (suc t) = orbitClosed pos (posIter (nextPos pos) t) (along t)

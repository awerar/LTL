{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Orbit -- positions on a lasso and their forward orbits, for any type S
-- of states.
--
-- m4.tex unwinds a lasso into the infinite sequence v_0,v_1,v_2,... with
-- v_i = v_{p+((i-p) mod (q-p))} for i >= p, and then says: "the lasso is a
-- finite structure with a total successor function, so Always and Eventually
-- evaluate on it by conjunction and disjunction over the finite forward orbit
-- of a state".
--
-- Taken literally that asks for indices into a flat list of states, a successor
-- function  k |-> k+1 wrapping at the end, and a forward orbit obtained by
-- iterating it -- and then for arithmetic: that consecutive indices step, that
-- the wrap lands on the right index, that the orbit from any index covers the
-- whole cycle.  None of that is necessary.
--
-- A POSITION is instead a pair (s , rest): the current state, and the states
-- still to come before the cycle starts again.  The successor is
--
--    (s , w ∷ ws)  |->  (w , ws)          walk on
--    (s , [])       |->  (c0 , c1)         wrap to the head of the cycle
--
-- which is Position and step of LTL.Trusted, with c0 and c1 its loopHead and
-- loopTail.  The forward orbit of (s , rest), with the fuel that is obviously
-- enough, is LITERALLY  posList s rest ++ posList c0 c1  -- walk out the
-- remaining rest, then walk once round the cycle -- which is orbitN-split
-- below, proved by a three-line induction.  Everything about orbits follows
-- from that one equation by memAppL and memAppR.
--
-- The module is parameterised by the type of states, like LTL.Lib.Nodes by its
-- nodes.  LTL.Countermodel.Run instantiates it at valuations, for the runs the elimination
-- builds, and LTL.Semantics at LTL.Trusted's Instant, for an arbitrary lasso;
-- LTL.Countermodel.LassoEval evaluates formulas on either.

module LTL.Countermodel.Orbit (S : Set) where

open import LTL.Lib.Prelude

------------------------------------------------------------------------
-- Positions and the successor function

Pos : Set
Pos = S × List S

posState : Pos -> S
posState (s , rest) = s

nextPos : S -> List S -> Pos -> Pos
nextPos c0 c1 (s , [])     = c0 , c1
nextPos c0 c1 (s , w ∷ ws) = w , ws

posIter : S -> List S -> Nat -> Pos -> Pos
posIter c0 c1 zero    pos = pos
posIter c0 c1 (suc i) pos = posIter c0 c1 i (nextPos c0 c1 pos)

posIter-plus : (c0 : S) (c1 : List S) (i t : Nat) (pos : Pos)
            -> posIter c0 c1 (i + t) pos ≡
               posIter c0 c1 t (posIter c0 c1 i pos)
posIter-plus c0 c1 zero    t pos = refl
posIter-plus c0 c1 (suc i) t pos = posIter-plus c0 c1 i t (nextPos c0 c1 pos)

------------------------------------------------------------------------
-- The forward orbit

posList : S -> List S -> List Pos
posList s []       = (s , []) ∷ []
posList s (w ∷ ws) = (s , w ∷ ws) ∷ posList w ws

-- The first n positions of the orbit from pos.

orbitN : S -> List S -> Nat -> Pos -> List Pos
orbitN c0 c1 zero    pos = []
orbitN c0 c1 (suc n) pos = pos ∷ orbitN c0 c1 n (nextPos c0 c1 pos)

-- The equation everything rests on.
orbitN-split : (c0 : S) (c1 : List S) (s : S) (rest : List S) (n : Nat)
            -> orbitN c0 c1 (suc (length rest + n)) (s , rest) ≡
               posList s rest ++ orbitN c0 c1 n (c0 , c1)
orbitN-split c0 c1 s []       n = refl
orbitN-split c0 c1 s (w ∷ ws) n =
  cong (λ L -> (s , w ∷ ws) ∷ L) (orbitN-split c0 c1 w ws n)

orbitOf : S -> List S -> Pos -> List Pos
orbitOf c0 c1 (s , rest) =
  orbitN c0 c1 (suc (length rest + suc (length c1))) (s , rest)

-- One full turn from the head of the cycle visits posList c0 c1.

cycOrbit : (c0 : S) (c1 : List S)
        -> orbitN c0 c1 (suc (length c1)) (c0 , c1) ≡
           posList c0 c1 ++ []
cycOrbit c0 c1 =
  subst (λ k -> orbitN c0 c1 (suc k) (c0 , c1) ≡
                posList c0 c1 ++ [])
        (+-identityʳ (length c1))
        (orbitN-split c0 c1 c0 c1 zero)

orbitStem : (c0 : S) (c1 : List S) (s : S) (rest : List S) (q : Pos)
         -> q ∈ posList s rest -> q ∈ orbitOf c0 c1 (s , rest)
orbitStem c0 c1 s rest q m =
  subst (λ L -> q ∈ L)
        (sym (orbitN-split c0 c1 s rest (suc (length c1))))
        (memAppL (posList s rest) (orbitN c0 c1 (suc (length c1)) (c0 , c1)) m)

orbitCycle : (c0 : S) (c1 : List S) (s : S) (rest : List S) (q : Pos)
          -> q ∈ posList c0 c1 -> q ∈ orbitOf c0 c1 (s , rest)
orbitCycle c0 c1 s rest q m =
  subst (λ L -> q ∈ L)
        (sym (orbitN-split c0 c1 s rest (suc (length c1))))
        (memAppR (posList s rest) (orbitN c0 c1 (suc (length c1)) (c0 , c1))
                 (subst (λ L -> q ∈ L) (sym (cycOrbit c0 c1))
                        (memAppL (posList c0 c1) [] m)))

-- A state visited on a stretch is the state of a position on it.

posShift : {s w : S} {ws : List S} {z : S}
        -> Σ[ q ∈ Pos ] q ∈ posList w ws × posState q ≡ z
        -> Σ[ q ∈ Pos ] q ∈ posList s (w ∷ ws) × posState q ≡ z
posShift (q , mq , eq) = q , there mq , eq

posList-mem : (s : S) (rest : List S) {z : S} -> z ∈ s ∷ rest
           -> Σ[ q ∈ Pos ] q ∈ posList s rest × posState q ≡ z
posList-mem s []       here      = (s , []) , here , refl
posList-mem s []       (there ())
posList-mem s (w ∷ ws) here      = (s , w ∷ ws) , here , refl
posList-mem s (w ∷ ws) (there m) = posShift (posList-mem w ws m)

-- Every position of an orbit is reached from its start by iterating.

posBump : {c0 : S} {c1 : List S} {pos q : Pos}
       -> Σ[ t ∈ Nat ] posIter c0 c1 t (nextPos c0 c1 pos) ≡ q
       -> Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q
posBump (t , e) = suc t , e

orbitN-iter : (c0 : S) (c1 : List S) (n : Nat) (pos q : Pos)
           -> q ∈ orbitN c0 c1 n pos
           -> Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q
orbitN-iter c0 c1 zero    pos q ()
orbitN-iter c0 c1 (suc n) pos q here      = zero , refl
orbitN-iter c0 c1 (suc n) pos q (there m) =
  posBump (orbitN-iter c0 c1 n (nextPos c0 c1 pos) q m)

orbitOf-iter : (c0 : S) (c1 : List S) (pos q : Pos)
            -> q ∈ orbitOf c0 c1 pos
            -> Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q
orbitOf-iter c0 c1 (s , rest) q m =
  orbitN-iter c0 c1 (suc (length rest + suc (length c1))) (s , rest) q m

------------------------------------------------------------------------
-- The orbit, once more, as a plain concatenation.
--
-- Everything below is read off this equation: the orbit of (s , rest) is the
-- rest of the walk followed by one turn of the cycle.

orbitEq : (c0 : S) (c1 : List S) (s : S) (rest : List S)
       -> orbitOf c0 c1 (s , rest) ≡
          posList s rest ++ posList c0 c1
orbitEq c0 c1 s rest =
  trans (orbitN-split c0 c1 s rest (suc (length c1)))
        (cong (λ L -> posList s rest ++ L)
              (trans (cycOrbit c0 c1) (++-identityʳ (posList c0 c1))))

orbitHead : (c0 : S) (c1 : List S) (pos : Pos) -> pos ∈ orbitOf c0 c1 pos
orbitHead c0 c1 (s , rest) = here

posList-hd : (s : S) (rest : List S) -> (s , rest) ∈ posList s rest
posList-hd s []       = here
posList-hd s (w ∷ ws) = here

------------------------------------------------------------------------
-- The orbit is closed under the successor.
--
-- Walking on stays inside the same stretch until the stretch runs out, and
-- then lands on the head of the cycle, which is in the orbit either way.

posList-next : (c0 : S) (c1 : List S) (s : S) (rest : List S) (q : Pos)
            -> q ∈ posList s rest
            -> nextPos c0 c1 q ∈ posList s rest ⊎
               nextPos c0 c1 q ≡ (c0 , c1)
posList-next c0 c1 s []       q here      = inr refl
posList-next c0 c1 s []       q (there ())
posList-next c0 c1 s (w ∷ ws) q here      = inl (there (posList-hd w ws))
posList-next c0 c1 s (w ∷ ws) q (there m) =
  sumElim (λ mm -> inl (there mm)) inr (posList-next c0 c1 w ws q m)

orbitClosed : (c0 : S) (c1 : List S) (pos q : Pos)
           -> q ∈ orbitOf c0 c1 pos -> nextPos c0 c1 q ∈ orbitOf c0 c1 pos
orbitClosed c0 c1 (s , rest) q m =
  subst (λ L -> nextPos c0 c1 q ∈ L) (sym (orbitEq c0 c1 s rest))
        (sumElim onStem onCyc
                 (memAppCase (posList s rest) (posList c0 c1)
                             (subst (λ L -> q ∈ L) (orbitEq c0 c1 s rest) m)))
  where
    intoCyc : nextPos c0 c1 q ≡ (c0 , c1)
           -> nextPos c0 c1 q ∈ posList s rest ++ posList c0 c1
    intoCyc e =
      subst (λ r -> r ∈ posList s rest ++ posList c0 c1) (sym e)
            (memAppR (posList s rest) (posList c0 c1) (posList-hd c0 c1))

    onStem : q ∈ posList s rest
          -> nextPos c0 c1 q ∈ posList s rest ++ posList c0 c1
    onStem mq = sumElim (λ mm -> memAppL (posList s rest) (posList c0 c1) mm)
                        intoCyc (posList-next c0 c1 s rest q mq)

    onCyc : q ∈ posList c0 c1
         -> nextPos c0 c1 q ∈ posList s rest ++ posList c0 c1
    onCyc mq = sumElim (λ mm -> memAppR (posList s rest) (posList c0 c1) mm)
                       intoCyc (posList-next c0 c1 c0 c1 q mq)

posIter-suc : (c0 : S) (c1 : List S) (t : Nat) (pos : Pos)
           -> posIter c0 c1 (suc t) pos ≡ nextPos c0 c1 (posIter c0 c1 t pos)
posIter-suc c0 c1 zero    pos = refl
posIter-suc c0 c1 (suc t) pos = posIter-suc c0 c1 t (nextPos c0 c1 pos)

orbitIter : (c0 : S) (c1 : List S) (t : Nat) (pos : Pos)
         -> posIter c0 c1 t pos ∈ orbitOf c0 c1 pos
orbitIter c0 c1 zero    pos = orbitHead c0 c1 pos
orbitIter c0 c1 (suc t) pos =
  subst (λ r -> r ∈ orbitOf c0 c1 pos) (sym (posIter-suc c0 c1 t pos))
        (orbitClosed c0 c1 pos (posIter c0 c1 t pos) (orbitIter c0 c1 t pos))

-- so the orbit of a successor is contained in the orbit
orbitSub : (c0 : S) (c1 : List S) (pos q : Pos)
        -> q ∈ orbitOf c0 c1 (nextPos c0 c1 pos) -> q ∈ orbitOf c0 c1 pos
orbitSub c0 c1 pos q m = fromIter (orbitOf-iter c0 c1 (nextPos c0 c1 pos) q m)
  where
    fromIter : (Σ[ t ∈ Nat ] posIter c0 c1 t (nextPos c0 c1 pos) ≡ q)
            -> q ∈ orbitOf c0 c1 pos
    fromIter (t , et) =
      subst (λ r -> r ∈ orbitOf c0 c1 pos) et (orbitIter c0 c1 (suc t) pos)

-- Iterating k + n times is iterating n times and then k more.

posIter-+ : (c0 : S) (c1 : List S) (k n : Nat) (pos : Pos)
         -> posIter c0 c1 (k + n) pos ≡ posIter c0 c1 k (posIter c0 c1 n pos)
posIter-+ c0 c1 zero    n pos = refl
posIter-+ c0 c1 (suc k) n pos =
  trans (posIter-suc c0 c1 (k + n) pos)
        (trans (cong (nextPos c0 c1) (posIter-+ c0 c1 k n pos))
               (sym (posIter-suc c0 c1 k (posIter c0 c1 n pos))))

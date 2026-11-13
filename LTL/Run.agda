{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Run -- the lasso unwound, as the finite structure G24 and G25 run on.
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
-- whole cycle.  That is the index bookkeeping section 3 of the plan warned
-- about, and none of it is necessary.
--
-- A POSITION is instead a pair (s , rest): the current state, and the states
-- still to come before the cycle starts again.  The successor is
--
--    (s , w ∷ ws)  |->  (w , ws)          walk on
--    (s , [])       |->  (c0 , c1)         wrap to the head of the cycle
--
-- and a position is VALID when rest is a walk from s back to the cycle's end b.
-- Validity is preserved by the successor, and the step proof falls out of the
-- Walk constructor being consumed: no arithmetic at all.  Better still, the
-- forward orbit of (s , rest), with the fuel that is obviously enough, is
-- LITERALLY  posList s rest ++ posList c0 c1  -- walk out the remaining rest,
-- then walk once round the cycle -- which is orbitN-split below, proved by a
-- three-line induction.  Everything G24 needs about orbits follows from that
-- one equation by memAppL and memAppR.

module LTL.Run where

open import LTL.Lasso public

------------------------------------------------------------------------
-- Addition (_+_ is Agda.Builtin.Nat's, re-exported by LTL.Base)

+-identityʳ : (m : Nat) -> m + zero ≡ m
+-identityʳ zero    = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

------------------------------------------------------------------------
-- Positions and the successor function

Pos : Set
Pos = Val × List Val

posState : Pos -> Val
posState (s , rest) = s

nextPos : Val -> List Val -> Pos -> Pos
nextPos c0 c1 (s , [])     = c0 , c1
nextPos c0 c1 (s , w ∷ ws) = w , ws

posIter : Val -> List Val -> Nat -> Pos -> Pos
posIter c0 c1 zero    pos = pos
posIter c0 c1 (suc i) pos = posIter c0 c1 i (nextPos c0 c1 pos)

posIter-plus : (c0 : Val) (c1 : List Val) (i t : Nat) (pos : Pos)
            -> posIter c0 c1 (i + t) pos ≡
               posIter c0 c1 t (posIter c0 c1 i pos)
posIter-plus c0 c1 zero    t pos = refl
posIter-plus c0 c1 (suc i) t pos = posIter-plus c0 c1 i t (nextPos c0 c1 pos)

------------------------------------------------------------------------
-- Valid positions.
--
-- rest is a walk from s back to b, the end of the cycle.  This is the whole
-- invariant; the transition relation of the run is a consequence of it.

data ValidPos (P : Formula) (b : Val) : Pos -> Set where
  vpos : (s : Val) (rest : List Val) -> s ∈ Uinf P
      -> Walk P (Uinf P) s rest b -> ValidPos P b (s , rest)

posStep : (P : Formula) (b c0 : Val) (c1 : List Val)
       -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
       -> {pos : Pos} -> ValidPos P b pos
       -> ValidPos P b (nextPos c0 c1 pos) ×
          step P (posState pos) (posState (nextPos c0 c1 pos)) ≡ true
posStep P b c0 c1 mc0 wc stb (vpos s []        ms wnil) =
  vpos c0 c1 mc0 wc , stb
posStep P b c0 c1 mc0 wc stb (vpos s (w ∷ ws) ms (wcons mw st wk)) =
  vpos w ws mw wk , st

posIn : (P : Formula) (b : Val) {pos : Pos}
     -> ValidPos P b pos -> posState pos ∈ Uinf P
posIn P b (vpos s rest ms wk) = ms

------------------------------------------------------------------------
-- The forward orbit

posList : Val -> List Val -> List Pos
posList s []       = (s , []) ∷ []
posList s (w ∷ ws) = (s , w ∷ ws) ∷ posList w ws

-- The first n positions of the orbit from pos.

orbitN : Val -> List Val -> Nat -> Pos -> List Pos
orbitN c0 c1 zero    pos = []
orbitN c0 c1 (suc n) pos = pos ∷ orbitN c0 c1 n (nextPos c0 c1 pos)

-- The equation everything rests on.
orbitN-split : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val) (n : Nat)
            -> orbitN c0 c1 (suc (length rest + n)) (s , rest) ≡
               posList s rest ++ orbitN c0 c1 n (c0 , c1)
orbitN-split c0 c1 s []       n = refl
orbitN-split c0 c1 s (w ∷ ws) n =
  cong (λ L -> (s , w ∷ ws) ∷ L) (orbitN-split c0 c1 w ws n)

orbitOf : Val -> List Val -> Pos -> List Pos
orbitOf c0 c1 (s , rest) =
  orbitN c0 c1 (suc (length rest + suc (length c1))) (s , rest)

-- One full turn from the head of the cycle visits posList c0 c1.

cycOrbit : (c0 : Val) (c1 : List Val)
        -> orbitN c0 c1 (suc (length c1)) (c0 , c1) ≡
           posList c0 c1 ++ []
cycOrbit c0 c1 =
  subst (λ k -> orbitN c0 c1 (suc k) (c0 , c1) ≡
                posList c0 c1 ++ [])
        (+-identityʳ (length c1))
        (orbitN-split c0 c1 c0 c1 zero)

orbitStem : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val) (q : Pos)
         -> q ∈ posList s rest -> q ∈ orbitOf c0 c1 (s , rest)
orbitStem c0 c1 s rest q m =
  subst (λ L -> q ∈ L)
        (sym (orbitN-split c0 c1 s rest (suc (length c1))))
        (memAppL (posList s rest) (orbitN c0 c1 (suc (length c1)) (c0 , c1)) m)

orbitCycle : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val) (q : Pos)
          -> q ∈ posList c0 c1 -> q ∈ orbitOf c0 c1 (s , rest)
orbitCycle c0 c1 s rest q m =
  subst (λ L -> q ∈ L)
        (sym (orbitN-split c0 c1 s rest (suc (length c1))))
        (memAppR (posList s rest) (orbitN c0 c1 (suc (length c1)) (c0 , c1))
                 (subst (λ L -> q ∈ L) (sym (cycOrbit c0 c1))
                        (memAppL (posList c0 c1) [] m)))

-- A state visited on a stretch is the state of a position on it.

posShift : {s w : Val} {ws : List Val} {z : Val}
        -> Σ[ q ∈ Pos ] q ∈ posList w ws × posState q ≡ z
        -> Σ[ q ∈ Pos ] q ∈ posList s (w ∷ ws) × posState q ≡ z
posShift (q , mq , eq) = q , there mq , eq

posList-mem : (s : Val) (rest : List Val) {z : Val} -> z ∈ s ∷ rest
           -> Σ[ q ∈ Pos ] q ∈ posList s rest × posState q ≡ z
posList-mem s []       here      = (s , []) , here , refl
posList-mem s []       (there ())
posList-mem s (w ∷ ws) here      = (s , w ∷ ws) , here , refl
posList-mem s (w ∷ ws) (there m) = posShift (posList-mem w ws m)

-- Every position of an orbit is reached from its start by iterating.

posBump : {c0 : Val} {c1 : List Val} {pos q : Pos}
       -> Σ[ t ∈ Nat ] posIter c0 c1 t (nextPos c0 c1 pos) ≡ q
       -> Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q
posBump (t , e) = suc t , e

orbitN-iter : (c0 : Val) (c1 : List Val) (n : Nat) (pos q : Pos)
           -> q ∈ orbitN c0 c1 n pos
           -> Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q
orbitN-iter c0 c1 zero    pos q ()
orbitN-iter c0 c1 (suc n) pos q here      = zero , refl
orbitN-iter c0 c1 (suc n) pos q (there m) =
  posBump (orbitN-iter c0 c1 n (nextPos c0 c1 pos) q m)

orbitOf-iter : (c0 : Val) (c1 : List Val) (pos q : Pos)
            -> q ∈ orbitOf c0 c1 pos
            -> Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q
orbitOf-iter c0 c1 (s , rest) q m =
  orbitN-iter c0 c1 (suc (length rest + suc (length c1))) (s , rest) q m

------------------------------------------------------------------------
-- The run, extracted from a lasso.
--
-- The cycle is split once and for all into its head c0 and tail c1, which is
-- what makes nextPos total; the lasso's null qs ≡ false is what licenses
-- the split, and that in turn is what the extra step of roundOf bought.
--
-- The fields of mkRun, as they are named where a Run is taken apart: b, the
-- last state of the cycle; c0, c1, its head and tail; mc0 : c0 ∈ Uinf P; wc,
-- the walk round the cycle; stb, the step from b back to c0; mbc : b is on the
-- cycle; cyc, every eventuality pending on the cycle is fulfilled on it; rest,
-- the stem; mv0 : v0 ∈ Uinf P; and wr, the walk along the stem.

data Run (P : Formula) (v0 : Val) : Set where
  mkRun : (b c0 : Val) (c1 : List Val)
       -> c0 ∈ Uinf P
       -> Walk P (Uinf P) c0 c1 b
       -> step P b c0 ≡ true
       -> b ∈ c0 ∷ c1 -> AllFulfilled P b (c0 ∷ c1) (b ∷ c0 ∷ c1)
       -> (rest : List Val) -> v0 ∈ Uinf P -> Walk P (Uinf P) v0 rest b
       -> Run P v0

runOf : (P : Formula) (v0 : Val) -> v0 ∈ Uinf P -> Lasso P v0 -> Run P v0
runOf P v0 mv0 (mkLasso b mb ps wp []       wq () cyc)
runOf P v0 mv0 (mkLasso b mb ps wp (q ∷ qs) (wcons mq st wqs) nn cyc) =
  mkRun b q qs mq wqs st (walkEnd P (Uinf P) wqs) cyc
        (ps ++ q ∷ qs) mv0
        (walkApp P (Uinf P) wp (wcons mq st wqs))

------------------------------------------------------------------------
-- The orbit, once more, as a plain concatenation.
--
-- Everything below is read off this equation: the orbit of (s , rest) is the
-- rest of the walk followed by one turn of the cycle.

orbitEq : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val)
       -> orbitOf c0 c1 (s , rest) ≡
          posList s rest ++ posList c0 c1
orbitEq c0 c1 s rest =
  trans (orbitN-split c0 c1 s rest (suc (length c1)))
        (cong (λ L -> posList s rest ++ L)
              (trans (cycOrbit c0 c1) (++-identityʳ (posList c0 c1))))

orbitHead : (c0 : Val) (c1 : List Val) (pos : Pos) -> pos ∈ orbitOf c0 c1 pos
orbitHead c0 c1 (s , rest) = here

posList-hd : (s : Val) (rest : List Val) -> (s , rest) ∈ posList s rest
posList-hd s []       = here
posList-hd s (w ∷ ws) = here

------------------------------------------------------------------------
-- The orbit is closed under the successor.
--
-- Walking on stays inside the same stretch until the stretch runs out, and
-- then lands on the head of the cycle, which is in the orbit either way.

posList-next : (c0 : Val) (c1 : List Val) (s : Val) (rest : List Val) (q : Pos)
            -> q ∈ posList s rest
            -> nextPos c0 c1 q ∈ posList s rest ⊎
               nextPos c0 c1 q ≡ (c0 , c1)
posList-next c0 c1 s []       q here      = inr refl
posList-next c0 c1 s []       q (there ())
posList-next c0 c1 s (w ∷ ws) q here      = inl (there (posList-hd w ws))
posList-next c0 c1 s (w ∷ ws) q (there m) =
  sumElim (λ mm -> inl (there mm)) inr (posList-next c0 c1 w ws q m)

orbitClosed : (c0 : Val) (c1 : List Val) (pos q : Pos)
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

posIter-suc : (c0 : Val) (c1 : List Val) (t : Nat) (pos : Pos)
           -> posIter c0 c1 (suc t) pos ≡ nextPos c0 c1 (posIter c0 c1 t pos)
posIter-suc c0 c1 zero    pos = refl
posIter-suc c0 c1 (suc t) pos = posIter-suc c0 c1 t (nextPos c0 c1 pos)

orbitIter : (c0 : Val) (c1 : List Val) (t : Nat) (pos : Pos)
         -> posIter c0 c1 t pos ∈ orbitOf c0 c1 pos
orbitIter c0 c1 zero    pos = orbitHead c0 c1 pos
orbitIter c0 c1 (suc t) pos =
  subst (λ r -> r ∈ orbitOf c0 c1 pos) (sym (posIter-suc c0 c1 t pos))
        (orbitClosed c0 c1 pos (posIter c0 c1 t pos) (orbitIter c0 c1 t pos))

-- so the orbit of a successor is contained in the orbit
orbitSub : (c0 : Val) (c1 : List Val) (pos q : Pos)
        -> q ∈ orbitOf c0 c1 (nextPos c0 c1 pos) -> q ∈ orbitOf c0 c1 pos
orbitSub c0 c1 pos q m = fromIter (orbitOf-iter c0 c1 (nextPos c0 c1 pos) q m)
  where
    fromIter : (Σ[ t ∈ Nat ] posIter c0 c1 t (nextPos c0 c1 pos) ≡ q)
            -> q ∈ orbitOf c0 c1 pos
    fromIter (t , et) =
      subst (λ r -> r ∈ orbitOf c0 c1 pos) et (orbitIter c0 c1 (suc t) pos)

------------------------------------------------------------------------
-- Validity is preserved along the run, hence throughout an orbit

posIterValid : (P : Formula) (b c0 : Val) (c1 : List Val)
            -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
            -> (t : Nat) (pos : Pos) -> ValidPos P b pos
            -> ValidPos P b (posIter c0 c1 t pos)
posIterValid P b c0 c1 mc0 wc stb zero    pos vp = vp
posIterValid P b c0 c1 mc0 wc stb (suc t) pos vp =
  posIterValid P b c0 c1 mc0 wc stb t (nextPos c0 c1 pos)
               (fst (posStep P b c0 c1 mc0 wc stb vp))

orbitValid : (P : Formula) (b c0 : Val) (c1 : List Val)
          -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
          -> (pos q : Pos) -> ValidPos P b pos -> q ∈ orbitOf c0 c1 pos
          -> ValidPos P b q
orbitValid P b c0 c1 mc0 wc stb pos q vp m =
  fromIter (orbitOf-iter c0 c1 pos q m)
  where
    fromIter : (Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q) -> ValidPos P b q
    fromIter (t , et) =
      subst (λ r -> ValidPos P b r) et
            (posIterValid P b c0 c1 mc0 wc stb t pos vp)

-- the state of the run at stage i
stateAt : (P : Formula) (v0 : Val) -> Run P v0 -> Nat -> Val
stateAt P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) i =
  posState (posIter c0 c1 i (v0 , rest))

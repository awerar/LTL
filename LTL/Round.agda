{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Round -- G22 of FORMALISATION-PLAN.md, the round of m4.tex section 5.
--
--   A round from u in U_inf is the finite path in U_inf obtained as follows.
--   Let u_0 := u.  For j = 1,...,m: if the j-th eventuality is pending at
--   u_{j-1}, let u_j be the endpoint of a path in U_inf from u_{j-1} to a state
--   fulfilling it, which exists by Lemma 5.1; otherwise u_j := u_{j-1} by the
--   empty path.  The round ends at u_m.
--
-- The construction is a recursion along the list of eventualities, and the
-- payload is the property Proposition 5.3 will use:
--
--   every eventuality pending at u is fulfilled at some state the round visits.
--
-- Note that this is pending at u = u_0, not at u_{j-1}, which is what the
-- construction tests.  walkPersist bridges the two, exactly as the note does:
-- along the walk built so far, a pending eventuality is either already
-- fulfilled -- and then there is nothing to do -- or still pending at the
-- endpoint, where the next stage of the recursion deals with it.
--
-- One extra step is appended at the end so that a round is never empty.  The
-- note does not need this because it reads the boundary sequence as a path;
-- here the cycle of Proposition 5.3 is assembled out of round walks, and a
-- cycle must contain at least one transition.

module LTL.Round where

open import LTL.Fix public

------------------------------------------------------------------------
-- The body of a round: the eventualities of As dealt with, in order

data RoundB (P : Formula) (As : List Formula) (u : Val) : Set where
  mkRoundB : (ws : List Val) (x : Val)
          -> Walk P (Uinf P) u ws x -> x ∈ Uinf P
          -> ((A : Formula) -> A ∈ As -> valOf P u (□ A) ≡ false
                -> Fulfil P A u ws)
          -> RoundB P As u

nilFul : (P : Formula) (u : Val) (A : Formula)
      -> A ∈ [] {A = Formula} -> valOf P u (□ A) ≡ false -> Fulfil P A u []
nilFul P u A ()

roundBody : (P : Formula) (As : List Formula)
         -> ({A : Formula} -> A ∈ As -> A ∈ □Args (sub P))
         -> (u : Val) -> u ∈ Uinf P -> RoundB P As u
roundBody P []       sbA u mu = mkRoundB [] u wnil mu (nilFul P u)
roundBody P (A ∷ As) sbA u mu = onPend (valOf P u (□ A)) refl
  where
    -- ws1 takes u to x1, and deals with A if A was pending at u; the recursion
    -- then deals with As from x1.
    combine : (ws1 : List Val) (x1 : Val)
           -> Walk P (Uinf P) u ws1 x1 -> x1 ∈ Uinf P
           -> (valOf P u (□ A) ≡ false -> Fulfil P A u ws1)
           -> RoundB P (A ∷ As) u
    combine ws1 x1 wk1 mx1 hA =
      go (roundBody P As (λ m -> sbA (there m)) x1 mx1)
      where
        go : RoundB P As x1 -> RoundB P (A ∷ As) u
        go (mkRoundB ws2 x2 wk2 mx2 h2) =
          mkRoundB (ws1 ++ ws2) x2 (walkApp P (Uinf P) wk1 wk2) mx2 prop
          where
            prop : (B : Formula) -> B ∈ A ∷ As
                -> valOf P u (□ B) ≡ false -> Fulfil P B u (ws1 ++ ws2)
            prop B here      pd = fulfilPrefix ws1 ws2 (hA pd)
            prop B (there m) pd =
              sumElim (λ f   -> fulfilPrefix ws1 ws2 f)
                      (λ pd2 -> fulfilSuffix ws1 ws2 (walkEnd P (Uinf P) wk1) (h2 B m pd2))
                      (walkPersist P (Uinf P) B (□Args-mem (sub P) (sbA (there m)))
                                   wk1 pd)

    onPend : (b : Bool) -> valOf P u (□ A) ≡ b -> RoundB P (A ∷ As) u
    -- not pending at u: the empty path, and the obligation is vacuous
    onPend true  ep =
      combine [] u wnil mu
              (λ pd -> emptyElim (true≢false (trans (sym ep) pd)))
    -- pending at u: Lemma 5.1 supplies a walk to a state fulfilling it
    onPend false ep = fromEsc (uinfFulfil P u mu A (sbA here) ep)
      where
        fromEsc : Escape P (Uinf P) A u -> RoundB P (A ∷ As) u
        fromEsc (esc ws1 x1 wk1 mx1 ex) =
          combine ws1 x1 wk1 mx1 (λ pd -> ful x1 (walkEnd P (Uinf P) wk1) ex)

------------------------------------------------------------------------
-- A round, with the extra step that makes it nonempty

data Round (P : Formula) (u : Val) : Set where
  mkRound : (rs : List Val) (x : Val)
         -> Walk P (Uinf P) u rs x -> x ∈ Uinf P
         -> null rs ≡ false -> FulfilledAt P u rs u
         -> Round P u

roundOf : (P : Formula) (u : Val) -> u ∈ Uinf P -> Round P u
roundOf P u mu = fromBody (roundBody P (□Args (sub P)) (λ m -> m) u mu)
  where
    fromBody : RoundB P (□Args (sub P)) u -> Round P u
    fromBody (mkRoundB ws x wk mx h) = fromSucc (uinfSucc P x mx)
      where
        fromSucc : SuccInUinf P x -> Round P u
        fromSucc (succInUinf y my st) =
          mkRound (ws ++ y ∷ []) y
                  (walkApp P (Uinf P) wk (wcons my st wnil)) my
                  (null-appR ws y [])
                  (λ A mA pd -> fulfilPrefix ws (y ∷ []) (h A mA pd))

------------------------------------------------------------------------
-- The list the note calls the round

roundList : (P : Formula) (u : Val) -> Round P u -> List Val
roundList P u (mkRound rs x wk mx nn h) = rs

round : (P : Formula) (u : Val) -> u ∈ Uinf P -> List Val
round P u mu = roundList P u (roundOf P u mu)

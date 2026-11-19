{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Walk -- finite paths of the transition relation, carrying
-- the list of states they visit:
--
--   Walk P us v ws x   --  v -> ws_1 -> ... -> ws_n = x, every ws_i in us
--
-- Indexing by the endpoint keeps concatenation free of bookkeeping.  (Path of
-- LTL.Elimination.Gfp is the same relation without the list, for proofs that
-- build nothing.)
--
-- The main lemma is walkPersist: along a walk, an eventuality pending at the
-- start is either fulfilled at a state visited, or still pending at the end.

module LTL.Countermodel.Walk where

open import LTL.Elimination.Elim public

------------------------------------------------------------------------
-- Walks

data Walk (P : Formula) (us : List Val) : Val -> List Val -> Val -> Set where
  wnil  : {v : Val} -> Walk P us v [] v
  wcons : {v w : Val} {ws : List Val} {x : Val}
       -> w ∈ us -> step P v w ≡ true
       -> Walk P us w ws x -> Walk P us v (w ∷ ws) x

module _ (P : Formula) where

  walkApp : (us : List Val) {v x y : Val} {ws zs : List Val}
         -> Walk P us v ws x -> Walk P us x zs y -> Walk P us v (ws ++ zs) y
  walkApp us wnil             w2 = w2
  walkApp us (wcons mw st w1) w2 = wcons mw st (walkApp us w1 w2)

  -- The endpoint is one of the states visited.
  walkEnd : (us : List Val) {v : Val} {ws : List Val} {x : Val}
         -> Walk P us v ws x -> x ∈ v ∷ ws
  walkEnd us wnil             = here
  walkEnd us (wcons mw st wk) = there (walkEnd us wk)

------------------------------------------------------------------------
-- Fulfilment along a walk

data Fulfil (P : Formula) (A : Formula) (v : Val) (ws : List Val) : Set where
  ful : (z : Val) -> z ∈ v ∷ ws -> valOf P z A ≡ false -> Fulfil P A v ws

-- A Fulfil proof carries over to a walk with one more state in front.

fulfilCons : {P A : Formula} {v w : Val} {ws : List Val}
          -> Fulfil P A w ws -> Fulfil P A v (w ∷ ws)
fulfilCons (ful z m q) = ful z (there m) q

------------------------------------------------------------------------
-- Persistence along a walk.  If □ A is pending at v then, walking to x,
-- either A fails somewhere on the way (the eventuality is fulfilled) or □ A
-- is still pending at x.  Each step is `persist`, i.e. (T3).

walkPersist : (P : Formula) (us : List Val) (A : Formula) -> □ A ∈ sub P
           -> {v : Val} {ws : List Val} {x : Val} -> Walk P us v ws x
           -> valOf P v (□ A) ≡ false
           -> Fulfil P A v ws ⊎ valOf P x (□ A) ≡ false
walkPersist P us A mb wnil e = inr e
walkPersist P us A mb (wcons {v} {w} {ws} {x} mw st wk) e with valOf P v A in ea
... | false = inl (ful v here ea)
... | true  =
  sumElim (λ f -> inl (fulfilCons f)) inr
          (walkPersist P us A mb wk (persist P v w A mb st e ea))

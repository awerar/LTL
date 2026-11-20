{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Countermodel.Walk -- finite paths of the transition relation, carrying
-- the list of states they visit:
--
--   Walk us v ws x   --  v -> ws_1 -> ... -> ws_n = x, every ws_i in us
--
-- Indexing by the endpoint keeps concatenation free of bookkeeping.
--
-- The main lemma is walkPersist: along a walk, an eventuality pending at the
-- start is either fulfilled at a state visited, or still pending at the end.

open import LTL.Syntax.Formula using (Formula)

module LTL.Countermodel.Walk (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Step P
open import LTL.States.Closure P

------------------------------------------------------------------------
-- Walks

data Walk (us : List Val) : Val -> List Val -> Val -> Set where
  wnil  : {v : Val} -> Walk us v [] v
  wcons : {v w : Val} {ws : List Val} {x : Val}
       -> w ∈ us -> step v w ≡ true
       -> Walk us w ws x -> Walk us v (w ∷ ws) x

walkApp : (us : List Val) {v x y : Val} {ws zs : List Val}
       -> Walk us v ws x -> Walk us x zs y -> Walk us v (ws ++ zs) y
walkApp us wnil             w2 = w2
walkApp us (wcons mw st w1) w2 = wcons mw st (walkApp us w1 w2)

-- The endpoint is one of the states visited.
walkEnd : (us : List Val) {v : Val} {ws : List Val} {x : Val}
       -> Walk us v ws x -> x ∈ v ∷ ws
walkEnd us wnil             = here
walkEnd us (wcons mw st wk) = there (walkEnd us wk)

------------------------------------------------------------------------
-- Fulfilment along a walk

data Fulfil (A : Formula) (v : Val) (ws : List Val) : Set where
  ful : (z : Val) -> z ∈ v ∷ ws -> valOf z A ≡ false -> Fulfil A v ws

-- A Fulfil proof carries over to a walk with one more state in front.

fulfilCons : {A : Formula} {v w : Val} {ws : List Val}
          -> Fulfil A w ws -> Fulfil A v (w ∷ ws)
fulfilCons (ful z m q) = ful z (there m) q

------------------------------------------------------------------------
-- Persistence along a walk.  If □ A is pending at v then, walking to x,
-- either A fails somewhere on the way (the eventuality is fulfilled) or □ A
-- is still pending at x.  Each step is `persist`, i.e. (T3).

walkPersist : (us : List Val) (A : Formula) -> □ A ∈ sub P
           -> {v : Val} {ws : List Val} {x : Val} -> Walk us v ws x
           -> valOf v (□ A) ≡ false
           -> Fulfil A v ws ⊎ valOf x (□ A) ≡ false
walkPersist us A mb wnil e = inr e
walkPersist us A mb (wcons {v} {w} {ws} {x} mw st wk) e with valOf v A in ea
... | false = inl (ful v here ea)
... | true  =
  sumElim (λ f -> inl (fulfilCons f)) inr
          (walkPersist us A mb wk (persist v w A mb st e ea))

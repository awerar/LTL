{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Reach -- G7 of FORMALISATION-PLAN.md.
--
-- Reach_U(v) of m4.tex section 3: the states reachable from v by ->-steps
-- inside U, v included.  It is needed twice: in condition (R2) of
-- Definition 3.1, and to build the loop invariant B = beta_W of Theorem 4.1,
-- where W = Reach_{U_k}(v).
--
-- Computed by fuel-bounded iteration rather than well-founded recursion: each
-- round either adds a state or stabilises, so length us rounds suffice.
--
-- What survives of this module is the SET machinery -- ≡ᵛ, ∈ᵛ, insertV,
-- unionV -- which the rest of the development uses throughout.  reach itself is
-- kept for the computation below, but the elimination procedure does not use
-- it: "length us rounds suffice" is exactly the claim one has to prove to get
-- the closure property of Theorem 4.1 step (ii) out of it, and it is a
-- pigeonhole argument over a duplicate-free accumulator.  LTL.Gfp replaces the
-- reachable set by the largest closed set of unfulfilling states, where closure
-- is free, and shows in gfpSound/gfpComplete that the resulting condition (R2)
-- is the note's, with Reach_U(v) taken in its exact sense rather than
-- approximated from below by a fuel bound.
--
-- It is also where the generic set layer meets valuations.  LTL.Sets and
-- LTL.Bar are stated for any element type, and LTL.Nodes for any node type with
-- an equality test; below,  _≡ᵛ_  is defined, proved sound and reflexive, and
-- LTL.Nodes is instantiated at Val with it.  That instance supplies ∈ᵛ ≢ᵛ, the
-- hypothesis names (Closed, AllSat, ...) and listBar to the whole development,
-- under the names it has always used.  LTL.SccLasso instantiates LTL.Graph with
-- the same three arguments.

module LTL.Reach where

open import LTL.Step public
open import LTL.Bar  public

------------------------------------------------------------------------
-- Valuations as a set

infix 4.5 _≡ᵛ_

_≡ᵛ_ : Val -> Val -> Bool
[]      ≡ᵛ []      = true
[]      ≡ᵛ (c ∷ w) = false
(b ∷ v) ≡ᵛ []      = false
(b ∷ v) ≡ᵛ (c ∷ w) = (b ⇔ᵇ c) ∧ᵇ (v ≡ᵛ w)

≡ᵛ-refl : (v : Val) -> v ≡ᵛ v ≡ true
≡ᵛ-refl []          = refl
≡ᵛ-refl (true  ∷ v) = ≡ᵛ-refl v
≡ᵛ-refl (false ∷ v) = ≡ᵛ-refl v

eqCons : {b c : Bool} {v w : Val} -> b ≡ c -> v ≡ w -> b ∷ v ≡ c ∷ w
eqCons refl refl = refl

≡ᵛ-sound : (v w : Val) -> v ≡ᵛ w ≡ true -> v ≡ w
≡ᵛ-sound []      []      e = refl
≡ᵛ-sound []      (c ∷ w) ()
≡ᵛ-sound (b ∷ v) []      ()
≡ᵛ-sound (b ∷ v) (c ∷ w) e =
  eqCons (⇔ᵇ-sound b c (andTrueL (b ⇔ᵇ c) (v ≡ᵛ w) e))
         (≡ᵛ-sound v w (andTrueR (b ⇔ᵇ c) (v ≡ᵛ w) e))

-- The set layer, at Val.  ∈ᵛ comes from here:  v ∈ᵛ us = any (v ≡ᵛ_) us .

open import LTL.Nodes _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl public

insertV : Val -> List Val -> List Val
insertV v us = filterCons (¬ᵇ (v ∈ᵛ us)) v us

unionV : List Val -> List Val -> List Val
unionV []       ys = ys
unionV (x ∷ xs) ys = insertV x (unionV xs ys)

------------------------------------------------------------------------
-- One round of expansion, then the fuel-bounded closure

reachStep : Formula -> List Val -> List Val -> List Val
reachStep P us acc = unionV (concat (map (succs P us) acc)) acc

reachIter : Formula -> Nat -> List Val -> List Val -> List Val
reachIter P zero    us acc = acc
reachIter P (suc n) us acc = reachIter P n us (reachStep P us acc)

reach : Formula -> List Val -> Val -> List Val
reach P us v = reachIter P (length us) us (v ∷ [])

------------------------------------------------------------------------
-- Reading a successor list

succsMem : (P : Formula) (us : List Val) (v : Val) {w : Val}
        -> w ∈ succs P us v -> w ∈ us × step P v w ≡ true
succsMem P us v m =
  filter_sub (step P v) us m , filter_prop (step P v) us m

succsIn : (P : Formula) (us : List Val) (v : Val) {w : Val}
       -> w ∈ us -> step P v w ≡ true -> w ∈ succs P us v
succsIn P us v mw st = filter_true (step P v) us mw st

------------------------------------------------------------------------
-- Computational checks.
--
-- For ◇ p the three states are sPending = 1010, sFulfil = 1001 and
-- sSink = 0110 (see LTL.Step).  sPending and sFulfil reach everything; sSink
-- reaches only itself.

reach_◇P : map (λ v -> length (reach ◇P (St ◇P) v)) (St ◇P) ≡
                3 ∷ 3 ∷ 1 ∷ []
reach_◇P = refl

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SCC.SccSeed -- every state of Ust is reached from a state containing
-- P (ustSeedTo).
--
-- The graph search covers all of Ust P, so a fair component can lie anywhere
-- in it; this lemma gives the countermodel a start that contains P, with a
-- stem from there to the component.  The proof follows closeGo's recursion: a
-- state a round adds is a seed, or a successor of a state already in.  The
-- trail comes out inside StCand P, and seedTrail lifts it into Ust using
-- ustClosed.

open import LTL.Syntax.Formula using (Formula)

module LTL.SCC.SccSeed (P : Formula) where

open import LTL.States.Common
open import LTL.States.State P
open import LTL.States.Step P
open import LTL.States.Closure P
open import LTL.Countermodel.Walk P

------------------------------------------------------------------------
-- A seed and a trail inside StCand from it.

record Seeded (w : Val) : Set where
  constructor seeded
  field
    seed      : Val
    visited   : List Val
    seedIn    : seed ∈ StCand
    seedHolds : valOf seed P ≡ true
    trail     : Trail StCand seed visited w

-- One round: a state it adds is a seed, or a successor of something already in.

addSeeded : (acc : List Val)
         -> (∀[ z ∈ acc ] Seeded z)
         -> ∀[ z ∈ addAll acc ] Seeded z
addSeeded acc sd z m =
  sumElim fromNew (λ m2 -> sd z m2)
          (memAppCase (filter (missing acc) StCand) acc m)
  where
    fromNew : z ∈ filter (missing acc) StCand -> Seeded z
    fromNew m1 =
      sumElim isSeed viaU
              (∨ᵇ-true (valOf z P) (any (λ u -> step u z) acc) want)
      where
        mzs : z ∈ StCand
        mzs = filter-sub (missing acc) StCand m1

        want : wanted acc z ≡ true
        want = ∧ᵇ-trueˡ (wanted acc z) (¬ᵇ (z ∈ᵛ acc))
                        (filter-prop (missing acc) StCand m1)

        isSeed : valOf z P ≡ true -> Seeded z
        isSeed e = seeded z [] mzs e tNil

        viaU : any (λ u -> step u z) acc ≡ true -> Seeded z
        viaU ea = pick (any-true (λ u -> step u z) acc ea)
          where
            pick : (∃[ u ∈ acc ] step u z ≡ true)
                -> Seeded z
            pick (u , mu , su) =
              seeded seed (visited ++ z ∷ []) seedIn seedHolds
                     (trailApp StCand trail (tCons mzs su tNil))
              where open Seeded (sd u mu)

closeGoSeeded   : {E : Pred} (acc : List Val)
               -> (av : Avail E StCand acc)
               -> (bar : IFin E)
               -> (∀[ z ∈ acc ] Seeded z)
               -> {z : Val} -> z ∈ closeGo acc av bar -> Seeded z
closeFindSeeded : {E : Pred} (acc : List Val)
               -> (av : Avail E StCand acc)
               -> (bar : IFin E) (fr : FindResult (settled acc) StCand)
               -> (∀[ z ∈ acc ] Seeded z)
               -> {z : Val} -> z ∈ closeFind acc av bar fr -> Seeded z

closeGoSeeded acc av bar =
  closeFindSeeded acc av bar (findFalse (settled acc) StCand)

closeFindSeeded acc av bar      (allTrue f)    sd {z} m = sd z m
closeFindSeeded acc av (cBar h) (found x mx q) sd     m =
  closeGoSeeded (addAll acc) _ (h x (av x mx (notInAcc acc x q)))
                (addSeeded acc sd) m

ustSeeded : {z : Val} -> z ∈ Ust -> Seeded z
ustSeeded =
  closeGoSeeded [] (λ z mz e -> stAllSat z (stCandSt mz)) vecBar noSd
  where
    noSd : (z : Val) -> z ∈ [] {A = Val} -> Seeded z
    noSd z ()

-- A trail of states out of Ust stays in Ust P.

seedTrail : {s : Val} {zs : List Val} {w : Val}
         -> s ∈ Ust -> Trail StCand s zs w
         -> Trail Ust s zs w
seedTrail ms tNil                   = tNil
seedTrail ms (tCons {x = y} m e t) = tCons my e (seedTrail my t)
  where
    my : y ∈ Ust
    my = ustClosed ms (stCandSt m) e

record SeedTo (w : Val) : Set where
  constructor seedTo
  field
    seed      : Val
    seedIn    : seed ∈ Ust
    seedHolds : valOf seed P ≡ true
    reaches   : Reaches Ust seed w

ustSeedTo : ∀[ w ∈ Ust ] SeedTo w
ustSeedTo w m =
  seedTo seed mu seedHolds (reachesBy visited (seedTrail mu trail))
  where
    open Seeded (ustSeeded m)

    mu : seed ∈ Ust
    mu = ustSeed (stCandSt seedIn) seedHolds

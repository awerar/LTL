{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SCC.SccSeed -- every state of Ust P is reached from a state containing
-- P (ustSeedTo).
--
-- The graph search covers all of Ust P, so a fair component can lie anywhere
-- in it; this lemma gives the countermodel a start that contains P, with a
-- stem from there to the component.  The proof follows closeGo's recursion: a
-- state a round adds is a seed, or a successor of a state already in.  The
-- trail comes out inside StCand P, and seedTrail lifts it into Ust P using
-- ustClosed.

module LTL.SCC.SccSeed where

open import LTL.SCC.SccExtract public

------------------------------------------------------------------------
-- A seed and a trail inside StCand P from it.

record Seeded (P : Formula) (w : Val) : Set where
  constructor seeded
  field
    seed      : Val
    visited   : List Val
    seedIn    : seed ∈ StCand P
    seedHolds : valOf P seed P ≡ true
    trail     : Trail (StCand P) (step P) seed visited w

-- One round: a state it adds is a seed, or a successor of something already in.

module _ (P : Formula) where

  addSeeded : (acc : List Val)
           -> ((z : Val) -> z ∈ acc -> Seeded P z)
           -> (z : Val) -> z ∈ addAll P acc -> Seeded P z
  addSeeded acc sd z m =
    sumElim fromNew (λ m2 -> sd z m2)
            (memAppCase (filter (missing P acc) (StCand P)) acc m)
    where
      fromNew : z ∈ filter (missing P acc) (StCand P) -> Seeded P z
      fromNew m1 =
        sumElim isSeed viaU
                (∨ᵇ-true (valOf P z P) (any (λ u -> step P u z) acc) want)
        where
          mzs : z ∈ StCand P
          mzs = filter-sub (missing P acc) (StCand P) m1

          want : wanted P acc z ≡ true
          want = ∧ᵇ-trueˡ (wanted P acc z) (¬ᵇ (z ∈ᵛ acc))
                          (filter-prop (missing P acc) (StCand P) m1)

          isSeed : valOf P z P ≡ true -> Seeded P z
          isSeed e = seeded z [] mzs e tNil

          viaU : any (λ u -> step P u z) acc ≡ true -> Seeded P z
          viaU ea = pick (any-true (λ u -> step P u z) acc ea)
            where
              pick : (Σ[ u ∈ Val ] u ∈ acc × step P u z ≡ true)
                  -> Seeded P z
              pick (u , mu , su) = ext (sd u mu)
                where
                  ext : Seeded P u -> Seeded P z
                  ext (seeded s zs ms es t) =
                    seeded s (zs ++ z ∷ []) ms es
                           (trailApp (StCand P) (step P) t (tCons mzs su tNil))

  closeGoSeeded   : {E : Pred} (acc : List Val)
                 -> (av : Avail E (StCand P) acc)
                 -> (bar : IFin E)
                 -> ((z : Val) -> z ∈ acc -> Seeded P z)
                 -> {z : Val} -> z ∈ closeGo P acc av bar -> Seeded P z
  closeFindSeeded : {E : Pred} (acc : List Val)
                 -> (av : Avail E (StCand P) acc)
                 -> (bar : IFin E) (fr : FindResult (settled P acc) (StCand P))
                 -> ((z : Val) -> z ∈ acc -> Seeded P z)
                 -> {z : Val} -> z ∈ closeFind P acc av bar fr -> Seeded P z

  closeGoSeeded acc av bar =
    closeFindSeeded acc av bar (findFalse (settled P acc) (StCand P))

  closeFindSeeded acc av bar      (allTrue f)    sd {z} m = sd z m
  closeFindSeeded acc av (cBar h) (found x mx q) sd     m =
    closeGoSeeded (addAll P acc) _ (h x (av x mx (notInAcc P acc x q)))
                  (addSeeded acc sd) m

  ustSeeded : {z : Val} -> z ∈ Ust P -> Seeded P z
  ustSeeded =
    closeGoSeeded [] (λ z mz e -> stAllSat P z (stCandSt P mz)) (vecBar P) noSd
    where
      noSd : (z : Val) -> z ∈ [] {A = Val} -> Seeded P z
      noSd z ()

  -- A trail of states out of Ust P stays in Ust P.

  seedTrail : {s : Val} {zs : List Val} {w : Val}
           -> s ∈ Ust P -> Trail (StCand P) (step P) s zs w
           -> Trail (Ust P) (step P) s zs w
  seedTrail ms tNil                   = tNil
  seedTrail ms (tCons {x = y} m e t) = tCons my e (seedTrail my t)
    where
      my : y ∈ Ust P
      my = ustClosed P ms (stCandSt P m) e

record SeedTo (P : Formula) (w : Val) : Set where
  constructor seedTo
  field
    seed      : Val
    seedIn    : seed ∈ Ust P
    seedHolds : valOf P seed P ≡ true
    reaches   : Reaches (Ust P) (step P) seed w

ustSeedTo : (P : Formula) (w : Val) -> w ∈ Ust P -> SeedTo P w
ustSeedTo P w m = conv (ustSeeded P m)
  where
    conv : Seeded P w -> SeedTo P w
    conv (seeded s zs ms es t) =
      seedTo s mu es (reachesBy zs (seedTrail P mu t))
      where
        mu : s ∈ Ust P
        mu = ustSeed P (stCandSt P ms) es

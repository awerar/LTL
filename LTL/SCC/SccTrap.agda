{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.SCC.SccTrap -- two lemmas that connect the graph search on Ust P to the
-- rest of the development.
--
-- 1. Every state of Ust P is reached from a state containing P (ustSeedTo).
--    So a fair component anywhere in Ust P is reachable from a state that
--    contains P, and the countermodel can start there.  The proof follows
--    closeGo's recursion: a state a round adds is a seed, or a successor of a
--    state already in.  The trail comes out inside StCand P, and seedTrail
--    lifts it into Ust P using ustClosed.
--
-- 2. A trap survives the elimination (uinfTrap).  A Trap is a set in which
--    every state has a successor and every pending eventuality fails
--    somewhere reachable: (R1) and (R2) fail on it.  trapKeep shows one round
--    keeps a trap, and elimGoTrap runs that along elimGo, so  C subset Ust P
--    gives  C subset Uinf P .  This is the inclusion sccLasso needs.

module LTL.SCC.SccTrap where

open import LTL.SCC.SccExtract public

------------------------------------------------------------------------
-- Two list facts, in the shape the two lemmas want.

mem-notNull : {A : Set} (xs : List A) {x : A} -> x ∈ xs -> null xs ≡ false
mem-notNull []       ()
mem-notNull (y ∷ ys) m = refl

any-none : {A : Set} (p : A -> Bool) (xs : List A)
        -> ((y : A) -> y ∈ xs -> p y ≡ false) -> any p xs ≡ false
any-none p []       h = refl
any-none p (y ∷ ys) h =
  subst (λ b -> b ∨ᵇ any p ys ≡ false) (sym (h y here))
        (any-none p ys (λ z m -> h z (there m)))

------------------------------------------------------------------------
-- 1. Every state of Ust P is reached from a state containing P.  The trail
-- lies inside StCand P; seedTrail lifts it into Ust P.

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

------------------------------------------------------------------------
-- 2. Traps: every state has a successor inside C, and every eventuality
-- pending at a state of C fails somewhere reachable inside C.

record Trap (P : Formula) (C : List Val) : Set where
  constructor mkTrap
  field
    -- not (R1): every state of C has a successor inside C
    succInside : (z : Val) -> z ∈ C
              -> Σ[ y ∈ Val ] y ∈ C × step P z y ≡ true
    -- not (R2): an eventuality pending in C fails somewhere reachable in C
    failInside : (z : Val) -> z ∈ C -> (A : Formula) -> A ∈ □Args (sub P)
              -> valOf P z (□ A) ≡ false
              -> Σ[ y ∈ Val ] Path P C z y × valOf P y A ≡ false

module _ (P : Formula) where

  pathMono : (C us : List Val)
          -> C ⊆ us
          -> {v w : Val} -> Path P C v w -> Path P us v w
  pathMono C us sb pnil                   = pnil
  pathMono C us sb (pcons {w = y} m e p) = pcons (sb y m) e (pathMono C us sb p)

  -- One round keeps a trap.  (R1) fails because the successor is in C, hence
  -- in us; (R2) fails because gfpSound would make the eventuality hold along
  -- the trap's own path to a state where it fails.

  trapKeep : (us C : List Val) -> Trap P C
          -> C ⊆ us
          -> (z : Val) -> z ∈ C -> keep P us (evList P us) z ≡ true
  trapKeep us C (mkTrap hsucc hful) sb z mz =
    cong ¬ᵇ_ (∨ᵇ-false-intro (r1 P us z) (r2 P (evList P us) z) e1 e2)
    where
      e1 : r1 P us z ≡ false
      e1 = onS (hsucc z mz)
        where
          onS : (Σ[ y ∈ Val ] y ∈ C × step P z y ≡ true)
             -> null (succs P us z) ≡ false
          onS (y , my , st) =
            mem-notNull (succs P us z) (succsIn P us z (sb y my) st)

      e2 : r2 P (evList P us) z ≡ false
      e2 = any-none (badEv P z) (evList P us) each
        where
          each : (g : Ev) -> g ∈ evList P us -> badEv P z g ≡ false
          each (A , W) mg = byPend
            where
              pr : A ∈ □Args (sub P) × W ≡ gfpW P us A
              pr = evList-of P us mg

              notInW : valOf P z (□ A) ≡ false -> z ∈ᵛ W ≡ false
              notInW ep = refuteTrue (z ∈ᵛ W) λ em ->
                clash (subst (λ L -> z ∈ L) (snd pr) (∈ᵛ-sound z W em))
                      (hful z mz A (fst pr) ep)
                where
                  clash : z ∈ gfpW P us A
                       -> (Σ[ y ∈ Val ] Path P C z y × valOf P y A ≡ false)
                       -> Empty
                  clash mzW (y , pa , ef) =
                    true≢false (trans (sym (gfpSound P us A z mzW y
                                                     (pathMono C us sb pa)))
                                      ef)

              -- badEv is  pending P z A ∧ᵇ z ∈ᵛ W , so it is false at once
              -- unless □ A is pending at z, and then z ∉ W is the point
              byPend : badEv P z (A , W) ≡ false
              byPend with valOf P z (□ A) in ep
              ... | true  = refl
              ... | false = notInW ep

  -- and therefore the whole elimination keeps it: elimGo's recursion with one
  -- invariant added.

  elimGoTrap   : {E : Pred} (us : List Val)
                 (sb : AllSat E us) (bar : IFin E)
              -> (C : List Val) -> Trap P C -> C ⊆ us
              -> (z : Val) -> z ∈ C -> z ∈ elimGo P us sb bar
  elimFindTrap : {E : Pred} (us : List Val)
                 (sb : AllSat E us) (bar : IFin E)
                 (fr : FindResult (keep P us (evList P us)) us)
              -> (C : List Val) -> Trap P C -> C ⊆ us
              -> (z : Val) -> z ∈ C -> z ∈ elimFind P us sb bar fr

  elimGoTrap us sb bar =
    elimFindTrap us sb bar (findFalse (keep P us (evList P us)) us)

  elimFindTrap us sb bar      (allTrue f)   C tr inc z mz = inc z mz
  elimFindTrap us sb (cBar h) (found x m q) C tr inc z mz =
    elimGoTrap (elimRound P us)
               (dropAllSat (keep P us (evList P us)) us sb x q) (h x (sb x m))
               C tr inc' z mz
    where
      inc' : (y : Val) -> y ∈ C -> y ∈ elimRound P us
      inc' y my = filter-true (keep P us (evList P us)) us (inc y my)
                              (trapKeep us C tr inc y my)

  uinfTrap : (C : List Val) -> Trap P C
          -> C ⊆ Ust P
          -> (z : Val) -> z ∈ C -> z ∈ Uinf P
  uinfTrap = elimGoTrap (Ust P) (ustAllSat P) (ustBar P)

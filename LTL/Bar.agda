{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Bar -- inductively finite sets, after Coquand and Siles, "A Decision
-- Procedure for Regular Expression Equivalence in Type Theory" (CPP 2011), §1.
--
--   Bar R E   holds when, starting from E and repeatedly picking an x and
--             passing to  E intersect (R x) , one always stops.
--
-- With R the complement of equality this says: one cannot go on choosing
-- DISTINCT elements of E forever.  That is exactly the principle the
-- development used to re-derive by hand, once per use, as a decreasing length.
-- Phase 8 (G29) replaces all of those by recursion on a Bar: shrinkGo
-- (LTL.Gfp), elimGo (LTL.Elim), lassoSearch (LTL.Lasso), and then closeGo
-- (LTL.Closure), which is G30 and which no length would have justified at all.
--
-- Subsets are taken DECIDABLE, as boolean predicates, rather than as
-- Prop-valued ones.  Everything this development quantifies over is decidable,
-- and it keeps Bar in Set rather than Set1.
--
-- Two suppliers of Bars are provided and they are used for different things.
--
--   barOfList / listBar -- a Kuratowski finite list gives a Bar.  Right when
--     the search removes from a list that is already in hand and whose length
--     one is willing to pay for once: W_0 in LTL.Gfp, U_inf in LTL.Lasso.
--
--   vecIFin / guardedVecBar -- the vectors of a given length are inductively
--     finite, by induction on the length, in O(n) rather than 2^n.  Right when
--     there is no such list: the elimination, which is not to force
--     length (Ust P) merely to bound itself, and above all the closure of
--     LTL.Closure, which GROWS and so has no decreasing measure at all.
--
-- The second is the useful direction and the hard one: the paper notes that the
-- product lemma is essentially the proof that a product of well-quasi-orderings
-- is one.

module LTL.Bar where

open import LTL.Sets public

------------------------------------------------------------------------
-- Bar

data Bar {A : Set} (R : A -> A -> Bool) : (A -> Bool) -> Set where
  cBar : {E : A -> Bool}
      -> ((x : A) -> E x ≡ true
            -> Bar R (λ y -> E y ∧ᵇ R x y))
      -> Bar R E

-- The recursion principle.  Every "keep going until you run out" argument in
-- the development is this with a different C.
barRec : {A : Set} {R : A -> A -> Bool} (C : (A -> Bool) -> Set)
      -> ({E : A -> Bool}
            -> ((x : A) -> E x ≡ true -> C (λ y -> E y ∧ᵇ R x y))
            -> C E)
      -> {E : A -> Bool} -> Bar R E -> C E
barRec C f (cBar h) = f (λ x ex -> barRec C f (h x ex))

barStep : {A : Set} (R : A -> A -> Bool) (E F : A -> Bool)
       -> ((x : A) -> E x ≡ true -> F x ≡ true)
       -> (x y : A) -> E y ∧ᵇ R x y ≡ true
       -> F y ∧ᵇ R x y ≡ true
barStep R E F sb x y e =
  andIntro (F y) (R x y) (sb y (andTrueL (E y) (R x y) e))
                         (andTrueR (E y) (R x y) e)

barMono : {A : Set} {R : A -> A -> Bool} {E F : A -> Bool}
       -> ((x : A) -> E x ≡ true -> F x ≡ true)
       -> Bar R F -> Bar R E
barMono {R = R} {E = E} {F = F} sb (cBar h) =
  cBar (λ x ex -> barMono (barStep R E F sb x) (h x (sb x ex)))

------------------------------------------------------------------------
-- Inductive finiteness for valuations

infix 4.5 _≢ᵛ_

_≢ᵛ_ : Val -> Val -> Bool
x ≢ᵛ y = ¬ᵇ (x ≡ᵛ y)

≢ᵛ-self : (x : Val) -> x ≢ᵛ x ≡ false
≢ᵛ-self x = cong ¬ᵇ_ (≡ᵛ-refl x)

-- IFin E: E is inductively finite.  One cannot keep choosing pairwise distinct
-- vectors that satisfy E forever, so a search that always picks a new one
-- stops.

IFin : (Val -> Bool) -> Set
IFin E = Bar _≢ᵛ_ E

------------------------------------------------------------------------
-- Kuratowski implies inductively finite.
--
-- The ≤ measure of the development survives here and nowhere else: it is paid
-- once, when the Bar is built, and no search counts anything afterwards.

barOfList : {E : Pred} (n : Nat) (xs : List Val) -> length xs ≤ n
         -> ((x : Val) -> E x ≡ true -> x ∈ xs) -> IFin E
barOfList         zero    xs le sb =
  cBar (λ x ex -> emptyElim (leZeroNil xs le (sb x ex)))
barOfList {E = E} (suc n) xs le sb =
  cBar (λ x ex -> barOfList n (filter (x ≢ᵛ_) xs)
                    (lePred (leTrans (filter_lt (x ≢ᵛ_) xs (sb x ex)
                                                (≢ᵛ-self x)) le))
                    (λ z ez -> filter_true (x ≢ᵛ_) xs
                                 (sb z (andTrueL (E z) (x ≢ᵛ z) ez))
                                 (andTrueR (E z) (x ≢ᵛ z) ez)))

------------------------------------------------------------------------
-- Boolean glue for the two closure lemmas

∧∨-distrib : (g h t : Bool) -> (g ∨ᵇ h) ∧ᵇ t ≡ true
          -> g ∧ᵇ t ∨ᵇ h ∧ᵇ t ≡ true
∧∨-distrib true  h true  e = refl
∧∨-distrib true  h false ()
∧∨-distrib false h t     e = e

∧∨-weaken : (g h t : Bool) -> (g ∨ᵇ h) ∧ᵇ t ≡ true
         -> g ∨ᵇ h ∧ᵇ t ≡ true
∧∨-weaken true  h t e = refl
∧∨-weaken false h t e = e

∧∨-split : (e f r s : Bool)
        -> (e ∧ᵇ f) ∧ᵇ (r ∨ᵇ s) ≡ true
        -> (e ∧ᵇ r) ∧ᵇ f ∨ᵇ e ∧ᵇ f ∧ᵇ s ≡ true
∧∨-split true  true  true  s h = refl
∧∨-split true  true  false s h = h
∧∨-split true  false r     s ()
∧∨-split false f     r     s ()

------------------------------------------------------------------------
-- Union.  Lemma 1, second bullet.
--
-- Double induction: on the first witness for the G-case, on the second for
-- the H-case.  barMono does the work that would otherwise need funext, since
-- Bar is indexed by the predicate and the two sides are only pointwise equal.

barUnion : {A : Set} {T : A -> A -> Bool} {G H : A -> Bool}
        -> Bar T G -> Bar T H -> Bar T (λ y -> G y ∨ᵇ H y)
barUnion {A} {T} {G} {H} (cBar hg) bh = inner H bh
  where
    inner : (H' : A -> Bool) -> Bar T H' -> Bar T (λ y -> G y ∨ᵇ H' y)
    inner H' (cBar hh) = cBar pick
      where
        pick : (x : A) -> G x ∨ᵇ H' x ≡ true
            -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
        pick x ex = sumElim fromG fromH (orTrue (G x) (H' x) ex)
          where
            fromG : G x ≡ true
                 -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
            fromG eg =
              barMono (λ y ey -> ∧∨-distrib (G y) (H' y) (T x y) ey)
                      (barUnion (hg x eg)
                                (barMono (λ y ey -> andTrueL (H' y) (T x y) ey)
                                         (cBar hh)))

            fromH : H' x ≡ true
                 -> Bar T (λ y -> (G y ∨ᵇ H' y) ∧ᵇ T x y)
            fromH eh =
              barMono (λ y ey -> ∧∨-weaken (G y) (H' y) (T x y) ey)
                      (inner (λ y -> H' y ∧ᵇ T x y) (hh x eh))

------------------------------------------------------------------------
-- Product.  Lemma 1, fourth bullet -- the load-bearing one.

prodPred : {A B : Set} -> (A -> Bool) -> (B -> Bool) -> A × B -> Bool
prodPred E F (x , y) = E x ∧ᵇ F y

prodRel : {A B : Set} -> (A -> A -> Bool) -> (B -> B -> Bool)
       -> A × B -> A × B -> Bool
prodRel R S (x , y) (u , v) = R x u ∨ᵇ S y v

prodMono : {A B : Set} (R : A -> A -> Bool) (S : B -> B -> Bool)
           (E : A -> Bool) (F : B -> Bool) (x : A) (y : B) (q : A × B)
        -> prodPred E F q ∧ᵇ prodRel R S (x , y) q ≡ true
        -> prodPred (λ a -> E a ∧ᵇ R x a) F q ∨ᵇ
           prodPred E (λ b -> F b ∧ᵇ S y b) q ≡ true
prodMono R S E F x y (u , v) e = ∧∨-split (E u) (F v) (R x u) (S y v) e

barProd : {A B : Set} {R : A -> A -> Bool} {S : B -> B -> Bool}
       -> {E : A -> Bool} {F : B -> Bool}
       -> Bar R E -> Bar S F -> Bar (prodRel R S) (prodPred E F)
barProd {A} {B} {R} {S} {E} {F} (cBar he) bf = inner F bf
  where
    inner : (F' : B -> Bool) -> Bar S F'
         -> Bar (prodRel R S) (prodPred E F')
    inner F' (cBar hf) = cBar pick
      where
        pick : (p : A × B) -> prodPred E F' p ≡ true
            -> Bar (prodRel R S)
                   (λ q -> prodPred E F' q ∧ᵇ prodRel R S p q)
        pick (x , y) ep =
          barMono (prodMono R S E F' x y)
                  (barUnion (barProd (he x (andTrueL (E x) (F' y) ep)) (cBar hf))
                            (inner (λ b -> F' b ∧ᵇ S y b)
                                   (hf y (andTrueR (E x) (F' y) ep))))

------------------------------------------------------------------------
-- Pulling back along a map that reflects the relation on a domain D

barPull : {A B : Set} {R : A -> A -> Bool} {S : B -> B -> Bool}
       -> (f : B -> A) (D : B -> Bool)
       -> ((y z : B) -> D y ≡ true -> D z ≡ true -> S y z ≡ true
             -> R (f y) (f z) ≡ true)
       -> {E : A -> Bool} -> Bar R E
       -> Bar S (λ y -> D y ∧ᵇ E (f y))
barPull {A} {B} {R} {S} f D h {E} (cBar hE) = cBar pick
  where
    pick : (y : B) -> D y ∧ᵇ E (f y) ≡ true
        -> Bar S (λ z -> (D z ∧ᵇ E (f z)) ∧ᵇ S y z)
    pick y ey =
      barMono keep (barPull f D h (hE (f y) (andTrueR (D y) (E (f y)) ey)))
      where
        keep : (z : B) -> (D z ∧ᵇ E (f z)) ∧ᵇ S y z ≡ true
            -> D z ∧ᵇ E (f z) ∧ᵇ R (f y) (f z) ≡ true
        keep z ez =
          andIntro (D z) (E (f z) ∧ᵇ R (f y) (f z))
                   (andTrueL (D z) (E (f z))
                             (andTrueL (D z ∧ᵇ E (f z)) (S y z) ez))
                   (andIntro (E (f z)) (R (f y) (f z))
                             (andTrueR (D z) (E (f z))
                                       (andTrueL (D z ∧ᵇ E (f z)) (S y z) ez))
                             (h y z (andTrueL (D y) (E (f y)) ey)
                                    (andTrueL (D z) (E (f z))
                                              (andTrueL (D z ∧ᵇ E (f z))
                                                        (S y z) ez))
                                    (andTrueR (D z ∧ᵇ E (f z)) (S y z) ez)))

------------------------------------------------------------------------
-- Bool is inductively finite

infix 4.5 _≢ᵇ_

_≢ᵇ_ : Bool -> Bool -> Bool
a ≢ᵇ b = ¬ᵇ (a ⇔ᵇ b)

noThreeDistinct : (x y z : Bool) -> x ≢ᵇ y ≡ true -> x ≢ᵇ z ≡ true
               -> y ≢ᵇ z ≡ true -> Empty
noThreeDistinct true  true  z     () e2 e3
noThreeDistinct true  false true  e1 () e3
noThreeDistinct true  false false e1 e2 ()
noThreeDistinct false false z     () e2 e3
noThreeDistinct false true  false e1 () e3
noThreeDistinct false true  true  e1 e2 ()

boolIFin : Bar _≢ᵇ_ (λ b -> true)
boolIFin =
  cBar (λ x ex ->
  cBar (λ y ey ->
  cBar (λ z ez ->
    emptyElim (noThreeDistinct x y z ey
                 (andTrueL (x ≢ᵇ z) (y ≢ᵇ z) ez)
                 (andTrueR (x ≢ᵇ z) (y ≢ᵇ z) ez)))))

------------------------------------------------------------------------
-- Vectors of a given length are inductively finite -- in O(n), not 2^n.
--
-- This is the point of the file.  A valuation of length n+1 is a Bool paired
-- with a valuation of length n, so barProd applies, and barPull transports the
-- result back along uncons.  The recursion is on n; allVecs never appears.

-- v has length n, as a boolean predicate (so that it can be a Bar's E).

hasLength : Nat -> Val -> Bool
hasLength n v = length v ≡ⁿ n

headV : Val -> Bool
headV []      = false
headV (b ∷ v) = b

tailV : Val -> Val
tailV []      = []
tailV (b ∷ v) = v

unconsV : Val -> Bool × Val
unconsV v = headV v , tailV v

lenZero : (v : Val) -> length v ≡ⁿ zero ≡ true -> v ≡ []
lenZero []      e = refl
lenZero (b ∷ v) ()

lenTail : (m : Nat) (v : Val) -> hasLength (suc m) v ≡ true
       -> hasLength m (tailV v) ≡ true
lenTail m []      ()
lenTail m (b ∷ v) e = e

deMorgan : (a b : Bool) -> ¬ᵇ (a ∧ᵇ b) ≡ true
        -> ¬ᵇ a ∨ᵇ ¬ᵇ b ≡ true
deMorgan true  true  ()
deMorgan true  false e = refl
deMorgan false b     e = refl

unconsNeq : (m : Nat) (y z : Val) -> hasLength (suc m) y ≡ true
         -> hasLength (suc m) z ≡ true -> y ≢ᵛ z ≡ true
         -> prodRel _≢ᵇ_ _≢ᵛ_ (unconsV y) (unconsV z) ≡ true
unconsNeq m []      z       () ez e
unconsNeq m (b ∷ v) []      ey () e
unconsNeq m (b ∷ v) (c ∷ w) ey ez e = deMorgan (b ⇔ᵇ c) (v ≡ᵛ w) e

vecIFin : (n : Nat) -> IFin (hasLength n)
vecIFin zero =
  cBar (λ x ex -> cBar (λ y ey ->
    emptyElim (clash x y ex (andTrueL (hasLength zero y) (x ≢ᵛ y) ey)
                            (andTrueR (hasLength zero y) (x ≢ᵛ y) ey))))
  where
    clash : (x y : Val) -> hasLength zero x ≡ true -> hasLength zero y ≡ true
         -> x ≢ᵛ y ≡ true -> Empty
    clash x y ex ey e = true≢false (sym nil2)
      where
        -- both are [], and [] ≢ᵛ [] is false
        nil2 : [] ≢ᵛ [] ≡ true
        nil2 = subst (λ u -> u ≢ᵛ [] ≡ true) (lenZero x ex)
                     (subst (λ u -> x ≢ᵛ u ≡ true) (lenZero y ey) e)
vecIFin (suc m) =
  barMono (λ v ev -> andIntro (hasLength (suc m) v)
                              (prodPred (λ b -> true) (hasLength m) (unconsV v))
                              ev (lenTail m v ev))
          (barPull unconsV (hasLength (suc m)) (unconsNeq m)
                   (barProd boolIFin (vecIFin m)))


------------------------------------------------------------------------
-- The invariant the removing searches carry.
--
-- AllSat E xs says the list xs lies inside the predicate E.  A search that
-- removes an element x from xs passes to E intersect (R x), and that is
-- precisely the sub-Bar cBar hands over -- so the "pool" of section 4c of
-- FORMALISATION-PLAN.md is no longer a list carried alongside the search: it
-- is the Bar's own predicate.

-- Naming convention for the searches built on this (Closure, Gfp, Elim, Fix,
-- Graph, SccTrap):
--   sb    a subset proof: AllSat E xs, or xs ⊆ ys;
--   bar   the IFin E the search recurses on;
--   av    the "available" invariant of a growing search, Avail E ws acc:
--         every candidate in ws not yet in the accumulator acc still
--         satisfies the Bar's predicate E.
-- A search comes as a pair fooGo / fooFind: fooGo runs findFalse for one
-- round, and fooFind cases on its FindResult -- allTrue stops, found x
-- recurses on the smaller Bar that cBar hands over.

AllSat : Pred -> List Val -> Set
AllSat E xs = (x : Val) -> x ∈ xs -> E x ≡ true

Avail : Pred -> List Val -> List Val -> Set
Avail E ws acc = (z : Val) -> z ∈ ws -> z ∈ᵛ acc ≡ false -> E z ≡ true

memAllSat : (xs : List Val) -> AllSat (λ v -> v ∈ᵛ xs) xs
memAllSat xs x m = ∈ᵛ-complete x xs m

listBar : (xs : List Val) -> IFin (λ v -> v ∈ᵛ xs)
listBar xs = barOfList (length xs) xs (leRefl (length xs))
                       (λ x ex -> ∈ᵛ-sound x xs ex)

-- Dropping x from the list is dropping x from the predicate.  Both searches of
-- G29 that remove a member of the list they are searching use this.

dropAllSat : {E : Pred} (p : Pred) (xs : List Val) -> AllSat E xs
          -> (x : Val) -> p x ≡ false
          -> AllSat (λ y -> E y ∧ᵇ (x ≢ᵛ y)) (filter p xs)
dropAllSat {E} p xs sb x q z mz =
  andIntro (E z) (x ≢ᵛ z)
           (sb z (filter_sub p xs mz))
           (cong ¬ᵇ_ (onEq (x ≡ᵛ z) refl))
  where
    onEq : (b : Bool) -> x ≡ᵛ z ≡ b -> x ≡ᵛ z ≡ false
    onEq false e = e
    onEq true  e =
      emptyElim (true≢false (trans (sym (subst (λ u -> p u ≡ true)
                                               (sym (≡ᵛ-sound x z e))
                                               (filter_prop p xs mz)))
                                   q))

------------------------------------------------------------------------
-- Members of allVecs n have length n.
--
-- Needed to hand guardedVecBar the states: St P is a subset of allVecs
-- (length (sub P)), so the length-n predicate is a correct E for it, and then
-- the search never touches the enumeration.

map_mem_inv : {A B : Set} (f : A -> B) (xs : List A) {y : B}
           -> y ∈ map f xs -> Σ[ x ∈ A ] x ∈ xs × y ≡ f x
map_mem_inv f []       ()
map_mem_inv f (x ∷ xs) here      = x , here , refl
map_mem_inv f (x ∷ xs) (there m) = shift (map_mem_inv f xs m)
  where
    shift : (Σ[ z ∈ _ ] z ∈ xs × _) -> Σ[ z ∈ _ ] z ∈ x ∷ xs × _
    shift (z , mz , ez) = z , there mz , ez

allVecs_len : (n : Nat) {v : Val} -> v ∈ allVecs n -> hasLength n v ≡ true
allVecs_len zero    here      = refl
allVecs_len zero    (there ())
allVecs_len (suc n) m =
  sumElim (fromHalf true) (fromHalf false)
          (memAppCase (map (λ bs -> true  ∷ bs) (allVecs n))
                      (map (λ bs -> false ∷ bs) (allVecs n)) m)
  where
    fromHalf : {v : Val} (b : Bool) -> v ∈ map (λ bs -> b ∷ bs) (allVecs n)
            -> hasLength (suc n) v ≡ true
    fromHalf {v} b mv = fromSig (map_mem_inv (λ bs -> b ∷ bs) (allVecs n) mv)
      where
        fromSig : (Σ[ w ∈ Val ] w ∈ allVecs n × v ≡ b ∷ w)
               -> hasLength (suc n) v ≡ true
        fromSig (w , mw , ew) =
          subst (λ u -> hasLength (suc n) u ≡ true) (sym ew) (allVecs_len n mw)

stAllSat : (P : Formula) -> AllSat (hasLength (length (sub P))) (St P)
stAllSat P x m =
  allVecs_len (length (sub P))
              (filter_sub (isState P) (allVecs (length (sub P))) m)

------------------------------------------------------------------------
-- The guard of Barras, refined by Gonthier (siles.pdf, section 5).
--
-- The paper's point is that one computes with the decision procedure DIRECTLY,
-- as a type-theoretic boolean function, without extracting to ML.  It also
-- records the price: a function defined by recursion on a well-foundedness
-- proof forces that proof as it runs, "and this computation is heavy, and
-- furthermore seems irrelevant, since the accessibility predicate has only one
-- constructor".
--
-- Their fix transfers, and the reason it transfers is worth stating.  Barras's
-- guard works on `well_founded`, a Pi-type, so a guarded proof can produce a
-- constructor without ever applying the proof it wraps.  Bar R E at a FIXED E
-- is a tree, not a function, and admits no such trick -- but vecIFin gives the
-- Pi-form we need, since every subset of the length-n vectors is Bar by
-- barMono.  guardBar k then supplies 2^k constructors lazily, so a search of
-- depth below 2^k never touches vecIFin at all.

AllBar : Nat -> Set
AllBar n = (E : Pred)
        -> ((v : Val) -> E v ≡ true -> hasLength n v ≡ true) -> IFin E

allVecBar : (n : Nat) -> AllBar n
allVecBar n E sb = barMono sb (vecIFin n)

guardBar : (n k : Nat) -> AllBar n -> AllBar n
guardBar n zero    w = w
guardBar n (suc k) w =
  λ E sb -> cBar (λ x ex ->
    guardBar n k (guardBar n k w)
             (λ y -> E y ∧ᵇ (x ≢ᵛ y))
             (λ v ev -> sb v (andTrueL (E v) (x ≢ᵛ v) ev)))

-- The guard depth is n itself, and that is not a cosmetic choice.
--
-- Two things fix it.  A search that keeps choosing DISTINCT vectors of length n
-- runs for at most 2^n steps, and guardBar n k supplies 2^k constructors, so
-- k = n is exactly enough: for |Sub P| = 13 the guard alone carries 8192 peels
-- and vecIFin is never reached.
--
-- More importantly, a literal depth is unusable.  guardBar n k unfolds to 2^k
-- copies of what it wraps, so with k a literal the NORMAL FORM of the guarded
-- Bar has 2^k nodes -- and Agda normalises the constructor types of a data
-- declaration, so every data type whose constructors mention U_infinity
-- (SuccInUinf, Escape, Walk, Round, Lasso, Run, ValidPos: most of Phases 5 and
-- 6) would normalise it.  With k = n and P a variable the match on k is
-- blocked, the guard stays folded, and the explosion cannot happen; on a closed
-- formula n reduces and the guard does its job.  Laziness has to be arranged
-- in the term, not merely relied on in the evaluator.

guardedVecBar : (n : Nat) -> AllBar n
guardedVecBar n = guardBar n n (allVecBar n)

{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Pretty -- the answers of the decision procedures, as text one can read.
--
-- A derivation is a finite tree and a countermodel is a finite lasso, so both
-- can be written down.  LTL.Proofs does that with the datatypes DTree / RTree,
-- and C-c C-n then prints the TERM: every constructor fully qualified, every
-- abbreviation of LTL.Formula unfolded (A ∧ B appears as ¬ (A ⇒ ¬ B)), and
-- the tree laid out as nested applications.  That is right for checking a
-- shape by refl and useless for reading a proof.
--
-- This module renders to a String instead, in the two forms a proof is read
-- in on paper:
--
--   renderDeriv d    the Hilbert-style proof of m4.tex §1: numbered lines,
--                    each an axiom instance or obtained by (MP) / (Gen) from
--                    earlier lines cited by number.  A formula already proved
--                    is cited again rather than proved twice, so subproofs
--                    that the tree repeats appear once.
--   renderTree n d   the derivation tree, indented, to depth n.
--   renderCM Q c     the lasso countermodel: the variables true at each time
--                    point of the prefix and of the loop (m4 §5, Prop 5.3).
--
-- and the entry points
--
--   prove Q          renders decidePC Q (LTL.ShortPC), whose certificates
--                    are short.  proveWith decide Q renders decide's
--                    certificate instead, but that is not practical: it is
--                    82357 constructors already for p ⇒ p (LTL.Proofs), and
--                    rendering it did not finish in six minutes.
--   proveLines Q     prove Q as one String per line, for editors that only
--                    offer plain C-c C-n (see below).
--   proveTree n Q    the tree view of decidePC Q.
--
-- Formulas are printed with the fixities of LTL.Formula and minimal
-- parentheses.  Of the abbreviations, ∧, ⇔ and ◇ are put back: their unfolded
-- shapes ¬ (A ⇒ ¬ B) and ¬ □ ¬ A are rarely meant literally.  ∨, ⊤ and ⊥ are
-- NOT: ¬ A ⇒ B is the antecedent of (P3) and p ⇒ p is the identity theorem,
-- and printing them as B ∨ ¬ A or ⊤ would hide what is being proved.
-- showFormulaRaw prints with no abbreviations at all.  Variables are p q r s t,
-- then x5, x6, ...  The output uses the same spacing as Agda source, so a
-- printed formula can be pasted back into a file.
--
-- How to look at the output.  A String shown by C-c C-n is a quoted literal
-- with \n escapes.  C-u C-u C-c C-n (Agda's "use show instance" mode) instead
-- evaluates  show (expr)  and prints the resulting string raw, with real line
-- breaks; show below is the identity on String, which is all that mode needs.
-- So, with this module (or LTL.Proofs) loaded:
--
--   C-u C-u C-c C-n   prove (□ pv ⇒ pv)
--
-- tools/show-proof does the same from a terminal.  An editor mode that talks
-- to Agda over --interaction-json gets the string back quoted either way; for
-- those, plain C-c C-n on  proveLines Q  shows one quoted line per row.
--
-- Strings are Agda.Builtin.String, which binds the NATURAL builtin through
-- Agda.Builtin.Nat; that is why LTL.Base takes its Nat from there.  Nothing in
-- the development depends on this module.

module LTL.Pretty where

open import LTL.ShortPC public
open import Agda.Builtin.String public using (String)
open import Agda.Builtin.String using (primStringAppend; primShowNat; primStringToList)
import Agda.Builtin.List as B

------------------------------------------------------------------------
-- Strings and numbers

infixr 5 _<>_

_<>_ : String -> String -> String
_<>_ = primStringAppend

-- C-u C-u C-c C-n wraps its input as  show (...)
show : String -> String
show s = s

showNat : Nat -> String
showNat = primShowNat

-- Length of a builtin list (primStringToList gives one; it is not
-- LTL.Prelude's List).

blen : {A : Set} -> B.List A -> Nat
blen B.[]       = zero
blen (_ B.∷ xs) = suc (blen xs)

strLen : String -> Nat
strLen s = blen (primStringToList s)

infix  4.5 _≤ⁿ_
infixl 6   _⊔_

_≤ⁿ_ : Nat -> Nat -> Bool
zero  ≤ⁿ m     = true
suc n ≤ⁿ zero  = false
suc n ≤ⁿ suc m = n ≤ⁿ m

_⊔_ : Nat -> Nat -> Nat
n ⊔ m = if n ≤ⁿ m then m else n

spaces : Nat -> String
spaces zero    = ""
spaces (suc n) = " " <> spaces n

padL padR : Nat -> String -> String
padL w s = spaces (w ∸ strLen s) <> s
padR w s = s <> spaces (w ∸ strLen s)

concatS : List String -> String
concatS []        = ""
concatS (s ∷ ss) = s <> concatS ss

-- the lines, each followed by a line break
unlines : List String -> String
unlines []        = ""
unlines (s ∷ ss) = s <> "\n" <> unlines ss

commaSep : List String -> String
commaSep []           = ""
commaSep (s ∷ [])     = s
commaSep (s ∷ t ∷ ss) = s <> ", " <> commaSep (t ∷ ss)

------------------------------------------------------------------------
-- Formulas
--
-- fm c A prints A in a context of precedence c: A is parenthesised when its
-- own precedence is below c.  Precedences are those of LTL.Formula: the prefix
-- operators 30, ∧ 22, ⇒ 20 (both right associative), ⇔ 19 (non-associative).
-- The helpers take the pieces of the formula already split, never a rebuilt
-- formula, so every recursive call is on a subterm.

showVar : Nat -> String
showVar zero                         = "p"
showVar (suc zero)                   = "q"
showVar (suc (suc zero))             = "r"
showVar (suc (suc (suc zero)))       = "s"
showVar (suc (suc (suc (suc zero)))) = "t"
showVar (suc (suc (suc (suc (suc n))))) =
  "x" <> showNat (suc (suc (suc (suc (suc n)))))

paren : Nat -> Nat -> String -> String
paren c prec s = if c ≤ⁿ prec then s else "(" <> s <> ")"

notS : Nat -> String -> String
notS c s = paren c 30 ("¬ " <> s)

impS : Nat -> String -> String -> String
impS c a b = paren c 20 (a <> " ⇒ " <> b)

andS : Nat -> String -> String -> String
andS c a b = paren c 22 (a <> " ∧ " <> b)

mutual
  fm : Nat -> Formula -> String
  fm c (var n) = showVar n
  fm c (¬ A)   = fmNot c A
  fm c (A ⇒ B) = impS c (fm 21 A) (fm 20 B)
  fm c (○ A)   = paren c 30 ("○ " <> fm 30 A)
  fm c (□ A)   = paren c 30 ("□ " <> fm 30 A)

  -- the formula  ¬ A
  fmNot : Nat -> Formula -> String
  fmNot c (var n) = notS c (fm 30 (var n))
  fmNot c (¬ A)   = notS c (fm 30 (¬ A))
  fmNot c (A ⇒ B) = fmNotImp c A B
  fmNot c (○ A)   = notS c (fm 30 (○ A))
  fmNot c (□ A)   = fmNotBox c A

  -- the formula  ¬ □ A ;  ◇ A when A is a negation
  fmNotBox : Nat -> Formula -> String
  fmNotBox c (¬ A)   = paren c 30 ("◇ " <> fm 30 A)
  fmNotBox c (var n) = notS c ("□ " <> fm 30 (var n))
  fmNotBox c (A ⇒ B) = notS c ("□ " <> fm 30 (A ⇒ B))
  fmNotBox c (○ A)   = notS c ("□ " <> fm 30 (○ A))
  fmNotBox c (□ A)   = notS c ("□ " <> fm 30 (□ A))

  -- the formula  ¬ (A ⇒ B) ;  A ∧ B' when B is  ¬ B'
  fmNotImp : Nat -> Formula -> Formula -> String
  fmNotImp c A (¬ B)   = fmAnd c A B
  fmNotImp c A (var n) = notS c (impS 30 (fm 21 A) (fm 20 (var n)))
  fmNotImp c A (B ⇒ C) = notS c (impS 30 (fm 21 A) (fm 20 (B ⇒ C)))
  fmNotImp c A (○ B)   = notS c (impS 30 (fm 21 A) (fm 20 (○ B)))
  fmNotImp c A (□ B)   = notS c (impS 30 (fm 21 A) (fm 20 (□ B)))

  -- the formula  A ∧ B ;  X ⇔ Y when it is  (X ⇒ Y) ∧ (Y ⇒ X)
  fmAnd : Nat -> Formula -> Formula -> String
  fmAnd c (X ⇒ Y) B = fmAndImp c X Y B
  fmAnd c (var n) B = andS c (fm 23 (var n)) (fm 22 B)
  fmAnd c (¬ A)   B = andS c (fm 23 (¬ A)) (fm 22 B)
  fmAnd c (○ A)   B = andS c (fm 23 (○ A)) (fm 22 B)
  fmAnd c (□ A)   B = andS c (fm 23 (□ A)) (fm 22 B)

  fmAndImp : Nat -> Formula -> Formula -> Formula -> String
  fmAndImp c X Y (Y' ⇒ X') =
    if (X ≡ᶠ X') ∧ᵇ (Y ≡ᶠ Y')
       then paren c 19 (fm 20 X <> " ⇔ " <> fm 20 Y)
       else andS c (impS 23 (fm 21 X) (fm 20 Y)) (fm 22 (Y' ⇒ X'))
  fmAndImp c X Y (var n) = andS c (impS 23 (fm 21 X) (fm 20 Y)) (fm 22 (var n))
  fmAndImp c X Y (¬ B)   = andS c (impS 23 (fm 21 X) (fm 20 Y)) (fm 22 (¬ B))
  fmAndImp c X Y (○ B)   = andS c (impS 23 (fm 21 X) (fm 20 Y)) (fm 22 (○ B))
  fmAndImp c X Y (□ B)   = andS c (impS 23 (fm 21 X) (fm 20 Y)) (fm 22 (□ B))

showFormula : Formula -> String
showFormula = fm 0

-- the primitive connectives only
fmRaw : Nat -> Formula -> String
fmRaw c (var n) = showVar n
fmRaw c (¬ A)   = notS c (fmRaw 30 A)
fmRaw c (A ⇒ B) = impS c (fmRaw 21 A) (fmRaw 20 B)
fmRaw c (○ A)   = paren c 30 ("○ " <> fmRaw 30 A)
fmRaw c (□ A)   = paren c 30 ("□ " <> fmRaw 30 A)

showFormulaRaw : Formula -> String
showFormulaRaw = fmRaw 0

------------------------------------------------------------------------
-- Derivations as numbered Hilbert proofs
--
-- linearise walks the tree premises-first and appends one line per formula
-- proved.  A formula that is already a line is cited by its number and its
-- subtree is not visited again.  For mp d e the line reads  MP i, j  with i the
-- line of the implication (d) and j that of its antecedent (e).

data Justification : Set where
  byAx  : String -> Justification
  byMP  : Nat -> Nat -> Justification
  byGen : Nat -> Justification

data ProofLine : Set where
  proofLine : Formula -> Justification -> ProofLine

-- the number of lines so far, and the lines, newest first
data ProofState : Set where
  proofState : Nat -> List ProofLine -> ProofState

data Found : Set where
  notFound : Found
  foundAt  : Nat -> Found

-- the line proving A, searching lines n, n-1, ..., 1
findLine : Formula -> Nat -> List ProofLine -> Found
findLine A zero    ls                   = notFound
findLine A (suc n) []                   = notFound
findLine A (suc n) (proofLine B j ∷ ls) =
  if A ≡ᶠ B then foundAt (suc n) else findLine A n ls

pushFound : Formula -> Justification -> Nat -> List ProofLine -> Found -> ProofState × Nat
pushFound A j n ls (foundAt i) = proofState n ls , i
pushFound A j n ls notFound    = proofState (suc n) (proofLine A j ∷ ls) , suc n

-- Add A as a new line, unless an earlier line already proves it; either way
-- return the number of the line that proves A.

push : Formula -> Justification -> ProofState -> ProofState × Nat
push A j (proofState n ls) = pushFound A j n ls (findLine A n ls)

axName : {A : Formula} -> ⊢ A -> String
axName p1       = "P1"
axName p2       = "P2"
axName p3       = "P3"
axName k□       = "K□"
axName k○       = "K○"
axName exp      = "Exp"
axName ind      = "Ind"
axName lin      = "Lin"
axName (pc e)   = "PC"
axName (mp d e) = "MP"
axName (gen d)  = "Gen"

-- The last step of MP: the implication is line i and the antecedent has just
-- been laid out as line j, so B follows by MP i, j.  linGen is the same for
-- Gen, after its premise.

linMP2 : Formula -> Nat -> ProofState × Nat -> ProofState × Nat
linMP2 B i (s , j) = push B (byMP i j) s

linGen : Formula -> ProofState × Nat -> ProofState × Nat
linGen A (s , i) = push A (byGen i) s

mutual
  linearise : {A : Formula} -> ⊢ A -> ProofState -> ProofState × Nat
  linearise {A} d (proofState n ls) = linFound d (proofState n ls) (findLine A n ls)

  linFound : {A : Formula} -> ⊢ A -> ProofState -> Found -> ProofState × Nat
  linFound d s (foundAt i) = s , i
  linFound d s notFound    = linNew d s

  linNew : {A : Formula} -> ⊢ A -> ProofState -> ProofState × Nat
  linNew {A} p1       s = push A (byAx "P1")  s
  linNew {A} p2       s = push A (byAx "P2")  s
  linNew {A} p3       s = push A (byAx "P3")  s
  linNew {A} k□       s = push A (byAx "K□")  s
  linNew {A} k○       s = push A (byAx "K○")  s
  linNew {A} exp      s = push A (byAx "Exp") s
  linNew {A} ind      s = push A (byAx "Ind") s
  linNew {A} lin      s = push A (byAx "Lin") s
  linNew {A} (pc e)   s = push A (byAx "PC")  s
  linNew {A} (mp d e) s = linMP A (linearise d s) e
  linNew {A} (gen d)  s = linGen A (linearise d s)

  linMP : (B : Formula) {A : Formula} -> ProofState × Nat -> ⊢ A
       -> ProofState × Nat
  linMP B (s , i) e = linMP2 B i (linearise e s)

justifStr : Justification -> String
justifStr (byAx s)   = s
justifStr (byMP i j) = "MP " <> showNat i <> ", " <> showNat j
justifStr (byGen i)  = "Gen " <> showNat i

-- number, justification and formula of each line, oldest first
data Row : Set where
  row : String -> String -> String -> Row

rowsRev : Nat -> List ProofLine -> List Row -> List Row
rowsRev n       []                   acc = acc
rowsRev zero    (proofLine A j ∷ ls) acc = acc
rowsRev (suc n) (proofLine A j ∷ ls) acc =
  rowsRev n ls (row (showNat (suc n)) (justifStr j) (showFormula A) ∷ acc)

justWidth : List Row -> Nat
justWidth []                 = zero
justWidth (row _ j _ ∷ rs) = strLen j ⊔ justWidth rs

rowLines : Nat -> Nat -> List Row -> List String
rowLines nw jw []                 = []
rowLines nw jw (row k j f ∷ rs) =
  (padL nw k <> "  " <> padR jw j <> "  " <> f) ∷ rowLines nw jw rs

stateLines : Formula -> ProofState -> List String
stateLines A (proofState n ls) =
  ("⊢ " <> showFormula A) ∷ "" ∷ rowLines (strLen (showNat n)) (justWidth rows) rows
  where
    rows : List Row
    rows = rowsRev n ls []

proofLines : {A : Formula} -> ⊢ A -> List String
proofLines {A} d = stateLines A (fst (linearise d (proofState zero [])))

renderDeriv : {A : Formula} -> ⊢ A -> String
renderDeriv d = unlines (proofLines d)

------------------------------------------------------------------------
-- Derivations as trees
--
-- Each node is  rule  formula ; the children of  MP  are the implication and
-- then its antecedent.  Below depth n a subtree is shown as ⋮ .  pre is the
-- prefix of the node's own line, rest the prefix its children continue from.

mutual
  treeS : {A : Formula} -> Nat -> String -> String -> ⊢ A -> List String
  treeS     zero    pre rest d = (pre <> "⋮") ∷ []
  treeS {A} (suc n) pre rest d =
    (pre <> padR 3 (axName d) <> "  " <> showFormula A) ∷ treeKids n rest d

  treeKids : {A : Formula} -> Nat -> String -> ⊢ A -> List String
  treeKids n rest (mp d e) = treeS n (rest <> "├─ ") (rest <> "│  ") d ++
                             treeS n (rest <> "└─ ") (rest <> "   ") e
  treeKids n rest (gen d)  = treeS n (rest <> "└─ ") (rest <> "   ") d
  treeKids n rest p1       = []
  treeKids n rest p2       = []
  treeKids n rest p3       = []
  treeKids n rest k□       = []
  treeKids n rest k○       = []
  treeKids n rest exp      = []
  treeKids n rest ind      = []
  treeKids n rest lin      = []
  treeKids n rest (pc e)   = []

treeLines : {A : Formula} -> Nat -> ⊢ A -> List String
treeLines n d = treeS n "" "" d

renderTree : {A : Formula} -> Nat -> ⊢ A -> String
renderTree n d = unlines (treeLines n d)

------------------------------------------------------------------------
-- Countermodels
--
-- countermodel v0 r ... with r = mkRun b c0 c1 ... rest ... is the run
--   v0, rest            (a walk from v0 ending at b)
--   c0, c1, c0, c1, ... (a cycle from b back to b, repeated forever)
-- and Q is false at time 0.  Each time point is shown as the set of
-- variables true there; by Hintikka's lemma (LTL.Hintikka) that set of
-- variables is all of the model that matters.

isVar : Formula -> Bool
isVar (var n) = true
isVar (¬ A)   = false
isVar (A ⇒ B) = false
isVar (○ A)   = false
isVar (□ A)   = false

-- sub P may list a formula more than once
nubFormulas : List Formula -> List Formula
nubFormulas []       = []
nubFormulas (A ∷ As) = A ∷ filter (λ B -> ¬ᵇ (A ≡ᶠ B)) (nubFormulas As)

stateStr : Formula -> Val -> String
stateStr P v =
  "{" <> commaSep (map showFormula (filter (λ A -> valOf P v A)
                                           (nubFormulas (filter isVar (sub P))))) <> "}"

statesLines : Formula -> Nat -> List Val -> List String
statesLines P i []       = []
statesLines P i (v ∷ vs) =
  ("  " <> padL 3 (showNat i) <> "  " <> stateStr P v) ∷ statesLines P (suc i) vs

cmLines : (Q : Formula) -> LassoCountermodel Q -> List String
cmLines Q (countermodel v0 (mkRun b c0 c1 _ _ _ _ _ rest _ _) _ _ _) =
  ("⊬ " <> showFormula Q) ∷ ""
  ∷ "Countermodel: the formula is false at time 0.  Variables true at each time:"
  ∷ statesLines (¬ Q) zero (v0 ∷ rest)
  ++ "then repeating forever:"
  ∷ statesLines (¬ Q) loopStart (c0 ∷ c1)
  ++ ("  (back to time " <> showNat loopStart <> ")") ∷ []
  where
    loopStart : Nat
    loopStart = suc (length rest)

renderCM : (Q : Formula) -> LassoCountermodel Q -> String
renderCM Q c = unlines (cmLines Q c)

------------------------------------------------------------------------
-- Entry points

Decider : Set
Decider = (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q

resultLines : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
           -> List String
resultLines Q (inl d) = proofLines d
resultLines Q (inr c) = cmLines Q c

proveLinesWith : Decider -> Formula -> List String
proveLinesWith dec Q = resultLines Q (dec Q)

-- one String per line: what plain C-c C-n displays best
proveLines : Formula -> List String
proveLines = proveLinesWith decidePC

proveWith : Decider -> Formula -> String
proveWith dec Q = unlines (proveLinesWith dec Q)

prove : Formula -> String
prove = proveWith decidePC

proveTree : Nat -> Formula -> String
proveTree n Q = go (decidePC Q)
  where
    go : ⊢ Q ⊎ LassoCountermodel Q -> String
    go (inl d) = renderTree n d
    go (inr c) = renderCM Q c

------------------------------------------------------------------------
-- Checks: the printer on the identity (L1), the abbreviations, and a
-- countermodel.  The first is ⇒Refl_full of LTL.Proofs, as text.

pretty_identity : renderDeriv (⇒Refl {var zero}) ≡
  "⊢ p ⇒ p\n\n1  P2       (p ⇒ (p ⇒ p) ⇒ p) ⇒ (p ⇒ p ⇒ p) ⇒ p ⇒ p\n2  P1       p ⇒ (p ⇒ p) ⇒ p\n3  MP 1, 2  (p ⇒ p ⇒ p) ⇒ p ⇒ p\n4  P1       p ⇒ p ⇒ p\n5  MP 3, 4  p ⇒ p\n"
pretty_identity = refl

pretty_sugar :
  showFormula (□ var 0 ⇒ var 0 ∧ ○ var 0 ∧ ○ □ var 0)
   ∷ showFormula (◇ var 0 ∧ ◇ var 1 ⇒ ◇ (var 0 ∧ var 1))
   ∷ showFormula (○ ¬ var 0 ⇔ ¬ ○ var 0)
   ∷ showFormula (¬ var 0 ⇒ var 1)
   ∷ showFormula (¬ (var 0 ⇒ var 1))
   ∷ showFormulaRaw (◇ var 0)
   ∷ [] ≡
     "□ p ⇒ p ∧ ○ p ∧ ○ □ p"
   ∷ "◇ p ∧ ◇ q ⇒ ◇ (p ∧ q)"
   ∷ "○ ¬ p ⇔ ¬ ○ p"
   ∷ "¬ p ⇒ q"
   ∷ "¬ (p ⇒ q)"
   ∷ "¬ □ ¬ p"
   ∷ []
pretty_sugar = refl

pretty_countermodel : prove (var 0 ⇒ □ var 0) ≡
  "⊬ p ⇒ □ p\n\nCountermodel: the formula is false at time 0.  Variables true at each time:\n    0  {p}\n    1  {}\n    2  {p}\n    3  {p}\nthen repeating forever:\n    4  {p}\n  (back to time 4)\n"
pretty_countermodel = refl

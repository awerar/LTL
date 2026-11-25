# CLAUDE.md

Constructive LTL decision procedures in Agda. Given `Q : Formula`, the
procedures return `⊢ Q ⊎ LassoCountermodel Q`: a Hilbert-style
derivation or a certified finite lasso countermodel.

## Ground rules

- `LTL/Statement.agda` is the user's hand-checked specification (LTL
  semantics, `Valid`, the proof system `⊢`, `LassoCountermodel`,
  `DecisionProcedure`, and the record `Statement` of obligations). **Never edit
  it**; if it needs a change, tell the user. `Formula`, `∧`, `⇔` (re-exported by
  `LTL/2-Syntax/Formula.agda`), `⊢` (by `Deriv`) and `not`/`imp` (as `¬ᵇ`/`⇒ᵇ`,
  by `Prelude`) are its own, with the same fixities, and
  `Bool`/`List` are Agda's builtins, so its `Instant`/`Period` use our types.
  Import it qualified (`import LTL.Statement as S`) because its other names clash.
- `LTL/Main.agda` is hand-checked the same way: the few lines stating that
  `Statement`'s obligations hold (`statement : S.Statement`). **Never edit it**
  either; if a rename elsewhere breaks it, tell the user. Both files are
  untracked by `tools/proof-map`, and a local hook blocks edits to them.
- Agda 2.8.0, **no standard library**. Every file starts with
  `{-# OPTIONS --safe --without-K --exact-split #-}`. Keep it that way: no
  postulates, holes, or termination pragmas. Agda's own `Agda.Builtin.*`
  modules are fine (`Base` re-exports `Agda.Builtin.Nat`).
- Typecheck with e.g. `agda LTL/Main.agda`; `LTL.agda-lib` at the root
  supplies the include path, and interfaces go to `_build/` (see README for
  the full list). The modules in `LTL/9-Benchmarks/`
  (`Examples`, `Lecture`) are slow; the core proof
  modules should stay fast.
- Language: `var n`, `¬ A`, `A ⇒ B`, `○ A` (next), `□ A` (always). `A ∧ B`,
  `A ∨ B`, `A ⇔ B`, `◇ A`, `⊥`, `⊤` are abbreviations (`LTL/2-Syntax/Formula.agda`,
  with `⋀`/`⋁` over lists). Implication is `⇒` because Agda
  reserves `→`. Lemma names use the same symbols (`⇒Trans`, `□Elim`, `k□`).
  **Until is not implemented** (it is the thesis goal).
- Prelude notation follows Agda's standard library: `x ≡ y` (`sym`, `trans`,
  `cong`, `subst`), `A ⊎ B` (`inl`/`inr`; case analysis `[ f , g ] x`, with
  lambda branches parenthesised), `Σ[ x ∈ A ] B` and `A × B` (both built with
  `_,_`; `fst`/`snd`; `Statement`'s `σ , n ⊨ A` parses beside it), `x ∷ xs`,
  `xs ++ ys`, `x ∈ xs` (`here`/`there`), `xs ⊆ ys`, `m < n`, `m ≤ n`, `m + n`, `m ∸ n`,
  `if b then x else y` (a branch with an infix operator parenthesised,
  `if p x then (x ∷ xs) else xs`), and list helpers `filter any all null concat concatMap`.
  Quantifiers bounded by a list: `∀[ x ∈ xs ] B` for `(x : _) -> x ∈ xs -> B`,
  `∀ⁱ[ x ∈ xs ] B` for `{x : _} -> x ∈ xs -> B` (x read off the membership
  proof; callers pass only `m`), and `∃[ x ∈ xs ] B` for
  `Σ[ x ∈ _ ] x ∈ xs × B` (the witness is a pair field, so it has no implicit
  variant). Use ∀/∀ⁱ only when `B` is a single conclusion: the notation's body
  stops at the first unparenthesised `->` (and a `⊎` body needs parentheses),
  so when more hypotheses follow, write the telescope out.
  Boolean-valued operators carry a superscript naming their domain:
  connectives `∧ᵇ ∨ᵇ ¬ᵇ ⇒ᵇ ⇔ᵇ ≢ᵇ` on Bool (the plain symbols are the LTL
  connectives); tests `n ≡ⁿ m`, `n ≤ⁿ m` on Nat, `v ≡ᵛ w`, `v ≢ᵛ w`,
  `v ∈ᵛ us` on nodes (`LTL/1-Lib/DecEq.agda`, re-exported by `Nodes`; valuations
  at the instance `valEq` made in `LTL/5-States/Reach.agda`), `A ≡ᶠ B` on formulas (all `infix 4.5`,
  so `v ∈ᵛ us ≡ true` needs no parentheses). Lemmas about a symbol use the
  stdlib hyphen style (`∈ᵛ-sound`, `≡ᶠ-refl`); never `foo_bar`, which Agda
  reads as a mixfix operator. The Boolean lemmas, all in the "Boolean lemmas"
  section of `LTL/1-Lib/Prelude.agda`, follow one scheme: `∧ᵇ-trueˡ`, `∧ᵇ-split`,
  `∨ᵇ-introʳ`, `¬ᵇ-true`, `⇒ᵇ-mp`, `⇔ᵇ-sound`; add new ones there. `⊢ A` (`Statement`'s `data ⊢_`,
  re-exported by `LTL/2-Syntax/Deriv.agda`) is derivability. `Empty`/`Unit` keep their names, because
  `⊥`/`⊤` are formulas; `Empty` is `Statement`'s, re-exported by `Base`.
  Function types and lambdas stay ASCII (`->`) apart from `λ`.
- Signatures: use the named hypotheses instead of spelling them out:
  `Pred`/`Edges` (`Node -> Bool`, `Node -> Node -> Bool`), `xs ⊆ ys`,
  `C closed-under G within ws`, `NoneSat f C`, `HoldsOutside R ws`,
  `AllSat Pool xs`, `Finiteᵛ Pool` (all `LTL/1-Lib/Nodes.agda`, as is list
  difference `ws ∖ C`, so a growing search's invariant is
  `AllSat Pool (ws ∖ acc)`), `Fair P cy` (`LTL/6-Countermodel/Lasso.agda`).
  Boolean predicates as sets use `Exhaustible`'s algebra: `E ∩ F`, `E ∪ F`,
  `f ⁻¹ E`, `E ⊆ᵖ F`, so a pool shrunk by a pick is `Pool ∩ (x ≢ᵛ_)`, not
  `λ y -> Pool y ∧ᵇ (x ≢ᵛ y)`. The searches recurse on
  `Exhaustible Apart Pool` (`Finiteᵛ Pool` at nodes): `Pool` is the set
  still to pick from, `Apart x` what may follow a pick of x.
  A run of lemmas that share leading arguments, passed on
  unchanged, sits in a `module _ (ws : List Val) (G : Edges) where` block, so
  callers outside see the same arguments.
- Implicit arguments: a leading implicit that no clause or `where` block
  names is a `private variable`, declared at the top of the module
  (`A B C : Set` and `x y : A` in `Base`/`Prelude`/`Sets`/`Exhaustible`, the formulas
  `A B C P Q : Formula` in `Prop`/`PropList`/`Temporal`, trail endpoints,
  visited lists, `ws` and the search's pool `Pool` in `Graph`/`FairGraph`), so
  `⇒Trans : ⊢ A ⇒ B -> ⊢ B ⇒ C -> ⊢ A ⇒ C`. A variable is not in scope in the
  body: a definition whose clauses bind its implicits (`∧Fst {A} {B} = …`)
  keeps its binders, and one whose body needs a single name binds it by name
  (`keepIn {ws = ws} p t h`) or sits in a `module _ {ws : List Node}` block,
  which also carries shared explicit arguments (`reachesInto`'s `cl`).
  Generalised arguments come in order of first appearance in the signature.
  A variable clashes with any definition of the same name in the module,
  `where`-local ones and record fields included; hence `r` is not a variable in
  `FairGraph` (the `r` fields of `Terminal`, `FairIn`, `FairLoop`). In the
  graph layer `ws` is a variable wherever another argument's type fixes it (a
  `Reaches`, `Loop`, `Circuit`, `FairIn`, `HasSucc`, `zs ⊆ ws` or closed-under
  hypothesis), so a call reads `reachesApp r1 r2`; it stays explicit where it
  only occurs under a function (`reachSet ws v`, `sccOf ws r`, `outs ws x`),
  since Agda cannot infer it there.
- P-modules: the modules that work over one formula P — `State`, `Step`,
  `StepLemma`, `Closure`, `Extract`, `CompletePC`,
  `Walk`, `Lasso`, `Hintikka`, `SccLasso`, `SccExtract`, `SccSeed` — take it as a module parameter,
  `module LTL.5-States.Step (P : Formula) where` (with `Formula` imported above
  the header), so P is never written at a call site inside them. A P-module
  opens `LTL.5-States.Common` and each P-module it uses at P
  (`open import LTL.5-States.State P`), privately, and re-exports nothing:
  applying a module copies its names, so two re-exported copies of `valOf`
  would be ambiguous. The exceptions are `Walk`, which re-exports its
  applications of `Graph` and `FairGraph` at `step`, and `Lasso`, which re-exports `OrbitEval`
  at `readVal`. Code that does not mention P goes in an unparameterised
  module (`Common`, `Taut`, `VecFinite`, `Reach`), or an importer opening the
  P-module unapplied would see a spurious P argument. `Decide` works the same
  way one level up: its parameter is the input Q, and it opens the P-modules
  at `¬ Q`. Everywhere else (`Answer`, `Inspect`, `Correct`, `Pretty`, the tests) these
  modules are opened unapplied, so every name takes its formula first
  (`St benAri`, `Lasso (¬ Q) v0`, `decide Q`). `LTL.8-Procedures.Everything`
  re-exports all of them unapplied, and those importers import it.
- An unparameterised module that has a P-module in scope unapplied must not
  also open one applied, since the two copies of each name clash. A
  parameterised module opens the unparameterised ones it needs, never
  `Everything`.
- Names: prefer a readable name to an abbreviation. Names that follow the notes
  (`St`, `Ust`, `r1`, `chi`, `beta`) stay, with a
  comment at the definition. The search conventions (`fooGo`/`fooFind`, the
  `subset`/`fin`/`avail`/`next` binders, `x∈` for "x is in the pool") are
  explained above `AllSat` in `LTL/1-Lib/Nodes.agda`.
- Comments explain the code as it is today. A module header is about 5–15
  lines: what the module provides and its one or two non-obvious design
  choices. A comment above a definition is 1–4 lines, longer only for a subtle
  proof step. No references to development goals (G1, G2, …), plans, phases,
  checkpoints, or the lemma/theorem numbering of `m4.tex`/`m5.tex`; no history
  ("used to", "now", "before …"), which belongs in git. The labels of axioms,
  rules and conditions — (P1)–(P3), (L0)–(L7), (D1)–(D6), (S1)/(S2),
  (T1)–(T3), (R1), (Ind), (Lin), (Exp), (PC) — are the code's own
  vocabulary and stay.
- Computational `refl` checks go in `LTL/9-Tests/Checks.agda` (one section per module)
  or `LTL/9-Tests/GraphExamples.agda`, not in the proof modules.

## Documents

- `docs/ltl-master-thesis.tex` — thesis proposal (learn LTL, clarify the proof,
  add Until, semantics, readable proofs).
- `docs/m4.tex` — elimination-based procedure: system L (§1), states/transitions
  (§2), elimination (§3), extraction Thm 4.1 (§4), lasso branch (§5),
  decidability Thm 6.1 (§6).
- `docs/m5.tex` — SCC / fair-graph certificate procedure and comparison with m4.
- `docs/methodology.md` — how the project is worked on, and how AI is used.

## Module index (`LTL/`, in dependency order)

Each layer lives in its own folder, and a module's name follows its path
(`LTL/2-Syntax/Formula.agda` is `LTL.2-Syntax.Formula`). The `LTL/` root holds
only `Statement` and `Main`, what a reviewer must trust, and `Pretty`. A folder's numeric prefix is its
layer below, so folders sort in dependency order (the prefix is part of the
module name). Folder names never equal a module name.

0. **Specification** (root) — `Statement` (read-only, see above).
1. **Foundations** (`1-Lib/`) — `Base` (Nat and Bool from `Agda.Builtin`, `Statement`'s Empty, Unit,
   `≡`); `Prelude` (`≡ⁿ`, `⊎`, `Σ`, `×`, List from `Agda.Builtin.List`, `∈`, `⊆`,
   `<`, `nth`, Boolean connectives and all Boolean lemmas, `refuteTrue`, and
   membership in both directions for `++`, `map`, `filter`, `any`, `all`).
   Generic set layer, used by the graph layer at
   any node type: `Sets` (what the searches run on: `≤`, `decideAll`, a
   shrinking filter, the `null` lemmas); `Exhaustible`
   (Boolean predicates as subsets, `Subset A` with `∩ ∪ ⁻¹ ⊆ᵖ`, and Boolean
   relations as `Apartness A`; inductively
   finite sets `Exhaustible Apart Pool`, Coquand–Siles's bar type, built by
   `everyPick`, and their closure lemmas `exhaustibleSubset`, `exhaustibleUnion`,
   `exhaustibleProd`, `exhaustiblePreimage`; all searches recurse on one); `DecEq` (the record `DecEq A` bundling a Boolean
   equality test `_≡ᵛ_` with its soundness and reflexivity; module
   `Membership`: `∈ᵛ`, `≢ᵛ` and their lemmas; `Finite eq Pool`, `Exhaustible`
   with `≢ᵛ` as apartness; the instance `boolEq` at Bool and `boolFinite`);
   `Nodes` (parameterised by a
   node type and `eq : DecEq Node`, re-exporting `Membership eq`: `Finiteᵛ`
   (`Finite eq`),
   `listFinite`, the hypothesis names, list difference `∖ᵛ`/`∖`). m5's graph layer, parameterised like `Nodes` and by the
   edge test `G`: `Graph` (trails, the growing search `closure`, and the
   reachable set as an instance of it); `FairGraph` (components, the
   `fairGraph` certificate theorem, `certAll`, exclusivity, `certShape`;
   largest module), whose step kinds `CertStep` are a module of their own so
   that they do not depend on the graph.
   The P-module `Walk` applies both at `G = step` and re-exports them, so
   inside the P-modules their names read `Reaches ws`, `Cert fs ws`, and
   outside they take P first, `Cert (¬ Q) fs ws`.
2. **Syntax and proof system** (`2-Syntax/`) — `Formula` (`Statement`'s datatype,
   abbreviations (with `lit`, `⋀`/`⋁`), decidable `≡ᶠ`, the subformula list `sub`); `Skel` (propositional skeleton, valuations `Val` and `allVals`,
   `indexOf`, `nub`, `atoms`, `argsOf` (the A with `c A` in a list), `valFrom`, `isTaut` for (PC)); `Deriv` (re-exports `Statement`'s `data ⊢_`: 10 constructors + optional `pc`, whose side condition `Tautology` `pcTaut` meets via `isTaut` and `tautologyHolds` reads back).
3. **Derived rules (m4 Lemmas 1.1–1.2)** (`3-Rules/`) — `Prop` (L0–L7 via
   `⇒Refl`/`liftP`/`mpU`, no deduction theorem); `PropList` (`⋁Elim`,
   `⋁Drop`, `splitD`); `Temporal` (D1–D6, `expConv`, `indRule`).
4. **Semantics on lassos** (`4-Semantics/`) — `Orbit` (positions `(s , rest)`,
   `nextPos`, forward orbits; parameterised by the state type, mirroring
   `Statement`'s `Position`/`step`); `OrbitEval` (Boolean `evalAt` at positions,
   □ over the forward orbit, and its soundness; any state type, read by `read`).
5. **States and transitions (m4 §2)** (`5-States/`) — `Common`
   (the formula-independent base of the
   P-modules: re-exports `Rules`, `Reach` and `Orbit` at `Val`; the `refute`
   lemmas); P-modules `State` (a valuation is a row of bits over
   `stateAtoms = atoms (sub P)`, read by the skeleton evaluation, so (S1) holds
   by definition and `isState` is (S2) alone; `valOf`, `subformulas`,
   `eventualities`, `nexts`, `St`, `stLen`, `chi`, `beta`); `Step` (`step` as
   T1–T3 over `nexts` and `eventualities`, `StepFails`, `succs`); `StepLemma` (`chiProj`, Lemmas
   2.7–2.8); `CompletePC` (`stateCompletePC`, `betaElimPC`: state completeness
   and (L5) via (PC)). `Taut` (Boolean facts about chi/beta for (PC), stated
   for any P, and `tautChi`) is unparameterised.
   The finite search infrastructure, in the same folder: `Reach` (`valEq`, the `DecEq` of
   valuations, and the `Val` instance of `Nodes`); `VecFinite` (valuations of a given
   length are inductively finite, `guardedVecFinite`); `Closure` (`Ust`, the
   explored state set: `Graph`'s growing `closure` at `step`, seeded by the
   states containing `P`; its members are states, `ustState`); `Extract`
   (`betaElim`, `Refuted`, (R1) and `extractR1`: the pieces of m4 Thm 4.1
   that `SccExtract` reuses); `Closure` and `Extract` are P-modules. m4's elimination (§3) is not formalised: the
   SCC search replaces it, and countermodels live in `Ust`.
6. **Lasso countermodel branch (m4 §5)** (`6-Countermodel/`, all P-modules) —
   `Walk` (`Graph` at `step`, so walks are `Trail v zs w`, with `zs ⊆ Ust`
   kept beside them; `Fulfil`,
   `trailPersist`);
   `Lasso` (the record of Prop 5.3: a `Cycle` whose head `loop` is a valid
   position, as in `Statement`'s `Lasso`, fairness at its end `b`, and a valid
   start; and `OrbitEval` at `Val`, giving `evalAt` and `eval`);
   `Hintikka` (`globalFulfil`, Lemma 5.4, and Hintikka's lemma).
7. **SCC certificates** (`7-SCC/`, m5, P-modules applying `FairGraph`'s
   theorem to the state graph): `SccLasso` (`sccLasso`: a `FairLoop` is a `Lasso`),
   `SccExtract` (`ustCertRefuted`: a certificate refutes every state of
   `Ust`), `SccSeed` (`ustSeedTo`: every state of `Ust` is `Seeded`, reached from
   one containing `P`).
8. **Decision procedure** (`8-Procedures/`) — `Answer`
   (`LassoCountermodel`, `isProof` with `proofFrom` and `countermodelFrom`:
   only what `decideCorrect` uses); `Inspect` (off the proof path, for
   `Pretty`, tests and benchmarks: `cmRest`, `cmCycle`, `cmTrace`, `cmShape`,
   `derivCounts`);
   `Decide` (parameterised by the input Q: `provableSCC`, closed with (PC),
   `sccShape`, and `decide`, Thm 6.1); `Everything` (re-exports
   all of the above unapplied, for importers); `Correct` (imports
   `Everything`; the bridge: on a `Statement` lasso that starts at `pos0` and
   loops back to `loop`, `evalAt` is `Statement`'s `⊨` (`evalAt-holds`,
   `holds-evalAt`); `⊢-valid`, `toCountermodel`, `cmUnderivable`,
   `decideCorrect`, and the corollaries `deriveComplete` and
   `countermodelComplete`). At the root: `Main` (`statement :
   Statement.Statement`, the obligations met; `--safe` is coinfective, so
   checking it checks everything).
9. **Examples and benchmarks** — in `9-Tests/` (fast): `Checks` (the core
   modules' `refl` checks and example formulas: `benAri`, `◇P`, `bnb`, `c5`,
   …); `GraphExamples` (`Graph`'s and `FairGraph`'s computational checks, at `Node = Nat`);
   `Figure11` (the 46 formulas of Schmitt & Goubault-Larrecq Fig. 11, definitions
   only, opened by `tools/show-proof`). In
   `9-Benchmarks/` (slow): `Examples` (`decide` on the `Figure11` formulas); `Lecture` (`F a ∧ F b → F(a∧b)`).
10. **Readable output** (root) — `Pretty` (`prove`, `proveTree`, `proveLines`:
   decide results as numbered Hilbert proofs, trees, or lasso countermodels,
   rendered to `Agda.Builtin.String`; this is why `Base` takes `Nat` from
   `Agda.Builtin.Nat`). `tools/show-proof` runs it from the terminal via
   `agda --interaction-json`. Rendering is slow for large certificates.

## Reviewing

The user reviews the proof top down from `statement` (`LTL/Main.agda`) and bottom up from
the foundations, refactoring along the way. `tools/proof-map` (see README)
prints the dependency tree in either direction and keeps
the review marks in `docs/review.tsv`. Mark a definition (`tools/proof-map
done NAME`) only once the user says they are satisfied with it, after any
refactor of it, and commit the ledger along with that refactor. The user may
also tick definitions in the VS Code extension `tools/vscode-proof-map`,
which writes the same ledger.

## Public API

- `decide` (`LTL/8-Procedures/Decide.agda`) — of type
  `(Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q` (`LTL/8-Procedures/Answer.agda`).
- `decideCorrect` (`LTL/8-Procedures/Correct.agda`) — the same procedure as a
  `Statement.DecisionProcedure`.
- `statement` (`LTL/Main.agda`) — all of `Statement`'s obligations.

## Adding Until (expected touch points)

`Statement` (the constructor and its `⊨` clause; the user must make that change)
→ `Formula` (with `sub`) → `Deriv` → `State`/`Step` → the eventualities
(`eventualities` in `State`, read by `isState`, `step`, `Fair` in `Lasso`,
`evPreds` in `SccLasso` and `CompletePC`)
→ `OrbitEval`/`Correct`/`Hintikka` → the SCC fairness predicates in
`SccLasso`.

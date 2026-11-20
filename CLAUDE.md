# CLAUDE.md

Constructive LTL decision procedures in Agda. Given `Q : Formula`, the
procedures return `⊢ Q ⊎ LassoCountermodel Q`: a Hilbert-style
derivation or a certified finite lasso countermodel.

## Ground rules

- `LTL/Trusted.agda` is the user's hand-checked specification (LTL
  semantics, `valid`, `LassoCounterModel`, `DecisionProcedure`). **Never edit
  it**; if it needs a change, tell the user. `Formula` is its datatype
  (re-exported by `LTL/Syntax/Formula.agda` with this development's fixities), and
  `Bool`/`List` are Agda's builtins, so its `Instant`/`Period` use our types.
  Import it qualified (`import LTL.Trusted as T`) because its other names clash.
- Agda 2.8.0, **no standard library**. Every file starts with
  `{-# OPTIONS --safe --without-K --exact-split #-}`. Keep it that way: no
  postulates, holes, or termination pragmas. Agda's own `Agda.Builtin.*`
  modules are fine (`Base` re-exports `Agda.Builtin.Nat`).
- Typecheck from the repository root, e.g. `agda -i . LTL/Correct.agda`
  (see README for the full list). The modules in `LTL/Benchmarks/`
  (`Examples`, `Lecture`) are slow; the core proof
  modules should stay fast.
- Language: `var n`, `¬ A`, `A ⇒ B`, `○ A` (next), `□ A` (always). `A ∧ B`,
  `A ∨ B`, `A ⇔ B`, `◇ A`, `⊥`, `⊤` are abbreviations (`LTL/Syntax/Formula.agda`;
  `⋀`/`⋁` over lists in `LTL/States/Val.agda`). Implication is `⇒` because Agda
  reserves `→`. Lemma names use the same symbols (`⇒Trans`, `□Elim`, `k□`).
  **Until is not implemented** (it is the thesis goal).
- Prelude notation follows Agda's standard library: `x ≡ y` (`sym`, `trans`,
  `cong`, `subst`), `A ⊎ B` (`inl`/`inr`), `Σ[ x ∈ A ] B` and `A × B` (both
  built with `_,_`; `fst`/`snd`; `Trusted`'s `σ , n ⊨ A` parses beside it), `x ∷ xs`, `xs ++ ys`, `x ∈ xs`
  (`here`/`there`), `xs ⊆ ys`, `m < n`, `m ≤ n`, `m + n`, `m ∸ n`,
  `if b then x else y`, and list helpers `filter any all null concat`.
  Boolean-valued operators carry a superscript naming their domain:
  connectives `∧ᵇ ∨ᵇ ¬ᵇ ⇒ᵇ ⇔ᵇ ≢ᵇ` on Bool (the plain symbols are the LTL
  connectives); tests `n ≡ⁿ m`, `n ≤ⁿ m` on Nat, `v ≡ᵛ w`, `v ≢ᵛ w`,
  `v ∈ᵛ us` on nodes (`LTL/Lib/Nodes.agda`; valuations at the `Val` instance made in
  `LTL/States/Reach.agda`), `A ≡ᶠ B`, `A ∈ᶠ As` on formulas (all `infix 4.5`,
  so `v ∈ᵛ us ≡ true` needs no parentheses). Lemmas about a symbol use the
  stdlib hyphen style (`∈ᵛ-sound`, `≡ᶠ-refl`); never `foo_bar`, which Agda
  reads as a mixfix operator. The Boolean lemmas, all in the "Boolean lemmas"
  section of `LTL/Lib/Prelude.agda`, follow one scheme: `∧ᵇ-trueˡ`, `∧ᵇ-split`,
  `∨ᵇ-introʳ`, `¬ᵇ-true`, `⇒ᵇ-mp`, `⇔ᵇ-complete`; add new ones there. `⊢ A` (`data ⊢_` in
  `LTL/Syntax/Deriv.agda`) is derivability. `Empty`/`Unit` keep their names, because
  `⊥`/`⊤` are formulas; `Empty` is `Trusted`'s, re-exported by `Base`.
  Function types and lambdas stay ASCII (`->`) apart from `λ`.
- Signatures: use the named hypotheses instead of spelling them out:
  `Pred`/`Edges` (`Node -> Bool`, `Node -> Node -> Bool`), `xs ⊆ ys`,
  `Closed ws G C`, `NoneSat f C`, `HoldsOutside R ws`, `AllSat`/`Avail`
  (all `LTL/Lib/Nodes.agda`), `Fair P cy` (`LTL/Countermodel/Lasso.agda`).
  A run of lemmas that share leading arguments, passed on
  unchanged, sits in a `module _ (ws : List Val) (G : Edges) where` block, so
  callers outside see the same arguments.
- P-modules: the modules that work over one formula P — `State`, `Step`,
  `Proj`, `NonState`, `Complete`, `StepLemma`, `Closure`, `Extract`,
  `CompletePC`, `Walk`, `Lasso`, `Global`, `Eval`, `Hintikka`, `SccLasso`,
  `SccExtract`, `SccSeed` — take it as a module parameter,
  `module LTL.States.Step (P : Formula) where` (with `Formula` imported above
  the header), so P is never written at a call site inside them. A P-module
  opens `LTL.States.Common` and each P-module it uses at P
  (`open import LTL.States.State P`), privately, and re-exports nothing:
  applying a module copies its names, so two re-exported copies of `valOf`
  would be ambiguous. The exceptions are `SccLasso`, which re-exports its
  application of `Graph` at `step`, and `Eval`, which re-exports `OrbitEval`
  at `readVal`. Code that does not mention P goes in an unparameterised
  module (`Common`, `Taut`, `VecBar`, `Reach`), or an importer opening the
  P-module unapplied would see a spurious P argument. `Decide` works the same
  way one level up: its parameter is the input Q, and it opens the P-modules
  at `¬ Q`. Everywhere else (`Answer`, `Correct`, `Pretty`, the tests) these
  modules are opened unapplied, so every name takes its formula first
  (`St benAri`, `Lasso (¬ Q) v0`, `decide Q`). `LTL.Procedures.Everything`
  re-exports all of them unapplied, and those importers import it.
- An unparameterised module that has a P-module in scope unapplied must not
  also open one applied, since the two copies of each name clash. A
  parameterised module opens the unparameterised ones it needs, never
  `Everything`.
- Names: prefer a readable name to an abbreviation. Names that follow the notes
  (`St`, `Ust`, `r1`, `chi`, `beta`) stay, with a
  comment at the definition. The search conventions (`fooGo`/`fooFind`, the
  `sb`/`bar`/`av` binders) are explained above `AllSat` in `LTL/Lib/Nodes.agda`.
- Comments explain the code as it is today. A module header is about 5–15
  lines: what the module provides and its one or two non-obvious design
  choices. A comment above a definition is 1–4 lines, longer only for a subtle
  proof step. No references to development goals (G1, G2, …), plans, phases,
  checkpoints, or the lemma/theorem numbering of `m4.tex`/`m5.tex`; no history
  ("used to", "now", "before …"), which belongs in git. The labels of axioms,
  rules and conditions — (P1)–(P3), (L0)–(L7), (D1)–(D6), (S1)/(S2),
  (T1)–(T3), (R1), (Ind), (Lin), (Exp), (PC) — are the code's own
  vocabulary and stay.
- Computational `refl` checks go in `LTL/Tests/Checks.agda` (one section per module)
  or `LTL/Tests/GraphExamples.agda`, not in the proof modules.

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
(`LTL/Syntax/Formula.agda` is `LTL.Syntax.Formula`). The `LTL/` root holds
only `Trusted`, `Correct` and `Pretty`. Folder names never equal
a module name.

0. **Specification** (root) — `Trusted` (read-only, see above).
1. **Foundations** (`Lib/`) — `Base` (Nat and Bool from `Agda.Builtin`, `Trusted`'s Empty, Unit,
   `≡`); `Prelude` (`⊎`, `Σ`, `×`, List from `Agda.Builtin.List`, `∈`, `⊆`,
   `<`, index/nth, Boolean connectives and all Boolean lemmas, `refuteTrue`).
   Generic set layer, importing only `Prelude` and used by the graph layer at
   any node type: `Sets` (`≤`, `FindResult`, filter/any/all lemmas, `CertStep`); `Bar`
   (inductively finite sets after Coquand–Siles, closure lemmas; all searches
   recurse on a Bar); `Nodes` (parameterised by a node type and a sound,
   reflexive equality test `_≡ᵛ_`: `∈ᵛ`, `≢ᵛ`, `IFin`, `listBar`, the
   hypothesis names).
2. **Syntax and proof system** (`Syntax/`) — `Formula` (`Trusted`'s datatype,
   abbreviations, decidable `≡ᶠ`); `Sub` (subformula list `sub`); `Skel` (propositional skeleton,
   `isTaut` for (PC)); `Deriv` (`data ⊢_`: 10 constructors + optional `pc`).
3. **Derived rules (m4 Lemmas 1.1–1.2)** (`Rules/`) — `Prop` (L0–L7 via
   `⇒Refl`/`liftP`/`mpU`, no deduction theorem); `PropList` (`⋁Elim`,
   `⋁Drop`, `splitD`); `Temporal` (D1–D6, `expConv`, `indRule`).
4. **States and transitions (m4 §2)** (`States/`, with layer 5) — `Val` (literals,
   `⋀`/`⋁`, `litList`); `Common` (the formula-independent base of the
   P-modules: re-exports `Rules`, `Reach` and `Orbit` at `Val`; the `refute`
   lemmas, `AllLen`, `allComplete`); P-modules `State` (`isState`, `St`,
   `chi`, `beta`); `Step` (`step`, `succs`, T1–T3); `Proj`, `NonState`,
   `Complete` (`stateComplete`, Lemmas 2.5–2.6); `StepLemma` (Lemmas
   2.7–2.8). `Taut` (Boolean facts about chi/beta for (PC), stated for any
   P, and `tautChi`) is unparameterised.
5. **Finite search infrastructure** (`States/`) — `Reach` (`≡ᵛ` on valuations, the
   `Val` instance of `Nodes`); `VecBar` (valuations of a given
   length are inductively finite, `guardedVecBar`); `Closure` (`Ust`, the
   explored state set; its members are states, `ustState`); `Extract`
   (`betaElim`, `Refuted`, (R1) and `extractR1`: the pieces of m4 Thm 4.1
   that `SccExtract` reuses); `Closure` and `Extract` are P-modules. m4's elimination (§3) is not formalised: the
   SCC search replaces it, and countermodels live in `Ust`.
6. **Lasso countermodel branch (m4 §5)** (`Countermodel/`) — `Orbit` (positions `(s , rest)`,
   `nextPos`, forward orbits; parameterised by the state type, mirroring
   `Trusted`'s `Position`/`step`); `OrbitEval` (Boolean `evalAt` at positions,
   □ over the forward orbit, and its soundness; any state type, read by `read`); `Walk`;
   `Lasso` (the record of Prop 5.3: a `Cycle` whose head `loop` is a valid
   position, as in `Trusted`'s `Lasso`, fairness at its end `b`, and a valid
   start);
   `Global` (Lemma 5.4); `Eval` (`OrbitEval` at `Val`); `Hintikka`. All but
   `Orbit` and `OrbitEval` are P-modules.
7. **Decision procedure** — in `SCC/` (m5): `Graph` (the `fairGraph`
   certificate theorem, largest module; parameterised like `Nodes` and by the
   edge test `G`, imports only the generic layer; the P-module `SccLasso`
   applies it at `G = step` and re-exports it, so inside the P-modules its
   names read `Trail ws`, `Cert fs ws`, and outside they take P first,
   `Cert (¬ Q) fs ws`); `SccLasso`,
   `SccExtract` (`ustCertRefuted`: a certificate refutes every state of
   `Ust`), `SccSeed` (`ustSeedTo`: every state of `Ust` is reached from one
   containing `P`). In `Procedures/`: `CompletePC` (P-module;
   `stateCompletePC`, `betaElimPC`: Lemma 2.6 and (L5) via (PC)); `Answer`
   (`LassoCountermodel`, `isProof`, `countermodelFrom`, `cmLasso`,
   `cmTrace`, `cmShape`, `countermodelFrom`, `proofFrom`, `derivCounts`);
   `Decide` (parameterised by the input Q: `provableSCC`, closed with (PC),
   `sccProof`, `sccShape`, and `decide`, Thm 6.1); `Everything` (re-exports
   all of the above unapplied, for importers). At the root:
   `Correct` (the bridge: on a `Trusted` lasso that starts at `pos0` and loops
   back to `loop`, `evalAt` is `Trusted`'s `⊨` (`evalAt-holds`,
   `holds-evalAt`); `⊢-valid`, `toCounterModel`, `cmUnderivable`, and
   `decideCorrect`).
8. **Examples and benchmarks** — in `Tests/` (fast): `Checks` (the core
   modules' `refl` checks and example formulas: `benAri`, `◇P`, `bnb`, `c5`,
   …); `GraphExamples` (Graph's computational checks, at `Node = Nat`). In
   `Benchmarks/` (slow): `Examples` (46 formulas, Schmitt & Goubault-Larrecq
   Fig. 11); `Lecture` (`F a ∧ F b → F(a∧b)`).
9. **Readable output** (root) — `Pretty` (`prove`, `proveTree`, `proveLines`:
   decide results as numbered Hilbert proofs, trees, or lasso countermodels,
   rendered to `Agda.Builtin.String`; this is why `Base` takes `Nat` from
   `Agda.Builtin.Nat`). `tools/show-proof` runs it from the terminal via
   `agda --interaction-json`. Rendering is slow for large certificates.

## Public API

- `decide` (`LTL/Procedures/Decide.agda`) — of type
  `(Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q` (`LTL/Procedures/Answer.agda`).
- `decideCorrect` (`LTL/Correct.agda`) — the same procedure as a
  `Trusted.DecisionProcedure`.

## Adding Until (expected touch points)

`Trusted` (the constructor and its `⊨` clause; the user must make that change)
→ `Formula` → `Sub` → `Deriv` → `State`/`Step` → the eventualities
(currently `□Args` in `Skel`, read by `Fair` in `Lasso` and by `CompletePC`)
→ `OrbitEval`/`Correct`/`Hintikka` → the SCC fairness predicates in
`SccLasso`.

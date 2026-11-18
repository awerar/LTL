# Constructive LTL decision procedures in Agda

This development constructs a decision procedure returning either a derivation
of a temporal formula or a certified lasso countermodel. It includes procedures
based on state elimination and on strongly connected components, and versions
with shorter proof certificates.

The current language has propositional variables, negation `¬`, implication
`⇒`, **next** `○`, and **always** `□`. Eventually `◇` and the other Boolean
connectives (`∧`, `∨`, `⇔`, `⊤`, `⊥`) are abbreviations. **Until is not yet
implemented.**

## Start here

- [Master's thesis proposal](docs/ltl-master-thesis.pdf)
  ([LaTeX source](docs/ltl-master-thesis.tex)): learn LTL, understand the existing
  proof, extend it with Until, and study execution and readable certificates.
- [Proof extraction from a failed LTL tableau](docs/m4.pdf)
  ([LaTeX](docs/m4.tex)): the state-elimination argument.
- [The SCC decision procedure](docs/m5.pdf)
  ([LaTeX](docs/m5.tex)): the graph certificate argument and comparison.
- [LTL/Trusted.agda](LTL/Trusted.agda): the specification, a small
  hand-checked module stating the LTL semantics and what a decision procedure
  must prove. [LTL/Correct.agda](LTL/Correct.agda) proves it for all three
  procedures.
- [LTL/Procedures/Decide.agda](LTL/Procedures/Decide.agda) and
  [LTL/Procedures/DecideSCC.agda](LTL/Procedures/DecideSCC.agda): the two public decision procedures.
- [LTL/Procedures/ShortPC.agda](LTL/Procedures/ShortPC.agda): shorter derivations using a checked
  propositional-consequence rule.

## Check the development

Tested with **Agda 2.8.0**. No Agda standard library is needed. From the repository
root:

```sh
agda -i . LTL/Correct.agda
agda -i . LTL/Procedures/DecideSCC.agda
agda -i . LTL/Procedures/ShortPC.agda
agda -i . LTL/Tests/Checks.agda
agda -i . LTL/Tests/GraphExamples.agda
agda -i . LTL/Benchmarks/Compare.agda
agda -i . LTL/Benchmarks/Lecture.agda
agda -i . LTL/Benchmarks/Proofs.agda
```

`Checks` and `GraphExamples` hold the computational checks of the core
modules. `Compare` imports the examples and contains computational comparisons on 47
formulas. `Lecture` examines a worked example. `Proofs` measures and inspects
proof certificates. These benchmark modules take longer than the core proofs.
The source comments include historical timings; those depend on the machine and
evaluation method.

The files use `--safe --without-K --exact-split`. There are no postulates,
unfinished goals, or termination overrides. The procedures return a derivation
or a finite lasso countermodel. `LTL/Correct.agda` connects this to the
semantics of `LTL/Trusted.agda`: each procedure is a `DecisionProcedure`.
When it answers true, the formula is valid, meaning true at time 0 of every
lasso (ultimately periodic) interpretation. When it answers false, it returns a
lasso on which the formula is false. Validity on arbitrary infinite words is
not stated. The proposal discusses that distinction.

## Viewing proofs

[LTL/Pretty.agda](LTL/Pretty.agda) prints the result of `decidePC` in a
readable form. For a valid formula you get a numbered Hilbert proof, where
each line is an axiom or follows from earlier lines by MP or Gen. For an
invalid one you get the lasso countermodel: the variables true at each time
point, and where the loop starts. `∧`, `⇔` and `◇` are printed as
abbreviations; `∨`, `⊤` and `⊥` are not, so `¬ A ⇒ B` and `p ⇒ p` read as
written.

From a terminal (needs Python 3):

```sh
tools/show-proof 'G p -> p'                 # numbered proof
tools/show-proof '□ pv ⇒ pv'                # the same, in Agda syntax
tools/show-proof --tree 6 'G p -> p'        # proof tree, to depth 6
tools/show-proof 'F p & F q -> F (p & q)'   # countermodel
tools/show-proof --raw 'F p'                # formula without abbreviations
tools/show-proof --expr 'renderDeriv (dne {pv})'   # any String expression
```

The formula can be written in ASCII or in Agda syntax, or a mix of both. The
ASCII forms are:

| ASCII | Means |
|---|---|
| `~`, `!`, `not` | `¬` |
| `X`, `next` | `○` |
| `G`, `[]`, `always` | `□` |
| `F`, `<>`, `eventually` | `◇` |
| `&`, `/\`, `and` | `∧` |
| `\|`, `\/`, `or` | `∨` |
| `->`, `=>` | `⇒` |
| `<->`, `<=>` | `⇔` |
| `true`, `false` | `⊤`, `⊥` |

The variables `p q r s t` and `x0`, `x1`, … are `var 0` to `var 4` and `var N`,
which are also the names used in the output. Precedence is Agda's: prefix
operators bind tightest, then `∧`, `∨`, `⇒` (right associative), `⇔`. The
formula is evaluated with `LTL.Pretty` and `LTL.Benchmarks.Examples` open, so `pv`, `qv`,
`axT`, … can also be used. `tools/show-proof --help` lists all of this. Set
`AGDA` to choose the Agda binary.

In an editor, load `LTL/Pretty.agda` or `LTL/Benchmarks/Proofs.agda`, then:

- Emacs: `C-u C-u C-c C-n prove (□ pv ⇒ pv)` prints the text with real line
  breaks. Plain `C-c C-n` shows a quoted string with `\n` escapes.
- Editors that talk to Agda over `--interaction-json` (for example the VS Code
  extensions) always show a quoted string. `C-c C-n proveLines (□ pv ⇒ pv)`
  gives one quoted string per line.

Other functions: `proveTree n Q`, `renderDeriv d` and `renderTree n d` for any
derivation `d`, `showFormula` and `showFormulaRaw`.

Limitations: rendering is computed by Agda's normaliser, so it is only
practical for small certificates. `p ⇒ p`, `□ p ⇒ p` and the countermodel
examples take about a second. Some formulas, such as `□ pv ⇒ ○ pv`, did not
finish within 90 seconds. `decide`'s own certificates (`proveWith decide Q`)
are far too large to render; see `LTL/Benchmarks/Proofs.agda`.

## Repository layout

The notes (`m4`, `m5`), the thesis proposal and the methodology are in
[docs/](docs). The Agda modules are grouped by the part of the argument they
formalise. A module's name follows its path, so `LTL/Syntax/Formula.agda` is
`LTL.Syntax.Formula`.

| Folder | Modules | What it is |
|---|---|---|
| `LTL/` | `Trusted`, `Semantics`, `Correct`, `Pretty` | the specification, the proof that the Boolean evaluation is its semantics (so derivable formulas are valid), the three procedures as `DecisionProcedure`s, and readable output |
| `LTL/Lib/` | `Base`, `Prelude`, `Sets`, `Bar`, `Nodes` | foundations without the standard library; inductively finite sets |
| `LTL/Syntax/` | `Formula`, `Sub`, `Skel`, `Deriv` | syntax and deductive rules (`⊢ A`: A is derivable), m4 §1 |
| `LTL/Rules/` | `Prop`, `PropList`, `Temporal` | derived rules, m4 Lemmas 1.1–1.2 |
| `LTL/States/` | `Val`, `State`, `Step`, `Taut`, `Proj`, `NonState`, `Complete`, `StepLemma`, `Reach`, `VecBar`, `Closure` | states, transitions and the finite state space, m4 §2 |
| `LTL/Elimination/` | `Gfp`, `Elim`, `Trace`, `Extract` | elimination and extraction of derivations, m4 §3–4 |
| `LTL/Countermodel/` | `Orbit`, `LassoEval`, `Walk`, `Fix`, `Round`, `Lasso`, `Run`, `Global`, `Eval`, `Sound`, `Hintikka` | finite lasso countermodels and their correctness, m4 §5 |
| `LTL/SCC/` | `Graph`, `SccLasso`, `SccExtract`, `SccTrap` | graph certificates and their application to temporal logic, m5 |
| `LTL/Procedures/` | `Decide`, `DecideSCC`, `CompletePC`, `ShortPC` | the decision procedures, m4 Thm 6.1 |
| `LTL/Tests/` | `Checks`, `GraphExamples` | computational checks of the core modules |
| `LTL/Benchmarks/` | `Examples`, `Lecture`, `Compare`, `Proofs` | slow benchmarks and certificate measurements |

The source comments cite goals (G1–G40), phases and checkpoints of the plans
of the original development, which are not in this repository;
[docs/plan-index.md](docs/plan-index.md) lists where each one lives in the code.

The textbook and external papers used during the original development are not
included in this repository; bibliographic links are provided in the proposal.

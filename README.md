# Constructive LTL decision procedures in Agda

This development constructs a decision procedure, `decide`, returning either
a derivation of a temporal formula or a certified lasso countermodel. It
searches the state graph for fair strongly connected components (m5). Its
derivations use a checked propositional-consequence rule, which keeps the
certificates short.

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
- [LTL/Statement.agda](LTL/Statement.agda): the specification, a small
  hand-checked module stating the LTL semantics and what a decision procedure
  must prove. [LTL/Correct.agda](LTL/Correct.agda) proves it for the
  procedure.
- [LTL/Procedures/Decide.agda](LTL/Procedures/Decide.agda): the public
  decision procedure, and [LTL/Procedures/Answer.agda](LTL/Procedures/Answer.agda):
  what it returns and how to read it.

## Check the development

Tested with **Agda 2.8.0**. No Agda standard library is needed. From the repository
root (`LTL.agda-lib` supplies the include path; interfaces go to `_build/`):

```sh
agda LTL/Correct.agda
agda LTL/Pretty.agda
agda LTL/Tests/Checks.agda
agda LTL/Tests/GraphExamples.agda
agda LTL/Benchmarks/Examples.agda
agda LTL/Benchmarks/Lecture.agda
```

`Checks` and `GraphExamples` hold the computational checks of the core
modules. `Examples` decides 46 formulas from Schmitt and Goubault-Larrecq.
`Lecture` examines a worked example. These benchmark modules take longer than
the core proofs.
Timings quoted in the source comments depend on the machine and evaluation
method.

The files use `--safe --without-K --exact-split`. There are no postulates,
unfinished goals, or termination overrides. The procedures return a derivation
or a finite lasso countermodel. `LTL/Correct.agda` connects this to the
semantics of `LTL/Statement.agda`: `decide` is a `DecisionProcedure`.
When it answers true, the formula is valid, meaning true at time 0 of every
lasso (ultimately periodic) interpretation. When it answers false, it returns a
lasso on which the formula is false. Validity on arbitrary infinite words is
not stated. The proposal discusses that distinction.

## Viewing proofs

[LTL/Pretty.agda](LTL/Pretty.agda) prints the result of `decide` in a
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

In an editor, load `LTL/Pretty.agda`, then:

- Emacs: `C-u C-u C-c C-n prove (□ pv ⇒ pv)` prints the text with real line
  breaks. Plain `C-c C-n` shows a quoted string with `\n` escapes.
- Editors that talk to Agda over `--interaction-json` (for example the VS Code
  extensions) always show a quoted string. `C-c C-n proveLines (□ pv ⇒ pv)`
  gives one quoted string per line.

Other functions: `proveTree n Q`, `renderDeriv d` and `renderTree n d` for any
derivation `d`, `showFormula` and `showFormulaRaw`.

Limitations: rendering is computed by Agda's normaliser, so it is only
practical for small certificates.

## Repository layout

The notes (`m4`, `m5`), the thesis proposal and the methodology are in
[docs/](docs). The Agda modules are grouped by the part of the argument they
formalise. A module's name follows its path, so `LTL/Syntax/Formula.agda` is
`LTL.Syntax.Formula`.

| Folder | Modules | What it is |
|---|---|---|
| `LTL/` | `Statement`, `Correct`, `Pretty` | the specification; the proof that the Boolean evaluation is its semantics (so derivable formulas are valid) and that the procedure is a `DecisionProcedure`; readable output |
| `LTL/Lib/` | `Base`, `Prelude`, `Sets`, `Bar`, `Nodes`, `Graph`, `FairGraph` | foundations without the standard library; inductively finite sets; graph search and the generic fair-graph certificate theorem of m5 |
| `LTL/Syntax/` | `Formula`, `Skel`, `Deriv`, `Val` | syntax and deductive rules (`⊢ A`: A is derivable), m4 §1 |
| `LTL/Rules/` | `Prop`, `PropList`, `Temporal` | derived rules, m4 Lemmas 1.1–1.2 |
| `LTL/Semantics/` | `Orbit`, `OrbitEval` | positions on a lasso and Boolean evaluation of formulas there |
| `LTL/States/` | `Reach`, `Common`, `State`, `Step`, `Taut`, `CompletePC`, `StepLemma`, `VecBar`, `Closure`, `Extract` | states, transitions, the finite state space, and the building blocks of extraction, m4 §2 and §4 |
| `LTL/Countermodel/` | `Walk`, `Lasso`, `Hintikka` | finite lasso countermodels and their correctness, m4 §5 |
| `LTL/SCC/` | `SccLasso`, `SccExtract`, `SccSeed` | graph certificates applied to temporal logic, m5 |
| `LTL/Procedures/` | `Answer`, `Decide`, `Everything` | the decision procedure and its answer type, m4 Thm 6.1 |
| `LTL/Tests/` | `Checks`, `GraphExamples` | computational checks of the core modules |
| `LTL/Benchmarks/` | `Examples`, `Lecture` | slow benchmarks |

The modules that work over one fixed formula P (most of `States/`,
and all of `Countermodel/` and `SCC/`) take it as a module parameter,
so P is not passed around inside them. `Decide` is parameterised the same way
by the input Q, and opens them at `¬ Q`. `LTL/Procedures/Everything.agda`
opens all of these modules without arguments for everyone else, so there
every name takes its formula first: `St P`, `Lasso (¬ Q) v0`, `decide Q`.

The textbook and external papers used during the original development are not
included in this repository; bibliographic links are provided in the proposal.

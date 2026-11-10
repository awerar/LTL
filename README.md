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
- [Proof extraction from a failed LTL tableau](m4.pdf)
  ([LaTeX](m4.tex)): the state-elimination argument.
- [The SCC decision procedure](m5.pdf)
  ([LaTeX](m5.tex)): the graph certificate argument and comparison.
- [LTL/Decide.agda](LTL/Decide.agda) and
  [LTL/DecideSCC.agda](LTL/DecideSCC.agda): the two public decision procedures.
- [LTL/ShortPC.agda](LTL/ShortPC.agda): shorter derivations using a checked
  propositional-consequence rule.

## Check the development

Tested with **Agda 2.8.0**. No Agda standard library is needed. From the repository
root:

```sh
agda -i . LTL/DecideSCC.agda
agda -i . LTL/ShortPC.agda
agda -i . LTL/Compare.agda
agda -i . LTL/Lecture.agda
agda -i . LTL/Proofs.agda
```

`Compare` imports the examples and contains computational comparisons on 47
formulas. `Lecture` examines a worked example. `Proofs` measures and inspects
proof certificates. These benchmark modules take longer than the core proofs.
The source comments include historical timings; those depend on the machine and
evaluation method.

The files use `--safe --without-K --exact-split`. There are no postulates,
unfinished goals, or termination overrides. The result is expressed in terms
of derivability and finite lasso countermodels. Its relationship to semantic
validity on arbitrary infinite words requires careful specification of the
semantics and constructive assumptions; the proposal discusses this distinction.

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
formula is evaluated with `LTL.Pretty` and `LTL.Examples` open, so `pv`, `qv`,
`axT`, … can also be used. `tools/show-proof --help` lists all of this. Set
`AGDA` to choose the Agda binary.

In an editor, load `LTL/Pretty.agda` or `LTL/Proofs.agda`, then:

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
are far too large to render; see `LTL/Proofs.agda`.

## Mathematical entry points

`Formula`, `Deriv`: syntax and deductive rules.

`Closure`, `Gfp`, `Elim`, `Trace`, `Extract`: the finite search and extraction of
derivations from eliminated states.

`Lasso`, `Run`, `Eval`, `Sound`, `Hintikka`: finite countermodels and their
correctness.

`Graph`, `SccLasso`, `SccExtract`, `SccTrap`: graph certificates and their
application to temporal logic.

The textbook and external papers used during the original development are not
included in this repository; bibliographic links are provided in the proposal.

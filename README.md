# ReactLib

Lean libraries for [Reactor](https://github.com/zeroth-research/reactive-modules).
The libraries come in two Lake packages, each in its own directory:

| Package | Library | Modules | Contents |
|---------|---------|---------|----------|
| [`ReactLib`](ReactLib) | `Spec` | `Spec.LTL` | LTL formulas and their semantics |
| | `Relational` | `Relational.Mat`, `Relational.Circ`, `Relational.Basic` | matrices, the box combinators over them, reactive modules and their proof rules |
| [`LeanAI`](LeanAI) | `LeanAI` | `LeanAI`, `LeanAI.*` | the `ai_solve` tactic and its LLM backends |

Both are pinned to `leanprover/lean4:v4.34.0`. `ReactLib` requires cslib at
the same version, and gets Mathlib through it. `LeanAI` needs nothing beyond
Lean core, which is why it is a package of its own: requiring it does not
fetch Mathlib.

## Using them

From a git checkout:

```toml
[[require]]
name = "ReactLib"
git = "https://github.com/zeroth-research/ReactLib"
rev = "<commit>"
subDir = "ReactLib"
```

From a local checkout:

```toml
[[require]]
name = "ReactLib"
path = "../ReactLib/ReactLib"
```

Either way, the project can import the modules of both `Spec` and
`Relational`. The projects `verith` generates require both packages from
git. Set `REACTLIB` to a local checkout of this repository to make them
require it by path instead.

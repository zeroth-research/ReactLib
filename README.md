# reactor-lean

Lean libraries for [Reactor](https://github.com/zeroth-research/reactive-modules).
Each library is a separate Lake package in its own directory:

| Package | Modules | Contents |
|---------|---------|----------|
| [`Relational`](Relational) | `Relational.Mat`, `Relational.Box`, `Relational.LTL`, `Relational.Basic` | matrices, the box combinators over them, LTL, reactive modules and their proof rules |
| [`LeanAI`](LeanAI) | `LeanAI`, `LeanAI.*` | the `ai_solve` tactic and its LLM backends |

Both are pinned to `leanprover/lean4:v4.34.0`. `Relational` requires cslib at
the same version, and gets Mathlib through it.

## Using them

From a git checkout:

```toml
[[require]]
name = "Relational"
git = "https://github.com/zeroth-research/reactor-lean"
rev = "<commit>"
subDir = "Relational"
```

From a local checkout:

```toml
[[require]]
name = "Relational"
path = "../reactor-lean/Relational"
```

The projects `verith` generates require both packages from git. Set
`REACTOR_LEAN` to a local checkout of this repository to make them
require it by path instead.

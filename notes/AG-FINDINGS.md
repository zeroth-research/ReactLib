# Review of the composition work and the route to assume-guarantee

Review of `69a3ed1` (split of `Relational.Basic` into `Basic`, `Module`,
`ProofRules`) and `a6d3468` (composition of TSs and reactive modules, the
`Common` library), and a plan for an assume-guarantee (AG) rule. Paper
references are to `~/papers/paper-formalizing-rm/`.

Since the review, the libraries were reorganised:

- `Relational.Circ` is removed.
- The old `ReactiveModule` (a deterministic, input-driven system) is now
  `ReactiveTS`, in `Relational/ReactiveTS.lean`.
- `Common.Module` (Alur–Henzinger atoms and modules) is now
  `Relational.Module`, in `Relational/Module.lean`, in `namespace Relational`.
  The `Common` library is gone.

Paths below are relative to `ReactLib/`.

## Status

| # | Finding | Status |
|---|---------|--------|
| 1 | `Module` clashes with Mathlib's `Module` | **fixed**: `namespace Relational` |
| 2 | Atoms cannot have state | **fixed** |
| 3 | Private variables are never written | **fixed** |
| 4 | Atoms are deterministic functions | open |
| 5 | `ReactiveTS.compose` is intersection, not parallel composition | open |
| 6 | Implicit `Name`/`Dom`; `compose` takes a proof | open |
| 7 | Name sets as lists with `∩ = ∅` | open |
| 8 | Off-by-one in `ReactiveTS.traces'` | open |
| 9 | Await acyclicity is atom-level only | open |

`69a3ed1` is a pure move: a sorted-line diff of old `Basic` against the new
three files shows only headers and imports changed.

## Findings

1. **Fixed — name clash with Mathlib.** A root-level `structure Module`
   collided with Mathlib's `Module`: importing it together with
   `Relational.Basic` failed with `environment already contains
   'Module.noConfusionType'`. `Val`, `Atom` and `Module` now live in
   `namespace Relational`, and `Relational.lean` imports them alongside the
   Mathlib-based modules.

2. **Fixed — atoms could not have state.** `read ∩ write = ∅` forbade
   `x' := x + 1`, so no counter or latch was expressible, and
   `await ∩ read = ∅` forbade reading `x` while awaiting `x'`. The cause was
   `update : Val (read ++ await) → Val write`, which gives one value per name.
   Now `update : Val read → Val await → Val write`
   (`Relational/Module.lean:30`), and only `await_write_disj` remains, as in
   Alur–Henzinger.

3. **Fixed — private variables were never written.** The atoms had to write
   exactly `intf`, so `priv` acted as an unconstrained hidden input. Now the
   atoms write exactly the controlled variables: `atoms_cov_ctrl` and
   `atoms_write_ctrl` over `intf ++ priv` (`Relational/Module.lean:73-74`).
   `Module.compose` re-proves both; disjointness of the controlled sets comes
   from `composable`.

4. **Atoms are deterministic functions** (`Relational/Module.lean:26, 30`).
   Alur–Henzinger atoms are left-total relations. With functions, a
   specification cannot be more nondeterministic than its implementation
   except through external variables, so refinement and AG are nearly
   vacuous. Fix: `init : Val await → Val write → Prop`,
   `update : Val read → Val await → Val write → Prop`, plus left-totality as a
   separate predicate or field (paper: `AtomicTrans.rel` / `total` in
   `lean/ReactiveModules/Common/AtomicTransition.lean`).

5. **`ReactiveTS.compose` is intersection, not parallel composition**
   (`Relational/ReactiveTS.lean:111`). Both systems own the whole `State` and
   are deterministic, so a joint step needs `A.update s l = B.update s l`. It
   means "both specs hold" and usually has no traces unless the systems agree.
   `TS.compose` (`Relational/Basic.lean:113`) is fine as language
   intersection over a shared global state; `ωTrace_compose` is the paper's
   `thm:langint`. What is missing is *ownership* (which part of the state a
   TS constrains) and *non-blocking*. Without them the composition can
   deadlock, the ω-trace set silently shrinks, and the circular AG rule is
   false: take `N₁ = N₂` with an empty language. `ReactiveTS.toTS` can never
   own a proper part of the state, so components need a different
   constructor (`TS.leftComp` in `notes/AG.lean`).

6. **Implicit `Name`/`Dom`; `compose` takes a proof**
   (`Relational/Module.lean:13-15, 96`). `Dom` is never inferable, hence
   `(Name := Name) (Dom := Dom)` everywhere. `Module.compose M₁ M₂ h` will be
   painful for AG, which juggles four composites and their proofs. The paper
   uses a total `parComp` on a `RawModule` plus a separate `WF` predicate
   (`lean/ReactiveModules/Relational/Model/Module.lean`). Proof fields also
   force `Module.ext` and `cases` gymnastics.

7. **Name sets as lists** (`Relational/Module.lean:33, 67-70, 90-92, 106`).
   `X ∩ Y = ∅` is `List.inter … = []`, and every use starts with
   `simp [List.eq_nil_iff_forall_not_mem]`. Commutativity holds only up to
   `Perm` (`Module.Equiv`, line 186), and nothing shows `Equiv` is a
   congruence for `compose` or for the future semantics. Use `Finset Name`,
   or a `Disjoint X Y := ∀ x ∈ X, x ∉ Y` predicate with membership-level
   equivalence (paper: `ListDisjoint` in `Common/Basic.lean`).
   `Val X := ∀ x ∈ X, Dom x` is workable but needs `proj`/`extend`/`ext`
   lemmas; for semantics a total valuation `∀ x, Dom x` as the state is much
   easier.

8. **Off-by-one in `ReactiveTS.traces'`** (`Relational/ReactiveTS.lean:37`,
   predates these commits). It requires `update_pre (inps i)` for all `i`,
   including `inps 0`, which is only the init input. It should be
   `update_pre (inps (i + 1))`. `traces` does not have this problem.

9. **Await acyclicity is atom-level only** (`Atom.Acyclic`,
   `Relational/Module.lean:40`). Alur–Henzinger's refinement clause 3 (spec
   awaits ⊆ impl awaits) needs the name-level await relation; define it and
   derive the atom-level form. `stateTraces_compose`
   (`Relational/Basic.lean:135`) being one-directional is correct as
   documented.

## Route to the AG rule

Build on the semantic `TS` layer, over a shared global state, with
`TS.compose` as intersection. Connect `Relational.Module` later through a
`Module.toTS`, once it has trace semantics and finding 4 is fixed.

Steps 0–3 are fully proved in `notes/AG.lean` (about 280 lines, imports only
`Relational.Basic`, no `sorry`, axioms `propext`, `Classical.choice`,
`Quot.sound`). It is not part of the `Relational` library yet; the next move
is to bring it in as `Relational/AG.lean`. Steps 4–6 are unchecked sketches.

**Step 0 — refinement and the non-circular rule (trivial).**
```lean
def TS.Refines (A B : TS State Label) : Prop := ∀ ss μs, A.ωTrace ss μs → B.ωTrace ss μs
theorem Refines.refl / Refines.trans
theorem compose_refines_left  : (A.compose B).Refines A
theorem Refines.compose : A.Refines A' → B.Refines B' → (A.compose B).Refines (A'.compose B')
theorem ag_noncircular (h₁ : M₁.Refines N₁) (h₂ : (N₁.compose M₂).Refines N₂) :
    (M₁.compose M₂).Refines (N₁.compose N₂)
```

**Step 1 — finite executions; safety is free when the whole state is observed.**
```lean
def FinExec (ts : TS State Label) (n : Nat) (ss μs) : Prop :=
  ts.start (ss.get 0) ∧ ∀ i, i < n → ts.Tr (ss.get i) (μs.get i) (ss.get (i+1))
theorem ωTrace_iff_finExec : ts.ωTrace ss μs ↔ ∀ n, ts.FinExec n ss μs
theorem finExec_compose : (A.compose B).FinExec n ss μs ↔ A.FinExec n ss μs ∧ B.FinExec n ss μs
def PrefixRefines (A B) : Prop := ∀ n ss μs, A.FinExec n ss μs → B.FinExec n ss μs
theorem PrefixRefines.refines : A.PrefixRefines B → A.Refines B
```

**Step 2 — ownership, non-blocking, circular AG without awaits.**
```lean
structure Owns (A : TS State Label) (π : State → P) : Prop where
  start : ∀ s t, A.start s → π s = π t → A.start t
  step  : ∀ s l s' t', A.Tr s l s' → π s' = π t' → A.Tr s l t'
structure Enabled (A : TS State Label) : Prop where
  start : ∃ s, A.start s
  step  : ∀ s l, ∃ s', A.Tr s l s'
theorem ag_circular_prefix (π₁ : State → P₁) (π₂ : State → P₂)
    (glue : ∀ a b, ∃ c, π₁ c = π₁ a ∧ π₂ c = π₂ b)
    (hM₁ : M₁.Owns π₁) (hN₁ : N₁.Owns π₁) (hM₂ : M₂.Owns π₂) (hN₂ : N₂.Owns π₂)
    (eN₁ : N₁.Enabled) (eN₂ : N₂.Enabled)
    (p₁ : (M₁.compose N₂).PrefixRefines N₁) (p₂ : (N₁.compose M₂).PrefixRefines N₂) :
    (M₁.compose M₂).PrefixRefines (N₁.compose N₂)
```
Induction on `n`. For the `N₁` step, take any `N₂` step (by `Enabled`), glue
its π₂-part with the real successor's π₁-part, apply `p₁` to the modified
prefix, and transfer the step back with `N₁.Owns π₁`.

**Step 3 — ω-trace premises (Alur–Henzinger's form).**
```lean
theorem Enabled.compose … (hA : A.Owns π₁) (hB : B.Owns π₂) (eA : A.Enabled) (eB : B.Enabled) :
    (A.compose B).Enabled
theorem Enabled.finExec_extends (eA : A.Enabled) (h : A.FinExec n ss μs) :
    ∃ ss', A.ωTrace ss' μs ∧ ∀ i, i ≤ n → ss'.get i = ss.get i      -- uses choice
theorem Refines.prefixRefines (eA : A.Enabled) : A.Refines B → A.PrefixRefines B
theorem assume_guarantee … (eM₁ eM₂ eN₁ eN₂ : Enabled)
    (p₁ : (M₁.compose N₂).Refines N₁) (p₂ : (N₁.compose M₂).Refines N₂) :
    (M₁.compose M₂).Refines (N₁.compose N₂)
```
`Enabled` quantifies over all states and labels; it can later be weakened to
reachable states.

**Step 4 — bridge from `Relational.Module`** (needs finding 4 first). With the
state `σ := ∀ x : Name, Dom x` and `Label := Unit`:
```lean
def Atom.holds (a) (s s' : σ) : Prop := a.update (restrict s a.read) (restrict s' a.await) (restrict s' a.write)
def Module.toTS (M) : TS σ Unit    -- Tr s _ s' := ∀ a ∈ M.atoms, a.holds s s'; start similarly with init
theorem Module.ωTrace_compose : (M₁.compose M₂ h).toTS.ωTrace ss μs ↔ M₁.toTS.ωTrace ss μs ∧ M₂.toTS.ωTrace ss μs
theorem Module.toTS_owns (hMoore : ∀ a ∈ M.atoms, a.await = []) : M.toTS.Owns (fun s => restrict s (M.intf ++ M.priv))
theorem Module.toTS_enabled   -- from left-totality of atoms + acyclicity (topological firing order)
```
`glue` follows from `composable` (disjoint controlled sets). With these,
Step 3 gives AG for await-free modules with all variables observed.
`toTS_enabled` with awaits needs a topological sort of the atoms: medium
effort (paper: `Relational/Model/FlatTotal.lean`).

**Step 5 — the hard step: awaits, i.e. the real Alur–Henzinger rule.**
`Owns` fails for an atom that awaits the partner's new values, so the
induction must go variable by variable inside a round, along one linear order
compatible with the await orders of all four modules.

- It needs an extra hypothesis. With trace inclusion alone the circular rule
  is unsound: paper `thm:ag-sem` / `ex:ag-wide`, four memoryless Boolean
  modules with pairwise acyclic composites that do not merge.
- The fix is Alur–Henzinger's Def. 3(3) await clause (spec awaits ⊆ impl
  awaits on observables), or more generally "the union of the four await
  relations is acyclic" (`thm:ag-union`).
- The abstract skeleton is `cat_ag` over prefix systems: if at each sub-step
  one of `G₁`, `G₂` is receptive, then `A₁∧G₂ ≤ G₁` and `G₁∧A₂ ≤ G₂` give
  `A₁∧A₂ ≤ G₁∧G₂`. About 130 lines with no Mathlib; ports verbatim.
- The hard part is instantiating it: defining partial-round prefixes, showing
  each module's behaviour on them is restriction-closed and extendable, and
  lifting whole-round premises to partial rounds. In the paper's Lean that is
  `AHPartial.lean` (1307 lines) plus `AGAlurHenzinger.lean` (1296 lines).

**Step 6 — hiding** (private variables, refinement as projected trace
inclusion). The second hard step, independent of Step 5. Prefix containment
no longer implies trace containment; it needs König's lemma and finite
domains for the spec's private variables (paper `lem:safety`(2), with a
counterexample when they are infinite), and Alur–Henzinger's scoping side
conditions. Defer it: keep private variables observable first.

**Suggested order:** bring in Steps 0–3 as `Relational/AG.lean`; fix
finding 4 and do Step 4; then decide whether Step 5 or 6 is worth it.

## Paper material to reuse

Under `~/papers/paper-formalizing-rm/`:

- `lean/Explore/Common/PrefixSystem.lean`: `RMCat.PrefixSys.cat_ag`, the
  abstract circular AG; self-contained, the skeleton for Step 5. Paper side:
  `notes/cat/thm/cat-ag.tex`, `notes/cat/def/prefixsys.tex`.
- `lean/ReactiveModules/Relational/AG/AGAlurHenzinger.lean`: `AGOrder`
  (around line 315), the AH99 round induction over an abstract acyclic order
  containing the four await relations. `AG/AHPartial.lean`: partial-round run
  constructions. `AG/AGUnion.lean`, `AG/AGStrong.lean`: final theorems
  (`assumeGuarantee_union`, `RawModule.assumeGuarantee`, `AGStrongHyps`).
- `lean/ReactiveModules/Relational/AG/Safety.lean`: `tracePrefix_extends`,
  `trace_of_prefixes` (König), for Step 6.
- `lean/ReactiveModules/Relational/Intersection/LangIntersection.lean`:
  `langInt`, the analogue of `ωTrace_compose` with hiding.
- `lean/ReactiveModules/Relational/Refinement/ParFunctor.lean`,
  `Refinement/SynRefinement.lean`: precongruence, `SynRefines`, `Refines`.
- Data-model templates: `lean/ReactiveModules/Common/Basic.lean` (`Val`,
  `proj`, `extend`, `ListDisjoint`), `Common/AtomicTransition.lean`
  (relational left-total atoms), `Relational/Model/Module.lean` (`RawModule`
  + `WF`, total `parComp`), `Relational/Model/FlatTotal.lean` (topological
  sort, totality).
- Statements and pitfalls: `relational/assume-guarantee.tex`,
  `relational/thm/ag.tex`, `relational/thm/ag-sem.tex`,
  `relational/thm/ag-union.tex`, `relational/cor/ag-ah99.tex`,
  `relational/lem/safety.tex`, `relational/ag-ah99-note.tex`;
  `reports/assume-guarantee.md` (rule-to-Lean table, the missed
  scoping/pairing hypothesis); `REFINEMENT.md` (definitions of ⊑, ⪯_S);
  `AH99-TRANSCRIPT.md` lines ~490 (Def. 3), ~690 (Def. 6), 764–870 (Prop. 5
  with proof); `lean/ReactiveModules/Relational/AG/DESIGN.md` (rejected
  alternatives).
- The root `AG-CT-REPORT.md` covers only the probabilistic/ct-scheduler rule
  and is not relevant here.

The paper's Lean uses the Lean module system and separate old/new names
(`List (Var × Var)`), so its proofs are a guide rather than a copy-paste
port. Only `PrefixSystem.lean` ports unchanged.

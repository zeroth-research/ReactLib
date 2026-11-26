import Relational.Basic
import Relational.Module
import Mathlib.Data.Finset.Pi

/-!
  The semantics of a reactive module (`Relational.Module`): rounds, runs and
  traces.

  A state gives a value to every name (`State Dom`). In the initial round
  every atom chooses initial values of the variables it writes, given the
  initial values of those it awaits (`Module.InitRound`). In an update round
  every atom chooses new values of the variables it writes, given the old
  values of those it reads and the new values of those it awaits
  (`Module.UpdateRound`). The environment chooses the external variables:
  rounds do not constrain them, nor any name outside the module.

  A run is an initial round followed by update rounds (`Module.Run`); it is
  an ω-trace of the module's transition system `Module.toTS`. A trace is the
  observable part of a run, the interface and external variables
  (`Module.Trace`).
-/

namespace Relational

universe u

variable {Name : Type} {Dom : Name → Type u}

/-- A state: a value for every name. -/
abbrev State (Dom : Name → Type u) := ∀ x, Dom x

/-- The part of the state `s` on the names `X`. -/
abbrev State.restrict (s : State Dom) (X : Finset Name) : Val Dom X :=
  X.restrict s

@[simp] theorem State.restrict_apply (s : State Dom) (X : Finset Name) (x : X) :
    s.restrict X x = s x := rfl

/-! ### Rounds -/

/-- The atom `A` initialises the state `s`: the values in `s` of the
    variables `A` writes are allowed by those of the variables it awaits. -/
def Atom.Init (A : Atom Dom) (s : State Dom) : Prop :=
  A.init (s.restrict A.await) (s.restrict A.write)

/-- The atom `A` updates the state `s` to `s'`: the values in `s'` of the
    variables `A` writes are allowed by the values in `s` of those it reads
    and the values in `s'` of those it awaits. -/
def Atom.Update (A : Atom Dom) (s s' : State Dom) : Prop :=
  A.update (s.restrict A.read) (s'.restrict A.await) (s'.restrict A.write)

/-- The initial round of `M` gives the state `s`: every atom initialises it. -/
def Module.InitRound (M : Module Dom) (s : State Dom) : Prop :=
  ∀ A ∈ M.atoms, A.Init s

/-- An update round of `M` takes the state `s` to `s'`: every atom updates
    `s` to `s'`. -/
def Module.UpdateRound (M : Module Dom) (s s' : State Dom) : Prop :=
  ∀ A ∈ M.atoms, A.Update s s'

/-- An atom's initial round depends only on the variables it awaits and
    writes. -/
theorem Atom.Init.congr {A : Atom Dom} {t t' : State Dom}
    (ha : ∀ x ∈ A.await, t x = t' x) (hw : ∀ x ∈ A.write, t x = t' x)
    (h : A.Init t) : A.Init t' := by
  have e₁ : t.restrict A.await = t'.restrict A.await := by
    funext ⟨x, hx⟩; exact ha x hx
  have e₂ : t.restrict A.write = t'.restrict A.write := by
    funext ⟨x, hx⟩; exact hw x hx
  simpa [Atom.Init, e₁, e₂] using h

/-- An atom's update round depends only on the old values of the variables
    it reads and the new values of those it awaits and writes. -/
theorem Atom.Update.congr {A : Atom Dom} {s s' t t' : State Dom}
    (hr : ∀ x ∈ A.read, s x = s' x)
    (ha : ∀ x ∈ A.await, t x = t' x) (hw : ∀ x ∈ A.write, t x = t' x)
    (h : A.Update s t) : A.Update s' t' := by
  have e₀ : s.restrict A.read = s'.restrict A.read := by
    funext ⟨x, hx⟩; exact hr x hx
  have e₁ : t.restrict A.await = t'.restrict A.await := by
    funext ⟨x, hx⟩; exact ha x hx
  have e₂ : t.restrict A.write = t'.restrict A.write := by
    funext ⟨x, hx⟩; exact hw x hx
  simpa [Atom.Update, e₀, e₁, e₂] using h

section Locality

variable [DecidableEq Name]

theorem Module.ctrl_subset_vars (M : Module Dom) : M.ctrl ⊆ M.vars := by
  intro x
  simp only [Module.ctrl, Module.vars, Finset.mem_union]
  tauto

/-- An initial round of a well-formed module depends only on the variables
    of the module. -/
theorem Module.WF.initRound_congr {M : Module Dom} (hM : M.WF) {s t : State Dom}
    (h : ∀ x ∈ M.vars, s x = t x) (hs : M.InitRound s) : M.InitRound t :=
  fun A hA => (hs A hA).congr (fun x hx => h x (hM.atoms_await_vars A hA hx))
    (fun x hx => h x (M.ctrl_subset_vars (hM.atoms_write_ctrl A hA hx)))

/-- An update round of a well-formed module depends only on the variables
    of the module. -/
theorem Module.WF.updateRound_congr {M : Module Dom} (hM : M.WF) {s s' t t' : State Dom}
    (h : ∀ x ∈ M.vars, s x = t x) (h' : ∀ x ∈ M.vars, s' x = t' x)
    (hs : M.UpdateRound s s') : M.UpdateRound t t' :=
  fun A hA => (hs A hA).congr (fun x hx => h x (hM.atoms_read_vars A hA hx))
    (fun x hx => h' x (hM.atoms_await_vars A hA hx))
    (fun x hx => h' x (M.ctrl_subset_vars (hM.atoms_write_ctrl A hA hx)))

end Locality

/-! ### Runs -/

/-- The transition system of `M`: its states are `State Dom`, its initial
    states those of an initial round, its transitions update rounds. It has
    a single label. -/
def Module.toTS (M : Module Dom) : TS (State Dom) Unit where
  Tr s _ s' := M.UpdateRound s s'
  start := {s | M.InitRound s}

/-- A run of `M`: an initial round followed by update rounds. -/
def Module.Run (M : Module Dom) (ss : Cslib.ωSequence (State Dom)) : Prop :=
  M.InitRound (ss 0) ∧ ∀ i, M.UpdateRound (ss i) (ss (i + 1))

/-- The runs of `M` are the ω-traces of its transition system. -/
theorem Module.run_iff_ωTrace (M : Module Dom) (ss : Cslib.ωSequence (State Dom))
    (μs : Cslib.ωSequence Unit) : M.Run ss ↔ M.toTS.ωTrace ss μs :=
  Iff.rfl

/-- A run of `M` with `n` update rounds: the states `ss 0, …, ss n`. Later
    states are irrelevant. -/
def Module.FinRun (M : Module Dom) (n : Nat) (ss : Nat → State Dom) : Prop :=
  M.InitRound (ss 0) ∧ ∀ i < n, M.UpdateRound (ss i) (ss (i + 1))

theorem Module.Run.finRun {M : Module Dom} {ss : Cslib.ωSequence (State Dom)}
    (h : M.Run ss) (n : Nat) : M.FinRun n ss :=
  ⟨h.1, fun i _ => h.2 i⟩

/-- A sequence all of whose prefixes are finite runs is a run. -/
theorem Module.Run.of_finRun {M : Module Dom} {ss : Cslib.ωSequence (State Dom)}
    (h : ∀ n, M.FinRun n ss) : M.Run ss :=
  ⟨(h 0).1, fun i => (h (i + 1)).2 i (Nat.lt_succ_self i)⟩

/-! ### Traces -/

section Traces

variable [DecidableEq Name]

/-- The observable variables of `M`: its interface and external variables. -/
def Module.obs (M : Module Dom) : Finset Name := M.intf ∪ M.extl

/-- `ts` is a trace of `M`: it agrees with a run of `M` on the observable
    variables. Only the observable part of `ts` matters (`Module.Trace.congr`). -/
def Module.Trace (M : Module Dom) (ts : Cslib.ωSequence (State Dom)) : Prop :=
  ∃ ss, M.Run ss ∧ ∀ i, ∀ x ∈ M.obs, ss i x = ts i x

theorem Module.Run.trace {M : Module Dom} {ss} (h : M.Run ss) : M.Trace ss :=
  ⟨ss, h, fun _ _ _ => rfl⟩

theorem Module.Trace.congr {M : Module Dom} {ts ts'} (h : M.Trace ts)
    (hobs : ∀ i, ∀ x ∈ M.obs, ts i x = ts' i x) : M.Trace ts' := by
  obtain ⟨ss, hrun, hss⟩ := h
  exact ⟨ss, hrun, fun i x hx => (hss i x hx).trans (hobs i x hx)⟩

/-- `ts` is a trace prefix of `M` of length `n + 1`: its states `0, …, n`
    agree with a finite run of `M` on the observable variables. These are
    Alur and Henzinger's traces, which are finite. -/
def Module.FinTrace (M : Module Dom) (n : Nat) (ts : Nat → State Dom) : Prop :=
  ∃ ss, M.FinRun n ss ∧ ∀ i ≤ n, ∀ x ∈ M.obs, ss i x = ts i x

theorem Module.Trace.finTrace {M : Module Dom} {ts : Cslib.ωSequence (State Dom)}
    (h : M.Trace ts) (n : Nat) : M.FinTrace n ts := by
  obtain ⟨ss, hrun, hss⟩ := h
  exact ⟨ss, hrun.finRun n, fun i _ x hx => hss i x hx⟩

end Traces

/-! ### Composition -/

section Compose

variable [DecidableEq Name]

theorem Module.initRound_compose (M₁ M₂ : Module Dom) (s : State Dom) :
    (M₁.compose M₂).InitRound s ↔ M₁.InitRound s ∧ M₂.InitRound s := by
  simp [Module.InitRound, Module.compose, or_imp, forall_and]

theorem Module.updateRound_compose (M₁ M₂ : Module Dom) (s s' : State Dom) :
    (M₁.compose M₂).UpdateRound s s' ↔ M₁.UpdateRound s s' ∧ M₂.UpdateRound s s' := by
  simp [Module.UpdateRound, Module.compose, or_imp, forall_and]

/-- The runs of a composition are exactly the runs common to both
    components. -/
theorem Module.run_compose (M₁ M₂ : Module Dom) (ss : Cslib.ωSequence (State Dom)) :
    (M₁.compose M₂).Run ss ↔ M₁.Run ss ∧ M₂.Run ss := by
  simp only [Module.Run, Module.initRound_compose, Module.updateRound_compose, forall_and]
  tauto

/-- The transition system of a composition has exactly the ω-traces common
    to the transition systems of the components. -/
theorem Module.ωTrace_toTS_compose (M₁ M₂ : Module Dom) (ss : Cslib.ωSequence (State Dom))
    (μs : Cslib.ωSequence Unit) :
    (M₁.compose M₂).toTS.ωTrace ss μs ↔ (M₁.toTS.compose M₂.toTS).ωTrace ss μs := by
  rw [TS.ωTrace_compose, ← Module.run_iff_ωTrace, ← Module.run_iff_ωTrace,
    ← Module.run_iff_ωTrace]
  exact Module.run_compose M₁ M₂ ss

/-- The observable variables of a component are observable in the
    composition. -/
theorem Module.obs_subset_compose_left (M₁ M₂ : Module Dom) :
    M₁.obs ⊆ (M₁.compose M₂).obs := by
  intro x
  simp only [Module.obs, Module.compose, Finset.mem_union, Finset.mem_sdiff]
  tauto

theorem Module.obs_subset_compose_right (M₁ M₂ : Module Dom) :
    M₂.obs ⊆ (M₁.compose M₂).obs := by
  intro x
  simp only [Module.obs, Module.compose, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- A trace of a composition is a trace of both components. The converse
    holds for well-formed composable modules (`Module.Trace.compose`, in
    `Relational.AG.Traces`). -/
theorem Module.Trace.of_compose {M₁ M₂ : Module Dom} {ts}
    (h : (M₁.compose M₂).Trace ts) : M₁.Trace ts ∧ M₂.Trace ts := by
  obtain ⟨ss, hrun, hss⟩ := h
  obtain ⟨h₁, h₂⟩ := (Module.run_compose M₁ M₂ ss).mp hrun
  exact ⟨⟨ss, h₁, fun i x hx => hss i x (Module.obs_subset_compose_left M₁ M₂ hx)⟩,
    ⟨ss, h₂, fun i x hx => hss i x (Module.obs_subset_compose_right M₁ M₂ hx)⟩⟩

end Compose

/-! ### Equivalent modules -/

section Equiv

variable [DecidableEq Name]

omit [DecidableEq Name] in
/-- Equivalent modules have the same runs. -/
theorem Module.Equiv.run_iff {M N : Module Dom} (h : M.Equiv N)
    (ss : Cslib.ωSequence (State Dom)) : M.Run ss ↔ N.Run ss := by
  simp only [Module.Run, Module.InitRound, Module.UpdateRound, h.2.2.2.mem_iff]

/-- Equivalent modules have the same traces. -/
theorem Module.Equiv.trace_iff {M N : Module Dom} (h : M.Equiv N)
    (ts : Cslib.ωSequence (State Dom)) : M.Trace ts ↔ N.Trace ts := by
  simp only [Module.Trace, Module.obs, h.1, h.2.1, h.run_iff]

end Equiv

end Relational

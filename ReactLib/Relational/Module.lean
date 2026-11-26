import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation

/-!
  Reactive modules in the style of Alur and Henzinger: atoms over named
  variables, modules built from atoms, their parallel composition, and its
  commutativity and associativity.

  A `Module` is plain data and `Module.compose` is total. Well-formedness is
  the separate predicate `Module.WF`, preserved by composing `Composable`
  modules (`Module.WF.compose`).
-/

namespace Relational

universe u

-- the type of names
variable {Name : Type}
-- domain for names (mapping names to their types)
variable {Dom : Name → Type u}

/-- A valuation of the names `X` (a state, or a part of one): a function on
    the elements of `X`, as in Mathlib's `Finset.restrict`. -/
abbrev Val (Dom : Name → Type u) (X : Finset Name) := (x : X) → Dom x

structure Atom (Dom : Name → Type u) where
  -- sets of names, *not* variables with different versions
  await : Finset Name
  read : Finset Name
  write : Finset Name

  -- the initial values of `write` that the new values of `await` allow
  init : Val Dom await → Val Dom write → Prop
  -- the new values of `write` that the old values of `read` and the new
  -- values of `await` allow. The two valuations are separate, so a name may
  -- be both read and awaited, and an atom may read the variables it writes.
  update : Val Dom read → Val Dom await → Val Dom write → Prop

  -- an atom never blocks: for all inputs, reachable or not, some values of
  -- `write` are allowed. Unlike AH's executable atoms, an atom may allow
  -- infinitely many; limit closure of traces needs finite branching
  -- (`Module.FinBranching`, `Relational.AG.Safety`)
  init_total : ∀ a, ∃ w, init a w
  update_total : ∀ r a, ∃ w, update r a w

  -- an atom does not await the new value of a variable it writes
  await_write_disj : Disjoint await write

/-- A deterministic atom: `init` and `update` are functions. It is left-total
    by construction. -/
def Atom.ofFun (await read write : Finset Name)
    (init : Val Dom await → Val Dom write)
    (update : Val Dom read → Val Dom await → Val Dom write)
    (await_write_disj : Disjoint await write) : Atom Dom where
  await := await
  read := read
  write := write
  init a w := w = init a
  update r a w := w = update r a
  init_total a := ⟨init a, rfl⟩
  update_total r a := ⟨update r a, rfl⟩
  await_write_disj := await_write_disj

/-! ### Await dependencies -/

/-- `a` awaits `b`: `a` awaits (uses the new value, in the same round, of) a
    variable that `b` writes. -/
def Atom.awaits (a b : Atom Dom) : Prop :=
  ∃ x ∈ a.await, x ∈ b.write

/-- The await dependencies among the atoms `As` have no cycle. Only membership
    in `As` matters, not the order or multiplicity of the atoms. -/
def Atom.Acyclic (As : List (Atom Dom)) : Prop :=
  ∀ a ∈ As, ¬ Relation.TransGen (fun a b => a ∈ As ∧ b ∈ As ∧ a.awaits b) a a

theorem Atom.Acyclic.of_subset {As Bs : List (Atom Dom)}
    (hsub : As ⊆ Bs) (h : Atom.Acyclic Bs) : Atom.Acyclic As :=
  -- every edge among `As` is an edge among `Bs`
  fun a ha hcyc => h a (hsub ha)
    (Relation.TransGen.mono (fun _ _ h => ⟨hsub h.1, hsub h.2.1, h.2.2⟩) _ _ hcyc)

theorem Atom.Acyclic.congr {As Bs : List (Atom Dom)}
    (hmem : ∀ a, a ∈ As ↔ a ∈ Bs) (h : Atom.Acyclic Bs) : Atom.Acyclic As :=
  h.of_subset fun _ ha => (hmem _).mp ha

/-- The name-level await relation of the atoms `As`: in a round, the new value
    of `x` depends on the new value of `y`, because some atom writes `x` and
    awaits `y`. -/
def Atom.dependsOn (As : List (Atom Dom)) (x y : Name) : Prop :=
  ∃ A ∈ As, x ∈ A.write ∧ y ∈ A.await

/-- No name (transitively) depends on itself within a round. -/
def Atom.NameAcyclic (As : List (Atom Dom)) : Prop :=
  ∀ x, ¬ Relation.TransGen (Atom.dependsOn As) x x

/-- A chain of atoms, each awaiting the next, is a chain of names, each
    depending on the next. -/
private theorem Atom.dependsOn_of_awaits {As : List (Atom Dom)} {a b : Atom Dom}
    (h : Relation.TransGen (fun a b => a ∈ As ∧ b ∈ As ∧ a.awaits b) a b) :
    ∃ z ∈ a.await, ∀ w ∈ b.await, Relation.TransGen (Atom.dependsOn As) z w := by
  induction h with
  | single h =>
    obtain ⟨-, hb, z, hz, hzb⟩ := h
    exact ⟨z, hz, fun w hw => .single ⟨_, hb, hzb, hw⟩⟩
  | tail _ h ih =>
    obtain ⟨z₀, hz₀, ih⟩ := ih
    obtain ⟨-, hc, z, hz, hzc⟩ := h
    exact ⟨z₀, hz₀, fun w hw => .tail (ih z hz) ⟨_, hc, hzc, hw⟩⟩

/-- A chain of names, each depending on the next, is a chain of atoms, each
    awaiting the next. -/
private theorem Atom.awaits_of_dependsOn {As : List (Atom Dom)} {x y : Name}
    (h : Relation.TransGen (Atom.dependsOn As) x y) :
    ∃ A ∈ As, x ∈ A.write ∧ ∃ B ∈ As, y ∈ B.await ∧
      Relation.ReflTransGen (fun a b => a ∈ As ∧ b ∈ As ∧ a.awaits b) A B := by
  induction h with
  | single h =>
    obtain ⟨A, hA, hx, hy⟩ := h
    exact ⟨A, hA, hx, A, hA, hy, .refl⟩
  | tail _ h ih =>
    obtain ⟨A, hA, hx, B, hB, hy, hAB⟩ := ih
    obtain ⟨C, hC, hyC, hz⟩ := h
    exact ⟨A, hA, hx, C, hC, hz, hAB.tail ⟨hB, hC, _, hy, hyC⟩⟩

/-- The atoms have no await cycle iff the names have no dependency cycle. -/
theorem Atom.acyclic_iff_nameAcyclic {As : List (Atom Dom)} :
    Atom.Acyclic As ↔ Atom.NameAcyclic As := by
  constructor
  · intro h x hx
    obtain ⟨A, hA, hxA, B, -, hxB, hAB⟩ := Atom.awaits_of_dependsOn hx
    -- `B` awaits `x`, which `A` writes: close the cycle
    exact h A hA (Relation.TransGen.tail' hAB ⟨by grind, hA, x, hxB, hxA⟩)
  · intro h a _ hcyc
    obtain ⟨z, hz, hdep⟩ := Atom.dependsOn_of_awaits hcyc
    exact h z (hdep z hz)

/-! ### Modules -/

variable [DecidableEq Name]

@[ext]
structure Module (Dom : Name → Type u) where
  intf : Finset Name
  extl : Finset Name
  priv : Finset Name

  atoms : List (Atom Dom)

/-- The controlled variables: those the atoms write. -/
def Module.ctrl (M : Module Dom) : Finset Name := M.intf ∪ M.priv

/-- All variables of a module. -/
def Module.vars (M : Module Dom) : Finset Name := M.extl ∪ M.priv ∪ M.intf

open Function in
/-- A well-formed module. -/
structure Module.WF (M : Module Dom) : Prop where
  intf_extl_disj : Disjoint M.intf M.extl
  intf_priv_disj : Disjoint M.intf M.priv
  extl_priv_disj : Disjoint M.extl M.priv
  atoms_pairwise_disj : M.atoms.Pairwise (Disjoint on Atom.write)

  -- the atoms write exactly the controlled (interface and private) variables
  atoms_cov_ctrl : ∀ x ∈ M.ctrl, ∃ A ∈ M.atoms, x ∈ A.write
  atoms_write_ctrl : ∀ A ∈ M.atoms, A.write ⊆ M.ctrl
  atoms_read_vars : ∀ A ∈ M.atoms, A.read ⊆ M.vars
  atoms_await_vars : ∀ A ∈ M.atoms, A.await ⊆ M.vars

  -- the atoms can be executed in some order: no atom (transitively) awaits
  -- itself
  atoms_acyclic : Atom.Acyclic M.atoms

/-- `M₁` and `M₂` can be composed: their interfaces are disjoint, neither
    touches the other's private variables, and their atoms together can be
    executed in some order. -/
structure Module.Composable (M₁ M₂ : Module Dom) : Prop where
  intf_disj : Disjoint M₁.intf M₂.intf
  priv₁_disj : Disjoint M₁.priv M₂.vars
  priv₂_disj : Disjoint M₂.priv M₁.vars
  acyclic : Atom.Acyclic (M₁.atoms ++ M₂.atoms)

/-- Parallel composition. It is defined for all modules; it is well-formed
    when the modules are and are `Composable` (`Module.WF.compose`). -/
def Module.compose (M₁ M₂ : Module Dom) : Module Dom where
  intf := M₁.intf ∪ M₂.intf
  extl := (M₁.extl ∪ M₂.extl) \ (M₁.intf ∪ M₂.intf)
  priv := M₁.priv ∪ M₂.priv
  atoms := M₁.atoms ++ M₂.atoms

/-- The variables of a composition are those of its components. -/
theorem Module.vars_compose (M₁ M₂ : Module Dom) :
    (M₁.compose M₂).vars = M₁.vars ∪ M₂.vars := by
  ext x
  simp only [Module.vars, Module.compose, Finset.mem_union, Finset.mem_sdiff]
  grind

theorem Module.WF.compose {M₁ M₂ : Module Dom} (h₁ : M₁.WF) (h₂ : M₂.WF)
    (hc : M₁.Composable M₂) : (M₁.compose M₂).WF := by
  obtain ⟨ie₁, ip₁, ep₁, pw₁, cov₁, wc₁, rv₁, av₁, _⟩ := h₁
  obtain ⟨ie₂, ip₂, ep₂, pw₂, cov₂, wc₂, rv₂, av₂, _⟩ := h₂
  obtain ⟨hi, hp₁, hp₂, hac⟩ := hc
  simp only [Module.ctrl, Module.vars, Finset.disjoint_left, Finset.subset_iff,
    Finset.mem_union] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hac⟩
  all_goals simp only [Module.compose, Module.ctrl, Module.vars, Finset.disjoint_left,
    Finset.subset_iff, Finset.mem_union, Finset.mem_sdiff, List.mem_append]
  · grind
  · grind
  · grind
  · rw [List.pairwise_append]
    refine ⟨pw₁, pw₂, fun a ha b hb => ?_⟩
    simp only [Function.onFun, Finset.disjoint_left]
    have := wc₁ a ha
    have := wc₂ b hb
    grind
  · intro x hx
    rcases hx with (hx | hx) | (hx | hx)
    · obtain ⟨A, hA, hw⟩ := cov₁ x (.inl hx); exact ⟨A, .inl hA, hw⟩
    · obtain ⟨A, hA, hw⟩ := cov₂ x (.inl hx); exact ⟨A, .inr hA, hw⟩
    · obtain ⟨A, hA, hw⟩ := cov₁ x (.inr hx); exact ⟨A, .inl hA, hw⟩
    · obtain ⟨A, hA, hw⟩ := cov₂ x (.inr hx); exact ⟨A, .inr hA, hw⟩
  · intro A hA x hx
    rcases hA with hA | hA
    · have := wc₁ A hA hx; grind
    · have := wc₂ A hA hx; grind
  · intro A hA x hx
    rcases hA with hA | hA
    · have := rv₁ A hA hx; grind
    · have := rv₂ A hA hx; grind
  · intro A hA x hx
    rcases hA with hA | hA
    · have := av₁ A hA hx; grind
    · have := av₂ A hA hx; grind

/-! ### Equivalence -/

/-- Modules are equivalent when they agree up to the order of their atoms. -/
def Module.Equiv (M N : Module Dom) : Prop :=
  M.intf = N.intf ∧ M.extl = N.extl ∧ M.priv = N.priv ∧ M.atoms.Perm N.atoms

omit [DecidableEq Name] in
theorem Module.Equiv.refl (M : Module Dom) : M.Equiv M :=
  ⟨rfl, rfl, rfl, .refl _⟩

omit [DecidableEq Name] in
theorem Module.Equiv.symm {M N : Module Dom} (h : M.Equiv N) : N.Equiv M :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

omit [DecidableEq Name] in
theorem Module.Equiv.trans {M N P : Module Dom} (h : M.Equiv N) (h' : N.Equiv P) :
    M.Equiv P :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
    h.2.2.2.trans h'.2.2.2⟩

/-- Equivalence is a congruence for composition. -/
theorem Module.Equiv.compose {M M' N N' : Module Dom} (hM : M.Equiv M')
    (hN : N.Equiv N') : (M.compose N).Equiv (M'.compose N') := by
  obtain ⟨i, e, p, a⟩ := hM
  obtain ⟨i', e', p', a'⟩ := hN
  exact ⟨by simp [Module.compose, i, i'], by simp [Module.compose, i, i', e, e'],
    by simp [Module.compose, p, p'], a.append a'⟩

theorem Module.Equiv.vars {M N : Module Dom} (h : M.Equiv N) : M.vars = N.vars := by
  simp [Module.vars, h.1, h.2.1, h.2.2.1]

theorem Module.Equiv.wf {M N : Module Dom} (h : M.Equiv N) (hM : M.WF) : N.WF := by
  obtain ⟨i, e, p, a⟩ := h
  have hmem : ∀ A, A ∈ N.atoms ↔ A ∈ M.atoms := fun A => a.mem_iff.symm
  have pw' := (a.pairwise_iff fun h => Disjoint.symm h).mp
    hM.atoms_pairwise_disj
  obtain ⟨ie, ip, ep, -, cov, wc, rv, av, ac⟩ := hM
  simp only [Module.ctrl, Module.vars, i, e, p] at *
  refine ⟨ie, ip, ep, pw', ?_, ?_, ?_, ?_, ac.congr hmem⟩
  · intro x hx
    obtain ⟨A, hA, hw⟩ := cov x hx
    exact ⟨A, (hmem A).mpr hA, hw⟩
  · exact fun A hA => wc A ((hmem A).mp hA)
  · exact fun A hA => rv A ((hmem A).mp hA)
  · exact fun A hA => av A ((hmem A).mp hA)

theorem Module.Equiv.composable {M M' N N' : Module Dom} (hM : M.Equiv M')
    (hN : N.Equiv N') (h : M.Composable N) : M'.Composable N' := by
  obtain ⟨hi, hp₁, hp₂, hac⟩ := h
  refine ⟨?_, ?_, ?_, hac.congr fun A => ?_⟩
  · rw [← hM.1, ← hN.1]; exact hi
  · rw [← hM.2.2.1, ← hN.vars]; exact hp₁
  · rw [← hN.2.2.1, ← hM.vars]; exact hp₂
  · simp only [List.mem_append, hM.2.2.2.mem_iff, hN.2.2.2.mem_iff]

/-! ### Commutativity -/

theorem Module.Composable.symm {M₁ M₂ : Module Dom}
    (h : M₁.Composable M₂) : M₂.Composable M₁ :=
  ⟨h.intf_disj.symm, h.priv₂_disj, h.priv₁_disj,
    h.acyclic.congr fun a => by simp [or_comm]⟩

/-- Composition is commutative up to the order of the atoms. -/
theorem Module.compose_comm (M₁ M₂ : Module Dom) :
    (M₁.compose M₂).Equiv (M₂.compose M₁) := by
  refine ⟨Finset.union_comm _ _, ?_, Finset.union_comm _ _, List.perm_append_comm⟩
  simp only [Module.compose, Finset.union_comm]

/-! ### Associativity -/

/-- Composition is associative. -/
theorem Module.compose_assoc (M₁ M₂ M₃ : Module Dom) :
    (M₁.compose M₂).compose M₃ = M₁.compose (M₂.compose M₃) := by
  ext x <;> simp only [Module.compose, Finset.mem_union, Finset.mem_sdiff,
    List.append_assoc] <;> grind

/-- Whenever `(M₁ ∥ M₂) ∥ M₃` is composable, so is `M₁ ∥ (M₂ ∥ M₃)`. -/
theorem Module.Composable.assoc {M₁ M₂ M₃ : Module Dom}
    (h₁₂ : M₁.Composable M₂) (h : (M₁.compose M₂).Composable M₃) :
    M₂.Composable M₃ ∧ M₁.Composable (M₂.compose M₃) := by
  obtain ⟨i₁₂, p₁₂, p₂₁, _⟩ := h₁₂
  obtain ⟨i, p, p', hac⟩ := h
  rw [Module.vars_compose] at p'
  have hac₂₃ : Atom.Acyclic (M₂.atoms ++ M₃.atoms) :=
    hac.of_subset fun a ha => by simp [Module.compose] at ha ⊢; grind
  have hac₁₂₃ : Atom.Acyclic (M₁.atoms ++ (M₂.compose M₃).atoms) :=
    hac.congr fun a => by simp [Module.compose]
  refine ⟨⟨?_, ?_, ?_, hac₂₃⟩, ⟨?_, ?_, ?_, hac₁₂₃⟩⟩
  all_goals
    try rw [Module.vars_compose]
    simp only [Module.compose, Finset.disjoint_left, Finset.mem_union] at *
    grind

/-- Whenever `M₁ ∥ (M₂ ∥ M₃)` is composable, so is `(M₁ ∥ M₂) ∥ M₃`. -/
theorem Module.Composable.assoc' {M₁ M₂ M₃ : Module Dom}
    (h₂₃ : M₂.Composable M₃) (h : M₁.Composable (M₂.compose M₃)) :
    M₁.Composable M₂ ∧ (M₁.compose M₂).Composable M₃ := by
  obtain ⟨i₂₃, p₂₃, p₃₂, _⟩ := h₂₃
  obtain ⟨i, p, p', hac⟩ := h
  rw [Module.vars_compose] at p
  have hac₁₂ : Atom.Acyclic (M₁.atoms ++ M₂.atoms) :=
    hac.of_subset fun a ha => by simp [Module.compose] at ha ⊢; grind
  have hac₁₂₃ : Atom.Acyclic ((M₁.compose M₂).atoms ++ M₃.atoms) :=
    hac.congr fun a => by simp [Module.compose]
  refine ⟨⟨?_, ?_, ?_, hac₁₂⟩, ⟨?_, ?_, ?_, hac₁₂₃⟩⟩
  all_goals
    try rw [Module.vars_compose]
    simp only [Module.compose, Finset.disjoint_left, Finset.mem_union] at *
    grind

end Relational

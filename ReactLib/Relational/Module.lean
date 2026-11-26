import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas

/-!
  Reactive modules in the style of Alur and Henzinger: atoms over named
  variables, modules built from atoms, their parallel composition, and its
  commutativity and associativity.
-/

namespace Relational

-- the type of names
variable {Name : Type 0} [DecidableEq Name]
-- domain for names (mapping names to their types)
variable {Dom : Name → Type u}
-- valuation of names (a state)
abbrev Val (X: List Name) := ∀ x ∈ X, Dom x

structure Atom where
  -- lists of names, *not* variables with different versions
  await: List Name
  read: List Name
  write: List Name

  init: (Val (Dom := Dom) await) -> (Val (Dom := Dom) write)
  update: (Val (Dom := Dom) (read ++ await)) -> (Val (Dom := Dom) write)

  await_write_disj: await ∩ write = ∅ 
  read_write_disj: read ∩ write = ∅ 
  await_read_disj: await ∩ read = ∅ 
/-- `a` awaits `b`: `a` reads, in the same round, a variable that `b` writes. -/
def Atom.awaits (a b : Atom (Name := Name) (Dom := Dom)) : Prop :=
  ∃ x ∈ a.await, x ∈ b.write

/-- The await dependencies among the atoms `As` have no cycle. Only membership
    in `As` matters, not the order or multiplicity of the atoms. -/
def Atom.Acyclic (As : List (Atom (Name := Name) (Dom := Dom))) : Prop :=
  ∀ a ∈ As, ¬ Relation.TransGen (fun a b => a ∈ As ∧ b ∈ As ∧ a.awaits b) a a

theorem Atom.Acyclic.of_subset {As Bs : List (Atom (Name := Name) (Dom := Dom))}
    (hsub : As ⊆ Bs) (h : Atom.Acyclic Bs) : Atom.Acyclic As := by
  intro a ha hcyc
  apply h a (hsub ha)
  -- every edge among `As` is an edge among `Bs`
  have : ∀ {x y}, Relation.TransGen (fun a b => a ∈ As ∧ b ∈ As ∧ a.awaits b) x y →
      Relation.TransGen (fun a b => a ∈ Bs ∧ b ∈ Bs ∧ a.awaits b) x y := by
    intro x y hxy
    induction hxy with
    | single h => exact .single ⟨hsub h.1, hsub h.2.1, h.2.2⟩
    | tail _ h ih => exact .tail ih ⟨hsub h.1, hsub h.2.1, h.2.2⟩
  exact this hcyc

theorem Atom.Acyclic.congr {As Bs : List (Atom (Name := Name) (Dom := Dom))}
    (hmem : ∀ a, a ∈ As ↔ a ∈ Bs) (h : Atom.Acyclic Bs) : Atom.Acyclic As :=
  h.of_subset fun _ ha => (hmem _).mp ha

structure Module where
  intf: List Name
  extl: List Name
  priv: List Name

  atoms: List (Atom (Name := Name) (Dom := Dom))

  intf_extl_disj: intf ∩ extl = ∅
  intf_priv_disj: intf ∩ priv = ∅
  extl_priv_disj: extl ∩  priv = ∅
  atoms_pairwise_disj: atoms.Pairwise fun a b => a.write ∩ b.write = ∅

  atoms_cov_intf: ∀ n ∈ intf, ∃ A ∈ atoms, n ∈ A.write
  intf_cov_atoms: ∀ A ∈ atoms, A.write ⊆ intf
  atoms_read_mod: ∀ A ∈ atoms, A.read ⊆ extl ∪ priv ∪ intf
  atoms_await_mod: ∀ A ∈ atoms, A.await ⊆ extl ∪ priv ∪ intf

  -- the atoms can be executed in some order: no atom (transitively) awaits
  -- itself
  atoms_acyclic: Atom.Acyclic atoms

/-- Two modules are equal when their fields are; the proof fields are
    irrelevant. -/
theorem Module.ext {M N : Module (Name := Name) (Dom := Dom)}
    (hi : M.intf = N.intf) (he : M.extl = N.extl) (hp : M.priv = N.priv)
    (ha : M.atoms = N.atoms) : M = N := by
  cases M; cases N; simp_all

def Module.composable (M₁ M₂ : Module (Name := Name) (Dom := Dom)): Prop :=
    M₁.intf ∩ M₂.intf = ∅ ∧
    (M₁.priv ∩ (M₂.priv ++ M₂.extl ++ M₂.intf) = ∅) ∧
    (M₂.priv ∩ (M₁.priv ++ M₁.extl ++ M₁.intf) = ∅) ∧
    -- the atoms of both modules together can be executed in some order
    Atom.Acyclic (M₁.atoms ++ M₂.atoms)

def Module.compose (M₁ M₂ : Module (Name := Name) (Dom := Dom)) (hcomp: M₁.composable M₂): Module (Name := Name) (Dom := Dom):=
  have h₁ := M₁.intf_extl_disj
  have h₂ := M₁.intf_priv_disj
  have h₃ := M₁.extl_priv_disj
  have h₄ := M₂.intf_extl_disj
  have h₅ := M₂.intf_priv_disj
  have h₆ := M₂.extl_priv_disj
  have hc := hcomp
  {
  intf := M₁.intf ++ M₂.intf
  extl := (M₁.extl ++ M₂.extl).removeAll (M₁.intf ++ M₂.intf)
  priv := M₁.priv ++ M₂.priv

  atoms := M₁.atoms ++ M₂.atoms

  intf_extl_disj := by
    simp [List.eq_nil_iff_forall_not_mem, List.removeAll] at *
    grind
  intf_priv_disj := by
    simp [List.eq_nil_iff_forall_not_mem, Module.composable] at *
    grind
  extl_priv_disj := by
    simp [List.eq_nil_iff_forall_not_mem, Module.composable, List.removeAll] at *
    grind
  atoms_pairwise_disj := by
    have p₁ := M₁.atoms_pairwise_disj
    have p₂ := M₂.atoms_pairwise_disj
    have w₁ := M₁.intf_cov_atoms
    have w₂ := M₂.intf_cov_atoms
    simp only [Module.composable] at hc
    rw [List.pairwise_append]
    refine ⟨p₁, p₂, fun a ha b hb => ?_⟩
    have wa := w₁ a ha
    have wb := w₂ b hb
    simp [List.eq_nil_iff_forall_not_mem, List.subset_def] at *
    grind
  atoms_cov_intf := by
    intro n hn
    simp only [List.mem_append] at hn ⊢
    rcases hn with hn | hn
    · obtain ⟨A, hA, hw⟩ := M₁.atoms_cov_intf n hn
      exact ⟨A, Or.inl hA, hw⟩
    · obtain ⟨A, hA, hw⟩ := M₂.atoms_cov_intf n hn
      exact ⟨A, Or.inr hA, hw⟩
  intf_cov_atoms := by
    intro A hA
    simp only [List.mem_append] at hA
    rcases hA with hA | hA
    · exact List.subset_append_of_subset_left _ (M₁.intf_cov_atoms A hA)
    · exact List.subset_append_of_subset_right _ (M₂.intf_cov_atoms A hA)
  atoms_read_mod := by
    intro A hA x hx
    simp only [List.mem_append] at hA
    rcases hA with hA | hA
    · have := M₁.atoms_read_mod A hA hx
      simp [List.removeAll] at this ⊢
      grind
    · have := M₂.atoms_read_mod A hA hx
      simp [List.removeAll] at this ⊢
      grind
  atoms_await_mod := by
    intro A hA x hx
    simp only [List.mem_append] at hA
    rcases hA with hA | hA
    · have := M₁.atoms_await_mod A hA hx
      simp [List.removeAll] at this ⊢
      grind
    · have := M₂.atoms_await_mod A hA hx
      simp [List.removeAll] at this ⊢
      grind
  atoms_acyclic := hcomp.2.2.2
  }

/-! ### Commutativity -/

theorem Module.composable_comm {M₁ M₂ : Module (Name := Name) (Dom := Dom)}
    (h : M₁.composable M₂) : M₂.composable M₁ := by
  obtain ⟨hi, hp₁, hp₂, hac⟩ := h
  refine ⟨?_, hp₂, hp₁, hac.congr fun a => by simp [or_comm]⟩
  simp [List.eq_nil_iff_forall_not_mem] at hi ⊢
  grind

/-- Modules are equivalent when their fields agree up to the order of the
    lists. -/
def Module.Equiv (M N : Module (Name := Name) (Dom := Dom)) : Prop :=
  M.intf.Perm N.intf ∧ M.extl.Perm N.extl ∧ M.priv.Perm N.priv ∧
  M.atoms.Perm N.atoms

/-- Composition is commutative: whenever `M₁ ∥ M₂` is defined, so is
    `M₂ ∥ M₁`, and the two are equivalent. -/
theorem Module.compose_comm {M₁ M₂ : Module (Name := Name) (Dom := Dom)}
    (h : M₁.composable M₂) :
    (M₁.compose M₂ h).Equiv (M₂.compose M₁ (Module.composable_comm h)) := by
  refine ⟨List.perm_append_comm, ?_, List.perm_append_comm, List.perm_append_comm⟩
  simp only [Module.compose, List.removeAll]
  exact (List.perm_append_comm.filter _).trans (by
    apply List.Perm.of_eq
    apply List.filter_congr
    intro x _
    simp [or_comm])

/-! ### Associativity -/

/-- Composition is associative: whenever `(M₁ ∥ M₂) ∥ M₃` is defined, so
    is `M₁ ∥ (M₂ ∥ M₃)`, and the two are equal. -/
theorem Module.composable_assoc {M₁ M₂ M₃ : Module (Name := Name) (Dom := Dom)}
    (h₁₂ : M₁.composable M₂) (h : (M₁.compose M₂ h₁₂).composable M₃) :
    ∃ h₂₃ : M₂.composable M₃, M₁.composable (M₂.compose M₃ h₂₃) := by
  have ⟨i₁₂, p₁₂, p₂₁, _⟩ := h₁₂
  have ⟨i, p, p', hac⟩ := h
  simp only [Module.compose] at i p p' hac
  have hac₂₃ : Atom.Acyclic (M₂.atoms ++ M₃.atoms) :=
    hac.of_subset fun a ha => by simp at ha ⊢; grind
  refine ⟨⟨?_, ?_, ?_, hac₂₃⟩, ?_, ?_, ?_, ?_⟩
  rotate_right
  · simp only [Module.compose]
    exact hac.congr fun a => by simp
  all_goals
    try simp only [Module.compose]
    simp [List.eq_nil_iff_forall_not_mem, List.removeAll] at i₁₂ p₁₂ p₂₁ i p p' ⊢
    grind

/-- The converse of `composable_assoc`. -/
theorem Module.composable_assoc' {M₁ M₂ M₃ : Module (Name := Name) (Dom := Dom)}
    (h₂₃ : M₂.composable M₃) (h : M₁.composable (M₂.compose M₃ h₂₃)) :
    ∃ h₁₂ : M₁.composable M₂, (M₁.compose M₂ h₁₂).composable M₃ := by
  have ⟨i₂₃, p₂₃, p₃₂, _⟩ := h₂₃
  have ⟨i, p, p', hac⟩ := h
  simp only [Module.compose] at i p p' hac
  have hac₁₂ : Atom.Acyclic (M₁.atoms ++ M₂.atoms) :=
    hac.of_subset fun a ha => by simp at ha ⊢; grind
  refine ⟨⟨?_, ?_, ?_, hac₁₂⟩, ?_, ?_, ?_, ?_⟩
  rotate_right
  · simp only [Module.compose]
    exact hac.congr fun a => by simp
  all_goals
    try simp only [Module.compose]
    simp [List.eq_nil_iff_forall_not_mem, List.removeAll] at i₂₃ p₂₃ p₃₂ i p p' ⊢
    grind

theorem Module.compose_assoc {M₁ M₂ M₃ : Module (Name := Name) (Dom := Dom)}
    (h₁₂ : M₁.composable M₂) (h : (M₁.compose M₂ h₁₂).composable M₃)
    (h₂₃ : M₂.composable M₃) (h' : M₁.composable (M₂.compose M₃ h₂₃)) :
    (M₁.compose M₂ h₁₂).compose M₃ h = M₁.compose (M₂.compose M₃ h₂₃) h' := by
  apply Module.ext <;> simp only [Module.compose, List.append_assoc]
  simp only [List.removeAll, List.filter_append, List.filter_filter, List.append_assoc]
  -- both sides filter each `extl` by "not in any interface"
  congr 1 <;> try congr 1
  all_goals first
    | (funext x; simp; grind)
    | (apply List.filter_congr; intro x _; simp; try grind)

end Relational

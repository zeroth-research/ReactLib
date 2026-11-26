import Relational.AG.Defs
import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Set.Finite.Basic

/-!
  Lemmas towards the assume-guarantee rule (`Relational.AG.Rule`).

  * Rounds: an acyclic list of atoms can be sorted topologically
    (`Atom.Acyclic.exists_sorted`), and a partly fixed round can be completed
    by firing the remaining atoms in that order (`Module.WF.exists_round`).
    In particular a well-formed module never blocks
    (`Module.WF.exists_initRound`, `Module.WF.exists_updateRound`).
  * Await dependencies: they are well-founded (`Module.WF.dependsOn_wf`),
    and clauses (1) and (3) of the conclusion of the rule hold
    (`Module.ag_intf`, `Module.ag_awaits`).
-/

namespace Relational

universe u

/-! ### Rounds -/

/-- An acyclic relation whose sources lie in a finite set is well-founded
    (successors are smaller). -/
theorem wf_of_acyclic_of_finite {α : Type*} (r : α → α → Prop) (s : Set α) (hs : s.Finite)
    (hdom : ∀ a b, r a b → a ∈ s) (hac : ∀ a, ¬ Relation.TransGen r a a) :
    WellFounded (fun c a => r a c) := by
  have : IsStrictOrder α (fun c a => Relation.TransGen r a c) :=
    { irrefl := hac, trans := fun _ _ _ h₁ h₂ => h₂.trans h₁ }
  have hwf : s.WellFoundedOn (fun c a => Relation.TransGen r a c) := hs.wellFoundedOn
  have key : ∀ a ∈ s, Acc (fun c a => r a c) a := by
    intro a ha
    refine hwf.induction (P := fun a => Acc (fun c a => r a c) a) ha fun a _ ih => ?_
    refine ⟨_, fun c hc => ?_⟩
    by_cases hcs : c ∈ s
    · exact ih c hcs (.single hc)
    · exact ⟨_, fun d hd => absurd (hdom _ _ hd) hcs⟩
  refine ⟨fun a => ?_⟩
  by_cases has : a ∈ s
  · exact key a has
  · exact ⟨_, fun d hd => absurd (hdom _ _ hd) has⟩

variable {Name : Type} {Dom : Name → Type u}

/-- A nonempty acyclic list of atoms has an atom that awaits no atom of the list. -/
theorem Atom.Acyclic.exists_min {As : List (Atom Dom)} (h : Atom.Acyclic As)
    {A₀ : Atom Dom} (hA₀ : A₀ ∈ As) : ∃ A ∈ As, ∀ B ∈ As, ¬ A.awaits B := by
  have hwf := wf_of_acyclic_of_finite (fun a b => a ∈ As ∧ b ∈ As ∧ a.awaits b)
    {a | a ∈ As} (List.finite_toSet As) (fun a b h => h.1)
    (fun a hc => by
      have ha : a ∈ As := by
        obtain ⟨b, hab, -⟩ := Relation.TransGen.head'_iff.mp hc
        exact hab.1
      exact h a ha hc)
  obtain ⟨A, hA, hmin⟩ := hwf.has_min {a | a ∈ As} ⟨A₀, hA₀⟩
  exact ⟨A, hA, fun B hB hAB => hmin B hB ⟨hA, hB, hAB⟩⟩

/-- Topological order: the atoms can be listed so that no atom awaits a later one
    (or itself). -/
theorem Atom.Acyclic.exists_sorted : ∀ {As : List (Atom Dom)}, Atom.Acyclic As →
    ∃ l : List (Atom Dom), l.Perm As ∧ l.Pairwise (fun a b => ¬ a.awaits b) ∧
      ∀ a ∈ l, ¬ a.awaits a := by
  intro As
  induction hn : As.length generalizing As with
  | zero =>
    intro _
    have : As = [] := List.length_eq_zero_iff.mp hn
    subst this
    exact ⟨[], .refl _, .nil, by simp⟩
  | succ n ih =>
    intro h
    obtain ⟨A₀, hA₀⟩ : ∃ a, a ∈ As := List.exists_mem_of_length_pos (by omega)
    obtain ⟨A, hA, hmin⟩ := h.exists_min hA₀
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hA
    have hperm : (A :: (s ++ t)).Perm (s ++ A :: t) := List.perm_middle.symm
    obtain ⟨l, hl, hsorted, hirr⟩ := ih (As := s ++ t) (by simp at hn ⊢; omega)
      (h.of_subset fun a ha => by simp at ha ⊢; tauto)
    refine ⟨A :: l, (hl.cons A).trans hperm, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨fun b hb => hmin b ?_, hsorted⟩
      have := hl.subset hb
      simp at this ⊢; tauto
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hmin _ hA
      · exact hirr a ha

/-- Executing a topologically sorted list of atoms with pairwise disjoint writes,
    for an abstract round predicate `R` (instances: `Atom.Init`, `Atom.Update s`). -/
theorem Atom.exists_round_sorted (R : Atom Dom → State Dom → Prop)
    (hcongr : ∀ A (t t' : State Dom), (∀ x ∈ A.await, t x = t' x) → (∀ x ∈ A.write, t x = t' x) →
      R A t → R A t')
    (htotal : ∀ A (t : State Dom), ∃ t' : State Dom, (∀ x, x ∉ A.write → t' x = t x) ∧ R A t') :
    ∀ l : List (Atom Dom), l.Pairwise (fun a b => ¬ a.awaits b) →
      l.Pairwise (fun a b => Disjoint a.write b.write) → ∀ t : State Dom,
      ∃ t' : State Dom, (∀ A ∈ l, R A t') ∧ ∀ x, (∀ A ∈ l, x ∉ A.write) → t' x = t x := by
  intro l
  induction l with
  | nil => intro _ _ t; exact ⟨t, by simp, fun _ _ => rfl⟩
  | cons A l ih =>
    intro hs hd t
    rw [List.pairwise_cons] at hs hd
    obtain ⟨t₁, ht₁, hA⟩ := htotal A t
    obtain ⟨t', hl, ht'⟩ := ih hs.2 hd.2 t₁
    refine ⟨t', ?_, fun x hx => ?_⟩
    · intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · refine hcongr _ t₁ t' (fun x hx => ?_) (fun x hx => ?_) hA
        · exact (ht' x fun C hC hxC => hs.1 C hC ⟨x, hx, hxC⟩).symm
        · exact (ht' x fun C hC hxC =>
            Finset.disjoint_left.mp (hd.1 C hC) hx hxC).symm
      · exact hl B hB
    · rw [ht' x fun C hC => hx C (List.mem_cons_of_mem _ hC)]
      exact ht₁ x (hx _ List.mem_cons_self)

variable [DecidableEq Name]

/-- Completing a partial round: if the atoms in `K` (closed under awaits) already
    fire in `t`, then all atoms fire in some `t'` that agrees with `t` outside the
    controlled variables and on the variables written by `K`. With `K = ∅` this is
    non-blockingness of a round. -/
theorem Module.WF.exists_round {M : Module Dom} (hM : M.WF)
    (R : Atom Dom → State Dom → Prop)
    (hcongr : ∀ A (t t' : State Dom), (∀ x ∈ A.await, t x = t' x) → (∀ x ∈ A.write, t x = t' x) →
      R A t → R A t')
    (htotal : ∀ A (t : State Dom), ∃ t' : State Dom, (∀ x, x ∉ A.write → t' x = t x) ∧ R A t')
    (K : Atom Dom → Prop)
    (hK : ∀ A ∈ M.atoms, K A → ∀ B ∈ M.atoms, A.awaits B → K B)
    (t : State Dom) (hKt : ∀ A ∈ M.atoms, K A → R A t) :
    ∃ t' : State Dom, (∀ A ∈ M.atoms, R A t') ∧ (∀ x, x ∉ M.ctrl → t' x = t x) ∧
      ∀ A ∈ M.atoms, K A → ∀ x ∈ A.write, t' x = t x := by
  classical
  have hsub : M.atoms.filter (fun A => ¬ K A) ⊆ M.atoms := List.filter_sublist.subset
  obtain ⟨l, hperm, hsorted, -⟩ := (hM.atoms_acyclic.of_subset hsub).exists_sorted
  have hmem : ∀ A, A ∈ l ↔ A ∈ M.atoms ∧ ¬ K A := fun A => by
    rw [hperm.mem_iff]; simp
  have hdisj : l.Pairwise (fun a b => Disjoint a.write b.write) :=
    (hperm.pairwise_iff (fun h => Disjoint.symm h)).mpr
      (hM.atoms_pairwise_disj.sublist List.filter_sublist)
  obtain ⟨t', hl, ht'⟩ := Atom.exists_round_sorted R hcongr htotal l hsorted hdisj t
  have hkeep : ∀ A ∈ M.atoms, K A → ∀ x ∈ A.write, t' x = t x := by
    intro A hA hKA x hx
    refine ht' x fun C hC hxC => ?_
    have hCm := (hmem C).mp hC
    have hne : A ≠ C := fun h => hCm.2 (h ▸ hKA)
    have : Std.Symm (fun a b : Atom Dom => Disjoint a.write b.write) :=
      ⟨fun _ _ h => Disjoint.symm h⟩
    exact Finset.disjoint_left.mp (hM.atoms_pairwise_disj.forall hA hCm.1 hne) hx hxC
  refine ⟨t', fun A hA => ?_, fun x hx => ?_, hkeep⟩
  · by_cases hKA : K A
    · refine hcongr A t t' (fun x hx => ?_) (fun x hx => (hkeep A hA hKA x hx).symm)
        (hKt A hA hKA)
      refine (ht' x fun C hC hxC => ?_).symm
      have hCm := (hmem C).mp hC
      exact hCm.2 (hK A hA hKA C hCm.1 ⟨x, hx, hxC⟩)
    · exact hl A ((hmem A).mpr ⟨hA, hKA⟩)
  · exact ht' x fun C hC hxC =>
      hx (hM.atoms_write_ctrl C ((hmem C).mp hC).1 hxC)

/-! The two instances of the abstract round predicate. -/

omit [DecidableEq Name] in
theorem Atom.Init.congr {A : Atom Dom} {t t' : State Dom}
    (ha : ∀ x ∈ A.await, t x = t' x) (hw : ∀ x ∈ A.write, t x = t' x)
    (h : A.Init t) : A.Init t' := by
  have e₁ : t.restrict A.await = t'.restrict A.await := by
    funext x hx; exact ha x hx
  have e₂ : t.restrict A.write = t'.restrict A.write := by
    funext x hx; exact hw x hx
  simpa [Atom.Init, e₁, e₂] using h

omit [DecidableEq Name] in
theorem Atom.Update.congr {A : Atom Dom} {s s' t t' : State Dom}
    (hr : ∀ x ∈ A.read, s x = s' x)
    (ha : ∀ x ∈ A.await, t x = t' x) (hw : ∀ x ∈ A.write, t x = t' x)
    (h : A.Update s t) : A.Update s' t' := by
  have e₀ : s.restrict A.read = s'.restrict A.read := by
    funext x hx; exact hr x hx
  have e₁ : t.restrict A.await = t'.restrict A.await := by
    funext x hx; exact ha x hx
  have e₂ : t.restrict A.write = t'.restrict A.write := by
    funext x hx; exact hw x hx
  simpa [Atom.Update, e₀, e₁, e₂] using h

theorem Atom.exists_init (A : Atom Dom) (t : State Dom) :
    ∃ t', (∀ x, x ∉ A.write → t' x = t x) ∧ A.Init t' := by
  obtain ⟨w, hw⟩ := A.init_total (t.restrict A.await)
  refine ⟨fun x => if h : x ∈ A.write then w x h else t x, fun x hx => by simp [hx], ?_⟩
  have e₁ : State.restrict (fun x => if h : x ∈ A.write then w x h else t x) A.await
      = t.restrict A.await := by
    funext x hx
    have : x ∉ A.write := Finset.disjoint_left.mp A.await_write_disj hx
    simp [State.restrict, this]
  have e₂ : State.restrict (fun x => if h : x ∈ A.write then w x h else t x) A.write = w := by
    funext x hx
    simp [State.restrict, hx]
  simpa [Atom.Init, e₁, e₂] using hw

theorem Atom.exists_update (A : Atom Dom) (s t : State Dom) :
    ∃ t', (∀ x, x ∉ A.write → t' x = t x) ∧ A.Update s t' := by
  obtain ⟨w, hw⟩ := A.update_total (s.restrict A.read) (t.restrict A.await)
  refine ⟨fun x => if h : x ∈ A.write then w x h else t x, fun x hx => by simp [hx], ?_⟩
  have e₁ : State.restrict (fun x => if h : x ∈ A.write then w x h else t x) A.await
      = t.restrict A.await := by
    funext x hx
    have : x ∉ A.write := Finset.disjoint_left.mp A.await_write_disj hx
    simp [State.restrict, this]
  have e₂ : State.restrict (fun x => if h : x ∈ A.write then w x h else t x) A.write = w := by
    funext x hx
    simp [State.restrict, hx]
  simpa [Atom.Update, e₁, e₂] using hw

/-- A module never blocks: any state has a successor that takes prescribed values
    outside the controlled variables. No `Nonempty (Dom x)` is needed, `e` is the
    witness. -/
theorem Module.WF.exists_updateRound {M : Module Dom} (hM : M.WF) (s e : State Dom) :
    ∃ t, M.UpdateRound s t ∧ ∀ x, x ∉ M.ctrl → t x = e x := by
  obtain ⟨t, h, he, -⟩ := hM.exists_round (fun A t => A.Update s t)
    (fun A t t' ha hw h => h.congr (fun _ _ => rfl) ha hw) (fun A t => A.exists_update s t)
    (fun _ => False) (fun _ _ h => h.elim) e (fun _ _ h => h.elim)
  exact ⟨t, h, he⟩

theorem Module.WF.exists_initRound {M : Module Dom} (hM : M.WF) (e : State Dom) :
    ∃ t, M.InitRound t ∧ ∀ x, x ∉ M.ctrl → t x = e x := by
  obtain ⟨t, h, he, -⟩ := hM.exists_round (fun A t => A.Init t)
    (fun A t t' ha hw h => h.congr ha hw) (fun A t => A.exists_init t)
    (fun _ => False) (fun _ _ h => h.elim) e (fun _ _ h => h.elim)
  exact ⟨t, h, he⟩

/-! ### Await dependencies -/

omit [DecidableEq Name] in
theorem Atom.dependsOn_append {As Bs : List (Atom Dom)} {x y : Name} :
    Atom.dependsOn (As ++ Bs) x y ↔ Atom.dependsOn As x y ∨ Atom.dependsOn Bs x y := by
  simp only [Atom.dependsOn, List.mem_append]
  constructor
  · rintro ⟨A, hA | hA, h⟩
    · exact .inl ⟨A, hA, h⟩
    · exact .inr ⟨A, hA, h⟩
  · rintro (⟨A, hA, h⟩ | ⟨A, hA, h⟩)
    · exact ⟨A, .inl hA, h⟩
    · exact ⟨A, .inr hA, h⟩

theorem Module.WF.dependsOn_ctrl {M : Module Dom} (h : M.WF) {x y : Name}
    (hd : Atom.dependsOn M.atoms x y) : x ∈ M.ctrl ∧ y ∈ M.vars := by
  obtain ⟨A, hA, hx, hy⟩ := hd
  exact ⟨h.atoms_write_ctrl A hA hx, h.atoms_await_vars A hA hy⟩

/-- The await dependencies of a well-formed module are well-founded. -/
theorem Module.WF.dependsOn_wf {M : Module Dom} (h : M.WF) :
    WellFounded (fun y x => Atom.dependsOn M.atoms x y) :=
  wf_of_acyclic_of_finite _ (↑M.ctrl) M.ctrl.finite_toSet
    (fun _ _ hd => (h.dependsOn_ctrl hd).1) (Atom.acyclic_iff_nameAcyclic.mp h.atoms_acyclic)

/-- An await dependency of `M` from an interface to an observable variable:
    what clause (3) of `Implements` speaks about. -/
def Module.Seg (M : Module Dom) (y x : Name) : Prop :=
  y ∈ M.intf ∧ x ∈ M.obs ∧ M.Awaits y x

/-- An await chain of `N` mixed with steps of a relation `r` that avoids the
    private variables of `N`, between names that are not private to `N`, splits
    into steps of `r` and interface-to-observable await dependencies of `N`. -/
theorem Module.WF.awaits_split {N : Module Dom} (hN : N.WF) (r : Name → Name → Prop)
    (hr : ∀ x y, r x y → x ∉ N.priv ∧ y ∉ N.priv)
    {a b : Name} (ha : a ∉ N.priv) (hb : b ∉ N.priv)
    (h : Relation.TransGen (fun x y => r x y ∨ Atom.dependsOn N.atoms x y) a b) :
    Relation.TransGen (fun x y => r x y ∨ N.Seg x y) a b := by
  let T := Relation.TransGen (fun x y => r x y ∨ N.Seg x y)
  -- the state of the scan at `b`
  let G' : Name → Prop := fun b =>
    (b ∉ N.priv → b = a ∨ T a b) ∧
    (b ∈ N.priv → ∃ c, (c = a ∨ T a c) ∧ c ∈ N.intf ∧ N.Awaits c b)
  let G : Name → Prop := fun b =>
    (b ∉ N.priv → T a b) ∧
    (b ∈ N.priv → ∃ c, (c = a ∨ T a c) ∧ c ∈ N.intf ∧ N.Awaits c b)
  have ext : ∀ {c b}, (c = a ∨ T a c) → (r c b ∨ N.Seg c b) → T a b := by
    rintro c b (rfl | hc) hs
    · exact .single hs
    · exact .tail hc hs
  have step : ∀ {b b'}, G' b → (r b b' ∨ Atom.dependsOn N.atoms b b') → G b' := by
    intro b b' ⟨g₁, g₂⟩ hd
    by_cases hbp : b ∈ N.priv
    · obtain ⟨c, hc', hci, hcb⟩ := g₂ hbp
      rcases hd with hd | hd
      · exact absurd hbp (hr _ _ hd).1
      · have hcb' : N.Awaits c b' := .tail hcb hd
        refine ⟨fun hb' => ext hc' (.inr ⟨hci, ?_, hcb'⟩), fun _ => ⟨c, hc', hci, hcb'⟩⟩
        have := (hN.dependsOn_ctrl hd).2
        simp [Module.vars, Module.obs] at this ⊢; tauto
    · have hab := g₁ hbp
      rcases hd with hd | hd
      · exact ⟨fun _ => ext hab (.inl hd), fun hb' => absurd hb' (hr _ _ hd).2⟩
      · have hbi : b ∈ N.intf := by
          have := (hN.dependsOn_ctrl hd).1
          simp [Module.ctrl] at this; tauto
        refine ⟨fun hb' => ext hab (.inr ⟨hbi, ?_, .single hd⟩),
          fun _ => ⟨b, hab, hbi, .single hd⟩⟩
        have := (hN.dependsOn_ctrl hd).2
        simp [Module.vars, Module.obs] at this ⊢; tauto
  have main : G b := by
    clear hb
    induction h with
    | single hd => exact step ⟨fun _ => .inl rfl, fun hp => absurd hp ha⟩ hd
    | tail _ hd ih => exact step ⟨fun hp => .inr (ih.1 hp), ih.2⟩ hd
  exact main.1 hb

/-- The dependencies of `M` avoid the private variables of a module composable
    with it. -/
theorem Module.Composable.dependsOn_not_priv {M N : Module Dom} (hM : M.WF)
    (hc : M.Composable N) {x y : Name} (hd : Atom.dependsOn M.atoms x y) :
    x ∉ N.priv ∧ y ∉ N.priv := by
  have h := hM.dependsOn_ctrl hd
  have d := Finset.disjoint_left.mp hc.priv₂_disj
  refine ⟨fun hp => d hp ?_, fun hp => d hp h.2⟩
  have := h.1
  simp [Module.ctrl, Module.vars] at this ⊢; tauto

/-- So do its interface-to-observable await dependencies. -/
theorem Module.Composable.seg_not_priv {M N : Module Dom}
    (hc : M.Composable N) {x y : Name} (hd : M.Seg x y) :
    x ∉ N.priv ∧ y ∉ N.priv := by
  have d := Finset.disjoint_left.mp hc.priv₂_disj
  obtain ⟨hx, hy, -⟩ := hd
  refine ⟨fun hp => d hp ?_, fun hp => d hp ?_⟩
  · simp [Module.vars, hx]
  · simp [Module.vars, Module.obs] at hy ⊢; tauto

/-! ### Clauses (1) and (3) of the rule -/

section AG

variable {P₁ P₂ Q₁ Q₂ : Module Dom}

/-- Clause (1) of the conclusion. -/
theorem Module.ag_intf (hQ : Q₁.Composable Q₂)
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂) :
    Q₁.intf ⊆ P₁.intf ∧ Q₂.intf ⊆ P₂.intf := by
  have d := Finset.disjoint_left.mp hQ.intf_disj
  constructor
  · intro x hx
    have := h₁.intf hx
    simp only [Module.compose, Finset.mem_union] at this
    rcases this with h | h
    · exact h
    · exact absurd h (d hx)
  · intro x hx
    have := h₂.intf hx
    simp only [Module.compose, Finset.mem_union] at this
    rcases this with h | h
    · exact absurd hx (d h)
    · exact h

/-- The four kinds of links of AH's chains in the proof of clause (3). -/
def Module.Link (P₁ P₂ Q₁ Q₂ : Module Dom) (x y : Name) : Prop :=
  (Atom.dependsOn P₁.atoms x y ∨ Atom.dependsOn P₂.atoms x y) ∨ Q₁.Seg x y ∨ Q₂.Seg x y

/-- AH's stronger claim for clause (3): every chain of links is an await
    dependency of `P₁ ∥ P₂`. -/
theorem Module.ag_awaits_link (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂) :
    ∀ a b, Relation.TransGen (Module.Link P₁ P₂ Q₁ Q₂) a b → (P₁.compose P₂).Awaits a b := by
  have wP := wP₁.compose wP₂ hP
  intro a
  induction a using wP.dependsOn_wf.induction with
  | _ a ih =>
  intro b hab
  -- it is enough to find a first step in `P₁ ∥ P₂` followed by links
  suffices h : ∃ c, Atom.dependsOn (P₁.compose P₂).atoms a c ∧
      Relation.ReflTransGen (Module.Link P₁ P₂ Q₁ Q₂) c b by
    obtain ⟨c, hac, hcb⟩ := h
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hcb with rfl | hcb
    · exact .single hac
    · exact .trans (.single hac) (ih c hac b hcb)
  obtain ⟨c, hac, hcb⟩ := Relation.TransGen.head'_iff.mp hab
  have hdQ := Finset.disjoint_left.mp hQ.intf_disj
  -- a chain of `M`-dependencies and `N`-segments, with `M ∈ {P₁, P₂}` and
  -- `N ∈ {Q₁, Q₂}`, is a chain of links
  have lift₁ : ∀ {x y}, Relation.ReflTransGen
      (fun x y => Atom.dependsOn P₁.atoms x y ∨ Q₂.Seg x y) x y →
      Relation.ReflTransGen (Module.Link P₁ P₂ Q₁ Q₂) x y :=
    fun h => Relation.ReflTransGen.mono (fun _ _ h => by unfold Module.Link; tauto) _ _ h
  have lift₂ : ∀ {x y}, Relation.ReflTransGen
      (fun x y => Atom.dependsOn P₂.atoms x y ∨ Q₁.Seg x y) x y →
      Relation.ReflTransGen (Module.Link P₁ P₂ Q₁ Q₂) x y :=
    fun h => Relation.ReflTransGen.mono (fun _ _ h => by unfold Module.Link; tauto) _ _ h
  rcases hac with hac | hac | hac
  · exact ⟨c, by simpa [Module.compose, Atom.dependsOn_append] using hac, hcb⟩
  · -- a `Q₁` segment: by the first premise it is an await chain of `P₁ ∥ Q₂`
    obtain ⟨hai, hco, hac⟩ := hac
    have h := h₁.awaits c hco a hai hac
    have h' : Relation.TransGen
        (fun x y => Atom.dependsOn P₁.atoms x y ∨ Atom.dependsOn Q₂.atoms x y) a c :=
      Relation.TransGen.mono
        (fun x y hd => by simpa [Module.compose, Atom.dependsOn_append] using hd) _ _ h
    have hap : a ∉ Q₂.priv := fun hp => Finset.disjoint_left.mp hQ.priv₂_disj hp
      (by simp [Module.vars, hai])
    have hcp : c ∉ Q₂.priv := fun hp => Finset.disjoint_left.mp hQ.priv₂_disj hp
      (by simp [Module.vars, Module.obs] at hco ⊢; tauto)
    obtain ⟨d, had, hdc⟩ := Relation.TransGen.head'_iff.mp
      (wQ₂.awaits_split _ (fun _ _ hd => hP₁Q₂.dependsOn_not_priv wP₁ hd) hap hcp h')
    rcases had with had | had
    · exact ⟨d, by simp [Module.compose, Atom.dependsOn_append, had], (lift₁ hdc).trans hcb⟩
    · exact absurd had.1 (hdQ hai)
  · -- a `Q₂` segment, symmetrically
    obtain ⟨hai, hco, hac⟩ := hac
    have h := h₂.awaits c hco a hai hac
    have h' : Relation.TransGen
        (fun x y => Atom.dependsOn P₂.atoms x y ∨ Atom.dependsOn Q₁.atoms x y) a c :=
      Relation.TransGen.mono (fun x y hd => by
        have := hd
        simp only [Module.compose, Atom.dependsOn_append] at this
        tauto) _ _ h
    have hap : a ∉ Q₁.priv := fun hp => Finset.disjoint_left.mp hQ.priv₁_disj hp
      (by simp [Module.vars, hai])
    have hcp : c ∉ Q₁.priv := fun hp => Finset.disjoint_left.mp hQ.priv₁_disj hp
      (by simp [Module.vars, Module.obs] at hco ⊢; tauto)
    obtain ⟨d, had, hdc⟩ := Relation.TransGen.head'_iff.mp
      (wQ₁.awaits_split _ (fun _ _ hd => hQ₁P₂.symm.dependsOn_not_priv wP₂ hd) hap hcp h')
    rcases had with had | had
    · exact ⟨d, by simp [Module.compose, Atom.dependsOn_append, had], (lift₂ hdc).trans hcb⟩
    · exact absurd hai (hdQ had.1)

/-- Clause (3) for each specification separately: used in the trace part. -/
theorem Module.ag_awaits_seg (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂) {y x : Name} :
    (Q₁.Seg y x → (P₁.compose P₂).Awaits y x) ∧ (Q₂.Seg y x → (P₁.compose P₂).Awaits y x) :=
  ⟨fun h => Module.ag_awaits_link wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ h₁ h₂ _ _
      (.single (.inr (.inl h))),
   fun h => Module.ag_awaits_link wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ h₁ h₂ _ _
      (.single (.inr (.inr h)))⟩

/-- Clause (3) of the conclusion. -/
theorem Module.ag_awaits (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂) :
    ∀ x ∈ (Q₁.compose Q₂).obs, ∀ y ∈ (Q₁.compose Q₂).intf,
      (Q₁.compose Q₂).Awaits y x → (P₁.compose P₂).Awaits y x := by
  intro x hx y hy hyx
  have wQ := wQ₁.compose wQ₂ hQ
  have hyp : y ∉ Q₂.priv ∧ y ∉ Q₁.priv := by
    have := Finset.disjoint_left.mp wQ.intf_priv_disj hy
    simp [Module.compose] at this; tauto
  have hxp : x ∉ Q₂.priv ∧ x ∉ Q₁.priv := by
    have h1 := Finset.disjoint_left.mp wQ.intf_priv_disj
    have h2 := Finset.disjoint_left.mp wQ.extl_priv_disj
    simp only [Module.obs, Finset.mem_union] at hx
    rcases hx with hx | hx
    · have := h1 hx; simp [Module.compose] at this; tauto
    · have := h2 hx; simp [Module.compose] at this; tauto
  -- split the chain of `Q₁ ∥ Q₂` into `Q₂` segments, then into `Q₁` segments
  have h' : Relation.TransGen
      (fun x y => Atom.dependsOn Q₁.atoms x y ∨ Atom.dependsOn Q₂.atoms x y) y x :=
    Relation.TransGen.mono
      (fun x y hd => by simpa [Module.compose, Atom.dependsOn_append] using hd) _ _ hyx
  have s₁ := wQ₂.awaits_split _ (fun _ _ hd => hQ.dependsOn_not_priv wQ₁ hd) hyp.1 hxp.1 h'
  have s₁' : Relation.TransGen
      (fun x y => Q₂.Seg x y ∨ Atom.dependsOn Q₁.atoms x y) y x :=
    Relation.TransGen.mono (fun _ _ h => h.symm) _ _ s₁
  have s₂ := wQ₁.awaits_split _ (fun _ _ hd => hQ.symm.seg_not_priv hd) hyp.2 hxp.2 s₁'
  exact Module.ag_awaits_link wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ h₁ h₂ _ _
    (Relation.TransGen.mono (fun _ _ h => by unfold Module.Link; tauto) _ _ s₂)

end AG

end Relational

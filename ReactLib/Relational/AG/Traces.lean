import Relational.AG.Lemmas

/-!
  Trace inclusion for the assume-guarantee rule: clause (4) of the conclusion
  of `Module.assume_guarantee` (`Module.ag_traces`), after [AH99, Prop. 5].

  Let `ss` be a run of `P₁ ∥ P₂`. By induction on the number `k` of rounds,
  `ss` is a trace of `Q₁` and of `Q₂`, which is enough
  (`Module.FinTrace.compose`). Within round `k` the induction goes along a
  topological order of the atoms of `P₁ ∥ P₂` (`Module.ag_round`). The
  invariant is that both `Q₁` and `Q₂` have a run that agrees with `ss` in
  the rounds before `k`, and in round `k` on the external variables of
  `P₁ ∥ P₂` and on the variables written by the atoms treated so far
  (`Module.PartialTrace`, `Module.Done`). For the next atom, say of `P₁`:

  * `Q₂` does not control what the atom writes, so its run can be changed to
    agree with `ss` there (`Module.WF.partialTrace_extend`, AH's fact (C));
  * this run and `ss` give a run of `P₁ ∥ Q₂` that agrees with `ss` on the
    treated variables, and the premise `P₁ ∥ Q₂ ≼ Q₁` turns it into a run of
    `Q₁` (`Module.ag_step`).

  Both steps fix the atoms whose values are already determined
  (`Module.Keep`) and fire the others again (`Module.WF.complete_step`).
  That the fixed atoms await only treated variables is clause (3),
  `Module.ag_awaits_seg`.

  The order is on atoms, not on variables: an atom writes its variables
  together, so they are treated together.
-/

namespace Relational

universe u

variable {Name : Type} {Dom : Name → Type u}

/-! ### The rounds of a run -/

/-- The atom `A` takes round `k` of the run `r` to the state `t`: it
    initialises `t` if `k = 0`, and updates `r (k - 1)` to `t` otherwise. -/
def Atom.Step (A : Atom Dom) (r : Nat → State Dom) : Nat → State Dom → Prop
  | 0, t => A.Init t
  | k + 1, t => A.Update (r k) t

theorem Atom.Step.congr {A : Atom Dom} {r r' : Nat → State Dom} {k : Nat} {t t' : State Dom}
    (hr : ∀ i < k, ∀ x ∈ A.read, r i x = r' i x)
    (ha : ∀ x ∈ A.await, t x = t' x) (hw : ∀ x ∈ A.write, t x = t' x)
    (h : A.Step r k t) : A.Step r' k t' := by
  cases k with
  | zero => exact Atom.Init.congr ha hw h
  | succ k => exact Atom.Update.congr (hr k (Nat.lt_succ_self k)) ha hw h

/-- A finite run is a sequence of rounds. -/
theorem Module.finRun_iff {M : Module Dom} {n : Nat} {r : Nat → State Dom} :
    M.FinRun n r ↔ ∀ i ≤ n, ∀ A ∈ M.atoms, A.Step r i (r i) := by
  constructor
  · rintro ⟨h0, hs⟩ i hi A hA
    cases i with
    | zero => exact h0 A hA
    | succ i => exact hs i hi A hA
  · intro h
    exact ⟨fun A hA => h 0 (Nat.zero_le _) A hA, fun i hi A hA => h (i + 1) hi A hA⟩

theorem Module.FinRun.mono {M : Module Dom} {n k : Nat} {r : Nat → State Dom}
    (h : M.FinRun n r) (hk : k ≤ n) : M.FinRun k r :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

/-- Replacing the last state of a run by the result of another round `k`. -/
theorem Module.finRun_update {M : Module Dom} {k : Nat} {r : Nat → State Dom} {t : State Dom}
    (hr : ∀ i < k, ∀ A ∈ M.atoms, A.Step r i (r i)) (ht : ∀ A ∈ M.atoms, A.Step r k t) :
    M.FinRun k (Function.update r k t) := by
  rw [Module.finRun_iff]
  intro i hi A hA
  have hpre : ∀ j < i, ∀ x ∈ A.read, r j x = Function.update r k t j x := by
    intro j hj x _
    rw [Function.update_of_ne (by omega)]
  rcases Nat.lt_or_eq_of_le hi with hlt | rfl
  · rw [Function.update_of_ne (by omega)]
    exact (hr i hlt A hA).congr hpre (fun _ _ => rfl) (fun _ _ => rfl)
  · rw [Function.update_self]
    exact (ht A hA).congr hpre (fun _ _ => rfl) (fun _ _ => rfl)

variable [DecidableEq Name]

theorem Atom.exists_step (A : Atom Dom) (r : Nat → State Dom) (k : Nat) (t : State Dom) :
    ∃ t' : State Dom, (∀ x, x ∉ A.write → t' x = t x) ∧ A.Step r k t' := by
  cases k with
  | zero => exact A.exists_init t
  | succ k => exact A.exists_update (r k) t

theorem Module.obs_subset_vars (M : Module Dom) : M.obs ⊆ M.vars := by
  intro x
  simp only [Module.obs, Module.vars, Finset.mem_union]
  tauto

theorem Module.mem_atoms_compose {M N : Module Dom} {A : Atom Dom} :
    A ∈ (M.compose N).atoms ↔ A ∈ M.atoms ∨ A ∈ N.atoms :=
  List.mem_append

theorem Module.mem_ctrl_compose {M N : Module Dom} {x : Name} :
    x ∈ (M.compose N).ctrl ↔ x ∈ M.ctrl ∨ x ∈ N.ctrl := by
  simp only [Module.ctrl, Module.compose, Finset.mem_union]
  tauto

theorem Module.WF.extl_not_ctrl {M : Module Dom} (hM : M.WF) {x : Name} (hx : x ∈ M.extl) :
    x ∉ M.ctrl := by
  intro hc
  rcases Finset.mem_union.mp hc with h | h
  · exact Finset.disjoint_left.mp hM.intf_extl_disj h hx
  · exact Finset.disjoint_left.mp hM.extl_priv_disj hx h

/-- A variable of `M` is external or controlled. -/
theorem Module.mem_vars_iff {M : Module Dom} {x : Name} :
    x ∈ M.vars ↔ x ∈ M.extl ∨ x ∈ M.ctrl := by
  simp only [Module.vars, Module.ctrl, Finset.mem_union]
  tauto

/-- A variable of `M` that is not private is observable. -/
theorem Module.mem_obs_of_not_priv {M : Module Dom} {x : Name} (hx : x ∈ M.vars)
    (hp : x ∉ M.priv) : x ∈ M.obs := by
  simp only [Module.vars, Module.obs, Finset.mem_union] at hx ⊢
  tauto

/-- Composable modules control disjoint sets of variables. -/
theorem Module.Composable.not_ctrl {M N : Module Dom} (hc : M.Composable N) {x : Name}
    (hx : x ∈ M.ctrl) : x ∉ N.ctrl := by
  intro hn
  have hxv := M.ctrl_subset_vars hx
  have hnv := N.ctrl_subset_vars hn
  rcases Finset.mem_union.mp hx with h | h
  · rcases Finset.mem_union.mp hn with h' | h'
    · exact Finset.disjoint_left.mp hc.intf_disj h h'
    · exact Finset.disjoint_left.mp hc.priv₂_disj h' hxv
  · exact Finset.disjoint_left.mp hc.priv₁_disj h hnv

/-- Every variable is written by at most one atom. -/
theorem Module.WF.writer_unique {M : Module Dom} (hM : M.WF) {A B : Atom Dom}
    (hA : A ∈ M.atoms) (hB : B ∈ M.atoms) {x : Name} (hxA : x ∈ A.write)
    (hxB : x ∈ B.write) : A = B := by
  by_contra hne
  exact Finset.disjoint_left.mp (hM.atoms_pairwise_disj.forall hA hB hne) hxA hxB

/-- A round of an atom of `M` depends only on the variables of `M`. -/
theorem Module.WF.step_congr {M : Module Dom} (hM : M.WF) {A : Atom Dom} (hA : A ∈ M.atoms)
    {r r' : Nat → State Dom} {k : Nat} {t t' : State Dom}
    (hr : ∀ i < k, ∀ x ∈ M.vars, r i x = r' i x) (ht : ∀ x ∈ M.vars, t x = t' x)
    (h : A.Step r k t) : A.Step r' k t' :=
  h.congr (fun i hi x hx => hr i hi x (hM.atoms_read_vars A hA hx))
    (fun x hx => ht x (hM.atoms_await_vars A hA hx))
    (fun x hx => ht x (M.ctrl_subset_vars (hM.atoms_write_ctrl A hA hx)))

/-- A run of `M` depends only on the variables of `M`. -/
theorem Module.WF.finRun_congr {M : Module Dom} (hM : M.WF) {n : Nat} {r r' : Nat → State Dom}
    (h : ∀ i ≤ n, ∀ x ∈ M.vars, r i x = r' i x) (hr : M.FinRun n r) : M.FinRun n r' := by
  rw [Module.finRun_iff] at hr ⊢
  intro i hi A hA
  exact hM.step_congr hA (fun j hj => h j (by omega)) (h i hi) (hr i hi A hA)

theorem Module.finRun_compose (M₁ M₂ : Module Dom) (n : Nat) (r : Nat → State Dom) :
    (M₁.compose M₂).FinRun n r ↔ M₁.FinRun n r ∧ M₂.FinRun n r := by
  simp only [Module.FinRun, Module.initRound_compose, Module.updateRound_compose]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    exact ⟨⟨a, fun i hi => (h i hi).1⟩, b, fun i hi => (h i hi).2⟩
  · rintro ⟨⟨a, h₁⟩, b, h₂⟩
    exact ⟨⟨a, b⟩, fun i hi => ⟨h₁ i hi, h₂ i hi⟩⟩

/-- Completing round `k` of a run: `Module.WF.exists_round` for `Atom.Step`. -/
theorem Module.WF.complete_step {M : Module Dom} (hM : M.WF) (r : Nat → State Dom) (k : Nat)
    (K : Atom Dom → Prop)
    (hK : ∀ A ∈ M.atoms, K A → ∀ B ∈ M.atoms, A.awaits B → K B)
    (t : State Dom) (hKt : ∀ A ∈ M.atoms, K A → A.Step r k t) :
    ∃ t' : State Dom, (∀ A ∈ M.atoms, A.Step r k t') ∧ (∀ x, x ∉ M.ctrl → t' x = t x) ∧
      ∀ A ∈ M.atoms, K A → ∀ x ∈ A.write, t' x = t x :=
  hM.exists_round (fun A t => A.Step r k t)
    (fun _ _ _ ha hw h => h.congr (fun _ _ _ _ => rfl) ha hw)
    (fun A t => A.exists_step r k t) K hK t hKt

/-- A common trace of two composable modules is a trace of their composition:
    the converse of `Module.Trace.of_compose` for finite traces. The runs of
    the components are glued along their private variables. -/
theorem Module.FinTrace.compose {M₁ M₂ : Module Dom} (h₁ : M₁.WF) (h₂ : M₂.WF)
    (hc : M₁.Composable M₂) {n : Nat} {ts : Nat → State Dom}
    (t₁ : M₁.FinTrace n ts) (t₂ : M₂.FinTrace n ts) : (M₁.compose M₂).FinTrace n ts := by
  obtain ⟨r₁, hr₁, ho₁⟩ := t₁
  obtain ⟨r₂, hr₂, ho₂⟩ := t₂
  let rr : Nat → State Dom := fun i x =>
    if x ∈ M₁.priv then r₁ i x else if x ∈ M₂.priv then r₂ i x else ts i x
  have e₁ : ∀ i ≤ n, ∀ x ∈ M₁.vars, r₁ i x = rr i x := by
    intro i hi x hx
    by_cases hp : x ∈ M₁.priv
    · simp [rr, hp]
    · have hp₂ : x ∉ M₂.priv := fun h => Finset.disjoint_left.mp hc.priv₂_disj h hx
      simp [rr, hp, hp₂, ho₁ i hi x (Module.mem_obs_of_not_priv hx hp)]
  have e₂ : ∀ i ≤ n, ∀ x ∈ M₂.vars, r₂ i x = rr i x := by
    intro i hi x hx
    have hp₁ : x ∉ M₁.priv := fun h => Finset.disjoint_left.mp hc.priv₁_disj h hx
    by_cases hp : x ∈ M₂.priv
    · simp [rr, hp, hp₁]
    · simp [rr, hp, hp₁, ho₂ i hi x (Module.mem_obs_of_not_priv hx hp)]
  refine ⟨rr, (Module.finRun_compose M₁ M₂ n rr).mpr
    ⟨h₁.finRun_congr e₁ hr₁, h₂.finRun_congr e₂ hr₂⟩, fun i hi x hx => ?_⟩
  have w := h₁.compose h₂ hc
  have hp : x ∉ (M₁.compose M₂).priv := by
    intro hp
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.disjoint_left.mp w.intf_priv_disj h hp
    · exact Finset.disjoint_left.mp w.extl_priv_disj h hp
  simp only [Module.compose, Finset.mem_union, not_or] at hp
  simp [rr, hp.1, hp.2]

/-- A common trace of two composable modules is a trace of their composition
    [AH99, Prop. 3]: the converse of `Module.Trace.of_compose`. -/
theorem Module.Trace.compose {M₁ M₂ : Module Dom} (h₁ : M₁.WF) (h₂ : M₂.WF)
    (hc : M₁.Composable M₂) {ts : Cslib.ωSequence (State Dom)}
    (t₁ : M₁.Trace ts) (t₂ : M₂.Trace ts) : (M₁.compose M₂).Trace ts := by
  obtain ⟨r₁, hr₁, ho₁⟩ := t₁
  obtain ⟨r₂, hr₂, ho₂⟩ := t₂
  let rr : Cslib.ωSequence (State Dom) := ⟨fun i x =>
    if x ∈ M₁.priv then r₁ i x else if x ∈ M₂.priv then r₂ i x else ts i x⟩
  have e₁ : ∀ i, ∀ x ∈ M₁.vars, r₁ i x = rr i x := by
    intro i x hx
    by_cases hp : x ∈ M₁.priv
    · simp [rr, hp]
    · have hp₂ : x ∉ M₂.priv := fun h => Finset.disjoint_left.mp hc.priv₂_disj h hx
      simp [rr, hp, hp₂, ho₁ i x (Module.mem_obs_of_not_priv hx hp)]
  have e₂ : ∀ i, ∀ x ∈ M₂.vars, r₂ i x = rr i x := by
    intro i x hx
    have hp₁ : x ∉ M₁.priv := fun h => Finset.disjoint_left.mp hc.priv₁_disj h hx
    by_cases hp : x ∈ M₂.priv
    · simp [rr, hp, hp₁]
    · simp [rr, hp, hp₁, ho₂ i x (Module.mem_obs_of_not_priv hx hp)]
  refine ⟨rr, (Module.run_compose M₁ M₂ rr).mpr
    ⟨.of_finRun fun n => h₁.finRun_congr (fun i _ => e₁ i) (hr₁.finRun n),
     .of_finRun fun n => h₂.finRun_congr (fun i _ => e₂ i) (hr₂.finRun n)⟩,
    fun i x hx => ?_⟩
  have w := h₁.compose h₂ hc
  have hp : x ∉ (M₁.compose M₂).priv := by
    intro hp
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.disjoint_left.mp w.intf_priv_disj h hp
    · exact Finset.disjoint_left.mp w.extl_priv_disj h hp
  simp only [Module.compose, Finset.mem_union, not_or] at hp
  simp [rr, hp.1, hp.2]

/-! ### Partial traces -/

/-- `ts` is an `X`-partial trace of `N` with `k` full rounds: some run of `N`
    agrees with `ts` on the observable variables in the rounds before `k`,
    and in round `k` on those in `X`. These are AH's partial traces. -/
def Module.PartialTrace (N : Module Dom) (k : Nat) (X : Set Name) (ts : Nat → State Dom) :
    Prop :=
  ∃ r, N.FinRun k r ∧ (∀ i < k, ∀ x ∈ N.obs, r i x = ts i x) ∧
    ∀ x ∈ N.obs, x ∈ X → r k x = ts k x

theorem Module.PartialTrace.mono {N : Module Dom} {k : Nat} {X X' : Set Name}
    {ts : Nat → State Dom} (h : N.PartialTrace k X ts)
    (hX : ∀ x ∈ N.obs, x ∈ X' → x ∈ X) : N.PartialTrace k X' ts := by
  obtain ⟨r, hr, hpre, hk⟩ := h
  exact ⟨r, hr, hpre, fun x hx hx' => hk x hx (hX x hx hx')⟩

theorem Module.PartialTrace.finTrace {N : Module Dom} {n : Nat} {ts : Nat → State Dom}
    (h : N.PartialTrace n Set.univ ts) : N.FinTrace n ts := by
  obtain ⟨r, hr, hpre, hk⟩ := h
  refine ⟨r, hr, fun i hi x hx => ?_⟩
  rcases Nat.lt_or_eq_of_le hi with hlt | rfl
  · exact hpre i hlt x hx
  · exact hk x hx trivial

/-- A run of `k` rounds can be extended by a round: a module never blocks. -/
theorem Module.WF.partialTrace_start {N : Module Dom} (hN : N.WF) {k : Nat}
    {r ts : Nat → State Dom} (hr : ∀ i < k, ∀ A ∈ N.atoms, A.Step r i (r i))
    (hobs : ∀ i < k, ∀ x ∈ N.obs, r i x = ts i x) : N.PartialTrace k ∅ ts := by
  obtain ⟨t', ht', -, -⟩ := hN.complete_step r k (fun _ => False) (fun _ _ h => h.elim)
    (r k) (fun _ _ h => h.elim)
  refine ⟨Function.update r k t', Module.finRun_update hr ht', fun i hi x hx => ?_,
    fun x _ hx => absurd hx (Set.notMem_empty x)⟩
  rw [Function.update_of_ne (by omega)]
  exact hobs i hi x hx

theorem Module.WF.partialTrace_zero {N : Module Dom} (hN : N.WF) (ts : Nat → State Dom) :
    N.PartialTrace 0 ∅ ts :=
  hN.partialTrace_start (r := ts) (fun i hi => absurd hi (Nat.not_lt_zero i))
    (fun i hi => absurd hi (Nat.not_lt_zero i))

theorem Module.WF.partialTrace_succ {N : Module Dom} (hN : N.WF) {k : Nat}
    {ts : Nat → State Dom} (h : N.PartialTrace k Set.univ ts) :
    N.PartialTrace (k + 1) ∅ ts := by
  obtain ⟨r, hr, hpre, hk⟩ := h
  refine hN.partialTrace_start (r := r)
    (fun i hi => Module.finRun_iff.mp hr i (by omega)) (fun i hi x hx => ?_)
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
  · exact hpre i hlt x hx
  · exact hk x hx trivial

/-- The atoms of `N` whose round is determined by the values in `X`: they
    write an interface variable in `X`, or one that such a variable awaits.
    These are kept when a partial round is completed. -/
def Module.Keep (N : Module Dom) (X : Set Name) (B : Atom Dom) : Prop :=
  ∃ y ∈ N.intf, y ∈ X ∧ ∃ z ∈ B.write, y = z ∨ N.Awaits y z

omit [DecidableEq Name] in
theorem Module.Keep.awaits {N : Module Dom} {X : Set Name} {B : Atom Dom} (hB : B ∈ N.atoms)
    (h : N.Keep X B) {w : Name} (hw : w ∈ B.await) : ∃ y ∈ N.intf, y ∈ X ∧ N.Awaits y w := by
  obtain ⟨y, hy, hyX, z, hz, hyz⟩ := h
  have hd : Atom.dependsOn N.atoms z w := ⟨B, hB, hz, hw⟩
  refine ⟨y, hy, hyX, ?_⟩
  rcases hyz with rfl | hyz
  · exact .single hd
  · exact .tail hyz hd

omit [DecidableEq Name] in
/-- The kept atoms are closed under awaits. -/
theorem Module.Keep.closed {N : Module Dom} {X : Set Name} {B C : Atom Dom}
    (hB : B ∈ N.atoms) (h : N.Keep X B) (hBC : B.awaits C) : N.Keep X C := by
  obtain ⟨w, hw, hwC⟩ := hBC
  obtain ⟨y, hy, hyX, hyw⟩ := h.awaits hB hw
  exact ⟨y, hy, hyX, w, hwC, .inr hyw⟩

/-- The observable variables a kept atom awaits are in `X`, if `X` is closed
    under the await dependencies of `N`. -/
theorem Module.Keep.await_mem {N : Module Dom} {X : Set Name} {B : Atom Dom}
    (hX : ∀ y x, N.Seg y x → y ∈ X → x ∈ X) (hB : B ∈ N.atoms) (h : N.Keep X B)
    {w : Name} (hw : w ∈ B.await) (hwo : w ∈ N.obs) : w ∈ X := by
  obtain ⟨y, hy, hyX, hyw⟩ := h.awaits hB hw
  exact hX y w ⟨hy, hwo, hyw⟩ hyX

/-- [AH99, fact (C)]: a partial trace of `N` can be extended by any values of
    variables that `N` does not control. -/
theorem Module.WF.partialTrace_extend {N : Module Dom} (hN : N.WF) {k : Nat}
    {X Y : Set Name} {ts : Nat → State Dom}
    (hX : ∀ y x, N.Seg y x → y ∈ X → x ∈ X) (hY : ∀ x ∈ Y, x ∉ N.ctrl)
    (h : N.PartialTrace k X ts) : N.PartialTrace k (X ∪ Y) ts := by
  classical
  obtain ⟨r, hr, hpre, hk⟩ := h
  have hr' := Module.finRun_iff.mp hr
  -- the target of the round: as before, with the values of `ts` on `Y`
  let e : State Dom := fun x => if x ∈ Y then ts k x else r k x
  have heY : ∀ x ∈ Y, e x = ts k x := fun x hx => by simp [e, hx]
  have heN : ∀ x, x ∉ Y → e x = r k x := fun x hx => by simp [e, hx]
  have hfire : ∀ B ∈ N.atoms, N.Keep X B → B.Step r k e := by
    intro B hB hKB
    refine (hr' k le_rfl B hB).congr (fun _ _ _ _ => rfl) (fun w hw => ?_) (fun w hw => ?_)
    · by_cases hwY : w ∈ Y
      · rw [heY w hwY]
        have hwo : w ∈ N.obs := by
          have hwv := Module.mem_vars_iff.mp (hN.atoms_await_vars B hB hw)
          have hwc := hY w hwY
          simp only [Module.obs, Finset.mem_union]
          tauto
        exact hk w hwo (hKB.await_mem hX hB hw hwo)
      · exact (heN w hwY).symm
    · exact (heN w fun hwY => hY w hwY (hN.atoms_write_ctrl B hB hw)).symm
  obtain ⟨t', ht', hoff, hkeep⟩ := hN.complete_step r k (N.Keep X)
    (fun A hA hKA B _ hAB => hKA.closed hA hAB) e hfire
  refine ⟨Function.update r k t', Module.finRun_update (fun i hi => hr' i (by omega)) ht',
    fun i hi x hx => ?_, fun x hx hxXY => ?_⟩
  · rw [Function.update_of_ne (by omega)]
    exact hpre i hi x hx
  · rw [Function.update_self]
    have hxXY' : x ∈ X ∨ x ∈ Y := hxXY
    rcases Finset.mem_union.mp hx with hxi | hxe
    · have hxc : x ∈ N.ctrl := Finset.mem_union_left _ hxi
      have hxY : x ∉ Y := fun hxY => hY x hxY hxc
      have hxX : x ∈ X := hxXY'.resolve_right hxY
      obtain ⟨B, hB, hxB⟩ := hN.atoms_cov_ctrl x hxc
      rw [hkeep B hB ⟨x, hxi, hxX, x, hxB, .inl rfl⟩ x hxB, heN x hxY]
      exact hk x hx hxX
    · rw [hoff x (hN.extl_not_ctrl hxe)]
      by_cases hxY : x ∈ Y
      · exact heY x hxY
      · rw [heN x hxY]
        exact hk x hx (hxXY'.resolve_right hxY)

/-! ### The variables treated so far in a round -/

/-- The variables of `P` whose values in the current round are fixed once
    the atoms `l` have fired: the external ones and those `l` writes. -/
def Module.Done (P : Module Dom) (l : List (Atom Dom)) : Set Name :=
  {x | x ∈ P.extl ∨ ∃ B ∈ l, x ∈ B.write}

/-- `l` consists of atoms of `P` and contains every atom of `P` that one of
    its atoms awaits. -/
def Module.AwaitClosed (P : Module Dom) (l : List (Atom Dom)) : Prop :=
  (∀ B ∈ l, B ∈ P.atoms) ∧ ∀ B ∈ l, ∀ C ∈ P.atoms, B.awaits C → C ∈ l

/-- What a treated atom awaits is treated. -/
theorem Module.WF.done_await {P : Module Dom} (wP : P.WF) {l : List (Atom Dom)}
    (hl : P.AwaitClosed l) {B : Atom Dom} (hB : B ∈ l) {x : Name} (hx : x ∈ B.await) :
    x ∈ P.Done l := by
  rcases Module.mem_vars_iff.mp (wP.atoms_await_vars B (hl.1 B hB) hx) with hxe | hxc
  · exact .inl hxe
  · obtain ⟨C, hC, hxC⟩ := wP.atoms_cov_ctrl x hxc
    exact .inr ⟨C, hl.2 B hB C hC ⟨x, hx, hxC⟩, hxC⟩

/-- The treated variables are closed under the await dependencies of `P`. -/
theorem Module.WF.done_awaits {P : Module Dom} (wP : P.WF) {l : List (Atom Dom)}
    (hl : P.AwaitClosed l) {y w : Name} (h : P.Awaits y w) (hy : y ∈ P.Done l) :
    w ∈ P.Done l := by
  have step : ∀ {y w}, Atom.dependsOn P.atoms y w → y ∈ P.Done l → w ∈ P.Done l := by
    rintro y w ⟨B', hB', hyB', hwB'⟩ hy
    rcases hy with hye | ⟨B, hB, hyB⟩
    · exact absurd (wP.atoms_write_ctrl B' hB' hyB') (wP.extl_not_ctrl hye)
    · have hBB' : B = B' := wP.writer_unique (hl.1 B hB) hB' hyB hyB'
      subst hBB'
      exact wP.done_await hl hB hwB'
  have h' : Relation.TransGen (Atom.dependsOn P.atoms) y w := h
  clear h
  induction h' with
  | single hd => exact step hd hy
  | tail _ hd ih => exact step hd ih

/-! ### The assume-guarantee step -/

/-- One half of the step for the next atom of `P`: `M` is the component of
    `P` whose atoms `l` has just been extended with, `N` the specification of
    the other component, and `Q` the specification of `M`. If the run `ss`
    of `M` is an `l`-partial trace of `N`, it is one of `Q`, because every
    run of `M ∥ N` is a trace of `Q` (`prem`). -/
theorem Module.ag_step {P M N Q : Module Dom} (wP : P.WF) (wM : M.WF) (wN : N.WF)
    (hc : M.Composable N)
    -- `M` is a component of `P`
    (hsub : ∀ A ∈ M.atoms, A ∈ P.atoms)
    (hown : ∀ B ∈ P.atoms, ∀ x ∈ B.write, x ∈ M.ctrl → B ∈ M.atoms)
    (hQN : ∀ x ∈ Q.obs, x ∉ N.priv)
    -- the await dependencies of `N` are await dependencies of `P`
    (hseg : ∀ y x, N.Seg y x → P.Awaits y x)
    {k : Nat} {ss : Nat → State Dom}
    (prem : ∀ u, M.FinRun k u → N.FinRun k u → Q.FinTrace k u)
    (hss : M.FinRun k ss) {l : List (Atom Dom)} (hl : P.AwaitClosed l)
    (hN : N.PartialTrace k (P.Done l) ss) : Q.PartialTrace k (P.Done l) ss := by
  classical
  obtain ⟨r, hr, hpre, hk⟩ := hN
  have hr' := Module.finRun_iff.mp hr
  have hss' := Module.finRun_iff.mp hss
  have hX : ∀ y x, N.Seg y x → y ∈ P.Done l → x ∈ P.Done l :=
    fun y x h hy => wP.done_awaits hl (hseg y x h) hy
  have hMN : ∀ x ∈ M.vars, x ∉ N.priv :=
    fun x hx hp => Finset.disjoint_left.mp hc.priv₂_disj hp hx
  -- the run of `M ∥ N`: `r` on the variables of `N`, and `ss` elsewhere
  let u : Nat → State Dom := fun i x => if x ∈ N.vars then r i x else ss i x
  have huN : ∀ i, ∀ x ∈ N.vars, u i x = r i x := fun i x hx => by simp [u, hx]
  have huM : ∀ i < k, ∀ x, x ∉ N.priv → u i x = ss i x := by
    intro i hi x hp
    by_cases hx : x ∈ N.vars
    · rw [huN i x hx]
      exact hpre i hi x (Module.mem_obs_of_not_priv hx hp)
    · simp [u, hx]
  have huk : ∀ x, x ∉ N.priv → x ∈ P.Done l → u k x = ss k x := by
    intro x hp hD
    by_cases hx : x ∈ N.vars
    · rw [huN k x hx]
      exact hk x (Module.mem_obs_of_not_priv hx hp) hD
    · simp [u, hx]
  -- its rounds before `k`
  have hu : ∀ i < k, ∀ A ∈ (M.compose N).atoms, A.Step u i (u i) := by
    intro i hi A hA
    rcases Module.mem_atoms_compose.mp hA with hA | hA
    · exact wM.step_congr hA (fun j hj x hx => (huM j (by omega) x (hMN x hx)).symm)
        (fun x hx => (huM i hi x (hMN x hx)).symm) (hss' i (by omega) A hA)
    · exact wN.step_congr hA (fun j _ x hx => (huN j x hx).symm)
        (fun x hx => (huN i x hx).symm) (hr' i (by omega) A hA)
  -- in round `k`, keep the atoms of `M` in `l` and the atoms of `N` they determine
  let K : Atom Dom → Prop := fun A =>
    (A ∈ M.atoms ∧ A ∈ l) ∨ (A ∈ N.atoms ∧ N.Keep (P.Done l) A)
  have hKclosed : ∀ A ∈ (M.compose N).atoms, K A →
      ∀ B ∈ (M.compose N).atoms, A.awaits B → K B := by
    intro A _ hKA B hB hAB
    obtain ⟨x, hxA, hxB⟩ := id hAB
    rcases hKA with ⟨hAM, hAl⟩ | ⟨hAN, hAK⟩
    · rcases Module.mem_atoms_compose.mp hB with hBM | hBN
      · exact Or.inl ⟨hBM, hl.2 A hAl B (hsub B hBM) hAB⟩
      · have hxi : x ∈ N.intf := by
          have h1 := Finset.mem_union.mp (wN.atoms_write_ctrl B hBN hxB)
          have h2 := hMN x (wM.atoms_await_vars A hAM hxA)
          tauto
        exact Or.inr ⟨hBN, x, hxi, wP.done_await hl hAl hxA, x, hxB, .inl rfl⟩
    · rcases Module.mem_atoms_compose.mp hB with hBM | hBN
      · have hxp := hMN x (M.ctrl_subset_vars (wM.atoms_write_ctrl B hBM hxB))
        have hxD : x ∈ P.Done l := hAK.await_mem hX hAN hxA
          (Module.mem_obs_of_not_priv (wN.atoms_await_vars A hAN hxA) hxp)
        rcases hxD with hxe | ⟨B', hB', hxB'⟩
        · exact absurd (wP.atoms_write_ctrl B (hsub B hBM) hxB) (wP.extl_not_ctrl hxe)
        · have hBB' : B' = B := wP.writer_unique (hl.1 B' hB') (hsub B hBM) hxB' hxB
          exact Or.inl ⟨hBM, hBB' ▸ hB'⟩
      · exact Or.inr ⟨hBN, hAK.closed hAN hAB⟩
  have hKfire : ∀ A ∈ (M.compose N).atoms, K A → A.Step u k (u k) := by
    intro A _ hKA
    rcases hKA with ⟨hAM, hAl⟩ | ⟨hAN, -⟩
    · refine (hss' k le_rfl A hAM).congr
        (fun j hj x hx => (huM j hj x (hMN x (wM.atoms_read_vars A hAM hx))).symm)
        (fun x hx => ?_) (fun x hx => ?_)
      · exact (huk x (hMN x (wM.atoms_await_vars A hAM hx)) (wP.done_await hl hAl hx)).symm
      · exact (huk x (hMN x (M.ctrl_subset_vars (wM.atoms_write_ctrl A hAM hx)))
          (.inr ⟨A, hAl, hx⟩)).symm
    · exact wN.step_congr hAN (fun j _ x hx => (huN j x hx).symm)
        (fun x hx => (huN k x hx).symm) (hr' k le_rfl A hAN)
  obtain ⟨t', ht', hoff, hkeep⟩ :=
    (wM.compose wN hc).complete_step u k K hKclosed (u k) hKfire
  -- the premise gives a run of `Q`
  obtain ⟨hrM, hrN⟩ := (Module.finRun_compose M N k _).mp (Module.finRun_update hu ht')
  obtain ⟨r₁, hr₁, hr₁o⟩ := prem _ hrM hrN
  refine ⟨r₁, hr₁, fun i hi x hx => ?_, fun x hx hxD => ?_⟩
  · rw [hr₁o i (by omega) x hx, Function.update_of_ne (by omega)]
    exact huM i hi x (hQN x hx)
  · rw [hr₁o k le_rfl x hx, Function.update_self]
    have huk' : u k x = ss k x := huk x (hQN x hx) hxD
    by_cases hxM : x ∈ M.ctrl
    · -- written by a kept atom of `M`
      rcases hxD with hxe | ⟨B, hB, hxB⟩
      · obtain ⟨A, hA, hxA⟩ := wM.atoms_cov_ctrl x hxM
        exact absurd (wP.atoms_write_ctrl A (hsub A hA) hxA) (wP.extl_not_ctrl hxe)
      · have hBM := hown B (hl.1 B hB) x hxB hxM
        rw [hkeep B (Module.mem_atoms_compose.mpr (.inl hBM)) (Or.inl ⟨hBM, hB⟩) x hxB]
        exact huk'
    · by_cases hxN : x ∈ N.ctrl
      · -- written by a kept atom of `N`
        have hxi : x ∈ N.intf := by
          have h1 := Finset.mem_union.mp hxN
          have h2 := hQN x hx
          tauto
        obtain ⟨B, hB, hxB⟩ := wN.atoms_cov_ctrl x hxN
        rw [hkeep B (Module.mem_atoms_compose.mpr (.inr hB))
          (Or.inr ⟨hB, x, hxi, hxD, x, hxB, .inl rfl⟩) x hxB]
        exact huk'
      · rw [hoff x (fun h => (Module.mem_ctrl_compose.mp h).elim hxM hxN)]
        exact huk'

section AG

variable {P₁ P₂ Q₁ Q₂ : Module Dom}

omit [DecidableEq Name] in
/-- The variables treated after one more atom. -/
theorem Module.done_concat {P : Module Dom} {l : List (Atom Dom)} {A : Atom Dom} {x : Name}
    (hx : x ∈ P.Done (l ++ [A])) : x ∈ P.Done l ∪ {x | x ∈ A.write} := by
  rcases hx with hxe | ⟨B, hB, hxB⟩
  · exact .inl (.inl hxe)
  · rcases List.mem_append.mp hB with hB | hB
    · exact .inl (.inr ⟨B, hB, hxB⟩)
    · rw [List.mem_singleton.mp hB] at hxB
      exact .inr hxB

/-- A round of the assume-guarantee induction: if the run `ss` of `P₁ ∥ P₂`
    is a trace of `Q₁` and of `Q₂` before round `k`, it is one up to and
    including round `k`. The induction is over a topological order of the
    atoms of `P₁ ∥ P₂`. -/
theorem Module.ag_round (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    (hobs : (Q₁.compose Q₂).obs ⊆ (P₁.compose P₂).obs)
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂)
    {k : Nat} {ss : Nat → State Dom} (hss₁ : P₁.FinRun k ss) (hss₂ : P₂.FinRun k ss)
    (i₁ : Q₁.PartialTrace k ∅ ss) (i₂ : Q₂.PartialTrace k ∅ ss) :
    Q₁.PartialTrace k Set.univ ss ∧ Q₂.PartialTrace k Set.univ ss := by
  have wP := wP₁.compose wP₂ hP
  obtain ⟨l, hperm, hsorted, hirr⟩ := wP.atoms_acyclic.exists_sorted
  have hmem : ∀ A, A ∈ l ↔ A ∈ (P₁.compose P₂).atoms := fun A => hperm.mem_iff
  have hseg := fun y x =>
    Module.ag_awaits_seg wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ h₁ h₂ (y := y) (x := x)
  obtain ⟨hi₁, hi₂⟩ := Module.ag_intf hQ h₁ h₂
  -- the premises, as statements about common runs
  have prem₁ : ∀ u, P₁.FinRun k u → Q₂.FinRun k u → Q₁.FinTrace k u := fun u a b =>
    h₁.traces k u ⟨u, (Module.finRun_compose P₁ Q₂ k u).mpr ⟨a, b⟩, fun _ _ _ _ => rfl⟩
  have prem₂ : ∀ u, P₂.FinRun k u → Q₁.FinRun k u → Q₂.FinTrace k u := fun u a b =>
    h₂.traces k u ⟨u, (Module.finRun_compose Q₁ P₂ k u).mpr ⟨b, a⟩, fun _ _ _ _ => rfl⟩
  -- the external variables of `P₁ ∥ P₂` are not controlled by the specifications
  have hext : ∀ {N : Module Dom}, N.WF → N.intf ⊆ (P₁.compose P₂).intf →
      N.PartialTrace k ∅ ss → N.PartialTrace k ((P₁.compose P₂).Done []) ss := by
    intro N wN hNi hN
    refine (wN.partialTrace_extend (Y := {x | x ∈ (P₁.compose P₂).extl ∧ x ∉ N.ctrl})
      (fun _ _ _ h => h.elim) (fun x hx => hx.2) hN).mono fun x hx hxD => ?_
    rcases hxD with hxe | ⟨B, hB, -⟩
    · refine .inr ⟨hxe, fun hc => ?_⟩
      rcases Finset.mem_union.mp hc with h | h
      · exact Finset.disjoint_left.mp wP.intf_extl_disj (hNi h) hxe
      · rcases Finset.mem_union.mp hx with h' | h'
        · exact Finset.disjoint_left.mp wN.intf_priv_disj h' h
        · exact Finset.disjoint_left.mp wN.extl_priv_disj h' h
    · simp at hB
  have key : ∀ l₀ l₁, l₀ ++ l₁ = l → (P₁.compose P₂).AwaitClosed l₀ ∧
      Q₁.PartialTrace k ((P₁.compose P₂).Done l₀) ss ∧
      Q₂.PartialTrace k ((P₁.compose P₂).Done l₀) ss := by
    intro l₀
    induction l₀ using List.reverseRecOn with
    | nil =>
      intro _ _
      exact ⟨⟨by simp, by simp⟩,
        hext wQ₁ (hi₁.trans Finset.subset_union_left) i₁,
        hext wQ₂ (hi₂.trans Finset.subset_union_right) i₂⟩
    | append_singleton l₀ A ih =>
      intro l₁ hl
      have hl' : l₀ ++ A :: l₁ = l := by simpa using hl
      obtain ⟨hcl, j₁, j₂⟩ := ih (A :: l₁) hl'
      have hAl : A ∈ l := by rw [← hl']; simp
      have hAP := (hmem A).mp hAl
      have hs : (l₀ ++ A :: l₁).Pairwise (fun a b => ¬ a.awaits b) := hl' ▸ hsorted
      rw [List.pairwise_append] at hs
      have hcl' : (P₁.compose P₂).AwaitClosed (l₀ ++ [A]) := by
        refine ⟨fun B hB => ?_, fun B hB C hC hBC => ?_⟩
        · rcases List.mem_append.mp hB with h | h
          · exact hcl.1 B h
          · rw [List.mem_singleton.mp h]
            exact hAP
        · have hCl : C ∈ l₀ ++ A :: l₁ := hl' ▸ (hmem C).mpr hC
          rcases List.mem_append.mp hCl with h | h
          · exact List.mem_append.mpr (.inl h)
          · exfalso
            rcases List.mem_append.mp hB with hB | hB
            · exact hs.2.2 B hB C h hBC
            · have hBA : B = A := List.mem_singleton.mp hB
              subst hBA
              rcases List.mem_cons.mp h with hCB | h
              · subst hCB
                exact hirr _ hAl hBC
              · exact (List.pairwise_cons.mp hs.2.1).1 C h hBC
      have hD₁ : ∀ y x, Q₁.Seg y x → y ∈ (P₁.compose P₂).Done l₀ →
          x ∈ (P₁.compose P₂).Done l₀ :=
        fun y x h hy => wP.done_awaits hcl ((hseg y x).1 h) hy
      have hD₂ : ∀ y x, Q₂.Seg y x → y ∈ (P₁.compose P₂).Done l₀ →
          x ∈ (P₁.compose P₂).Done l₀ :=
        fun y x h hy => wP.done_awaits hcl ((hseg y x).2 h) hy
      rcases Module.mem_atoms_compose.mp hAP with hA | hA
      · -- an atom of `P₁`: extend the run of `Q₂`, then get one of `Q₁`
        have j₂' : Q₂.PartialTrace k ((P₁.compose P₂).Done (l₀ ++ [A])) ss :=
          (wQ₂.partialTrace_extend (Y := {x | x ∈ A.write}) hD₂
            (fun x hx => hP₁Q₂.not_ctrl (wP₁.atoms_write_ctrl A hA hx)) j₂).mono
            fun x _ hx => Module.done_concat hx
        have j₁' := Module.ag_step wP wP₁ wQ₂ hP₁Q₂
          (fun B hB => Module.mem_atoms_compose.mpr (.inl hB))
          (fun B hB x hxB hx => (Module.mem_atoms_compose.mp hB).resolve_right
            fun hB₂ => hP.not_ctrl hx (wP₂.atoms_write_ctrl B hB₂ hxB))
          (fun x hx hp => Finset.disjoint_left.mp hQ.priv₂_disj hp (Q₁.obs_subset_vars hx))
          (fun y x h => (hseg y x).2 h) prem₁ hss₁ hcl' j₂'
        exact ⟨hcl', j₁', j₂'⟩
      · -- an atom of `P₂`, symmetrically
        have j₁' : Q₁.PartialTrace k ((P₁.compose P₂).Done (l₀ ++ [A])) ss :=
          (wQ₁.partialTrace_extend (Y := {x | x ∈ A.write}) hD₁
            (fun x hx => hQ₁P₂.symm.not_ctrl (wP₂.atoms_write_ctrl A hA hx)) j₁).mono
            fun x _ hx => Module.done_concat hx
        have j₂' := Module.ag_step wP wP₂ wQ₁ hQ₁P₂.symm
          (fun B hB => Module.mem_atoms_compose.mpr (.inr hB))
          (fun B hB x hxB hx => (Module.mem_atoms_compose.mp hB).resolve_left
            fun hB₁ => hP.not_ctrl (wP₁.atoms_write_ctrl B hB₁ hxB) hx)
          (fun x hx hp => Finset.disjoint_left.mp hQ.priv₁_disj hp (Q₂.obs_subset_vars hx))
          (fun y x h => (hseg y x).1 h) prem₂ hss₂ hcl' j₁'
        exact ⟨hcl', j₁', j₂'⟩
  obtain ⟨-, f₁, f₂⟩ := key l [] (by simp)
  -- after all atoms, every observable variable is treated
  have hall : ∀ x ∈ (P₁.compose P₂).obs, x ∈ (P₁.compose P₂).Done l := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxi | hxe
    · obtain ⟨B, hB, hxB⟩ := wP.atoms_cov_ctrl x (Finset.mem_union_left _ hxi)
      exact .inr ⟨B, (hmem B).mpr hB, hxB⟩
    · exact .inl hxe
  exact ⟨f₁.mono fun x hx _ => hall x (hobs (Module.obs_subset_compose_left Q₁ Q₂ hx)),
    f₂.mono fun x hx _ => hall x (hobs (Module.obs_subset_compose_right Q₁ Q₂ hx))⟩

/-- Clause (4) of the conclusion of the assume-guarantee rule: every trace of
    `P₁ ∥ P₂` is a trace of `Q₁ ∥ Q₂`. -/
theorem Module.ag_traces (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    (hextl : (Q₁.compose Q₂).extl ⊆ (P₁.compose P₂).obs)
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂) :
    ∀ n ts, (P₁.compose P₂).FinTrace n ts → (Q₁.compose Q₂).FinTrace n ts := by
  rintro n ts ⟨ss, hss, hts⟩
  have hobs : (Q₁.compose Q₂).obs ⊆ (P₁.compose P₂).obs := by
    obtain ⟨hi₁, hi₂⟩ := Module.ag_intf hQ h₁ h₂
    exact Finset.union_subset
      ((Finset.union_subset_union hi₁ hi₂).trans Finset.subset_union_left) hextl
  obtain ⟨hss₁, hss₂⟩ := (Module.finRun_compose P₁ P₂ n ss).mp hss
  -- by induction on the number of rounds, `ss` is a trace of `Q₁` and of `Q₂`
  have full : ∀ k ≤ n, Q₁.PartialTrace k Set.univ ss ∧ Q₂.PartialTrace k Set.univ ss := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact Module.ag_round wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ hobs h₁ h₂
        (hss₁.mono hk) (hss₂.mono hk) (wQ₁.partialTrace_zero ss) (wQ₂.partialTrace_zero ss)
    | succ k ih =>
      intro hk
      obtain ⟨f₁, f₂⟩ := ih (by omega)
      exact Module.ag_round wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ hobs h₁ h₂
        (hss₁.mono hk) (hss₂.mono hk) (wQ₁.partialTrace_succ f₁) (wQ₂.partialTrace_succ f₂)
  obtain ⟨f₁, f₂⟩ := full n le_rfl
  obtain ⟨rr, hrr, hrro⟩ := Module.FinTrace.compose wQ₁ wQ₂ hQ f₁.finTrace f₂.finTrace
  exact ⟨rr, hrr, fun i hi x hx => (hrro i hi x hx).trans (hts i hi x (hobs hx))⟩

end AG

end Relational

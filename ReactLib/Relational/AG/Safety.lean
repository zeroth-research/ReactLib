import Relational.AG.Traces
import Mathlib.Order.KonigLemma

/-!
  The traces of a reactive module are a safety property: an ω-sequence all
  of whose prefixes are finite traces of a well-formed module `M` is a trace
  of `M`, when `M` is finitely branching (`Module.trace_of_finTraces`).

  `Module.FinBranching`: given the old state and the values of all
  non-private variables in the new state, a round allows finitely many values
  of the private variables. Finite private domains give it
  (`Module.FinBranching.of_finite`), and so do deterministic atoms
  (`Atom.FinBranching.ofFun`, `Module.FinBranching.of_atoms'`: only the atoms
  that write private variables matter), e.g. a private `Nat` counter
  (`Example.counter_finBranching`). It is preserved by composition
  (`Module.FinBranching.compose`). It is weaker than AH's executability of
  atoms (finitely many outputs per input), which `Atom` does not require.

  The proof is König's lemma for finitely branching chains
  (`exists_chain_of_finite_branching`). The runs witnessing the prefixes are
  first normalised to agree with the given sequence outside the private
  variables (`Module.withPriv`), which a well-formed module allows, since its
  atoms look only at its own variables. A normalised run is then a chain of
  valuations of the private variables.

  Some finiteness is needed, also of the initial round: let a private counter
  start anywhere and count down to zero, and let an interface bit tell
  whether it is positive. Every `1ᵏ` is a finite trace, but `1^ω` is not a
  trace.

  Conversely, every finite run of a well-formed module extends to a run
  (`Module.WF.extend_finRun`, [AH99, Prop. 1]), so trace inclusion gives
  finite-trace inclusion (`Module.finTraces_of_traces`). Hence `Implements`
  can be established from trace inclusion (`Module.Implements.of_trace`),
  and gives trace inclusion for finitely branching specifications
  (`Module.Implements.trace`).
-/

namespace Relational

universe u

/-- König's lemma for chains. If `R₀` holds of finitely many values, every
    value has finitely many `R i`-successors, and for every `n` some sequence
    starts in `R₀` and makes its first `n` steps along `R`, then some sequence
    starts in `R₀` and makes all its steps along `R`. From Mathlib's
    `exists_seq_forall_proj_of_forall_finite`, with the chains of length
    `n + 1` as level `n`. -/
theorem exists_chain_of_finite_branching {V : Type*} (R₀ : V → Prop)
    (R : Nat → V → V → Prop)
    (h₀ : {v | R₀ v}.Finite) (hR : ∀ i v, {v' | R i v v'}.Finite)
    (h : ∀ n, ∃ p : Nat → V, R₀ (p 0) ∧ ∀ i < n, R i (p i) (p (i + 1))) :
    ∃ p : Nat → V, R₀ (p 0) ∧ ∀ i, R i (p i) (p (i + 1)) := by
  -- `α n`: the chains of length `n`, projected to shorter ones by restriction
  let α (n : Nat) := {p : Fin (n + 1) → V //
    R₀ (p 0) ∧ ∀ k : Fin n, R k (p k.castSucc) (p k.succ)}
  let π {i j : Nat} (hij : i ≤ j) (b : α j) : α i :=
    ⟨fun k => b.1 (k.castLE (by omega)), by simpa using b.2.1,
      fun k => by simpa using b.2.2 (k.castLE hij)⟩
  have : Finite (α 0) := by
    have : Finite {v | R₀ v} := h₀.to_subtype
    refine Finite.of_injective (fun p : α 0 => (⟨p.1 0, p.2.1⟩ : {v | R₀ v})) ?_
    intro p q hpq
    apply Subtype.ext; funext k
    simpa [Fin.fin_one_eq_zero k] using congrArg Subtype.val hpq
  have : ∀ n, Nonempty (α n) := fun n => by
    obtain ⟨p, hp0, hp⟩ := h n
    exact ⟨⟨fun k => p k, hp0, fun k => hp k k.2⟩⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
    (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun i a => by
      -- an extension of `a` is determined by its last value, a successor
      let last := fun b : α (i + 1) => b.1 (Fin.last (i + 1))
      refine Set.Finite.of_finite_image (f := last) ((hR i (a.1 (Fin.last i))).subset ?_) ?_
      · rintro _ ⟨b, rfl, rfl⟩
        have hl : (Fin.last i).castLE (Nat.le_succ (i + 1)) = (Fin.last i).castSucc :=
          Fin.ext rfl
        show R i (b.1 ((Fin.last i).castLE _)) _
        rw [hl]
        exact b.2.2 (Fin.last i)
      · intro b hb c hc hbc
        change π (Nat.le_add_right i 1) b = a at hb
        change π (Nat.le_add_right i 1) c = a at hc
        apply Subtype.ext; funext k
        refine Fin.lastCases hbc (fun k => ?_) k
        exact congrArg (fun a : α i => a.1 k) (hb.trans hc.symm))
  refine ⟨fun n => (f n).1 (Fin.last n), by simpa using (f 0).2.1, fun n => ?_⟩
  have e : (f (n + 1)).1 (Fin.last n).castSucc = (f n).1 (Fin.last n) :=
    congrArg (fun a : α n => a.1 (Fin.last n)) (hf (Nat.le_succ n))
  have := (f (n + 1)).2.2 (Fin.last n)
  rw [Fin.succ_last, e] at this
  exact this

variable {Name : Type} {Dom : Name → Type u}

variable [DecidableEq Name]

/-- The state with the private variables of `M` as in `v` and all other
    names as in `t`. -/
def Module.withPriv (M : Module Dom) (t : State Dom) (v : Val Dom M.priv) : State Dom :=
  fun x => if h : x ∈ M.priv then v ⟨x, h⟩ else t x

/-- A state that agrees with `t` on the observable variables of a
    well-formed module `M` agrees on the variables of `M` with `t` taking its
    own values of the private variables. -/
theorem Module.WF.withPriv_eq {M : Module Dom} {s t : State Dom}
    (hobs : ∀ x ∈ M.obs, s x = t x) {x : Name} (hx : x ∈ M.vars) :
    M.withPriv t (s.restrict M.priv) x = s x := by
  by_cases hp : x ∈ M.priv
  · simp [Module.withPriv, hp]
  · have : x ∈ M.obs := by
      simp only [Module.vars, Module.obs, Finset.mem_union] at hx ⊢
      tauto
    simp [Module.withPriv, hp, hobs x this]

/-! ### Finite branching -/

/-- `M` is finitely branching: given the old state and the values of all
    other names in the new state, a round allows finitely many values of the
    private variables. -/
structure Module.FinBranching (M : Module Dom) : Prop where
  init : ∀ t : State Dom, {v : Val Dom M.priv | M.InitRound (M.withPriv t v)}.Finite
  update : ∀ s t : State Dom,
    {v : Val Dom M.priv | M.UpdateRound s (M.withPriv t v)}.Finite

/-- A module whose private variables have finite domains is finitely
    branching. -/
theorem Module.FinBranching.of_finite {M : Module Dom}
    (hfin : ∀ x ∈ M.priv, Finite (Dom x)) : M.FinBranching :=
  have : ∀ x : M.priv, Finite (Dom x) := fun x => hfin x x.2
  ⟨fun _ => Set.toFinite _, fun _ _ => Set.toFinite _⟩

/-- The traces of a well-formed, finitely branching module are a safety
    property: an ω-sequence all of whose prefixes are finite traces is a
    trace. -/
theorem Module.trace_of_finTraces {M : Module Dom} (hM : M.WF)
    (hfb : M.FinBranching) {ts : Cslib.ωSequence (State Dom)}
    (h : ∀ n, M.FinTrace n ts) : M.Trace ts := by
  obtain ⟨p, hp0, hp⟩ := exists_chain_of_finite_branching
    (fun v => M.InitRound (M.withPriv (ts 0) v))
    (fun i v v' => M.UpdateRound (M.withPriv (ts i) v) (M.withPriv (ts (i + 1)) v'))
    (hfb.init (ts 0)) (fun i v => hfb.update (M.withPriv (ts i) v) (ts (i + 1)))
    (fun n => by
      -- normalise the run of the prefix of length `n`
      obtain ⟨ss, ⟨hinit, hupd⟩, hobs⟩ := h n
      have heq : ∀ i ≤ n, ∀ x ∈ M.vars,
          ss i x = M.withPriv (ts i) ((ss i).restrict M.priv) x :=
        fun i hi x hx => (Module.WF.withPriv_eq (hobs i hi) hx).symm
      exact ⟨fun i => (ss i).restrict M.priv,
        hM.initRound_congr (heq 0 (Nat.zero_le n)) hinit,
        fun i hi => hM.updateRound_congr (heq i (by omega)) (heq (i + 1) (by omega))
          (hupd i hi)⟩)
  refine ⟨(fun i => M.withPriv (ts i) (p i) : Nat → State Dom), ⟨hp0, hp⟩,
    fun i x hx => ?_⟩
  have hx' : x ∉ M.priv := by
    have h₁ := Finset.disjoint_left.mp hM.intf_priv_disj
    have h₂ := Finset.disjoint_left.mp hM.extl_priv_disj
    simp only [Module.obs, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact h₁ hx
    · exact h₂ hx
  show M.withPriv (ts i) (p i) x = ts i x
  simp [Module.withPriv, hx']

/-! ### Finite branching of compositions -/

/-- On the variables of `M₁`, setting the private variables of `M₁ ∥ M₂` is
    setting those of `M₁`. -/
theorem Module.Composable.withPriv_left {M₁ M₂ : Module Dom} (hc : M₁.Composable M₂)
    (t : State Dom) (v : Val Dom (M₁.compose M₂).priv) {x : Name} (hx : x ∈ M₁.vars) :
    (M₁.compose M₂).withPriv t v x =
      M₁.withPriv t (fun y => v ⟨y, Finset.mem_union_left _ y.2⟩) x := by
  by_cases h₁ : x ∈ M₁.priv
  · simp [Module.withPriv, Module.compose, h₁]
  · have h₂ : x ∉ M₂.priv := fun h => Finset.disjoint_left.mp hc.priv₂_disj h hx
    simp [Module.withPriv, Module.compose, h₁, h₂]

theorem Module.Composable.withPriv_right {M₁ M₂ : Module Dom} (hc : M₁.Composable M₂)
    (t : State Dom) (v : Val Dom (M₁.compose M₂).priv) {x : Name} (hx : x ∈ M₂.vars) :
    (M₁.compose M₂).withPriv t v x =
      M₂.withPriv t (fun y => v ⟨y, Finset.mem_union_right _ y.2⟩) x := by
  by_cases h₂ : x ∈ M₂.priv
  · simp [Module.withPriv, Module.compose, h₂]
  · have h₁ : x ∉ M₁.priv := fun h => Finset.disjoint_left.mp hc.priv₁_disj h hx
    simp [Module.withPriv, Module.compose, h₁, h₂]

/-- Finite branching is preserved by composition. -/
theorem Module.FinBranching.compose {M₁ M₂ : Module Dom} (w₁ : M₁.WF) (w₂ : M₂.WF)
    (hc : M₁.Composable M₂) (h₁ : M₁.FinBranching) (h₂ : M₂.FinBranching) :
    (M₁.compose M₂).FinBranching := by
  -- a valuation of the private variables of `M₁ ∥ M₂` is a pair of valuations
  let φ : Val Dom (M₁.compose M₂).priv → Val Dom M₁.priv × Val Dom M₂.priv :=
    fun v => (fun y => v ⟨y, Finset.mem_union_left _ y.2⟩,
      fun y => v ⟨y, Finset.mem_union_right _ y.2⟩)
  have hφ : Function.Injective φ := by
    intro v w hvw
    funext ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hx' | hx'
    · exact congrFun (congrArg Prod.fst hvw) ⟨x, hx'⟩
    · exact congrFun (congrArg Prod.snd hvw) ⟨x, hx'⟩
  constructor
  · intro t
    refine (((h₁.init t).prod (h₂.init t)).preimage hφ.injOn).subset fun v hv => ?_
    obtain ⟨hv₁, hv₂⟩ := (Module.initRound_compose M₁ M₂ _).mp hv
    exact ⟨w₁.initRound_congr (fun x hx => hc.withPriv_left t v hx) hv₁,
      w₂.initRound_congr (fun x hx => hc.withPriv_right t v hx) hv₂⟩
  · intro s t
    refine (((h₁.update s t).prod (h₂.update s t)).preimage hφ.injOn).subset fun v hv => ?_
    obtain ⟨hv₁, hv₂⟩ := (Module.updateRound_compose M₁ M₂ _ _).mp hv
    exact ⟨w₁.updateRound_congr (fun _ _ => rfl) (fun x hx => hc.withPriv_left t v hx) hv₁,
      w₂.updateRound_congr (fun _ _ => rfl) (fun x hx => hc.withPriv_right t v hx) hv₂⟩

/-! ### A per-atom criterion -/

omit [DecidableEq Name] in
/-- The atom `A` is finitely branching in the variables `P`: given the values
    it reads and awaits, and the values of the variables it writes outside
    `P`, it allows finitely many values of the variables it writes. -/
structure Atom.FinBranching (A : Atom Dom) (P : Finset Name) : Prop where
  init : ∀ (a : Val Dom A.await) (t : State Dom),
    {w : Val Dom A.write | A.init a w ∧ ∀ x : A.write, ↑x ∉ P → w x = t x}.Finite
  update : ∀ (r : Val Dom A.read) (a : Val Dom A.await) (t : State Dom),
    {w : Val Dom A.write | A.update r a w ∧ ∀ x : A.write, ↑x ∉ P → w x = t x}.Finite

omit [DecidableEq Name] in
/-- An atom that writes no variable of `P` is finitely branching in `P`. -/
theorem Atom.FinBranching.of_disjoint {A : Atom Dom} {P : Finset Name}
    (hd : Disjoint A.write P) : A.FinBranching P := by
  have key : ∀ t : State Dom, ∀ w : Val Dom A.write,
      (∀ x : A.write, ↑x ∉ P → w x = t x) → w ∈ ({t.restrict A.write} : Set _) := by
    intro t w hw
    refine Set.mem_singleton_iff.mpr ?_
    funext x
    exact hw x (Finset.disjoint_left.mp hd x.2)
  exact ⟨fun a t => (Set.finite_singleton _).subset fun w hw => key t w hw.2,
    fun r a t => (Set.finite_singleton _).subset fun w hw => key t w hw.2⟩

omit [DecidableEq Name] in
/-- A deterministic atom is finitely branching. -/
theorem Atom.FinBranching.ofFun (await read write : Finset Name)
    (init : Val Dom await → Val Dom write)
    (update : Val Dom read → Val Dom await → Val Dom write)
    (hd : Disjoint await write) (P : Finset Name) :
    (Atom.ofFun await read write init update hd).FinBranching P :=
  ⟨fun a _ => (Set.finite_singleton (init a)).subset fun _ hw => hw.1,
    fun r a _ => (Set.finite_singleton (update r a)).subset fun _ hw => hw.1⟩

omit [DecidableEq Name] in
/-- An atom is finitely branching in `P` when the variables of `P` it writes
    have finite domains. -/
theorem Atom.FinBranching.of_finite {A : Atom Dom} {P : Finset Name}
    (hfin : ∀ x ∈ A.write, x ∈ P → Finite (Dom x)) : A.FinBranching P := by
  have key : ∀ t : State Dom,
      {w : Val Dom A.write | ∀ x : A.write, ↑x ∉ P → w x = t x}.Finite := by
    intro t
    refine Set.forall_finite_image_eval_iff.mp fun x => ?_
    by_cases hP : ↑x ∈ P
    · have := hfin x x.2 hP
      exact Set.toFinite _
    · refine (Set.finite_singleton (t x)).subset ?_
      rintro _ ⟨w, hw, rfl⟩
      exact hw x hP
  exact ⟨fun a t => (key t).subset fun w hw => hw.2,
    fun r a t => (key t).subset fun w hw => hw.2⟩

/-- The rounds of a well-formed module whose atoms are finitely branching in
    its private variables allow finitely many values of the private
    variables. The atoms are followed along their await dependencies: the
    private variables an atom awaits take finitely many values, each of which
    allows finitely many values of those it writes. -/
theorem Module.WF.finite_round {M : Module Dom} (hM : M.WF)
    (rel : ∀ A : Atom Dom, Val Dom A.await → Val Dom A.write → Prop)
    (hrel : ∀ A ∈ M.atoms, ∀ (a : Val Dom A.await) (t : State Dom),
      {w : Val Dom A.write | rel A a w ∧ ∀ x : A.write, ↑x ∉ M.priv → w x = t x}.Finite)
    (t : State Dom) :
    {v : Val Dom M.priv | ∀ A ∈ M.atoms,
      rel A ((M.withPriv t v).restrict A.await)
        ((M.withPriv t v).restrict A.write)}.Finite := by
  set S := {v : Val Dom M.priv | ∀ A ∈ M.atoms,
      rel A ((M.withPriv t v).restrict A.await)
        ((M.withPriv t v).restrict A.write)} with hS
  -- every private variable takes finitely many values, by induction along
  -- the await dependencies
  have key : ∀ x, ∀ hx : x ∈ M.priv,
      ((fun v : Val Dom M.priv => v ⟨x, hx⟩) '' S).Finite := by
    intro x
    induction x using hM.dependsOn_wf.induction with
    | _ x ih =>
      intro hx
      obtain ⟨A, hA, hxA⟩ := hM.atoms_cov_ctrl x (by simp [Module.ctrl, hx])
      -- the variables `A` awaits take finitely many values
      have hAw : ((fun v : Val Dom M.priv =>
          (M.withPriv t v).restrict A.await) '' S).Finite := by
        refine Set.forall_finite_image_eval_iff.mp fun ⟨y, hy⟩ => ?_
        rw [Set.image_image]
        by_cases hyp : y ∈ M.priv
        · refine (ih y ⟨A, hA, hxA, hy⟩ hyp).subset ?_
          rintro _ ⟨v, hv, rfl⟩
          exact ⟨v, hv, by simp [Module.withPriv, hyp]⟩
        · refine (Set.finite_singleton (t y)).subset ?_
          rintro _ ⟨v, hv, rfl⟩
          simp [Module.withPriv, hyp]
      have hW := hAw.biUnion fun a _ => hrel A hA a t
      refine (hW.image fun w => w ⟨x, hxA⟩).subset ?_
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨(M.withPriv t v).restrict A.write, ?_, by simp [Module.withPriv, hx]⟩
      simp only [Set.mem_iUnion]
      exact ⟨_, ⟨v, hv, rfl⟩, hv A hA,
        fun y hyp => by simp [Module.withPriv, hyp]⟩
  exact Set.forall_finite_image_eval_iff.mp fun x => key x x.2

/-- A well-formed module whose atoms are finitely branching in its private
    variables is finitely branching. -/
theorem Module.FinBranching.of_atoms {M : Module Dom} (hM : M.WF)
    (h : ∀ A ∈ M.atoms, A.FinBranching M.priv) : M.FinBranching :=
  ⟨fun t => hM.finite_round (fun A => A.init) (fun A hA a t => (h A hA).init a t) t,
    fun s t => hM.finite_round (fun A => A.update (s.restrict A.read))
      (fun A hA a t => (h A hA).update _ a t) t⟩

/-- Only the atoms that write a private variable matter. -/
theorem Module.FinBranching.of_atoms' {M : Module Dom} (hM : M.WF)
    (h : ∀ A ∈ M.atoms, ¬ Disjoint A.write M.priv → A.FinBranching M.priv) :
    M.FinBranching :=
  .of_atoms hM fun A hA => by
    by_cases hd : Disjoint A.write M.priv
    · exact .of_disjoint hd
    · exact h A hA hd

/-! ### Finite and infinite traces -/

/-- A finite run of a well-formed module extends to a run [AH99, Prop. 1]:
    a well-formed module never blocks. -/
theorem Module.WF.extend_finRun {M : Module Dom} (hM : M.WF) {n : Nat}
    {r : Nat → State Dom} (h : M.FinRun n r) :
    ∃ ss : Cslib.ωSequence (State Dom), M.Run ss ∧ ∀ i ≤ n, ss i = r i := by
  choose f hf using fun s => hM.exists_updateRound s s
  let g : Nat → State Dom := fun i => if i ≤ n then r i else f^[i - n] (r n)
  refine ⟨⟨g⟩, ⟨?_, fun i => ?_⟩, fun i hi => by show g i = r i; simp [g, hi]⟩
  · show M.InitRound (g 0); simpa [g] using h.1
  · show M.UpdateRound (g i) (g (i + 1))
    by_cases hi : i < n
    · simpa [g, show i ≤ n by omega, show i + 1 ≤ n by omega] using h.2 i hi
    · have e : i + 1 - n = (i - n) + 1 := by omega
      have hg : g (i + 1) = f (g i) := by
        simp only [g, show ¬ i + 1 ≤ n by omega, ite_false, e, Function.iterate_succ_apply']
        by_cases hin : i ≤ n
        · have : i = n := by omega
          subst this; simp
        · simp [hin]
      rw [hg]; exact (hf (g i)).1

/-- The finite traces of a well-formed module are the prefixes of its
    traces. -/
theorem Module.WF.finTrace_iff {M : Module Dom} (hM : M.WF) {n : Nat}
    {ts : Nat → State Dom} :
    M.FinTrace n ts ↔ ∃ ts' : Cslib.ωSequence (State Dom), M.Trace ts' ∧
      ∀ i ≤ n, ∀ x ∈ M.obs, ts' i x = ts i x := by
  constructor
  · rintro ⟨r, hr, ho⟩
    obtain ⟨ss, hrun, hss⟩ := hM.extend_finRun hr
    exact ⟨ss, hrun.trace, fun i hi x hx => by rw [hss i hi]; exact ho i hi x hx⟩
  · rintro ⟨ts', ⟨ss, hrun, hss⟩, h⟩
    exact ⟨ss, hrun.finRun n, fun i hi x hx => (hss i x hx).trans (h i hi x hx)⟩

/-- Trace inclusion implies finite-trace inclusion, for a well-formed
    implementation. -/
theorem Module.finTraces_of_traces {P Q : Module Dom} (hP : P.WF) (hobs : Q.obs ⊆ P.obs)
    (h : ∀ ts, P.Trace ts → Q.Trace ts) : ∀ n ts, P.FinTrace n ts → Q.FinTrace n ts := by
  intro n ts hts
  obtain ⟨ts', ht', hagree⟩ := hP.finTrace_iff.mp hts
  obtain ⟨q, hq, hqo⟩ := (h ts' ht').finTrace n
  exact ⟨q, hq, fun i hi x hx => (hqo i hi x hx).trans (hagree i hi x (hobs hx))⟩

/-- Finite-trace inclusion implies trace inclusion for a finitely branching
    specification. -/
theorem Module.Implements.trace {P Q : Module Dom} (h : P.Implements Q) (hQ : Q.WF)
    (hfb : Q.FinBranching) : ∀ ts, P.Trace ts → Q.Trace ts :=
  fun _ hts => Module.trace_of_finTraces hQ hfb fun n => h.traces n _ (hts.finTrace n)

/-- `Implements` with trace inclusion in place of finite-trace inclusion,
    for a well-formed implementation. -/
theorem Module.Implements.of_trace {P Q : Module Dom} (hP : P.WF)
    (intf : Q.intf ⊆ P.intf) (extl : Q.extl ⊆ P.obs)
    (awaits : ∀ x ∈ Q.obs, ∀ y ∈ Q.intf, Q.Awaits y x → P.Awaits y x)
    (h : ∀ ts, P.Trace ts → Q.Trace ts) : P.Implements Q where
  intf := intf
  extl := extl
  awaits := awaits
  traces := Module.finTraces_of_traces hP
    (Finset.union_subset (intf.trans Finset.subset_union_left) extl) h

/-! ### Example: a private counter -/

namespace Example

/-- A deterministic counter over `Nat`. -/
def counterAtom : Atom (fun _ : Unit => Nat) :=
  Atom.ofFun ∅ {()} {()} (fun _ _ => 0) (fun r _ _ => r ⟨(), by simp⟩ + 1) (by simp)

/-- A module with a private counter and nothing else. -/
def counter : Module (fun _ : Unit => Nat) where
  intf := ∅
  extl := ∅
  priv := {()}
  atoms := [counterAtom]

theorem counter_wf : counter.WF where
  intf_extl_disj := by simp [counter]
  intf_priv_disj := by simp [counter]
  extl_priv_disj := by simp [counter]
  atoms_pairwise_disj := by simp [counter]
  atoms_cov_ctrl := by simp [counter, Module.ctrl, counterAtom, Atom.ofFun]
  atoms_write_ctrl := by simp [counter, Module.ctrl, counterAtom, Atom.ofFun]
  atoms_read_vars := by simp [counter, Module.vars, counterAtom, Atom.ofFun]
  atoms_await_vars := by simp [counter, Module.vars, counterAtom, Atom.ofFun]
  atoms_acyclic := by
    intro a _ h
    obtain ⟨b, ⟨ha, -, x, hx, -⟩, -⟩ := Relation.TransGen.head'_iff.mp h
    simp only [counter, List.mem_singleton] at ha
    subst ha
    simp [counterAtom, Atom.ofFun] at hx

/-- The counter is finitely branching, though its private variable has an
    infinite domain. -/
theorem counter_finBranching : counter.FinBranching :=
  .of_atoms counter_wf fun A hA => by
    simp only [counter, List.mem_singleton] at hA
    subst hA
    exact .ofFun ..

example : ¬ ∀ x ∈ counter.priv, Finite ((fun _ : Unit => Nat) x) :=
  fun h => have := h () (by simp [counter]); not_finite Nat

/-- So its traces are limit-closed. -/
example {ts : Cslib.ωSequence (State fun _ : Unit => Nat)}
    (h : ∀ n, counter.FinTrace n ts) : counter.Trace ts :=
  Module.trace_of_finTraces counter_wf counter_finBranching h

end Example

end Relational

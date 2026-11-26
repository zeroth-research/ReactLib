import Relational.Semantics
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Bounds.Basic

/-!
  The traces of a reactive module are a safety property: an ω-sequence all
  of whose prefixes are finite traces of a well-formed module `M` is a trace
  of `M`, when the private variables of `M` have finite domains
  (`Module.trace_of_finTraces`).

  This is König's lemma. The runs witnessing the prefixes are first
  normalised to agree with the given sequence outside the private variables
  (`Module.withPriv`), which a well-formed module allows, since its atoms
  look only at its own variables. A normalised run is then a sequence of
  valuations of the private variables, of which there are finitely many
  (`Val.finite`), and each round relates only consecutive ones, so König's
  lemma for chains in a finite type applies (`exists_chain_of_finite`).

  Finiteness is needed: let a private counter start anywhere and count down
  to zero, and let an interface bit tell whether it is positive. Every
  `1ᵏ` is a finite trace, but `1^ω` is not a trace.
-/

namespace Relational

universe u

/-- König's lemma for chains in a finite type. If for every `n` some sequence
    starts in `R₀` and makes its first `n` steps along `R`, then some sequence
    starts in `R₀` and makes all its steps along `R`. -/
theorem exists_chain_of_finite {V : Type*} [Finite V] (R₀ : V → Prop)
    (R : Nat → V → V → Prop)
    (h : ∀ n, ∃ p : Nat → V, R₀ (p 0) ∧ ∀ i < n, R i (p i) (p (i + 1))) :
    ∃ p : Nat → V, R₀ (p 0) ∧ ∀ i, R i (p i) (p (i + 1)) := by
  -- `Ext k v`: chains of every length pass through `v` at position `k`
  let Ext (k : Nat) (v : V) : Prop :=
    ∀ n, k ≤ n → ∃ p : Nat → V, (R₀ (p 0) ∧ ∀ i < n, R i (p i) (p (i + 1))) ∧ p k = v
  -- some initial value extends to every length
  have h0 : ∃ v, Ext 0 v := by
    by_contra hne
    have : ∀ v, ∃ n, ∀ p : Nat → V,
        (R₀ (p 0) ∧ ∀ i < n, R i (p i) (p (i + 1))) → p 0 ≠ v := by
      intro v
      by_contra hv
      exact hne ⟨v, fun n _ => by
        by_contra hn
        exact hv ⟨n, fun p hp hpv => hn ⟨p, hp, hpv⟩⟩⟩
    choose f hf using this
    obtain ⟨N, hN⟩ := (Set.finite_range f).bddAbove
    obtain ⟨p, hp0, hp⟩ := h N
    exact hf (p 0) p ⟨hp0, fun i hi => hp i (lt_of_lt_of_le hi (hN ⟨_, rfl⟩))⟩ rfl
  -- and so does one of the successors of a value that does
  have hstep : ∀ k v, Ext k v → ∃ v', Ext (k + 1) v' ∧ R k v v' := by
    intro k v hv
    by_contra hne
    have : ∀ v', ∃ n, R k v v' → k + 1 ≤ n ∧ ∀ p : Nat → V,
        (R₀ (p 0) ∧ ∀ i < n, R i (p i) (p (i + 1))) → p (k + 1) ≠ v' := by
      intro v'
      by_contra hv'
      refine hne ⟨v', fun n hn => ?_, ?_⟩
      · by_contra hn'
        exact hv' ⟨n, fun _ => ⟨hn, fun p hp hpv => hn' ⟨p, hp, hpv⟩⟩⟩
      · by_contra hR
        exact hv' ⟨0, fun hR' => absurd hR' hR⟩
    choose f hf using this
    obtain ⟨N, hN⟩ := (Set.finite_range f).bddAbove
    obtain ⟨p, ⟨hp0, hp⟩, hpk⟩ := hv (max N (k + 1)) (by omega)
    have hR : R k v (p (k + 1)) := hpk ▸ hp k (by omega)
    have hle : f (p (k + 1)) ≤ N := hN ⟨_, rfl⟩
    exact (hf (p (k + 1)) hR).2 p ⟨hp0, fun i hi => hp i (by omega)⟩ rfl
  choose g hg hgR using hstep
  let q : (k : Nat) → {v // Ext k v} :=
    fun k => Nat.rec ⟨h0.choose, h0.choose_spec⟩ (fun k v => ⟨g k v.1 v.2, hg k v.1 v.2⟩) k
  refine ⟨fun k => (q k).1, ?_, fun k => hgR k (q k).1 (q k).2⟩
  obtain ⟨p, ⟨hp0, -⟩, hp⟩ := (q 0).2 0 le_rfl
  show R₀ (q 0).1
  exact hp ▸ hp0

variable {Name : Type} {Dom : Name → Type u}

/-- The valuations of finitely many variables with finite domains are
    finitely many. -/
theorem Val.finite {X : Finset Name} (hfin : ∀ x ∈ X, Finite (Dom x)) :
    Finite (Val Dom X) := by
  have : ∀ x : X, Finite (Dom x.1) := fun x => hfin x.1 x.2
  refine Finite.of_injective (fun (v : Val Dom X) (x : X) => v x.1 x.2) fun v w hvw => ?_
  funext x hx
  exact congrFun hvw ⟨x, hx⟩

variable [DecidableEq Name]

/-- The state with the private variables of `M` as in `v` and all other
    names as in `t`. -/
def Module.withPriv (M : Module Dom) (t : State Dom) (v : Val Dom M.priv) : State Dom :=
  fun x => if h : x ∈ M.priv then v x h else t x

/-- A state that agrees with `t` on the observable variables of a
    well-formed module `M` agrees on the variables of `M` with `t` taking its
    own values of the private variables. -/
theorem Module.WF.withPriv_eq {M : Module Dom} {s t : State Dom}
    (hobs : ∀ x ∈ M.obs, s x = t x) {x : Name} (hx : x ∈ M.vars) :
    M.withPriv t (s.restrict M.priv) x = s x := by
  by_cases hp : x ∈ M.priv
  · simp [Module.withPriv, hp, State.restrict]
  · have : x ∈ M.obs := by
      simp only [Module.vars, Module.obs, Finset.mem_union] at hx ⊢
      tauto
    simp [Module.withPriv, hp, hobs x this]

/-- An initial round of a well-formed module depends only on the variables
    of the module. -/
theorem Module.WF.initRound_congr {M : Module Dom} (hM : M.WF) {s t : State Dom}
    (h : ∀ x ∈ M.vars, s x = t x) (hs : M.InitRound s) : M.InitRound t := by
  intro A hA
  have ha : t.restrict A.await = s.restrict A.await :=
    funext fun x => funext fun hx => (h x (hM.atoms_await_vars A hA hx)).symm
  have hw : t.restrict A.write = s.restrict A.write :=
    funext fun x => funext fun hx => (h x (by
      have := hM.atoms_write_ctrl A hA hx
      simp only [Module.ctrl, Module.vars, Finset.mem_union] at this ⊢
      tauto)).symm
  simpa only [Atom.Init, ha, hw] using hs A hA

/-- An update round of a well-formed module depends only on the variables
    of the module. -/
theorem Module.WF.updateRound_congr {M : Module Dom} (hM : M.WF) {s s' t t' : State Dom}
    (h : ∀ x ∈ M.vars, s x = t x) (h' : ∀ x ∈ M.vars, s' x = t' x)
    (hs : M.UpdateRound s s') : M.UpdateRound t t' := by
  intro A hA
  have hr : t.restrict A.read = s.restrict A.read :=
    funext fun x => funext fun hx => (h x (hM.atoms_read_vars A hA hx)).symm
  have ha : t'.restrict A.await = s'.restrict A.await :=
    funext fun x => funext fun hx => (h' x (hM.atoms_await_vars A hA hx)).symm
  have hw : t'.restrict A.write = s'.restrict A.write :=
    funext fun x => funext fun hx => (h' x (by
      have := hM.atoms_write_ctrl A hA hx
      simp only [Module.ctrl, Module.vars, Finset.mem_union] at this ⊢
      tauto)).symm
  simpa only [Atom.Update, hr, ha, hw] using hs A hA

/-- The traces of a well-formed module whose private variables have finite
    domains are a safety property: an ω-sequence all of whose prefixes are
    finite traces is a trace. -/
theorem Module.trace_of_finTraces {M : Module Dom} (hM : M.WF)
    (hfin : ∀ x ∈ M.priv, Finite (Dom x)) {ts : Cslib.ωSequence (State Dom)}
    (h : ∀ n, M.FinTrace n ts) : M.Trace ts := by
  have := Val.finite hfin
  obtain ⟨p, hp0, hp⟩ := exists_chain_of_finite
    (fun v => M.InitRound (M.withPriv (ts 0) v))
    (fun i v v' => M.UpdateRound (M.withPriv (ts i) v) (M.withPriv (ts (i + 1)) v'))
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

end Relational

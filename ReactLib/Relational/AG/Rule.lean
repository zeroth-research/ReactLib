import Relational.AG.Traces
import Relational.AG.Safety

/-!
  Alur and Henzinger's assume-guarantee rule for reactive modules
  (`Relational.Module`), [AH99, Prop. 5]: if `P₁ ∥ Q₂` implements `Q₁` and
  `Q₁ ∥ P₂` implements `Q₂`, then `P₁ ∥ P₂` implements `Q₁ ∥ Q₂`.

  The implementation preorder is AH's Def. 3 (`Module.Implements`), with
  finite traces. Over ω-traces the rule also needs the private variables of
  the specifications to have finite domains
  (`Module.assume_guarantee_trace`). Premises given as trace inclusions turn
  into `Implements` by `Module.Implements.of_trace`.

  Also here: a composition implements its components
  (`Module.compose_implements_left`, `_right`), and `Implements` is a
  precongruence for composition [AH99, Prop. 4] (`Module.Implements.compose`).

  AH also rename the private variables of an implementation apart from its
  specification. This is not needed: `Pⱼ` and `Qⱼ` are never composed, and the
  four `Composable` hypotheses give every disjointness the proof uses.

  Clauses (1) and (3) of `Module.assume_guarantee` are in
  `Relational.AG.Lemmas`, and trace inclusion (clause (4), `Module.ag_traces`)
  in `Relational.AG.Traces`. `Module.assume_guarantee_trace` follows by
  König's lemma (`Module.trace_of_finTraces`, `Relational.AG.Safety`).
-/

namespace Relational

universe u

variable {Name : Type} [DecidableEq Name] {Dom : Name → Type u}

/-- The assume-guarantee rule [AH99, Prop. 5]. -/
theorem Module.assume_guarantee {P₁ P₂ Q₁ Q₂ : Module Dom}
    (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    -- the four composites are defined
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    -- every external variable of `Q₁ ∥ Q₂` is observable in `P₁ ∥ P₂`
    (hextl : (Q₁.compose Q₂).extl ⊆ (P₁.compose P₂).obs)
    -- the premises
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂) :
    (P₁.compose P₂).Implements (Q₁.compose Q₂) where
  intf := by
    obtain ⟨i₁, i₂⟩ := Module.ag_intf hQ h₁ h₂
    exact Finset.union_subset_union i₁ i₂
  extl := hextl
  awaits := Module.ag_awaits wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ h₁ h₂
  traces := Module.ag_traces wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ hextl h₁ h₂

/-- The assume-guarantee rule over ω-traces. Prefix containment gives
    ω-trace containment by König's lemma, which needs the private variables
    of the specifications to have finite domains. -/
theorem Module.assume_guarantee_trace {P₁ P₂ Q₁ Q₂ : Module Dom}
    (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    (hextl : (Q₁.compose Q₂).extl ⊆ (P₁.compose P₂).obs)
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂)
    (hfin : ∀ x ∈ Q₁.priv ∪ Q₂.priv, Finite (Dom x)) :
    ∀ ts, (P₁.compose P₂).Trace ts → (Q₁.compose Q₂).Trace ts :=
  fun _ h => Module.trace_of_finTraces (wQ₁.compose wQ₂ hQ) hfin fun n =>
    (Module.assume_guarantee wP₁ wP₂ wQ₁ wQ₂ hP hQ hP₁Q₂ hQ₁P₂ hextl h₁ h₂).traces n _
      (h.finTrace n)

/-! ### Compositionality -/

/-- A composition implements its left component. -/
theorem Module.compose_implements_left (M N : Module Dom) : (M.compose N).Implements M where
  intf := Finset.subset_union_left
  extl := fun _ hx => Module.obs_subset_compose_left M N (Finset.mem_union_right _ hx)
  awaits _ _ _ _ h := Relation.TransGen.mono
    (fun _ _ hd => Atom.dependsOn_append.mpr (.inl hd)) _ _ h
  traces := by
    rintro n ts ⟨r, hr, ho⟩
    exact ⟨r, ((Module.finRun_compose M N n r).mp hr).1,
      fun i hi x hx => ho i hi x (Module.obs_subset_compose_left M N hx)⟩

/-- A composition implements its right component. -/
theorem Module.compose_implements_right (M N : Module Dom) : (M.compose N).Implements N where
  intf := Finset.subset_union_right
  extl := fun _ hx => Module.obs_subset_compose_right M N (Finset.mem_union_right _ hx)
  awaits _ _ _ _ h := Relation.TransGen.mono
    (fun _ _ hd => Atom.dependsOn_append.mpr (.inr hd)) _ _ h
  traces := by
    rintro n ts ⟨r, hr, ho⟩
    exact ⟨r, ((Module.finRun_compose M N n r).mp hr).2,
      fun i hi x hx => ho i hi x (Module.obs_subset_compose_right M N hx)⟩

/-- Compositionality [AH99, Prop. 4]: if `P` implements `Q`, then `P ∥ R`
    implements `Q ∥ R`. An instance of the assume-guarantee rule. -/
theorem Module.Implements.compose {P Q R : Module Dom} (h : P.Implements Q)
    (wP : P.WF) (wQ : Q.WF) (wR : R.WF) (hPR : P.Composable R) (hQR : Q.Composable R) :
    (P.compose R).Implements (Q.compose R) := by
  refine Module.assume_guarantee wP wR wQ wR hPR hQR hPR hQR ?_
    ((Module.compose_implements_left P R).trans h) (Module.compose_implements_right Q R)
  intro x hx
  simp only [Module.compose, Finset.mem_sdiff, Finset.mem_union] at hx
  rcases hx.1 with hx | hx
  · exact Module.obs_subset_compose_left P R (h.extl hx)
  · exact Module.obs_subset_compose_right P R (Finset.mem_union_right _ hx)

end Relational

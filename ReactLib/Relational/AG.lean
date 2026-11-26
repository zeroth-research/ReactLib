import Relational.Semantics

/-!
  Alur and Henzinger's assume-guarantee rule for reactive modules
  (`Relational.Module`), [AH99, Prop. 5]: if `P₁ ∥ Q₂` implements `Q₁` and
  `Q₁ ∥ P₂` implements `Q₂`, then `P₁ ∥ P₂` implements `Q₁ ∥ Q₂`.

  The implementation preorder is AH's Def. 3 (`Module.Implements`), with
  finite traces (`Module.FinTrace`). Over ω-traces the rule also needs the
  private variables of the specifications to have finite domains
  (`Module.assume_guarantee_trace`); see `notes/AG-FINDINGS.md`, Step 6.

  The rules are stated only; their proofs are `sorry`.
-/

namespace Relational

universe u

variable {Name : Type} [DecidableEq Name] {Dom : Name → Type u}

/-- In `M`, the new value of `y` depends, transitively, on the new value of
    `x`: AH's `y ≻_M x`. -/
def Module.Awaits (M : Module Dom) (y x : Name) : Prop :=
  Relation.TransGen (Atom.dependsOn M.atoms) y x

/-- `P` implements `Q` [AH99, Def. 3]. -/
structure Module.Implements (P Q : Module Dom) : Prop where
  -- (1) every interface variable of `Q` is an interface variable of `P`
  intf : Q.intf ⊆ P.intf
  -- (2) every external variable of `Q` is an observable variable of `P`
  extl : Q.extl ⊆ P.obs
  -- (3) `P` has at least the await dependencies of `Q` from its interface
  -- variables to its observable variables
  awaits : ∀ x ∈ Q.obs, ∀ y ∈ Q.intf, Q.Awaits y x → P.Awaits y x
  -- (4) every trace of `P`, projected to the observable variables of `Q`, is
  -- a trace of `Q`. `FinTrace Q` looks only at those variables.
  traces : ∀ n ts, P.FinTrace n ts → Q.FinTrace n ts

theorem Module.Implements.obs_subset {P Q : Module Dom} (h : P.Implements Q) :
    Q.obs ⊆ P.obs := by
  intro x hx
  simp only [Module.obs, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact Finset.mem_union_left _ (h.intf hx)
  · exact h.extl hx

theorem Module.Implements.refl (P : Module Dom) : P.Implements P where
  intf := subset_rfl
  extl := Finset.subset_union_right
  awaits _ _ _ _ h := h
  traces _ _ h := h

theorem Module.Implements.trans {P Q R : Module Dom} (hPQ : P.Implements Q)
    (hQR : Q.Implements R) : P.Implements R where
  intf := hQR.intf.trans hPQ.intf
  extl := hQR.extl.trans hPQ.obs_subset
  awaits x hx y hy h :=
    hPQ.awaits x (hQR.obs_subset hx) y (hQR.intf hy) (hQR.awaits x hx y hy h)
  traces n ts h := hQR.traces n ts (hPQ.traces n ts h)

/-- AH's naming convention between an implementation `M` and its
    specification `N`, which are never composed: a private variable of
    either is not a variable of the other. -/
structure Module.Scoped (M N : Module Dom) : Prop where
  priv_left : Disjoint M.priv N.vars
  priv_right : Disjoint N.priv M.vars

/-- The assume-guarantee rule [AH99, Prop. 5]. -/
theorem Module.assume_guarantee {P₁ P₂ Q₁ Q₂ : Module Dom}
    (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    -- the four composites are defined
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    -- each implementation is scoped against its specification
    (s₁ : P₁.Scoped Q₁) (s₂ : P₂.Scoped Q₂)
    -- every external variable of `Q₁ ∥ Q₂` is observable in `P₁ ∥ P₂`
    (hextl : (Q₁.compose Q₂).extl ⊆ (P₁.compose P₂).obs)
    -- the premises
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂) :
    (P₁.compose P₂).Implements (Q₁.compose Q₂) := by
  sorry

/-- The assume-guarantee rule over ω-traces. Prefix containment gives
    ω-trace containment by König's lemma, which needs the private variables
    of the specifications to have finite domains. -/
theorem Module.assume_guarantee_trace {P₁ P₂ Q₁ Q₂ : Module Dom}
    (wP₁ : P₁.WF) (wP₂ : P₂.WF) (wQ₁ : Q₁.WF) (wQ₂ : Q₂.WF)
    (hP : P₁.Composable P₂) (hQ : Q₁.Composable Q₂)
    (hP₁Q₂ : P₁.Composable Q₂) (hQ₁P₂ : Q₁.Composable P₂)
    (s₁ : P₁.Scoped Q₁) (s₂ : P₂.Scoped Q₂)
    (hextl : (Q₁.compose Q₂).extl ⊆ (P₁.compose P₂).obs)
    (h₁ : (P₁.compose Q₂).Implements Q₁) (h₂ : (Q₁.compose P₂).Implements Q₂)
    (hfin : ∀ x ∈ Q₁.priv ∪ Q₂.priv, Finite (Dom x)) :
    ∀ ts, (P₁.compose P₂).Trace ts → (Q₁.compose Q₂).Trace ts := by
  sorry

end Relational

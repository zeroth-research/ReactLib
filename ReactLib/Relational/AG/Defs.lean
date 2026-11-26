import Relational.Semantics

/-!
  Alur and Henzinger's implementation preorder on reactive modules
  [AH99, Def. 3] (`Module.Implements`), with finite traces
  (`Module.FinTrace`), and the await dependencies it speaks about
  (`Module.Awaits`).
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

end Relational

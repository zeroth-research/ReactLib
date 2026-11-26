import Relational.Basic
import Spec.LTL
import Relational.Mat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
  Proof rules for LTL properties of transition systems: invariance
  (`G`), recurrence (`G F`) via ranking functions, and transfer of
  properties along a simulation.
-/

universe u v

/-  ----------------------------------------------------------------
 Proof rules
 ----------------------------------------------------------------- -/
section proof_rules

open LTLFormula

/-- Proof rule saying that if a set of states `S` is invariant,
    then `G S` holds on every trace (`S : StateSet State` is a `Set State`,
    a predicate on states, so it is an atomic proposition). -/
theorem rule_globally {State: Type u} {Label : Type v}
    (lts : TS State Label)
    (S : StateSet State)
    (hinv : lts.StateSet_isInvariant S) :
    ∀ ss μs, lts.ωTrace ss μs → ss ⊧ G (AP S) := by
  intro ss μs htr
  simp [Globally]
  simp [Finally]
  simp [sem]
  intro x
  rw [(drop_get_zero ss x).symm]
  exact lts.trace_states_in_invariant S hinv htr x


/-- `rule_buchi` with the hypothesis on the ranking function curried. -/
theorem rule_buchi' {State: Type u} {Label : Type v}
    (lts : TS State Label)                    -- the TS
    (B : State → Prop)                        -- proposition `B`
    (I : StateSet State)                      -- invariant `I`
    (hinv : lts.StateSet_isInvariant I)
    (V : State → Nat)                         -- ranking function on
                                              -- (I ∧ ¬B)-states
    -- assume `V` is a function such that whenever `B` does not hold,
    -- then in next steps the value of `V` decreases
    (hrank : ∀ s s', I s → ¬(B s) → (∃ l, lts.Tr s l s') → V s' < V s) :
    -- Then `B` holds infinitely many times
    ∀ ss μs, lts.ωTrace ss μs → ss ⊧ G (F (AP B)) := by
  intro ss μs htr
  have hI := lts.trace_states_in_invariant I hinv htr
  rw [Globally.explicit]
  intro i
  rw [Finally.explicit]
  by_contra! h
  simp only [sem, ← drop_get_zero] at h
  -- staying in `¬B` from `i` on, `V` would decrease forever
  have hdec : ∀ k, V (ss.get (i + k)) + k ≤ V (ss.get i) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have : V (ss.get (i + k + 1)) < V (ss.get (i + k)) :=
        hrank _ _ (hI (i + k)) (drop_get_n ss i k ▸ h k) ⟨μs.get (i + k), htr.2 (i + k)⟩
      show V (ss.get (i + k + 1)) + (k + 1) ≤ _; omega
  have := hdec (V (ss.get i) + 1)
  omega

/-- Proof rule saying that if we have a ranking function
    on `¬B` states (states where `B` does not hold),
    then every trace in the transition system visits
    `B` states infinitely often. (The existence of such
    function proves that no trace stays in `¬B` states
    forever; `¬B` states may still recur infinitely often.)

    To make the statement more powerful, we work relative to
    states `I` that overapproximate all states in the system
    (`I` is an invariant). This is important, because this
    makes `V` easier to find (without `I`, `V` would have to work
    for *all* possible states, not only reachable states).
    At the same time, we work with `I` instead of reachable states,
    because reachable states might be hard/impossible to represent
    or even compute exactly. Obtaining a superset might be much
    easier.
-/
theorem rule_buchi {State: Type u} {Label : Type v}
    (lts : TS State Label)                    -- the TS
    (B : State → Prop)                        -- proposition `B`
    (I : StateSet State)                      -- invariant `I`
    (hinv : lts.StateSet_isInvariant I)
    (V : State → Nat)                         -- ranking function on
                                              -- (I ∧ ¬B)-states
    -- assume `V` is a function such that whenever `B` does not hold,
    -- then in next steps the value of `V` decreases
    (hrank : ∀ s s', I s ∧ ¬(B s) ∧ (∃ l, lts.Tr s l s') → V s' < V s) :
    -- Then `B` holds infinitely many times
    ∀ ss μs, lts.ωTrace ss μs → ss ⊧ G (F (AP B)) :=
  rule_buchi' lts B I hinv V fun s s' a b c => hrank s s' ⟨a, b, c⟩


/-- Every run of `A` is a run of `B`, so a `G`-property of `B` is one of `A`.

    A certificate about a *model* of a module (e.g. its NA encoding) carries
    back to the module: `f` maps a module state to the model's state,
    `hinit`/`hstep` say the model admits every module step, and the property
    comes back through `f`. Only one direction is needed,
    because a model with *more* behaviours still satisfies `G Q` on fewer.

    `g` relabels. The two systems agree about states and need not agree
    about labels: a reactive module is labelled by its external inputs,
    while the NA model reads its inputs out of the state and is labelled by
    `Unit × Unit`. Nothing here reads a label, so `g` only has to exist. -/
theorem TS.transfer {S : Type u} {T : Type u} {L : Type v} {L' : Type v}
    (A : TS S L) (B : TS T L') (f : S → T) (g : L → L')
    (hinit : ∀ s, A.start s → B.start (f s))
    (hstep : ∀ s l s', A.Tr s l s' → B.Tr (f s) (g l) (f s'))
    (Q : StateSet T)
    (hB : ∀ ts μs, B.ωTrace ts μs → ts ⊧ G (AP Q)) :
    ∀ ss μs, A.ωTrace ss μs → ss ⊧ G (AP (fun s => Q (f s))) := by
  intro ss μs htr
  have hmap : B.ωTrace (Cslib.ωSequence.map f ss) (Cslib.ωSequence.map g μs) :=
    ⟨hinit _ htr.1, fun i => hstep _ _ _ (htr.2 i)⟩
  have h := hB _ _ hmap
  simp [sem] at h ⊢
  intro x
  exact h x


theorem rule_buchi_mat_nat
    {State: Type u} {Label : Type v}
    ----------
    (lts : TS State Label)                    -- the TS
    (B : State → Prop)                        -- proposition `B`
    (I : StateSet State)                      -- invariant `I`
    (hinv : lts.StateSet_isInvariant I)
    (V : State → (Matrix (Fin v₁) (Fin v₂) Nat))             -- ranking function on
                                              -- (I ∧ ¬B)-states
    -- assume that whenever `B` does not hold, then in the next step `V`
    -- decreases (its entries are natural numbers, so bounded below)
    (h_rank : ∀ s s', I s ∧ ¬(B s) ∧ (∃ l, lts.Tr s l s')
              → (∀ x y, (V s') x y ≤ (V s) x y) ∧ (∃ x y, (V s') x y < (V s) x y)):
    -- Then `B` holds infinitely many times
    ∀ ss μs, lts.ωTrace ss μs → ss ⊧ G (F (AP B)) := by
  apply rule_buchi lts B I hinv
    (fun s => Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => (V s) i j)))
  intro s s' ⟨hIs, hBs, htr⟩
  obtain ⟨hle, x, y, hlt⟩ := h_rank s s' ⟨hIs, hBs, htr⟩
  exact Finset.sum_lt_sum
    (fun i _ => Finset.sum_le_sum (fun j _ => hle i j))
    ⟨x, Finset.mem_univ x, Finset.sum_lt_sum (fun j _ => hle x j)
      ⟨y, Finset.mem_univ y, hlt⟩⟩


theorem rule_buchi_mat_int
    {State: Type u} {Label : Type v}
    ----------
    (lts : TS State Label)                    -- the TS
    (B : State → Prop)                        -- proposition `B`
    (I : StateSet State)                      -- invariant `I`
    (hinv : lts.StateSet_isInvariant I)
    (V : State → (Matrix (Fin v₁) (Fin v₂) Int))             -- ranking function on
                                              -- (I ∧ ¬B)-states
    -- assume that `V` is bounded below (`h_rankpos`) and that whenever `B`
    -- does not hold, then in the next step `V` decreases
    (h_rankpos: ∀ s x y, (V s) x y ≥ 0)
    (h_rank : ∀ s s', I s ∧ ¬(B s) ∧ (∃ l, lts.Tr s l s')
              → (∀ x y, (V s') x y ≤ (V s) x y) ∧ (∃ x y, (V s') x y < (V s) x y)):
    -- Then `B` holds infinitely many times
    ∀ ss μs, lts.ωTrace ss μs → ss ⊧ G (F (AP B)) := by
    apply rule_buchi_mat_nat lts B I hinv (fun s i j => (V s i j).toNat)
    intro s s' ⟨hIs, hBs, htr⟩
    obtain ⟨hle, x, y, hlt⟩ := h_rank s s' ⟨hIs, hBs, htr⟩
    refine ⟨fun i j => ?_, x, y, ?_⟩
    · have h1 : (V s') i j ≥ 0 := h_rankpos s' i j
      have h2 : (V s') i j ≤ (V s) i j := hle i j
      exact Int.toNat_le_toNat (hle i j)
    · have := h_rankpos s x y
      have := h_rankpos s' x y
      omega


end proof_rules

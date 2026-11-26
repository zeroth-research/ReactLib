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

/-- Proof rule saying that if a set of states S is invariant,
    then `Globally S` holds on every trace
    (S is state of sets which is the same as atomic proposition) -/
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
    (B : State → Prop) [DecidablePred B]      -- proposition `B`
    (I : StateSet State)                      -- invariant `I`
    (hinv : lts.StateSet_isInvariant I)
    (V : State → Nat)                         -- ranking function on
                                              -- (I ∧ ¬B)-states
    -- assume `V` is a function such that whenever `B` does not hold,
    -- then in next steps the value of `V` decreases
    (hrank : ∀ s s', I s ∧ ¬(B s) ∧ (∃ l, lts.Tr s l s') → V s' < V s) :
    -- Then then `B` holds infinitely many times
    ∀ ss μs, lts.ωTrace ss μs → ss ⊧ G (F (AP B)) := by
  intro ss μs htr
  simp [LTLFormula.sem]
  simp [<- drop_get_zero]
  have hI := lts.trace_states_in_invariant I hinv htr
  have hstep : ∀ j, ∃ l, lts.Tr (ss.get j) l (ss.get (j + 1)) := by
    intro j; exists μs.get j; exact htr.2 j
  intro i
  suffices ∀ k n, V (ss.get n) ≤ k → ∃ x, B (ss.get (n + x)) from
    this (V (ss.get i)) i (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro n hv
    exists 0
    simp
    if hb : B (ss.get n) then
      exact hb
    else
      have : V (ss.get n) ≤ V (ss.get (n + 1)) := by simp_all
      exact absurd (hrank _ _ ⟨ (hI n), hb, (hstep n)⟩) (Nat.not_lt.mpr this)
  | succ k ih =>
    intro n hv
    if hb : B (ss.get n) then
      exact ⟨0, by simp; exact hb⟩
    else
      have hdec := hrank _ _ ⟨ hI n, hb, (hstep n)⟩
      obtain ⟨x, hbx⟩ := ih (n + 1) (by omega)
      exists x + 1
      have : n + (x + 1) = n + 1 + x := by omega
      rw [this]
      exact hbx


/-- Every run of `A` is a run of `B`, so a `G`-property of `B` is one of `A`.

    The `--fbk-proveit` route ends in a certificate about a *model* -- the NA
    encoding `infer/fbk_proveit/na.py` writes and `lean2vmt` reads. This is
    what carries that back to the module: `f` maps a module state to the
    model's slots, `hinit`/`hstep` say the model admits every module step,
    and the property comes back through `f`. Only one direction is needed,
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


/-- `rule_buchi` with the hypothesis on the ranking function curried. -/
theorem rule_buchi' {State: Type u} {Label : Type v}
    (lts : TS State Label)                    -- the TS
    (B : State → Prop) [DecidablePred B]      -- proposition `B`
    (I : StateSet State)                      -- invariant `I`
    (hinv : lts.StateSet_isInvariant I)
    (V : State → Nat)                         -- ranking function on
                                              -- (I ∧ ¬B)-states
    -- assume `V` is a function such that whenever `B` does not hold,
    -- then in next steps the value of `V` decreases
    (hrank : ∀ s s', I s → ¬(B s) → (∃ l, lts.Tr s l s') → V s' < V s) :
    -- Then then `B` holds infinitely many times
    ∀ ss μs, lts.ωTrace ss μs → ss ⊧ G (F (AP B)) := by
  intro ss μs htr
  simp [LTLFormula.sem]
  simp [<- drop_get_zero]
  have hI := lts.trace_states_in_invariant I hinv htr
  have hstep : ∀ j, ∃ l, lts.Tr (ss.get j) l (ss.get (j + 1)) := by
    intro j; exists μs.get j; exact htr.2 j
  intro i
  suffices ∀ k n, V (ss.get n) ≤ k → ∃ x, B (ss.get (n + x)) from
    this (V (ss.get i)) i (Nat.le_refl _)
  intro k
  induction k with
  | zero =>
    intro n hv
    exists 0
    simp
    if hb : B (ss.get n) then
      exact hb
    else
      have : V (ss.get n) ≤ V (ss.get (n + 1)) := by simp_all
      exact absurd (hrank _ _ (hI n) hb (hstep n)) (Nat.not_lt.mpr this)
  | succ k ih =>
    intro n hv
    if hb : B (ss.get n) then
      exact ⟨0, by simp; exact hb⟩
    else
      have hdec := hrank _ _ (hI n) hb (hstep n)
      obtain ⟨x, hbx⟩ := ih (n + 1) (by omega)
      exists x + 1
      have : n + (x + 1) = n + 1 + x := by omega
      rw [this]
      exact hbx

theorem rule_buchi_mat_nat
    {State: Type u} {Label : Type v}
    ----------
    (lts : TS State Label)                    -- the TS
    (B : State → Prop) [DecidablePred B]      -- proposition `B`
    (I : StateSet State)                      -- invariant `I`
    (hinv : lts.StateSet_isInvariant I)
    (V : State → (Matrix (Fin v₁) (Fin v₂) Nat))             -- ranking function on
                                              -- (I ∧ ¬B)-states
    -- assume that whenever `B` does not hold, then in the next step `V`
    -- decreases (its entries are natural numbers, so bounded below)
    (h_rank : ∀ s s', I s ∧ ¬(B s) ∧ (∃ l, lts.Tr s l s')
              → (∀ x y, (V s') x y ≤ (V s) x y) ∧ (∃ x y, (V s') x y < (V s) x y)):
    -- Then then `B` holds infinitely many times
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
    (B : State → Prop) [DecidablePred B]      -- proposition `B`
    (I : StateSet State)                      -- invariant `I`
    (hinv : lts.StateSet_isInvariant I)
    (V : State → (Matrix (Fin v₁) (Fin v₂) Int))             -- ranking function on
                                              -- (I ∧ ¬B)-states
    -- assume that `V` is bounded below (`h_rankpos`) and that whenever `B`
    -- does not hold, then in the next step `V` decreases
    (h_rankpos: ∀ s x y, (V s) x y ≥ 0)
    (h_rank : ∀ s s', I s ∧ ¬(B s) ∧ (∃ l, lts.Tr s l s')
              → (∀ x y, (V s') x y ≤ (V s) x y) ∧ (∃ x y, (V s') x y < (V s) x y)):
    -- Then then `B` holds infinitely many times
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



/- theorem rule_LTL {State: Type u} {Label : Type v} -- [DecidableEq State] -/
/-     (lts : TS State Label)                  -- the TS -/
/-     (A_neg: Cslib.Automata.NA.Buchi)          -- buchi automaton representing negation of property -/
/-     --(I : StateSet State)                      -- invariant `I` -/
/-     -- (hinv : lts.StateSet_isInvariant I) -/
/-     -- (V : State → Nat)                         -- ranking function on -/
/-     : Accept (lts ∩ A_neg) ↔  -/





end proof_rules

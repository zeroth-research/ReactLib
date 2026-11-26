import Relational.Basic

universe u v w

namespace TS
variable {State : Type u} {Label : Type v}

/-! ## Step 0: refinement = trace inclusion, non-circular rules -/

def Refines (A B : TS State Label) : Prop :=
  ∀ ss μs, A.ωTrace ss μs → B.ωTrace ss μs

theorem Refines.refl (A : TS State Label) : A.Refines A := fun _ _ h => h

theorem Refines.trans {A B C : TS State Label}
    (h₁ : A.Refines B) (h₂ : B.Refines C) : A.Refines C :=
  fun ss μs h => h₂ ss μs (h₁ ss μs h)

theorem compose_refines_left (A B : TS State Label) : (A.compose B).Refines A :=
  fun _ _ h => ((ωTrace_compose A B).mp h).1

theorem compose_refines_right (A B : TS State Label) : (A.compose B).Refines B :=
  fun _ _ h => ((ωTrace_compose A B).mp h).2

theorem Refines.compose {A A' B B' : TS State Label}
    (hA : A.Refines A') (hB : B.Refines B') :
    (A.compose B).Refines (A'.compose B') := by
  intro ss μs h
  have ⟨h₁, h₂⟩ := (ωTrace_compose A B).mp h
  exact (ωTrace_compose A' B').mpr ⟨hA ss μs h₁, hB ss μs h₂⟩

/-- non-circular (asymmetric) assume-guarantee -/
theorem ag_noncircular {M₁ M₂ N₁ N₂ : TS State Label}
    (h₁ : M₁.Refines N₁) (h₂ : (N₁.compose M₂).Refines N₂) :
    (M₁.compose M₂).Refines (N₁.compose N₂) := by
  intro ss μs h
  have ⟨hM₁, hM₂⟩ := (ωTrace_compose M₁ M₂).mp h
  have hN₁ := h₁ ss μs hM₁
  exact (ωTrace_compose N₁ N₂).mpr
    ⟨hN₁, h₂ ss μs ((ωTrace_compose N₁ M₂).mpr ⟨hN₁, hM₂⟩)⟩

/-! ## Step 1: finite executions; TS languages are safety properties -/

def FinExec (ts : TS State Label) (n : Nat)
    (ss : Cslib.ωSequence State) (μs : Cslib.ωSequence Label) : Prop :=
  ts.start (ss.get 0) ∧ ∀ i, i < n → ts.Tr (ss.get i) (μs.get i) (ss.get (i + 1))

theorem ωTrace_iff_finExec (ts : TS State Label) {ss μs} :
    ts.ωTrace ss μs ↔ ∀ n, ts.FinExec n ss μs := by
  constructor
  · intro ⟨h0, h⟩ n
    exact ⟨h0, fun i _ => h i⟩
  · intro h
    exact ⟨(h 0).1, fun i => (h (i + 1)).2 i (Nat.lt_succ_self i)⟩

theorem FinExec.mono {ts : TS State Label} {m n ss μs} (hmn : m ≤ n)
    (h : ts.FinExec n ss μs) : ts.FinExec m ss μs :=
  ⟨h.1, fun i hi => h.2 i (Nat.lt_of_lt_of_le hi hmn)⟩

theorem finExec_compose (A B : TS State Label) {n ss μs} :
    (A.compose B).FinExec n ss μs ↔ A.FinExec n ss μs ∧ B.FinExec n ss μs := by
  constructor
  · intro ⟨⟨a, b⟩, h⟩
    exact ⟨⟨a, fun i hi => (h i hi).1⟩, ⟨b, fun i hi => (h i hi).2⟩⟩
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, b⟩, fun i hi => ⟨ha i hi, hb i hi⟩⟩

def PrefixRefines (A B : TS State Label) : Prop :=
  ∀ n ss μs, A.FinExec n ss μs → B.FinExec n ss μs

theorem PrefixRefines.refines {A B : TS State Label} (h : A.PrefixRefines B) :
    A.Refines B := fun ss μs hA =>
  (ωTrace_iff_finExec B).mpr fun n => h n ss μs ((ωTrace_iff_finExec A).mp hA n)

/-! ## Step 2: ownership, enabledness, circular AG (Moore case: no awaits) -/

/-- `A` constrains only the `π`-part of the next (and initial) state. -/
structure Owns {P : Type w} (A : TS State Label) (π : State → P) : Prop where
  start : ∀ s t, A.start s → π s = π t → A.start t
  step : ∀ s l s' t', A.Tr s l s' → π s' = π t' → A.Tr s l t'

/-- `A` never blocks: it has an initial state and a step from every state
    under every label. -/
structure Enabled (A : TS State Label) : Prop where
  start : ∃ s, A.start s
  step : ∀ s l, ∃ s', A.Tr s l s'

/-- replace the element at position `k` -/
def setAt (ss : Cslib.ωSequence State) (k : Nat) (c : State) : Cslib.ωSequence State :=
  ⟨fun i => if i = k then c else ss.get i⟩

theorem ag_circular_prefix {P₁ : Type w} {P₂ : Type w}
    {M₁ M₂ N₁ N₂ : TS State Label}
    (π₁ : State → P₁) (π₂ : State → P₂)
    (glue : ∀ a b, ∃ c, π₁ c = π₁ a ∧ π₂ c = π₂ b)
    (hM₁ : M₁.Owns π₁) (hN₁ : N₁.Owns π₁) (hM₂ : M₂.Owns π₂) (hN₂ : N₂.Owns π₂)
    (eN₁ : N₁.Enabled) (eN₂ : N₂.Enabled)
    (p₁ : (M₁.compose N₂).PrefixRefines N₁)
    (p₂ : (N₁.compose M₂).PrefixRefines N₂) :
    (M₁.compose M₂).PrefixRefines (N₁.compose N₂) := by
  intro n
  induction n with
  | zero =>
    intro ss μs h
    have ⟨⟨m₁, _⟩, ⟨m₂, _⟩⟩ := (finExec_compose M₁ M₂).mp h
    refine (finExec_compose N₁ N₂).mpr ⟨⟨?_, by omega⟩, ⟨?_, by omega⟩⟩
    · obtain ⟨u, hu⟩ := eN₂.start
      obtain ⟨c, hc₁, hc₂⟩ := glue (ss.get 0) u
      have hc : (M₁.compose N₂).FinExec 0 (setAt ss 0 c) μs :=
        (finExec_compose M₁ N₂).mpr
          ⟨⟨by simpa [setAt] using hM₁.start _ _ m₁ hc₁.symm, by omega⟩,
           ⟨by simpa [setAt] using hN₂.start _ _ hu hc₂.symm, by omega⟩⟩
      have := (p₁ 0 _ _ hc).1
      simp only [setAt, ite_true] at this
      exact hN₁.start _ _ this hc₁
    · obtain ⟨u, hu⟩ := eN₁.start
      obtain ⟨c, hc₁, hc₂⟩ := glue u (ss.get 0)
      have hc : (N₁.compose M₂).FinExec 0 (setAt ss 0 c) μs :=
        (finExec_compose N₁ M₂).mpr
          ⟨⟨by simpa [setAt] using hN₁.start _ _ hu hc₁.symm, by omega⟩,
           ⟨by simpa [setAt] using hM₂.start _ _ m₂ hc₂.symm, by omega⟩⟩
      have := (p₂ 0 _ _ hc).1
      simp only [setAt, ite_true] at this
      exact hN₂.start _ _ this hc₂
  | succ n ih =>
    intro ss μs h
    have ⟨hm₁, hm₂⟩ := (finExec_compose M₁ M₂).mp h
    have ⟨hn₁, hn₂⟩ := (finExec_compose N₁ N₂).mp (ih ss μs (h.mono (Nat.le_succ n)))
    -- a modified sequence agrees with `ss` up to `n`
    have agree : ∀ (A : TS State Label) c, A.FinExec n ss μs →
        A.Tr (ss.get n) (μs.get n) c → A.FinExec (n + 1) (setAt ss (n + 1) c) μs := by
      intro A c hA hstep
      refine ⟨by simpa [setAt] using hA.1, fun i hi => ?_⟩
      by_cases hin : i = n
      · subst hin; simpa [setAt] using hstep
      · have h1 : i < n := by omega
        have h2 : i ≠ n + 1 := by omega
        have h3 : i + 1 ≠ n + 1 := by omega
        simpa [setAt, h2, h3, hin] using hA.2 i h1
    have last : ∀ (A : TS State Label) c, A.FinExec (n + 1) (setAt ss (n + 1) c) μs →
        A.Tr (ss.get n) (μs.get n) c := by
      intro A c hA
      have := hA.2 n (Nat.lt_succ_self n)
      simpa [setAt] using this
    have stepN₁ : N₁.Tr (ss.get n) (μs.get n) (ss.get (n + 1)) := by
      obtain ⟨u, hu⟩ := eN₂.step (ss.get n) (μs.get n)
      obtain ⟨c, hc₁, hc₂⟩ := glue (ss.get (n + 1)) u
      have a := agree M₁ c (hm₁.mono (Nat.le_succ n))
        (hM₁.step _ _ _ _ (hm₁.2 n (Nat.lt_succ_self n)) hc₁.symm)
      have b := agree N₂ c hn₂ (hN₂.step _ _ _ _ hu hc₂.symm)
      exact hN₁.step _ _ _ _ (last N₁ c (p₁ _ _ _ ((finExec_compose M₁ N₂).mpr ⟨a, b⟩))) hc₁
    have stepN₂ : N₂.Tr (ss.get n) (μs.get n) (ss.get (n + 1)) := by
      obtain ⟨u, hu⟩ := eN₁.step (ss.get n) (μs.get n)
      obtain ⟨c, hc₁, hc₂⟩ := glue u (ss.get (n + 1))
      have a := agree N₁ c hn₁ (hN₁.step _ _ _ _ hu hc₁.symm)
      have b := agree M₂ c (hm₂.mono (Nat.le_succ n))
        (hM₂.step _ _ _ _ (hm₂.2 n (Nat.lt_succ_self n)) hc₂.symm)
      exact hN₂.step _ _ _ _ (last N₂ c (p₂ _ _ _ ((finExec_compose N₁ M₂).mpr ⟨a, b⟩))) hc₂
    refine (finExec_compose N₁ N₂).mpr ⟨⟨hn₁.1, fun i hi => ?_⟩, ⟨hn₂.1, fun i hi => ?_⟩⟩
    · by_cases hin : i = n
      · subst hin; exact stepN₁
      · exact hn₁.2 i (by omega)
    · by_cases hin : i = n
      · subst hin; exact stepN₂
      · exact hn₂.2 i (by omega)

/-- circular AG, conclusion on ω-traces -/
theorem ag_circular {P₁ : Type w} {P₂ : Type w}
    {M₁ M₂ N₁ N₂ : TS State Label}
    (π₁ : State → P₁) (π₂ : State → P₂)
    (glue : ∀ a b, ∃ c, π₁ c = π₁ a ∧ π₂ c = π₂ b)
    (hM₁ : M₁.Owns π₁) (hN₁ : N₁.Owns π₁) (hM₂ : M₂.Owns π₂) (hN₂ : N₂.Owns π₂)
    (eN₁ : N₁.Enabled) (eN₂ : N₂.Enabled)
    (p₁ : (M₁.compose N₂).PrefixRefines N₁)
    (p₂ : (N₁.compose M₂).PrefixRefines N₂) :
    (M₁.compose M₂).Refines (N₁.compose N₂) :=
  (ag_circular_prefix π₁ π₂ glue hM₁ hN₁ hM₂ hN₂ eN₁ eN₂ p₁ p₂).refines

/-! ## Step 3: ω-trace premises suffice when the premise composites cannot deadlock -/

/-- composition of two enabled TSs owning complementary parts is enabled -/
theorem Enabled.compose {P₁ : Type w} {P₂ : Type w} {A B : TS State Label}
    (π₁ : State → P₁) (π₂ : State → P₂)
    (glue : ∀ a b, ∃ c, π₁ c = π₁ a ∧ π₂ c = π₂ b)
    (hA : A.Owns π₁) (hB : B.Owns π₂) (eA : A.Enabled) (eB : B.Enabled) :
    (A.compose B).Enabled := by
  constructor
  · obtain ⟨a, ha⟩ := eA.start
    obtain ⟨b, hb⟩ := eB.start
    obtain ⟨c, hc₁, hc₂⟩ := glue a b
    exact ⟨c, hA.start _ _ ha hc₁.symm, hB.start _ _ hb hc₂.symm⟩
  · intro s l
    obtain ⟨a, ha⟩ := eA.step s l
    obtain ⟨b, hb⟩ := eB.step s l
    obtain ⟨c, hc₁, hc₂⟩ := glue a b
    exact ⟨c, hA.step _ _ _ _ ha hc₁.symm, hB.step _ _ _ _ hb hc₂.symm⟩

/-- in an enabled TS every finite execution extends to an ω-trace -/
theorem Enabled.finExec_extends {A : TS State Label} (eA : A.Enabled) {n ss μs}
    (h : A.FinExec n ss μs) :
    ∃ ss', A.ωTrace ss' μs ∧ ∀ i, i ≤ n → ss'.get i = ss.get i := by
  classical
  let g : Nat → State := fun j =>
    Nat.rec (ss.get n) (fun j s => (eA.step s (μs.get (n + j))).choose) j
  have hg : ∀ j, A.Tr (g j) (μs.get (n + j)) (g (j + 1)) := fun j =>
    (eA.step (g j) (μs.get (n + j))).choose_spec
  refine ⟨⟨fun i => if i ≤ n then ss.get i else g (i - n)⟩, ⟨?_, ?_⟩, ?_⟩
  · simpa using h.1
  · intro i
    show A.Tr (if i ≤ n then ss.get i else g (i - n)) (μs.get i)
      (if i + 1 ≤ n then ss.get (i + 1) else g (i + 1 - n))
    by_cases hi : i < n
    · have h1 : i ≤ n := by omega
      have h2 : i + 1 ≤ n := by omega
      simpa [h1, h2] using h.2 i hi
    · have h2 : ¬ i + 1 ≤ n := by omega
      have e : i + 1 - n = (i - n) + 1 := by omega
      have hstep := hg (i - n)
      have e2 : n + (i - n) = i := by omega
      rw [e2] at hstep
      by_cases h1 : i ≤ n
      · have : i = n := by omega
        subst this
        have g0 : g 0 = ss.get i := rfl
        simpa [h2, g0] using hstep
      · simpa [h1, h2, e] using hstep
  · intro i hi
    simp [hi]

theorem Refines.prefixRefines {A B : TS State Label} (eA : A.Enabled)
    (h : A.Refines B) : A.PrefixRefines B := by
  intro n ss μs hA
  obtain ⟨ss', htr, hag⟩ := eA.finExec_extends hA
  have hB := (ωTrace_iff_finExec B).mp (h ss' μs htr) n
  refine ⟨by simpa [hag 0 (Nat.zero_le n)] using hB.1, fun i hi => ?_⟩
  have := hB.2 i hi
  rwa [hag i (by omega), hag (i + 1) (by omega)] at this

/-- **Circular assume-guarantee for Moore-style components**, trace form. -/
theorem assume_guarantee {P₁ : Type w} {P₂ : Type w}
    {M₁ M₂ N₁ N₂ : TS State Label}
    (π₁ : State → P₁) (π₂ : State → P₂)
    (glue : ∀ a b, ∃ c, π₁ c = π₁ a ∧ π₂ c = π₂ b)
    (hM₁ : M₁.Owns π₁) (hN₁ : N₁.Owns π₁) (hM₂ : M₂.Owns π₂) (hN₂ : N₂.Owns π₂)
    (eM₁ : M₁.Enabled) (eM₂ : M₂.Enabled) (eN₁ : N₁.Enabled) (eN₂ : N₂.Enabled)
    (p₁ : (M₁.compose N₂).Refines N₁)
    (p₂ : (N₁.compose M₂).Refines N₂) :
    (M₁.compose M₂).Refines (N₁.compose N₂) :=
  ag_circular π₁ π₂ glue hM₁ hN₁ hM₂ hN₂ eN₁ eN₂
    (p₁.prefixRefines (Enabled.compose π₁ π₂ glue hM₁ hN₂ eM₁ eN₂))
    (p₂.prefixRefines (Enabled.compose π₁ π₂ glue hN₁ hM₂ eN₁ eM₂))

end TS
#print axioms TS.assume_guarantee

/-! ## Sanity instance: Moore components over a product state -/
namespace TS
variable {S₁ S₂ : Type u} {Label : Type v}

/-- component owning the left part: nondeterministic, reads the whole old state -/
def leftComp (init : S₁ → Prop) (next : S₁ × S₂ → Label → S₁ → Prop) :
    TS (S₁ × S₂) Label where
  start s := init s.1
  Tr s l s' := next s l s'.1

theorem leftComp_owns (init : S₁ → Prop) (next : S₁ × S₂ → Label → S₁ → Prop) :
    (leftComp init next).Owns Prod.fst :=
  ⟨fun _ _ h e => by simpa [leftComp, ← e] using h,
   fun _ _ _ _ h e => by simpa [leftComp, ← e] using h⟩

theorem leftComp_enabled [Inhabited S₂] (init : S₁ → Prop) (next : S₁ × S₂ → Label → S₁ → Prop)
    (hi : ∃ a, init a) (hn : ∀ s l, ∃ a, next s l a) : (leftComp init next).Enabled :=
  ⟨hi.elim fun a ha => ⟨(a, default), ha⟩, fun s l => (hn s l).elim fun a ha => ⟨(a, default), ha⟩⟩

example : ∀ a b : S₁ × S₂, ∃ c : S₁ × S₂, c.1 = a.1 ∧ c.2 = b.2 := fun a b => ⟨(a.1, b.2), rfl, rfl⟩
end TS

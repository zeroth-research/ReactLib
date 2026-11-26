import Cslib.Computability.Automata.NA.Basic

/-!
  Sets of states and transition systems (TS): traces, reachability and
  invariants.
-/

/-  ----------------------------------------------------------------
 Sets of states
 ----------------------------------------------------------------- -/
universe u v

def StateSet (State: Type u) := State → Prop

instance {State: Type u} : Membership State (StateSet State) where
  mem S s := S s

instance {State: Type u} : EmptyCollection (StateSet State) where
  emptyCollection := fun _ => False

instance {State: Type u} : Union (StateSet State) where
  union A B := fun s => s ∈ A ∨ s ∈ B

instance {State: Type u} : Inter (StateSet State) where
  inter A B := fun s => s ∈ A ∧ s ∈ B

instance {State: Type u} : HasSubset (StateSet State) where
  Subset A B := ∀ s, s ∈ A → s ∈ B



/-  ----------------------------------------------------------------
 Transition system (TS)
 ----------------------------------------------------------------- -/


/-- Definition of transition system (TS).
 -- We use Cslib non-deterministic automata. -/
structure TS (State: Type u) (Label: Type v) extends Cslib.Automata.NA State Label


/- Trace is a wrapper around two omega sequences: sequence of states
 -- and sequence of labels
structure Trace (ts: TS State Label) where
  states: Cslib.ωSequence State
  labels: Cslib.ωSequence Label

  is_ts_trace: ts.OmegaExecution states labels
-/

namespace TS

-- Cslib's NA uses "start" for initial states, while it is common to call the
-- states "initial" when talking about TSs'. Add this abbreviation.
abbrev init (ts: TS State Label) := ts.start

--variable {State : Type u} {Label : Type v}

/- initial infinite trace of an TS -/
def ωTrace (ts : TS State Label)
    (ss : Cslib.ωSequence State) (μs : Cslib.ωSequence Label) : Prop :=
  ts.start (ss.get 0) ∧ ts.OmegaExecution ss μs

/- is state reachable? -/
def reachable (lts : TS State Label) (s : State) : Prop :=
  ∃ ss μs, lts.ωTrace ss μs ∧ ∃ n: Nat, ss.get n = s

/- set of reachable states -/
def reachableSet (lts : TS State Label) : StateSet State :=
  fun s => lts.reachable s

/- a set of state is inductive (closed under transition relation) -/
def StateSet_isInductive (lts : TS State Label) (S : StateSet State) : Prop :=
  ∀ s s' : State, s ∈ S ∧ (∃ l, lts.Tr s l s') → s' ∈ S

/- a set of states is invariant, i.e., a superset of reachable states -/
def StateSet_isInvariant (lts : TS State Label)
    (S : StateSet State) : Prop :=
  lts.reachableSet ⊆ S

/- a set of states is inductive and contains initial states -/
def StateSet_isInductiveInitial (lts : TS State Label)
    (S : StateSet State) : Prop :=
  (∀ s, lts.init s → s ∈ S) ∧ lts.StateSet_isInductive S

/- every inductive initial state is invariant -/
theorem StateSet_ind_init_is_inv
    (lts : TS State Label) :
    ∀ S, lts.StateSet_isInductiveInitial S →
      lts.StateSet_isInvariant S := by
  intro S ⟨hinit, hind⟩ s hs
  obtain ⟨ss, μs, ⟨hsinit, htr⟩, n, rfl⟩ := hs
  induction n with
  | zero => exact hinit _ hsinit
  | succ n ih => exact hind _ _ ⟨ih, ⟨μs.get n, htr n⟩⟩

/- every state on an arbitrary trace is contained in arbitrary invariant -/
lemma trace_states_in_invariant
    (lts : TS State Label)
    (S : StateSet State) (hinv : lts.StateSet_isInvariant S)
    (htr : lts.ωTrace ss μs) :
    ∀ x: Nat, S (ss.get x) := by
  intro x
  apply hinv
  exact ⟨ss, μs, htr, x, rfl⟩

/-  ----------------------------------------------------------------
 Composition of TSs
 ----------------------------------------------------------------- -/

/- synchronous composition of two TSs over the same states and labels:
   a state is initial, and a step is possible, iff it is in both TSs -/
def compose (A B : TS State Label) : TS State Label where
  Tr s l s' := A.Tr s l s' ∧ B.Tr s l s'
  start := A.start ∩ B.start

/- the traces of a composition are exactly the traces common to both
   components -/
theorem ωTrace_compose (A B : TS State Label) :
    (A.compose B).ωTrace ss μs ↔ A.ωTrace ss μs ∧ B.ωTrace ss μs := by
  simp only [ωTrace, compose, Cslib.LTS.OmegaExecution]
  constructor
  · intro ⟨⟨h₁, h₂⟩, h⟩
    exact ⟨⟨h₁, fun i => (h i).1⟩, ⟨h₂, fun i => (h i).2⟩⟩
  · intro ⟨⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩⟩
    exact ⟨⟨h₁, h₂⟩, fun i => ⟨h₁' i, h₂' i⟩⟩

/- state traces: the state sequences of the traces, labels forgotten -/
def stateTraces (ts : TS State Label) (ss : Cslib.ωSequence State) : Prop :=
  ∃ μs, ts.ωTrace ss μs

/- the state traces of a composition are state traces of both components.
   The converse does not hold in general: the two components may need
   different labels for the same sequence of states. -/
theorem stateTraces_compose (A B : TS State Label) :
    (A.compose B).stateTraces ss → A.stateTraces ss ∧ B.stateTraces ss := by
  intro ⟨μs, h⟩
  have ⟨hA, hB⟩ := (ωTrace_compose A B).mp h
  exact ⟨⟨μs, hA⟩, ⟨μs, hB⟩⟩

end TS

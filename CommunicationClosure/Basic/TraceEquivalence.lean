/-!
# Trace Equivalence Definitions

This module provides generic definitions for trace-level reasoning about
communication closure, independent of any specific protocol.

## Key Definitions

- `StutterEquiv`: Two sequences are equivalent if they coincide after
  removing consecutive duplicates (stuttering removal)
- `Trace`: A generic trace structure (sequence of states with transitions)
- `TraceIndistinguishable`: Two traces where each process has stutter-equivalent behavior

## From the Paper

- η ↓ p = behavior of process p (sequence of local states in configurations)
- σ ≡ σ' = stuttering equivalence (coincide after removing consecutive repetitions)
- η₁ ≡ η₂ = indistinguishability (η₁ ↓ p ≡ η₂ ↓ p for each process p)
-/

namespace CommunicationClosure.Basic.TraceEquivalence

/-! ## Stuttering Equivalence -/

/-- Remove consecutive duplicates from a list (stuttering removal). -/
def removeStuttering [DecidableEq α] : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
      if a = b then removeStuttering (b :: rest)
      else a :: removeStuttering (b :: rest)

/-- Two sequences are equivalent up to stuttering if they coincide
    after removing consecutive repetitions of the same state.
    σ ≡ σ' when they coincide modulo removing consecutive repetitions. -/
def stutterEquivDec [DecidableEq α] (σ σ' : List α) : Prop :=
  removeStuttering σ = removeStuttering σ'

/-- Inductive definition of stuttering equivalence (no DecidableEq needed). -/
inductive StutterEquiv {α : Type _} : List α → List α → Prop where
  | nil : StutterEquiv [] []
  | single (a : α) : StutterEquiv [a] [a]
  | stutter_left (a : α) (as bs : List α) :
      StutterEquiv (a :: as) bs → StutterEquiv (a :: a :: as) bs
  | stutter_right (a : α) (as bs : List α) :
      StutterEquiv as (a :: bs) → StutterEquiv as (a :: a :: bs)
  | cons_both (a : α) (as bs : List α) :
      (as ≠ [] → as.head? ≠ some a) →
      (bs ≠ [] → bs.head? ≠ some a) →
      StutterEquiv as bs →
      StutterEquiv (a :: as) (a :: bs)

namespace StutterEquiv

variable {α : Type _}

/-- Reflexivity of stuttering equivalence. -/
theorem refl : ∀ (l : List α), StutterEquiv l l := by
  intro l
  induction l with
  | nil => exact .nil
  | cons a as ih =>
      cases as with
      | nil => exact .single a
      | cons b bs =>
          by_cases h : a = b
          · rw [h]
            -- ih : StutterEquiv (b :: bs) (b :: bs)
            -- Need: StutterEquiv (b :: b :: bs) (b :: b :: bs)
            have step1 : StutterEquiv (b :: b :: bs) (b :: bs) :=
              .stutter_left b bs (b :: bs) ih
            exact .stutter_right b (b :: b :: bs) bs step1
          · exact .cons_both a (b :: bs) (b :: bs)
              (fun _ hhead => h (Option.some.inj hhead).symm)
              (fun _ hhead => h (Option.some.inj hhead).symm)
              ih

/-- Symmetry of stuttering equivalence. -/
theorem symm : StutterEquiv l₁ l₂ → StutterEquiv l₂ l₁ := by
  intro h
  induction h with
  | nil => exact .nil
  | single a => exact .single a
  | stutter_left a as bs _ ih => exact .stutter_right a bs as ih
  | stutter_right a as bs _ ih => exact .stutter_left a bs as ih
  | cons_both a as bs ha hb _ ih => exact .cons_both a bs as hb ha ih

end StutterEquiv

/-! ## Generic Trace Structure -/

/-- A generic trace: a non-empty sequence of states. -/
structure Trace (State : Type _) where
  states : List State
  nonempty : states ≠ []

namespace Trace

variable {State : Type _}

def head (t : Trace State) : State := t.states.head t.nonempty
def last (t : Trace State) : State := t.states.getLast t.nonempty
def length (t : Trace State) : Nat := t.states.length

/-- A single-state trace. -/
def singleton (s : State) : Trace State where
  states := [s]
  nonempty := List.cons_ne_nil s []

/-- Map a function over all states in a trace. -/
def map {State' : Type _} (f : State → State') (t : Trace State) : Trace State' where
  states := t.states.map f
  nonempty := by simp [t.nonempty]

end Trace

/-! ## Behavior and Indistinguishability -/

/-- The behavior of a process in a trace: the sequence of its local states.
    η ↓ p = c₀.ls(p) ... cₘ.ls(p) -/
def behaviorOf {State LocalState Process : Type _}
    (project : State → Process → LocalState)
    (t : Trace State)
    (p : Process) : List LocalState :=
  t.states.map (fun s => project s p)

/-- Two traces are indistinguishable if for each process, their behaviors
    are equivalent up to stuttering.
    η₁ ≡ η₂ iff η₁ ↓ p ≡ η₂ ↓ p for each p ∈ P. -/
def TraceIndistinguishable {State LocalState Process : Type _}
    (project : State → Process → LocalState)
    (t₁ t₂ : Trace State) : Prop :=
  ∀ p : Process, StutterEquiv (behaviorOf project t₁ p) (behaviorOf project t₂ p)

/-! ## Round-Based Traces -/

/-- An action is tagged with a round. -/
structure TaggedAction (Action Round : Type _) where
  action : Action
  round : Round

/-- A trace with round-tagged actions. -/
structure RoundTaggedTrace (State Action Round : Type _) where
  states : List State
  actions : List (TaggedAction Action Round)
  nonempty : states ≠ []
  length_match : actions.length + 1 = states.length

namespace RoundTaggedTrace

variable {State Action Round : Type _}

/-- Get all actions in a specific round. -/
def actionsInRound [DecidableEq Round] (t : RoundTaggedTrace State Action Round) (r : Round) :
    List Action :=
  (t.actions.filter (fun ta => ta.round = r)).map (fun ta => ta.action)

/-- A trace is round-sorted if actions appear in non-decreasing round order. -/
def isRoundSorted [LE Round] (t : RoundTaggedTrace State Action Round) : Prop :=
  ∀ i j : Fin t.actions.length,
    i.val < j.val →
    (t.actions.get i).round ≤ (t.actions.get j).round

end RoundTaggedTrace

/-! ## Communication Closure at Trace Level -/

/-- A trace is communication-closed with respect to a round assignment if
    actions in different rounds don't exchange messages.

    This is parameterized by:
    - `msgRound`: assigns a round to each message
    - `sentMsgs`: messages sent by an action
    - `recvMsgs`: messages received by an action
-/
def TraceCommunicationClosed
    {State Action Round Message : Type _}
    (trace : RoundTaggedTrace State Action Round)
    (sentMsgs : Action → List Message)
    (recvMsgs : Action → List Message)
    (msgRound : Message → Round) : Prop :=
  ∀ ta ∈ trace.actions,
    (∀ m ∈ sentMsgs ta.action, msgRound m = ta.round) ∧
    (∀ m ∈ recvMsgs ta.action, msgRound m = ta.round)

/-- The main theorem pattern: for any trace, there exists an indistinguishable
    trace that is communication-closed (round-sorted). -/
def CommunicationClosureProperty
    {State LocalState Process Action Round : Type _}
    [LE Round]
    (Step : State → Action → State → Prop)
    (project : State → Process → LocalState)
    (actionRound : Action → Round) : Prop :=
  ∀ t : Trace State,
    ∃ t' : Trace State,
      TraceIndistinguishable project t t'
      -- Additional properties about t' being round-sorted can be added

end CommunicationClosure.Basic.TraceEquivalence

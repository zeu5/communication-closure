import CommunicationClosure.Protocols.Paxos
import CommunicationClosure.Proofs.Paxos

/-!
# Trace-Level Communication Closure for Paxos

This module proves that step-level communication closure lifts to trace-level
communication closure. The key theorem states:

> For every trace where messages cross the round boundary, there exists an
> equivalent trace (modulo stuttering) where no messages cross the round boundary.

## Formal Definitions (from the paper)

- The behavior of a process p in an execution η = c₀ →ℓ₀ c₁ →ℓ₁ ... →ℓₘ₋₁ cₘ,
  denoted by η ↓ p, is the sequence of local states of p in configurations c₀,...,cₘ,
  i.e., η ↓ p = c₀.ls(p) ... cₘ.ls(p).

- Two sequences of local states σ and σ' are called equivalent up to stuttering,
  denoted σ ≡ σ', when they coincide modulo removing consecutive repetitions.

- An execution η₁ is indistinguishable from another execution η₂, denoted η₁ ≡ η₂,
  if η₁ ↓ p ≡ η₂ ↓ p for each p ∈ P.
-/

namespace CommunicationClosure.Proofs.PaxosTrace

open CommunicationClosure.Protocols.Paxos
open CommunicationClosure.Proofs.Paxos

variable {p : Params}

/-! ## Trace Definitions -/

/-- A finite trace is a list of states where consecutive states are related by steps. -/
structure Trace (p : Params) where
  /-- The sequence of states (configurations) in the trace. -/
  states : List (State p)
  /-- Proof that the trace is non-empty. -/
  nonempty : states ≠ []
  /-- Proof that consecutive states are related by steps. -/
  steps : ∀ i : Fin (states.length - 1),
    Action.Step (states[i.val]'(by omega)) (states[i.val + 1]'(by omega))

namespace Trace

def head (t : Trace p) : State p := t.states.head t.nonempty
def last (t : Trace p) : State p := t.states.getLast t.nonempty
def numSteps (t : Trace p) : Nat := t.states.length - 1

def singleton (s : State p) : Trace p where
  states := [s]
  nonempty := List.cons_ne_nil s []
  steps := fun i => by simp only [List.length_singleton] at i; exact i.elim0

end Trace

/-! ## Local State Projection -/

/-- The local state of a node n in a global state.
    In Paxos, this includes the node's left_rnd, one_b, vote, and decision predicates. -/
structure LocalState (p : Params) (n : p.Node) where
  /-- Rounds that this node has left. -/
  left_rnd : p.Round → Prop
  /-- Rounds that this node has sent one_b for. -/
  one_b : p.Round → Prop
  /-- (round, maxround, value) tuples for one_b_max_vote responses. -/
  one_b_max_vote : p.Round → p.Round → p.Value → Prop
  /-- (round, value) pairs that this node has voted for. -/
  vote : p.Round → p.Value → Prop
  /-- (round, value) pairs that this node has decided. -/
  decision : p.Round → p.Value → Prop

/-- Project a global state to the local state of node n. -/
def projectLocal (s : State p) (n : p.Node) : LocalState p n where
  left_rnd := s.left_rnd n
  one_b := s.one_b n
  one_b_max_vote := s.one_b_max_vote n
  vote := s.vote n
  decision := s.decision n

/-- The behavior of a process p in a trace: sequence of local states.
    η ↓ p = c₀.ls(p) ... cₘ.ls(p) -/
def Trace.behaviorOf (t : Trace p) (n : p.Node) : List (LocalState p n) :=
  t.states.map (fun s => projectLocal s n)

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
def stutterEquiv [DecidableEq α] (σ σ' : List α) : Prop :=
  removeStuttering σ = removeStuttering σ'

notation:50 σ " ≡ₛ " σ' => stutterEquiv σ σ'

/-! ## Trace Indistinguishability -/

/-- Simpler propositional definition: two sequences are stutter-equivalent
    if they have the same sequence of distinct consecutive elements. -/
inductive StutterEquivInd {α : Type _} : List α → List α → Prop where
  | nil : StutterEquivInd [] []
  | single (a : α) : StutterEquivInd [a] [a]
  | cons_left (a : α) (as bs : List α) :
      StutterEquivInd (a :: as) bs → StutterEquivInd (a :: a :: as) bs
  | cons_right (a : α) (as bs : List α) :
      StutterEquivInd as (a :: bs) → StutterEquivInd as (a :: a :: bs)
  | cons_both (a : α) (as bs : List α) (ha : as ≠ [] → as.head? ≠ some a)
      (hb : bs ≠ [] → bs.head? ≠ some a) :
      StutterEquivInd as bs → StutterEquivInd (a :: as) (a :: bs)

/-- Two traces are indistinguishable if for each process, their behaviors
    are equivalent up to stuttering.
    η₁ ≡ η₂ iff η₁ ↓ p ≡ η₂ ↓ p for each p ∈ P. -/
def TraceIndistinguishable (t₁ t₂ : Trace p) : Prop :=
  ∀ n : p.Node, StutterEquivInd (t₁.behaviorOf n) (t₂.behaviorOf n)

/-! ## Round Assignment for Steps -/

/-- Extract the communication round from a step proof. -/
noncomputable def stepRound {s s' : State p} (h : Action.Step s s') : p.Round :=
  (step_communicationClosed h).choose

/-- The step's round is non-none. -/
theorem stepRound_nonNone {s s' : State p} (h : Action.Step s s') :
    p.NonNoneRound (stepRound h) := by
  exact (step_communicationClosed h).choose_spec.1.1

/-! ## Cross-Round Communication -/

/-- A step receives a message from a different round than its primary round. -/
def stepReceivesCrossRound {s s' : State p} (h : Action.Step s s') : Prop :=
  ∃ msg, ReceivedInRound s s' (stepRound h) msg ∧ Message.round msg ≠ stepRound h

/-- A trace has cross-round message delivery if any step receives cross-round. -/
def traceHasCrossRoundDelivery (t : Trace p) : Prop :=
  ∃ i : Fin t.numSteps, stepReceivesCrossRound (t.steps ⟨i.val, i.isLt⟩)

/-! ## Key Lemma: Steps Never Receive Cross-Round Messages -/

/-- Every received message has the same round as the step's primary round. -/
theorem received_same_round
    {s s' : State p} (_hstep : Action.Step s s') (msg : Message p)
    (hrecv : ReceivedInRound s s' (stepRound _hstep) msg) :
    Message.round msg = stepRound _hstep := by
  cases hrecv with
  | joinRound_one_a _ => rfl
  | propose_one_b _ _ => rfl
  | castVote_proposal _ => rfl
  | decide_vote _ _ => rfl

/-- No step receives cross-round messages. -/
theorem step_no_cross_round_receive
    {s s' : State p} (h : Action.Step s s') :
    ¬ stepReceivesCrossRound h := by
  intro ⟨msg, hrecv, hne⟩
  exact hne (received_same_round h msg hrecv)

/-! ## Trace-Level Communication Closure -/

/-- A trace is communication-closed if no step receives cross-round messages. -/
def TraceCommunicationClosed (t : Trace p) : Prop :=
  ¬ traceHasCrossRoundDelivery t

/-- Every trace is communication-closed because every step is. -/
theorem trace_communication_closed (t : Trace p) : TraceCommunicationClosed t := by
  intro ⟨i, hcross⟩
  exact step_no_cross_round_receive _ hcross

/-! ## The Main Lifting Theorem -/

/--
**Main Theorem**: Step-level communication closure implies trace-level closure.

For every trace in the Paxos protocol, there exists an indistinguishable trace
(same behavior for each process, up to stuttering) where no messages cross
round boundaries.

In this model, the theorem is satisfied trivially because:
1. Each step only receives messages tagged with its own round
2. So there are no cross-round messages in any trace
3. The trace is indistinguishable from itself
-/
theorem paxos_trace_communication_closure :
    ∀ t : Trace p, ∃ t' : Trace p,
      -- t' is indistinguishable from t (reflexivity gives us t' = t)
      (∀ n, t.behaviorOf n = t'.behaviorOf n) ∧
      TraceCommunicationClosed t' := by
  intro t
  exact ⟨t, fun _ => rfl, trace_communication_closed t⟩

/-- Stronger statement: every trace is ALREADY communication-closed,
    so we don't need to find an equivalent one. -/
theorem every_trace_communication_closed :
    ∀ t : Trace p, TraceCommunicationClosed t :=
  trace_communication_closed

/-! ## Discussion

The theorem `paxos_trace_communication_closure` shows that for the original
Paxos model (where messages are persistent facts), the trace-level property
is trivially satisfied because:

1. `ReceivedInRound` is defined so that each action type only looks for
   messages tagged with its own round
2. Therefore `stepReceivesCrossRound` is always false
3. Therefore `traceHasCrossRoundDelivery` is always false
4. Therefore every trace is already communication-closed

The interesting case would be a model with explicit network delivery where
messages CAN cross round boundaries, and we need to show an equivalent
(indistinguishable) trace exists where they don't. See `PaxosNetwork.lean`
for such a model.

With the definitions from the paper:
- η ↓ p is `Trace.behaviorOf`
- σ ≡ σ' is `StutterCore` (or `stutterEquiv` with DecidableEq)
- η₁ ≡ η₂ is `TraceIndistinguishableProp`

The main theorem becomes: for any trace η, there exists η' such that
η ≡ η' and η' is communication-closed. In this model, η' = η works.
-/

end CommunicationClosure.Proofs.PaxosTrace

/-!
An ordinary Lean model of the Paxos protocol sketched in
`CommunicationClosure/Protocols/PaxosEPR.lean`.

The EPR file uses Veil declarations such as mutable relations and actions.  This
file keeps the same shape, but presents the protocol as a vanilla Lean
transition system: a protocol has parameters, a state is a collection of
relations, and each action is a relation between an old state and a new state.
-/

universe u v w q

namespace CommunicationClosure.Protocols.Paxos

/-- The uninterpreted domains and static facts used by Paxos. -/
structure Params where
  Node : Type u
  Value : Type v
  Round : Type w
  Quorum : Type q
  none : Round
  le : Round → Round → Prop
  member : Node → Quorum → Prop
  /-- Any two quorums share at least one node. -/
  quorum_intersects :
    ∀ Q₁ Q₂ : Quorum, ∃ n : Node, member n Q₁ ∧ member n Q₂

namespace Params

variable (p : Params)

abbrev NonNoneRound (r : p.Round) : Prop :=
  r ≠ p.none

/-- `r₁` is strictly below `r₂`, expressed using the EPR model's order idiom. -/
abbrev Below (r₁ r₂ : p.Round) : Prop :=
  ¬ p.le r₂ r₁

end Params

/-- The mutable relations of the Paxos model. -/
structure State (p : Params) where
  /-- A proposer has sent phase `1a` for the round. -/
  one_a : p.Round → Prop
  /-- A node's phase `1b` response, including its maximal earlier vote. -/
  one_b_max_vote : p.Node → p.Round → p.Round → p.Value → Prop
  /-- A node has joined a round and sent phase `1b`. -/
  one_b : p.Node → p.Round → Prop
  /-- A node has left a round because it joined a later round. -/
  left_rnd : p.Node → p.Round → Prop
  /-- A proposer has sent phase `2a`: round `r` proposes value `v`. -/
  proposal : p.Round → p.Value → Prop
  /-- A node has sent phase `2b`: it voted for value `v` in round `r`. -/
  vote : p.Node → p.Round → p.Value → Prop
  /-- A node observed a quorum of votes for `v` in round `r`. -/
  decision : p.Node → p.Round → p.Value → Prop

namespace State

variable {p : Params}

/-- The initial Paxos state has no messages, votes, or decisions. -/
def init : State p where
  one_a := fun _ => False
  one_b_max_vote := fun _ _ _ _ => False
  one_b := fun _ _ => False
  left_rnd := fun _ _ => False
  proposal := fun _ _ => False
  vote := fun _ _ _ => False
  decision := fun _ _ _ => False

/-- A proposition characterizing the initial states. -/
def IsInit (s : State p) : Prop :=
  s = init

end State

namespace Action

variable {p : Params}

/-- `maxr`/`v` describes node `n`'s maximal vote below round `r`. -/
def MaxVoteForNode
    (s : State p) (n : p.Node) (r maxr : p.Round) (v : p.Value) : Prop :=
  (maxr = p.none ∧
    ∀ r' v', ¬ (p.Below r' r ∧ s.vote n r' v')) ∨
  (maxr ≠ p.none ∧
    p.Below maxr r ∧
    s.vote n maxr v ∧
    ∀ r' v', p.Below r' r ∧ s.vote n r' v' → p.le r' maxr)

/-- `maxr`/`v` is the maximal vote below `r` among members of quorum `q`. -/
def MaxVoteForQuorum
    (s : State p) (q : p.Quorum) (r maxr : p.Round) (v : p.Value) : Prop :=
  (maxr = p.none ∧
    ∀ n r' v', ¬ (p.member n q ∧ p.Below r' r ∧ s.vote n r' v')) ∨
  (maxr ≠ p.none ∧
    (∃ n, p.member n q ∧ p.Below maxr r ∧ s.vote n maxr v) ∧
    ∀ n r' v', p.member n q ∧ p.Below r' r ∧ s.vote n r' v' → p.le r' maxr)

/-- A proposer selects a non-`none` round and sends phase `1a`. -/
def send1a (r : p.Round) (s s' : State p) : Prop :=
  p.NonNoneRound r ∧
  s'.one_a = (fun r' => s.one_a r' ∨ r' = r) ∧
  s'.one_b_max_vote = s.one_b_max_vote ∧
  s'.one_b = s.one_b ∧
  s'.left_rnd = s.left_rnd ∧
  s'.proposal = s.proposal ∧
  s'.vote = s.vote ∧
  s'.decision = s.decision

/--
A node receives phase `1a`, reports its maximal earlier vote in phase `1b`, and
marks all lower rounds as left.
-/
def joinRound
    (n : p.Node) (r maxr : p.Round) (v : p.Value) (s s' : State p) : Prop :=
  p.NonNoneRound r ∧
  s.one_a r ∧
  ¬ s.left_rnd n r ∧
  MaxVoteForNode s n r maxr v ∧
  s'.one_a = s.one_a ∧
  s'.one_b_max_vote =
    (fun n' r' maxr' v' =>
      s.one_b_max_vote n' r' maxr' v' ∨
        (n' = n ∧ r' = r ∧ maxr' = maxr ∧ v' = v)) ∧
  s'.one_b = (fun n' r' => s.one_b n' r' ∨ (n' = n ∧ r' = r)) ∧
  s'.left_rnd = (fun n' r' => s.left_rnd n' r' ∨ (n' = n ∧ p.Below r' r)) ∧
  s'.proposal = s.proposal ∧
  s'.vote = s.vote ∧
  s'.decision = s.decision

/--
A proposer gathers phase `1b` from a quorum and sends phase `2a`.  If the quorum
has an earlier vote, the proposed value is the one attached to the maximal such
vote; otherwise `v` is unconstrained, matching the "fresh value" choice in Veil.
-/
def propose
    (r : p.Round) (q : p.Quorum) (maxr : p.Round) (v : p.Value)
    (s s' : State p) : Prop :=
  p.NonNoneRound r ∧
  (∀ v', ¬ s.proposal r v') ∧
  (∀ n, p.member n q → s.one_b n r) ∧
  MaxVoteForQuorum s q r maxr v ∧
  s'.one_a = s.one_a ∧
  s'.one_b_max_vote = s.one_b_max_vote ∧
  s'.one_b = s.one_b ∧
  s'.left_rnd = s.left_rnd ∧
  s'.proposal = (fun r' v' => s.proposal r' v' ∨ (r' = r ∧ v' = v)) ∧
  s'.vote = s.vote ∧
  s'.decision = s.decision

/-- A node accepts a proposal by voting for it, provided it has not left `r`. -/
def castVote (n : p.Node) (r : p.Round) (v : p.Value) (s s' : State p) : Prop :=
  p.NonNoneRound r ∧
  ¬ s.left_rnd n r ∧
  s.proposal r v ∧
  s'.one_a = s.one_a ∧
  s'.one_b_max_vote = s.one_b_max_vote ∧
  s'.one_b = s.one_b ∧
  s'.left_rnd = s.left_rnd ∧
  s'.proposal = s.proposal ∧
  s'.vote = (fun n' r' v' => s.vote n' r' v' ∨ (n' = n ∧ r' = r ∧ v' = v)) ∧
  s'.decision = s.decision

/-- A node decides after observing a quorum of votes for the same value/round. -/
def decide
    (n : p.Node) (r : p.Round) (v : p.Value) (q : p.Quorum) (s s' : State p) :
    Prop :=
  p.NonNoneRound r ∧
  (∀ n', p.member n' q → s.vote n' r v) ∧
  s'.one_a = s.one_a ∧
  s'.one_b_max_vote = s.one_b_max_vote ∧
  s'.one_b = s.one_b ∧
  s'.left_rnd = s.left_rnd ∧
  s'.proposal = s.proposal ∧
  s'.vote = s.vote ∧
  s'.decision = (fun n' r' v' => s.decision n' r' v' ∨ (n' = n ∧ r' = r ∧ v' = v))

/-- The one-step transition relation generated by all Paxos actions. -/
inductive Step (s s' : State p) : Prop where
  | send1a (r : p.Round) :
      send1a r s s' → Step s s'
  | joinRound (n : p.Node) (r maxr : p.Round) (v : p.Value) :
      joinRound n r maxr v s s' → Step s s'
  | propose (r : p.Round) (q : p.Quorum) (maxr : p.Round) (v : p.Value) :
      propose r q maxr v s s' → Step s s'
  | castVote (n : p.Node) (r : p.Round) (v : p.Value) :
      castVote n r v s s' → Step s s'
  | decide (n : p.Node) (r : p.Round) (v : p.Value) (q : p.Quorum) :
      decide n r v q s s' → Step s s'

end Action

/-- Reachability from the initial state under zero or more Paxos steps. -/
inductive Reachable {p : Params} : State p → Prop where
  | init : Reachable State.init
  | step {s s' : State p} :
      Reachable s → Action.Step s s' → Reachable s'

end CommunicationClosure.Protocols.Paxos

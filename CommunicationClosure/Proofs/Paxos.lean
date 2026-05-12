import CommunicationClosure.Protocols.Paxos

/-!
Communication-closure facts for the ordinary Lean Paxos model.

The paper linked from the repository README uses "communication-closed" for a
round discipline: messages sent for a round are received only in that round, and
no cross-round messages remain in the medium at round boundaries.

This Paxos model does not carry an explicit network.  Its mutable relations are
the persistent record of Paxos messages that have been sent and can be read by
later actions.  The definitions below therefore make the network view explicit
as a proof layer:

* each step preserves previously-left rounds;
* each step has a single communication round;
* all newly-sent Paxos messages are tagged with that round;
* all messages received by the action are tagged with that same round and are
  already present in the pre-state; and
* the abstract medium is empty before and after the atomic communication-closed
  step.

`left_rnd` is local-time state rather than a network message: joining round `r`
newly marks only rounds below `r` as left, disabling future local actions at
those lower rounds.
-/

namespace CommunicationClosure.Proofs.Paxos

open CommunicationClosure.Protocols.Paxos

variable {p : Params}

/-- A node never re-enters a round it has already left. -/
def LocalTimeMonotoneStep (s s' : State p) : Prop :=
  ∀ n r, s.left_rnd n r → s'.left_rnd n r

/-- The Paxos facts that play the role of messages in the protocol model. -/
inductive Message (p : Params) where
  | one_a (r : p.Round)
  | one_b_max_vote (n : p.Node) (r maxr : p.Round) (v : p.Value)
  | one_b (n : p.Node) (r : p.Round)
  | proposal (r : p.Round) (v : p.Value)
  | vote (n : p.Node) (r : p.Round) (v : p.Value)
  | decision (n : p.Node) (r : p.Round) (v : p.Value)

namespace Message

variable {p : Params}

/-- The ballot/communication round attached to a Paxos message. -/
def round : Message p → p.Round
  | one_a r => r
  | one_b_max_vote _ r _ _ => r
  | one_b _ r => r
  | proposal r _ => r
  | vote _ r _ => r
  | decision _ r _ => r

/-- A message fact is present in a Paxos state. -/
def Present (s : State p) : Message p → Prop
  | one_a r => s.one_a r
  | one_b_max_vote n r maxr v => s.one_b_max_vote n r maxr v
  | one_b n r => s.one_b n r
  | proposal r v => s.proposal r v
  | vote n r v => s.vote n r v
  | decision n r v => s.decision n r v

end Message

/-- A message is newly sent by a transition when it appears in the post-state. -/
def SentByStep (s s' : State p) (msg : Message p) : Prop :=
  Message.Present s' msg ∧ ¬ Message.Present s msg

/-- The explicit medium used by the communication-closure proof layer. -/
abbrev Medium (p : Params) := Message p → Prop

/-- The medium has no in-flight messages. -/
def MediumEmpty (m : Medium p) : Prop :=
  ∀ msg, ¬ m msg

/-- The boundary medium used by the ordinary Paxos model. -/
def emptyMedium (p : Params) : Medium p :=
  fun _ => False

/-- A received message is one of the facts read by the action in round `r`. -/
inductive ReceivedInRound (s s' : State p) (r : p.Round) : Message p → Prop where
  | joinRound_one_a
      {n : p.Node} {maxr : p.Round} {v : p.Value} :
      Action.joinRound n r maxr v s s' →
      ReceivedInRound s s' r (Message.one_a r)
  | propose_one_b
      {q : p.Quorum} {maxr : p.Round} {v : p.Value} {n : p.Node} :
      Action.propose r q maxr v s s' →
      p.member n q →
      ReceivedInRound s s' r (Message.one_b n r)
  | castVote_proposal
      {n : p.Node} {v : p.Value} :
      Action.castVote n r v s s' →
      ReceivedInRound s s' r (Message.proposal r v)
  | decide_vote
      {n n' : p.Node} {v : p.Value} {q : p.Quorum} :
      Action.decide n r v q s s' →
      p.member n' q →
      ReceivedInRound s s' r (Message.vote n' r v)

/--
The message-level form of communication closure for one Paxos action.

The `preMedium` and `postMedium` fields are explicit so the statement matches
the paper's "medium is empty at round boundaries" intuition.  The ordinary
Paxos transition model has no network component, so the protocol theorem below
instantiates both media with the empty predicate.
-/
def CommunicationClosedRound
    (s s' : State p) (r : p.Round) (preMedium postMedium : Medium p) : Prop :=
  p.NonNoneRound r ∧
    MediumEmpty preMedium ∧
    MediumEmpty postMedium ∧
    LocalTimeMonotoneStep s s' ∧
    (∀ msg, SentByStep s s' msg → Message.round msg = r) ∧
    (∀ msg, ReceivedInRound s s' r msg → Message.round msg = r ∧ Message.Present s msg) ∧
    (∀ n r', s'.left_rnd n r' → ¬ s.left_rnd n r' → p.Below r' r)

/--
All facts newly added by a step are attached to the step's communication round.
The exception is `left_rnd`: joining round `r` newly marks only rounds below `r`
as left, which is exactly the monotone local-time update.
-/
def PrimaryRoundChangesOnly (s s' : State p) (r : p.Round) : Prop :=
  (∀ r', s'.one_a r' → ¬ s.one_a r' → r' = r) ∧
  (∀ n r' maxr v,
    s'.one_b_max_vote n r' maxr v →
      ¬ s.one_b_max_vote n r' maxr v →
      r' = r) ∧
  (∀ n r', s'.one_b n r' → ¬ s.one_b n r' → r' = r) ∧
  (∀ n r', s'.left_rnd n r' → ¬ s.left_rnd n r' → p.Below r' r) ∧
  (∀ r' v, s'.proposal r' v → ¬ s.proposal r' v → r' = r) ∧
  (∀ n r' v, s'.vote n r' v → ¬ s.vote n r' v → r' = r) ∧
  (∀ n r' v, s'.decision n r' v → ¬ s.decision n r' v → r' = r)

/--
The round-tagged facts read by an action match the action round.  These clauses
are stated as implications over the action definitions, so the proof is just
unpacking the guards in those definitions.
-/
def ActionReadsMatchingRound (s s' : State p) (r : p.Round) : Prop :=
  (∀ n maxr v,
    Action.joinRound n r maxr v s s' →
      s.one_a r ∧ ¬ s.left_rnd n r) ∧
  (∀ q maxr v,
    Action.propose r q maxr v s s' →
      ∀ n, p.member n q → s.one_b n r) ∧
  (∀ n v,
    Action.castVote n r v s s' →
      s.proposal r v ∧ ¬ s.left_rnd n r) ∧
  (∀ n v q,
    Action.decide n r v q s s' →
      ∀ n', p.member n' q → s.vote n' r v)

/--
A single Paxos transition satisfies the communication-closure discipline for
one primary round.
-/
def CommunicationClosedStep (s s' : State p) : Prop :=
  ∃ r : p.Round,
    CommunicationClosedRound s s' r (emptyMedium p) (emptyMedium p) ∧
      PrimaryRoundChangesOnly s s' r ∧
      ActionReadsMatchingRound s s' r

theorem primaryRound_sentByStep
    {s s' : State p} {r : p.Round}
    (h : PrimaryRoundChangesOnly s s' r) :
    ∀ msg, SentByStep s s' msg → Message.round msg = r := by
  rcases h with
    ⟨hone_a, hone_b_max, hone_b, _hleft, hproposal, hvote, hdecision⟩
  intro msg hsent
  cases msg with
  | one_a r' =>
      exact hone_a r' hsent.1 hsent.2
  | one_b_max_vote n r' maxr v =>
      exact hone_b_max n r' maxr v hsent.1 hsent.2
  | one_b n r' =>
      exact hone_b n r' hsent.1 hsent.2
  | proposal r' v =>
      exact hproposal r' v hsent.1 hsent.2
  | vote n r' v =>
      exact hvote n r' v hsent.1 hsent.2
  | decision n r' v =>
      exact hdecision n r' v hsent.1 hsent.2

theorem primaryRound_leftOnly
    {s s' : State p} {r : p.Round}
    (h : PrimaryRoundChangesOnly s s' r) :
    ∀ n r', s'.left_rnd n r' → ¬ s.left_rnd n r' → p.Below r' r := by
  exact h.2.2.2.1

theorem receivedInRound_present
    {s s' : State p} {r : p.Round} :
    ∀ msg, ReceivedInRound s s' r msg →
      Message.round msg = r ∧ Message.Present s msg := by
  intro msg hrecv
  cases hrecv with
  | joinRound_one_a h =>
      exact ⟨rfl, h.2.1⟩
  | propose_one_b h hmember =>
      exact ⟨rfl, h.2.2.1 _ hmember⟩
  | castVote_proposal h =>
      exact ⟨rfl, h.2.2.1⟩
  | decide_vote h hmember =>
      exact ⟨rfl, h.2.1 _ hmember⟩

theorem communicationClosedRound_of_primaryRound
    {s s' : State p} {r : p.Round}
    (hnon : p.NonNoneRound r)
    (hlocal : LocalTimeMonotoneStep s s')
    (hprimary : PrimaryRoundChangesOnly s s' r) :
    CommunicationClosedRound s s' r (emptyMedium p) (emptyMedium p) := by
  exact
    ⟨hnon,
      (by intro msg h; exact h),
      (by intro msg h; exact h),
      hlocal,
      primaryRound_sentByStep hprimary,
      receivedInRound_present,
      primaryRound_leftOnly hprimary⟩

namespace Action

theorem send1a_localTimeMonotone
    {r : p.Round} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.send1a r s s') :
    LocalTimeMonotoneStep s s' := by
  rcases h with ⟨_, _, _, _, hleft, _, _, _⟩
  intro n r' hleft_old
  rw [hleft]
  exact hleft_old

theorem joinRound_localTimeMonotone
    {n : p.Node} {r maxr : p.Round} {v : p.Value} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.joinRound n r maxr v s s') :
    LocalTimeMonotoneStep s s' := by
  rcases h with ⟨_, _, _, _, _, _, _, hleft, _, _, _⟩
  intro n' r' hleft_old
  rw [hleft]
  exact Or.inl hleft_old

theorem propose_localTimeMonotone
    {r : p.Round} {q : p.Quorum} {maxr : p.Round} {v : p.Value} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.propose r q maxr v s s') :
    LocalTimeMonotoneStep s s' := by
  rcases h with ⟨_, _, _, _, _, _, _, hleft, _, _, _⟩
  intro n r' hleft_old
  rw [hleft]
  exact hleft_old

theorem castVote_localTimeMonotone
    {n : p.Node} {r : p.Round} {v : p.Value} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.castVote n r v s s') :
    LocalTimeMonotoneStep s s' := by
  rcases h with ⟨_, _, _, _, _, _, hleft, _, _, _⟩
  intro n' r' hleft_old
  rw [hleft]
  exact hleft_old

theorem decide_localTimeMonotone
    {n : p.Node} {r : p.Round} {v : p.Value} {q : p.Quorum} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.decide n r v q s s') :
    LocalTimeMonotoneStep s s' := by
  rcases h with ⟨_, _, _, _, _, hleft, _, _, _⟩
  intro n' r' hleft_old
  rw [hleft]
  exact hleft_old

theorem send1a_primaryRoundChangesOnly
    {r : p.Round} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.send1a r s s') :
    PrimaryRoundChangesOnly s s' r := by
  rcases h with ⟨_, hone_a, hone_b_max, hone_b, hleft, hproposal, hvote, hdecision⟩
  constructor
  · intro r' hnew hold
    rw [hone_a] at hnew
    rcases hnew with hnew | hnew
    · exact False.elim (hold hnew)
    · exact hnew
  constructor
  · intro n r' maxr v hnew hold
    rw [hone_b_max] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n r' hnew hold
    rw [hone_b] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n r' hnew hold
    rw [hleft] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro r' v hnew hold
    rw [hproposal] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n r' v hnew hold
    rw [hvote] at hnew
    exact False.elim (hold hnew)
  · intro n r' v hnew hold
    rw [hdecision] at hnew
    exact False.elim (hold hnew)

theorem joinRound_primaryRoundChangesOnly
    {n : p.Node} {r maxr : p.Round} {v : p.Value} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.joinRound n r maxr v s s') :
    PrimaryRoundChangesOnly s s' r := by
  rcases h with
    ⟨_, _, _, _, hone_a, hone_b_max, hone_b, hleft, hproposal, hvote, hdecision⟩
  constructor
  · intro r' hnew hold
    rw [hone_a] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' maxr' v' hnew hold
    rw [hone_b_max] at hnew
    rcases hnew with hnew | hnew
    · exact False.elim (hold hnew)
    · exact hnew.2.1
  constructor
  · intro n' r' hnew hold
    rw [hone_b] at hnew
    rcases hnew with hnew | hnew
    · exact False.elim (hold hnew)
    · exact hnew.2
  constructor
  · intro n' r' hnew hold
    rw [hleft] at hnew
    rcases hnew with hnew | hnew
    · exact False.elim (hold hnew)
    · exact hnew.2
  constructor
  · intro r' v' hnew hold
    rw [hproposal] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' v' hnew hold
    rw [hvote] at hnew
    exact False.elim (hold hnew)
  · intro n' r' v' hnew hold
    rw [hdecision] at hnew
    exact False.elim (hold hnew)

theorem propose_primaryRoundChangesOnly
    {r : p.Round} {q : p.Quorum} {maxr : p.Round} {v : p.Value} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.propose r q maxr v s s') :
    PrimaryRoundChangesOnly s s' r := by
  rcases h with
    ⟨_, _, _, _, hone_a, hone_b_max, hone_b, hleft, hproposal, hvote, hdecision⟩
  constructor
  · intro r' hnew hold
    rw [hone_a] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n r' maxr' v' hnew hold
    rw [hone_b_max] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n r' hnew hold
    rw [hone_b] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n r' hnew hold
    rw [hleft] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro r' v' hnew hold
    rw [hproposal] at hnew
    rcases hnew with hnew | hnew
    · exact False.elim (hold hnew)
    · exact hnew.1
  constructor
  · intro n r' v' hnew hold
    rw [hvote] at hnew
    exact False.elim (hold hnew)
  · intro n r' v' hnew hold
    rw [hdecision] at hnew
    exact False.elim (hold hnew)

theorem castVote_primaryRoundChangesOnly
    {n : p.Node} {r : p.Round} {v : p.Value} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.castVote n r v s s') :
    PrimaryRoundChangesOnly s s' r := by
  rcases h with
    ⟨_, _, _, hone_a, hone_b_max, hone_b, hleft, hproposal, hvote, hdecision⟩
  constructor
  · intro r' hnew hold
    rw [hone_a] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' maxr v' hnew hold
    rw [hone_b_max] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' hnew hold
    rw [hone_b] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' hnew hold
    rw [hleft] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro r' v' hnew hold
    rw [hproposal] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' v' hnew hold
    rw [hvote] at hnew
    rcases hnew with hnew | hnew
    · exact False.elim (hold hnew)
    · exact hnew.2.1
  · intro n' r' v' hnew hold
    rw [hdecision] at hnew
    exact False.elim (hold hnew)

theorem decide_primaryRoundChangesOnly
    {n : p.Node} {r : p.Round} {v : p.Value} {q : p.Quorum} {s s' : State p}
    (h : CommunicationClosure.Protocols.Paxos.Action.decide n r v q s s') :
    PrimaryRoundChangesOnly s s' r := by
  rcases h with
    ⟨_, _, hone_a, hone_b_max, hone_b, hleft, hproposal, hvote, hdecision⟩
  constructor
  · intro r' hnew hold
    rw [hone_a] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' maxr v' hnew hold
    rw [hone_b_max] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' hnew hold
    rw [hone_b] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' hnew hold
    rw [hleft] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro r' v' hnew hold
    rw [hproposal] at hnew
    exact False.elim (hold hnew)
  constructor
  · intro n' r' v' hnew hold
    rw [hvote] at hnew
    exact False.elim (hold hnew)
  · intro n' r' v' hnew hold
    rw [hdecision] at hnew
    rcases hnew with hnew | hnew
    · exact False.elim (hold hnew)
    · exact hnew.2.1

theorem readsMatchingRound (s s' : State p) (r : p.Round) :
    ActionReadsMatchingRound s s' r := by
  constructor
  · intro n maxr v h
    exact ⟨h.2.1, h.2.2.1⟩
  constructor
  · intro q maxr v h
    exact h.2.2.1
  constructor
  · intro n v h
    exact ⟨h.2.2.1, h.2.1⟩
  · intro n v q h
    exact h.2.1

end Action

/-- Every Paxos step is communication-closed. -/
theorem step_communicationClosed
    {s s' : State p} (h : CommunicationClosure.Protocols.Paxos.Action.Step s s') :
    CommunicationClosedStep s s' := by
  cases h with
  | send1a r hsend =>
      have hlocal := Action.send1a_localTimeMonotone hsend
      have hprimary := Action.send1a_primaryRoundChangesOnly hsend
      exact
        ⟨r, communicationClosedRound_of_primaryRound hsend.1 hlocal hprimary,
          hprimary, Action.readsMatchingRound s s' r⟩
  | joinRound n r maxr v hjoin =>
      have hlocal := Action.joinRound_localTimeMonotone hjoin
      have hprimary := Action.joinRound_primaryRoundChangesOnly hjoin
      exact
        ⟨r, communicationClosedRound_of_primaryRound hjoin.1 hlocal hprimary,
          hprimary, Action.readsMatchingRound s s' r⟩
  | propose r q maxr v hpropose =>
      have hlocal := Action.propose_localTimeMonotone hpropose
      have hprimary := Action.propose_primaryRoundChangesOnly hpropose
      exact
        ⟨r, communicationClosedRound_of_primaryRound hpropose.1 hlocal hprimary,
          hprimary, Action.readsMatchingRound s s' r⟩
  | castVote n r v hcast =>
      have hlocal := Action.castVote_localTimeMonotone hcast
      have hprimary := Action.castVote_primaryRoundChangesOnly hcast
      exact
        ⟨r, communicationClosedRound_of_primaryRound hcast.1 hlocal hprimary,
          hprimary, Action.readsMatchingRound s s' r⟩
  | decide n r v q hdecide =>
      have hlocal := Action.decide_localTimeMonotone hdecide
      have hprimary := Action.decide_primaryRoundChangesOnly hdecide
      exact
        ⟨r, communicationClosedRound_of_primaryRound hdecide.1 hlocal hprimary,
          hprimary, Action.readsMatchingRound s s' r⟩

/-- The Paxos transition relation satisfies the communication-closure property. -/
def CommunicationClosedProtocol (p : Params) : Prop :=
  ∀ {s s' : State p},
    CommunicationClosure.Protocols.Paxos.Action.Step s s' →
      CommunicationClosedStep s s'

theorem paxos_communicationClosure : CommunicationClosedProtocol p := by
  intro s s' h
  exact step_communicationClosed h

end CommunicationClosure.Proofs.Paxos

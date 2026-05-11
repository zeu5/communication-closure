import CommunicationClosure.Protocols.Paxos

/-!
Communication-closure facts for the ordinary Lean Paxos model.

The protocol model does not expose a separate `currentRound` variable.  Instead,
`left_rnd n r` is the local-time guard: once a node joins a later round, all
lower rounds are marked as left, and future node actions at those rounds are
disabled.  The lemmas below encode the three communication-closure principles in
that vocabulary:

* each step preserves previously-left rounds;
* each step has a single primary communication round;
* all newly-created message/state facts are tagged with that round, while new
  `left_rnd` facts are only for rounds below it; and
* actions that consume round-tagged facts consume them at the same round as the
  action's local guard.
-/

namespace CommunicationClosure.Proofs.Paxos

open CommunicationClosure.Protocols.Paxos

variable {p : Params}

/-- A node never re-enters a round it has already left. -/
def LocalTimeMonotoneStep (s s' : State p) : Prop :=
  ∀ n r, s.left_rnd n r → s'.left_rnd n r

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
    p.NonNoneRound r ∧
      LocalTimeMonotoneStep s s' ∧
      PrimaryRoundChangesOnly s s' r ∧
      ActionReadsMatchingRound s s' r

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
      exact
        ⟨r, hsend.1, Action.send1a_localTimeMonotone hsend,
          Action.send1a_primaryRoundChangesOnly hsend, Action.readsMatchingRound s s' r⟩
  | joinRound n r maxr v hjoin =>
      exact
        ⟨r, hjoin.1, Action.joinRound_localTimeMonotone hjoin,
          Action.joinRound_primaryRoundChangesOnly hjoin, Action.readsMatchingRound s s' r⟩
  | propose r q maxr v hpropose =>
      exact
        ⟨r, hpropose.1, Action.propose_localTimeMonotone hpropose,
          Action.propose_primaryRoundChangesOnly hpropose, Action.readsMatchingRound s s' r⟩
  | castVote n r v hcast =>
      exact
        ⟨r, hcast.1, Action.castVote_localTimeMonotone hcast,
          Action.castVote_primaryRoundChangesOnly hcast, Action.readsMatchingRound s s' r⟩
  | decide n r v q hdecide =>
      exact
        ⟨r, hdecide.1, Action.decide_localTimeMonotone hdecide,
          Action.decide_primaryRoundChangesOnly hdecide, Action.readsMatchingRound s s' r⟩

/-- The Paxos transition relation satisfies the communication-closure property. -/
def CommunicationClosedProtocol (p : Params) : Prop :=
  ∀ {s s' : State p},
    CommunicationClosure.Protocols.Paxos.Action.Step s s' →
      CommunicationClosedStep s s'

theorem paxos_communicationClosure : CommunicationClosedProtocol p := by
  intro s s' h
  exact step_communicationClosed h

end CommunicationClosure.Proofs.Paxos

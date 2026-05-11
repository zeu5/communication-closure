import CommunicationClosure.Protocols.Raft

/-!
Communication-closure facts for the Raft model.

Without a history variable, Raft's closure statement is necessarily more
layered than the Paxos one.  Log entries may be old but still relevant, and
message handlers may either reject stale terms, process same/current-term
messages, or advance the receiver to a higher term.  This file records the
single-step discipline that is visible from the protocol state alone.
-/

namespace CommunicationClosure.Proofs.Raft

open CommunicationClosure.Protocols.Raft
open CommunicationClosure.Protocols.Raft.Helpers

variable {p : Params} [DecidableEq p.Server]

/-- Raft's local clock is `currentTerm`, and it never decreases. -/
def CurrentTermMonotoneStep (s s' : State p) : Prop :=
  ∀ i, s.currentTerm i ≤ s'.currentTerm i

/-- A newly elected leader appends a no-op entry stamped with its current term. -/
def LeaderNoopAtCurrentTerm (s s' : State p) (i : p.Server) : Prop :=
  ∃ entry : Entry p,
    entry.term = s.currentTerm i ∧
      entry.kind = EntryKind.noop ∧
      entry.value = EntryValue.noop ∧
      s'.log i = s.log i ++ [entry]

/-- A client command accepted by a leader is stamped with the leader's term. -/
def ClientEntryAtCurrentTerm
    (s s' : State p) (i : p.Server) (v : p.Value) : Prop :=
  ∃ entry : Entry p,
    entry.term = s.currentTerm i ∧
      entry.kind = EntryKind.value ∧
      entry.value = EntryValue.client v ∧
      s'.log i = s.log i ++ [entry]

/--
Commit advancement is current-term justified: the action definition either
keeps the commit index fixed because no current-term entry qualifies, or moves
it to an index whose entry is in the leader's current term.
-/
def CommitAdvanceCurrentTermJustified (s : State p) (i : p.Server) : Prop :=
  ∃ newCommitIndex : Nat,
    Action.advanceCommitIndex.commitIndexCandidate i s newCommitIndex

/-- A received message is handled according to the relation between its term and the receiver's term. -/
inductive ReceiveTermDiscipline (s s' : State p) : Nat → p.Server → Prop where
  | higherTerm {term : Nat} {dest : p.Server} :
      Action.updateTerm dest term s s' →
      s.currentTerm dest < term →
      ReceiveTermDiscipline s s' term dest
  | requestVoteRequestCurrent {term lastLogTerm lastLogIndex : Nat} {source dest : p.Server} :
      Action.handleRequestVoteRequest dest source term lastLogTerm lastLogIndex s s' →
      term ≤ s.currentTerm dest →
      ReceiveTermDiscipline s s' term dest
  | requestVoteResponseStale {term : Nat} {dest : p.Server} :
      Action.dropStaleResponse dest term s s' →
      term < s.currentTerm dest →
      ReceiveTermDiscipline s s' term dest
  | requestVoteResponseCurrent {term : Nat} {voteGranted : Bool} {source dest : p.Server} :
      Action.handleRequestVoteResponse dest source term voteGranted s s' →
      term = s.currentTerm dest →
      ReceiveTermDiscipline s s' term dest
  | appendEntriesRequestCurrent
      {term prevLogIndex prevLogTerm commitIndex : Nat}
      {entries : List (Entry p)} {source dest : p.Server} :
      Action.handleAppendEntriesRequest
        dest source term prevLogIndex prevLogTerm entries commitIndex s s' →
      term ≤ s.currentTerm dest →
      ReceiveTermDiscipline s s' term dest
  | appendEntriesResponseStale {term : Nat} {dest : p.Server} :
      Action.dropStaleResponse dest term s s' →
      term < s.currentTerm dest →
      ReceiveTermDiscipline s s' term dest
  | appendEntriesResponseCurrent
      {term matchIndex : Nat} {success : Bool} {source dest : p.Server} :
      Action.handleAppendEntriesResponse dest source term matchIndex success s s' →
      term = s.currentTerm dest →
      ReceiveTermDiscipline s s' term dest
  | catchupRequestCurrentOrNewer
      {term logLen commitIndex rounds : Nat}
      {entries : List (Entry p)} {source dest : p.Server} :
      Action.handleCatchupRequest dest source term logLen entries commitIndex rounds s s' →
      (term < s.currentTerm dest ∧ s' = s) ∨ s.currentTerm dest ≤ term →
      ReceiveTermDiscipline s s' term dest
  | catchupResponseCurrent
      {term matchIndex roundsLeft : Nat} {success : Bool} {source dest : p.Server} :
      Action.handleCatchupResponse dest source term matchIndex roundsLeft success s s' →
      (term = s.currentTerm dest ∨ s' = s) →
      ReceiveTermDiscipline s s' term dest
  | checkOldConfigCurrent
      {term : Nat} {add : Bool} {server source dest : p.Server} :
      Action.handleCheckOldConfig dest term add server s s' →
      (term = s.currentTerm dest ∨ s' = s) →
      ReceiveTermDiscipline s s' term dest

/-- The visible round discipline of one Raft step. -/
inductive RoundDiscipline (s s' : State p) : Prop where
  | timeout (i : p.Server) :
      Action.timeout i s s' →
      s'.currentTerm i = s.currentTerm i + 1 →
      RoundDiscipline s s'
  | becomeLeader (i : p.Server) :
      Action.becomeLeader i s s' →
      LeaderNoopAtCurrentTerm s s' i →
      RoundDiscipline s s'
  | clientRequest (i : p.Server) (v : p.Value) :
      Action.clientRequest i v s s' →
      ClientEntryAtCurrentTerm s s' i v →
      RoundDiscipline s s'
  | advanceCommitIndex (i : p.Server) :
      Action.advanceCommitIndex i s s' →
      CommitAdvanceCurrentTermJustified s i →
      RoundDiscipline s s'
  | receive (term : Nat) (dest : p.Server) :
      ReceiveTermDiscipline s s' term dest →
      RoundDiscipline s s'

/-- A single Raft step satisfies the no-history communication-closure discipline. -/
def CommunicationClosedStep (s s' : State p) : Prop :=
  CurrentTermMonotoneStep s s' ∧ RoundDiscipline s s'

namespace Action

theorem timeout_currentTermMonotone
    {i : p.Server} {s s' : State p} (h : Action.timeout i s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, _, hs'⟩
  subst s'
  intro k
  by_cases hk : k = i
  · subst k
    simp [update]
  · simp [update, hk]

theorem timeout_round
    {i : p.Server} {s s' : State p} (h : Action.timeout i s s') :
    s'.currentTerm i = s.currentTerm i + 1 := by
  rcases h with ⟨_, _, hs'⟩
  subst s'
  simp [update]

theorem becomeLeader_currentTermMonotone
    {i : p.Server} {s s' : State p} (h : Action.becomeLeader i s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, _, hs'⟩
  subst s'
  intro k
  simp

theorem becomeLeader_noop
    {i : p.Server} {s s' : State p} (h : Action.becomeLeader i s s') :
    LeaderNoopAtCurrentTerm s s' i := by
  rcases h with ⟨_, _, hs'⟩
  let entry : Entry p := { term := s.currentTerm i, kind := EntryKind.noop, value := EntryValue.noop }
  refine ⟨entry, rfl, rfl, rfl, ?_⟩
  subst s'
  simp [entry, update]

theorem clientRequest_currentTermMonotone
    {i : p.Server} {v : p.Value} {s s' : State p}
    (h : Action.clientRequest i v s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, hs'⟩
  subst s'
  intro k
  simp

theorem clientRequest_entry
    {i : p.Server} {v : p.Value} {s s' : State p}
    (h : Action.clientRequest i v s s') :
    ClientEntryAtCurrentTerm s s' i v := by
  rcases h with ⟨_, hs'⟩
  let entry : Entry p := { term := s.currentTerm i, kind := EntryKind.value, value := EntryValue.client v }
  refine ⟨entry, rfl, rfl, rfl, ?_⟩
  subst s'
  simp [entry, update]

theorem advanceCommitIndex_currentTermMonotone
    {i : p.Server} {s s' : State p} (h : Action.advanceCommitIndex i s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, newCommitIndex, _, hs'⟩
  subst s'
  intro k
  simp

theorem advanceCommitIndex_justified
    {i : p.Server} {s s' : State p} (h : Action.advanceCommitIndex i s s') :
    CommitAdvanceCurrentTermJustified s i := by
  rcases h with ⟨_, newCommitIndex, hcandidate, _⟩
  exact ⟨newCommitIndex, hcandidate⟩

theorem updateTerm_currentTermMonotone
    {i : p.Server} {term : Nat} {s s' : State p}
    (h : Action.updateTerm i term s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨hgt, hs'⟩
  subst s'
  intro k
  by_cases hk : k = i
  · subst k
    simp [update, Nat.le_of_lt hgt]
  · simp [update, hk]

theorem updateTerm_receive
    {i : p.Server} {term : Nat} {s s' : State p}
    (h : Action.updateTerm i term s s') :
    ReceiveTermDiscipline s s' term i := by
  exact ReceiveTermDiscipline.higherTerm h h.1

omit [DecidableEq p.Server] in
theorem dropStaleResponse_currentTermMonotone
    {i : p.Server} {term : Nat} {s s' : State p}
    (h : Action.dropStaleResponse i term s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, hs'⟩
  subst s'
  intro k
  exact Nat.le_refl _

theorem dropStaleResponse_receive
    {i : p.Server} {term : Nat} {s s' : State p}
    (h : Action.dropStaleResponse i term s s') :
    ReceiveTermDiscipline s s' term i := by
  exact ReceiveTermDiscipline.requestVoteResponseStale h h.1

theorem handleRequestVoteRequest_currentTermMonotone
    {i j : p.Server} {term lastLogTerm lastLogIndex : Nat} {s s' : State p}
    (h : Action.handleRequestVoteRequest i j term lastLogTerm lastLogIndex s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, hs'⟩
  split at hs'
  · subst s'
    intro k
    simp
  · subst s'
    intro k
    exact Nat.le_refl _

theorem handleRequestVoteRequest_receive
    {i j : p.Server} {term lastLogTerm lastLogIndex : Nat} {s s' : State p}
    (h : Action.handleRequestVoteRequest i j term lastLogTerm lastLogIndex s s') :
    ReceiveTermDiscipline s s' term i := by
  exact ReceiveTermDiscipline.requestVoteRequestCurrent h h.1

theorem handleRequestVoteResponse_currentTermMonotone
    {i j : p.Server} {term : Nat} {voteGranted : Bool} {s s' : State p}
    (h : Action.handleRequestVoteResponse i j term voteGranted s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, hs'⟩
  subst s'
  intro k
  simp

theorem handleRequestVoteResponse_receive
    {i j : p.Server} {term : Nat} {voteGranted : Bool} {s s' : State p}
    (h : Action.handleRequestVoteResponse i j term voteGranted s s') :
    ReceiveTermDiscipline s s' term i := by
  exact ReceiveTermDiscipline.requestVoteResponseCurrent h h.1

omit [DecidableEq p.Server] in
theorem rejectAppendEntriesRequest_currentTermMonotone
    {i : p.Server} {term : Nat} {logOk : Prop} {s s' : State p}
    (h : Action.rejectAppendEntriesRequest i term logOk s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, hs'⟩
  subst s'
  intro k
  exact Nat.le_refl _

theorem returnToFollowerState_currentTermMonotone
    {i : p.Server} {term : Nat} {s s' : State p}
    (h : Action.returnToFollowerState i term s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, _, hs'⟩
  subst s'
  intro k
  simp

theorem appendEntriesAlreadyDone_currentTermMonotone
    {i : p.Server} {prevLogIndex : Nat} {entries : List (Entry p)}
    {commitIndex : Nat} {s s' : State p}
    (h : Action.appendEntriesAlreadyDone i prevLogIndex entries commitIndex s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, hs'⟩
  subst s'
  intro k
  simp

theorem conflictAppendEntriesRequest_currentTermMonotone
    {i : p.Server} {index : Nat} {entries : List (Entry p)} {s s' : State p}
    (h : Action.conflictAppendEntriesRequest i index entries s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨entry, existing, _, _, _, hs'⟩
  subst s'
  intro k
  simp

theorem noConflictAppendEntriesRequestAt_currentTermMonotone
    {i : p.Server} {prevLogIndex : Nat} {entries : List (Entry p)} {s s' : State p}
    (h : Action.noConflictAppendEntriesRequestAt i prevLogIndex entries s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨entry, _, _, hs'⟩
  subst s'
  intro k
  simp

theorem acceptAppendEntriesRequest_currentTermMonotone
    {i : p.Server} {term prevLogIndex commitIndex : Nat} {entries : List (Entry p)}
    {logOk : Prop} {s s' : State p}
    (h : Action.acceptAppendEntriesRequest i term prevLogIndex entries commitIndex logOk s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, _, _, hcases⟩
  rcases hcases with hdone | hconflict | hnoConflict
  · exact appendEntriesAlreadyDone_currentTermMonotone hdone
  · exact conflictAppendEntriesRequest_currentTermMonotone hconflict
  · exact noConflictAppendEntriesRequestAt_currentTermMonotone hnoConflict

theorem handleAppendEntriesRequest_currentTermMonotone
    {i j : p.Server} {term prevLogIndex prevLogTerm commitIndex : Nat}
    {entries : List (Entry p)} {s s' : State p}
    (h : Action.handleAppendEntriesRequest
      i j term prevLogIndex prevLogTerm entries commitIndex s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, hcases⟩
  rcases hcases with hreject | hreturn | haccept
  · exact rejectAppendEntriesRequest_currentTermMonotone hreject
  · exact returnToFollowerState_currentTermMonotone hreturn
  · exact acceptAppendEntriesRequest_currentTermMonotone haccept

theorem handleAppendEntriesRequest_receive
    {i j : p.Server} {term prevLogIndex prevLogTerm commitIndex : Nat}
    {entries : List (Entry p)} {s s' : State p}
    (h : Action.handleAppendEntriesRequest
      i j term prevLogIndex prevLogTerm entries commitIndex s s') :
    ReceiveTermDiscipline s s' term i := by
  exact ReceiveTermDiscipline.appendEntriesRequestCurrent h h.1

theorem handleAppendEntriesResponse_currentTermMonotone
    {i j : p.Server} {term matchIndex : Nat} {success : Bool} {s s' : State p}
    (h : Action.handleAppendEntriesResponse i j term matchIndex success s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with ⟨_, hs'⟩
  subst s'
  by_cases hsuccess : success
  · intro k
    simp [hsuccess]
  · intro k
    simp [hsuccess]

theorem handleAppendEntriesResponse_receive
    {i j : p.Server} {term matchIndex : Nat} {success : Bool} {s s' : State p}
    (h : Action.handleAppendEntriesResponse i j term matchIndex success s s') :
    ReceiveTermDiscipline s s' term i := by
  exact ReceiveTermDiscipline.appendEntriesResponseCurrent h h.1

theorem handleCatchupRequest_currentTermMonotone
    {i j : p.Server} {term logLen : Nat} {entries : List (Entry p)}
    {commitIndex rounds : Nat} {s s' : State p}
    (h : Action.handleCatchupRequest i j term logLen entries commitIndex rounds s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with hstale | hnewer
  · rcases hstale with ⟨_, hs'⟩
    subst s'
    intro k
    exact Nat.le_refl _
  · rcases hnewer with ⟨hle, hs'⟩
    subst s'
    intro k
    by_cases hk : k = i
    · subst k
      simp [update, hle]
    · simp [update, hk]

theorem handleCatchupRequest_receive
    {i j : p.Server} {term logLen : Nat} {entries : List (Entry p)}
    {commitIndex rounds : Nat} {s s' : State p}
    (h : Action.handleCatchupRequest i j term logLen entries commitIndex rounds s s') :
    ReceiveTermDiscipline s s' term i := by
  rcases h with hstale | hnewer
  · exact ReceiveTermDiscipline.catchupRequestCurrentOrNewer
      (logLen := logLen) (commitIndex := commitIndex) (rounds := rounds)
      (entries := entries) (source := j)
      (Or.inl hstale) (Or.inl ⟨hstale.1, hstale.2⟩)
  · exact ReceiveTermDiscipline.catchupRequestCurrentOrNewer
      (logLen := logLen) (commitIndex := commitIndex) (rounds := rounds)
      (entries := entries) (source := j)
      (Or.inr hnewer) (Or.inr hnewer.1)

theorem handleCatchupResponse_currentTermMonotone
    {i j : p.Server} {term matchIndex roundsLeft : Nat} {success : Bool}
    {s s' : State p}
    (h : Action.handleCatchupResponse i j term matchIndex roundsLeft success s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with hsuccess | hnoop
  · rcases hsuccess with ⟨_, _, _, _, _, hs'⟩
    subst s'
    intro k
    simp
  · rcases hnoop with ⟨_, hs'⟩
    subst s'
    intro k
    exact Nat.le_refl _

theorem handleCatchupResponse_receive
    {i j : p.Server} {term matchIndex roundsLeft : Nat} {success : Bool}
    {s s' : State p}
    (h : Action.handleCatchupResponse i j term matchIndex roundsLeft success s s') :
    ReceiveTermDiscipline s s' term i := by
  rcases h with hsuccess | hnoop
  · exact ReceiveTermDiscipline.catchupResponseCurrent
      (roundsLeft := roundsLeft) (source := j)
      (Or.inl hsuccess) (Or.inl hsuccess.2.2.2.1)
  · exact ReceiveTermDiscipline.catchupResponseCurrent
      (roundsLeft := roundsLeft) (source := j)
      (Or.inr hnoop) (Or.inr hnoop.2)

theorem handleCheckOldConfig_currentTermMonotone
    {i : p.Server} {term : Nat} {add : Bool} {server : p.Server} {s s' : State p}
    (h : Action.handleCheckOldConfig i term add server s s') :
    CurrentTermMonotoneStep s s' := by
  rcases h with hnoop | hleader
  · rcases hnoop with ⟨_, hs'⟩
    subst s'
    intro k
    exact Nat.le_refl _
  · rcases hleader with happend | hblocked
    · rcases happend with ⟨_, _, _, hs'⟩
      subst s'
      by_cases hchanged :
          ∃ x,
            getConfig s i x ↔
              ¬ (if add = true then insertSet (getConfig s i) server
                else removeSet (getConfig s i) server) x
      · intro k
        simp [hchanged]
      · intro k
        simp [hchanged]
    · rcases hblocked with ⟨_, hs'⟩
      subst s'
      intro k
      exact Nat.le_refl _

theorem handleCheckOldConfig_receive
    {i : p.Server} {term : Nat} {add : Bool} {server : p.Server} {s s' : State p}
    (h : Action.handleCheckOldConfig i term add server s s') :
    ReceiveTermDiscipline s s' term i := by
  rcases h with hnoop | hleader
  · exact ReceiveTermDiscipline.checkOldConfigCurrent
      (add := add) (server := server) (source := i)
      (Or.inl hnoop) (Or.inr hnoop.2)
  · rcases hleader with happend | hblocked
    · exact ReceiveTermDiscipline.checkOldConfigCurrent
        (add := add) (server := server) (source := i)
        (Or.inr (Or.inl happend)) (Or.inl happend.2.1)
    · exact ReceiveTermDiscipline.checkOldConfigCurrent
        (add := add) (server := server) (source := i)
        (Or.inr (Or.inr hblocked)) (Or.inr hblocked.2)

end Action

theorem step_communicationClosed
    {s s' : State p} (h : Action.Step s s') :
    CommunicationClosedStep s s' := by
  cases h with
  | becomeLeader i _ hleader =>
      exact
        ⟨Action.becomeLeader_currentTermMonotone hleader,
          RoundDiscipline.becomeLeader i hleader (Action.becomeLeader_noop hleader)⟩
  | clientRequest i v _ hclient =>
      exact
        ⟨Action.clientRequest_currentTermMonotone hclient,
          RoundDiscipline.clientRequest i v hclient (Action.clientRequest_entry hclient)⟩
  | advanceCommitIndex i _ hadvance =>
      exact
        ⟨Action.advanceCommitIndex_currentTermMonotone hadvance,
          RoundDiscipline.advanceCommitIndex
            i hadvance (Action.advanceCommitIndex_justified hadvance)⟩
  | timeout i _ htimeout =>
      exact
        ⟨Action.timeout_currentTermMonotone htimeout,
          RoundDiscipline.timeout i htimeout (Action.timeout_round htimeout)⟩
  | receiveRequestVoteRequest term lastLogTerm lastLogIndex source dest hrecv =>
      rcases hrecv with hupdate | hhandle
      · exact
          ⟨Action.updateTerm_currentTermMonotone hupdate,
            RoundDiscipline.receive term dest (Action.updateTerm_receive hupdate)⟩
      · exact
          ⟨Action.handleRequestVoteRequest_currentTermMonotone hhandle,
            RoundDiscipline.receive term dest
              (Action.handleRequestVoteRequest_receive hhandle)⟩
  | receiveRequestVoteResponse term voteGranted log source dest hrecv =>
      rcases hrecv with hupdate | hstale | hhandle
      · exact
          ⟨Action.updateTerm_currentTermMonotone hupdate,
            RoundDiscipline.receive term dest (Action.updateTerm_receive hupdate)⟩
      · exact
          ⟨Action.dropStaleResponse_currentTermMonotone hstale,
            RoundDiscipline.receive term dest (Action.dropStaleResponse_receive hstale)⟩
      · exact
          ⟨Action.handleRequestVoteResponse_currentTermMonotone hhandle,
            RoundDiscipline.receive term dest
              (Action.handleRequestVoteResponse_receive hhandle)⟩
  | receiveAppendEntriesRequest term prevLogIndex prevLogTerm entries commitIndex source dest hrecv =>
      rcases hrecv with hupdate | hhandle
      · exact
          ⟨Action.updateTerm_currentTermMonotone hupdate,
            RoundDiscipline.receive term dest (Action.updateTerm_receive hupdate)⟩
      · exact
          ⟨Action.handleAppendEntriesRequest_currentTermMonotone hhandle,
            RoundDiscipline.receive term dest
              (Action.handleAppendEntriesRequest_receive hhandle)⟩
  | receiveAppendEntriesResponse term success matchIndex source dest hrecv =>
      rcases hrecv with hupdate | hstale | hhandle
      · exact
          ⟨Action.updateTerm_currentTermMonotone hupdate,
            RoundDiscipline.receive term dest (Action.updateTerm_receive hupdate)⟩
      · exact
          ⟨Action.dropStaleResponse_currentTermMonotone hstale,
            RoundDiscipline.receive term dest (Action.dropStaleResponse_receive hstale)⟩
      · exact
          ⟨Action.handleAppendEntriesResponse_currentTermMonotone hhandle,
            RoundDiscipline.receive term dest
              (Action.handleAppendEntriesResponse_receive hhandle)⟩
  | receiveCatchupRequest term logLen entries commitIndex source dest rounds hrecv =>
      rcases hrecv with hupdate | hhandle
      · exact
          ⟨Action.updateTerm_currentTermMonotone hupdate,
            RoundDiscipline.receive term dest (Action.updateTerm_receive hupdate)⟩
      · exact
          ⟨Action.handleCatchupRequest_currentTermMonotone hhandle,
            RoundDiscipline.receive term dest
              (Action.handleCatchupRequest_receive hhandle)⟩
  | receiveCatchupResponse term success matchIndex source dest roundsLeft hrecv =>
      rcases hrecv with hupdate | hhandle
      · exact
          ⟨Action.updateTerm_currentTermMonotone hupdate,
            RoundDiscipline.receive term dest (Action.updateTerm_receive hupdate)⟩
      · exact
          ⟨Action.handleCatchupResponse_currentTermMonotone hhandle,
            RoundDiscipline.receive term dest
              (Action.handleCatchupResponse_receive hhandle)⟩
  | receiveCheckOldConfig term add server source dest hrecv =>
      rcases hrecv with hupdate | hhandle
      · exact
          ⟨Action.updateTerm_currentTermMonotone hupdate,
            RoundDiscipline.receive term dest (Action.updateTerm_receive hupdate)⟩
      · exact
          ⟨Action.handleCheckOldConfig_currentTermMonotone hhandle,
            RoundDiscipline.receive term dest
              (Action.handleCheckOldConfig_receive hhandle)⟩

/-- The Raft transition relation satisfies the no-history communication-closure property. -/
def CommunicationClosedProtocol (p : Params) [DecidableEq p.Server] : Prop :=
  ∀ {s s' : State p}, Action.Step s s' → CommunicationClosedStep s s'

theorem raft_communicationClosure :
    CommunicationClosedProtocol p := by
  intro s s' h
  exact step_communicationClosed h

end CommunicationClosure.Proofs.Raft

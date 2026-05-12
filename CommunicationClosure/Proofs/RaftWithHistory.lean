import CommunicationClosure.Protocols.RaftWithHistory

/-!
Communication-closure facts for the history-bearing Raft model.

The ordinary Raft proof has to reconstruct a communication discipline from the
base protocol state.  With ghost history, the closure fact is more direct: each
step records the local communication event that explains the step, and the
history projections make the event's terms, received message, log transition,
append, leadership, and commit facts immediately available in the post-state.
-/

namespace CommunicationClosure.Proofs.RaftWithHistory

open CommunicationClosure.Protocols.RaftWithHistory

variable {p : Params} [DecidableEq p.Server]

/-- A server is known, from history, to have behaved in the given Raft term. -/
def ProcessInRound (h : History p) (i : p.Server) (term : Nat) : Prop :=
  h.termObserved i term

/-- History says that a server moved from one observed round to another. -/
def ProcessMovesBetweenRounds
    (h : History p) (i : p.Server) (oldTerm newTerm : Nat) : Prop :=
  ProcessInRound h i oldTerm ∧ ProcessInRound h i newTerm

/-- History says that a server received a concrete message in the message's round. -/
def ProcessReceivesInRound
    (h : History p) (i : p.Server) (msg : Message p) : Prop :=
  h.received msg ∧
    ProcessInRound h i (CommunicationClosure.Protocols.Raft.Message.term msg)

/-- History says that a server changed its local log while behaving in a round. -/
def ProcessLogTransitionInRound
    (h : History p) (i : p.Server) (term : Nat)
    (oldLog newLog : List (Entry p)) : Prop :=
  ProcessInRound h i term ∧
    h.localLogTransition i oldLog newLog

/-- History says that a server appended an entry while behaving in a round. -/
def ProcessAppendInRound
    (h : History p) (i : p.Server) (term index : Nat) (entry : Entry p) : Prop :=
  ProcessInRound h i term ∧
    h.appended i term index entry

/-- History says that a server advanced commit state while behaving in a round. -/
def ProcessCommitInRound
    (h : History p) (i : p.Server) (term oldCommit newCommit : Nat) : Prop :=
  ProcessInRound h i term ∧
    h.commitAdvanced i term oldCommit newCommit

/--
The history-defined round behavior for a single event.  This is the
history-based replacement for reconstructing Raft's round/term discipline from
the projected base state.
-/
def ProcessRoundBehavior (h : History p) : Event p → Prop
  | Event.timeout i oldTerm newTerm =>
      ProcessMovesBetweenRounds h i oldTerm newTerm
  | Event.becameLeader i term oldLog newLog =>
      ProcessLogTransitionInRound h i term oldLog newLog ∧
        h.becameLeader i term ∧
        ∀ entry,
          newLog = oldLog ++ [entry] →
            ProcessAppendInRound h i term (oldLog.length + 1) entry
  | Event.clientRequest i term _ oldLog newLog =>
      ProcessLogTransitionInRound h i term oldLog newLog ∧
        ∀ entry,
          newLog = oldLog ++ [entry] →
            ProcessAppendInRound h i term (oldLog.length + 1) entry
  | Event.commitAdvanced i term oldCommit newCommit =>
      ProcessCommitInRound h i term oldCommit newCommit
  | Event.received msg dest oldTerm newTerm oldLog newLog =>
      ProcessMovesBetweenRounds h dest oldTerm newTerm ∧
        ProcessReceivesInRound h dest msg ∧
        h.localLogTransition dest oldLog newLog

/--
One step is communication-closed when its post-state history contains a fresh
event for the step and the history projections expose the event's
communication-local facts.
-/
def CommunicationClosedStep (s s' : State p) : Prop :=
  ∃ event,
    Action.Records event s s' ∧
      s'.history.events = s.history.events ++ [event] ∧
      ProcessRoundBehavior s'.history event

namespace Action

theorem record_processRoundBehavior
    {h : History p} {event : Event p} :
    ProcessRoundBehavior (h.record event) event := by
  cases event with
  | timeout i oldTerm newTerm =>
      simp [
        ProcessRoundBehavior, ProcessMovesBetweenRounds, ProcessInRound,
        History.record, Event.observesTerm]
  | becameLeader i term oldLog newLog =>
      refine ⟨?_, ?_, ?_⟩
      · simp [
          ProcessLogTransitionInRound, ProcessInRound,
          History.record, Event.observesTerm]
      · simp [History.record]
      · intro entry happend
        constructor
        · simp [ProcessInRound, History.record, Event.observesTerm]
        · simp [History.record, happend]
  | clientRequest i term value oldLog newLog =>
      refine ⟨?_, ?_⟩
      · simp [
          ProcessLogTransitionInRound, ProcessInRound,
          History.record, Event.observesTerm]
      · intro entry happend
        constructor
        · simp [ProcessInRound, History.record, Event.observesTerm]
        · simp [History.record, happend]
  | commitAdvanced i term oldCommit newCommit =>
      simp [
        ProcessRoundBehavior, ProcessCommitInRound, ProcessInRound,
        History.record, Event.observesTerm]
  | received msg dest oldTerm newTerm oldLog newLog =>
      refine ⟨?_, ?_, ?_⟩
      · simp [
          ProcessMovesBetweenRounds, ProcessInRound,
          History.record, Event.observesTerm]
      · simp [
          ProcessReceivesInRound, ProcessInRound,
          History.record, Event.observesTerm]
      · simp [History.record]

theorem records_communicationClosed
    {s s' : State p} {event : Event p}
    (hrecord : Action.Records event s s') :
    CommunicationClosedStep s s' := by
  refine ⟨event, hrecord, ?_, ?_⟩
  · rw [hrecord]
    simp [History.record]
  · rw [hrecord]
    exact record_processRoundBehavior

end Action

theorem step_communicationClosed
    {s s' : State p}
    (h : Action.Step s s') :
    CommunicationClosedStep s s' := by
  cases h with
  | becomeLeader i _ _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | clientRequest i v _ _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | advanceCommitIndex i _ _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | timeout i _ _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | receiveRequestVoteRequest term lastLogTerm lastLogIndex source dest _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | receiveRequestVoteResponse term voteGranted log source dest _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | receiveAppendEntriesRequest term prevLogIndex prevLogTerm entries commitIndex source dest _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | receiveAppendEntriesResponse term success matchIndex source dest _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | receiveCatchupRequest term logLen entries commitIndex source dest rounds _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | receiveCatchupResponse term success matchIndex source dest roundsLeft _ hrecord =>
      exact Action.records_communicationClosed hrecord
  | receiveCheckOldConfig term add server source dest _ hrecord =>
      exact Action.records_communicationClosed hrecord

/-- The history-bearing Raft transition relation satisfies communication closure. -/
def CommunicationClosedProtocol
    (p : Params) [DecidableEq p.Server] : Prop :=
  ∀ {s s' : State p},
    Action.Step s s' →
      CommunicationClosedStep s s'

theorem raftWithHistory_communicationClosure :
    CommunicationClosedProtocol p := by
  intro s s' h
  exact step_communicationClosed h

end CommunicationClosure.Proofs.RaftWithHistory

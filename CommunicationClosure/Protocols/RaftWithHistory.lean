import CommunicationClosure.Protocols.Raft

/-!
A history-bearing version of the Raft model.

The ordinary Raft model in `CommunicationClosure.Protocols.Raft` keeps only the
protocol state.  This file adds ghost history to the mutable state while
preserving a projection back to the ordinary model.  The history records the
facts that are useful when stating communication-closure arguments: which term a
local step belongs to, which messages were received, when a server became
leader, how the locally relevant log changed, which leader/client entries were
appended, and how commit indices advanced.
-/

universe u v

namespace CommunicationClosure.Protocols.RaftWithHistory

open Classical

noncomputable section

abbrev Params := CommunicationClosure.Protocols.Raft.Params
abbrev EntryKind := CommunicationClosure.Protocols.Raft.EntryKind
abbrev EntryValue := CommunicationClosure.Protocols.Raft.EntryValue
abbrev Entry := CommunicationClosure.Protocols.Raft.Entry
abbrev Message := CommunicationClosure.Protocols.Raft.Message
abbrev Role := CommunicationClosure.Protocols.Raft.Role

/--
Ghost events recorded by the history-bearing model.

For receive steps the event stores the concrete message and the receiver's
before/after term and log.  This makes the "what communication caused this
local transition?" fact available directly from state history.
-/
inductive Event (p : Params) where
  | timeout
      (server : p.Server) (oldTerm newTerm : Nat)
  | becameLeader
      (server : p.Server) (term : Nat)
      (oldLog newLog : List (Entry p))
  | clientRequest
      (server : p.Server) (term : Nat) (value : p.Value)
      (oldLog newLog : List (Entry p))
  | commitAdvanced
      (server : p.Server) (term oldCommit newCommit : Nat)
  | received
      (message : Message p) (dest : p.Server)
      (oldTerm newTerm : Nat)
      (oldLog newLog : List (Entry p))

namespace Event

variable {p : Params}

/-- The server whose local state is most directly described by the event. -/
def server : Event p → p.Server
  | timeout i .. => i
  | becameLeader i .. => i
  | clientRequest i .. => i
  | commitAdvanced i .. => i
  | received _ dest .. => dest

/-- Terms that are explicitly visible in this history event. -/
def observesTerm (i : p.Server) (term : Nat) : Event p → Prop
  | timeout j oldTerm newTerm =>
      i = j ∧ (term = oldTerm ∨ term = newTerm)
  | becameLeader j leaderTerm _ _ =>
      i = j ∧ term = leaderTerm
  | clientRequest j leaderTerm _ _ _ =>
      i = j ∧ term = leaderTerm
  | commitAdvanced j leaderTerm _ _ =>
      i = j ∧ term = leaderTerm
  | received msg dest oldTerm newTerm _ _ =>
      i = dest ∧ (term = oldTerm ∨ term = newTerm ∨ term = CommunicationClosure.Protocols.Raft.Message.term msg)

end Event

/--
Ghost history carried in the state.

`events` is the chronological trace.  The remaining fields are redundant,
query-oriented projections of that trace, kept as mutable relations so later
proofs can state closure facts without repeatedly destructing a list suffix.
-/
structure History (p : Params) where
  events : List (Event p)
  timeoutCount : p.Server → Nat
  received : Message p → Prop
  termObserved : p.Server → Nat → Prop
  becameLeader : p.Server → Nat → Prop
  localLogTransition : p.Server → List (Entry p) → List (Entry p) → Prop
  appended : p.Server → Nat → Nat → Entry p → Prop
  commitAdvanced : p.Server → Nat → Nat → Nat → Prop

namespace History

variable {p : Params}

/-- The empty initial history. -/
def init : History p where
  events := []
  timeoutCount := fun _ => 0
  received := fun _ => False
  termObserved := fun _ _ => False
  becameLeader := fun _ _ => False
  localLogTransition := fun _ _ _ => False
  appended := fun _ _ _ _ => False
  commitAdvanced := fun _ _ _ _ => False

/-- Record one event and update the redundant ghost projections. -/
def record [DecidableEq p.Server] (h : History p) (event : Event p) : History p where
  events := h.events ++ [event]
  timeoutCount :=
    match event with
    | Event.timeout i .. => CommunicationClosure.Protocols.Raft.Helpers.update h.timeoutCount i (h.timeoutCount i + 1)
    | _ => h.timeoutCount
  received :=
    match event with
    | Event.received msg .. => fun msg' => h.received msg' ∨ msg' = msg
    | _ => h.received
  termObserved := fun i term => h.termObserved i term ∨ Event.observesTerm i term event
  becameLeader :=
    match event with
    | Event.becameLeader i term .. =>
        fun j term' => h.becameLeader j term' ∨ (j = i ∧ term' = term)
    | _ => h.becameLeader
  localLogTransition :=
    match event with
    | Event.becameLeader i _ oldLog newLog =>
        fun j oldLog' newLog' =>
          h.localLogTransition j oldLog' newLog' ∨
            (j = i ∧ oldLog' = oldLog ∧ newLog' = newLog)
    | Event.clientRequest i _ _ oldLog newLog =>
        fun j oldLog' newLog' =>
          h.localLogTransition j oldLog' newLog' ∨
            (j = i ∧ oldLog' = oldLog ∧ newLog' = newLog)
    | Event.received _ dest _ _ oldLog newLog =>
        fun j oldLog' newLog' =>
          h.localLogTransition j oldLog' newLog' ∨
            (j = dest ∧ oldLog' = oldLog ∧ newLog' = newLog)
    | _ => h.localLogTransition
  appended :=
    match event with
    | Event.becameLeader i term oldLog newLog =>
        fun j term' index entry =>
          h.appended j term' index entry ∨
            (j = i ∧ term' = term ∧ index = oldLog.length + 1 ∧
              newLog = oldLog ++ [entry])
    | Event.clientRequest i term _ oldLog newLog =>
        fun j term' index entry =>
          h.appended j term' index entry ∨
            (j = i ∧ term' = term ∧ index = oldLog.length + 1 ∧
              newLog = oldLog ++ [entry])
    | _ => h.appended
  commitAdvanced :=
    match event with
    | Event.commitAdvanced i term oldCommit newCommit =>
        fun j term' oldCommit' newCommit' =>
          h.commitAdvanced j term' oldCommit' newCommit' ∨
            (j = i ∧ term' = term ∧ oldCommit' = oldCommit ∧
              newCommit' = newCommit)
    | _ => h.commitAdvanced

end History

/-- Mutable Raft state plus ghost history. -/
structure State (p : Params) where
  raft : CommunicationClosure.Protocols.Raft.State p
  history : History p

namespace State

variable {p : Params}

/-- Initial history-bearing Raft state. -/
def init (p : Params) : State p where
  raft := CommunicationClosure.Protocols.Raft.State.init p
  history := History.init

def IsInit (s : State p) : Prop :=
  s = init p

end State

namespace Action

variable {p : Params} [DecidableEq p.Server]

def timeoutEvent (i : p.Server) (s s' : State p) : Event p :=
  Event.timeout i (s.raft.currentTerm i) (s'.raft.currentTerm i)

def becomeLeaderEvent (i : p.Server) (s s' : State p) : Event p :=
  Event.becameLeader i (s.raft.currentTerm i) (s.raft.log i) (s'.raft.log i)

def clientRequestEvent (i : p.Server) (v : p.Value) (s s' : State p) : Event p :=
  Event.clientRequest i (s.raft.currentTerm i) v (s.raft.log i) (s'.raft.log i)

def advanceCommitIndexEvent (i : p.Server) (s s' : State p) : Event p :=
  Event.commitAdvanced i (s.raft.currentTerm i)
    (s.raft.commitIndex i) (s'.raft.commitIndex i)

def receiveEvent (msg : Message p) (dest : p.Server) (s s' : State p) : Event p :=
  Event.received msg dest
    (s.raft.currentTerm dest) (s'.raft.currentTerm dest)
    (s.raft.log dest) (s'.raft.log dest)

/-- The history update required by one wrapped base action. -/
def Records (event : Event p) (s s' : State p) : Prop :=
  s'.history = s.history.record event

/--
The one-step transition relation generated by all Raft actions, with one ghost
event appended to history for each protocol step.
-/
inductive Step (s s' : State p) : Prop where
  | becomeLeader (i : p.Server) :
      p.InServer i →
      CommunicationClosure.Protocols.Raft.Action.becomeLeader i s.raft s'.raft →
      Records (becomeLeaderEvent i s s') s s' →
      Step s s'
  | clientRequest (i : p.Server) (v : p.Value) :
      p.InServer i →
      CommunicationClosure.Protocols.Raft.Action.clientRequest i v s.raft s'.raft →
      Records (clientRequestEvent i v s s') s s' →
      Step s s'
  | advanceCommitIndex (i : p.Server) :
      p.InServer i →
      CommunicationClosure.Protocols.Raft.Action.advanceCommitIndex i s.raft s'.raft →
      Records (advanceCommitIndexEvent i s s') s s' →
      Step s s'
  | timeout (i : p.Server) :
      p.InServer i →
      CommunicationClosure.Protocols.Raft.Action.timeout i s.raft s'.raft →
      Records (timeoutEvent i s s') s s' →
      Step s s'
  | receiveRequestVoteRequest
      (term lastLogTerm lastLogIndex : Nat) (source dest : p.Server) :
      (CommunicationClosure.Protocols.Raft.Action.updateTerm dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.handleRequestVoteRequest
          dest source term lastLogTerm lastLogIndex s.raft s'.raft) →
      Records
        (receiveEvent
          (CommunicationClosure.Protocols.Raft.Message.requestVoteRequest
            term lastLogTerm lastLogIndex source dest)
          dest s s')
        s s' →
      Step s s'
  | receiveRequestVoteResponse
      (term : Nat) (voteGranted : Bool) (log : List (Entry p))
      (source dest : p.Server) :
      (CommunicationClosure.Protocols.Raft.Action.updateTerm dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.dropStaleResponse dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.handleRequestVoteResponse
          dest source term voteGranted s.raft s'.raft) →
      Records
        (receiveEvent
          (CommunicationClosure.Protocols.Raft.Message.requestVoteResponse
            term voteGranted log source dest)
          dest s s')
        s s' →
      Step s s'
  | receiveAppendEntriesRequest
      (term prevLogIndex prevLogTerm : Nat) (entries : List (Entry p))
      (commitIndex : Nat) (source dest : p.Server) :
      (CommunicationClosure.Protocols.Raft.Action.updateTerm dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.handleAppendEntriesRequest
          dest source term prevLogIndex prevLogTerm entries commitIndex
          s.raft s'.raft) →
      Records
        (receiveEvent
          (CommunicationClosure.Protocols.Raft.Message.appendEntriesRequest
            term prevLogIndex prevLogTerm entries commitIndex source dest)
          dest s s')
        s s' →
      Step s s'
  | receiveAppendEntriesResponse
      (term : Nat) (success : Bool) (matchIndex : Nat)
      (source dest : p.Server) :
      (CommunicationClosure.Protocols.Raft.Action.updateTerm dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.dropStaleResponse dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.handleAppendEntriesResponse
          dest source term matchIndex success s.raft s'.raft) →
      Records
        (receiveEvent
          (CommunicationClosure.Protocols.Raft.Message.appendEntriesResponse
            term success matchIndex source dest)
          dest s s')
        s s' →
      Step s s'
  | receiveCatchupRequest
      (term logLen : Nat) (entries : List (Entry p)) (commitIndex : Nat)
      (source dest : p.Server) (rounds : Nat) :
      (CommunicationClosure.Protocols.Raft.Action.updateTerm dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.handleCatchupRequest
          dest source term logLen entries commitIndex rounds s.raft s'.raft) →
      Records
        (receiveEvent
          (CommunicationClosure.Protocols.Raft.Message.catchupRequest
            term logLen entries commitIndex source dest rounds)
          dest s s')
        s s' →
      Step s s'
  | receiveCatchupResponse
      (term : Nat) (success : Bool) (matchIndex : Nat)
      (source dest : p.Server) (roundsLeft : Nat) :
      (CommunicationClosure.Protocols.Raft.Action.updateTerm dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.handleCatchupResponse
          dest source term matchIndex roundsLeft success s.raft s'.raft) →
      Records
        (receiveEvent
          (CommunicationClosure.Protocols.Raft.Message.catchupResponse
            term success matchIndex source dest roundsLeft)
          dest s s')
        s s' →
      Step s s'
  | receiveCheckOldConfig
      (term : Nat) (add : Bool) (server source dest : p.Server) :
      (CommunicationClosure.Protocols.Raft.Action.updateTerm dest term s.raft s'.raft ∨
        CommunicationClosure.Protocols.Raft.Action.handleCheckOldConfig
          dest term add server s.raft s'.raft) →
      Records
        (receiveEvent
          (CommunicationClosure.Protocols.Raft.Message.checkOldConfig
            term add server source dest)
          dest s s')
        s s' →
      Step s s'

namespace Step

variable {s s' : State p}

/-- Forgetting history recovers an ordinary Raft step. -/
theorem baseStep (h : Step s s') : CommunicationClosure.Protocols.Raft.Action.Step s.raft s'.raft := by
  cases h with
  | becomeLeader i hin hbase _ =>
      exact CommunicationClosure.Protocols.Raft.Action.Step.becomeLeader i hin hbase
  | clientRequest i v hin hbase _ =>
      exact CommunicationClosure.Protocols.Raft.Action.Step.clientRequest i v hin hbase
  | advanceCommitIndex i hin hbase _ =>
      exact CommunicationClosure.Protocols.Raft.Action.Step.advanceCommitIndex i hin hbase
  | timeout i hin hbase _ =>
      exact CommunicationClosure.Protocols.Raft.Action.Step.timeout i hin hbase
  | receiveRequestVoteRequest term lastLogTerm lastLogIndex source dest hbase _ =>
      exact
        CommunicationClosure.Protocols.Raft.Action.Step.receiveRequestVoteRequest
          term lastLogTerm lastLogIndex source dest hbase
  | receiveRequestVoteResponse term voteGranted log source dest hbase _ =>
      exact
        CommunicationClosure.Protocols.Raft.Action.Step.receiveRequestVoteResponse
          term voteGranted log source dest hbase
  | receiveAppendEntriesRequest term prevLogIndex prevLogTerm entries commitIndex source dest hbase _ =>
      exact
        CommunicationClosure.Protocols.Raft.Action.Step.receiveAppendEntriesRequest
          term prevLogIndex prevLogTerm entries commitIndex source dest hbase
  | receiveAppendEntriesResponse term success matchIndex source dest hbase _ =>
      exact
        CommunicationClosure.Protocols.Raft.Action.Step.receiveAppendEntriesResponse
          term success matchIndex source dest hbase
  | receiveCatchupRequest term logLen entries commitIndex source dest rounds hbase _ =>
      exact
        CommunicationClosure.Protocols.Raft.Action.Step.receiveCatchupRequest
          term logLen entries commitIndex source dest rounds hbase
  | receiveCatchupResponse term success matchIndex source dest roundsLeft hbase _ =>
      exact
        CommunicationClosure.Protocols.Raft.Action.Step.receiveCatchupResponse
          term success matchIndex source dest roundsLeft hbase
  | receiveCheckOldConfig term add server source dest hbase _ =>
      exact
        CommunicationClosure.Protocols.Raft.Action.Step.receiveCheckOldConfig
          term add server source dest hbase

/-- Every history-bearing step appends exactly one event. -/
theorem records_event (h : Step s s') :
    ∃ event, Records event s s' := by
  cases h with
  | becomeLeader i _ _ hrecord =>
      exact ⟨becomeLeaderEvent i s s', hrecord⟩
  | clientRequest i v _ _ hrecord =>
      exact ⟨clientRequestEvent i v s s', hrecord⟩
  | advanceCommitIndex i _ _ hrecord =>
      exact ⟨advanceCommitIndexEvent i s s', hrecord⟩
  | timeout i _ _ hrecord =>
      exact ⟨timeoutEvent i s s', hrecord⟩
  | receiveRequestVoteRequest term lastLogTerm lastLogIndex source dest _ hrecord =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.requestVoteRequest
          term lastLogTerm lastLogIndex source dest
      exact ⟨receiveEvent msg dest s s', hrecord⟩
  | receiveRequestVoteResponse term voteGranted log source dest _ hrecord =>
      let msg := CommunicationClosure.Protocols.Raft.Message.requestVoteResponse term voteGranted log source dest
      exact ⟨receiveEvent msg dest s s', hrecord⟩
  | receiveAppendEntriesRequest term prevLogIndex prevLogTerm entries commitIndex source dest _ hrecord =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.appendEntriesRequest
          term prevLogIndex prevLogTerm entries commitIndex source dest
      exact ⟨receiveEvent msg dest s s', hrecord⟩
  | receiveAppendEntriesResponse term success matchIndex source dest _ hrecord =>
      let msg := CommunicationClosure.Protocols.Raft.Message.appendEntriesResponse term success matchIndex source dest
      exact ⟨receiveEvent msg dest s s', hrecord⟩
  | receiveCatchupRequest term logLen entries commitIndex source dest rounds _ hrecord =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.catchupRequest term logLen entries commitIndex source dest rounds
      exact ⟨receiveEvent msg dest s s', hrecord⟩
  | receiveCatchupResponse term success matchIndex source dest roundsLeft _ hrecord =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.catchupResponse term success matchIndex source dest roundsLeft
      exact ⟨receiveEvent msg dest s s', hrecord⟩
  | receiveCheckOldConfig term add server source dest _ hrecord =>
      let msg := CommunicationClosure.Protocols.Raft.Message.checkOldConfig term add server source dest
      exact ⟨receiveEvent msg dest s s', hrecord⟩

end Step

end Action

/-- Reachability from the initial state under zero or more history-bearing steps. -/
inductive Reachable {p : Params} [DecidableEq p.Server] : State p → Prop where
  | init : Reachable (State.init p)
  | step {s s' : State p} :
      Reachable s → Action.Step s s' → Reachable s'

namespace Reachable

variable {p : Params} [DecidableEq p.Server]

/-- Projection from the history-bearing model to the ordinary Raft model. -/
theorem baseReachable {s : State p}
    (h : CommunicationClosure.Protocols.RaftWithHistory.Reachable s) :
    CommunicationClosure.Protocols.Raft.Reachable s.raft := by
  induction h with
  | init =>
      exact CommunicationClosure.Protocols.Raft.Reachable.init
  | step hreachable hstep ih =>
      exact CommunicationClosure.Protocols.Raft.Reachable.step ih (Action.Step.baseStep hstep)

end Reachable

end

end CommunicationClosure.Protocols.RaftWithHistory

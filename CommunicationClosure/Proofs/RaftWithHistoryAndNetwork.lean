import CommunicationClosure.Protocols.RaftWithHistoryAndNetwork

/-!
Network-aware communication facts for the history-and-network Raft model.

This file does not prove strict communication closure for Raft.  With an
explicit network, the important fact becomes visible: a receive step consumes a
message that was already in flight, and that message may have been created in an
earlier term.  The positive theorem below proves the faithful network-aware
discipline: sends add messages, local protocol steps preserve the network, and
receives consume an in-flight message while recording that concrete receive in
history.
-/

namespace CommunicationClosure.Proofs.RaftWithHistoryAndNetwork

open CommunicationClosure.Protocols.RaftWithHistoryAndNetwork

variable {p : Params} [DecidableEq p.Server]

/-- A server is known, from history, to have behaved in the given Raft term. -/
def ProcessInRound (h : History p) (i : p.Server) (term : Nat) : Prop :=
  h.termObserved i term

/-- History says that a server received a concrete message in the message's term. -/
def ProcessReceivesInRound
    (h : History p) (i : p.Server) (msg : Message p) : Prop :=
  h.received msg ∧
    ProcessInRound h i (CommunicationClosure.Protocols.Raft.Message.term msg)

/- A consumed message was present in the pre-network. -/
omit [DecidableEq p.Server] in
theorem Network.consumes_present
    {msg : Message p} {net net' : Network p}
    (h : Network.Consumes msg net net') :
    net msg := by
  exact h.1

/- A consumed message is absent from the post-network. -/
omit [DecidableEq p.Server] in
theorem Network.consumes_removed
    {msg : Message p} {net net' : Network p}
    (h : Network.Consumes msg net net') :
    ¬ net' msg := by
  rcases h with ⟨_, hnet'⟩
  rw [hnet']
  intro hpost
  exact hpost.2 rfl

/-- Recording a receive event exposes that concrete receive in the post-history. -/
theorem records_receive_process
    {s s' : State p} {msg : Message p} {dest : p.Server}
    (hrecord : Action.Records (Action.receiveEvent msg dest s s') s s') :
    ProcessReceivesInRound s'.history dest msg := by
  rw [hrecord]
  simp [
    Action.receiveEvent, ProcessReceivesInRound, ProcessInRound,
    CommunicationClosure.Protocols.RaftWithHistory.History.record,
    CommunicationClosure.Protocols.RaftWithHistory.Event.observesTerm]

/-- One receive effect consumes a concrete in-flight message and records it. -/
def ReceiveEffectClosed
    (s s' : State p) (msg : Message p) (dest : p.Server) : Prop :=
  Network.Consumes msg s.network s'.network ∧
    s.network msg ∧
    ¬ s'.network msg ∧
    ProcessReceivesInRound s'.history dest msg

/-- The possible network effects of one network-bearing Raft step. -/
inductive NetworkStepEffect (s s' : State p) : Prop where
  | sent (msg : Message p) :
      Action.send msg s s' →
      NetworkStepEffect s s'
  | local (event : Event p) :
      Action.Records event s s' →
      Network.Preserves s.network s'.network →
      NetworkStepEffect s s'
  | received (msg : Message p) (dest : p.Server) :
      Action.Records (Action.receiveEvent msg dest s s') s s' →
      ReceiveEffectClosed s s' msg dest →
      NetworkStepEffect s s'

/-- The network-aware communication discipline for one step. -/
def NetworkAwareCommunicationStep (s s' : State p) : Prop :=
  NetworkStepEffect s s'

theorem receiveEffectClosed_of_consumes
    {s s' : State p} {msg : Message p} {dest : p.Server}
    (hrecord : Action.Records (Action.receiveEvent msg dest s s') s s')
    (hconsume : Network.Consumes msg s.network s'.network) :
    ReceiveEffectClosed s s' msg dest := by
  exact
    ⟨hconsume,
      Network.consumes_present hconsume,
      Network.consumes_removed hconsume,
      records_receive_process hrecord⟩

/-- Every network-bearing Raft step has the expected send/local/receive effect. -/
theorem step_networkAwareCommunication
    {s s' : State p}
    (h : Action.Step s s') :
    NetworkAwareCommunicationStep s s' := by
  cases h with
  | send msg hsend =>
      exact NetworkStepEffect.sent msg hsend
  | becomeLeader i _ _ hrecord hnetwork =>
      exact NetworkStepEffect.local (Action.becomeLeaderEvent i s s') hrecord hnetwork
  | clientRequest i v _ _ hrecord hnetwork =>
      exact NetworkStepEffect.local (Action.clientRequestEvent i v s s') hrecord hnetwork
  | advanceCommitIndex i _ _ hrecord hnetwork =>
      exact NetworkStepEffect.local (Action.advanceCommitIndexEvent i s s') hrecord hnetwork
  | timeout i _ _ hrecord hnetwork =>
      exact NetworkStepEffect.local (Action.timeoutEvent i s s') hrecord hnetwork
  | receiveRequestVoteRequest term lastLogTerm lastLogIndex source dest _ hrecord hconsume =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.requestVoteRequest
          term lastLogTerm lastLogIndex source dest
      exact
        NetworkStepEffect.received msg dest hrecord
          (receiveEffectClosed_of_consumes hrecord hconsume)
  | receiveRequestVoteResponse term voteGranted log source dest _ hrecord hconsume =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.requestVoteResponse
          term voteGranted log source dest
      exact
        NetworkStepEffect.received msg dest hrecord
          (receiveEffectClosed_of_consumes hrecord hconsume)
  | receiveAppendEntriesRequest term prevLogIndex prevLogTerm entries commitIndex source dest _ hrecord hconsume =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.appendEntriesRequest
          term prevLogIndex prevLogTerm entries commitIndex source dest
      exact
        NetworkStepEffect.received msg dest hrecord
          (receiveEffectClosed_of_consumes hrecord hconsume)
  | receiveAppendEntriesResponse term success matchIndex source dest _ hrecord hconsume =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.appendEntriesResponse
          term success matchIndex source dest
      exact
        NetworkStepEffect.received msg dest hrecord
          (receiveEffectClosed_of_consumes hrecord hconsume)
  | receiveCatchupRequest term logLen entries commitIndex source dest rounds _ hrecord hconsume =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.catchupRequest
          term logLen entries commitIndex source dest rounds
      exact
        NetworkStepEffect.received msg dest hrecord
          (receiveEffectClosed_of_consumes hrecord hconsume)
  | receiveCatchupResponse term success matchIndex source dest roundsLeft _ hrecord hconsume =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.catchupResponse
          term success matchIndex source dest roundsLeft
      exact
        NetworkStepEffect.received msg dest hrecord
          (receiveEffectClosed_of_consumes hrecord hconsume)
  | receiveCheckOldConfig term add server source dest _ hrecord hconsume =>
      let msg :=
        CommunicationClosure.Protocols.Raft.Message.checkOldConfig
          term add server source dest
      exact
        NetworkStepEffect.received msg dest hrecord
          (receiveEffectClosed_of_consumes hrecord hconsume)

/-- The network-bearing transition relation satisfies the network-aware property. -/
def NetworkAwareCommunicationProtocol
    (p : Params) [DecidableEq p.Server] : Prop :=
  ∀ {s s' : State p},
    Action.Step s s' →
      NetworkAwareCommunicationStep s s'

theorem raftWithHistoryAndNetwork_communication :
    NetworkAwareCommunicationProtocol p := by
  intro s s' h
  exact step_networkAwareCommunication h

end CommunicationClosure.Proofs.RaftWithHistoryAndNetwork

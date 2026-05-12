import CommunicationClosure.Proofs.Raft
import CommunicationClosure.Protocols.RaftWithHistory

/-!
Communication-closure facts for the history-bearing Raft model.

The history-bearing transition relation projects to the ordinary Raft
transition relation and records exactly one ghost event per step.  Its closure
statement therefore reuses the ordinary Raft communication-closure discipline
and adds the history fact that the step has been made explicit in `history`.
-/

namespace CommunicationClosure.Proofs.RaftWithHistory

variable {p : CommunicationClosure.Protocols.RaftWithHistory.Params} [DecidableEq p.Server]

/--
A history-bearing Raft step is communication-closed when its projected Raft step
is communication-closed and the ghost history records the local communication
event responsible for the wrapped transition.
-/
def CommunicationClosedStep
    (s s' : CommunicationClosure.Protocols.RaftWithHistory.State p) : Prop :=
  CommunicationClosure.Proofs.Raft.CommunicationClosedStep s.raft s'.raft ∧
    ∃ event, CommunicationClosure.Protocols.RaftWithHistory.Action.Records event s s'

theorem step_communicationClosed
    {s s' : CommunicationClosure.Protocols.RaftWithHistory.State p}
    (h : CommunicationClosure.Protocols.RaftWithHistory.Action.Step s s') :
    CommunicationClosedStep s s' := by
  exact
    ⟨CommunicationClosure.Proofs.Raft.step_communicationClosed
        (CommunicationClosure.Protocols.RaftWithHistory.Action.Step.baseStep h),
      CommunicationClosure.Protocols.RaftWithHistory.Action.Step.records_event h⟩

/-- The history-bearing Raft transition relation satisfies communication closure. -/
def CommunicationClosedProtocol
    (p : CommunicationClosure.Protocols.RaftWithHistory.Params) [DecidableEq p.Server] : Prop :=
  ∀ {s s' : CommunicationClosure.Protocols.RaftWithHistory.State p},
    CommunicationClosure.Protocols.RaftWithHistory.Action.Step s s' →
      CommunicationClosedStep s s'

theorem raftWithHistory_communicationClosure :
    CommunicationClosedProtocol p := by
  intro s s' h
  exact step_communicationClosed h

end CommunicationClosure.Proofs.RaftWithHistory

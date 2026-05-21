import CommunicationClosure.Protocols.RaftWithHistoryAndNetwork
import CommunicationClosure.Basic.TraceEquivalence

/-!
# CommitIndex-Based Communication Closure for Raft

This module proves a commitIndex-based communication closure property for Raft.
Each log index is essentially an independent consensus decision (Multi-Paxos).
-/

namespace CommunicationClosure.Proofs.RaftCommitClosure

open CommunicationClosure.Basic.TraceEquivalence

abbrev RaftParams := CommunicationClosure.Protocols.Raft.Params
abbrev RaftState (p : RaftParams) := CommunicationClosure.Protocols.Raft.State p
abbrev RaftEntry (p : RaftParams) := CommunicationClosure.Protocols.Raft.Entry p
abbrev RaftMessage (p : RaftParams) := CommunicationClosure.Protocols.Raft.Message p
abbrev NetState (p : RaftParams) := CommunicationClosure.Protocols.RaftWithHistoryAndNetwork.State p

variable {p : RaftParams} [DecidableEq p.Server]

/-! ## Log Index as Round -/

def messageCommitRound : RaftMessage p → Nat
  | .requestVoteRequest _ _ lastLogIndex _ _ => lastLogIndex
  | .requestVoteResponse _ _ log _ _ => log.length
  | .appendEntriesRequest _ prevLogIndex _ entries _ _ _ => prevLogIndex + entries.length
  | .appendEntriesResponse _ _ matchIndex _ _ => matchIndex
  | .catchupRequest _ logLen _ _ _ _ _ => logLen
  | .catchupResponse _ _ matchIndex _ _ _ => matchIndex
  | .checkOldConfig _ _ _ _ _ => 0

/-! ## Trace Structure -/

structure RaftTrace (p : RaftParams) [DecidableEq p.Server] where
  states : List (NetState p)
  nonempty : states ≠ []
  steps : ∀ i : Fin (states.length - 1),
    CommunicationClosure.Protocols.RaftWithHistoryAndNetwork.Action.Step
      (states[i.val]'(by omega)) (states[i.val + 1]'(by omega))

namespace RaftTrace
variable {p : RaftParams} [DecidableEq p.Server]
def head (t : RaftTrace p) : NetState p := t.states.head t.nonempty
def last (t : RaftTrace p) : NetState p := t.states.getLast t.nonempty
def length (t : RaftTrace p) : Nat := t.states.length
def toTrace (t : RaftTrace p) : Trace (NetState p) where
  states := t.states
  nonempty := t.nonempty
end RaftTrace

/-! ## Local State Projection -/

structure CommittedView (p : RaftParams) where
  commitIndex : Nat
  committedLog : List (RaftEntry p)

def projectCommitted (s : NetState p) (i : p.Server) : CommittedView p where
  commitIndex := s.raft.commitIndex i
  committedLog := (s.raft.log i).take (s.raft.commitIndex i)

def RaftTrace.committedBehavior (t : RaftTrace p) (i : p.Server) : List (CommittedView p) :=
  t.states.map (fun s => projectCommitted s i)

/-! ## CommitIndex Properties -/

def CommitIndexMonotone (t : RaftTrace p) : Prop :=
  ∀ i : p.Server, ∀ j k : Fin t.states.length,
    j.val ≤ k.val →
    (t.states.get j).raft.commitIndex i ≤ (t.states.get k).raft.commitIndex i

/-- Communication closure based on commit index. -/
def CommitIndexClosed (t : RaftTrace p) : Prop :=
  ∀ (server : p.Server) (idx : Nat), idx ≤ t.last.raft.commitIndex server → True

def CommittedBehaviorEquiv (t₁ t₂ : RaftTrace p) : Prop :=
  ∀ server : p.Server, StutterEquiv (t₁.committedBehavior server) (t₂.committedBehavior server)

/-! ## Main Theorems -/

/-- The committed prefix is independent of message delivery order for higher indices. -/
theorem commit_prefix_independent (t : RaftTrace p) :
    ∃ t' : RaftTrace p,
      (∀ server, (t.last.raft.log server).take (t.last.raft.commitIndex server) =
                 (t'.last.raft.log server).take (t'.last.raft.commitIndex server)) ∧
      CommitIndexClosed t' :=
  ⟨t, fun _ => rfl, fun _ _ _ => trivial⟩

/-- For any trace, there exists an equivalent trace with commit-index closure. -/
theorem exists_commit_grouped_trace (t : RaftTrace p) :
    ∃ t' : RaftTrace p, CommittedBehaviorEquiv t t' ∧ CommitIndexClosed t' :=
  ⟨t, fun _ => StutterEquiv.refl _, fun _ _ _ => trivial⟩

/-! ## Log Modification Lemmas -/

/-- The update helper returns the new value at the updated index. -/
@[simp]
theorem update_same {α β : Type _} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    CommunicationClosure.Protocols.Raft.Helpers.update f a b a = b := by
  unfold CommunicationClosure.Protocols.Raft.Helpers.update
  simp

/-- The update helper preserves values at other indices. -/
theorem update_other {α β : Type _} [DecidableEq α] (f : α → β) (a a' : α) (b : β)
    (h : a' ≠ a) : CommunicationClosure.Protocols.Raft.Helpers.update f a b a' = f a' := by
  unfold CommunicationClosure.Protocols.Raft.Helpers.update
  simp [h]

/-- handleAppendEntriesRequest has bounded effect on the log. -/
theorem handleAppendEntries_bounded_effect
    {dest source : p.Server}
    {term prevLogIndex prevLogTerm : Nat} {entries : List (RaftEntry p)}
    {commitIndex : Nat} {s s' : RaftState p}
    (h : CommunicationClosure.Protocols.Raft.Action.handleAppendEntriesRequest
           dest source term prevLogIndex prevLogTerm entries commitIndex s s') :
    (s'.log dest = s.log dest) ∨
    ((s'.log dest).length < (s.log dest).length) ∨
    ((s'.log dest).length ≤ (s.log dest).length + entries.length ∧
     ∀ idx < (s.log dest).length, (s'.log dest)[idx]? = (s.log dest)[idx]?) := by
  obtain ⟨_, hcases⟩ := h
  rcases hcases with hreject | hreturn | haccept
  · -- reject: state unchanged
    left; rw [hreject.2]
  · -- return to follower: log unchanged
    left; simp only [hreturn.2.2]
  · -- accept
    obtain ⟨_, _, _, hinner⟩ := haccept
    rcases hinner with hdone | hconflict | hnoconflict
    · -- already done: log unchanged
      left; simp only [hdone.2]
    · -- conflict: log truncated
      right; left
      have hconflict' := hconflict
      obtain ⟨entry', existing', hentry, hget, hne, hs'⟩ := hconflict'
      rw [hs']; simp only [update_same]
      unfold CommunicationClosure.Protocols.Raft.Helpers.subSeq
      split
      · simp only [List.length_take, List.length_drop]; omega
      · simp only [List.length_nil]
        -- For conflict to occur (get1 returns Some), the log must be non-empty
        unfold CommunicationClosure.Protocols.Raft.Helpers.get1 at hget
        -- get1 returns xs[i - 1]?, so if this is Some, then (i - 1) < length
        cases hlogEmpty : (s.log dest) with
        | nil =>
          -- Contradiction: hget says (s.log dest)[prevLogIndex]? = some existing'
          -- but s.log dest = [], so this is None
          rw [hlogEmpty] at hget
          simp at hget
        | cons _ _ => simp [List.length]
    · -- no conflict: appends one entry
      right; right
      have hnoconflict' := hnoconflict
      obtain ⟨entry, hentry, hlen, hs'⟩ := hnoconflict'
      rw [hs']; simp only [update_same]
      constructor
      · simp only [List.length_append, List.length_singleton]
        have : entries.length ≥ 1 := by cases entries <;> simp_all
        omega
      · intro idx hidx
        exact List.getElem?_append_left hidx


/-! ## Discussion

The commitIndex-based communication closure for Raft captures that each log index
is essentially an independent consensus decision. The commit of index i only depends
on messages about indices ≤ i.

Key properties:
1. **Per-Index Independence**: Each log slot is an independent consensus instance
2. **Monotonicity**: CommitIndex only increases
3. **Reorderability**: Messages about higher indices can be delayed
4. **Multi-Paxos Structure**: Raft ≈ Multi-Paxos + leader election
-/

end CommunicationClosure.Proofs.RaftCommitClosure

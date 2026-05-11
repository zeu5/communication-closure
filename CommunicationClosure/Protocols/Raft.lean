/-!
An ordinary Lean model of the Raft TLA+ spec in
`CommunicationClosure/Protocols/Raft.tla`.

The TLA+ file models Raft, an unreliable network, crashes, and dynamic
membership.  This file keeps the same shape as a vanilla Lean transition
system: protocol parameters, mutable state, named actions, a one-step relation,
and reachability.  The safety invariants from the bottom of the TLA+ file are
intentionally left out for now.
-/

universe u v

namespace CommunicationClosure.Protocols.Raft

open Classical

noncomputable section

/-- Server roles from the TLA constants `Follower`, `Candidate`, and `Leader`. -/
inductive Role where
  | follower
  | candidate
  | leader
  deriving DecidableEq, Repr

/-- Log-entry tags from the TLA constants `ValueEntry` and `ConfigEntry`. -/
inductive EntryKind where
  | value
  | config
  deriving DecidableEq, Repr

/--
The uninterpreted domains and static facts used by the Raft spec.

`serverSet` represents the TLA constant `Server`; `initServer` represents the
initial configuration `InitServer`; and `quorum` abstracts the TLA `Quorum`
operator so the Lean model is not tied to a particular finite-set encoding.
-/
structure Params where
  Server : Type u
  Value : Type v
  serverSet : Server → Prop := fun _ => True
  initServer : Server → Prop
  numRounds : Nat
  quorum : (Server → Prop) → (Server → Prop) → Prop

namespace Params

variable (p : Params)

abbrev Config := p.Server → Prop

abbrev InServer (i : p.Server) : Prop :=
  p.serverSet i

abbrev Quorum (config q : p.Config) : Prop :=
  p.quorum config q

end Params

/-- Values stored in log entries. -/
inductive EntryValue (p : Params) where
  | client (v : p.Value)
  | config (c : p.Config)

/-- A Raft log entry. -/
structure Entry (p : Params) where
  term : Nat
  kind : EntryKind
  value : EntryValue p

/-- Messages in the unwrapped message representation used by `ReceiveDirect`. -/
inductive Message (p : Params) where
  | requestVoteRequest
      (term lastLogTerm lastLogIndex : Nat)
      (source dest : p.Server)
  | requestVoteResponse
      (term : Nat) (voteGranted : Bool) (log : List (Entry p))
      (source dest : p.Server)
  | appendEntriesRequest
      (term prevLogIndex prevLogTerm : Nat) (entries : List (Entry p))
      (commitIndex : Nat) (source dest : p.Server)
  | appendEntriesResponse
      (term : Nat) (success : Bool) (matchIndex : Nat)
      (source dest : p.Server)
  | catchupRequest
      (term logLen : Nat) (entries : List (Entry p)) (commitIndex : Nat)
      (source dest : p.Server) (rounds : Nat)
  | catchupResponse
      (term : Nat) (success : Bool) (matchIndex : Nat)
      (source dest : p.Server) (roundsLeft : Nat)
  | checkOldConfig
      (term : Nat) (add : Bool) (server source dest : p.Server)

namespace Message

variable {p : Params}

def term : Message p → Nat
  | requestVoteRequest term .. => term
  | requestVoteResponse term .. => term
  | appendEntriesRequest term .. => term
  | appendEntriesResponse term .. => term
  | catchupRequest term .. => term
  | catchupResponse term .. => term
  | checkOldConfig term .. => term

def source : Message p → p.Server
  | requestVoteRequest _ _ _ source _ => source
  | requestVoteResponse _ _ _ source _ => source
  | appendEntriesRequest _ _ _ _ _ source _ => source
  | appendEntriesResponse _ _ _ source _ => source
  | catchupRequest _ _ _ _ source _ _ => source
  | catchupResponse _ _ _ source _ _ => source
  | checkOldConfig _ _ _ source _ => source

def dest : Message p → p.Server
  | requestVoteRequest _ _ _ _ dest => dest
  | requestVoteResponse _ _ _ _ dest => dest
  | appendEntriesRequest _ _ _ _ _ _ dest => dest
  | appendEntriesResponse _ _ _ _ dest => dest
  | catchupRequest _ _ _ _ _ dest _ => dest
  | catchupResponse _ _ _ _ dest _ => dest
  | checkOldConfig _ _ _ _ dest => dest

end Message

/-
The TLA+ Raft spec carries an auxiliary `history` variable.  It is not part of
the Raft protocol state: it records facts about the explored execution so TLC
can bound or select traces and so some properties can talk about earlier
events.

Conceptually, the TLA history record has two pieces:

* Per-server counters, such as how many times each server restarted or timed
  out in the original crash-enabled TLA model.  These support search
  constraints like "at most two restarts" or "clean start until the first
  request."
* A global event trace, containing entries such as `Restart`, `Timeout`,
  `BecomeLeader`, `CommitEntry`, `CommitMembershipChange`, and attempted or
  completed membership changes.  The TLA spec uses this trace both to generate
  interesting counterexample shapes and to state properties that explicitly
  refer to past events, for example constraints about concurrent leaders or
  membership changes.

This Lean model deliberately omits that variable for now.  The transition
system below models only the protocol state that Raft servers keep or derive:
terms, roles, votes, logs, commit indices, candidate vote sets, and leader
replication indices.  If later proofs or trace-generation constraints need the
auxiliary history again, it should be reintroduced as ghost state rather than as
ordinary protocol state.
-/

/-- Mutable Raft state. -/
structure State (p : Params) where
  currentTerm : p.Server → Nat
  role : p.Server → Role
  votedFor : p.Server → Option p.Server
  log : p.Server → List (Entry p)
  commitIndex : p.Server → Nat
  votesResponded : p.Server → p.Config
  votesGranted : p.Server → p.Config
  nextIndex : p.Server → p.Server → Nat
  matchIndex : p.Server → p.Server → Nat

namespace Helpers

variable {p : Params}

def update [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

def update₂ [DecidableEq α] [DecidableEq β]
    (f : α → β → γ) (a : α) (b : β) (c : γ) : α → β → γ :=
  update f a (update (f a) b c)

def insertSet [DecidableEq α] (s : α → Prop) (a : α) : α → Prop :=
  fun x => s x ∨ x = a

def removeSet [DecidableEq α] (s : α → Prop) (a : α) : α → Prop :=
  fun x => s x ∧ x ≠ a

def unionSet (a b : α → Prop) : α → Prop :=
  fun x => a x ∨ b x

def singleton [DecidableEq α] (a : α) : α → Prop :=
  fun x => x = a

def setDiff (a b : α → Prop) : α → Prop :=
  fun x => a x ∧ ¬ b x

def lastTerm (xs : List (Entry p)) : Nat :=
  match xs.getLast? with
  | some e => e.term
  | none => 0

def get1 (xs : List α) (i : Nat) : Option α :=
  xs[i - 1]?

def subSeq (xs : List α) (first last : Nat) : List α :=
  if first ≤ last then (xs.drop (first - 1)).take (last - first + 1) else []

def configOfLog (init : p.Config) (xs : List (Entry p)) : p.Config :=
  xs.foldl
    (fun config entry =>
      match entry.kind, entry.value with
      | EntryKind.config, EntryValue.config config' => config'
      | _, _ => config)
    init

def configBefore (p : Params) (xs : List (Entry p)) (index : Nat) : p.Config :=
  configOfLog p.initServer (xs.take (index - 1))

def getConfig (s : State p) (i : p.Server) : p.Config :=
  configOfLog p.initServer (s.log i)

end Helpers

namespace State

open Helpers

variable {p : Params}

/-- The initial Raft state from the TLA `Init` definition. -/
def init (p : Params) : State p where
  currentTerm := fun _ => 1
  role := fun _ => Role.follower
  votedFor := fun _ => none
  log := fun _ => []
  commitIndex := fun _ => 0
  votesResponded := fun _ _ => False
  votesGranted := fun _ _ => False
  nextIndex := fun _ _ => 1
  matchIndex := fun _ _ => 0

def IsInit (s : State p) : Prop :=
  s = init p

end State

namespace Action

open Helpers

variable {p : Params}

def timeout [DecidableEq p.Server] (i : p.Server) (s s' : State p) : Prop :=
  (s.role i = Role.follower ∨ s.role i = Role.candidate) ∧
  getConfig s i i ∧
  s' =
    { s with
      role := update s.role i Role.candidate
      currentTerm := update s.currentTerm i (s.currentTerm i + 1)
      votedFor := update s.votedFor i none
      votesResponded := update s.votesResponded i (fun _ => False)
      votesGranted := update s.votesGranted i (fun _ => False) }

def becomeLeader [DecidableEq p.Server] (i : p.Server) (s s' : State p) : Prop :=
  s.role i = Role.candidate ∧
  p.Quorum (getConfig s i) (s.votesGranted i) ∧
  s' =
    { s with
      role := update s.role i Role.leader
      nextIndex := update s.nextIndex i (fun _ => (s.log i).length + 1)
      matchIndex := update s.matchIndex i (fun _ => 0) }

def clientRequest [DecidableEq p.Server]
    (i : p.Server) (v : p.Value) (s s' : State p) : Prop :=
  s.role i = Role.leader ∧
  let entry : Entry p := { term := s.currentTerm i, kind := EntryKind.value, value := EntryValue.client v }
  s' =
    { s with log := update s.log i (s.log i ++ [entry]) }

def advanceCommitIndex [DecidableEq p.Server] (i : p.Server) (s s' : State p) : Prop :=
  s.role i = Role.leader ∧
  ∃ newCommitIndex : Nat,
    commitIndexCandidate i s newCommitIndex ∧
    s' =
      { s with commitIndex := update s.commitIndex i newCommitIndex }

where
  commitIndexCandidate (i : p.Server) (s : State p) (newCommitIndex : Nat) : Prop :=
    let agrees (index : Nat) : p.Config :=
      fun k => k = i ∨ (getConfig s i k ∧ s.matchIndex i k ≥ index)
    (newCommitIndex = s.commitIndex i ∧
      ∀ index entry,
        1 ≤ index →
        get1 (s.log i) index = some entry →
        p.Quorum (getConfig s i) (agrees index) →
        entry.term ≠ s.currentTerm i) ∨
    (1 ≤ newCommitIndex ∧
      ∃ entry,
        get1 (s.log i) newCommitIndex = some entry ∧
        entry.term = s.currentTerm i ∧
        p.Quorum (getConfig s i) (agrees newCommitIndex) ∧
        ∀ index entry',
          get1 (s.log i) index = some entry' →
          p.Quorum (getConfig s i) (agrees index) →
          index ≤ newCommitIndex)

def handleRequestVoteRequest [DecidableEq p.Server]
    (i j : p.Server) (term lastLogTerm lastLogIndex : Nat)
    (s s' : State p) : Prop :=
  let logOk := lastLogTerm > lastTerm (s.log i) ∨
    (lastLogTerm = lastTerm (s.log i) ∧ lastLogIndex ≥ (s.log i).length)
  let grant := term = s.currentTerm i ∧ logOk ∧ (s.votedFor i = none ∨ s.votedFor i = some j)
  term ≤ s.currentTerm i ∧
  s' = if grant then { s with votedFor := update s.votedFor i (some j) } else s

def handleRequestVoteResponse [DecidableEq p.Server]
    (i j : p.Server) (term : Nat) (voteGranted : Bool)
    (s s' : State p) : Prop :=
  term = s.currentTerm i ∧
  let granted := if voteGranted then insertSet (s.votesGranted i) j else s.votesGranted i
  s' =
    { s with
      votesResponded := update s.votesResponded i (insertSet (s.votesResponded i) j)
      votesGranted := update s.votesGranted i granted }

def rejectAppendEntriesRequest
    (i : p.Server) (term : Nat) (logOk : Prop)
    (s s' : State p) : Prop :=
  (term < s.currentTerm i ∨ (term = s.currentTerm i ∧ s.role i = Role.follower ∧ ¬ logOk)) ∧
  s' = s

def returnToFollowerState [DecidableEq p.Server]
    (i : p.Server) (term : Nat) (s s' : State p) : Prop :=
  term = s.currentTerm i ∧
  s.role i = Role.candidate ∧
  s' = { s with role := update s.role i Role.follower }

def appendEntriesAlreadyDone [DecidableEq p.Server]
    (i : p.Server) (prevLogIndex : Nat) (entries : List (Entry p))
    (commitIndex : Nat) (s s' : State p) : Prop :=
  let index := prevLogIndex + 1
  (entries = [] ∨
    ∃ entry existing,
      entries[0]? = some entry ∧
      get1 (s.log i) index = some existing ∧
      existing.term = entry.term) ∧
  s' = { s with commitIndex := update s.commitIndex i commitIndex }

def conflictAppendEntriesRequest [DecidableEq p.Server]
    (i : p.Server) (index : Nat) (entries : List (Entry p)) (s s' : State p) : Prop :=
  ∃ entry existing,
    entries[0]? = some entry ∧
    get1 (s.log i) index = some existing ∧
    existing.term ≠ entry.term ∧
    s' = { s with log := update s.log i (subSeq (s.log i) 1 ((s.log i).length - 1)) }

def noConflictAppendEntriesRequestAt [DecidableEq p.Server]
    (i : p.Server) (prevLogIndex : Nat) (entries : List (Entry p)) (s s' : State p) : Prop :=
  ∃ entry,
    entries[0]? = some entry ∧
    (s.log i).length = prevLogIndex ∧
    s' = { s with log := update s.log i (s.log i ++ [entry]) }

def acceptAppendEntriesRequest [DecidableEq p.Server]
    (i : p.Server) (term prevLogIndex : Nat) (entries : List (Entry p))
    (commitIndex : Nat) (logOk : Prop) (s s' : State p) : Prop :=
  term = s.currentTerm i ∧
  s.role i = Role.follower ∧
  logOk ∧
  let index := prevLogIndex + 1
  (appendEntriesAlreadyDone i prevLogIndex entries commitIndex s s' ∨
   conflictAppendEntriesRequest i index entries s s' ∨
   noConflictAppendEntriesRequestAt i prevLogIndex entries s s')

def handleAppendEntriesRequest [DecidableEq p.Server]
    (i _j : p.Server) (term prevLogIndex prevLogTerm : Nat)
    (entries : List (Entry p)) (commitIndex : Nat)
    (s s' : State p) : Prop :=
  let logOk :=
    prevLogIndex = 0 ∨
      ∃ entry,
        get1 (s.log i) prevLogIndex = some entry ∧
        prevLogTerm = entry.term
  term ≤ s.currentTerm i ∧
  (rejectAppendEntriesRequest i term logOk s s' ∨
   returnToFollowerState i term s s' ∨
   acceptAppendEntriesRequest i term prevLogIndex entries commitIndex logOk s s')

def handleAppendEntriesResponse [DecidableEq p.Server]
    (i j : p.Server) (term matchIndex : Nat) (success : Bool)
    (s s' : State p) : Prop :=
  term = s.currentTerm i ∧
  let s₁ :=
    if success then
      { s with
        nextIndex := update₂ s.nextIndex i j (matchIndex + 1)
        matchIndex := update₂ s.matchIndex i j matchIndex }
    else
      { s with nextIndex := update₂ s.nextIndex i j (Nat.max (s.nextIndex i j - 1) 1) }
  s' = s₁

def handleCatchupRequest [DecidableEq p.Server]
    (i _j : p.Server) (term logLen : Nat) (entries : List (Entry p))
    (_commitIndex _rounds : Nat) (s s' : State p) : Prop :=
  (term < s.currentTerm i ∧
    s' = s) ∨
  (term ≥ s.currentTerm i ∧
    let newLog :=
      if s.log i = [] then entries
      else subSeq (s.log i) 1 (Nat.min logLen (s.log i).length) ++ entries
    s' =
      { s with
        currentTerm := update s.currentTerm i term
        log := update s.log i newLog })

def handleCatchupResponse [DecidableEq p.Server]
    (i j : p.Server) (term matchIndex _roundsLeft : Nat) (success : Bool)
    (s s' : State p) : Prop :=
  (success = true ∧
    ((matchIndex ≠ s.commitIndex i ∧ matchIndex ≠ s.matchIndex i j) ∨
      matchIndex = s.commitIndex i) ∧
    s.role i = Role.leader ∧
    term = s.currentTerm i ∧
    ¬ getConfig s i j ∧
    let s₁ :=
      { s with
        nextIndex := update₂ s.nextIndex i j (matchIndex + 1)
        matchIndex := update₂ s.matchIndex i j matchIndex }
    s' = s₁) ∨
  ((success = false ∨
      (((matchIndex = s.commitIndex i ∨ matchIndex = s.matchIndex i j) ∧
        matchIndex ≠ s.commitIndex i) ∨
       s.role i ≠ Role.leader ∨
       term ≠ s.currentTerm i ∨
       getConfig s i j)) ∧
    s' = s)

def handleCheckOldConfig [DecidableEq p.Server]
    (i : p.Server) (term : Nat) (add : Bool) (server : p.Server)
    (s s' : State p) : Prop :=
  ((s.role i ≠ Role.leader ∨ term ≠ s.currentTerm i) ∧ s' = s) ∨
  (s.role i = Role.leader ∧ term = s.currentTerm i ∧
    ((∀ idx entry,
        get1 (s.log i) idx = some entry →
        entry.kind = EntryKind.config →
        idx ≤ s.commitIndex i) ∧
      let newConfig := if add then insertSet (getConfig s i) server else removeSet (getConfig s i) server
      let configChanged := ∃ x, getConfig s i x ↔ ¬ newConfig x
      let newEntry : Entry p :=
        { term := s.currentTerm i, kind := EntryKind.config, value := EntryValue.config newConfig }
      let s₁ := if configChanged then { s with log := update s.log i (s.log i ++ [newEntry]) } else s
      s' = s₁) ∨
    ((∃ idx entry,
        get1 (s.log i) idx = some entry ∧
        entry.kind = EntryKind.config ∧
        idx > s.commitIndex i) ∧
      s' = s))

def updateTerm [DecidableEq p.Server]
    (i : p.Server) (term : Nat) (s s' : State p) : Prop :=
  term > s.currentTerm i ∧
  s' =
    { s with
      currentTerm := update s.currentTerm i term
      role := update s.role i Role.follower
      votedFor := update s.votedFor i none }

def dropStaleResponse (i : p.Server) (term : Nat) (s s' : State p) : Prop :=
  term < s.currentTerm i ∧
  s' = s

/-- The one-step transition relation generated by all Raft actions. -/
inductive Step [DecidableEq p.Server] (s s' : State p) : Prop where
  | becomeLeader (i : p.Server) :
      p.InServer i → becomeLeader i s s' → Step s s'
  | clientRequest (i : p.Server) (v : p.Value) :
      p.InServer i → clientRequest i v s s' → Step s s'
  | advanceCommitIndex (i : p.Server) :
      p.InServer i → advanceCommitIndex i s s' → Step s s'
  | timeout (i : p.Server) :
      p.InServer i → timeout i s s' → Step s s'
  | receiveRequestVoteRequest
      (term lastLogTerm lastLogIndex : Nat) (source dest : p.Server) :
      (updateTerm dest term s s' ∨
        handleRequestVoteRequest dest source term lastLogTerm lastLogIndex s s') →
      Step s s'
  | receiveRequestVoteResponse
      (term : Nat) (voteGranted : Bool) (log : List (Entry p)) (source dest : p.Server) :
      (updateTerm dest term s s' ∨
        dropStaleResponse dest term s s' ∨
        handleRequestVoteResponse dest source term voteGranted s s') →
      Step s s'
  | receiveAppendEntriesRequest
      (term prevLogIndex prevLogTerm : Nat) (entries : List (Entry p))
      (commitIndex : Nat) (source dest : p.Server) :
      (updateTerm dest term s s' ∨
        handleAppendEntriesRequest dest source term prevLogIndex prevLogTerm entries commitIndex s s') →
      Step s s'
  | receiveAppendEntriesResponse
      (term : Nat) (success : Bool) (matchIndex : Nat) (source dest : p.Server) :
      (updateTerm dest term s s' ∨
        dropStaleResponse dest term s s' ∨
        handleAppendEntriesResponse dest source term matchIndex success s s') →
      Step s s'
  | receiveCatchupRequest
      (term logLen : Nat) (entries : List (Entry p)) (commitIndex : Nat)
      (source dest : p.Server) (rounds : Nat) :
      (updateTerm dest term s s' ∨
        handleCatchupRequest dest source term logLen entries commitIndex rounds s s') →
      Step s s'
  | receiveCatchupResponse
      (term : Nat) (success : Bool) (matchIndex : Nat)
      (source dest : p.Server) (roundsLeft : Nat) :
      (updateTerm dest term s s' ∨
        handleCatchupResponse dest source term matchIndex roundsLeft success s s') →
      Step s s'
  | receiveCheckOldConfig
      (term : Nat) (add : Bool) (server source dest : p.Server) :
      (updateTerm dest term s s' ∨
        handleCheckOldConfig dest term add server s s') →
      Step s s'

end Action

/-- Reachability from the initial state under zero or more Raft steps. -/
inductive Reachable {p : Params} [DecidableEq p.Server] : State p → Prop where
  | init : Reachable (State.init p)
  | step {s s' : State p} :
      Reachable s → Action.Step s s' → Reachable s'

end

end CommunicationClosure.Protocols.Raft

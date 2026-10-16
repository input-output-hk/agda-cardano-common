{-# OPTIONS --guardedness #-}

-- Two real model admissions establish the registry's allocation premises.
-- The initial fixture starts after accepted-socket handoff, not at accept().
module ConnectionManagement.CSP.RegistryAdmission where

open import Data.List using (List; []; _∷_; map; take)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_ )
open import ConnectionManagement.Store using (Store; put)
import ConnectionManagement.Rules.OriginMonitor as Single
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; allocate; dispatch; erase)
import ConnectionManagement.Rules.Server as Server
open import ConnectionManagement.Properties.HandlerResources using (Resources; selection-fork-resources)
import ConnectionManagement.Properties.HandlerDispatcherInterference as Retention
import ConnectionManagement.Properties.OriginRegistry as Proof
open import ConnectionManagement.CSP.OriginRegistry
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
import ConnectionManagement.CSP.Process as OpenProcess
import ConnectionManagement.CSP.Correspondence as OpenProof
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (w₀; w₁; child₀; child₁; key₀; key₁; r₀; r₁)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

allocation₁ allocation₂ publication₁ publication₂ : Action
allocation₁ = allocate child₀ (ident 0) (ident 0) key₀ (G.proto ∷ []) duplex
allocation₂ = allocate child₁ (ident 1) (ident 1) key₁ (G.proto ∷ []) duplex
publication₁ = dispatch (Open.handlerPublication child₀ (S.negotiated (ident 0) duplex) Open.resultWritten)
publication₂ = dispatch (Open.handlerPublication child₁ (S.negotiated (ident 1) duplex) Open.resultWritten)

-- Explicit snapshots keep transition checks local rather than expanding replay.
ticket₁ ticket₂ : Single.Ticket
ticket₁ = Single.ticket (ident 0) (G.proto ∷ []) duplex
ticket₂ = Single.ticket (ident 1) (G.proto ∷ []) duplex
pending₁ pending₂ published₁ published₂ : Entry
pending₁ = entry (Single.target child₀ (ident 0)) (Single.awaitingPublication ticket₁)
pending₂ = entry (Single.target child₁ (ident 1)) (Single.awaitingPublication ticket₂)
published₁ = entry (Single.target child₀ (ident 0)) (Single.published ticket₁)
published₂ = entry (Single.target child₁ (ident 1)) (Single.published ticket₂)

s0 s1 s2 s3 s4 s5 s6 s7 s8 : State
s0 = start F.start
s1 = start (F.pre (S.cmStore (S.taken w₀) [] 0) (S.count F.parentLease) [] 0)
s2 = start (F.pre (S.cmStore (S.taken w₀) [] 0) (S.prepare F.parentLease) [] 0)
s3 = start E.beforeSelect
s4 = start E.beforeFork
s5 = start E.forked
s6 = registry E.installed (pending₁ ∷ [])
s7 = registry (record (F.snapshot F.unneg (S.full F.binding)
  (S.countPublished (ident 0) (ident 0)) (S.handling child₀) [] [] [])
  { inboundGovernor = Open.inboundGovernor G.installed }) (pending₁ ∷ [])
s8 = registry (record F.waiting { inboundGovernor = Open.inboundGovernor G.installed }) (pending₁ ∷ [])

-- Builders specify finite fixtures only; they are not operational rules.
second : S.AdmissionPC → S.CMStore → List PromiseId → ℕ →
  Store WorkerId S.HandlerStart → Store SocketId S.SocketOwner → Open.Configuration
second pc cm ps n hs ss = record (machine s8) { world = record (Open.world (machine s8))
  { admissions = put w₁ (S.admissionWorker r₁ pc) (S.admissions (Open.world (machine s8)))
  ; cm = cm; promises = ps; nextPromise = n; handlers = hs; sockets = ss } }
lease₂ : S.Lease
lease₂ = S.lease w₁ F.binding
locked selectedCM restoredCM : S.CMStore
locked = S.cmStore (S.taken w₁) ((ident 0 , F.unneg) ∷ []) 1
selectedCM = S.cmStore (S.taken w₁)
  ((ident 0 , F.unneg) ∷ (ident 1 , S.unnegotiated inbound key₁ child₁) ∷ []) 2
restoredCM = record selectedCM { mapCell = S.full (S.insertConnection key₁ (ident 1) F.binding) }
oldHandlers : Store WorkerId S.HandlerStart
oldHandlers = S.handlers (Open.world (machine s8))
oldSockets : Store SocketId S.SocketOwner
oldSockets = S.sockets (Open.world (machine s8))
newHandlers : Store WorkerId S.HandlerStart
newHandlers = put child₁ (S.handlerStart (ident 1) (ident 1) (ident 1) key₁) oldHandlers
newSockets : Store SocketId S.SocketOwner
newSockets = put (ident 1) (S.handling child₁) oldSockets
s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 : State
s9 = registry (second (S.count lease₂) locked (ident 0 ∷ []) 1 oldHandlers oldSockets) (pending₁ ∷ [])
s10 = registry (second (S.prepare lease₂) locked (ident 0 ∷ []) 1 oldHandlers oldSockets) (pending₁ ∷ [])
s11 = registry (second (S.selectEntry lease₂ (ident 1)) locked (ident 1 ∷ ident 0 ∷ []) 2 oldHandlers oldSockets) (pending₁ ∷ [])
s12 = registry (second (S.forkHandler lease₂ (ident 1) (ident 1)) selectedCM (ident 1 ∷ ident 0 ∷ []) 2 oldHandlers oldSockets) (pending₁ ∷ [])
s13 = registry (second (S.publish lease₂ (ident 1) (ident 1)) selectedCM (ident 1 ∷ ident 0 ∷ []) 2 newHandlers newSockets) (pending₁ ∷ [])
s14 = registry (second (S.countPublished (ident 1) (ident 1)) restoredCM (ident 1 ∷ ident 0 ∷ []) 2 newHandlers newSockets) (pending₁ ∷ [])
s15 = registry (second (S.awaitHandshake (ident 1) (ident 1)) restoredCM (ident 1 ∷ ident 0 ∷ []) 2 newHandlers newSockets) (pending₁ ∷ [])
s16 = registry (record (machine s15)
  { inboundGovernor = record (Open.inboundGovernor (machine s15))
    { execution = record G.e₀
      { handles = put (ident 1) (M.handleState (ident 1) (G.proto ∷ []) duplex) G.handleTable
      ; muxes = put (ident 1) (record G.newMux { key = key₁ }) ((G.mid , G.newMux) ∷ []) } } }) (pending₂ ∷ pending₁ ∷ [])
s17 = registry (record (machine s16) { world = record (Open.world (machine s16))
  { handshakeResults = (ident 1 , S.negotiated (ident 1) duplex) ∷ [] } }) (published₂ ∷ pending₁ ∷ [])
s18 = registry (record (machine s17) { world = record (Open.world (machine s17))
  { handshakeResults = (ident 1 , S.negotiated (ident 1) duplex) ∷ (ident 0 , S.negotiated (ident 0) duplex) ∷ [] } }) (published₂ ∷ published₁ ∷ [])

schedule : List Action
schedule =
  dispatch (Open.admissionStep w₀ Server.take) ∷
  dispatch (Open.admissionStep w₀ Server.countLimit) ∷
  dispatch (Open.admissionStep w₀ Server.allocatePromise) ∷
  dispatch (Open.admissionStep w₀ Server.chooseEntry) ∷
  dispatch (Open.admissionStep w₀ Server.fork) ∷
  allocation₁ ∷
  dispatch (Open.admissionStep w₀ Server.putMapBack) ∷
  dispatch (Open.admissionStep w₀ Server.readCounters) ∷
  dispatch (Open.admissionStep w₁ Server.take) ∷
  dispatch (Open.admissionStep w₁ Server.countLimit) ∷
  dispatch (Open.admissionStep w₁ Server.allocatePromise) ∷
  dispatch (Open.admissionStep w₁ Server.chooseEntry) ∷
  dispatch (Open.admissionStep w₁ Server.fork) ∷
  dispatch (Open.admissionStep w₁ Server.putMapBack) ∷
  dispatch (Open.admissionStep w₁ Server.readCounters) ∷
  allocation₂ ∷
  publication₂ ∷
  publication₁ ∷ []
path : Executes s0 schedule s18
path = next {s₁ = s1} refl (next {s₁ = s2} refl (next {s₁ = s3} refl (next {s₁ = s4} refl (next {s₁ = s5} refl (next {s₁ = s6} refl (next {s₁ = s7} refl (next {s₁ = s8} refl (next {s₁ = s9} refl (next {s₁ = s10} refl (next {s₁ = s11} refl (next {s₁ = s12} refl (next {s₁ = s13} refl (next {s₁ = s14} refl (next {s₁ = s15} refl (next {s₁ = s16} refl (next {s₁ = s17} refl (next {s₁ = s18} refl (done))))))))))))))))))

-- Each certificate is produced by successful CM selection and Server fork.
first-resources : Resources child₀ (Open.world (machine s5))
first-resources = selection-fork-resources w₀ r₀ F.parentLease (ident 0) (machine s3)
  {c₁ = machine s4} {c₂ = machine s5} refl refl refl
second-fork-resources : Resources child₁ (Open.world (machine s13))
second-fork-resources = selection-fork-resources w₁ r₁ (S.lease w₁ F.binding) (ident 1) (machine s11)
  {c₁ = machine s12} {c₂ = machine s13} refl refl refl

second-parent-path : Open.Executes (machine s13)
  (Open.admissionStep w₁ Server.putMapBack ∷ Open.admissionStep w₁ Server.readCounters ∷ []) (machine s15)
second-parent-path = Open.next {c₁ = machine s14} refl (Open.next refl Open.done)
second-resources : Resources child₁ (Open.world (machine s15))
second-resources = Retention.all-resources second-parent-path second-fork-resources

supported : Proof.Supported path
supported = Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next first-resources (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next second-resources (Proof.next tt (Proof.next tt (Proof.done))))))))))))))))))

all-certified : Proof.Invariant s18
all-certified = Proof.reachable path supported
accepted : traces (Process s0) (map label schedule)
accepted = trace-intro path

-- Projection retains the whole admission/allocation/publication schedule.
open import Semantics.Failures {E = OpenProcess.Channel} {I = ExtI OpenProcess.Channel}
  using () renaming (traces to open-traces)
projected : open-traces (OpenProcess.Process F.start) (map OpenProcess.label (map erase schedule))
projected = OpenProof.trace-intro (Proof.exec-projects path)

-- Both handles are allocated before either promise is filled.
both-pending : entries s16 ≡
  entry (Single.target child₁ (ident 1)) (Single.awaitingPublication (Single.ticket (ident 1) (G.proto ∷ []) duplex)) ∷
  entry (Single.target child₀ (ident 0)) (Single.awaitingPublication (Single.ticket (ident 0) (G.proto ∷ []) duplex)) ∷ []
both-pending = refl
both-published : entries s18 ≡
  entry (Single.target child₁ (ident 1)) (Single.published (Single.ticket (ident 1) (G.proto ∷ []) duplex)) ∷
  entry (Single.target child₀ (ident 0)) (Single.published (Single.ticket (ident 0) (G.proto ∷ []) duplex)) ∷ []
both-published = refl

-- Certify the first ticket after the second admission, before its allocation.
second-admission-prefix : Executes s0 (take 15 schedule) s15
second-admission-prefix = next {s₁ = s1} refl (next {s₁ = s2} refl (next {s₁ = s3} refl (next {s₁ = s4} refl (next {s₁ = s5} refl (next {s₁ = s6} refl (next {s₁ = s7} refl (next {s₁ = s8} refl (next {s₁ = s9} refl (next {s₁ = s10} refl (next {s₁ = s11} refl (next {s₁ = s12} refl (next {s₁ = s13} refl (next {s₁ = s14} refl (next {s₁ = s15} refl (done)))))))))))))))
second-admission-supported : Proof.Supported second-admission-prefix
second-admission-supported = Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next first-resources (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt (Proof.done)))))))))))))))
first-retained : Proof.Invariant s15
first-retained = Proof.reachable second-admission-prefix second-admission-supported

-- A reusable prefix for negative controls at the jointly pending state.
allocation-prefix : Executes s0 (take 16 schedule) s16
allocation-prefix = next {s₁ = s1} refl (next {s₁ = s2} refl (next {s₁ = s3} refl (next {s₁ = s4} refl (next {s₁ = s5} refl (next {s₁ = s6} refl (next {s₁ = s7} refl (next {s₁ = s8} refl (next {s₁ = s9} refl (next {s₁ = s10} refl (next {s₁ = s11} refl (next {s₁ = s12} refl (next {s₁ = s13} refl (next {s₁ = s14} refl (next {s₁ = s15} refl (next {s₁ = s16} refl (done))))))))))))))))

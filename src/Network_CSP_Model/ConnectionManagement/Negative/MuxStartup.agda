{-# OPTIONS --guardedness #-}

-- Initialized standalone startup controls. The publication event is the
-- prerequisite's explicit input, not a source handler reachability theorem.
module ConnectionManagement.Negative.MuxStartup where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; _×_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.Rules.MuxStartup as Startup
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Properties.MuxStartup as Properties
module S = Startup ⊤
module P = Properties ⊤
module Pool = S.Pool

muxer₀ demuxer₀ : JobId
muxer₀ = ident 0
demuxer₀ = ident 1

firstFork firstRegistered secondFork bothRegistered : Pool.State
firstFork = record Pool.initial
  { handles = (muxer₀ , Pool.bodyRunning) ∷ []; parentFork = just muxer₀ }
firstRegistered = record firstFork { registered = muxer₀ ∷ []; parentFork = nothing }
secondFork = record firstRegistered
  { handles = (muxer₀ , Pool.bodyRunning) ∷ (demuxer₀ , Pool.bodyRunning) ∷ []
  ; parentFork = just demuxer₀ }
bothRegistered = record secondFork { registered = demuxer₀ ∷ muxer₀ ∷ []; parentFork = nothing }

s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ : S.State
s₀ = S.initial
s₁ = S.startupState S.published Pool.initial
s₂ = S.startupState S.bufferReady Pool.initial
s₃ = S.startupState S.bearerReady Pool.initial
s₄ = S.startupState S.runEntered Pool.initial
s₅ = S.startupState S.startingTraced Pool.initial
s₆ = S.startupState S.egressReady Pool.initial
s₇ = S.startupState S.poolReady Pool.initial
s₈ = S.startupState (S.muxerForked muxer₀) firstFork
s₉ = S.startupState (S.muxerRegistered muxer₀) firstRegistered
s₁₀ = S.startupState (S.demuxerForked muxer₀ demuxer₀) secondFork
s₁₁ = S.startupState (S.demuxerRegistered muxer₀ demuxer₀) bothRegistered
s₁₂ = S.startupState (S.matureTraced muxer₀ demuxer₀) bothRegistered
s₁₃ = S.startupState (S.monitoring muxer₀ demuxer₀) bothRegistered

append : ∀ {p as q bs r} → S.Executes p as q → S.Executes q bs r → S.Executes p (as ++ bs) r
append S.done tail = tail
append (S.next eq path) tail = S.next eq (append path tail)
prefixActions : List S.Action
prefixActions = S.observePublication ∷ S.allocateBuffer ∷ S.createBearer ∷ S.enterRun ∷
  S.traceStarting ∷ S.allocateEgress ∷ S.openPool ∷ S.forkMuxer muxer₀ ∷ []
prefix : S.Executes s₀ prefixActions s₈
prefix = S.next refl (S.next refl (S.next refl (S.next refl
  (S.next refl (S.next refl (S.next refl (S.next refl S.done)))))))
suffixActions : List S.Action
suffixActions = S.registerMuxer ∷ S.forkDemuxer demuxer₀ ∷ S.registerDemuxer ∷ S.traceMature ∷ S.enterMonitor ∷ []
suffix : S.Executes s₈ suffixActions s₁₃
suffix = S.next refl (S.next refl (S.next refl (S.next refl (S.next refl S.done))))
initialized-startup : S.Executes S.initial (prefixActions ++ suffixActions) s₁₃
initialized-startup = append prefix suffix

-- These are the four real queued-pool transitions underlying that startup.
physical-forks-and-registrations : Pool.Executes Pool.initial
  (Pool.fork muxer₀ ∷ Pool.register ∷ Pool.fork demuxer₀ ∷ Pool.register ∷ []) bothRegistered
physical-forks-and-registrations = Pool.next refl (Pool.next refl (Pool.next refl (Pool.next refl Pool.done)))
initialized-physical-certificate : P.Pair muxer₀ demuxer₀ bothRegistered × P.PoolTrace Pool.initial bothRegistered
initialized-physical-certificate = P.monitoring-from-initial muxer₀ demuxer₀ initialized-startup refl

buffer-before-publication-refused : S.step S.allocateBuffer s₀ ≡ nothing
buffer-before-publication-refused = refl
pool-before-bearer-refused : S.step S.openPool s₂ ≡ nothing
pool-before-bearer-refused = refl
second-fork-before-first-registration-refused : S.step (S.forkDemuxer demuxer₀) s₈ ≡ nothing
second-fork-before-first-registration-refused = refl
kernel-second-fork-in-masked-gap-refused : Pool.step (Pool.fork demuxer₀) firstFork ≡ nothing
kernel-second-fork-in-masked-gap-refused = refl
physical-id-reuse-refused : S.step (S.forkDemuxer muxer₀) s₉ ≡ nothing
physical-id-reuse-refused = refl
monitor-before-second-fork-refused : S.step S.enterMonitor s₉ ≡ nothing
monitor-before-second-fork-refused = refl
monitor-before-mature-refused : S.step S.enterMonitor s₁₁ ≡ nothing
monitor-before-mature-refused = refl
mature-before-second-registration-refused : S.step S.traceMature s₁₀ ≡ nothing
mature-before-second-registration-refused = refl

-- The first child can return and publish into the shared queue before its
-- parent's insertion. The real registry still blocks premature deregistration.
returned queued inserted removed terminal : Pool.State
returned = record firstFork { handles = (muxer₀ , Pool.bodyReturned tt) ∷ [] }
queued = record returned
  { handles = (muxer₀ , Pool.deregisterPending Pool.normalExit) ∷ []; completions = tt ∷ [] }
inserted = record queued { registered = muxer₀ ∷ []; parentFork = nothing }
removed = record inserted { handles = (muxer₀ , Pool.deregistered Pool.normalExit) ∷ []; registered = [] }
terminal = record removed { handles = (muxer₀ , Pool.resultAvailable Pool.normalExit) ∷ [] }
fast₁ fast₂ fast₃ fast₄ fast₅ : S.State
fast₁ = S.startupState (S.muxerForked muxer₀) returned
fast₂ = S.startupState (S.muxerForked muxer₀) queued
fast₃ = S.startupState (S.muxerRegistered muxer₀) inserted
fast₄ = S.startupState (S.muxerRegistered muxer₀) removed
fast₅ = S.startupState (S.muxerRegistered muxer₀) terminal
child-return-before-registration : S.step (S.child (S.bodyReturned muxer₀ tt)) s₈ ≡ just fast₁
child-return-before-registration = refl
child-publication-before-registration : S.step (S.child (S.publishCompletion muxer₀)) fast₁ ≡ just fast₂
child-publication-before-registration = refl
deregister-before-insertion-refused : S.step (S.child (S.deregister muxer₀)) fast₂ ≡ nothing
deregister-before-insertion-refused = refl
insert-after-child-publication : S.step S.registerMuxer fast₂ ≡ just fast₃
insert-after-child-publication = refl
child-deregister-after-insertion : S.step (S.child (S.deregister muxer₀)) fast₃ ≡ just fast₄
child-deregister-after-insertion = refl
child-async-result-after-deregister : S.step (S.child (S.publishAsyncResult muxer₀)) fast₄ ≡ just fast₅
child-async-result-after-deregister = refl
completed-id-still-not-reusable : S.step (S.forkDemuxer muxer₀) fast₅ ≡ nothing
completed-id-still-not-reusable = refl

fastActions : List S.Action
fastActions = S.child (S.bodyReturned muxer₀ tt) ∷ S.child (S.publishCompletion muxer₀) ∷
  S.registerMuxer ∷ S.child (S.deregister muxer₀) ∷ S.child (S.publishAsyncResult muxer₀) ∷ []
fastSuffix : S.Executes s₈ fastActions fast₅
fastSuffix = S.next refl (S.next refl (S.next refl (S.next refl (S.next refl S.done))))
initialized-fast-child : S.Executes S.initial (prefixActions ++ fastActions) fast₅
initialized-fast-child = append prefix fastSuffix
initialized-fast-capture : P.Valid fast₅
initialized-fast-capture = P.from-initial initialized-fast-child

fastSecondFork fastBothRegistered : Pool.State
fastSecondFork = record terminal
  { handles = (muxer₀ , Pool.resultAvailable Pool.normalExit) ∷ (demuxer₀ , Pool.bodyRunning) ∷ []
  ; parentFork = just demuxer₀ }
fastBothRegistered = record fastSecondFork { registered = demuxer₀ ∷ []; parentFork = nothing }
fast₆ fast₇ fast₈ fast₉ : S.State
fast₆ = S.startupState (S.demuxerForked muxer₀ demuxer₀) fastSecondFork
fast₇ = S.startupState (S.demuxerRegistered muxer₀ demuxer₀) fastBothRegistered
fast₈ = S.startupState (S.matureTraced muxer₀ demuxer₀) fastBothRegistered
fast₉ = S.startupState (S.monitoring muxer₀ demuxer₀) fastBothRegistered
fastMonitorActions : List S.Action
fastMonitorActions = S.forkDemuxer demuxer₀ ∷ S.registerDemuxer ∷ S.traceMature ∷ S.enterMonitor ∷ []
fastMonitorSuffix : S.Executes fast₅ fastMonitorActions fast₉
fastMonitorSuffix = S.next refl (S.next refl (S.next refl (S.next refl S.done)))
initialized-fast-monitoring : S.Executes S.initial ((prefixActions ++ fastActions) ++ fastMonitorActions) fast₉
initialized-fast-monitoring = append initialized-fast-child fastMonitorSuffix
initialized-fast-physical-certificate : P.Pair muxer₀ demuxer₀ fastBothRegistered × P.PoolTrace Pool.initial fastBothRegistered
initialized-fast-physical-certificate = P.monitoring-from-initial muxer₀ demuxer₀ initialized-fast-monitoring refl


-- Configured startups: the layout alone fixes the ordered roles. Each
-- execution certificate below proves that the guarded execution returned just.
exec : List S.Action → S.State → Maybe S.State
exec [] s = just s
exec (a ∷ as) s with S.step a s
... | nothing = nothing
... | just t = exec as t
exec-runs : ∀ as s {t} → exec as s ≡ just t → S.Executes s as t
exec-runs [] s refl = S.done
exec-runs (a ∷ as) s eq with S.step a s in advanced
... | just next = S.next advanced (exec-runs as next eq)
toEgress : List S.Action
toEgress = S.observePublication ∷ S.allocateBuffer ∷ S.createBearer ∷ S.enterRun ∷ S.traceStarting ∷ S.allocateEgress ∷ []
-- n configured forks, each followed by its parent registration, ids k..k+n-1.
forkRegister : ℕ → ℕ → List S.Action
forkRegister k 0 = []
forkRegister k (suc n) = S.forkConfigured (ident k) ∷ S.registerConfigured ∷ forkRegister (suc k) n
configuredActions : E.Layout → ℕ → List S.Action
configuredActions plan n = toEgress ++ (S.configureStartup plan ∷ S.openPool ∷
  forkRegister 0 n ++ (S.traceConfiguredMature ∷ S.enterConfiguredMonitor ∷ []))
final : E.Layout → ℕ → S.State
final plan n with exec (configuredActions plan n) S.initial
... | just t = t
... | nothing = S.initial

initialized-plain2 : S.Executes S.initial (configuredActions E.plainLayout 2) (final E.plainLayout 2)
initialized-plain2 = exec-runs (configuredActions E.plainLayout 2) S.initial refl
initialized-scheduled3 : S.Executes S.initial (configuredActions (E.scheduledLayout false) 3) (final (E.scheduledLayout false) 3)
initialized-scheduled3 = exec-runs (configuredActions (E.scheduledLayout false) 3) S.initial refl
initialized-slice4 : S.Executes S.initial (configuredActions (E.scheduledLayout true) 4) (final (E.scheduledLayout true) 4)
initialized-slice4 = exec-runs (configuredActions (E.scheduledLayout true) 4) S.initial refl

-- Exact ordered role bindings and monitor entry after the complete plan.
plain2-roles : S.infraBindings (S.phase (final E.plainLayout 2)) ≡ (Types.muxer , ident 0) ∷ (Types.demuxer , ident 1) ∷ []
plain2-roles = refl
scheduled3-roles : S.infraBindings (S.phase (final (E.scheduledLayout false) 3)) ≡
  (Types.laneMuxer E.directLane , ident 0) ∷ (Types.laneMuxer E.scheduledLane , ident 1) ∷ (Types.demuxer , ident 2) ∷ []
scheduled3-roles = refl
slice4-roles : S.infraBindings (S.phase (final (E.scheduledLayout true) 4)) ≡
  (Types.laneMuxer E.directLane , ident 0) ∷ (Types.laneMuxer E.scheduledLane , ident 1) ∷
  (Types.laneMuxer E.sliceLane , ident 2) ∷ (Types.demuxer , ident 3) ∷ []
slice4-roles = refl
slice4-monitoring : S.monitoringPC (S.phase (final (E.scheduledLayout true) 4)) ≡ true
slice4-monitoring = refl
slice4-lane-role : S.roleId (Types.laneMuxer E.sliceLane) (S.phase (final (E.scheduledLayout true) 4)) ≡ just (ident 2)
slice4-lane-role = refl
missing-slice-has-no-role : Types.roleForLane (E.scheduledLayout false) E.sliceLane ≡ nothing
missing-slice-has-no-role = refl
lane-muxers-share-result-tag : Types.infraResult (Types.laneMuxer E.sliceLane) (errorId 7) ≡ Types.infraResult Types.muxer (errorId 7)
lane-muxers-share-result-tag = refl
scheduled3-certificate : P.ConfiguredValid
  (S.configuredFrame (E.scheduledLayout false) 3
    ((Types.laneMuxer E.directLane , ident 0) ∷ (Types.laneMuxer E.scheduledLane , ident 1) ∷ (Types.demuxer , ident 2) ∷ [])
    S.cfgMonitoring) (S.pool (final (E.scheduledLayout false) 3))
scheduled3-certificate = proj₁ (P.configured-from-initial _ initialized-scheduled3 refl)
  where open import Data.Product using (proj₁)

-- Refusals: no fork before the previous registration, no Mature before the
-- plan is exhausted, no extra fork afterwards, no late configuration, no reuse.
cfgReady1 cfgForked1 cfgDone : S.State
cfgReady1 = final (E.scheduledLayout false) 0
cfgForked1 with exec (toEgress ++ (S.configureStartup (E.scheduledLayout false) ∷ S.openPool ∷ S.forkConfigured (ident 0) ∷ [])) S.initial
... | just t = t
... | nothing = S.initial
cfgDone = final (E.scheduledLayout false) 3
no-mature-before-plan : S.step S.traceConfiguredMature cfgForked1 ≡ nothing
no-mature-before-plan = refl
no-fork-in-registration-gap : S.step (S.forkConfigured (ident 1)) cfgForked1 ≡ nothing
no-fork-in-registration-gap = refl
no-fork-after-plan : S.step (S.forkConfigured (ident 9)) cfgDone ≡ nothing
no-fork-after-plan = refl
no-late-configuration : S.step (S.configureStartup E.plainLayout) s₇ ≡ nothing
no-late-configuration = refl
no-legacy-fork-in-configured-frame : S.step (S.forkMuxer (ident 9)) cfgForked1 ≡ nothing
no-legacy-fork-in-configured-frame = refl

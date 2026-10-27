{-# OPTIONS --guardedness #-}

-- Initialized standalone startup controls. The publication event is the
-- prerequisite's explicit input, not a source handler reachability theorem.
module ConnectionManagement.Negative.MuxStartup where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; _×_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.Rules.MuxStartup as Startup
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

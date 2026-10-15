{-# OPTIONS --guardedness #-}

-- Caller, mux and cleanup interleavings before publication and attachment.
module ConnectionManagement.CSP.HandlerRuntimeInterference where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerEstablishment
open import ConnectionManagement.Properties.HandlerRuntimeInterference
open import ConnectionManagement.Properties.HandlerConsumerEffects using (ParentAction)
import ConnectionManagement.Properties.HandlerConsumerEffects as Effects
open import ConnectionManagement.Properties.HandlerReferences using (Chain; TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement using (all-exec-preserves)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; cancelError)
import ConnectionManagement.CSP.HandlerEstablishment as Establish
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; key₀)
open import ConnectionManagement.Scenarios.Handshake using (success; info)
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-resources : ∀ {c as P w} → Interference as → Resources w (world c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Resources w (world c′))
raw-resources covered r reach with exec-inv reach
... | c′ , same , path = c′ , same , resources-exec covered path r

raw-prepared : ∀ {c as P w hid mid} → Interference as → Prepared w hid mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Prepared w hid mid (world c′) (inboundGovernor c′))
raw-prepared covered p reach with exec-inv reach
... | c′ , same , path = c′ , same , prepared-exec covered path p

-- Interference lists are restricted; the suffix after attachment is arbitrary.
raw-delayed-attachment : ∀ {w hid mid c P} flow err before after suffix →
  Interference before → Interference after → Prepared w hid mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label (before ++
    (handlerPublication w (negotiated hid flow) resultWritten ∷
      (after ++ (handlerStep w (L.attach err) ∷ suffix)))) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-delayed-attachment {w} {hid} {mid} flow err before after suffix beforeCovered afterCovered prepared reach
  with exec-inv reach
... | c′ , same , path with exec-split before path
...   | c₁ , beforePath , next {c₁ = c₂} published rest with exec-split after rest
...     | c₃ , afterPath , next attached suffixPath = c′ , same ,
  all-exec-preserves suffixPath w (attach-established w err c₃
    (chain-exec afterCovered afterPath
      (publication-creates w hid mid flow c₁ (prepared-exec beforeCovered beforePath prepared) published)) attached)

import ConnectionManagement.Properties.MuxRetention as Mux
import ConnectionManagement.CSP.IGRuntime as Runtime
import ConnectionManagement.CSP.HandlerInterference as Caller
import ConnectionManagement.Rules.Cleanup as C
open import ConnectionManagement.Store using (lookup)

-- This registration fixture is reached by G.lifecycle-path without attachment.
-- Its certificate says nothing about whether a later attach will be enabled.
registered-prepared : Prepared child₀ (ident 0) G.mid (world G.registered) (inboundGovernor G.registered)
registered-prepared = record
  { resources = record { original = _; found = refl; entryExists = _ , refl; socketExists = _ , refl }
  ; hd = _; mx = _; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl }
start-covered : Interference Runtime.startActions
start-covered = more (mux Mux.command) (more (mux Mux.demand) (more (mux Mux.sample)
  (more (mux Mux.trace) (more (mux Mux.started) (more (mux Mux.fork) empty)))))
running-prepared : Prepared child₀ (ident 0) G.mid (world Runtime.jobRunning) (inboundGovernor Runtime.jobRunning)
running-prepared = prepared-exec start-covered Runtime.start-path registered-prepared
running-csp : Process G.registered ⟹⟨ map label Runtime.startActions ⟩ Process Runtime.jobRunning
running-csp = exec-intro Runtime.start-path
whole-start-csp : Process F.start ⟹⟨ map label (G.lifecycle ++ Runtime.startActions) ⟩ Process Runtime.jobRunning
whole-start-csp = exec-intro (exec-append G.lifecycle-path Runtime.start-path)

-- Cleanup before publication: no lifecycle frame is ever attached here.
cleanupSnapshot : ConnectionState → MapCell → SocketOwner → CleanupPC → Configuration
cleanupSnapshot st cell owner pc = record
  (F.snapshot st cell (awaitHandshake (ident 0) (ident 0)) owner [] [] (F.cleanupStore pc))
  { inboundGovernor = inboundGovernor Caller.waiting }
exited takenMap selected socketClosed mapPublished cleaned : Configuration
exited = cleanupSnapshot F.unneg (full F.binding) (handling child₀) cleanupAcquire
takenMap = cleanupSnapshot F.unneg (taken child₀) (handling child₀) (cleanupSelect F.childLease)
selected = cleanupSnapshot (terminated nothing) (taken child₀) (handling child₀)
  (cleanupClose F.childLease [] countImmediately)
socketClosed = cleanupSnapshot (terminated nothing) (taken child₀) closed
  (cleanupPublish F.childLease [] countImmediately)
mapPublished = cleanupSnapshot (terminated nothing) (full []) closed (cleanupCount cleanupNormal)
cleaned = cleanupSnapshot (terminated nothing) (full []) closed (cleanupDone cleanupNormal)
cleanupActions : List Action
cleanupActions = handlerExit child₀ ∷ cleanupStep child₀ C.takeCleanupMap ∷
  cleanupStep child₀ C.selectCleanupEntry ∷ cleanupStep child₀ C.closeHandlerSocket ∷
  cleanupStep child₀ C.publishCleanupMap ∷ cleanupStep child₀ C.readCleanupCounters ∷ []
cleanup-covered : Interference cleanupActions
cleanup-covered = more exit (more cleanup (more cleanup (more cleanup (more cleanup (more cleanup empty)))))
cleanup-path : Executes Caller.waiting cleanupActions cleaned
cleanup-path = next {c₁ = exited} refl (next {c₁ = takenMap} refl (next {c₁ = selected} refl
  (next {c₁ = socketClosed} refl (next {c₁ = mapPublished} refl (next refl done)))))
cleaned-prepared : Prepared child₀ (ident 0) G.mid (world cleaned) (inboundGovernor cleaned)
cleaned-prepared = prepared-exec cleanup-covered cleanup-path Caller.waiting-prepared
cleaned-resources : Resources child₀ (world cleaned)
cleaned-resources = resources-exec cleanup-covered cleanup-path (Prepared.resources Caller.waiting-prepared)
cleanup-csp : Process Caller.waiting ⟹⟨ map label cleanupActions ⟩ Process cleaned
cleanup-csp = exec-intro cleanup-path
cleaned-socket : lookup (ident 0) (sockets (world cleaned)) ≡ just closed
cleaned-socket = refl
cleaned-map : mapCell (cm (world cleaned)) ≡ full []
cleaned-map = refl
untracked-throughout-end : handlerLifecycles cleaned ≡ []
untracked-throughout-end = refl

-- A local queued-shutdown fixture; the source of that command is not modeled
-- by this witness. Commands may change without changing the mux key.
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Properties.CleanupRetention as Retention
open import ConnectionManagement.Properties.HandlerAnchors using (setMux-preserves)
stopMux stoppingMux stoppedMux : M.Mux
stopMux = record Runtime.runningMux { commands = M.shutdown ∷ [] }
stoppingMux = record stopMux { commands = []; status = M.stopping }
stoppedMux = record stoppingMux { status = M.stopped; runningJobs = []; callback = M.readActive M.muxStopped }
stopInput stoppingState stoppedState : Configuration
stopInput = record Runtime.jobRunning { inboundGovernor = IG.setMux G.mid stopMux (inboundGovernor Runtime.jobRunning) }
stoppingState = record Runtime.jobRunning { inboundGovernor = IG.setMux G.mid stoppingMux (inboundGovernor Runtime.jobRunning) }
stoppedState = record Runtime.jobRunning { inboundGovernor = IG.setMux G.mid stoppedMux (inboundGovernor Runtime.jobRunning) }
stopInput-prepared : Prepared child₀ (ident 0) G.mid (world stopInput) (inboundGovernor stopInput)
stopInput-prepared = prepared-retained (Retention.retains refl refl (λ _ p → p) (λ _ p → p))
  (setMux-preserves G.mid Runtime.runningMux stopMux (inboundGovernor Runtime.jobRunning) refl refl) running-prepared
stopActions : List Action
stopActions = igStep (IG.monitorCommand G.mid) ∷ igStep (IG.finishStop G.mid) ∷ []
stop-covered : Interference stopActions
stop-covered = more (mux Mux.command) (more (mux Mux.stopped) empty)
stop-path : Executes stopInput stopActions stoppedState
stop-path = next {c₁ = stoppingState} refl (next refl done)
stopped-prepared : Prepared child₀ (ident 0) G.mid (world stoppedState) (inboundGovernor stoppedState)
stopped-prepared = prepared-exec stop-covered stop-path stopInput-prepared
stop-csp : Process stopInput ⟹⟨ map label stopActions ⟩ Process stoppedState
stop-csp = exec-intro stop-path

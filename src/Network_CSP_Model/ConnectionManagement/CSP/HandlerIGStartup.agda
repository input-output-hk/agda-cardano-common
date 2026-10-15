{-# OPTIONS --guardedness #-}

-- Tracked startup/restart witnesses, including partial failure and stop request.
module ConnectionManagement.CSP.HandlerIGStartup where

open import Data.List using (List; map; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement
open import ConnectionManagement.Properties.HandlerIGStartup using (start; restart; failedStop)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked)
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.IGRuntime as Runtime
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

beforeStart afterStart beforeFailure afterFailure afterStop : Configuration
beforeStart = tracked L.monitoring G.prepared
afterStart = tracked L.monitoring G.registered
beforeFailure = tracked L.monitoring Runtime.failureInput
afterFailure = tracked L.monitoring Runtime.failedStart
afterStop = tracked L.monitoring Runtime.stopRequested
start-chain : TrackedChain child₀ beforeStart
start-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
failure-chain : TrackedChain child₀ beforeFailure
failure-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
start-path : Executes beforeStart (igStep IG.runResponders ∷ []) afterStart
start-path = next refl done
started-chain : TrackedChain child₀ afterStart
started-chain = exec-preserves (igStartup start empty) start-path child₀ start-chain
start-csp : Process beforeStart ⟹⟨ map label (igStep IG.runResponders ∷ []) ⟩ Process afterStart
start-csp = exec-intro start-path
failureActions : List Action
failureActions = igStep IG.runResponders ∷ igStep IG.requestFailedStop ∷ []
failure-path : Executes beforeFailure failureActions afterStop
failure-path = next {c₁ = afterFailure} refl (next refl done)
stop-requested-chain : TrackedChain child₀ afterStop
stop-requested-chain = exec-preserves (igStartup start (igStartup failedStop empty)) failure-path child₀ failure-chain
failure-csp : Process beforeFailure ⟹⟨ map label failureActions ⟩ Process afterStop
failure-csp = exec-intro failure-path

-- Local post-completion fixture. No assertion of a full preceding job trace.
completed : Terminated
completed = terminatedProtocol key₀ G.mid G.proto duplex clean
restartInput restartOutput restartFailure restartFailed : Configuration
restartInput = tracked L.monitoring (record G.registered { inboundGovernor =
  IG.setPC (IG.restartResponder 20 [] completed) (IG.setMux G.mid G.newMux (inboundGovernor G.registered)) })
restartOutput = tracked L.monitoring (record G.registered { inboundGovernor =
  IG.setPC (IG.readNext 20 []) (IG.setMux G.mid G.armedMux (inboundGovernor G.registered)) })
restartFailure = tracked L.monitoring (record G.registered { inboundGovernor =
  IG.setPC (IG.restartResponder 20 [] completed) (inboundGovernor G.registered) })
restartFailed = tracked L.monitoring (record G.registered { inboundGovernor =
  IG.setPC (IG.stopAfterFailure 20 [] G.mid 1 M.alreadyRunning) (inboundGovernor G.registered) })
restart-chain : TrackedChain child₀ restartInput
restart-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
restart-failure-chain : TrackedChain child₀ restartFailure
restart-failure-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
restart-path : Executes restartInput (igStep IG.restart ∷ []) restartOutput
restart-path = next refl done
restart-failure-path : Executes restartFailure (igStep IG.restart ∷ []) restartFailed
restart-failure-path = next refl done
restarted-chain : TrackedChain child₀ restartOutput
restarted-chain = exec-preserves (igStartup restart empty) restart-path child₀ restart-chain
restart-failed-chain : TrackedChain child₀ restartFailed
restart-failed-chain = exec-preserves (igStartup restart empty) restart-failure-path child₀ restart-failure-chain
restart-csp : Process restartInput ⟹⟨ map label (igStep IG.restart ∷ []) ⟩ Process restartOutput
restart-csp = exec-intro restart-path
restart-failure-csp : Process restartFailure ⟹⟨ map label (igStep IG.restart ∷ []) ⟩ Process restartFailed
restart-failure-csp = exec-intro restart-failure-path

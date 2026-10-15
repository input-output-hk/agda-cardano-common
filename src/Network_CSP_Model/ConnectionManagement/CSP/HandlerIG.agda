{-# OPTIONS --guardedness #-}

-- All IG actions participate in raw finite-trace reference preservation.
module ConnectionManagement.CSP.HandlerIG where

open import Data.List using (List; map; []; _∷_)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro)
open import ConnectionManagement.CSP.HandlerManagement using (raw-management-preserves)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked)
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.IGRuntime as Runtime
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- No coverage certificate is required from the caller for an IG action list.
ig-coverage : ∀ as → ManagementActions (map igStep as)
ig-coverage [] = empty
ig-coverage (a ∷ as) = ig (ig-coverage as)
raw-ig-reachability : ∀ {c as P} → Process c ⟹⟨ map label (map igStep as) ⟩ P →
  ∀ q → TrackedChain q c → Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain q c′)
raw-ig-reachability {as = as} = raw-management-preserves (ig-coverage as)

registrationStart registrationEnd : Configuration
registrationStart = tracked L.monitoring G.installed
registrationEnd = tracked L.monitoring G.registered
registration-initial : TrackedChain child₀ registrationStart
registration-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
registrationActions : List IG.IGAction
registrationActions = (IG.captureTime 10) ∷ (IG.registerInactivity) ∷ (IG.selectBatch) ∷ (IG.readEvent) ∷ (IG.registerIdleTimer) ∷ (IG.runResponders) ∷ []
registration-path : Executes registrationStart (map igStep registrationActions) registrationEnd
registration-path = next {c₁ = tracked L.monitoring G.timeRead} refl (next {c₁ = tracked L.monitoring G.timerArmed} refl (next {c₁ = tracked L.monitoring G.drained} refl (next {c₁ = tracked L.monitoring G.eventRead} refl (next {c₁ = tracked L.monitoring G.prepared} refl (next refl done)))))
registration-chain : TrackedChain child₀ registrationEnd
registration-chain = exec-preserves (ig-coverage registrationActions) registration-path child₀ registration-initial
registration-csp : Process registrationStart ⟹⟨ map label (map igStep registrationActions) ⟩ Process registrationEnd
registration-csp = exec-intro registration-path

maturityStart maturityEnd : Configuration
maturityStart = tracked L.monitoring G.registered
maturityEnd = tracked L.monitoring Runtime.m₅
maturity-initial : TrackedChain child₀ maturityStart
maturity-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
maturityActions : List IG.IGAction
maturityActions = (IG.finishBatch) ∷ (IG.captureTime 910) ∷ (IG.registerInactivity) ∷ (IG.selectBatch) ∷ (IG.readEvent) ∷ (IG.commitDecision) ∷ []
maturity-path : Executes maturityStart (map igStep maturityActions) maturityEnd
maturity-path = next {c₁ = tracked L.monitoring Runtime.m₀} refl (next {c₁ = tracked L.monitoring Runtime.m₁} refl (next {c₁ = tracked L.monitoring Runtime.m₂} refl (next {c₁ = tracked L.monitoring Runtime.m₃} refl (next {c₁ = tracked L.monitoring Runtime.m₄} refl (next refl done)))))
maturity-chain : TrackedChain child₀ maturityEnd
maturity-chain = exec-preserves (ig-coverage maturityActions) maturity-path child₀ maturity-initial
maturity-csp : Process maturityStart ⟹⟨ map label (map igStep maturityActions) ⟩ Process maturityEnd
maturity-csp = exec-intro maturity-path

drainStart drainEnd : Configuration
drainStart = tracked L.monitoring Runtime.blocked
drainEnd = tracked L.monitoring Runtime.endCommitted
drain-initial : TrackedChain child₀ drainStart
drain-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
drainActions : List IG.IGAction
drainActions = (IG.selectBatch) ∷ (IG.commitTracer G.mid) ∷ []
drain-path : Executes drainStart (map igStep drainActions) drainEnd
drain-path = next {c₁ = tracked L.monitoring Runtime.drainedWhileBlocked} refl (next refl done)
drain-chain : TrackedChain child₀ drainEnd
drain-chain = exec-preserves (ig-coverage drainActions) drain-path child₀ drain-initial
drain-csp : Process drainStart ⟹⟨ map label (map igStep drainActions) ⟩ Process drainEnd
drain-csp = exec-intro drain-path

exitStart exitEnd : Configuration
exitStart = tracked L.monitoring Runtime.activeSampled
exitEnd = tracked L.monitoring Runtime.afterExitWrite
exit-initial : TrackedChain child₀ exitStart
exit-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
exitActions : List IG.IGAction
exitActions = (IG.deactivateIG) ∷ (IG.flushOnExit) ∷ (IG.commitTracer G.mid) ∷ []
exit-path : Executes exitStart (map igStep exitActions) exitEnd
exit-path = next {c₁ = tracked L.monitoring Runtime.exiting} refl (next {c₁ = tracked L.monitoring Runtime.flushed} refl (next refl done))
exit-chain : TrackedChain child₀ exitEnd
exit-chain = exec-preserves (ig-coverage exitActions) exit-path child₀ exit-initial
exit-csp : Process exitStart ⟹⟨ map label (map igStep exitActions) ⟩ Process exitEnd
exit-csp = exec-intro exit-path

pollStart pollEnd : Configuration
pollStart = tracked L.monitoring Runtime.stoppedWait
pollEnd = tracked L.monitoring Runtime.waitDone
poll-initial : TrackedChain child₀ pollStart
poll-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
pollActions : List IG.IGAction
pollActions = (IG.pollStopped) ∷ []
poll-path : Executes pollStart (map igStep pollActions) pollEnd
poll-path = next refl done
poll-chain : TrackedChain child₀ pollEnd
poll-chain = exec-preserves (ig-coverage pollActions) poll-path child₀ poll-initial
poll-csp : Process pollStart ⟹⟨ map label (map igStep pollActions) ⟩ Process pollEnd
poll-csp = exec-intro poll-path

-- IG deactivation plus flushing does not cancel an already-sampled callback.
exited-inactive : IG.active (IG.execution (inboundGovernor exitEnd)) ≡ false
exited-inactive = refl
post-exit-messages : inboundInfo (world exitEnd) ≡ Runtime.startMessages
post-exit-messages = refl

timerExpired : Configuration
timerExpired = record maturityStart { inboundGovernor = record (inboundGovernor maturityStart)
  { execution = record (IG.execution (inboundGovernor maturityStart))
    { timers = put (ident 1) expired (IG.timers (IG.execution (inboundGovernor maturityStart))) } } }
expiration-path : Executes maturityStart (igStep (IG.expireTimer (ident 1)) ∷ []) timerExpired
expiration-path = next refl done
expiration-chain : TrackedChain child₀ timerExpired
expiration-chain = exec-preserves (ig empty) expiration-path child₀ maturity-initial
expiration-csp : Process maturityStart ⟹⟨ map label (igStep (IG.expireTimer (ident 1)) ∷ []) ⟩ Process timerExpired
expiration-csp = exec-intro expiration-path

{-# OPTIONS --guardedness #-}

-- Unrestricted raw dispatcher traces retain chains that already exist.
module ConnectionManagement.CSP.HandlerAll where

open import Data.List using (List; map; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerAttachment using (CreationPremises)
open import ConnectionManagement.Properties.HandlerManagement
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro)
open import ConnectionManagement.CSP.HandlerManagement using (raw-management-preserves; raw-attachment-management-creates)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked)
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.Fixtures as F
open import ConnectionManagement.Scenarios.Handshake using (success; info)
open import ConnectionManagement.Scenarios.Admission using (w₀; w₁; child₀; child₁; key₁; r₁)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.Handshake as H
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-all-preserves : ∀ {c as P} → Process c ⟹⟨ map label as ⟩ P →
  ∀ q → TrackedChain q c → Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain q c′)
raw-all-preserves {as = as} = raw-management-preserves (all-actions as)

-- Creation is still conditional; only the suffix action restriction is removed.
raw-attachment-all-creates : ∀ {w err c as P} →
  CreationPremises w (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label (handlerStep w (L.attach err) ∷ as) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-attachment-all-creates {as = as} premises =
  raw-attachment-management-creates premises (all-actions as)

-- Local coherent fixture before the first consumer reads its negotiated result.
consumerStart : Configuration
consumerStart = tracked L.monitoring (record F.published { inboundGovernor = inboundGovernor G.installed })
consumer-initial : TrackedChain child₀ consumerStart
consumer-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }

consumer1 consumer2 consumer3 consumer4 consumerEnd : Configuration
consumer1 = tracked L.monitoring (record (F.snapshot F.unneg (full F.binding) (commitHandshake (ident 0) success) (handling child₀) F.resultStore [] []) { inboundGovernor = inboundGovernor G.installed })
consumer2 = tracked L.monitoring (record (F.committed) { inboundGovernor = inboundGovernor G.installed })
consumer3 = tracked L.monitoring (record (F.snapshot F.idle (full F.binding) (notifyInbound info) (handling child₀) F.resultStore [] []) { inboundGovernor = inboundGovernor G.installed })
consumer4 = tracked L.monitoring (record (F.snapshot F.idle (full F.binding) (returnHandshake (connected info)) (handling child₀) F.resultStore (info ∷ []) []) { inboundGovernor = inboundGovernor G.installed })
consumerEnd = tracked L.monitoring (record (G.notified) { inboundGovernor = inboundGovernor G.installed })
consumerActions : List Action
consumerActions = (handshakeStep w₀ H.readResult) ∷ (handshakeStep w₀ H.commitResult) ∷ (handshakeStep w₀ H.readResultCounters) ∷ (handshakeStep w₀ H.enqueueInbound) ∷ (handshakeStep w₀ H.returnResult) ∷ []
consumer-path : Executes consumerStart consumerActions consumerEnd
consumer-path = next {c₁ = consumer1} refl (next {c₁ = consumer2} refl (next {c₁ = consumer3} refl (next {c₁ = consumer4} refl (next refl done))))
consumer-chain : TrackedChain child₀ consumerEnd
consumer-chain = all-exec-preserves consumer-path child₀ consumer-initial
consumer-csp : Process consumerStart ⟹⟨ map label consumerActions ⟩ Process consumerEnd
consumer-csp = exec-intro consumer-path

second1 second2 second3 second4 second5 second6 second7 second8 second9 second10 second11 secondEnd : Configuration
second1 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (count (lease w₁ F.binding))) (admissions (world consumerEnd))
  ; cm = record (cm (world consumerEnd)) { mapCell = taken w₁ } } }
second2 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (prepare (lease w₁ F.binding))) (admissions (world consumerEnd))
  ; cm = record (cm (world consumerEnd)) { mapCell = taken w₁ } } }
second3 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (selectEntry (lease w₁ F.binding) (ident 1))) (admissions (world consumerEnd))
  ; cm = record (cm (world consumerEnd)) { mapCell = taken w₁ }
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2 } }
second4 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (forkHandler (lease w₁ F.binding) (ident 1) (ident 1))) (admissions (world consumerEnd))
  ; cm = cmStore (taken w₁) ((ident 0 , F.idle) ∷ (ident 1 , unnegotiated inbound key₁ child₁) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2 } }
second5 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (publish (lease w₁ F.binding) (ident 1) (ident 1))) (admissions (world consumerEnd))
  ; cm = cmStore (taken w₁) ((ident 0 , F.idle) ∷ (ident 1 , unnegotiated inbound key₁ child₁) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2
  ; handlers = put child₁ (handlerStart (ident 1) (ident 1) (ident 1) key₁) (handlers (world consumerEnd))
  ; sockets = put (ident 1) (handling child₁) (sockets (world consumerEnd)) } }
second6 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (countPublished (ident 1) (ident 1))) (admissions (world consumerEnd))
  ; cm = cmStore (full (insertConnection key₁ (ident 1) F.binding)) ((ident 0 , F.idle) ∷ (ident 1 , unnegotiated inbound key₁ child₁) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2
  ; handlers = put child₁ (handlerStart (ident 1) (ident 1) (ident 1) key₁) (handlers (world consumerEnd))
  ; sockets = put (ident 1) (handling child₁) (sockets (world consumerEnd)) } }
second7 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (awaitHandshake (ident 1) (ident 1))) (admissions (world consumerEnd))
  ; cm = cmStore (full (insertConnection key₁ (ident 1) F.binding)) ((ident 0 , F.idle) ∷ (ident 1 , unnegotiated inbound key₁ child₁) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2
  ; handlers = put child₁ (handlerStart (ident 1) (ident 1) (ident 1) key₁) (handlers (world consumerEnd))
  ; sockets = put (ident 1) (handling child₁) (sockets (world consumerEnd)) } }
second8 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (awaitHandshake (ident 1) (ident 1))) (admissions (world consumerEnd))
  ; cm = cmStore (full (insertConnection key₁ (ident 1) F.binding)) ((ident 0 , F.idle) ∷ (ident 1 , unnegotiated inbound key₁ child₁) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2
  ; handlers = put child₁ (handlerStart (ident 1) (ident 1) (ident 1) key₁) (handlers (world consumerEnd))
  ; sockets = put (ident 1) (handling child₁) (sockets (world consumerEnd))
  ; handshakeResults = put (ident 1) query (handshakeResults (world consumerEnd)) } }
second9 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (commitHandshake (ident 1) query)) (admissions (world consumerEnd))
  ; cm = cmStore (full (insertConnection key₁ (ident 1) F.binding)) ((ident 0 , F.idle) ∷ (ident 1 , unnegotiated inbound key₁ child₁) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2
  ; handlers = put child₁ (handlerStart (ident 1) (ident 1) (ident 1) key₁) (handlers (world consumerEnd))
  ; sockets = put (ident 1) (handling child₁) (sockets (world consumerEnd))
  ; handshakeResults = put (ident 1) query (handshakeResults (world consumerEnd)) } }
second10 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (countHandshake (disconnected handshakeQuery))) (admissions (world consumerEnd))
  ; cm = cmStore (full F.binding) ((ident 0 , F.idle) ∷ (ident 1 , terminated nothing) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2
  ; handlers = put child₁ (handlerStart (ident 1) (ident 1) (ident 1) key₁) (handlers (world consumerEnd))
  ; sockets = put (ident 1) (handling child₁) (sockets (world consumerEnd))
  ; handshakeResults = put (ident 1) query (handshakeResults (world consumerEnd)) } }
second11 = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (returnHandshake (disconnected handshakeQuery))) (admissions (world consumerEnd))
  ; cm = cmStore (full F.binding) ((ident 0 , F.idle) ∷ (ident 1 , terminated nothing) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2
  ; handlers = put child₁ (handlerStart (ident 1) (ident 1) (ident 1) key₁) (handlers (world consumerEnd))
  ; sockets = put (ident 1) (handling child₁) (sockets (world consumerEnd))
  ; handshakeResults = put (ident 1) query (handshakeResults (world consumerEnd)) } }
secondEnd = record consumerEnd { world = record (world consumerEnd)
  { admissions = put w₁ (admissionWorker r₁ (completedHandshake (disconnected handshakeQuery))) (admissions (world consumerEnd))
  ; cm = cmStore (full F.binding) ((ident 0 , F.idle) ∷ (ident 1 , terminated nothing) ∷ []) 2
  ; promises = ident 1 ∷ promises (world consumerEnd)
  ; nextPromise = 2
  ; handlers = put child₁ (handlerStart (ident 1) (ident 1) (ident 1) key₁) (handlers (world consumerEnd))
  ; sockets = put (ident 1) (handling child₁) (sockets (world consumerEnd))
  ; handshakeResults = put (ident 1) query (handshakeResults (world consumerEnd)) } }
secondActions : List Action
secondActions = (admissionStep w₁ S.take) ∷ (admissionStep w₁ S.countLimit) ∷ (admissionStep w₁ S.allocatePromise) ∷ (admissionStep w₁ S.chooseEntry) ∷ (admissionStep w₁ S.fork) ∷ (admissionStep w₁ S.putMapBack) ∷ (admissionStep w₁ S.readCounters) ∷ (handlerPublication child₁ query resultWritten) ∷ (handshakeStep w₁ H.readResult) ∷ (handshakeStep w₁ H.commitResult) ∷ (handshakeStep w₁ H.readResultCounters) ∷ (handshakeStep w₁ H.returnResult) ∷ []
second-path : Executes consumerEnd secondActions secondEnd
second-path = next {c₁ = second1} refl (next {c₁ = second2} refl (next {c₁ = second3} refl (next {c₁ = second4} refl (next {c₁ = second5} refl (next {c₁ = second6} refl (next {c₁ = second7} refl (next {c₁ = second8} refl (next {c₁ = second9} refl (next {c₁ = second10} refl (next {c₁ = second11} refl (next refl done)))))))))))
second-chain : TrackedChain child₀ secondEnd
second-chain = all-exec-preserves second-path child₀ consumer-chain
second-csp : Process consumerEnd ⟹⟨ map label secondActions ⟩ Process secondEnd
second-csp = exec-intro second-path

-- Query removal discards the second binding, not either retained heap object.
second-binding-removed : lookupConnection key₁ (F.binding) ≡ nothing
second-binding-removed = refl
second-map : mapCell (cm (world secondEnd)) ≡ full F.binding
second-map = refl
second-entry-retained : lookup (ident 1) (entries (cm (world secondEnd))) ≡ just (terminated nothing)
second-entry-retained = refl

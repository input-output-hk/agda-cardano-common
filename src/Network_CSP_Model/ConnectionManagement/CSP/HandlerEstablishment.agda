{-# OPTIONS --guardedness #-}

-- Establishment through matched boundaries, then arbitrary dispatcher actions.
module ConnectionManagement.CSP.HandlerEstablishment where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerEstablishment
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement using (all-exec-preserves)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; cancelError)
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; r₀; key₀)
open import ConnectionManagement.Scenarios.Handshake using (success; info)
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- The trace explicitly uses the handler's key and the installed handle ID.
-- No CreationPremises or already-existing chain is supplied by the caller.
raw-establishment : ∀ {w c P} hid mid ps flow err as (r : Resources w (world c)) →
  Process c ⟹⟨ map label
    (igStep (IG.installHandle hid mid (handlerKey (original r)) ps flow) ∷
     handlerPublication w (negotiated hid flow) resultWritten ∷
     handlerStep w (L.attach err) ∷ as) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-establishment {w} {c} hid mid ps flow err as r reach with exec-inv reach
... | c′ , same , next {c₁ = installed} installEq (next {c₁ = published} publishEq (next attached rest)) =
  c′ , same , all-exec-preserves rest w
    (attach-established w err published
      (publication-creates w hid mid flow installed
        (install-prepares hid mid ps flow c r installEq) publishEq) attached)

-- Explicit snapshots avoid normalizing a long chain of computed states.
beforeSelect beforeFork forked installed published attached : Configuration
beforeSelect = F.pre (cmStore (taken w₀) [] 0)
  (selectEntry F.parentLease (ident 0)) (ident 0 ∷ []) 1
beforeFork = F.pre (cmStore (taken w₀) ((ident 0 , F.unneg) ∷ []) 1)
  (forkHandler F.parentLease (ident 0) (ident 0)) (ident 0 ∷ []) 1
forked = F.snapshot F.unneg (taken w₀) (publish F.parentLease (ident 0) (ident 0))
  (handling child₀) [] [] []
installed = record forked { inboundGovernor = inboundGovernor G.installed }
published = record installed { world = record (world installed) { handshakeResults = F.resultStore } }
attached = tracked L.monitoring published

prefix : List Action
prefix = admissionStep w₀ S.take ∷ admissionStep w₀ S.countLimit ∷
  admissionStep w₀ S.allocatePromise ∷ admissionStep w₀ S.chooseEntry ∷ admissionStep w₀ S.fork ∷ []
prefix-path : Executes F.start prefix forked
prefix-path = next {c₁ = takenMap} refl (next {c₁ = prepared} refl
  (next {c₁ = beforeSelect} refl (next {c₁ = beforeFork} refl (next refl done))))
  where
  takenMap = F.pre (cmStore (taken w₀) [] 0) (count F.parentLease) [] 0
  prepared = F.pre (cmStore (taken w₀) [] 0) (prepare F.parentLease) [] 0

-- Resource existence comes from the two actual transitions, not a certificate
-- of the desired final chain. No installed handle or negotiated result yet.
forked-resources : Resources child₀ (world forked)
forked-resources = selection-fork-resources w₀ r₀ F.parentLease (ident 0) beforeSelect
  {c₁ = beforeFork} {c₂ = forked} refl refl refl

-- Admission publication and handshake consumption occur after attachment here.
mapPublished waiting readResult committed counted enqueued completedState : Configuration
mapPublished = tracked L.monitoring (record (F.snapshot F.unneg (full F.binding)
  (countPublished (ident 0) (ident 0)) (handling child₀) F.resultStore [] [])
  { inboundGovernor = inboundGovernor G.installed })
waiting = tracked L.monitoring (record F.published { inboundGovernor = inboundGovernor G.installed })
readResult = tracked L.monitoring (record (F.snapshot F.unneg (full F.binding)
  (commitHandshake (ident 0) success) (handling child₀) F.resultStore [] [])
  { inboundGovernor = inboundGovernor G.installed })
committed = tracked L.monitoring (record F.committed { inboundGovernor = inboundGovernor G.installed })
counted = tracked L.monitoring (record (F.snapshot F.idle (full F.binding)
  (notifyInbound info) (handling child₀) F.resultStore [] []) { inboundGovernor = inboundGovernor G.installed })
enqueued = tracked L.monitoring (record (F.snapshot F.idle (full F.binding)
  (returnHandshake (connected info)) (handling child₀) F.resultStore (info ∷ []) []) { inboundGovernor = inboundGovernor G.installed })
completedState = tracked L.monitoring G.installed

suffix : List Action
suffix = admissionStep w₀ S.putMapBack ∷ admissionStep w₀ S.readCounters ∷
  handshakeStep w₀ H.readResult ∷ handshakeStep w₀ H.commitResult ∷
  handshakeStep w₀ H.readResultCounters ∷ handshakeStep w₀ H.enqueueInbound ∷
  handshakeStep w₀ H.returnResult ∷ []
suffix-path : Executes attached suffix completedState
suffix-path = next {c₁ = mapPublished} refl (next {c₁ = waiting} refl
  (next {c₁ = readResult} refl (next {c₁ = committed} refl (next {c₁ = counted} refl
  (next {c₁ = enqueued} refl (next refl done))))))

establish : List Action
establish = igStep (IG.installHandle (ident 0) G.mid key₀ (G.proto ∷ []) duplex) ∷
  handlerPublication child₀ success resultWritten ∷ handlerStep child₀ (L.attach cancelError) ∷ suffix
establish-path : Executes forked establish completedState
establish-path = next {c₁ = installed} refl (next {c₁ = published} refl
  (next {c₁ = attached} refl suffix-path))
establish-csp : Process forked ⟹⟨ map label establish ⟩ Process completedState
establish-csp = exec-intro establish-path

-- Apply the generic trace theorem to the witnessed path. This is derived
-- creation, rather than refl on the endpoint's resource lookups.
completedState-chain : TrackedChain child₀ completedState
completedState-chain = all-exec-preserves suffix-path child₀
  (attach-established child₀ cancelError published
    (publication-creates child₀ (ident 0) G.mid duplex installed
      (install-prepares (ident 0) G.mid (G.proto ∷ []) duplex forked forked-resources refl) refl) refl)

establishment-reachable : Σ Configuration (λ c′ → Process completedState ≡ Process c′ × TrackedChain child₀ c′)
establishment-reachable = raw-establishment (ident 0) G.mid (G.proto ∷ []) duplex cancelError suffix
  forked-resources establish-csp

whole-csp : Process F.start ⟹⟨ map label (prefix ++ establish) ⟩ Process completedState
whole-csp = exec-intro (exec-append prefix-path establish-path)

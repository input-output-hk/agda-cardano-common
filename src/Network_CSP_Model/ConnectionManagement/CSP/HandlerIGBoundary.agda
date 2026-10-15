{-# OPTIONS --guardedness #-}

-- IG publication removes registration; fresh installation grows reference tables.
module ConnectionManagement.CSP.HandlerIGBoundary where

open import Data.List using (map; []; _∷_)
open import Data.Integer using (+_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement
open import ConnectionManagement.Properties.HandlerIGBoundary using (CoveredIG; decision; install)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro)
open import ConnectionManagement.CSP.HandlerManagement using (r₆; release-end-chain)
open import ConnectionManagement.CSP.HandlerAttachment using (newlyAttached; created-chain)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked)
open import ConnectionManagement.CSP.IGRegistration using (proto)
import ConnectionManagement.CSP.InboundRelease as Release
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀; key₁)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- Extends the previously checked release endpoint through actual publication.
unregistered : Configuration
unregistered = tracked L.poolClosing Release.published
publication-path : Executes r₆ (igStep IG.commitDecision ∷ []) unregistered
publication-path = next refl done
unregistered-chain : TrackedChain child₀ unregistered
unregistered-chain = exec-preserves (igBoundary decision empty) publication-path child₀ release-end-chain
publication-csp : Process r₆ ⟹⟨ map label (igStep IG.commitDecision ∷ []) ⟩ Process unregistered
publication-csp = exec-intro publication-path

-- Allocate unrelated fresh references while the first handler is tracked.
newHandle : HandleId
newHandle = ident 10
newMux : MuxId
newMux = ident 10
installedMux : M.Mux
installedMux = M.muxState key₁ M.ready ((1 , M.idle) ∷ []) [] [] [] [] []
  (just (M.counters (+ 0) (+ 0))) M.returned
installAction : IG.IGAction
installAction = IG.installHandle newHandle newMux key₁ (proto ∷ []) duplex
added : Configuration
added = record newlyAttached { inboundGovernor = record (inboundGovernor newlyAttached)
  { execution = record (IG.execution (inboundGovernor newlyAttached))
    { handles = put newHandle (M.handleState newMux (proto ∷ []) duplex)
        (IG.handles (IG.execution (inboundGovernor newlyAttached)))
    ; muxes = put newMux installedMux (IG.muxes (IG.execution (inboundGovernor newlyAttached))) } } }
installation-path : Executes newlyAttached (igStep installAction ∷ []) added
installation-path = next refl done
old-chain-after-installation : TrackedChain child₀ added
old-chain-after-installation = exec-preserves (igBoundary install empty) installation-path child₀ created-chain
installation-csp : Process newlyAttached ⟹⟨ map label (igStep installAction ∷ []) ⟩ Process added
installation-csp = exec-intro installation-path
new-handle-present : lookup newHandle (IG.handles (IG.execution (inboundGovernor added))) ≡
  just (M.handleState newMux (proto ∷ []) duplex)
new-handle-present = refl
new-mux-present : lookup newMux (IG.muxes (IG.execution (inboundGovernor added))) ≡ just installedMux
new-mux-present = refl

registration-removed : lookup key₀ (IG.connections (IG.publishedState (inboundGovernor unregistered))) ≡ nothing
registration-removed = refl

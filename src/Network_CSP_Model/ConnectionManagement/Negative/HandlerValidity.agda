{-# OPTIONS --guardedness #-}

-- Mutated snapshots test the validator, not the reachability of source defects.
module ConnectionManagement.Negative.HandlerValidity where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; withMux; cancelError)
open import ConnectionManagement.CSP.HandlerOutcomes using (s₀; s₁₀; peerCleanup; err)
open import ConnectionManagement.CSP.IGRegistration using (mid)
open import ConnectionManagement.CSP.IGRuntime using (jobRunning; runningMux)
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀; key₁)
import ConnectionManagement.CSP.InboundRelease as Release
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Properties.HandlerValidity as V

missingHandler wrongCapture duplicated prematureCleanup unjoined wrongError : Configuration
missingHandler = record s₀ { world = record (world s₀) { handlers = [] } }
wrongCapture = record s₀ { handlerLifecycles = (child₀ , L.frame (ident 99) cancelError L.monitoring) ∷ [] }
duplicated = record s₀ { handlerLifecycles = handlerLifecycles s₀ ++ handlerLifecycles s₀ }
prematureCleanup = record s₀ { world = record (world s₀) { cleanups = (child₀ , cleanupAcquire) ∷ [] } }
unjoined = withMux (L.syncClosed err) (record runningMux { status = M.failed err }) s₀
wrongError = tracked (L.syncClosed (errorId 999)) s₁₀
missing-handler-rejected : V.valid missingHandler ≡ false
missing-handler-rejected = refl
wrong-capture-rejected : V.valid wrongCapture ≡ false
wrong-capture-rejected = refl
duplicate-owner-rejected : V.valid duplicated ≡ false
duplicate-owner-rejected = refl
premature-cleanup-rejected : V.valid prematureCleanup ≡ false
premature-cleanup-rejected = refl
unjoined-pool-rejected : V.valid unjoined ≡ false
unjoined-pool-rejected = refl
wrong-error-rejected : V.valid wrongError ≡ false
wrong-error-rejected = refl
wrong-key-rejected : V.valid (withMux L.monitoring (record runningMux { key = key₁ }) s₀) ≡ false
wrong-key-rejected = refl
missing-promise-rejected : V.valid (record s₀ { world = record (world s₀) { handshakeResults = [] } }) ≡ false
missing-promise-rejected = refl
finalizing-without-cleanup-rejected : V.valid (record peerCleanup { world = record (world peerCleanup) { cleanups = [] } }) ≡ false
finalizing-without-cleanup-rejected = refl

-- Tracking coverage is separate from validity of already-tracked frames.
untracked-is-not-covered : V.fullyTracked jobRunning ≡ false
untracked-is-not-covered = refl
-- Current entry replacement must not invalidate the original captured owner.
replacement-retains-capture : V.fullyTracked
  (Release.replaceEntry (inboundIdle key₀ (ident 99) (ident 99) duplex) s₀) ≡ true
replacement-retains-capture = refl

shared-mux-rejected : V.uniqueOwners
  ((child₀ , L.frame mid cancelError L.monitoring) ∷
   (ident 99 , L.frame mid cancelError L.monitoring) ∷ []) ≡ false
shared-mux-rejected = refl
missing-socket-rejected : V.valid (record s₀ { world = record (world s₀) { sockets = [] } }) ≡ false
missing-socket-rejected = refl
missing-entry-rejected : V.valid (record s₀ { world = record (world s₀)
  { cm = record (cm (world s₀)) { entries = [] } } }) ≡ false
missing-entry-rejected = refl

{-# OPTIONS --guardedness #-}

-- Every implemented dispatcher action preserves existing tracked chains.
-- Earlier coverage constructors remain available for existing clients.
module ConnectionManagement.Properties.HandlerManagement where

open import Data.List using (List; []; _∷_)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain; handler-step-preserves)
open import ConnectionManagement.Properties.HandlerBoundaries using (publication-preserves; exit-preserves)
import ConnectionManagement.Properties.HandlerCleanup as Cleanup
import ConnectionManagement.Properties.HandlerRelease as Release
import ConnectionManagement.Properties.HandlerRemote as Remote
import ConnectionManagement.Properties.HandlerIGBoundary as IG
import ConnectionManagement.Properties.HandlerIGStartup as Startup
import ConnectionManagement.Properties.HandlerIGMux as Mux
import ConnectionManagement.Properties.HandlerIG as AllIG
import ConnectionManagement.Properties.HandlerAdmission as Admission
import ConnectionManagement.Properties.HandlerHandshake as Handshake

data ManagementActions : List Action → Set where
  empty : ManagementActions []
  admission : ∀ {w a as} → ManagementActions as → ManagementActions (admissionStep w a ∷ as)
  handshake : ∀ {w a as} → ManagementActions as → ManagementActions (handshakeStep w a ∷ as)
  lifecycle : ∀ {w a as} → ManagementActions as → ManagementActions (handlerStep w a ∷ as)
  publication : ∀ {w result outcome as} → ManagementActions as → ManagementActions (handlerPublication w result outcome ∷ as)
  exit : ∀ {w as} → ManagementActions as → ManagementActions (handlerExit w ∷ as)
  cleanup : ∀ {w a as} → ManagementActions as → ManagementActions (cleanupStep w a ∷ as)
  release : ∀ {a as} → ManagementActions as → ManagementActions (releaseStep a ∷ as)
  remote : ∀ {a as} → ManagementActions as → ManagementActions (remoteStep a ∷ as)
  igBoundary : ∀ {a as} → IG.CoveredIG a → ManagementActions as → ManagementActions (igStep a ∷ as)
  igStartup : ∀ {a as} → Startup.CoveredStartup a → ManagementActions as → ManagementActions (igStep a ∷ as)
  igMux : ∀ {a as} → Mux.CoveredMux a → ManagementActions as → ManagementActions (igStep a ∷ as)
  ig : ∀ {a as} → ManagementActions as → ManagementActions (igStep a ∷ as)

exec-preserves : ∀ {c as c′} → ManagementActions as → Executes c as c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
exec-preserves empty done q chain = chain
exec-preserves (lifecycle {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (handler-step-preserves w a c eq q chain)
exec-preserves (publication {w} {result} {outcome} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (publication-preserves w result outcome c eq q chain)
exec-preserves (exit {w} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (exit-preserves w c eq q chain)
exec-preserves (cleanup {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (Cleanup.step-preserves w a c eq q chain)
exec-preserves (release {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (Release.step-preserves a c eq q chain)
exec-preserves (remote {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (Remote.step-preserves a c eq q chain)
exec-preserves (igBoundary {a} covered only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (IG.step-preserves a covered c eq q chain)
exec-preserves (igStartup {a} covered only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (Startup.step-preserves a covered c eq q chain)
exec-preserves (igMux {a} covered only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (Mux.step-preserves a covered c eq q chain)
exec-preserves (ig {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (AllIG.step-preserves a c eq q chain)

exec-preserves (admission {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (Admission.step-preserves w a c eq q chain)
exec-preserves (handshake {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (Handshake.step-preserves w a c eq q chain)

-- Exhaustive action-list coverage makes the former restriction unnecessary.
all-actions : ∀ as → ManagementActions as
all-actions [] = empty
all-actions (admissionStep w a ∷ as) = admission (all-actions as)
all-actions (handshakeStep w a ∷ as) = handshake (all-actions as)
all-actions (cleanupStep w a ∷ as) = cleanup (all-actions as)
all-actions (handlerPublication w r o ∷ as) = publication (all-actions as)
all-actions (handlerExit w ∷ as) = exit (all-actions as)
all-actions (handlerStep w a ∷ as) = lifecycle (all-actions as)
all-actions (igStep a ∷ as) = ig (all-actions as)
all-actions (remoteStep a ∷ as) = remote (all-actions as)
all-actions (releaseStep a ∷ as) = release (all-actions as)

all-exec-preserves : ∀ {c as c′} → Executes c as c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
all-exec-preserves {as = as} = exec-preserves (all-actions as)

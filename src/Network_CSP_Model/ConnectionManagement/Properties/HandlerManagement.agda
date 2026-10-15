{-# OPTIONS --guardedness #-}

-- Every IG action is covered. Admission and handshake-consumer steps remain
-- outside this reference-chain theorem. Earlier coverage constructors are kept.
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

data ManagementActions : List Action → Set where
  empty : ManagementActions []
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

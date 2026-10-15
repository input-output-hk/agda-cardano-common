{-# OPTIONS --guardedness #-}

-- Preserved pre-attachment evidence does not establish progress or readiness.
module ConnectionManagement.Negative.HandlerInterference where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerEstablishment using (Prepared)
open import ConnectionManagement.Properties.HandlerInterference using (prepared-effect)
open import ConnectionManagement.Properties.HandlerConsumerEffects using (effect)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro; refused-extension)
open import ConnectionManagement.CSP.HandlerInterference using (waiting; waiting-prepared)
open import ConnectionManagement.CSP.HandlerLifecycle using (cancelError)
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀)
open import ConnectionManagement.Scenarios.Handshake using (success)
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_; traces)

-- A coherent installed pair is not yet a published negotiation result.
empty-result-refused : advance (handshakeStep w₀ H.readResult) waiting ≡ nothing
empty-result-refused = refl
no-empty-result-trace : ¬ traces (Process waiting) (map label (handshakeStep w₀ H.readResult ∷ []))
no-empty-result-trace = refused-extension {as = []} done empty-result-refused
premature-attach-refused : advance (handlerStep child₀ (L.attach cancelError)) waiting ≡ nothing
premature-attach-refused = refl
no-premature-attach : ¬ traces (Process waiting) (map label (handlerStep child₀ (L.attach cancelError) ∷ []))
no-premature-attach = refused-extension {as = []} done premature-attach-refused

-- Handler exit is deliberately outside the new interference alphabet. This
-- concrete step retains Prepared but prevents publication because cleanup began.
exited : Configuration
exited = record waiting { world = record (world waiting)
  { cleanups = put child₀ cleanupAcquire (cleanups (world waiting)) } }
exit-path : Executes waiting (handlerExit child₀ ∷ []) exited
exit-path = next refl done
exit-csp : Process waiting ⟹⟨ map label (handlerExit child₀ ∷ []) ⟩ Process exited
exit-csp = exec-intro exit-path
exited-prepared : Prepared child₀ (ident 0) G.mid (world exited) (inboundGovernor exited)
exited-prepared = prepared-effect (effect refl refl refl (λ _ p → p)) waiting-prepared
publication-after-exit-refused : advance (handlerPublication child₀ success resultWritten) exited ≡ nothing
publication-after-exit-refused = refl
no-publication-after-exit : ¬ traces (Process waiting)
  (map label (handlerExit child₀ ∷ handlerPublication child₀ success resultWritten ∷ []))
no-publication-after-exit = refused-extension exit-path publication-after-exit-refused

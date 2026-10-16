{-# OPTIONS --guardedness #-}

-- Refusals after prefixes reachable from the accepted-socket initial fixture.
module ConnectionManagement.Negative.RegistryShutdown where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch)
import ConnectionManagement.Rules.InboundRelease as R
open import ConnectionManagement.Properties.RegistryPublication using (publication)
open import ConnectionManagement.Properties.RegistryAttachment using (attachment)
open import ConnectionManagement.Properties.RegistryUnique using (Unique; reachable-unique)
open import ConnectionManagement.CSP.OriginRegistry using (Process; refused-extension)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryShutdown
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.CSP.Fixtures as F
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)
import ConnectionManagement.Negative.RegistryCleanup

-- Cancellation delivery alone does not complete the handler's unwind.
delivered-prefix : List Action
delivered-prefix = prefix ++ (publication child₀ (ident 0) duplex ∷
  (waiting ++ (attachment child₀ Life.cancelError ∷ dispatch (Open.releaseStep (R.cancellationDelivered child₀)) ∷ [])))
delivered-path : Executes (start F.start) delivered-prefix (wrap Life.received)
delivered-path = append-path prefix-path (next {s₁ = wrap E.published} refl
  (append-path waiting-path (next {s₁ = wrap Life.attached} refl (next refl done))))
exit-refused : step (dispatch (Open.handlerExit child₀)) (wrap Life.received) ≡ nothing
exit-refused = refl
no-premature-exit : ¬ traces (Process (start F.start))
  (map label (delivered-prefix ++ (dispatch (Open.handlerExit child₀) ∷ [])))
no-premature-exit = refused-extension delivered-path exit-refused

reattach-refused : step (attachment child₀ Life.cancelError) (wrap Life.doneCleanup) ≡ nothing
reattach-refused = refl
no-reattachment-after-shutdown : ¬ traces (Process (start F.start))
  (map label (schedule ++ (attachment child₀ Life.cancelError ∷ [])))
no-reattachment-after-shutdown = refused-extension path reattach-refused

-- These now describe the endpoint of the full start-to-cleanup registry trace.
final-unique : Unique (entries (wrap Life.doneCleanup))
final-unique = reachable-unique path
final-socket : lookup (ident 0) (S.sockets (Open.world (machine (wrap Life.doneCleanup)))) ≡ just S.closed
final-socket = refl
final-map : S.mapCell (S.cm (Open.world (machine (wrap Life.doneCleanup)))) ≡ S.full []
final-map = refl
final-cleanup : lookup child₀ (S.cleanups (Open.world (machine (wrap Life.doneCleanup)))) ≡ just (S.cleanupDone S.cleanupNormal)
final-cleanup = refl

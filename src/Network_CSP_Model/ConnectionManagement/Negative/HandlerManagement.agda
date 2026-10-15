{-# OPTIONS --guardedness #-}

-- Failed batches have no endpoint; tracked cancellation retains its guards.
module ConnectionManagement.Negative.HandlerManagement where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Integer using (+_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerManagement using (r₃; multiStart)
open import ConnectionManagement.CSP.HandlerLifecycle using (pAttached; pRequested)
open import ConnectionManagement.Scenarios.Admission using (w₀)
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.RemoteState as RS
import ConnectionManagement.Rules.Pruning as P
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

failed-batch-no-endpoint : P.applyEdits
  ((ident 0 , terminated nothing) ∷ (ident 99 , terminated nothing) ∷ []) (world multiStart) ≡ nothing
failed-batch-no-endpoint = refl
wrong-release-target : advance (releaseStep (R.cancellationDelivered w₀)) r₃ ≡ nothing
wrong-release-target = refl
wrong-prune-target : advance (remoteStep (RS.pruneCancellationDelivered w₀)) pRequested ≡ nothing
wrong-prune-target = refl
no-pruning-replay : advance (remoteStep (RS.transactPruning 0 (+ 0 ∷ []))) pAttached ≡ nothing
no-pruning-replay = refl

no-wrong-release-trace : ¬ traces (Process r₃) (map label (releaseStep (R.cancellationDelivered w₀) ∷ []))
no-wrong-release-trace = refused-extension {as = []} done wrong-release-target
no-wrong-prune-trace : ¬ traces (Process pRequested) (map label (remoteStep (RS.pruneCancellationDelivered w₀) ∷ []))
no-wrong-prune-trace = refused-extension {as = []} done wrong-prune-target
no-pruning-replay-trace : ¬ traces (Process pAttached) (map label (remoteStep (RS.transactPruning 0 (+ 0 ∷ [])) ∷ []))
no-pruning-replay-trace = refused-extension {as = []} done no-pruning-replay

{-# OPTIONS --guardedness #-}

-- Retained preparation does not bypass cancellation, assertion or score guards.
module ConnectionManagement.Negative.HandlerGovernorInterference where

open import Data.List using (map; []; _∷_)
open import Data.Integer using (+_)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerGovernorInterference
import ConnectionManagement.CSP.InboundRelease as Release
import ConnectionManagement.CSP.RemoteState as Remote
import ConnectionManagement.CSP.Pruning as Prune
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.RemoteState as RS
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Pending cancellation must be delivered before release can return.
no-premature-release : ¬ traces (Process Release.requested)
  (map label (releaseStep R.returnToIG ∷ []))
no-premature-release = refused-extension {as = []} done Release.premature-return-refused
-- Self-pruning retained preparation, but the assertion phase still intervenes.
no-premature-prune-return : ¬ traces (Process Remote.p₁)
  (map label (remoteStep RS.returnToIG ∷ []))
no-premature-prune-return = refused-extension {as = []} done Remote.pruning-cannot-return
-- A scored transaction cannot be repeated using the preceding generation.
stale-pruning-refused : advance (remoteStep (RS.transactPruning 0 Prune.draws))
  (record Prune.multi { pruningGeneration = 1 }) ≡ nothing
stale-pruning-refused = refl
no-stale-pruning : ¬ traces (Process (record Prune.multi { pruningGeneration = 1 }))
  (map label (remoteStep (RS.transactPruning 0 Prune.draws) ∷ []))
no-stale-pruning = refused-extension {as = []} done stale-pruning-refused

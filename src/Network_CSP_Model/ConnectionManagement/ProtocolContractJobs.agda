{-# OPTIONS --guardedness #-}

-- A conditional protocol-body adapter to actual typed mux jobs. Bindings name
-- captured physical JobIds; numbers 2/3 and directions are checked on every use.
-- No raw body-result input is exported through this interface.
module ConnectionManagement.ProtocolContractJobs where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (does)
open import Class.DecEq using (_≟_)
open import Class.DecEq.Instances using (DecEq-ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (JobId)
import ConnectionManagement.ProtocolContracts as C
import ConnectionManagement.MuxProtocolJobs as W
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.MuxRuntime as M

number : C.Endpoint → ℕ
number C.chainClient = 2
number C.chainServer = 2
number C.fetchClient = 3
number C.fetchServer = 3
direction : C.Endpoint → M.JobDirection
direction C.chainClient = M.initiatorJob
direction C.fetchClient = M.initiatorJob
direction C.chainServer = M.responderJob
direction C.fetchServer = M.responderJob

-- Source instance contract: all four bindings belong to one captured connection
-- incarnation, are distinct and remain fixed. Rebinding after fork is excluded.
record State : Set where
  constructor attached
  field physical : W.State
        lifecycle : C.State
open State public

matches : C.Endpoint → JobId → W.State → Bool
matches ep j s with W.collector j s
... | nothing = false
... | just job = does (T.protocolNumber job ≟ number ep) ∧
  W.sameDirection (T.direction job) (direction ep)

-- Common body boundary used by both introduction and refusal controls. The
-- normal path still goes through the existing wanton/egress and pool guards.
completion : C.Phase → JobId → Maybe W.Action
completion (C.finished C.normal) j = just (W.protocolReturned j)
completion (C.finished (C.synchronous e)) j = just (W.protocolException j e)
completion _ _ = nothing
complete : C.Endpoint → JobId → State → Maybe State
complete ep j s with matches ep j (physical s) | completion (C.at ep (lifecycle s)) j
... | true | just action with W.step action (physical s)
...   | just next = just (record s { physical = next })
...   | nothing = nothing
complete ep j s | _ | _ = nothing

-- A successful boundary really executes the generic job operation. Async
-- cancellation has no successful completion action and cannot become Left e.
completion-sound : ∀ p j a → completion p j ≡ just a →
  (p ≡ C.finished C.normal → a ≡ W.protocolReturned j)
completion-sound (C.finished C.normal) j .(W.protocolReturned j) refl refl = refl
completion-sound (C.finished (C.synchronous e)) j .(W.protocolException j e) refl ()

-- Acquisition and body observations require the exact live physical child.
-- Registry environmental inputs are independent, shared per captured peer.
observe : C.Action → State → Maybe State
observe a s with C.step a (lifecycle s)
... | nothing = nothing
... | just next = just (record s { lifecycle = next })
observeBody : C.Endpoint → JobId → C.Action → State → Maybe State
observeBody ep j a s with matches ep j (physical s)
... | false = nothing
... | true = observe a s

-- This module exports body adapters rather than a replacement full dispatcher.
-- No source CM release, demotion, mux stop or handler exit is synthesized here.

-- The public dispatcher selects the required endpoint itself, so callers cannot
-- validate one child while advancing another child's bracket.
required : (C.Endpoint → JobId) → C.Action → W.State → Bool
required bind C.contextReady s = true
required bind C.keepAliveReady s = true
required bind C.keepAliveDying s = true
required bind C.registerSync s = matches C.chainClient (bind C.chainClient) s
required bind C.registerFetch s = matches C.fetchClient (bind C.fetchClient) s
required bind C.rendezvous s = matches C.chainClient (bind C.chainClient) s ∧ matches C.fetchClient (bind C.fetchClient) s
required bind C.enterCandidate s = matches C.chainClient (bind C.chainClient) s
required bind (C.acquireServer ep) s = matches ep (bind ep) s
required bind (C.await ep _) s = matches ep (bind ep) s
required bind (C.ready ep) s = matches ep (bind ep) s
required bind (C.terminate ep _) s = matches ep (bind ep) s
required bind (C.chainUninteresting _) s = matches C.chainClient (bind C.chainClient) s
required bind (C.collect ep) s = matches ep (bind ep) s
required bind (C.peerDone ep) s = matches ep (bind ep) s
required bind (C.bodyError ep _) s = matches ep (bind ep) s
required bind (C.asyncReceipt ep) s = matches ep (bind ep) s
required bind C.removeCandidate s = matches C.chainClient (bind C.chainClient) s
required bind C.signalSyncDone s = matches C.chainClient (bind C.chainClient) s
required bind C.removeFetch s = matches C.fetchClient (bind C.fetchClient) s
required bind (C.serverCleanup ep) s = matches ep (bind ep) s
required bind (C.cleanupFailure ep _) s = matches ep (bind ep) s
required bind C.fetchCleanupInterrupted s = matches C.fetchClient (bind C.fetchClient) s
required bind C.cancelSync s = matches C.chainClient (bind C.chainClient) s ∧ matches C.fetchClient (bind C.fetchClient) s

data Action : Set where
  event : C.Action → Action
  finishBody : C.Endpoint → Action
step : (C.Endpoint → JobId) → Action → State → Maybe State
step bind (event a) s with required bind a (physical s)
... | false = nothing
... | true = observe a s
step bind (finishBody ep) s = complete ep (bind ep) s

-- Both directions of the actual generic-step boundary, without normalising a
-- composed system or asserting that a configured initialized profile exists.
complete-via : ∀ ep j s {t} → complete ep j s ≡ just t →
  Σ W.Action (λ a → completion (C.at ep (lifecycle s)) j ≡ just a ×
    W.step a (physical s) ≡ just (physical t))
complete-via ep j s eq with matches ep j (physical s) | completion (C.at ep (lifecycle s)) j in selected
... | true | just a with W.step a (physical s) in advanced
...   | just next with eq
...     | refl = a , refl , advanced

complete-enabled : ∀ ep j s next a → matches ep j (physical s) ≡ true →
  completion (C.at ep (lifecycle s)) j ≡ just a → W.step a (physical s) ≡ just next →
  complete ep j s ≡ just (record s { physical = next })
complete-enabled ep j s next a matched selected advanced rewrite matched | selected | advanced = refl

{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through the catch and publication unwind layers: their own
-- observations enact local or transfer plans of startup unwinding.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysPublication (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.MuxPublicationUnwind as Publication
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysUnwind as UnwindKeys
import ConnectionManagement.Properties.SourceKeysDelta as DeltaKeys
private
  module N = Publication isBearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module W = N.W
  module P = N.P
  module U = N.U
  module S = N.S
  module Pool = N.Pool
  module Unwind = UnwindKeys isBearerClosed
  module Delta = DeltaKeys isBearerClosed

-- C: catch unwind.
rootC : C.Action → Maybe O.Action
rootC (C.run a) = Delta.rootD a
rootC _ = nothing
catch-select-root : ∀ w reason s {p} → C.select w reason s ≡ just p → Unwind.planRoot (C.action p) ≡ nothing
catch-select-root w reason s eq with lookup w (R.faults (D.base (C.base s))) | Pool.phase (C.poolAt w s) | lookup w (W.exits (R.base (D.base (C.base s))))
... | just f | Pool.closedPool | nothing with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols (D.base (C.base s)))
...   | R.asyncDead | R.async old | just m with D.M.finishMatches (D.M.failed old) (Mux.status m) | C.canObserve reason m s
...     | true | true = case just-injective eq of λ { refl → refl }
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.asyncDead | R.async old | just m | true | false = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.asyncDead | R.async old | just m | false | _ = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.readyBody | _ | _ = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.readyBuffer | _ | _ = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.awaitingClose | _ | _ = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.closing | _ | _ = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.poolClosed | _ | _ = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.asyncStatus | _ | _ = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.asyncDead | R.sync _ | _ = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.asyncDead | R.async _ | nothing = case eq of λ ()
catch-select-root w reason s eq | just f | Pool.closedPool | nothing | R.handedOff | _ | _ = case eq of λ ()
catch-select-root w reason s eq | nothing | _ | _ = case eq of λ ()
catch-select-root w reason s eq | just _ | Pool.openPool | _ = case eq of λ ()
catch-select-root w reason s eq | just _ | Pool.closing | _ = case eq of λ ()
catch-select-root w reason s eq | just _ | Pool.closedPool | just _ = case eq of λ ()
catch-select-root w reason s eq | just _ | Pool.cancelPending _ | _ = case eq of λ ()
catch-select-root w reason s eq | just _ | Pool.joinPending _ | _ = case eq of λ ()
catch-apply-keys : ∀ w p b s {s′} → Unwind.planRoot (C.action p) ≡ nothing → C.apply w p b s ≡ just s′ →
  KeySame (C.source s) (C.source s′)
catch-apply-keys w p b s rooted eq with R.enact (D.delivery b (C.action p)) (D.base (C.base s)) in enacted
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → Delta.nil _ (trans (Delta.delivery-root b (C.action p)) rooted)
  (Unwind.enact-keys (D.delivery b (C.action p)) (D.base (C.base s)) enacted) }
catch-observe-keys : ∀ w reason b s {s′} → C.observe w reason b s ≡ just s′ → KeySame (C.source s) (C.source s′)
catch-observe-keys w reason b s eq with C.select w reason s in selected
... | nothing = case eq of λ ()
... | just p = catch-apply-keys w p b s (catch-select-root w reason s selected) eq
step-keysC : ∀ a s {s′} → C.step a s ≡ just s′ → Effect (rootC a) (C.source s) (C.source s′)
step-keysC (C.run a) s eq with C.allowed a
... | false = case eq of λ ()
... | true with D.step a (C.base s) in stepped
...   | nothing = case eq of λ ()
...   | just d = case just-injective eq of λ { refl → Delta.step-keysD a (C.base s) stepped }
step-keysC (C.observeException w err) s eq = catch-observe-keys w _ false s eq
step-keysC (C.observeCancellation w site err) s eq = catch-observe-keys w _ false s eq
step-keysC (C.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (D.base (C.base s))))
... | Close.awaitDelivery _ w = catch-observe-keys w _ true s eq
step-keysC (C.deliverShutdown site err) s eq | Close.initial = case eq of λ ()
step-keysC (C.deliverShutdown site err) s eq | Close.reading = case eq of λ ()
step-keysC (C.deliverShutdown site err) s eq | Close.awaitResults = case eq of λ ()
step-keysC (C.deliverShutdown site err) s eq | Close.closed = case eq of λ ()
step-keysC (C.deliverShutdown site err) s eq | Close.sendReady _ _ = case eq of λ ()

-- N: publication unwind.
rootN : N.Action → Maybe O.Action
rootN (N.run a) = rootC a
rootN _ = nothing
publication-select-root : ∀ w at result s {p} → N.select w at result s ≡ just p → Unwind.planRoot (N.action p) ≡ nothing
publication-select-root w at result s eq with lookup w (N.failures s) | R.owner w (N.raw s) | lookup w (W.exits (R.base (N.raw s))) | lookup w (R.faults (N.raw s))
... | nothing | just f | nothing | nothing with N.siteReady at f (N.source s) | N.deliveryReady at result | S.phase (U.startup f) | Pool.handles (N.poolAt w s)
...   | true | true | S.awaitPublication | [] with lookup w (Shared.handlers (Machine.world (O.core (N.source s)))) |
    lookup (Shared.handlerPromise (U.captured f)) (Shared.handshakeResults (Machine.world (O.core (N.source s))))
...     | just actual | nothing with W.sameStart (U.captured f) actual
...       | true = case just-injective eq of λ { refl → refl }
...       | false = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.awaitPublication | [] | nothing | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.awaitPublication | [] | just _ | just _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.awaitPublication | _ ∷ _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.published | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.bufferReady | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.bearerReady | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.runEntered | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.startingTraced | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.egressReady | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.poolReady | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.muxerForked _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.muxerRegistered _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.demuxerForked _ _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.demuxerRegistered _ _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.matureTraced _ _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.monitoring _ _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | true | S.configured _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | true | false | _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just f | nothing | nothing | false | _ | _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | nothing | _ | _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just _ | nothing | just _ = case eq of λ ()
publication-select-root w at result s eq | nothing | just _ | just _ | _ = case eq of λ ()
publication-select-root w at result s eq | just _ | _ | _ | _ = case eq of λ ()
publication-apply-keys : ∀ w p b s {s′} → Unwind.planRoot (N.action p) ≡ nothing → N.apply w p b s ≡ just s′ →
  KeySame (N.source s) (N.source s′)
publication-apply-keys w p b s rooted eq with R.enact (D.delivery b (N.action p)) (N.raw s) in enacted
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → Delta.nil _ (trans (Delta.delivery-root b (N.action p)) rooted)
  (Unwind.enact-keys (D.delivery b (N.action p)) (N.raw s) enacted) }
publication-observe-keys : ∀ w at result b s {s′} → N.observe w at result b s ≡ just s′ → KeySame (N.source s) (N.source s′)
publication-observe-keys w at result b s eq with N.select w at result s in selected
... | nothing = case eq of λ ()
... | just p = publication-apply-keys w p b s (publication-select-root w at result s selected) eq
step-keysN : ∀ a s {s′} → N.step a s ≡ just s′ → Effect (rootN a) (N.source s) (N.source s′)
step-keysN (N.run a) s eq with N.allowed a s
... | false = case eq of λ ()
... | true with C.step a (N.base s) in stepped
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → step-keysC a (N.base s) stepped }
step-keysN (N.observeFailure w at result) s eq = publication-observe-keys w at result false s eq
step-keysN (N.deliverShutdown at err) s eq with Close.phase (W.shutdown (R.base (N.raw s)))
... | Close.awaitDelivery _ w = publication-observe-keys w at _ true s eq
step-keysN (N.deliverShutdown at err) s eq | Close.initial = case eq of λ ()
step-keysN (N.deliverShutdown at err) s eq | Close.reading = case eq of λ ()
step-keysN (N.deliverShutdown at err) s eq | Close.awaitResults = case eq of λ ()
step-keysN (N.deliverShutdown at err) s eq | Close.closed = case eq of λ ()
step-keysN (N.deliverShutdown at err) s eq | Close.sendReady _ _ = case eq of λ ()

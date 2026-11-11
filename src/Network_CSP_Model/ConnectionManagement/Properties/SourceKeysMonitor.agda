{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through the mux result monitor: its own actions write the
-- source only by inbound dispatcher steps.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysMonitor (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
import Relation.Nullary
import Class.DecEq
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxResultMonitor as Monitor
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysProtocol as Lower
private
  module L = Monitor isBearerClosed
  module Pool = P.Pool

rootM : L.Action → Maybe O.Action
rootM (L.run a) = Lower.rootP a
rootM _ = nothing
Same : L.State → L.State → Set
Same s s′ = KeySame (L.source s) (L.source s′)

inherit-keys : ∀ a s {s′} → L.inherit a s ≡ just s′ → Effect (Lower.rootP a) (L.source s) (L.source s′)
inherit-keys a s eq with L.delegateAllowed a s
... | false = case eq of λ ()
... | true with P.step a (L.base s) in stepped
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → Lower.step-keysP a (L.base s) stepped }
via-keys : ∀ act s {s′} → L.viaSource act s ≡ just s′ → Same s s′
via-keys act s eq with O.advance (O.inbound (Machine.igStep act)) (L.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → nonkey (O.inbound (Machine.igStep act)) (L.source s) refl advanced }
-- setPC keeps the source.
via-pc-keys : ∀ act w pc s {s′} → L.viaSource act s ≡ just s′ → Same s (L.setPC w pc s′)
via-pc-keys act w pc s eq = via-keys act s eq

select-keys : ∀ w s {s′} → L.selectHead w s ≡ just s′ → Same s s′
select-keys w s eq with L.pcAt w s | L.ownerContext w s
... | L.waiting | just (f , mid) with L.muxAt mid s | P.noParent (L.poolAt w s) | Pool.completions (L.poolAt w s)
...   | just m | true | item ∷ rest with Mux.status m | Mux.callback m
...     | Mux.ready | Mux.returned with Pool.step Pool.consumeCompletion (L.poolAt w s)
...       | nothing = case eq of λ ()
...       | just next = case just-injective eq of λ { refl → same-refl _ }
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.readActive _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.commitTrace _ _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.afterStart _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.forkPending _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.afterFailure = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.tracerFailed _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.stopping | _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.stopped | _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.failed _ | _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | nothing | _ | _ = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just _ | true | [] = case eq of λ ()
select-keys w s eq | L.waiting | just (f , mid) | just _ | false | _ = case eq of λ ()
select-keys w s eq | L.waiting | nothing = case eq of λ ()
select-keys w s eq | L.selected _ | _ = case eq of λ ()
select-keys w s eq | L.responderTracing _ | _ = case eq of λ ()
select-keys w s eq | L.initiatorTracing _ | _ = case eq of λ ()
select-keys w s eq | L.deadReady _ | _ = case eq of λ ()
select-keys w s eq | L.deadTracing _ | _ = case eq of λ ()
select-keys w s eq | L.finished _ | _ = case eq of λ ()

protocol-source-keys : ∀ w mid dir n outcome s {s′} → L.protocolSource w mid dir n outcome s ≡ just s′ → Same s s′
protocol-source-keys w mid Mux.responderJob n outcome s eq with L.muxAt mid s
... | nothing = case eq of λ ()
... | just m with L.legacyMatches n outcome (Mux.completions m)
...   | false = case eq of λ ()
...   | true with L.viaSource (IG.monitorCompletion mid) s in via
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → via-keys (IG.monitorCompletion mid) s via }
protocol-source-keys w mid Mux.initiatorJob n clean s eq = case just-injective eq of λ { refl → same-refl _ }
protocol-source-keys w mid Mux.initiatorJob n (errored err) s eq with L.viaSource (IG.recordMuxFailure mid err) s in via
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → via-keys (IG.recordMuxFailure mid err) s via }
handle-protocol-keys : ∀ w dir n gen outcome s {s′} → L.handleProtocol w dir n gen outcome s ≡ just s′ → Same s s′
handle-protocol-keys w dir n gen outcome s eq with L.ownerContext w s | L.findCaptured w dir n gen outcome (P.jobs (L.base s))
... | just (f , mid) | just (j , job) with Relation.Nullary.does (Types.mux job Class.DecEq.≟ mid) | L.muxAt mid s
...   | true | just m with Mux.status m | Mux.callback m
...     | Mux.ready | Mux.returned = protocol-source-keys w mid dir n outcome s eq
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.readActive _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.commitTrace _ _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.afterStart _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.forkPending _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.afterFailure = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.tracerFailed _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.stopping | _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.stopped | _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.failed _ | _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | nothing = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (f , mid) | just (j , job) | false | _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | nothing | _ = case eq of λ ()
handle-protocol-keys w dir n gen outcome s eq | just (_ , _) | nothing = case eq of λ ()
record-keys : ∀ w outcome s {s′} → L.recordFinish w outcome s ≡ just s′ → Same s s′
record-keys w outcome s eq with L.ownerContext w s
... | nothing = case eq of λ ()
... | just (f , mid) with L.viaSource (L.statusAction outcome mid) s in via
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → via-keys (L.statusAction outcome mid) s via }
handle-keys : ∀ w s {s′} → L.handleHead w s ≡ just s′ → Same s s′
handle-keys w s eq with L.pcAt w s
... | L.selected (Types.protocolCompletion dir n gen outcome) = handle-protocol-keys w dir n gen outcome s eq
... | L.selected (Types.infraMuxer err) = record-keys w (L.failed err) s eq
... | L.selected (Types.infraDemuxer err) = record-keys w (L.demuxFinish w err s) s eq
... | L.waiting = case eq of λ ()
... | L.responderTracing _ = case eq of λ ()
... | L.initiatorTracing _ = case eq of λ ()
... | L.deadReady _ = case eq of λ ()
... | L.deadTracing _ = case eq of λ ()
... | L.finished _ = case eq of λ ()
trace-keys : ∀ sample w s {s′} → L.traceSource sample w s ≡ just s′ → Same s s′
trace-keys sample w s eq with L.tracing (L.pcAt w s) | L.ownerContext w s
... | true | just (f , mid) with sample
...   | true = via-keys (IG.sampleTracer mid) s eq
...   | false = via-keys (IG.commitTracer mid) s eq
trace-keys sample w s eq | true | nothing = case eq of λ ()
trace-keys sample w s eq | false | _ = case eq of λ ()
finish-protocol-keys : ∀ w s {s′} → L.finishProtocol w s ≡ just s′ → Same s s′
finish-protocol-keys w s eq with L.pcAt w s | L.ownerContext w s
... | L.responderTracing clean | just (f , mid) with L.muxAt mid s
...   | just m with Mux.callback m
...     | Mux.returned = case just-injective eq of λ { refl → same-refl _ }
finish-protocol-keys w s eq | L.responderTracing clean | just (f , mid) | just m | Mux.readActive _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing clean | just (f , mid) | just m | Mux.commitTrace _ _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing clean | just (f , mid) | just m | Mux.afterStart _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing clean | just (f , mid) | just m | Mux.forkPending _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing clean | just (f , mid) | just m | Mux.afterFailure = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing clean | just (f , mid) | just m | Mux.tracerFailed _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing clean | just (f , mid) | nothing = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing (errored err) | just (f , mid) with L.muxAt mid s
... | just m with Mux.callback m
...   | Mux.afterFailure = case just-injective eq of λ { refl → same-refl _ }
finish-protocol-keys w s eq | L.responderTracing (errored err) | just (f , mid) | just m | Mux.readActive _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing (errored err) | just (f , mid) | just m | Mux.commitTrace _ _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing (errored err) | just (f , mid) | just m | Mux.afterStart _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing (errored err) | just (f , mid) | just m | Mux.forkPending _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing (errored err) | just (f , mid) | just m | Mux.tracerFailed _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing (errored err) | just (f , mid) | just m | Mux.returned = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
finish-protocol-keys w s eq | L.initiatorTracing outcome | just (f , mid) with L.muxAt mid s
... | just m with Mux.callback m
...   | Mux.returned = case just-injective eq of λ { refl → same-refl _ }
finish-protocol-keys w s eq | L.initiatorTracing outcome | just (f , mid) | just m | Mux.readActive _ = case eq of λ ()
finish-protocol-keys w s eq | L.initiatorTracing outcome | just (f , mid) | just m | Mux.commitTrace _ _ = case eq of λ ()
finish-protocol-keys w s eq | L.initiatorTracing outcome | just (f , mid) | just m | Mux.afterStart _ = case eq of λ ()
finish-protocol-keys w s eq | L.initiatorTracing outcome | just (f , mid) | just m | Mux.forkPending _ = case eq of λ ()
finish-protocol-keys w s eq | L.initiatorTracing outcome | just (f , mid) | just m | Mux.afterFailure = case eq of λ ()
finish-protocol-keys w s eq | L.initiatorTracing outcome | just (f , mid) | just m | Mux.tracerFailed _ = case eq of λ ()
finish-protocol-keys w s eq | L.initiatorTracing outcome | just (f , mid) | nothing = case eq of λ ()
finish-protocol-keys w s eq | L.waiting | _ = case eq of λ ()
finish-protocol-keys w s eq | L.selected _ | _ = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing clean | nothing = case eq of λ ()
finish-protocol-keys w s eq | L.responderTracing (errored _) | nothing = case eq of λ ()
finish-protocol-keys w s eq | L.initiatorTracing _ | nothing = case eq of λ ()
finish-protocol-keys w s eq | L.deadReady _ | _ = case eq of λ ()
finish-protocol-keys w s eq | L.deadTracing _ | _ = case eq of λ ()
finish-protocol-keys w s eq | L.finished _ | _ = case eq of λ ()
start-dead-keys : ∀ w s {s′} → L.startDead w s ≡ just s′ → Same s s′
start-dead-keys w s eq with L.pcAt w s | L.ownerContext w s
... | L.deadReady outcome | just (f , mid) with L.muxAt mid s
...   | just m with L.finishMatches outcome (Mux.status m) | L.deadAction outcome (Mux.callback m) mid
...     | true | just action with L.viaSource action s in via
...       | nothing = case eq of λ ()
...       | just next = case just-injective eq of λ { refl → via-keys action s via }
start-dead-keys w s eq | L.deadReady outcome | just (f , mid) | just m | true | nothing = case eq of λ ()
start-dead-keys w s eq | L.deadReady outcome | just (f , mid) | just m | false | _ = case eq of λ ()
start-dead-keys w s eq | L.deadReady outcome | just (f , mid) | nothing = case eq of λ ()
start-dead-keys w s eq | L.waiting | _ = case eq of λ ()
start-dead-keys w s eq | L.selected _ | _ = case eq of λ ()
start-dead-keys w s eq | L.responderTracing _ | _ = case eq of λ ()
start-dead-keys w s eq | L.initiatorTracing _ | _ = case eq of λ ()
start-dead-keys w s eq | L.deadReady _ | nothing = case eq of λ ()
start-dead-keys w s eq | L.deadTracing _ | _ = case eq of λ ()
start-dead-keys w s eq | L.finished _ | _ = case eq of λ ()
finish-mux-keys : ∀ w s {s′} → L.finishMux w s ≡ just s′ → Same s s′
finish-mux-keys w s eq with L.pcAt w s | L.ownerContext w s
... | L.deadTracing outcome | just (f , mid) with L.muxAt mid s
...   | just m with Mux.callback m | L.finishMatches outcome (Mux.status m)
...     | Mux.returned | true = case just-injective eq of λ { refl → same-refl _ }
finish-mux-keys w s eq | L.deadTracing outcome | just (f , mid) | just m | Mux.readActive _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.deadTracing outcome | just (f , mid) | just m | Mux.commitTrace _ _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.deadTracing outcome | just (f , mid) | just m | Mux.afterStart _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.deadTracing outcome | just (f , mid) | just m | Mux.forkPending _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.deadTracing outcome | just (f , mid) | just m | Mux.afterFailure | _ = case eq of λ ()
finish-mux-keys w s eq | L.deadTracing outcome | just (f , mid) | just m | Mux.tracerFailed _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.deadTracing outcome | just (f , mid) | just m | Mux.returned | false = case eq of λ ()
finish-mux-keys w s eq | L.deadTracing outcome | just (f , mid) | nothing = case eq of λ ()
finish-mux-keys w s eq | L.waiting | _ = case eq of λ ()
finish-mux-keys w s eq | L.selected _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.responderTracing _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.initiatorTracing _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.deadReady _ | _ = case eq of λ ()
finish-mux-keys w s eq | L.deadTracing _ | nothing = case eq of λ ()
finish-mux-keys w s eq | L.finished _ | _ = case eq of λ ()

step-keysM : ∀ a s {s′} → L.step a s ≡ just s′ → Effect (rootM a) (L.source s) (L.source s′)
step-keysM (L.run a) s eq = inherit-keys a s eq
step-keysM (L.consume w) s eq = select-keys w s eq
step-keysM (L.handleSelected w) s eq = handle-keys w s eq
step-keysM (L.sampleTracer w) s eq = trace-keys true w s eq
step-keysM (L.commitTracer w) s eq = trace-keys false w s eq
step-keysM (L.finishProtocolTrace w) s eq = finish-protocol-keys w s eq
step-keysM (L.beginDead w) s eq = start-dead-keys w s eq
step-keysM (L.finishDead w) s eq = finish-mux-keys w s eq

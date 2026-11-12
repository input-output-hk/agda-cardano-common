{-# OPTIONS --guardedness #-}

-- Content facts at the real allocation/publication boundaries. Retention is
-- stated for arbitrary source executions; attachment and live ownership are
-- deliberately absent from the premises.
module ConnectionManagement.Properties.LiveTrackerChainSteps where

open import Data.Bool using (true; false)
import Data.Unit
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import ConnectionManagement.IGTypes using (Protocol)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as R
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Properties.IGTableRetention as Table
import ConnectionManagement.Properties.StateRetention as State
import ConnectionManagement.Properties.OutboundWorldInvariant as World
module U = P.U

-- The whole immutable handle descriptor agrees with the negotiated bundle and
-- flow. Only the mutable mux's key is fixed.
record Anchor (h : S.HandlerStart) (ps : List Protocol)
              (flow : DataFlow) (hid : HandleId) (mid : MuxId) (ig : IG.Runtime) : Set where
 field
  handle-found : lookup hid (IG.handles (IG.execution ig)) ≡ just (R.handleState mid ps flow)
  mux-value : R.Mux
  mux-found : lookup mid (IG.muxes (IG.execution ig)) ≡ just mux-value
  mux-key : R.key mux-value ≡ S.handlerKey h
open Anchor public

-- Retained lookups preserve allocation and all negotiated handle fields.
anchor-retained : ∀ {h ps flow hid mid before after} → Table.Retains before after →
 Anchor h ps flow hid mid before → Anchor h ps flow hid mid after
anchor-retained {mid = mid} retained anchor with Table.muxesRetained retained mid (mux-value anchor) (mux-found anchor)
... | m , found , key = record
 { handle-found = Table.handlesRetained retained _ _ (handle-found anchor)
 ; mux-value = m; mux-found = found; mux-key = trans key (mux-key anchor) }

-- Source allocation has two outbound mode profiles and one inbound profile.
install-initiator : ∀ h ps flow hid mid ig queue {ig′ queue′} →
 IG.installInitiatorWith hid mid (S.handlerKey h) ps flow ig queue ≡ just (ig′ , queue′) → Anchor h ps flow hid mid ig′
install-initiator h ps flow hid mid ig queue eq with lookup hid (IG.handles (IG.execution ig)) |
 lookup mid (IG.muxes (IG.execution ig)) | IG.ordered ps | IG.supported ps
... | nothing | nothing | true | true = case just-injective eq of λ { refl → record
 { handle-found = lookup-put hid _ (IG.handles (IG.execution ig)); mux-value = _
 ; mux-found = lookup-put mid _ (IG.muxes (IG.execution ig)); mux-key = refl } }
... | just _ | _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ | _ = case eq of λ ()
... | nothing | nothing | false | _ = case eq of λ ()
... | nothing | nothing | true | false = case eq of λ ()
install-with : ∀ attachment h ps flow hid mid ig queue {ig′ queue′} →
 IG.installWith attachment hid mid (S.handlerKey h) ps flow ig queue ≡ just (ig′ , queue′) → Anchor h ps flow hid mid ig′
install-with attachment h ps flow hid mid ig queue eq with lookup hid (IG.handles (IG.execution ig)) |
 lookup mid (IG.muxes (IG.execution ig)) | IG.ordered ps | IG.supported ps
... | nothing | nothing | true | true = case just-injective eq of λ { refl → record
 { handle-found = lookup-put hid _ (IG.handles (IG.execution ig)); mux-value = _
 ; mux-found = lookup-put mid _ (IG.muxes (IG.execution ig)); mux-key = refl } }
... | just _ | _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ | _ = case eq of λ ()
... | nothing | nothing | false | _ = case eq of λ ()
... | nothing | nothing | true | false = case eq of λ ()

-- Expose the actual mode-sensitive interpreter, rather than assuming the
-- responder profile for every outbound handler.
install-mode : ∀ mode f hid mid ig queue {ig′ queue′} →
 IG.step mode (U.allocationAction f hid mid) ig queue ≡ just (ig′ , queue′) →
 Anchor (U.captured f) (U.bundle f) (U.flow f) hid mid ig′
install-mode mode f hid mid ig queue eq with U.birthProvenance f
... | inbound with mode
...   | S.noResponderMode = case eq of λ ()
...   | S.responderMode = install-with R.igTracer _ _ _ _ _ ig queue eq
install-mode S.noResponderMode f hid mid ig queue eq | outbound = install-initiator _ _ _ _ _ ig queue eq
install-mode S.responderMode f hid mid ig queue eq | outbound = install-with (IG.outboundTracer S.responderMode (U.flow f)) _ _ _ _ _ ig queue eq

-- Successful Machine allocation establishes its handle and mux content.
allocation : ∀ f hid mid c {c′} →
 M.advance (M.igStep (U.allocationAction f hid mid)) c ≡ just c′ →
 Anchor (U.captured f) (U.bundle f) (U.flow f) hid mid (M.inboundGovernor c′)
allocation f hid mid c eq with Life.allowIG (U.allocationAction f hid mid) (M.handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (M.responder c) (U.allocationAction f hid mid) (M.inboundGovernor c) (S.inboundInfo (M.world c)) in actual
...   | nothing = case eq of λ ()
...   | just (ig , queue) = case just-injective eq of λ { refl → install-mode (M.responder c) f hid mid (M.inboundGovernor c) (S.inboundInfo (M.world c)) actual }

-- Fixed anchor contents survive every outbound source action and finite run.
module FixedAnchor (h : S.HandlerStart) (ps : List Protocol)
                   (flow : DataFlow) (hid : HandleId) (mid : MuxId) where
 Predicate : S.State → IG.Runtime → Set
 Predicate s ig = Anchor h ps flow hid mid ig
 stable : ∀ {s s′ ig ig′} → State.Retains s s′ → Table.Retains ig ig′ → Predicate s ig → Predicate s′ ig′
 stable state tables = anchor-retained tables
 open World.Lift Predicate stable public using (Valid; advance-preserves; exec-preserves)

-- A successful real publication writes the captured owner's original promise.
-- This is a boundary theorem, with no claim that an unpublished frame has a result.
publication-result : ∀ w h result c {c′} →
 lookup w (S.handlers (M.world c)) ≡ just h →
 M.advance (M.handlerPublication w result M.resultWritten) c ≡ just c′ →
 lookup (S.handlerPromise h) (S.handshakeResults (M.world c′)) ≡ just result
publication-result w h result c handler eq with any (λ v → does (v ≟ w)) (M.publicationFaults c)
... | true = case eq of λ ()
... | false with lookup w (S.handlers (M.world c)) in found | lookup w (S.cleanups (M.world c))
...   | nothing | _ = case handler of λ ()
...   | just actual | just _ = case eq of λ ()
...   | just actual | nothing with any (λ p → does (p ≟ S.handlerPromise actual)) (S.promises (M.world c))
...     | false = case eq of λ ()
...     | true with lookup (S.handlerPromise actual) (S.handshakeResults (M.world c))
...       | just _ = case eq of λ ()
...       | nothing = case just-injective handler of λ { refl →
 case just-injective eq of λ { refl → lookup-put (S.handlerPromise actual) result (S.handshakeResults (M.world c)) } }

-- Lift allocation through the actual outbound dispatcher.
outbound-allocation : ∀ f hid mid c {c′} →
 O.advance (O.inbound (M.igStep (U.allocationAction f hid mid))) c ≡ just c′ →
 Anchor (U.captured f) (U.bundle f) (U.flow f) hid mid (M.inboundGovernor (O.core c′))
outbound-allocation f hid mid c eq with M.advance (M.igStep (U.allocationAction f hid mid)) (O.core c) in actual
... | nothing = case eq of λ ()
... | just core = case just-injective eq of λ { refl → allocation f hid mid (O.core c) actual }

-- Every successful supervised allocation establishes its newly stored frame's
-- exact handle/mux/negotiation chain, without an assumed resource certificate.
allocated : ∀ w hid mid s {t} → U.allocate w hid mid s ≡ just t →
 Σ U.Frame (λ f → lookup w (U.frames t) ≡ just f × U.progress f ≡ U.handleAllocated hid mid ×
 Anchor (U.captured f) (U.bundle f) (U.flow f) hid mid (M.inboundGovernor (O.core (U.source t))))
allocated w hid mid s eq with lookup w (U.frames s)
... | nothing = case eq of λ ()
... | just f with U.progress f
...   | U.returnedSuccess with O.advance (O.inbound (M.igStep (U.allocationAction f hid mid))) (U.source s) in actual
...     | nothing = case eq of λ ()
...     | just c = case just-injective eq of λ { refl → _ , lookup-put w _ (U.frames s) , refl , outbound-allocation f hid mid (U.source s) actual }
allocated w hid mid s eq | just f | U.handleAllocated h m = case eq of λ ()
allocated w hid mid s eq | just f | U.promisePublished h m = case eq of λ ()

-- The two state invariants still to be established through all tracker writers.
-- Defining them does not assert that a source trace alone establishes them.
AllocationAt : U.Frame → O.Configuration → Set
AllocationAt f c with U.progress f
... | U.returnedSuccess = Data.Unit.⊤
... | U.handleAllocated hid mid = Anchor (U.captured f) (U.bundle f) (U.flow f) hid mid (M.inboundGovernor (O.core c))
... | U.promisePublished hid mid = Anchor (U.captured f) (U.bundle f) (U.flow f) hid mid (M.inboundGovernor (O.core c))
PublicationAt : U.Frame → O.Configuration → Set
PublicationAt f c with U.progress f
... | U.returnedSuccess = Data.Unit.⊤
... | U.handleAllocated hid mid = Data.Unit.⊤
... | U.promisePublished hid mid = lookup (S.handlerPromise (U.captured f)) (S.handshakeResults (M.world (O.core c))) ≡ just (S.negotiated hid (U.flow f))
AllocationReferences : U.State → Set
AllocationReferences s = ∀ w f → lookup w (U.frames s) ≡ just f → AllocationAt f (U.source s)
PublicationReferences : U.State → Set
PublicationReferences s = ∀ w f → lookup w (U.frames s) ≡ just f → PublicationAt f (U.source s)

-- Publication through the outbound source wrapper has the same exact result.
outbound-publication-result : ∀ w h result c {c′} →
 lookup w (S.handlers (M.world (O.core c))) ≡ just h →
 O.advance (O.inbound (M.handlerPublication w result M.resultWritten)) c ≡ just c′ →
 lookup (S.handlerPromise h) (S.handshakeResults (M.world (O.core c′))) ≡ just result
outbound-publication-result w h result c registered eq with M.advance (M.handlerPublication w result M.resultWritten) (O.core c) in actual
... | nothing = case eq of λ ()
... | just core = case just-injective eq of λ { refl → publication-result w h result (O.core c) registered actual }

-- The supervised phase transition publishes this frame's negotiated result.
-- Snapshot/resource validity supplies the handler lookup; arbitrary prefixes
-- before this event are allowed.
published : ∀ w f hid mid s {t} →
 lookup w (U.frames s) ≡ just f → U.progress f ≡ U.handleAllocated hid mid →
 lookup w (S.handlers (M.world (O.core (U.source s)))) ≡ just (U.captured f) →
 U.publish w s ≡ just t →
 lookup (S.handlerPromise (U.captured f)) (S.handshakeResults (M.world (O.core (U.source t)))) ≡ just (S.negotiated hid (U.flow f))
published w f hid mid s frame progress registered eq rewrite frame | progress
 with O.advance (O.inbound (M.handlerPublication w (S.negotiated hid (U.flow f)) M.resultWritten)) (U.source s) in actual |
 U.Startup.step U.Startup.observePublication (U.startup f)
... | nothing | _ = case eq of λ ()
... | just c | nothing = case eq of λ ()
... | just c | just next = case just-injective eq of λ { refl →
 outbound-publication-result w (U.captured f) (S.negotiated hid (U.flow f)) (U.source s) registered actual }

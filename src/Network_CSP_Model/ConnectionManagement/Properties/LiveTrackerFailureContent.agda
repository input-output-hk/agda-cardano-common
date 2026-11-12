{-# OPTIONS --guardedness #-}

-- Saved publication-saved frames retain their own descriptors and negotiated
-- content. No equality of saved/current mutable continuations is asserted.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerFailureContent (b : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Properties.HandlerBirthEffects as Effects
import ConnectionManagement.Properties.LiveTrackerCapture as Aux
import ConnectionManagement.Properties.LiveTrackerCaptureFrontend as Captures
import ConnectionManagement.Properties.LiveTrackerContentFrontend as Frames
import ConnectionManagement.Properties.LiveTrackerFrameContent as Content
import ConnectionManagement.Properties.MuxPublicationUnwind as Paths
import ConnectionManagement.MuxPublicationUnwind as Model
import ConnectionManagement.Rules.CMShutdown as Close
private module N = Model b using (Executes; Failure; State; action; allowed; apply; base; captured; deliverShutdown; deliveryReady; done; failures; initial; next; observation; observe; observeFailure; poolAt; raw; run; select; siteReady; source; step)
import ConnectionManagement.MuxStartupUnwind as UnwindModel
private module R = UnwindModel b using (async; base; enact; faults; owner)
import ConnectionManagement.MuxHandlerExit as ExitModel
private module W = ExitModel b using (exits; sameStart; shutdown)
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
private module U = ProtocolModel.U using (captured; frames; startup)
private module Startup = ProtocolModel.Startup using (awaitPublication; bearerReady; bufferReady; demuxerForked; demuxerRegistered; egressReady; matureTraced; monitoring; muxerForked; muxerRegistered; phase; poolReady; published; runEntered; startingTraced)
private module Pool = ProtocolModel.Pool using (handles)
private module Capture = Captures.Publication b using (Valid; initialized-valid; step-preserves)
private module Frame = Frames.Publication b using (Valid; initialized-valid; step-preserves)
import ConnectionManagement.Properties.LiveTrackerCaptureExit as CaptureExit
private module AC = CaptureExit.Unwind b using (frames-present)

import ConnectionManagement.MuxCatchUnwind as CatchModel
private module C = CatchModel b using (initial; step)
import ConnectionManagement.MuxDeltaQ as DeltaModel
private module D = DeltaModel b using (delivery)

view : N.State → Effects.Registry
view = Effects.PublicationLayer.view b
record Snapshot (w : WorkerId) (saved : N.Failure) (registry : Effects.Registry) (c : O.Configuration) : Set where
 constructor snapshot
 field descriptor : Aux.Ref w (U.captured (N.captured saved)) registry
       negotiated : Content.Content w (N.captured saved) c
open Snapshot public
Covers : Store WorkerId N.Failure → Effects.Registry → O.Configuration → Set
Covers rows registry c = All (λ { (w , saved) → Snapshot w saved registry c }) rows
insert : ∀ w saved rows registry c → Snapshot w saved registry c → Covers rows registry c → Covers (put w saved rows) registry c
insert w saved [] registry c good [] = good ∷ []
insert w saved ((q , old) ∷ rows) registry c good (oldGood ∷ rest) with w ≟ q
... | yes refl = good ∷ rest
... | no _ = oldGood ∷ insert w saved rows registry c good rest
at : ∀ rows registry c → Covers rows registry c → ∀ w saved → lookup w rows ≡ just saved → Snapshot w saved registry c
at [] registry c [] w saved ()
at ((q , first) ∷ rows) registry c (good ∷ rest) w saved found with w ≟ q
... | yes refl = case just-injective found of λ { refl → good }
... | no _ = at rows registry c rest w saved found
transport : ∀ rows {registry registry′ c as d} → Aux.Retains registry registry′ → O.Executes c as d → Covers rows registry c → Covers rows registry′ d
transport [] retained path [] = []
transport ((w , saved) ∷ rows) retained path (good ∷ rest) =
 snapshot (retained w (U.captured (N.captured saved)) (descriptor good))
   (Content.execute path w (N.captured saved) (negotiated good)) ∷ transport rows retained path rest

selected-content : ∀ w site result s {p} → N.select w site result s ≡ just p →
  Frame.Valid s → Capture.Valid s → Snapshot w (N.observation p) (view s) (N.source s)
selected-content w site result s eq frames valid with lookup w (N.failures s) | R.owner w (N.raw s) in owner-found | lookup w (W.exits (R.base (N.raw s))) | lookup w (R.faults (N.raw s))
... | just oldFault | _ | _ | _ = case eq of λ ()
... | nothing | nothing | _ | _ = case eq of λ ()
... | nothing | just f | just e | _ = case eq of λ ()
... | nothing | just f | nothing | just oldFault = case eq of λ ()
... | nothing | just f | nothing | nothing with N.siteReady site f (N.source s) | N.deliveryReady site result | Startup.phase (U.startup f) | Pool.handles (N.poolAt w s)
...   | true | true | Startup.awaitPublication | [] with lookup w (Shared.handlers (Machine.world (O.core (N.source s)))) |
   lookup (Shared.handlerPromise (U.captured f)) (Shared.handshakeResults (Machine.world (O.core (N.source s))))
...     | just actual | nothing with W.sameStart (U.captured f) actual
...       | true = case just-injective eq of λ { refl →
   snapshot present (Content.at _ (N.source s) frames w f owner-found) }
  where present = Aux.covers-at (AC.frames-present {s = N.raw s} (proj₁ valid)) w f owner-found
...       | false = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | [] | nothing | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | [] | just actual | just value = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | false | _ | _ | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | false | _ | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | h ∷ rest = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.published | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.bufferReady | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.bearerReady | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.runEntered | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.startingTraced | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.egressReady | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | Startup.poolReady | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | (Startup.muxerForked j) | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | (Startup.muxerRegistered j) | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | (Startup.demuxerForked j k) | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | (Startup.demuxerRegistered j k) | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | (Startup.matureTraced j k) | _ = case eq of λ ()
selected-content w site result s eq frames valid | nothing | just f | nothing | nothing | true | true | (Startup.monitoring j k) | _ = case eq of λ ()

-- A selected transfer and optional acknowledgement cannot grow the physical
-- registry. Its actual source trace nevertheless transports saved content.
apply-preserves : ∀ w site result ack s {p t} → N.select w site result s ≡ just p →
  N.apply w p ack s ≡ just t → Snapshot w (N.observation p) (view s) (N.source s) →
  Covers (N.failures s) (view s) (N.source s) → Covers (N.failures t) (view t) (N.source t)
apply-preserves w site result ack s {p} {t} selected actual good valid =
 subst (λ rows → Covers rows (view t) (N.source t)) (sym (shape actual))
  (transport (put w (N.observation p) (N.failures s))
    (λ q h found → subst (λ registry → Aux.Ref q h registry)
       (sym (Effects.PublicationLayer.CIPaths.retention
         (Effects.PublicationLayer.apply-same b w p ack s
           (Effects.PublicationLayer.select-no-birth b w site result s selected) actual))) found)
    (proj₂ (Paths.Exit.machine (Paths.apply-projects b w p ack s actual)))
    (insert w (N.observation p) (N.failures s) (view s) (N.source s) good valid))
 where
 shape : ∀ {t} → N.apply w p ack s ≡ just t → N.failures t ≡ put w (N.observation p) (N.failures s)
 shape eq with R.enact (D.delivery ack (N.action p)) (N.raw s)
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → refl }

record Valid (s : N.State) : Set where
 constructor failure-valid
 field frames : Frame.Valid s
       captures : Capture.Valid s
       snapshots : Covers (N.failures s) (view s) (N.source s)
open Valid public
observe-preserves : ∀ w site result ack s {t} → N.observe w site result ack s ≡ just t → Valid s →
 Covers (N.failures t) (view t) (N.source t)
observe-preserves w site result ack s actual good with N.select w site result s in selected
... | nothing = case actual of λ ()
... | just p = apply-preserves w site result ack s selected actual
  (selected-content w site result s selected (frames good) (captures good)) (snapshots good)
step-snapshots : ∀ a s {t} → N.step a s ≡ just t → Valid s → Covers (N.failures t) (view t) (N.source t)
step-snapshots (N.run a) s {t} actual good =
 subst (λ rows → Covers rows (view t) (N.source t)) (sym (shape actual))
  (transport (N.failures s) (Aux.change-retains (Effects.PublicationLayer.change b (N.run a) s actual))
    (proj₂ (Paths.Exit.machine (Paths.step-projects b (N.run a) s actual))) (snapshots good))
 where
 shape : ∀ {t} → N.step (N.run a) s ≡ just t → N.failures t ≡ N.failures s
 shape eq with N.allowed a s
 ... | false = case eq of λ ()
 ... | true with C.step a (N.base s)
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → refl }
step-snapshots (N.observeFailure w site result) s actual good = observe-preserves w site result false s actual good
step-snapshots (N.deliverShutdown site err) s actual good with Close.phase (W.shutdown (R.base (N.raw s)))
... | Close.awaitDelivery e w = observe-preserves w site (R.async err) true s actual good
... | Close.initial = case actual of λ ()
... | Close.reading = case actual of λ ()
... | Close.sendReady e w = case actual of λ ()
... | Close.awaitResults = case actual of λ ()
... | Close.closed = case actual of λ ()
step-preserves : ∀ a s {t} → N.step a s ≡ just t → Valid s → Valid t
step-preserves a s actual good = failure-valid (Frame.step-preserves a s actual (frames good))
 (Capture.step-preserves a s actual (captures good)) (step-snapshots a s actual good)
initialized-valid : ∀ c {s} → N.initial c ≡ just s → Valid s
initialized-valid c actual = failure-valid (Frame.initialized-valid c actual) (Capture.initialized-valid c actual) (empty actual)
 where
 empty : ∀ {s} → N.initial c ≡ just s → Covers (N.failures s) (view s) (N.source s)
 empty eq with C.initial c
 ... | nothing = case eq of λ ()
 ... | just caught = case just-injective eq of λ { refl → [] }
run-preserves : ∀ {s as t} → N.Executes s as t → Valid s → Valid t
run-preserves N.done good = good
run-preserves (N.next {s = s} {a = a} actual rest) good = run-preserves rest (step-preserves a s actual good)
from-initial : ∀ c {start as s} → N.initial c ≡ just start → N.Executes start as s → Valid s
from-initial c initialized path = run-preserves path (initialized-valid c initialized)

{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through the two lowest Server layers: the outbound
-- handler supervisor and the mux handler supervisor. Handler and mux-startup
-- steps write only the dispatcher core; an outbound action has its own
-- machine effect (OutboundKeys.Effect of its root).
module ConnectionManagement.Properties.SourceKeysBase where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.MuxHandlerSupervision as Model
open import ConnectionManagement.Properties.OutboundKeys

-- B: a lifted outbound action is the only root.
rootB : B.Action → Maybe O.Action
rootB (B.handler _) = nothing
rootB (B.outbound x) = keyRoot x

handler-keys : ∀ a s {s′} → B.handlerStep a s ≡ just s′ → KeySame (B.source s) (B.source s′)
handler-keys a s eq with B.handlerAllowed a s
... | false = case eq of λ ()
... | true with H.step a (B.view s)
...   | nothing = case eq of λ ()
...   | just h = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
fork-keys : ∀ w s {s′} → B.forkOutbound w s ≡ just s′ → KeySame (B.source s) (B.source s′)
fork-keys w s eq with lookup w (O.acquiring (B.source s))
... | nothing = case eq of λ ()
... | just f with B.freshChild (A.child (A.req f)) s
...   | false = case eq of λ ()
...   | true with O.advance (O.acquire w A.forkOK) (B.source s) in advanced
...     | nothing = case eq of λ ()
...     | just c with lookup (A.child (A.req f)) (S.handlers (M.world (O.core c)))
...       | nothing = case eq of λ ()
...       | just h = case just-injective eq of λ { refl → nonkey (O.acquire w A.forkOK) (B.source s) refl advanced }
dispatch-keys : ∀ x s {s′} → B.dispatchOutbound x s ≡ just s′ → Effect (keyRoot x) (B.source s) (B.source s′)
dispatch-keys x s eq with B.outboundAllowed x s
... | false = case eq of λ ()
... | true with O.advance x (B.source s) in advanced
...   | nothing = case eq of λ ()
...   | just c = case just-injective eq of λ { refl → advance-effect x (B.source s) advanced }
fork-shape : ∀ x {w} → B.forkCaller x ≡ just w → x ≡ O.acquire w A.forkOK
fork-shape (O.acquire w A.forkOK) refl = refl
fork-shape (O.acquire w (A.select e)) ()
fork-shape (O.acquire w A.readCounters) ()
fork-shape (O.acquire w A.newPromise) ()
fork-shape (O.acquire w A.openOK) ()
fork-shape (O.acquire w A.configureOK) ()
fork-shape (O.acquire w A.bindOK) ()
fork-shape (O.acquire w A.connectOK) ()
fork-shape (O.acquire w (A.gotLocal p)) ()
fork-shape (O.acquire w A.updateLocalAddress) ()
fork-shape (O.acquire w A.commitConnected) ()
fork-shape (O.acquire w A.readResult) ()
fork-shape (O.acquire w A.commitHandshake) ()
fork-shape (O.acquire w A.returnResult) ()
fork-shape (O.acquire w (A.failIO e)) ()
fork-shape (O.acquire w (A.closeFailed e)) ()
fork-shape (O.acquire w A.closeOK) ()
fork-shape (O.acquire w A.removeReservation) ()
fork-shape (O.acquire w A.waitNegotiated) ()
fork-shape (O.inbound _) ()
fork-shape (O.beginAcquire _ _) ()
fork-shape (O.beginRelease _ _) ()
fork-shape (O.release _ _) ()
outbound-keys : ∀ x s {s′} → B.outboundStep x s ≡ just s′ → Effect (keyRoot x) (B.source s) (B.source s′)
outbound-keys x s eq with B.forkCaller x in fc
... | just w with fork-shape x fc
...   | refl = fork-keys w s eq
outbound-keys x s eq | nothing = dispatch-keys x s eq
step-keysB : ∀ a s {s′} → B.step a s ≡ just s′ → Effect (rootB a) (B.source s) (B.source s′)
step-keysB (B.handler a) s eq = handler-keys a s eq
step-keysB (B.outbound x) s eq = outbound-keys x s eq

-- U: mux handler supervision, for any typed result.
module U (Result : Set) where
  private module W = Model Result
  rootU : W.Action → Maybe O.Action
  rootU (W.run a) = rootB a
  rootU _ = nothing
  -- Startup bookkeeping writes no source.
  frame-same : ∀ w f s → KeySame (W.source s) (W.source (W.setFrame w f s))
  frame-same w f s = same-refl (W.source s)
  birth-source : ∀ x s → W.source (W.noteBirth x s) ≡ W.source s
  birth-source nothing s = refl
  birth-source (just (w , origin)) s = refl
  inherit-keys : ∀ a s {s′} → W.inherit a s ≡ just s′ → Effect (rootB a) (W.source s) (W.source s′)
  inherit-keys a s eq with W.baseAllowed a s ∧ W.birthFresh (W.birth a (W.base s)) (W.origins s)
  ... | false = case eq of λ ()
  ... | true with B.step a (W.base s) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just b = case just-injective eq of λ { refl → subst (λ c → Effect (rootB a) (W.source s) c)
    (sym (birth-source (W.birth a (W.base s)) (record s { base = b }))) (step-keysB a (W.base s) stepped) }
  negotiate-keys : ∀ w ps fl s {s′} → W.negotiateReturned w ps fl s ≡ just s′ → KeySame (W.source s) (W.source s′)
  negotiate-keys w ps fl s eq with lookup w (B.threads (W.base s)) | lookup w (W.origins s) | lookup w (W.frames s)
  ... | just t | just origin | nothing with H.phase t
  ...   | H.handshaking = case just-injective eq of λ { refl → same-refl _ }
  ...   | H.maskedSetup = case eq of λ ()
  ...   | H.caughtCancellation _ = case eq of λ ()
  ...   | H.cancellationPublished _ = case eq of λ ()
  ...   | H.bodyExited _ = case eq of λ ()
  ...   | H.finalizing _ = case eq of λ ()
  ...   | H.cleanupComplete _ _ = case eq of λ ()
  ...   | H.resultAvailable _ _ = case eq of λ ()
  negotiate-keys w ps fl s eq | nothing | _ | _ = case eq of λ ()
  negotiate-keys w ps fl s eq | just _ | nothing | _ = case eq of λ ()
  negotiate-keys w ps fl s eq | just _ | just _ | just _ = case eq of λ ()
  allocate-keys : ∀ w hid mid s {s′} → W.allocate w hid mid s ≡ just s′ → KeySame (W.source s) (W.source s′)
  allocate-keys w hid mid s eq with lookup w (W.frames s)
  ... | nothing = case eq of λ ()
  ... | just f with W.progress f
  ...   | W.returnedSuccess with O.advance (O.inbound (M.igStep (W.allocationAction f hid mid))) (W.source s) in advanced
  ...     | nothing = case eq of λ ()
  ...     | just c = case just-injective eq of λ { refl → nonkey (O.inbound (M.igStep (W.allocationAction f hid mid))) (W.source s) refl advanced }
  allocate-keys w hid mid s eq | just f | W.handleAllocated _ _ = case eq of λ ()
  allocate-keys w hid mid s eq | just f | W.promisePublished _ _ = case eq of λ ()
  configure-keys : ∀ w plan limit bound keys s {s′} → W.configure w plan limit bound keys s ≡ just s′ →
    KeySame (W.source s) (W.source s′)
  configure-keys w E.plainLayout limit bound keys s ()
  configure-keys w (E.scheduledLayout b) limit bound keys s eq with lookup w (W.frames s)
  ... | nothing = case eq of λ ()
  ... | just f with W.progress f
  ...   | W.handleAllocated hid mid with O.advance (O.inbound (M.igStep (IG.configureEgress mid (E.scheduledLayout b) limit bound keys))) (W.source s) in advanced
  ...     | nothing = case eq of λ ()
  ...     | just c = case just-injective eq of λ { refl → nonkey (O.inbound (M.igStep (IG.configureEgress mid (E.scheduledLayout b) limit bound keys))) (W.source s) refl advanced }
  configure-keys w (E.scheduledLayout b) limit bound keys s eq | just f | W.returnedSuccess = case eq of λ ()
  configure-keys w (E.scheduledLayout b) limit bound keys s eq | just f | W.promisePublished _ _ = case eq of λ ()
  register-keys : ∀ w s {s′} → W.registerFor w s ≡ just s′ → KeySame (W.source s) (W.source s′)
  register-keys w s eq with lookup w (W.frames s)
  ... | nothing = case eq of λ ()
  ... | just f with W.progress f | W.beforePool (W.Startup.phase (W.startup f))
  ...   | W.promisePublished hid mid | true with O.advance (O.inbound (M.igStep (IG.registerCells mid))) (W.source s) in advanced
  ...     | nothing = case eq of λ ()
  ...     | just c = case just-injective eq of λ { refl → nonkey (O.inbound (M.igStep (IG.registerCells mid))) (W.source s) refl advanced }
  register-keys w s eq | just f | W.promisePublished _ _ | false = case eq of λ ()
  register-keys w s eq | just f | W.returnedSuccess | _ = case eq of λ ()
  register-keys w s eq | just f | W.handleAllocated _ _ | _ = case eq of λ ()
  setup-keys : ∀ w s {s′} → W.setupFor w s ≡ just s′ → KeySame (W.source s) (W.source s′)
  setup-keys w s eq with lookup w (W.frames s)
  ... | nothing = case eq of λ ()
  ... | just f with W.scheduled f (W.source s) | W.nextSetup (W.setup f)
  ...   | true | just next = case just-injective eq of λ { refl → same-refl _ }
  ...   | true | nothing = case eq of λ ()
  ...   | false | _ = case eq of λ ()
  publish-keys : ∀ w s {s′} → W.publish w s ≡ just s′ → KeySame (W.source s) (W.source s′)
  publish-keys w s eq with lookup w (W.frames s)
  ... | nothing = case eq of λ ()
  ... | just f with W.progress f
  ...   | W.handleAllocated hid mid with O.advance
      (O.inbound (M.handlerPublication w (S.negotiated hid (W.flow f)) M.resultWritten)) (W.source s) in advanced |
      W.Startup.step W.Startup.observePublication (W.startup f)
  ...     | just c | just next = case just-injective eq of λ { refl → nonkey (O.inbound (M.handlerPublication w (S.negotiated hid (W.flow f)) M.resultWritten)) (W.source s) refl advanced }
  ...     | just c | nothing = case eq of λ ()
  ...     | nothing | _ = case eq of λ ()
  publish-keys w s eq | just f | W.returnedSuccess = case eq of λ ()
  publish-keys w s eq | just f | W.promisePublished _ _ = case eq of λ ()
  startup-keys : ∀ w a s {s′} → W.advanceStartup w a s ≡ just s′ → KeySame (W.source s) (W.source s′)
  startup-keys w a s eq with lookup w (W.frames s)
  ... | nothing = case eq of λ ()
  ... | just f with W.progress f | W.startupAllowed a f s
  ...   | W.promisePublished hid mid | true with W.Startup.step a (W.startup f)
  ...     | nothing = case eq of λ ()
  ...     | just next = case just-injective eq of λ { refl → same-refl _ }
  startup-keys w a s eq | just f | W.promisePublished _ _ | false = case eq of λ ()
  startup-keys w a s eq | just f | W.returnedSuccess | _ = case eq of λ ()
  startup-keys w a s eq | just f | W.handleAllocated _ _ | _ = case eq of λ ()
  step-keysU : ∀ a s {s′} → W.step a s ≡ just s′ → Effect (rootU a) (W.source s) (W.source s′)
  step-keysU (W.run a) s eq = inherit-keys a s eq
  step-keysU (W.negotiate w ps fl) s eq = negotiate-keys w ps fl s eq
  step-keysU (W.allocateHandle w hid mid) s eq = allocate-keys w hid mid s eq
  step-keysU (W.configureMux w plan limit bound keys) s eq = configure-keys w plan limit bound keys s eq
  step-keysU (W.registerCounters w) s eq = register-keys w s eq
  step-keysU (W.egressSetup w) s eq = setup-keys w s eq
  step-keysU (W.publishSuccess w) s eq = publish-keys w s (W.whenSetupDone-just w s (W.publish w s) eq)
  step-keysU (W.startupStep w a) s eq = startup-keys w a s eq

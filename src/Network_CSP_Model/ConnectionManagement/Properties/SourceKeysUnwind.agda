{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through startup unwinding: own plans are local, pool,
-- transfer or inbound-machine plans; only an inherited action has a root.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysUnwind (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.MuxHandlerExit
import ConnectionManagement.MuxExitCancellation
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysExit as ExitKeys
import ConnectionManagement.Properties.SourceKeysCancel as CancelKeys
private
  module R = Unwind isBearerClosed
  module W = ConnectionManagement.MuxHandlerExit isBearerClosed
  module X = ConnectionManagement.MuxExitCancellation isBearerClosed
  module G = W.G
  module M = G.M
  module P = G.P
  module U = G.U
  module Pool = G.Pool
  module Lower = CancelKeys isBearerClosed
  module Exit = ExitKeys isBearerClosed

rootR : R.Action → Maybe O.Action
rootR (R.run a) = Lower.rootX a
rootR _ = nothing
planRoot : R.Plan → Maybe O.Action
planRoot (R.inherited a) = Lower.rootX a
planRoot (R.machine x fs) = keyRoot x
planRoot (R.acknowledge p) = planRoot p
planRoot _ = nothing

enact-keys : ∀ plan s {s′} → R.enact plan s ≡ just s′ → Effect (planRoot plan) (R.source s) (R.source s′)
enact-keys (R.local fs) s eq = case just-injective eq of λ { refl → same-refl _ }
enact-keys (R.machine x fs) s eq with O.advance x (R.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → advance-effect x (R.source s) advanced }
enact-keys (R.pool w u act fs) s eq with Pool.step act (R.poolAt w s)
... | nothing = case eq of λ ()
... | just p = case just-injective eq of λ { refl → same-refl _ }
enact-keys (R.inherited a) s eq with X.step a (R.base s) in stepped
... | nothing = case eq of λ ()
... | just x = case just-injective eq of λ { refl → Lower.step-keysX a (R.base s) stepped }
enact-keys (R.transfer w f fs) s eq = case just-injective eq of λ { refl → same-refl _ }
enact-keys (R.acknowledge p) s eq with R.enact p s in first
... | nothing = case eq of λ ()
... | just next with W.control Close.acknowledgeDelivery (R.base next) in controlled
...   | nothing = case eq of λ ()
...   | just x = case just-injective eq of λ { refl → effect-after (planRoot p) (enact-keys p s first)
  (Exit.control-keys Close.acknowledgeDelivery (R.base next) controlled) }

start-root : ∀ w result route s {plan} → R.start w result route s ≡ just plan → planRoot plan ≡ nothing
start-root w result route s eq with R.free w s | R.owner w s | lookup w (W.exits (R.base s)) | P.noParent (R.poolAt w s)
... | true | just f | nothing | true with U.progress f
...   | U.promisePublished hid mid with P.muxAt mid (R.protocols s)
...     | just m with route f m
...       | just r = case just-injective eq of λ { refl → refl }
...       | nothing = case eq of λ ()
start-root w result route s eq | true | just f | nothing | true | U.promisePublished hid mid | nothing = case eq of λ ()
start-root w result route s eq | true | just f | nothing | true | (U.handshakePending helperPC) = case eq of λ ()
start-root w result route s eq | true | just f | nothing | true | U.returnedSuccess = case eq of λ ()
start-root w result route s eq | true | just f | nothing | true | U.handleAllocated _ _ = case eq of λ ()
start-root w result route s eq | true | nothing | _ | _ = case eq of λ ()
start-root w result route s eq | true | just _ | nothing | false = case eq of λ ()
start-root w result route s eq | true | just _ | just _ | _ = case eq of λ ()
start-root w result route s eq | false | _ | _ | _ = case eq of λ ()
cancel-root : ∀ w site err s {plan} → R.cancellationPlan w site err s ≡ just plan → planRoot plan ≡ nothing
cancel-root w site err s eq with R.deliveryControl w site s
... | true = start-root w _ _ s eq
... | false = case eq of λ ()
pool-root : ∀ w before act after s {plan} → R.withPool w before act after s ≡ just plan → planRoot plan ≡ nothing
pool-root w before act after s eq with lookup w (R.faults s) | R.owner w s
... | just f | just u with R.sameClose before (R.phase f)
...   | true = case just-injective eq of λ { refl → refl }
...   | false = case eq of λ ()
pool-root w before act after s eq | nothing | _ = case eq of λ ()
pool-root w before act after s eq | just _ | nothing = case eq of λ ()

choose-root : ∀ a s {plan} → R.choose a s ≡ just plan → planRoot plan ≡ rootR a
choose-root (R.run a) s eq with R.allowed a s
... | true = case just-injective eq of λ { refl → refl }
... | false = case eq of λ ()
choose-root (R.observeFailure w site err) s eq with R.siteControl w site s
... | true = start-root w _ _ s eq
... | false = case eq of λ ()
choose-root (R.observeCancellation w site err) s eq = cancel-root w site err s eq
choose-root (R.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base s))
... | Close.awaitDelivery e w with R.cancellationPlan w site err s in planned
...   | just p = case just-injective eq of λ { refl → cancel-root w site err s planned }
...   | nothing = case eq of λ ()
choose-root (R.deliverShutdown site err) s eq | Close.initial = case eq of λ ()
choose-root (R.deliverShutdown site err) s eq | Close.reading = case eq of λ ()
choose-root (R.deliverShutdown site err) s eq | Close.awaitResults = case eq of λ ()
choose-root (R.deliverShutdown site err) s eq | Close.closed = case eq of λ ()
choose-root (R.deliverShutdown site err) s eq | Close.sendReady _ _ = case eq of λ ()
choose-root (R.beginClose w order) s eq = pool-root w R.awaitingClose _ R.closing s eq
choose-root (R.requestCancel w) s eq = pool-root w R.closing _ R.closing s eq
choose-root (R.join w) s eq = pool-root w R.closing _ R.closing s eq
choose-root (R.finishClose w) s eq = pool-root w R.closing _ R.poolClosed s eq
choose-root (R.deliverCancel w) s eq with lookup w (R.faults s) | R.owner w s | Pool.phase (R.poolAt w s)
... | just f | just u | Pool.cancelPending j with R.phase f | G.wholeDeliverable w j u (W.base (R.base s))
...   | R.closing | true = case just-injective eq of λ { refl → refl }
choose-root (R.deliverCancel w) s eq | just f | just u | Pool.cancelPending j | R.readyBody | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just f | just u | Pool.cancelPending j | R.readyBuffer | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just f | just u | Pool.cancelPending j | R.awaitingClose | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just f | just u | Pool.cancelPending j | R.closing | false = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just f | just u | Pool.cancelPending j | R.poolClosed | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just f | just u | Pool.cancelPending j | R.asyncStatus | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just f | just u | Pool.cancelPending j | R.asyncDead | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just f | just u | Pool.cancelPending j | R.handedOff | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | nothing | _ | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just _ | nothing | _ = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just _ | just _ | Pool.openPool = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just _ | just _ | Pool.closing = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just _ | just _ | Pool.closedPool = case eq of λ ()
choose-root (R.deliverCancel w) s eq | just _ | just _ | Pool.joinPending _ = case eq of λ ()
choose-root (R.continueSync w) s eq with lookup w (R.faults s) | Pool.phase (R.poolAt w s)
... | just f | Pool.closedPool with R.phase f | R.outcome f
...   | R.poolClosed | R.sync err = case just-injective eq of λ { refl → refl }
choose-root (R.continueSync w) s eq | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just f | Pool.closedPool | R.poolClosed | R.async _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
choose-root (R.continueSync w) s eq | nothing | _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just _ | Pool.openPool = case eq of λ ()
choose-root (R.continueSync w) s eq | just _ | Pool.closing = case eq of λ ()
choose-root (R.continueSync w) s eq | just _ | Pool.cancelPending _ = case eq of λ ()
choose-root (R.continueSync w) s eq | just _ | Pool.joinPending _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq with lookup w (R.faults s) | Pool.phase (R.poolAt w s)
... | just f | Pool.closedPool with R.phase f | R.outcome f
...   | R.poolClosed | R.async err = case just-injective eq of λ { refl → refl }
choose-root (R.writeAsyncFailure w) s eq | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just f | Pool.closedPool | R.poolClosed | R.sync _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | nothing | _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just _ | Pool.openPool = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just _ | Pool.closing = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just _ | Pool.cancelPending _ = case eq of λ ()
choose-root (R.writeAsyncFailure w) s eq | just _ | Pool.joinPending _ = case eq of λ ()
choose-root (R.beginDead w) s eq with lookup w (R.faults s)
... | just f with R.phase f
...   | R.asyncStatus = case just-injective eq of λ { refl → refl }
choose-root (R.beginDead w) s eq | just f | R.readyBody = case eq of λ ()
choose-root (R.beginDead w) s eq | just f | R.readyBuffer = case eq of λ ()
choose-root (R.beginDead w) s eq | just f | R.awaitingClose = case eq of λ ()
choose-root (R.beginDead w) s eq | just f | R.closing = case eq of λ ()
choose-root (R.beginDead w) s eq | just f | R.poolClosed = case eq of λ ()
choose-root (R.beginDead w) s eq | just f | R.asyncDead = case eq of λ ()
choose-root (R.beginDead w) s eq | just f | R.handedOff = case eq of λ ()
choose-root (R.beginDead w) s eq | nothing = case eq of λ ()
choose-root (R.sampleDead w) s eq with lookup w (R.faults s)
... | just f with R.phase f
...   | R.asyncDead = case just-injective eq of λ { refl → refl }
choose-root (R.sampleDead w) s eq | just f | R.readyBody = case eq of λ ()
choose-root (R.sampleDead w) s eq | just f | R.readyBuffer = case eq of λ ()
choose-root (R.sampleDead w) s eq | just f | R.awaitingClose = case eq of λ ()
choose-root (R.sampleDead w) s eq | just f | R.closing = case eq of λ ()
choose-root (R.sampleDead w) s eq | just f | R.poolClosed = case eq of λ ()
choose-root (R.sampleDead w) s eq | just f | R.asyncStatus = case eq of λ ()
choose-root (R.sampleDead w) s eq | just f | R.handedOff = case eq of λ ()
choose-root (R.sampleDead w) s eq | nothing = case eq of λ ()
choose-root (R.commitDead w) s eq with lookup w (R.faults s)
... | just f with R.phase f
...   | R.asyncDead = case just-injective eq of λ { refl → refl }
choose-root (R.commitDead w) s eq | just f | R.readyBody = case eq of λ ()
choose-root (R.commitDead w) s eq | just f | R.readyBuffer = case eq of λ ()
choose-root (R.commitDead w) s eq | just f | R.awaitingClose = case eq of λ ()
choose-root (R.commitDead w) s eq | just f | R.closing = case eq of λ ()
choose-root (R.commitDead w) s eq | just f | R.poolClosed = case eq of λ ()
choose-root (R.commitDead w) s eq | just f | R.asyncStatus = case eq of λ ()
choose-root (R.commitDead w) s eq | just f | R.handedOff = case eq of λ ()
choose-root (R.commitDead w) s eq | nothing = case eq of λ ()
choose-root (R.finishDead w) s eq with lookup w (R.faults s)
... | just f with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols s)
...   | R.asyncDead | R.async err | just m with Mux.callback m | M.finishMatches (M.failed err) (Mux.status m)
...     | Mux.returned | true = case just-injective eq of λ { refl → refl }
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.async err | just m | Mux.readActive _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.async err | just m | Mux.commitTrace _ _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.async err | just m | Mux.afterStart _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.async err | just m | Mux.forkPending _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.async err | just m | Mux.afterFailure | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.async err | just m | Mux.tracerFailed _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.async err | just m | Mux.returned | false = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.readyBody | _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.readyBuffer | _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.awaitingClose | _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.closing | _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.poolClosed | _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncStatus | _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.sync _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.asyncDead | R.async _ | nothing = case eq of λ ()
choose-root (R.finishDead w) s eq | just f | R.handedOff | _ | _ = case eq of λ ()
choose-root (R.finishDead w) s eq | nothing = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq with lookup w (R.faults s)
... | just f with R.phase f | P.muxAt (R.mux f) (R.protocols s)
...   | R.asyncDead | just m with R.deadThrowPoint m
...     | true = case just-injective eq of λ { refl → refl }
...     | false = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | just f | R.readyBody | _ = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | just f | R.readyBuffer | _ = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | just f | R.awaitingClose | _ = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | just f | R.closing | _ = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | just f | R.poolClosed | _ = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | just f | R.asyncStatus | _ = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | just f | R.asyncDead | nothing = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | just f | R.handedOff | _ = case eq of λ ()
choose-root (R.observeDeadTraceException w err) s eq | nothing = case eq of λ ()
choose-root (R.handoff w) s eq with lookup w (R.faults s) | lookup w (W.exits (R.base s))
... | just f | nothing with R.phase f | R.outcome f
...   | R.readyBuffer | result with R.counterRow f s
...     | just _ = case just-injective eq of λ { refl → refl }
...     | nothing = case just-injective eq of λ { refl → refl }
choose-root (R.handoff w) s eq | just f | nothing | R.readyBody | R.sync err = case just-injective eq of λ { refl → refl }
choose-root (R.handoff w) s eq | just f | nothing | R.readyBody | R.async err = case just-injective eq of λ { refl → refl }
choose-root (R.handoff w) s eq | just f | nothing | R.awaitingClose | _ = case eq of λ ()
choose-root (R.handoff w) s eq | just f | nothing | R.closing | _ = case eq of λ ()
choose-root (R.handoff w) s eq | just f | nothing | R.poolClosed | _ = case eq of λ ()
choose-root (R.handoff w) s eq | just f | nothing | R.asyncStatus | _ = case eq of λ ()
choose-root (R.handoff w) s eq | just f | nothing | R.asyncDead | _ = case eq of λ ()
choose-root (R.handoff w) s eq | just f | nothing | R.handedOff | _ = case eq of λ ()
choose-root (R.handoff w) s eq | nothing | _ = case eq of λ ()
choose-root (R.handoff w) s eq | just _ | just _ = case eq of λ ()

step-keysR : ∀ a s {s′} → R.step a s ≡ just s′ → Effect (rootR a) (R.source s) (R.source s′)
step-keysR a s {s′} eq with R.choose a s in chosen
... | nothing = case eq of λ ()
... | just plan = subst (λ r → Effect r (R.source s) (R.source s′)) (choose-root a s chosen) (enact-keys plan s eq)

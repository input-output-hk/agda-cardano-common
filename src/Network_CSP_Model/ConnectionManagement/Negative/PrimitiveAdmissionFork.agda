{-# OPTIONS --guardedness #-}

-- G1 F5: initialized pre-birth synchronous async-fork failure and the outer
-- masked onException close. No worker/handler history is invented. Successful
-- IO/close-failure outcomes are supplied observations, not progress guarantees.
module ConnectionManagement.Negative.PrimitiveAdmissionFork where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing; from-just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (errorId; ident; outbound; remote)
import ConnectionManagement.State as Shared
import ConnectionManagement.Scenarios.Admission as F
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.Rules.OutboundAcquire as A
open import ConnectionManagement.Store using (lookup)
module S = Server (λ _ → false)

world : Shared.State
world = Shared.state F.emptyCM [] [] [] [] 0 [] [] []
start : S.State
start = Data.Maybe.from-just (S.initial (O.initial (M.initial Shared.responderMode world)))
failed : S.State
failed = S.setWorld (record world { sockets = ((ident 0 , Shared.acceptPending) ∷ []) })
  (record start { stage = S.acceptForkClosing (ident 0) (errorId 7) })
closed uncertain : S.State
closed = S.setWorld (record world { sockets = ((ident 0 , Shared.closed) ∷ []) }) failed
uncertain = S.setWorld (record world { sockets = ((ident 0 , Shared.closeUncertain (errorId 8)) ∷ []) }) failed

initialized : S.initial (O.initial (M.initial Shared.responderMode world)) ≡ just start
initialized = refl
failure-enabled : S.step (S.scope (S.forkFailure (ident 0) (errorId 7))) start ≡ just failed
failure-enabled = refl
no-fabricated-birth : S.workers failed ≡ [] × Shared.admissions (S.shared failed) ≡ [] × Shared.handlers (S.shared failed) ≡ []
no-fabricated-birth = refl , refl , refl
no-propagation-before-close : S.step (S.scope S.finishForkFailure) failed ≡ nothing
no-propagation-before-close = refl
close-enabled : S.step (S.closeForkFailure nothing) failed ≡ just closed
close-enabled = refl
close-replacement : S.step (S.closeForkFailure (just (S.sync (errorId 8)))) failed ≡ just uncertain
close-replacement = refl
close-once : S.step (S.closeForkFailure nothing) closed ≡ nothing
close-once = refl
no-close-without-failure : S.step (S.closeForkFailure nothing) start ≡ nothing
no-close-without-failure = refl
no-worker-result : S.step (S.workerResult F.w₀) closed ≡ nothing
no-worker-result = refl
no-fork-while-closing : S.step (S.acceptedFork F.w₀ F.r₀) failed ≡ nothing
no-fork-while-closing = refl
propagate : S.step (S.scope S.finishForkFailure) closed ≡ just (record closed { stage = S.acceptFailed })
propagate = refl
propagate-close-failure : S.step (S.scope S.finishForkFailure) uncertain ≡ just (record uncertain { stage = S.acceptFailed })
propagate-close-failure = refl
listener-finally-separate : S.listenerOpen closed ≡ true
listener-finally-separate = refl

-- The existing accept-loop finally closes the listener only after propagation.
listener-close : S.step (S.scope S.closeListener) (record closed { stage = S.acceptFailed }) ≡
  just (record closed { stage = S.acceptBodyExited; listenerOpen = false })
listener-close = refl
owned-socket-refused : S.step (S.scope (S.forkFailure (ident 0) (errorId 7)))
  (record closed { stage = S.serving }) ≡ nothing
owned-socket-refused = refl
stopped-fork-failure-refused : S.step (S.scope (S.forkFailure (ident 1) (errorId 7)))
  (record start { stage = S.serverReturned; listenerOpen = false }) ≡ nothing
stopped-fork-failure-refused = refl


-- The shared marker protects this accepted socket across composed actors.
pending-owned : lookup (ident 0) (Shared.sockets (S.shared failed)) ≡ just Shared.acceptPending
pending-owned = refl
reuseRequest : A.Request
reuseRequest = A.acquireRequest (remote (Shared.key F.r₀)) (ident 23) (ident 0) outbound nothing
reuseFrame : A.Frame
reuseFrame = A.frame reuseRequest (A.openSocket (ident 0) (ident 0))
outbound-open-refuses-pending : A.step (ident 24) Shared.responderMode A.openOK reuseFrame (S.shared failed) ≡ nothing
outbound-open-refuses-pending = refl
-- Local permission control for the same open, before acceptance owns the slot.
isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false
outbound-open-free-slot : isJust (A.step (ident 24) Shared.responderMode A.openOK reuseFrame world) ≡ true
outbound-open-free-slot = refl
socket-released : lookup (ident 0) (Shared.sockets (S.shared closed)) ≡ just Shared.closed
socket-released = refl

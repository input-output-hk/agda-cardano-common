{-# OPTIONS --guardedness #-}

-- Finite enabled operation schedules and mutations at source-specific sites.
module ConnectionManagement.Negative.ProtocolContracts2 where
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing; Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (errorId)
open import ConnectionManagement.ProtocolContracts using (normal; synchronous; cancelled)
open import ConnectionManagement.ProtocolContracts2

run : List Action → State → Maybe State
run [] s = just s
run (a ∷ as) s with step a s
... | nothing = nothing
... | just t = run as t

-- The initiator can service work, then later see Terminate at its next legal
-- blocking request. The receive/snapshot waits do not read that control.
txClosed : State
txClosed = record initial { tc = finished normal }
tx-client-clean : run
  (start txClient ∷ await txClient channel ∷ ready txClient ∷
   blockingRequest ∷ workAvailable ∷ await txClient snapshot ∷ ready txClient ∷
   blockingRequest ∷ terminate txClient ∷ sentDone txClient ∷ cleanup txClient ∷ [])
  initial ≡ just txClosed
tx-client-clean = refl

-- The typed server only accepts Done at a blocking request with depth zero.
-- V2's park, submission and both finalizer transactions must actually return.
txV2Closed : State
txV2Closed = record initial { ts2 = finished normal }
tx-v2-clean : run
  (start txServerV2 ∷ await txServerV2 initialDelay ∷ ready txServerV2 ∷
   await txServerV2 sharedChange ∷ ready txServerV2 ∷
   await txServerV2 claimableChange ∷ ready txServerV2 ∷
   issue txServerV2 ∷ collect txServerV2 ∷
   await txServerV2 submission ∷ ready txServerV2 ∷
   blockingIds txServerV2 ∷ blockingReply txServerV2 ∷
   blockingIds txServerV2 ∷ peerDone txServerV2 ∷ retireTx ∷ cleanup txServerV2 ∷ [])
  initial ≡ just txV2Closed
tx-v2-clean = refl
tx-v1-clean : run
  (start txServerV1 ∷ issue txServerV1 ∷ collect txServerV1 ∷
   blockingIds txServerV1 ∷ peerDone txServerV1 ∷ cleanup txServerV1 ∷ [])
  initial ≡ just (record initial { ts1 = finished normal })
tx-v1-clean = refl

keepClosed : State
keepClosed = record initial { kc = finished normal }
keep-clean-alone : run
  (start keepClient ∷ ready keepClient ∷ intervalElapsed ∷ ready keepClient ∷
   terminate keepClient ∷ sentDone keepClient ∷ keepSnapshot false ∷ [])
  initial ≡ just keepClosed
keep-clean-alone = refl
keep-clean-fetch : run
  (start keepClient ∷ ready keepClient ∷ terminate keepClient ∷ sentDone keepClient ∷
   keepSnapshot true ∷ fetchCancelReceived ∷ fetchDone ∷ [])
  initial ≡ just keepClosed
keep-clean-fetch = refl
keep-server-clean : run
  (start keepServer ∷ await keepServer channel ∷ peerDone keepServer ∷ cleanup keepServer ∷ [])
  initial ≡ just (record initial { ks = finished normal })
keep-server-clean = refl

-- Exception identities are final escaping outcomes after successful observed
-- cleanup; asynchronous cancellation never becomes a synchronous protocol error.
v2-error : run
  (start txServerV2 ∷ fail txServerV2 (errorId 7) ∷ retireTx ∷ cleanup txServerV2 ∷ [])
  initial ≡ just (record initial { ts2 = finished (synchronous (errorId 7)) })
v2-error = refl
keep-cancel : run
  (start keepClient ∷ receiveCancel keepClient ∷ keepSnapshot true ∷
   fetchCancelReceived ∷ fetchDone ∷ []) initial ≡
  just (record initial { kc = finished cancelled })
keep-cancel = refl
cleanup-replacement : run
  (start txServerV2 ∷ receiveCancel txServerV2 ∷ retireTx ∷
   cleanupError txServerV2 (errorId 9) ∷ []) initial ≡
  just (record initial { ts2 = finished (synchronous (errorId 9)) })
cleanup-replacement = refl
acquisition-failure : step (acquisitionFailed keepClient cancelled) initial ≡
  just (record initial { kc = finished cancelled })
acquisition-failure = refl

control-not-at-tx-receive : step (terminate txClient)
  (record initial { tc = blocked channel }) ≡ nothing
control-not-at-tx-receive = refl
control-not-at-snapshot : step (terminate txClient)
  (record initial { tc = blocked snapshot }) ≡ nothing
control-not-at-snapshot = refl
no-initial-keep-control : step (terminate keepClient)
  (record initial { kc = blocked channel ; dq = true }) ≡ nothing
no-initial-keep-control = refl
no-responder-control : ∀ s → step (terminate txServerV2) s ≡ nothing
no-responder-control s = refl
no-blocking-request-with-pipeline : step (blockingIds txServerV2)
  (record initial { ts2 = idle ; depth2 = 1 }) ≡ nothing
no-blocking-request-with-pipeline = refl
no-peer-done-with-pipeline : step (peerDone txServerV1)
  (record initial { ts1 = idle ; depth1 = 1 }) ≡ nothing
no-peer-done-with-pipeline = refl
no-v2-cleanup-before-retirement : step (cleanup txServerV2)
  (record initial { ts2 = cleaning normal }) ≡ nothing
no-v2-cleanup-before-retirement = refl
no-keep-cleanup-shortcut : step (cleanup keepClient)
  (record initial { kc = cleaning normal ; dq = true }) ≡ nothing
no-keep-cleanup-shortcut = refl
no-done-before-receipt : step fetchDone
  (record initial { kc = keepCancel normal ; dq = true ; dying = true }) ≡ nothing
no-done-before-receipt = refl
uninterruptible-join : step (receiveCancel keepClient)
  (record initial { kc = keepJoin normal ; dq = true ; dying = true }) ≡ nothing
uninterruptible-join = refl
no-restart : step (start keepClient) keepClosed ≡ nothing
no-restart = refl
no-duplicate-done : step fetchDone keepClosed ≡ nothing
no-duplicate-done = refl

keep-cookie-error : run
  (start keepClient ∷ fail keepClient (errorId 8) ∷ keepSnapshot false ∷ []) initial ≡
  just (record initial { kc = finished (synchronous (errorId 8)) })
keep-cookie-error = refl
failed-finalizer-retains-resources : step (cleanupError keepClient (errorId 9))
  (record initial { kc = keepJoin normal ; dq = true ; dying = true }) ≡
  just (record initial { kc = finished (synchronous (errorId 9)) ; dq = true ; dying = true })
failed-finalizer-retains-resources = refl

v2-release-interruption : step (releaseCancelled txServerV2)
  (record initial { ts2 = txRetired normal }) ≡
  just (record initial { ts2 = finished cancelled })
v2-release-interruption = refl
no-keep-release-interruption : ∀ s → step (releaseCancelled keepClient) s ≡ nothing
no-keep-release-interruption s = refl

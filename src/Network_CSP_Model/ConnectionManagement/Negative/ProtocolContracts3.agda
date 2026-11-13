{-# OPTIONS --guardedness #-}

-- Enabled finite source-operation schedules; readiness/credit/depth remain inputs.
module ConnectionManagement.Negative.ProtocolContracts3 where
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (errorId)
open import ConnectionManagement.ProtocolContracts using (normal; synchronous; cancelled)
open import ConnectionManagement.ProtocolContracts3
run : List Action → State → Maybe State
run [] s = just s
run (a ∷ as) s with step a s
... | nothing = nothing
... | just t = run as t

notifyClosed : State
notifyClosed = record initial { nc = finished normal }
notify-clean : run
  (start notifyClient ∷ checkControl notifyClient ∷ await notifyClient forecast ∷
   ready notifyClient ∷ continue notifyClient ∷ issue notifyClient ∷
   checkControl notifyClient ∷ await notifyClient arrival ∷ terminate notifyClient ∷
   quitSent ∷ collect notifyClient ∷ peerDone notifyClient ∷ innerClosed notifyClient ∷
   deletePeer notifyClient ∷ refundPeer notifyClient ∷ []) initial ≡ just notifyClosed
notify-clean = refl
fetchClosed : State
fetchClosed = record initial { fc = finished normal }
fetch-clean : run
  (start fetchClient ∷ checkControl fetchClient ∷ await fetchClient command ∷
   ready fetchClient ∷ continue fetchClient ∷ issue fetchClient ∷
   await fetchClient database ∷ ready fetchClient ∷ checkControl fetchClient ∷
   noCommand ∷ collect fetchClient ∷ checkControl fetchClient ∷ continue fetchClient ∷
   issue fetchClient ∷ checkControl fetchClient ∷ terminate fetchClient ∷
   collect fetchClient ∷ doneSent fetchClient ∷ innerClosed fetchClient ∷
   deletePeer fetchClient ∷ refundPeer fetchClient ∷ []) initial ≡ just fetchClosed
fetch-clean = refl
notify-server-clean : run
  (start notifyServer ∷ issue notifyServer ∷ await notifyServer command ∷
   peerDone notifyServer ∷ collect notifyServer ∷ doneSent notifyServer ∷
   innerClosed notifyServer ∷ []) initial ≡
  just (record initial { ns = finished normal })
notify-server-clean = refl
fetch-server-clean : run
  (start fetchServer ∷ await fetchServer database ∷ ready fetchServer ∷
   await fetchServer channel ∷ peerDone fetchServer ∷ innerClosed fetchServer ∷ [])
  initial ≡ just (record initial { fs = finished normal })
fetch-server-clean = refl

-- First exit removes shared state while siblings are still running. Cleanup
-- by a later sibling is idempotent; no zero-reference-count premise is invented.
shared-first-exit : run
  (start notifyClient ∷ start fetchClient ∷ start chainClient ∷ account ∷
   fail notifyClient (errorId 7) ∷ innerClosed notifyClient ∷ deletePeer notifyClient ∷
   refundPeer notifyClient ∷ []) initial ≡ just
  (record initial { nc = finished (synchronous (errorId 7)) ; fc = idle ; cs = idle })
shared-first-exit = refl
shared-idempotent : run
  (start notifyClient ∷ start fetchClient ∷ receiveCancel notifyClient ∷
   innerClosed notifyClient ∷ deletePeer notifyClient ∷ refundPeer notifyClient ∷
   receiveCancel fetchClient ∷ innerClosed fetchClient ∷ deletePeer fetchClient ∷
   refundPeer fetchClient ∷ []) initial ≡ just
  (record initial { nc = finished cancelled ; fc = finished cancelled })
shared-idempotent = refl
-- A late starter re-creates an entry; the next exit cleans it by peer key.
straggler : run
  (start notifyClient ∷ receiveCancel notifyClient ∷ innerClosed notifyClient ∷
   deletePeer notifyClient ∷ refundPeer notifyClient ∷ start chainClient ∷ account ∷
   chainExited ∷ innerClosed chainClient ∷ deletePeer chainClient ∷ refundPeer chainClient ∷ outerClosed ∷ [])
  initial ≡ just (record initial { nc = finished cancelled ; cs = finished normal })
straggler = refl
refund-interrupted : step (releaseCancelled fetchClient)
  (record initial { fc = refunding normal ; charged = true }) ≡
  just (record initial { fc = finished cancelled ; charged = true })
refund-interrupted = refl
replacement-retains-residue : step (cleanupError notifyClient (errorId 8))
  (record initial { nc = refunding cancelled ; charged = true }) ≡
  just (record initial { nc = finished (synchronous (errorId 8)) ; charged = true })
replacement-retains-residue = refl
acquisition-failure : step (acquisitionFailed fetchClient cancelled) initial ≡
  just (record initial { fc = finished cancelled })
acquisition-failure = refl

no-done-before-quit : step (peerDone notifyClient)
  (record initial { nc = quitting }) ≡ nothing
no-done-before-quit = refl
no-notify-done-before-drain : step (peerDone notifyClient)
  (record initial { nc = draining ; nd = 1 }) ≡ nothing
no-notify-done-before-drain = refl
no-fetch-done-before-drain : step (doneSent fetchClient)
  (record initial { fc = draining ; fd = 1 }) ≡ nothing
no-fetch-done-before-drain = refl
no-server-done-before-flush : step (doneSent notifyServer)
  (record initial { ns = draining ; sd = 1 }) ≡ nothing
no-server-done-before-flush = refl
no-control-during-fetch-collect : step (terminate fetchClient)
  (record initial { fc = fetchCollect ; fd = 1 }) ≡ nothing
no-control-during-fetch-collect = refl
no-control-during-db : step (terminate fetchClient)
  (record initial { fc = blocked database }) ≡ nothing
no-control-during-db = refl
no-responder-control : ∀ s → step (terminate notifyServer) s ≡ nothing
no-responder-control s = refl
no-refund-before-delete : step (refundPeer notifyClient)
  (record initial { nc = deleting normal ; present = true ; charged = true }) ≡ nothing
no-refund-before-delete = refl
no-delete-before-writer-close : step (deletePeer fetchClient)
  (record initial { fc = innerRelease normal ; present = true }) ≡ nothing
no-delete-before-writer-close = refl
no-reaccount-after-delete : step account
  (record initial { nc = refunding normal ; charged = true }) ≡ nothing
no-reaccount-after-delete = refl
no-double-collect : step (collect fetchClient) (record initial { fc = draining }) ≡ nothing
no-double-collect = refl
no-restart : step (start notifyClient) notifyClosed ≡ nothing
no-restart = refl
no-pump-join-shortcut : step (innerClosed notifyServer)
  (record initial { ns = draining }) ≡ nothing
no-pump-join-shortcut = refl

-- Shared Leios cleanup precedes the enclosing CS candidate/sync release.
no-outer-cs-before-shared : step outerClosed
  (record initial { cs = refunding normal }) ≡ nothing
no-outer-cs-before-shared = refl
cs-shared-is-not-job-complete : step (refundPeer chainClient)
  (record initial { cs = refunding normal ; charged = true }) ≡
  just (record initial { cs = outerRelease normal })
cs-shared-is-not-job-complete = refl

writer-close-error-still-cleans-shared : step (cleanupError fetchClient (errorId 9))
  (record initial { fc = innerRelease normal ; present = true ; charged = true }) ≡
  just (record initial { fc = deleting (synchronous (errorId 9)) ; present = true ; charged = true })
writer-close-error-still-cleans-shared = refl
writer-close-cancel-still-cleans-shared : step (releaseCancelled fetchClient)
  (record initial { fc = innerRelease normal ; present = true }) ≡
  just (record initial { fc = deleting cancelled ; present = true })
writer-close-cancel-still-cleans-shared = refl

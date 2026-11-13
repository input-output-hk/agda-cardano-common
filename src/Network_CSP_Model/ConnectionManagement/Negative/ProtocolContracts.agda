{-# OPTIONS --guardedness #-}

-- Enabled paths and single-event refusal controls for the captured-peer kernel.
module ConnectionManagement.Negative.ProtocolContracts where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (errorId)
open import ConnectionManagement.ProtocolContracts

-- A successful run requires every actual dispatcher edge, with no fallback.
run : List Action → State → Maybe State
run [] s = just s
run (a ∷ as) s with step a s
... | nothing = nothing
... | just t = run as t
startup : List Action
startup = contextReady ∷ keepAliveReady ∷ registerSync ∷ registerFetch ∷ rendezvous ∷ enterCandidate ∷ []
running : State
running = state active active fresh fresh true true false true true true false true
startup-enabled : run startup initial ≡ just running
startup-enabled = refl
clean : List Action
clean = terminate chainClient 1 ∷ collect chainClient ∷ peerDone chainClient ∷ removeCandidate ∷ signalSyncDone ∷
  await fetchClient fetchWork ∷ terminate fetchClient 0 ∷ peerDone fetchClient ∷ removeFetch ∷ []
closed : State
closed = state (finished normal) (finished normal) fresh fresh true true false false false true true false
clean-enabled : run (startup ++ clean) initial ≡ just closed
clean-enabled = refl
error-path : List Action
error-path = bodyError fetchClient (errorId 7) ∷ cancelSync ∷ removeCandidate ∷ signalSyncDone ∷ removeFetch ∷ []
failed : State
failed = record closed { cs = finished cancelled ; bf = finished (synchronous (errorId 7)) }
error-cleanup-enabled : run (startup ++ error-path) initial ≡ just failed
error-cleanup-enabled = refl
servers : List Action
servers = acquireServer chainServer ∷ await chainServer follower ∷ ready chainServer ∷ peerDone chainServer ∷ serverCleanup chainServer ∷
  acquireServer fetchServer ∷ await fetchServer database ∷ ready fetchServer ∷ peerDone fetchServer ∷ serverCleanup fetchServer ∷ []
servers-enabled : run servers initial ≡ just (record initial { csr = finished normal ; bfr = finished normal })
servers-enabled = refl
syncWaiting : State
syncWaiting = record initial { cs = registered ; syncEntry = true }
no-fetch-no-candidate : step enterCandidate syncWaiting ≡ nothing
no-fetch-no-candidate = refl
no-context : step registerFetch initial ≡ nothing
no-context = refl
no-keepalive : step registerFetch (record initial { context = true }) ≡ nothing
no-keepalive = refl
no-dying-restart : step registerFetch (record initial { context = true ; keepAlive = true ; dying = true }) ≡ nothing
no-dying-restart = refl
no-duplicate-sync : step registerSync syncWaiting ≡ nothing
no-duplicate-sync = refl
no-duplicate-fetch : step registerFetch running ≡ nothing
no-duplicate-fetch = refl
no-unregistered-start : step rendezvous syncWaiting ≡ nothing
no-unregistered-start = refl
no-return-before-drain : step (peerDone chainClient) (record running { cs = draining 1 }) ≡ nothing
no-return-before-drain = refl
no-control-in-ledger-wait : step (terminate chainClient 0) (record running { cs = blocked ledger }) ≡ nothing
no-control-in-ledger-wait = refl
no-control-in-jumping-wait : step (terminate chainClient 0) (record running { cs = blocked jumping }) ≡ nothing
no-control-in-jumping-wait = refl
no-control-in-receive : step (terminate fetchClient 0) (record running { bf = blocked channel }) ≡ nothing
no-control-in-receive = refl
no-server-control : step (terminate chainServer 0) (record running { csr = active }) ≡ nothing
no-server-control = refl
no-fetch-removal-before-sync : step removeFetch (record running { bf = cleaning normal }) ≡ nothing
no-fetch-removal-before-sync = refl
no-done-before-candidate-removal : step signalSyncDone (record running { cs = cleaning normal }) ≡ nothing
no-done-before-candidate-removal = refl
no-cancel-before-cleanup : step cancelSync running ≡ nothing
no-cancel-before-cleanup = refl
sync-acquisition-interruption : step (asyncReceipt chainClient) syncWaiting ≡
  just (record syncWaiting { cs = finished cancelled ; syncEntry = false ; syncDone = true })
sync-acquisition-interruption = refl
fetchWaiting : State
fetchWaiting = record initial { context = true ; keepAlive = true ; bf = registered ; fetchEntry = true }
fetch-acquisition-interruption : step (asyncReceipt fetchClient) fetchWaiting ≡
  just (record fetchWaiting { bf = finished cancelled ; fetchEntry = false })
fetch-acquisition-interruption = refl
no-duplicate-completion : step signalSyncDone closed ≡ nothing
no-duplicate-completion = refl

cleanup-interruption-enabled : step fetchCleanupInterrupted (record running { bf = cleaning normal }) ≡
  just (record running { bf = cleaning cancelled })
cleanup-interruption-enabled = refl
cleanup-error-replaces-body-error : step (cleanupFailure chainServer (errorId 9))
  (record initial { csr = cleaning (synchronous (errorId 7)) }) ≡
  just (record initial { csr = cleaning (synchronous (errorId 9)) })
cleanup-error-replaces-body-error = refl
no-cleanup-interruption-before-cleanup : step fetchCleanupInterrupted running ≡ nothing
no-cleanup-interruption-before-cleanup = refl
no-masked-direct-body-receipt-in-cleanup : step (asyncReceipt fetchClient)
  (record running { bf = cleaning normal }) ≡ nothing
no-masked-direct-body-receipt-in-cleanup = refl

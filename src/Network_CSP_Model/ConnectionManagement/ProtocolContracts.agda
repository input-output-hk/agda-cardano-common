{-# OPTIONS --guardedness #-}

-- One captured peer/incarnation, two client brackets and two independent server
-- brackets. Readiness and exception receipt are observations, never fairness.
module ConnectionManagement.ProtocolContracts where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import ConnectionManagement.Domain using (ErrorId)

data Endpoint : Set where
  chainClient fetchClient chainServer fetchServer : Endpoint
data Wait : Set where
  ledger jumping follower fetchWork channel database : Wait
data Exit : Set where
  normal : Exit
  synchronous : ErrorId → Exit
  cancelled : Exit
data Phase : Set where
  fresh registered active : Phase
  blocked : Wait → Phase
  draining : ℕ → Phase
  cleaning : Exit → Phase
  finished : Exit → Phase

-- syncDone is the captured doneVar, retained even after syncRegistry deletion.
-- candidate covers the inner ChainSync handle/CSJ bracket; server resources
-- cover the private follower/iterator registries.
record State : Set where
  constructor state
  field cs bf csr bfr : Phase
        context keepAlive dying syncEntry fetchEntry start syncDone candidate : Bool
open State public
initial : State
initial = state fresh fresh fresh fresh false false false false false false false false
at : Endpoint → State → Phase
at chainClient = cs
at fetchClient = bf
at chainServer = csr
at fetchServer = bfr
set : Endpoint → Phase → State → State
set chainClient p s = record s { cs = p }
set fetchClient p s = record s { bf = p }
set chainServer p s = record s { csr = p }
set fetchServer p s = record s { bfr = p }

-- These input events certify the named STM/IO operation actually returned.
-- They do not allow a control read to wake a different blocked transaction.
data Action : Set where
  contextReady keepAliveReady keepAliveDying : Action
  registerSync registerFetch rendezvous enterCandidate : Action
  acquireServer : Endpoint → Action
  await : Endpoint → Wait → Action
  ready : Endpoint → Action
  terminate : Endpoint → ℕ → Action
  chainUninteresting : ℕ → Action
  collect : Endpoint → Action
  peerDone : Endpoint → Action
  bodyError : Endpoint → ErrorId → Action
  asyncReceipt : Endpoint → Action
  removeCandidate signalSyncDone removeFetch : Action
  serverCleanup : Endpoint → Action
  cleanupFailure : Endpoint → ErrorId → Action
  fetchCleanupInterrupted : Action
  cancelSync : Action

-- Only these waits belong to the respective protocol; work/ledger data is
-- abstract. Channel and DB readiness include the concrete driver operation.
waitAllowed : Endpoint → Wait → Bool
waitAllowed chainClient ledger = true
waitAllowed chainClient jumping = true
waitAllowed chainClient channel = true
waitAllowed fetchClient fetchWork = true
waitAllowed fetchClient channel = true
waitAllowed fetchClient database = true
waitAllowed chainServer follower = true
waitAllowed chainServer channel = true
waitAllowed fetchServer database = true
waitAllowed fetchServer channel = true
waitAllowed _ _ = false
isServer : Endpoint → Bool
isServer chainServer = true
isServer fetchServer = true
isServer _ = false
canExit : Phase → Bool
canExit active = true
canExit (blocked _) = true
canExit (draining _) = true
canExit _ = false

-- Error/cancellation observations include completion of inner bracket unwinds.
-- Acquisition interruption has its own onException path, without body success.
exit : Endpoint → Exit → State → Maybe State
exit chainClient e s with cs s
... | registered = just (record s { cs = finished e ; syncEntry = false ; syncDone = true })
... | active = just (set chainClient (cleaning e) s)
... | blocked _ = just (set chainClient (cleaning e) s)
... | draining _ = just (set chainClient (cleaning e) s)
... | _ = nothing
exit fetchClient e s with bf s
... | registered = just (record s { bf = finished e ; fetchEntry = false })
... | active = just (set fetchClient (cleaning e) s)
... | blocked _ = just (set fetchClient (cleaning e) s)
... | draining _ = just (set fetchClient (cleaning e) s)
... | _ = nothing
exit ep e s with canExit (at ep s)
... | true = just (set ep (cleaning e) s)
... | false = nothing

step : Action → State → Maybe State
step contextReady s with context s
... | false = just (record s { context = true })
... | true = nothing
step keepAliveReady s with keepAlive s
... | false = just (record s { keepAlive = true })
... | true = nothing
step keepAliveDying s = just (record s { dying = true })
step registerSync s with cs s | syncEntry s
... | fresh | false = just (record s { cs = registered ; syncEntry = true })
... | _ | _ = nothing
step registerFetch s with bf s | context s ∧ keepAlive s ∧ not (dying s) ∧ not (fetchEntry s)
... | fresh | true = just (record s { bf = registered ; fetchEntry = true })
... | _ | _ = nothing
step rendezvous s with cs s | bf s
... | registered | registered = just (record s { bf = active ; start = true })
... | _ | _ = nothing
step enterCandidate s with cs s | start s ∧ fetchEntry s
... | registered | true = just (record s { cs = active ; candidate = true })
... | _ | _ = nothing
step (acquireServer ep) s with isServer ep | at ep s
... | true | fresh = just (set ep active s)
... | _ | _ = nothing
step (await ep w) s with at ep s | waitAllowed ep w
... | active | true = just (set ep (blocked w) s)
... | _ | _ = nothing
step (ready ep) s with at ep s
... | blocked _ = just (set ep active s)
... | _ = nothing
step (terminate chainClient n) s with cs s
... | active = just (set chainClient (draining n) s)
... | _ = nothing
step (terminate fetchClient n) s with bf s
... | active = just (set fetchClient (draining n) s)
... | blocked fetchWork = just (set fetchClient (draining n) s)
... | _ = nothing
step (terminate _ _) s = nothing
step (chainUninteresting n) s with cs s
... | active = just (set chainClient (draining n) s)
... | _ = nothing
step (collect ep) s with at ep s
... | draining (suc n) = just (set ep (draining n) s)
... | _ = nothing
step (peerDone ep) s with at ep s | isServer ep
... | draining zero | false = just (set ep (cleaning normal) s)
... | active | true = just (set ep (cleaning normal) s)
... | _ | _ = nothing
step (bodyError ep err) s = exit ep (synchronous err) s
step (asyncReceipt ep) s = exit ep cancelled s
step removeCandidate s with cs s
... | cleaning e = just (record s { candidate = false })
... | _ = nothing
step signalSyncDone s with cs s | candidate s
... | cleaning e | false = just (record s { cs = finished e ; syncEntry = false ; syncDone = true })
... | _ | _ = nothing
step removeFetch s with bf s | syncDone s
... | cleaning e | true = just (record s { bf = finished e ; fetchEntry = false })
... | _ | _ = nothing
step (serverCleanup ep) s with isServer ep | at ep s
... | true | cleaning e = just (set ep (finished e) s)
... | _ | _ = nothing
-- Observed throwTo receipt on dieFast / expiry / exception fallback. Merely
-- entering BF cleanup does not imply a timeout or an asynchronous receipt.
step (cleanupFailure ep err) s with at ep s
... | cleaning _ = just (set ep (cleaning (synchronous err)) s)
... | _ = nothing
step fetchCleanupInterrupted s with bf s
... | cleaning _ = just (set fetchClient (cleaning cancelled) s)
... | _ = nothing
step cancelSync s with bf s
... | cleaning _ = exit chainClient cancelled s
... | _ = nothing

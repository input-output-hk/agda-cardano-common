{-# OPTIONS --guardedness #-}

-- Actual PSA monitor fork combines fresh thread names, a fresh physical handle,
-- and the exact shared CM/source lens of the original fork operation.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesForkMonitor
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain using (ident)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.OutboundKeys using (Unique)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Properties.PeerSupervisionSupply as SupplyFacts
import ConnectionManagement.Properties.PeerJobFrames as RowFacts
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesJobBirth as Birth
import ConnectionManagement.Properties.OwnedFramesThreadBirth as ThreadBirth
import ConnectionManagement.Properties.OwnedFramesPoolTransport as PoolFacts
import ConnectionManagement.Properties.OwnedFramesObservation as Observation
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module Supply = SupplyFacts isIOManagerError
  module Rows = RowFacts isIOManagerError
  module B = Birth isBearerClosed isIOManagerError
  module T = ThreadBirth isBearerClosed isIOManagerError
  module P = PoolFacts isBearerClosed isIOManagerError
  module V = Observation isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- Restoring the first looked-up binding is an exact association-store identity.
put-existing : ∀ {K V} ⦃ _ : DecEq K ⦄ (k : K) (v : V) (rows : Store K V) → lookup k rows ≡ just v → put k v rows ≡ rows
put-existing k v [] ()
put-existing k v ((q , old) ∷ rows) saved with k ≟ q
... | yes refl with just-injective saved
...   | refl = refl
put-existing k v ((q , old) ∷ rows) saved | no apart = cong ((q , old) ∷_) (put-existing k v rows saved)

-- Raw job steps never change the independent logical followup table.
job-follows : ∀ j a c {d} → Sub.advance (Sub.jobStep j a) c ≡ just d → Sub.monitors d ≡ Sub.monitors c
job-follows j a c eq with lookup j (Sub.jobs c)
... | nothing = case eq of λ ()
... | just jf with Sub.queued jf | J.step a (Sub.execution jf) (Sub.world c)
...   | false | just (next , world′) = case just-injective eq of λ { refl → refl }
...   | true | result = case eq of λ ()
...   | false | nothing = case eq of λ ()

-- The independent monitor pool refuses historical handle-identity reuse.
pool-fresh : ∀ tid p {p′} → PS.Pool.step (PS.Pool.forkConcurrent tid) p ≡ just p′ → lookup tid (PS.Pool.handles p) ≡ nothing
pool-fresh tid p eq with PS.Pool.phase p | lookup tid (PS.Pool.handles p)
... | PS.Pool.openPool | nothing = refl
... | PS.Pool.openPool | just phase = case eq of λ ()
... | PS.Pool.closing | handle = case eq of λ ()
... | PS.Pool.closedPool | handle = case eq of λ ()
... | PS.Pool.cancelPending j | handle = case eq of λ ()
... | PS.Pool.joinPending j | handle = case eq of λ ()

-- Every successful physical fork keeps the old source tables and restores its
-- parent's unchanged job row before publishing the new thread and handle.
fork-monitor : ∀ j w s {t} → PS.fork j w s ≡ just t → D.Held s → D.Held t
fork-monitor j (ident n) s eq (inv , unique , aux) with lookup j (Sub.jobs (PS.machine s)) in saved | PS.byParent j (PS.monitors s) | PS.freshWorker (ident n) s in worker-free
... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) | J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s)) |
  PS.byPeer (J.connectionRef (Sub.execution jf)) (PS.monitors s) in peer-free
...   | G.establish | J.forkMonitor | true | nothing with Sub.advance (Sub.jobStep j J.launchMonitor) (PS.machine s) in spawned |
  PS.Pool.step (PS.Pool.forkConcurrent (ident n)) (PS.monitorPool s) in forked
...     | just c′ | just p′ = case just-injective eq of λ { refl →
  subst (λ cm → Inv cm (C.capture target)) (sym source) (proj₁ carried) , subst Unique (sym source) unique , proj₂ carried }
  where
  tid = ident n
  next-thread = PS.thread (J.connectionRef (Sub.execution jf)) (ident n) j PS.created PS.observing nothing nothing
  free = B.fresh-worker (ident n) s worker-free
  fresh = pool-fresh tid (PS.monitorPool s) forked
  stable = P.B.step-stable (PS.Pool.forkConcurrent tid) (PS.monitorPool s) refl forked
  born-context = T.born-context (C.capture s) tid next-thread
  after-context = P.bg-context born-context p′
  born-inv = T.born-inv (PS.cm s) (C.capture s) tid next-thread free peer-free fresh inv
  born-aux = T.born-aux (PS.cm s) (C.capture s) tid next-thread free peer-free fresh aux
  source = Supply.sub-launch-cm j (PS.machine s) spawned
  rows = trans (Rows.fork-rows j (PS.machine s) spawned jf) (put-existing j jf (Sub.jobs (PS.machine s)) saved)
  follows = job-follows j J.launchMonitor (PS.machine s) spawned
  target = record (PS.setMachine (record c′ { jobs = put j jf (Sub.jobs c′) }) s)
    { monitorPool = p′; monitors = put tid next-thread (PS.monitors s) }
  same = V.observed-equal after-context (C.capture target) rows follows refl refl refl refl
  carried = V.observed-preserves (PS.cm s) after-context (C.capture target) same
    (P.bg-inv (PS.cm s) born-context p′ stable born-inv) (P.bg-aux born-context p′ stable born-aux)
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | nothing | any = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | just c′ | nothing = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.forget | pc | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.activate | pc | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.close | pc | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.deactivate | pc | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.begin | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.awaitAcquire | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | (J.startBundle temp ns) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | (J.publishBundle temp) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.markWarm | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.finishActivation | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.awaitHot | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.awaitAll | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.callRelease | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.awaitRelease | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.delayFailure | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | (J.awaitCold result) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | (J.complete result) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | (J.acquirePolicy fault) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | (J.nodeDelivery fault) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | (J.nodeRethrow fault) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.forkMonitor | false | peer = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | true | G.establish | J.forkMonitor | true | just peer = case eq of λ ()
fork-monitor j (ident n) s eq held | nothing | any | fresh = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | just previous | fresh = case eq of λ ()
fork-monitor j (ident n) s eq held | just jf | nothing | false = case eq of λ ()

-- The real K forkMonitor label supplies all permissions without an extra premise.
k-fork-monitor : ∀ j w s {t} → K.step (K.peerStep (PS.forkMonitor j w)) s ≡ just t → R.Reach s → R.Reach t
k-fork-monitor j w = L.peer-lift (PS.forkMonitor j w) (fork-monitor j w)

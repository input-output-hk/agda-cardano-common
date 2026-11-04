{-# OPTIONS --safe #-}

-- Fresh counterexamples distinguish drained work from delayed trace publication/delivery.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownTests where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Bool Bool as Accounting
import Cardano_network.LeiosNotifyPipeLookahead.DriverShutdown Bool Bool as Shutdown
import Cardano_network.LeiosNotifyPipeLookahead.ServerShutdown Bool as Server

-- All concrete runs retain the production next-reply contract.
module Paired = Shutdown.For S.nodeNext

-- The source registers a real response job before incrementing inFlight at Send.
registered-client : C.State
registered-client = C.client C.writingRequest C.idle (C.responseJob ∷ []) [] 0 (+ 0) false nothing

-- This zero-counter, nonempty-work state is reachable from a fresh client.
registered-reachable : C.Run C.initial (C.continue (+ 1) ∷ []) registered-client
registered-reachable = C.visible C.continueZero (C.internal C.registerResponse C.stop)

-- Corrected inventory accepts it, including the one registered pending Send.
registered-accounted : Accounting.Accounted registered-client
registered-accounted = Accounting.initial-accounted registered-reachable

-- A zero scalar counter by itself cannot justify the claim that client work is empty.
zero-counter-not-empty : Accounting.Empty registered-client → ⊥
zero-counter-not-empty empty with Accounting.jobs-empty empty
... | ()

-- Done is decoded while its server Send trace hook is still pending.
idle-before-done : D.State
idle-before-done = D.pair (C.client C.awaitDone C.idle [] [] 0 (+ 0) true (just true))
  (S.state S.doneReady 0 S.idle 0 true) [] [] nothing (just D.done) (just D.done) nothing

-- Fresh peers perform all actual shutdown work before this three-record race ends.
idle-prefix : D.Run S.nodeNext D.initial (D.clientSend D.quit ∷ D.serverRecv D.quit ∷ []) idle-before-done
idle-prefix =
  D.internal (D.clientCallback D.terminate C.stopRequested) $
  D.internal (D.clientInternal C.setStopIdle) $
  D.internal (D.commitClient C.sentQuitIdle) $
  D.visible (D.clientSent C.sentQuitIdle) $
  D.internal (D.decodeServer (S.receiveQuit S.atFirst)) $
  D.visible (D.serverReceived (S.receiveQuit S.atFirst)) $
  D.internal (D.serverInternal S.setQuit) $
  D.internal (D.serverInternal S.drained) $
  D.internal (D.commitServer S.finish) $
  D.internal (D.decodeClient C.receivedDone) D.stop

-- The client can now record Done while the server has not published Send-Done.
idle-after-done : D.State
idle-after-done = D.pair (C.client C.closed C.idle [] [] 0 (+ 0) true (just true))
  (S.state S.doneReady 0 S.idle 0 true) [] [] nothing (just D.done) nothing nothing

-- This is the actual final receive operation, not a fabricated final-state assumption.
idle-done-step : D.Step S.nodeNext idle-before-done (D.clientRecv D.done) idle-after-done
idle-done-step = D.clientReceived C.receivedDone

-- Both peers' work has completed despite that one delayed server trace hook.
idle-completed : Shutdown.Completed idle-after-done
idle-completed = Paired.client-done-completed idle-prefix idle-done-step

-- Treating every Done receive as evidence that all trace hooks are clear is false.
done-receive-has-pending-send : D.pendingServerSend idle-after-done ≢ nothing
done-receive-has-pending-send ()

-- Server Send-Done can instead precede both responder packet deliveries and client draining.
server-done-first : D.State
server-done-first = D.pair
  (C.client C.draining C.awaiting (C.quitMarker ∷ []) [] 2 (+ 0) true (just true))
  (S.state S.closed 0 S.idle 0 true) [] (D.reply S.canceled ∷ D.done ∷ []) nothing nothing nothing nothing

-- A fresh one-request pair witnesses this complementary endpoint ordering.
server-done-first-run : D.Run S.nodeNext D.initial
  (D.clientSend D.request ∷ D.serverRecv D.request ∷ D.clientSend D.quit ∷
   D.serverRecv D.quit ∷ D.serverSend (D.reply S.canceled) ∷ D.serverSend D.done ∷ []) server-done-first
server-done-first-run =
  D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.visible (D.clientSent C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.clientCallback D.terminate C.stopRequested) $
  D.internal (D.clientInternal C.setStopBusy) $
  D.internal (D.clientInternal C.registerMarker) $
  D.internal (D.commitClient C.sentQuitBusy) $
  D.visible (D.clientSent C.sentQuitBusy) $
  D.internal (D.decodeServer (S.receiveQuit S.atNext)) $
  D.visible (D.serverReceived (S.receiveQuit S.atNext)) $
  D.internal (D.serverInternal S.setQuit) $
  D.internal (D.serverInternal (S.claim refl)) $
  D.internal (D.serverInternal (S.cancel refl)) $
  D.internal (D.commitServer (S.send refl)) $
  D.visible (D.serverSent (S.send refl)) $
  D.internal (D.serverInternal (S.retire refl)) $
  D.internal (D.serverInternal S.flush) $
  D.internal (D.serverInternal S.drained) $
  D.internal (D.commitServer S.finish) $
  D.visible (D.serverSent S.finish) D.stop

-- Server Done does not establish an empty network queue or an already-drained client.
server-done-queue-not-empty : D.serverToClient server-done-first ≢ []
server-done-queue-not-empty ()

-- In particular the marker and active response receiver are still real client work.
server-done-client-not-empty : Accounting.Empty (D.clientState server-done-first) → ⊥
server-done-client-not-empty empty with Accounting.jobs-empty empty
... | ()

-- Even this unfinished client's arbitrary continuations cannot issue new requests.
no-request-after-quit : ∀ {rows t u} → D.Run S.nodeNext server-done-first rows t →
  D.Step S.nodeNext t (D.clientSend D.request) u → ⊥
no-request-after-quit run next = Shutdown.no-client-request (Paired.client-stays-stopping run refl) next

-- An attempted new normal selection after the true Quit flag is excluded.
no-new-normal-after-flag : ∀ {s t} → S.Tau s t → S.quitFlag s ≡ true →
  S.sender s ≡ S.claimed → S.sender t ≡ S.selected (S.normal true) → ⊥
no-new-normal-after-flag pr flag before after with Server.tau-new-selection pr flag before after
... | ()

{-# OPTIONS --safe #-}

-- Shutdown origin uses the server's recorded Quit and preserves zero-request late Send-Done paths.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownPrecheckTests where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownPrecheck Bool ⊤ as Shutdown

-- The client's local idle close includes its real Quit Send and final Done Receive.
client-close : List Rows.ClientRow
client-close = Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ []

-- No server record means there is no source origin for that final acknowledgment.
orphan-done : Shutdown.Pass client-close [] → ⊥
orphan-done = toWitnessFalse {a? = Shutdown.decide client-close []} tt

-- A Request Receive cannot substitute for the distinct graceful shutdown command.
request-is-not-quit : Shutdown.Pass client-close (Rows.receiveCommand D.request ∷ []) → ⊥
request-is-not-quit = toWitnessFalse {a? = Shutdown.decide client-close (Rows.receiveCommand D.request ∷ [])} tt

-- Even a Send-Done row cannot fabricate the missing server Quit Receive origin.
send-is-not-origin : Shutdown.Pass client-close (Rows.sendResponse D.done ∷ []) → ⊥
send-is-not-origin = toWitnessFalse {a? = Shutdown.decide client-close (Rows.sendResponse D.done ∷ [])} tt

-- The matching server input may end immediately after Quit, before the delayed Done Send record.
server-quit : List Rows.ServerRow
server-quit = Rows.receiveCommand D.quit ∷ []

-- This origin condition does not require publication of the corresponding Send-Done hook.
late-done-send-allowed : Shutdown.Pass client-close server-quit
late-done-send-allowed = toWitness {a? = Shutdown.decide client-close server-quit} tt

-- The ordinary zero-request Quit/Done close likewise passes without inventing request credit.
idle-close : Shutdown.Pass client-close (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ [])
idle-close = toWitness {a? = Shutdown.decide client-close
  (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ [])} tt

-- A client Quit Send prefix has not received Done, so it need not already contain any server record.
quit-prefix : Shutdown.Pass (Rows.sendCommand D.quit ∷ []) []
quit-prefix = toWitness {a? = Shutdown.decide (Rows.sendCommand D.quit ∷ []) []} tt

-- Normal/Canceled reply concerns remain separate from the shutdown-origin guard.
non-done-prefix : Shutdown.Pass (Rows.receiveResponse (D.reply S.canceled) ∷ []) []
non-done-prefix = toWitness {a? = Shutdown.decide (Rows.receiveResponse (D.reply S.canceled) ∷ []) []} tt

-- The source has completed the client while server Send-Done still occupies its actual pending slot.
late-target : D.State
late-target = D.pair (C.client C.closed C.idle [] [] 0 (+ 0) true (just tt))
  (S.state S.doneReady 0 S.idle 0 true) [] [] nothing (just D.done) nothing nothing

-- Both callback contracts admit this real fresh idle shutdown, with Receive-Done before Send-Done.
late-source : ∀ contract → D.Run contract D.initial
  (D.clientSend D.quit ∷ D.serverRecv D.quit ∷ D.clientRecv D.done ∷ []) late-target
late-source contract =
  D.internal (D.clientCallback D.terminate C.stopRequested) $
  D.internal (D.clientInternal C.setStopIdle) $
  D.internal (D.commitClient C.sentQuitIdle) $
  D.visible (D.clientSent C.sentQuitIdle) $
  D.internal (D.decodeServer (S.receiveQuit S.atFirst)) $
  D.visible (D.serverReceived (S.receiveQuit S.atFirst)) $
  D.internal (D.serverInternal S.setQuit) $
  D.internal (D.serverInternal S.drained) $
  D.internal (D.commitServer S.finish) $
  D.internal (D.decodeClient C.receivedDone) $
  D.visible (D.clientReceived C.receivedDone) D.stop

-- The theorem applies to this inhabited prefix, rather than treating guard success as a source witness.
late-source-necessary : ∀ contract → Shutdown.Pass client-close server-quit
late-source-necessary contract = Shutdown.necessary {client = client-close} {server = server-quit}
  (Rows.client (Rows.server (Rows.client Rows.empty))) (late-source contract)

-- The pending Send-Done is retained explicitly; no strict Send-before-Receive premise was introduced.
pending-done : D.pendingServerSend late-target ≡ just D.done
pending-done = refl

-- The origin refutation excludes every merge and original source schedule, independent of search behavior.
no-orphan-source : ∀ {contract events target} → Rows.Merge client-close [] events →
  D.Run contract D.initial events target → ⊥
no-orphan-source merged source = orphan-done (Shutdown.necessary merged source)

import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊥ as EmptyDriver
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊥ as EmptyRows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownPrecheck Bool ⊥ as EmptyShutdown

-- Origin necessity itself does not assume an inhabited Return type or successful global termination.
empty-return : EmptyShutdown.Pass [] []
empty-return = EmptyShutdown.necessary {contract = S.nodeNext} EmptyRows.empty EmptyDriver.stop

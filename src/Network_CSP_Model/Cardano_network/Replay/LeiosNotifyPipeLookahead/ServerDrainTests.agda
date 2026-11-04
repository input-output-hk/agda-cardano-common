{-# OPTIONS --safe #-}

-- A fresh outstanding reply, Quit marker and both server/client drain phases are inhabited.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerDrainTests where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.Nat using (_≤_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.LeiosNotifyPipeLookahead.ServerSendSlot Bool Bool as Slot
import Cardano_network.LeiosNotifyPipeLookahead.ServerDrain Bool Bool as Drain
import Cardano_network.LeiosNotifyPipeLookahead.ClientReplyAccounting Bool Bool as Reply
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Bool Bool as Work
import Cardano_network.LeiosNotifyPipeLookahead.ClientPhase Bool Bool as ClientPhase
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Bool Bool as Budget
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Bool Bool as Progress
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Bool Bool as Projection
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Bool Bool as Cost
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownTests as Fixture
import Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingTests as Finish

-- Quit has been received with one unsent reply and one dummy Quit receiver outstanding.
stopping : D.State
stopping = D.pair
  (C.client C.draining C.awaiting (C.quitMarker ∷ []) [] 2 (+ 0) true (just true))
  (S.state S.signalQuit 1 S.idle 0 false) [] [] nothing nothing nothing nothing

-- The exact fresh wire prefix contains one request and its eventual Quit.
rows : List D.Event
rows = D.clientSend D.request ∷ D.serverRecv D.request ∷
  D.clientSend D.quit ∷ D.serverRecv D.quit ∷ []

-- All source and transport operations preceding server shutdown are actual driver rules.
prefix : D.Run S.nodeNext D.initial rows stopping
prefix =
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
  D.visible (D.serverReceived (S.receiveQuit S.atNext)) D.stop

-- The universal theorem applies without assuming that this prefix will eventually finish.
server-completion : Progress.Completion S.nodeNext Drain.Closed stopping
server-completion = Drain.fresh-complete prefix (refl , refl)

-- This explicit continuation exhibits cancellation, retirement, flush and final Done.
drain : D.Run S.nodeNext stopping
  (D.serverSend (D.reply S.canceled) ∷ D.serverSend D.done ∷ []) Fixture.server-done-first
drain =
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

-- Ten actual server operations close the server while two client work items still remain.
server-operations : Budget.steps drain ≡ 10
server-operations = refl

-- The finite bound is quantitative, but it is not an exact count or a time bound.
server-budget : Budget.steps drain ≤ Cost.rank stopping
server-budget = Budget.bounded drain (refl , refl)

-- The initial work potential includes outstanding server, client and transport operations.
initial-potential : Cost.rank stopping ≡ 47
initial-potential = refl

-- The existing client continuation really reaches a completely clean paired state afterward.
client-completion : Progress.Clean Finish.closed
client-completion = Progress.clean

-- Join already checked source paths without changing any protocol operation or wire row.
append : ∀ {p s es t fs u} → D.Run p s es t → D.Run p t fs u → D.Run p s (es ++ fs) u
append D.stop suffix = suffix
append (D.internal pr run) suffix = D.internal pr (append run suffix)
append (D.visible pr run) suffix = D.visible pr (append run suffix)

-- This single fresh example also includes the subsequent reply/marker drain to full closure.
full-drain : D.Run S.nodeNext stopping
  (D.serverSend (D.reply S.canceled) ∷ D.serverSend D.done ∷
   D.clientRecv (D.reply S.canceled) ∷ D.clientRecv D.done ∷ []) Finish.closed
full-drain = append drain Finish.finish-client

-- The complete example has ten server operations followed by twelve client operations.
full-operations : Budget.steps full-drain ≡ 22
full-operations = refl

-- The entire successful continuation still fits the same initial forty-seven-credit budget.
full-budget : Budget.steps full-drain ≤ Cost.rank stopping
full-budget = Budget.bounded full-drain (refl , refl)

-- A real Quit marker contributes work but no outstanding reply of its own.
client-work : Work.work (D.clientState stopping) ≡ 2
client-work = refl

-- Only the active response receiver still needs a packet at this point.
client-replies : Reply.owed (D.clientState stopping) ≡ 1
client-replies = refl

-- Fresh source projection instantiates the universal request/reply accounting theorem.
reply-accounting : Σ[ actions ∈ List C.Action ]
  (C.Run C.initial actions (D.clientState stopping) ×
   Reply.Balanced (Reply.observe actions (Reply.counts 0 0)) (D.clientState stopping))
reply-accounting with Projection.For.client S.nodeNext prefix
... | actions , source , matching = actions , source , Reply.initial-balanced source

-- A decoded Done with an unpublished server Send is also covered by the new slot invariant.
delayed-done-slot : Slot.Consistent Fixture.idle-before-done
delayed-done-slot = Slot.initial-consistent Fixture.idle-prefix

-- Server completion alone does not close the client or deliver the queued responder packets.
server-target-not-clean : ¬ Progress.Clean Fixture.server-done-first
server-target-not-clean ()

-- An already registered response is counted before its RequestNext Send record exists.
registered-reply : Reply.Balanced (Reply.counts 0 0) Fixture.registered-client
registered-reply = Reply.initial-balanced Fixture.registered-reachable

-- Pending sends cannot refer to a different selected payload, even during shutdown.
wrong-selected-slot : Slot.Slot (S.state S.flushing 0 (S.selected (S.normal true)) 0 true)
  (just (D.reply S.canceled)) → ⊥
wrong-selected-slot ()

-- A pending Done cannot coexist with an unclaimed source job.
done-with-work-slot : Slot.Slot (S.state S.doneReady 1 S.idle 0 true) (just D.done) → ⊥
done-with-work-slot ()

-- The selected return, true stop flag and client control guards hold at the fresh drain.
client-phase : ClientPhase.Phase (D.clientState stopping)
client-phase with Projection.For.client S.nodeNext prefix
... | actions , source , matching = ClientPhase.initial-phase source

-- All fresh Await-Done states have emptied receiver work, including delayed Send schedules.
await-empty : Work.Empty (D.clientState Fixture.idle-before-done)
await-empty with Projection.For.client S.nodeNext Fixture.idle-prefix
... | actions , source , matching = ClientPhase.await-empty source refl

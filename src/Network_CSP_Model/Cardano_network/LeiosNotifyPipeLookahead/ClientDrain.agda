{-# OPTIONS --safe #-}

-- After server closure, actual remaining packets enable the complete client/marker drain.
module Cardano_network.LeiosNotifyPipeLookahead.ClientDrain
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.ClientPhase Notification Return as Phase
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification Return as Work
import Cardano_network.LeiosNotifyPipeLookahead.ClientReplyAccounting Notification Return as Reply
import Cardano_network.LeiosNotifyPipeLookahead.CommandFlow Notification Return as Command
import Cardano_network.LeiosNotifyPipeLookahead.ResponseFlow Notification Return as Response
import Cardano_network.LeiosNotifyPipeLookahead.ReplyLedger Notification Return as Ledger
open import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return
  using (Move; internal; wire; Clean; clean)

-- The exact closed server shape carries no waiting, selected or unretired source work.
server : S.State
server = S.state S.closed 0 S.idle 0 true

-- Only client/responder state remains variable after the initiator direction is settled.
pair : C.State → List D.ServerMessage → Maybe D.ClientMessage → Maybe D.ServerMessage → D.State
pair c sc pc rc = D.pair c server [] sc pc nothing rc nothing

-- Every sealed client phase has no registered RequestNext waiting for its Send record.
sealed-registration : ∀ {m pc} → Command.Seal m pc → Reply.registeredRequest m ≡ 0
sealed-registration Command.pending = refl
sealed-registration (Command.recorded Command.drain) = refl
sealed-registration (Command.recorded Command.await) = refl
sealed-registration (Command.recorded Command.closed) = refl

-- A sealed pending client Send is Quit, never another request.
sealed-request : ∀ {m pc} → Command.Seal m pc → Ledger.request pc ≡ 0
sealed-request Command.pending = refl
sealed-request (Command.recorded _) = refl

-- The universal ledger reduces to the exact remaining responder packet count after closure.
remaining-replies : (c : C.State) (sc : List D.ServerMessage) (pc : Maybe D.ClientMessage)
  (rc : Maybe D.ServerMessage) → Command.Seal (C.main c) pc → Ledger.Balanced (pair c sc pc rc) →
  Reply.owed c ≡ Ledger.reply rc + Ledger.replies sc
remaining-replies c sc pc rc seal accounted rewrite sealed-registration seal | sealed-request seal =
  trans (sym (+-identityʳ (Reply.owed c))) accounted

-- An active response receiver contributes a strictly positive wire obligation.
awaiting-positive : ∀ n → n + 1 ≡ 0 → ⊥
awaiting-positive zero ()
awaiting-positive (suc n) ()

-- A drained server cannot strand an awaiting-reply receiver before Done or an empty FIFO.
awaiting-move : ∀ {p js results n a x sc rc} →
  Response.Flow (C.client C.draining C.awaiting js results n a true (just x)) server sc nothing rc →
  Reply.responses js + 1 ≡ Ledger.reply rc + Ledger.replies sc →
  Σ[ t ∈ D.State ] Move p (pair (C.client C.draining C.awaiting js results n a true (just x)) sc nothing rc) t
awaiting-move (Response.openFlow sc ps rc sn cn) accounted = ⊥-elim (sn refl)
awaiting-move {js = js} (Response.queued Response.lastDone Response.recorded Response.vacant cn) accounted =
  ⊥-elim (awaiting-positive (Reply.responses js) accounted)
awaiting-move (Response.queued (Response.reply sc) Response.recorded Response.vacant cn) accounted =
  _ , internal (D.decodeClient (C.receivedReply refl))
awaiting-move (Response.queued sc Response.recorded Response.reply cn) accounted =
  _ , wire (D.clientReceived (C.receivedReply refl))
awaiting-move {js = js} (Response.decoded Response.recorded cn) accounted =
  ⊥-elim (awaiting-positive (Reply.responses js) accounted)
awaiting-move (Response.received Response.recorded ()) accounted

-- Actual client work either schedules locally or consumes the exact available responder packet.
draining-move : ∀ {p r js results n a x sc rc} →
  Response.Flow (C.client C.draining r js results n a true (just x)) server sc nothing rc →
  Work.Accounted (C.client C.draining r js results n a true (just x)) →
  Reply.owed (C.client C.draining r js results n a true (just x)) ≡ Ledger.reply rc + Ledger.replies sc →
  Σ[ t ∈ D.State ] Move p (pair (C.client C.draining r js results n a true (just x)) sc nothing rc) t
draining-move {n = zero} flow work accounted = _ , internal (D.clientInternal C.drained)
draining-move {results = token ∷ results} {n = suc n} flow work accounted =
  _ , internal (D.clientInternal C.drainResult)
draining-move {r = C.idle} {js = []} {results = []} {n = suc n} flow () accounted
draining-move {r = C.idle} {js = C.responseJob ∷ js} {results = []} {n = suc n} flow work accounted =
  _ , internal (D.clientInternal (C.startResponse refl))
draining-move {r = C.idle} {js = C.quitMarker ∷ js} {results = []} {n = suc n} flow work accounted =
  _ , internal (D.clientInternal (C.startMarker refl))
draining-move {r = C.awaiting} {results = []} {n = suc n} flow work accounted = awaiting-move flow accounted
draining-move {r = C.inspect msg} {results = []} {n = suc n} flow work accounted =
  _ , internal (D.clientInternal (C.discardReply refl))
draining-move {r = C.handling msg} {results = []} {n = suc n} flow work accounted =
  _ , internal (D.clientCallback D.handled (C.delivered refl))
draining-move {r = C.bumpArrival} {results = []} {n = suc n} flow work accounted =
  _ , internal (D.clientInternal (C.countArrival refl))
draining-move {r = C.publish b} {results = []} {n = suc n} flow work accounted with b
... | Data.Bool.false = _ , internal (D.clientInternal (C.publishResponse refl))
... | true = _ , internal (D.clientInternal (C.publishMarker refl))

-- With no client reply obligations left, the sealed responder FIFO exposes Done itself.
done-move : ∀ {p a x sc rc} →
  Response.Flow (C.client C.awaitDone C.idle [] [] 0 a true (just x)) server sc nothing rc →
  0 ≡ Ledger.reply rc + Ledger.replies sc →
  Σ[ t ∈ D.State ] Move p (pair (C.client C.awaitDone C.idle [] [] 0 a true (just x)) sc nothing rc) t
done-move (Response.openFlow sc ps rc sn cn) accounted = ⊥-elim (sn refl)
done-move (Response.queued Response.lastDone Response.recorded Response.vacant cn) accounted =
  _ , internal (D.decodeClient C.receivedDone)
done-move (Response.queued (Response.reply sc) Response.recorded Response.vacant cn) ()
done-move (Response.queued sc Response.recorded Response.reply cn) ()
done-move (Response.decoded Response.recorded cn) accounted = _ , wire (D.clientReceived C.receivedDone)
done-move (Response.received Response.recorded ()) accounted

-- Ordinary request/collection phases cannot inhabit the physical-Quit seal.
before-not-sealed : ∀ {m pc} → Phase.Before m → Command.Seal m pc → ⊥
before-not-sealed Phase.poll (Command.recorded ())
before-not-sealed Phase.issue (Command.recorded ())
before-not-sealed Phase.writing (Command.recorded ())
before-not-sealed Phase.maybeCollect (Command.recorded ())
before-not-sealed Phase.waitCollect (Command.recorded ())
before-not-sealed Phase.adjust (Command.recorded ())

-- All sealed client phases either are clean or have a concrete enabled driver operation.
progress : ∀ {p c sc pc rc} → Phase.Phase c → Work.Accounted c → Command.Seal (C.main c) pc →
  Response.Flow c server sc nothing rc → Ledger.Balanced (pair c sc pc rc) →
  Clean (pair c sc pc rc) ⊎ (¬ Clean (pair c sc pc rc) × Σ[ t ∈ D.State ] Move p (pair c sc pc rc) t)
progress (Phase.before pre) work seal flow accounted = ⊥-elim (before-not-sealed pre seal)
progress Phase.accepted work (Command.recorded ()) flow accounted
progress (Phase.published Phase.register) work (Command.recorded ()) flow accounted
progress (Phase.published Phase.writeIdle) work Command.pending flow accounted =
  inj₂ ((λ ()) , _ , wire (D.clientSent C.sentQuitIdle))
progress (Phase.published Phase.writeIdle) work (Command.recorded ()) flow accounted
progress (Phase.published Phase.writeBusy) work Command.pending flow accounted =
  inj₂ ((λ ()) , _ , wire (D.clientSent C.sentQuitBusy))
progress (Phase.published Phase.writeBusy) work (Command.recorded ()) flow accounted
progress {c = c} {sc = sc} {rc = rc} (Phase.published Phase.drain) work (Command.recorded Command.drain) flow accounted =
  inj₂ ((λ ()) , draining-move flow work (remaining-replies c sc nothing rc (Command.recorded Command.drain) accounted))
progress {c = c} {sc = sc} {rc = rc} (Phase.published Phase.await) work (Command.recorded Command.await) flow accounted
  with Work.empty-at-zero {c = c} work refl refl
... | Work.empty refl refl refl =
  inj₂ ((λ ()) , done-move flow (remaining-replies c sc nothing rc (Command.recorded Command.await) accounted))
progress {c = c} (Phase.published Phase.closed) work (Command.recorded Command.closed) flow accounted
  with Work.empty-at-zero {c = c} work refl refl
... | Work.empty refl refl refl with Response.client-closed {raw = pair c _ nothing _} flow refl
...   | refl , refl = inj₁ clean

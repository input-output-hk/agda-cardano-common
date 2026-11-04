{-# OPTIONS --safe #-}

-- Outstanding client reply receivers are matched by actual server/transport obligations.
module Cardano_network.LeiosNotifyPipeLookahead.ReplyLedger
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc; suc-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.ClientReplyAccounting Notification Return as Client
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Server

-- Quit is not a request and never licenses another reply.
request : Maybe D.ClientMessage → ℕ
request (just D.request) = 1
request _ = 0

-- Done is not a reply obligation; normal and Canceled each count once.
reply : Maybe D.ServerMessage → ℕ
reply (just (D.reply _)) = 1
reply _ = 0

-- Counts retain multiplicity in the actual initiator queue.
requests : List D.ClientMessage → ℕ
requests [] = 0
requests (D.request ∷ xs) = suc (requests xs)
requests (D.quit ∷ xs) = requests xs

-- Counts retain multiplicity in the actual responder queue.
replies : List D.ServerMessage → ℕ
replies [] = 0
replies (D.reply _ ∷ xs) = suc (replies xs)
replies (D.done ∷ xs) = replies xs

-- This left side corrects for replies/requests committed before their Send trace hooks.
left : D.State → ℕ
left raw = Client.owed (D.clientState raw) +
  (request (D.pendingClientSend raw) + reply (D.pendingServerSend raw))

-- Every other outstanding obligation resides at one explicit source or transport location.
right : D.State → ℕ
right raw = Client.registeredRequest (C.main (D.clientState raw)) +
  (request (D.pendingServerRecv raw) + (requests (D.clientToServer raw) +
    (S.owed (D.serverState raw) + (reply (D.pendingClientRecv raw) + replies (D.serverToClient raw)))))

-- The exact numerical ledger is independent of packet payload equality and callback data domains.
Balanced : D.State → Set
Balanced raw = left raw ≡ right raw

-- A right-associated sum exposes the finite set of independent accounting locations.
sum : List ℕ → ℕ → ℕ
sum [] n = n
sum (a ∷ xs) n = a + sum xs n

-- One added unit passes through any finite prefix of natural additions.
raise : ∀ xs n → sum xs (suc n) ≡ suc (sum xs n)
raise [] n = refl
raise (a ∷ xs) n = trans (cong (a +_) (raise xs n)) (+-suc a (sum xs n))

-- Adding one unit on both normalized sides preserves the same ledger.
increment : ∀ {a b a′ b′} → a′ ≡ suc a → b′ ≡ suc b → a ≡ b → a′ ≡ b′
increment al br eq = trans al (trans (cong suc eq) (sym br))

-- Consuming matching units preserves the ledger constructively by successor injectivity.
decrement : ∀ {a b a′ b′} → a ≡ suc a′ → b ≡ suc b′ → a ≡ b → a′ ≡ b′
decrement al br eq = suc-injective (trans (sym al) (trans eq br))

-- Appending one RequestNext adds precisely one queued request occurrence.
snoc-request : ∀ xs → requests (xs ∷ʳ D.request) ≡ suc (requests xs)
snoc-request [] = refl
snoc-request (D.request ∷ xs) = cong suc (snoc-request xs)
snoc-request (D.quit ∷ xs) = snoc-request xs

-- Appending Quit adds no reply obligation.
snoc-quit : ∀ xs → requests (xs ∷ʳ D.quit) ≡ requests xs
snoc-quit [] = refl
snoc-quit (D.request ∷ xs) = cong suc (snoc-quit xs)
snoc-quit (D.quit ∷ xs) = snoc-quit xs

-- Appending a physical response adds one reply occurrence independently of its payload.
snoc-reply : ∀ xs m → replies (xs ∷ʳ D.reply m) ≡ suc (replies xs)
snoc-reply [] m = refl
snoc-reply (D.reply _ ∷ xs) m = cong suc (snoc-reply xs m)
snoc-reply (D.done ∷ xs) m = snoc-reply xs m

-- Appending Done adds no response occurrence.
snoc-done : ∀ xs → replies (xs ∷ʳ D.done) ≡ replies xs
snoc-done [] = refl
snoc-done (D.reply _ ∷ xs) = cong suc (snoc-done xs)
snoc-done (D.done ∷ xs) = snoc-done xs

-- Client scheduling moves response jobs but never creates a fabricated wire reply.
client-tau : ∀ {c c′ s cs sc pc ps rc rs} → C.Tau c c′ →
  Balanced (D.pair c s cs sc pc ps rc rs) → Balanced (D.pair c′ s cs sc pc ps rc rs)
client-tau (C.registerResponse {js = js}) eq rewrite Client.snoc-response js = cong suc eq
client-tau C.setStopIdle eq = eq
client-tau C.setStopBusy eq = eq
client-tau (C.registerMarker {js = js}) eq rewrite Client.snoc-marker js = eq
client-tau C.optionalEmpty eq = eq
client-tau C.optionalResult eq = eq
client-tau C.blockingResult eq = eq
client-tau C.adjustArrival eq = eq
client-tau C.drainResult eq = eq
client-tau C.drained eq = eq
client-tau {pc = pc} {ps = ps} (C.startResponse {js = js} _) eq =
  trans (cong (_+ (request pc + reply ps)) (+-suc (Client.responses js) 0)) eq
client-tau (C.startMarker _) eq = eq
client-tau (C.keepReply _) eq = eq
client-tau (C.discardReply _) eq = eq
client-tau (C.countArrival _) eq = eq
client-tau (C.publishResponse _) eq = eq
client-tau (C.publishMarker _) eq = eq

-- A client RequestNext Send discharges matching pending-Send and registration corrections.
client-send : ∀ {c c′ s cs sc ps rc rs} (m : D.ClientMessage) → C.Step c (D.clientSendAction m) c′ →
  Balanced (D.pair c s cs sc (just m) ps rc rs) → Balanced (D.pair c′ s cs sc nothing ps rc rs)
client-send {ps = ps} D.request (C.sentRequest {r = r} {js = js}) eq =
  decrement (+-suc (Client.responses js + Client.awaitingReply r) (reply ps)) refl eq
client-send D.quit C.sentQuitIdle eq = eq
client-send D.quit C.sentQuitBusy eq = eq

-- Reply Receive transfers a decoded packet and its corresponding client receiver together.
client-receive : ∀ {c c′ s cs sc pc ps rs} (m : D.ServerMessage) → C.Step c (D.clientRecvAction m) c′ →
  Balanced (D.pair c s cs sc pc ps (just m) rs) → Balanced (D.pair c′ s cs sc pc ps nothing rs)
client-receive {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rs = rs}
  (D.reply _) (C.receivedReply {m = m} {js = js} _) eq = decrement
    (cong (_+ (request pc + reply ps)) (+-suc (Client.responses js) 0))
    (raise (Client.registeredRequest m ∷ request rs ∷ requests cs ∷ S.owed s ∷ []) (replies sc)) eq
client-receive D.done C.receivedDone eq = eq

-- Server reply Send consumes its pending packet correction and exact unsent source job.
server-send : ∀ {p c s s′ cs sc pc rc rs} (m : D.ServerMessage) → S.Step p s (D.serverSendAction m) s′ →
  Balanced (D.pair c s cs sc pc (just m) rc rs) → Balanced (D.pair c s′ cs sc pc nothing rc rs)
server-send {c = c} {cs = cs} {sc = sc} {pc = pc} {rc = rc} {rs = rs}
  (D.reply _) (S.send {r = r} {w = w} _) eq = decrement
    (raise (Client.owed c ∷ request pc ∷ []) 0)
    (trans (cong (λ o → Client.registeredRequest (C.main c) +
      (request rs + (requests cs + (o + (reply rc + replies sc)))) )
      (Server.finish-job (S.unregistered r) w))
      (raise (Client.registeredRequest (C.main c) ∷ request rs ∷ requests cs ∷ [])
        ((S.unregistered r + (w + 0)) + (reply rc + replies sc)))) eq
server-send D.done S.finish eq = eq

-- Receiving a request moves its unit from the pending command into server owed work.
request-right : ∀ reg queued owed rest → reg + suc (queued + (owed + rest)) ≡
  reg + (queued + (suc owed + rest))
request-right reg queued owed rest = cong (reg +_) (sym (+-suc queued (owed + rest)))

-- The reader Receive records preserve every request unit; Quit contributes none.
server-receive : ∀ {p c s s′ cs sc pc ps rc} (m : D.ClientMessage) → S.Step p s (D.serverRecvAction m) s′ →
  Balanced (D.pair c s cs sc pc ps rc (just m)) → Balanced (D.pair c s′ cs sc pc ps rc nothing)
server-receive {c = c} {cs = cs} {sc = sc} {rc = rc}
  D.request (S.receiveRequest {w = w} {s = sender} S.atFirst) eq =
  trans eq (request-right (Client.registeredRequest (C.main c)) (requests cs)
    (w + S.unsent sender) (reply rc + replies sc))
server-receive {c = c} {cs = cs} {sc = sc} {rc = rc}
  D.request (S.receiveRequest {w = w} {s = sender} S.atNext) eq =
  trans eq (request-right (Client.registeredRequest (C.main c)) (requests cs)
    (w + S.unsent sender) (reply rc + replies sc))
server-receive D.quit (S.receiveQuit S.atFirst) eq = eq
server-receive D.quit (S.receiveQuit S.atNext) eq = eq

-- The four visible record constructors preserve the ledger without assuming settled hooks.
step-balanced : ∀ {p s row t} → D.Step p s row t → Balanced s → Balanced t
step-balanced {s = D.pair c s cs sc pc ps rc rs} (D.clientSent {m = m} pr) eq =
  client-send {s = s} {cs = cs} {sc = sc} {ps = ps} {rc = rc} {rs = rs} m pr eq
step-balanced {s = D.pair c s cs sc pc ps rc rs} (D.serverSent {m = m} pr) eq =
  server-send {c = c} {cs = cs} {sc = sc} {pc = pc} {rc = rc} {rs = rs} m pr eq
step-balanced {s = D.pair c s cs sc pc ps rc rs} (D.clientReceived {m = m} pr) eq =
  client-receive {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rs = rs} m pr eq
step-balanced {s = D.pair c s cs sc pc ps rc rs} (D.serverReceived {m = m} pr) eq =
  server-receive {c = c} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rc = rc} m pr eq

-- Physical commits, decodes and source scheduling preserve the same exact units.
tau-balanced : ∀ {p s t} → D.Tau p s t → Balanced s → Balanced t
tau-balanced {s = D.pair c s cs sc pc ps rc rs} (D.clientInternal pr) eq =
  client-tau {s = s} {cs = cs} {sc = sc} {pc = pc} {ps = ps} {rc = rc} {rs = rs} pr eq
tau-balanced (D.serverInternal {c = c} {cs = cs} {sc = sc} {rc = rc} {rs = rs} pr) eq =
  trans eq (cong (λ o → Client.registeredRequest (C.main c) +
    (request rs + (requests cs + (o + (reply rc + replies sc))))) (Server.tau-balance pr))
tau-balanced (D.clientCallback D.continue C.continueZero) eq = eq
tau-balanced (D.clientCallback D.continue (C.continueBelow _)) eq = eq
tau-balanced (D.clientCallback D.continue (C.continueFull _ _)) eq = eq
tau-balanced (D.clientCallback D.terminate C.stopRequested) eq = eq
tau-balanced (D.clientCallback D.handled (C.delivered _)) eq = eq
tau-balanced (D.serverCallback (S.choose _ _)) eq = eq
tau-balanced (D.commitClient {cs = cs} {m = D.quit} C.sentQuitIdle) eq rewrite snoc-quit cs = eq
tau-balanced (D.commitClient {cs = cs} {m = D.quit} C.sentQuitBusy) eq rewrite snoc-quit cs = eq
tau-balanced (D.commitClient {c = c} {s = s} {cs = cs} {sc = sc} {ps = ps} {rc = rc} {rs = rs}
  {m = D.request} C.sentRequest) eq rewrite snoc-request cs = increment
    (+-suc (Client.owed c) (reply ps))
    (raise (1 ∷ request rs ∷ []) (requests cs + (S.owed s + (reply rc + replies sc)))) eq
tau-balanced (D.commitServer {sc = sc} {m = D.done} S.finish) eq rewrite snoc-done sc = eq
tau-balanced (D.commitServer {c = c} {s = s} {cs = cs} {sc = sc} {pc = pc} {rc = rc} {rs = rs}
  {m = D.reply msg} (S.send _)) eq rewrite snoc-reply sc msg = increment
    (raise (Client.owed c ∷ request pc ∷ []) 0)
    (raise (Client.registeredRequest (C.main c) ∷ request rs ∷ requests cs ∷ S.owed s ∷ reply rc ∷ [])
      (replies sc)) eq
tau-balanced (D.decodeClient {m = D.reply _} _) eq = eq
tau-balanced (D.decodeClient {m = D.done} _) eq = eq
tau-balanced (D.decodeServer {m = D.request} _) eq = eq
tau-balanced (D.decodeServer {m = D.quit} _) eq = eq

-- Every finite paired continuation retains the exact client/server/packet obligation balance.
run-balanced : ∀ {p s rows t} → D.Run p s rows t → Balanced s → Balanced t
run-balanced D.stop eq = eq
run-balanced (D.internal pr run) eq = run-balanced run (tau-balanced pr eq)
run-balanced (D.visible pr run) eq = run-balanced run (step-balanced pr eq)

-- Fresh reliable paired runs contain no missing or phantom reply obligations.
initial-balanced : ∀ {p rows t} → D.Run p D.initial rows t → Balanced t
initial-balanced run = run-balanced run refl

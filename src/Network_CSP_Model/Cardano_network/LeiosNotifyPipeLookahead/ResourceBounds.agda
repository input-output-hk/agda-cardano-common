{-# OPTIONS --safe #-}

-- Conservative live-resource envelopes for the fresh combined production policy.
module Cardano_network.LeiosNotifyPipeLookahead.ResourceBounds (Notification : Set) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; m≤m+n; m≤n+m; +-mono-≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification ⊤ as A
import Cardano_network.LeiosNotifyPipeLookahead.ClientReplyAccounting Notification ⊤ as R
import Cardano_network.LeiosNotifyPipeLookahead.ClientBounds Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.ReplyLedger Notification ⊤ as L
import Cardano_network.LeiosNotifyPipeLookahead.CommandFlow Notification ⊤ as Commands
import Cardano_network.LeiosNotifyPipeLookahead.ResponseFlow Notification ⊤ as Responses
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as N
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as P

-- A Maybe slot stores at most one packet even while its trace callback is delayed.
occupied : ∀ {A : Set} → Maybe A → ℕ
occupied nothing = 0
occupied (just _) = 1

-- The structural slot bound needs neither freshness nor a fairness assumption.
slot-bound : ∀ {A : Set} (slot : Maybe A) → occupied slot ≤ 1
slot-bound nothing = z≤n
slot-bound (just _) = ≤-refl

-- All four hook locations are distinct from the two packet FIFOs.
pending : D.State → ℕ
pending raw = occupied (D.pendingClientSend raw) + (occupied (D.pendingServerSend raw) +
  (occupied (D.pendingClientRecv raw) + occupied (D.pendingServerRecv raw)))

-- Four independently blocked trace hooks can retain at most four packet values.
pending-bound : ∀ raw → pending raw ≤ 4
pending-bound raw = +-mono-≤ (slot-bound (D.pendingClientSend raw)) (+-mono-≤ (slot-bound (D.pendingServerSend raw))
  (+-mono-≤ (slot-bound (D.pendingClientRecv raw)) (slot-bound (D.pendingServerRecv raw))))

-- Quit cannot inflate a request-only obligation count.
request-bound : ∀ slot → L.request slot ≤ 1
request-bound nothing = z≤n
request-bound (just D.request) = ≤-refl
request-bound (just D.quit) = z≤n

-- Done similarly contributes no reply obligation.
reply-bound : ∀ slot → L.reply slot ≤ 1
reply-bound nothing = z≤n
reply-bound (just (D.reply _)) = ≤-refl
reply-bound (just D.done) = z≤n

-- Ordinary command queues consist entirely of counted RequestNext packets.
requests-length : ∀ {xs} → Commands.Requests xs → length xs ≡ L.requests xs
requests-length Commands.nil = refl
requests-length (Commands.request rest) rewrite requests-length rest = refl

-- A sealed command queue adds exactly its single final Quit.
quit-length : ∀ {xs} → Commands.QuitQueue xs → length xs ≡ suc (L.requests xs)
quit-length Commands.lastQuit = refl
quit-length (Commands.request rest) rewrite quit-length rest = refl

-- Every fresh command FIFO has at most one packet outside request accounting.
command-length : ∀ {c s cs pc rs} → Commands.Flow c s cs pc rs → length cs ≤ suc (L.requests cs)
command-length (Commands.openFlow _ xs _ _) rewrite requests-length xs = m≤n⇒m≤1+n ≤-refl
command-length (Commands.queued xs _ _ _) rewrite quit-length xs = ≤-refl
command-length (Commands.decoded _ _) = z≤n
command-length (Commands.received _ _) = z≤n

-- Ordinary responder queues consist entirely of counted normal/Canceled replies.
replies-length : ∀ {xs} → Responses.Replies xs → length xs ≡ L.replies xs
replies-length Responses.nil = refl
replies-length (Responses.reply rest) rewrite replies-length rest = refl

-- A sealed responder queue adds exactly its single final Done.
done-length : ∀ {xs} → Responses.DoneQueue xs → length xs ≡ suc (L.replies xs)
done-length Responses.lastDone = refl
done-length (Responses.reply rest) rewrite done-length rest = refl

-- Every fresh response FIFO has at most one packet outside reply accounting.
response-length : ∀ {c s sc ps rc} → Responses.Flow c s sc ps rc → length sc ≤ suc (L.replies sc)
response-length (Responses.openFlow xs _ _ _ _) rewrite replies-length xs = m≤n⇒m≤1+n ≤-refl
response-length (Responses.queued xs _ _ _) rewrite done-length xs = ≤-refl
response-length (Responses.decoded _ _) = z≤n
response-length (Responses.received _ _) = z≤n

-- A component bound can pass through any nonnegative prefix of a natural sum.
under-prefix : ∀ a {b c} → b ≤ c → b ≤ a + c
under-prefix a pr = ≤-trans pr (m≤n+m _ a)

-- The exact ledger bounds every outstanding resource on its right-hand side.
ledger-parts : ∀ raw → (L.requests (D.clientToServer raw) ≤ L.right raw) ×
  (S.owed (D.serverState raw) ≤ L.right raw) × (L.replies (D.serverToClient raw) ≤ L.right raw)
ledger-parts (D.pair c s cs sc pc ps rc rs) =
  under-prefix reg (under-prefix received (m≤m+n _ _)) ,
  under-prefix reg (under-prefix received (under-prefix queued (m≤m+n _ _))) ,
  under-prefix reg (under-prefix received (under-prefix queued (under-prefix owed (m≤n+m _ _))))
  where
  -- These names expose the right-associated ledger rather than normalizing whole peers.
  reg = R.registeredRequest (C.main c)
  -- Pending server Receive contributes one counted command.
  received = L.request rs
  -- The command FIFO contributes its counted requests.
  queued = L.requests cs
  -- The server itself retains the remaining source obligations.
  owed = S.owed s

-- Client obligations plus the two delayed Send corrections give a safe envelope.
left-bound : ∀ raw → A.work (D.clientState raw) ≤ 1001 → L.left raw ≤ 1003
left-bound raw work = +-mono-≤ (≤-trans (Client.owed≤work (D.clientState raw)) work)
  (+-mono-≤ (request-bound (D.pendingClientSend raw)) (reply-bound (D.pendingServerSend raw)))

-- Waiting jobs are a subset of the server's unfulfilled reply obligations.
waiting≤owed : ∀ s → S.waiting s ≤ S.owed s
waiting≤owed s = under-prefix (S.unregistered (S.reader s)) (m≤m+n _ _)

-- These are conservative bounds, not claims of minimal capacities or byte usage.
record Bounds (raw : D.State) : Set where
  constructor bounds
  field
    client-work : A.work (D.clientState raw) ≤ 1001
    server-owed : S.owed (D.serverState raw) ≤ 1003
    server-waiting : S.waiting (D.serverState raw) ≤ 1003
    command-packets : length (D.clientToServer raw) ≤ 1004
    response-packets : length (D.serverToClient raw) ≤ 1004
    pending-packets : pending raw ≤ 4
open Bounds public

-- Exact packet languages supply the one Quit/Done omitted by the numerical ledger.
assemble : ∀ raw → A.work (D.clientState raw) ≤ 1001 → L.Balanced raw →
  Commands.Consistent raw → Responses.Consistent raw → Bounds raw
assemble raw work balanced commands responses = bounds work server
  (≤-trans (waiting≤owed (D.serverState raw)) server)
  (≤-trans (command-length commands) (s≤s queued))
  (≤-trans (response-length responses) (s≤s replies))
  (pending-bound raw)
  where
  -- Equality transports the client-side envelope to the server/transport side.
  right : L.right raw ≤ 1003
  right = subst (_≤ 1003) balanced (left-bound raw work)
  -- Each counted queue is independently bounded by the same nonnegative total.
  queued = ≤-trans (proj₁ (ledger-parts raw)) right
  -- A source obligation is one component of the same ledger.
  server = ≤-trans (proj₁ (proj₂ (ledger-parts raw))) right
  -- The responder FIFO is another component of that ledger.
  replies = ≤-trans (proj₂ (proj₂ (ledger-parts raw))) right

-- Both live and failed node-client views retain their actual resource state.
client-view : ∀ t → Client.Invariant (N.clientView t) →
  Client.Bound (D.clientState (N.driverState t)) × A.Accounted (D.clientState (N.driverState t))
client-view (N.nodeDriver raw q true forecast stop) inv = inv
client-view (N.nodeDriver raw q false forecast stop) inv = inv

-- The production policy discharges all bound, ledger and packet-language premises.
initial-bounds : ∀ {actions t} → N.Run N.initial actions t → Bounds (N.driverState t)
initial-bounds {t = t} trace with P.client trace
... | inputs , source with client-view t (Client.initial-invariant source)
... | bound , accounted = assemble (N.driverState t) (Client.work-bound {c = D.clientState (N.driverState t)} bound accounted)
  (L.initial-balanced (P.driver trace)) (Commands.initial-consistent (P.driver trace))
  (Responses.initial-consistent (P.driver trace))

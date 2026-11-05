{-# OPTIONS --safe #-}

-- Prefix-count bounds for physical queues reuse the exact payload conservation theorem.
module Cardano_network.LeiosNotifyPipeLookahead.DriverPrefixBoundsQueues
  (Notification Return : Set) where

open import Data.Nat using (ℕ; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; ≤-reflexive; ≤-trans; m≤n+m; m≤m+n; +-mono-≤; ≤-refl)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.List.Properties using (length-++)
open import Data.Maybe using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification Return as B
open import Cardano_network.LeiosNotifyPipeLookahead.DriverPrefixBounds Notification Return

-- List representation and numeric occupancy describe the very same pending packet.
pending-size : ∀ {A : Set} (slot : Maybe A) → length (B.Packet.pending A slot) ≡ occupied slot
pending-size nothing = refl
pending-size (just _) = refl

-- Taking lengths preserves exact conservation without re-normalizing driver processes.
packet-size : ∀ {A : Set} (sent received : List A) (ps pr : Maybe A) (queue : List A) →
  B.Packet.Balance A sent received ps pr queue →
  length sent + occupied ps ≡ length received + (occupied pr + length queue)
packet-size sent received ps pr queue equal =
  trans (cong (length sent +_) (sym (pending-size ps)))
    (trans (sym (length-++ sent))
      (trans (cong length equal)
        (trans (length-++ received)
          (cong (length received +_)
            (trans (length-++ (B.Packet.pending _ pr))
              (cong (_+ length queue) (pending-size pr)))))))

-- Move a single row contribution past the remaining prefix count.
swap-prefix : ∀ a b c → a + (b + c) ≡ (b + a) + c
swap-prefix a b c = trans (sym (+-assoc a b c)) (cong (_+ c) (+-comm a b))

-- History length and row counting agree even with an arbitrary historical accumulator.
module HistoryLength (hook : Hook) (measure : B.History → ℕ)
  (advance-law : ∀ e past → measure (B.advance e past) ≡ Hook.row hook e + measure past) where
  module Count = Tally hook

  -- Folding records keeps exact occurrence counts, including repeated payloads.
  accumulated : ∀ es past → measure (B.observe es past) ≡ Count.rows es + measure past
  accumulated [] past = refl
  accumulated (e ∷ es) past = trans (accumulated es (B.advance e past))
    (trans (cong (Count.rows es +_) (advance-law e past))
      (swap-prefix (Count.rows es) (Hook.row hook e) (measure past)))

  -- Empty history removes the accumulator correction at a fresh session boundary.
  fresh : measure B.empty ≡ 0 → ∀ es → measure (B.observe es B.empty) ≡ Count.rows es
  fresh empty-zero es = trans (accumulated es B.empty)
    (trans (cong (Count.rows es +_) empty-zero) (+-identityʳ (Count.rows es)))

-- Appending the corresponding record increments this endpoint history exactly once.
clientSend-advance : ∀ e past → length (B.clientSends (B.advance e past)) ≡
  clientSendRow e + length (B.clientSends past)
clientSend-advance (D.clientSend m) past = trans (length-++ (B.clientSends past)) (+-comm _ 1)
clientSend-advance (D.serverSend m) past = refl
clientSend-advance (D.clientRecv m) past = refl
clientSend-advance (D.serverRecv m) past = refl

-- Instantiate history/row agreement for the clientSend endpoint.
module ClientSendHistory = HistoryLength clientSendHook (λ h → length (B.clientSends h)) clientSend-advance

-- Appending the corresponding record increments this endpoint history exactly once.
serverSend-advance : ∀ e past → length (B.serverSends (B.advance e past)) ≡
  serverSendRow e + length (B.serverSends past)
serverSend-advance (D.clientSend m) past = refl
serverSend-advance (D.serverSend m) past = trans (length-++ (B.serverSends past)) (+-comm _ 1)
serverSend-advance (D.clientRecv m) past = refl
serverSend-advance (D.serverRecv m) past = refl

-- Instantiate history/row agreement for the serverSend endpoint.
module ServerSendHistory = HistoryLength serverSendHook (λ h → length (B.serverSends h)) serverSend-advance

-- Appending the corresponding record increments this endpoint history exactly once.
serverRecv-advance : ∀ e past → length (B.serverReceives (B.advance e past)) ≡
  serverRecvRow e + length (B.serverReceives past)
serverRecv-advance (D.clientSend m) past = refl
serverRecv-advance (D.serverSend m) past = refl
serverRecv-advance (D.clientRecv m) past = refl
serverRecv-advance (D.serverRecv m) past = trans (length-++ (B.serverReceives past)) (+-comm _ 1)

-- Instantiate history/row agreement for the serverRecv endpoint.
module ServerRecvHistory = HistoryLength serverRecvHook (λ h → length (B.serverReceives h)) serverRecv-advance

-- Appending the corresponding record increments this endpoint history exactly once.
clientRecv-advance : ∀ e past → length (B.clientReceives (B.advance e past)) ≡
  clientRecvRow e + length (B.clientReceives past)
clientRecv-advance (D.clientSend m) past = refl
clientRecv-advance (D.serverSend m) past = refl
clientRecv-advance (D.clientRecv m) past = trans (length-++ (B.clientReceives past)) (+-comm _ 1)
clientRecv-advance (D.serverRecv m) past = refl

-- Instantiate history/row agreement for the clientRecv endpoint.
module ClientRecvHistory = HistoryLength clientRecvHook (λ h → length (B.clientReceives h)) clientRecv-advance

-- The command FIFO and pending server Receive are covered by actual client Send rows.
commands-exact : ∀ {p es t} (run : D.Run p D.initial es t) →
  ClientSend.rows es + occupied (D.pendingClientSend t) ≡
  ServerRecv.rows es + (occupied (D.pendingServerRecv t) + length (D.clientToServer t))
commands-exact {es = es} {t = t} run =
  trans (sym (cong₂ _+_ (ClientSendHistory.fresh refl es) refl))
    (trans (packet-size (B.clientSends (B.observe es B.empty))
      (B.serverReceives (B.observe es B.empty))
      (D.pendingClientSend t) (D.pendingServerRecv t) (D.clientToServer t)
      (B.to-server (B.initial-conservation run)))
      (cong₂ _+_ (ServerRecvHistory.fresh refl es) refl))

-- The reverse equation retains all normal, Canceled and Done packet occurrences.
responses-exact : ∀ {p es t} (run : D.Run p D.initial es t) →
  ServerSend.rows es + occupied (D.pendingServerSend t) ≡
  ClientRecv.rows es + (occupied (D.pendingClientRecv t) + length (D.serverToClient t))
responses-exact {es = es} {t = t} run =
  trans (sym (cong₂ _+_ (ServerSendHistory.fresh refl es) refl))
    (trans (packet-size (B.serverSends (B.observe es B.empty))
      (B.clientReceives (B.observe es B.empty))
      (D.pendingServerSend t) (D.pendingClientRecv t) (D.serverToClient t)
      (B.to-client (B.initial-conservation run)))
      (cong₂ _+_ (ClientRecvHistory.fresh refl es) refl))

-- Every client physical commit is either already decoded or still in the command FIFO.
client-commits-exact : ∀ {p es t} (run : D.Run p D.initial es t) →
  ClientSend.operations run ≡ ServerRecv.operations run + length (D.clientToServer t)
client-commits-exact {es = es} {t = t} run = trans (clientSend-exact run)
  (trans (commands-exact run)
    (trans (sym (+-assoc (ServerRecv.rows es) (occupied (D.pendingServerRecv t)) _))
      (cong (_+ length (D.clientToServer t)) (sym (serverRecv-exact run)))))

-- Every server physical commit is decoded or remains queued, even if Send is unrecorded.
server-commits-exact : ∀ {p es t} (run : D.Run p D.initial es t) →
  ServerSend.operations run ≡ ClientRecv.operations run + length (D.serverToClient t)
server-commits-exact {es = es} {t = t} run = trans (serverSend-exact run)
  (trans (responses-exact run)
    (trans (sym (+-assoc (ClientRecv.rows es) (occupied (D.pendingClientRecv t)) _))
      (cong (_+ length (D.serverToClient t)) (sym (clientRecv-exact run)))))

-- Decoded-but-unrecorded commands plus the remaining FIFO fit in the input-prefix envelope.
commands-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  occupied (D.pendingServerRecv t) + length (D.clientToServer t) ≤ ClientSend.rows es + 1
commands-bound {es = es} {t = t} run =
  ≤-trans (m≤n+m _ (ServerRecv.rows es))
    (≤-trans (≤-reflexive (trans (sym (commands-exact run)) (sym (clientSend-exact run))))
      (clientSend-bound run))

-- The same envelope holds independently for decoded and queued replies/Done.
responses-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  occupied (D.pendingClientRecv t) + length (D.serverToClient t) ≤ ServerSend.rows es + 1
responses-bound {es = es} {t = t} run =
  ≤-trans (m≤n+m _ (ClientRecv.rows es))
    (≤-trans (≤-reflexive (trans (sym (responses-exact run)) (sym (serverSend-exact run))))
      (serverSend-bound run))

-- Total command decodes cannot exceed commits, hence the client Send prefix plus one.
server-decodes-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  ServerRecv.operations run ≤ ClientSend.rows es + 1
server-decodes-bound run = ≤-trans (m≤m+n _ _)
  (≤-trans (≤-reflexive (sym (client-commits-exact run))) (clientSend-bound run))

-- Reply/Done decodes are similarly bounded by actual server Send rows plus one.
client-decodes-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  ClientRecv.operations run ≤ ServerSend.rows es + 1
client-decodes-bound run = ≤-trans (m≤m+n _ _)
  (≤-trans (≤-reflexive (sym (server-commits-exact run))) (serverSend-bound run))

-- Any selected row counter with contributions at most one fits within the input length.
rows-length : (hook : Hook) → (∀ e → Hook.row hook e ≤ 1) →
  ∀ es → Tally.rows hook es ≤ length es
rows-length hook one [] = z≤n
rows-length hook one (e ∷ es) = +-mono-≤ (one e) (rows-length hook one es)

-- A concrete input record contributes at most one client Send occurrence.
client-row-bound : ∀ e → clientSendRow e ≤ 1
client-row-bound (D.clientSend _) = s≤s z≤n
client-row-bound (D.serverSend _) = z≤n
client-row-bound (D.clientRecv _) = z≤n
client-row-bound (D.serverRecv _) = z≤n

-- A concrete input record contributes at most one server Send occurrence.
server-row-bound : ∀ e → serverSendRow e ≤ 1
server-row-bound (D.clientSend _) = z≤n
server-row-bound (D.serverSend _) = s≤s z≤n
server-row-bound (D.clientRecv _) = z≤n
server-row-bound (D.serverRecv _) = z≤n

-- Every physical client commit fits in the finite input length plus one pending Send.
client-commits-input-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  ClientSend.operations run ≤ length es + 1
client-commits-input-bound {es = es} run = ≤-trans (clientSend-bound run)
  (+-mono-≤ (rows-length clientSendHook client-row-bound es) ≤-refl)

-- The reverse physical commits obey the same bound independently of payload choice.
server-commits-input-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  ServerSend.operations run ≤ length es + 1
server-commits-input-bound {es = es} run = ≤-trans (serverSend-bound run)
  (+-mono-≤ (rows-length serverSendHook server-row-bound es) ≤-refl)

-- The entire command transport/decode buffer is bounded by the supplied input prefix.
commands-input-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  occupied (D.pendingServerRecv t) + length (D.clientToServer t) ≤ length es + 1
commands-input-bound {es = es} run = ≤-trans (commands-bound run)
  (+-mono-≤ (rows-length clientSendHook client-row-bound es) ≤-refl)

-- The reverse transport/decode buffer also has an actual-run input-length envelope.
responses-input-bound : ∀ {p es t} (run : D.Run p D.initial es t) →
  occupied (D.pendingClientRecv t) + length (D.serverToClient t) ≤ length es + 1
responses-input-bound {es = es} run = ≤-trans (responses-bound run)
  (+-mono-≤ (rows-length serverSendHook server-row-bound es) ≤-refl)

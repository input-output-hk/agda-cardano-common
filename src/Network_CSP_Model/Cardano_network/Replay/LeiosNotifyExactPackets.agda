{-# OPTIONS --guardedness #-}

-- Full native FIFO packets observed at every retained Notify summary field.
open import Cardano_network.Replay.LeiosNotifyExactParams renaming (exactParams to p)
module Cardano_network.Replay.LeiosNotifyExactPackets where

open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; mapMaybe)
open import Data.List.Properties using (mapMaybe-++)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; trans)
open import Class.DecEq using (_≟_)
open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p using (LNPEv; sendLNP; receiveLNP; apiLPev; doneLNP)
open import Cardano_network.Replay.LeiosNotifyPairedModel p
open import Cardano_network.Replay.LeiosNotifyPairedTrace p using (ClientQueues; stopC; stepC; ServerQueues; stopS; stepS)
open import Cardano_network.Replay.Common
import Cardano_network.Replay.LeiosNotifyPipeline as N
open import Cardano_network.Replay.LeiosNotifyExactObservation using (canonical) renaming (classify to cls)
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as Local

-- Packet observation retains full payloads, unlike the final replay classifier.
Packet : Set
Packet = Direction × Payload

-- Only application events are erased at this intermediate observation boundary.
packet : Local.Event → Maybe Packet
packet (Local.evLabel _ (sendLNP _ _) x) = just (Send , x)
packet (Local.evLabel _ (receiveLNP _ _) x) = just (Recv , x)
packet _ = nothing

-- The exact packet sequence of an original peer trace.
packets : List Local.Event → List Packet
packets = mapMaybe packet

-- Evaluate one packet with the client queue orientation.
clientPacket : Packet → Queues → Maybe Queues
clientPacket (Send , x) (queues cs sc) = just (queues (cs ∷ʳ x) sc)
clientPacket (Recv , x) (queues cs []) = nothing
clientPacket (Recv , x) (queues cs (y ∷ ys)) with x ≟ y
... | yes _ = just (queues cs ys)
... | no _ = nothing

-- The server packet orientation exchanges the two queues.
serverPacket : Packet → Queues → Maybe Queues
serverPacket (Send , x) (queues cs sc) = just (queues cs (sc ∷ʳ x))
serverPacket (Recv , x) (queues [] sc) = nothing
serverPacket (Recv , x) (queues (y ∷ ys) sc) with x ≟ y
... | yes _ = just (queues ys sc)
... | no _ = nothing

-- The concrete receive gate and packet evaluator make identical decisions.
recv-client : ∀ l d x q → clientGate (Local.evLabel _ (receiveLNP l d) x) q ≡ clientPacket (Recv , x) q
recv-client l d x (queues cs []) = refl
recv-client l d x (queues cs (y ∷ ys)) with x ≟ y
... | yes _ = refl
... | no _ = refl

-- The same identity for the server's opposite receive direction.
recv-server : ∀ l d x q → serverGate (Local.evLabel _ (receiveLNP l d) x) q ≡ serverPacket (Recv , x) q
recv-server l d x (queues [] sc) = refl
recv-server l d x (queues (y ∷ ys) sc) with x ≟ y
... | yes _ = refl
... | no _ = refl

-- A packet trace records every successful concrete client gate update.
data ClientPackets : Queues → List Packet → Queues → Set where
  nilC : ∀ {q} → ClientPackets q [] q
  consC : ∀ {q q′ q″ e t} → clientPacket e q ≡ just q′ →
    ClientPackets q′ t q″ → ClientPackets q (e ∷ t) q″

-- Server packet traces use the same exact-payload discipline.
data ServerPackets : Queues → List Packet → Queues → Set where
  nilS : ∀ {q} → ServerPackets q [] q
  consS : ∀ {q q′ q″ e t} → serverPacket e q ≡ just q′ →
    ServerPackets q′ t q″ → ServerPackets q (e ∷ t) q″

-- Restore application-only events without inventing network transitions.
expand-client : ∀ t {q q′} → ClientPackets q (packets t) q′ → ClientQueues q t q′
expand-client [] nilC = stopC
expand-client (Local.evLabel _ (sendLNP _ _) x ∷ t) (consC eq run) = stepC eq (expand-client t run)
expand-client (Local.evLabel _ (receiveLNP l d) x ∷ t) {q} (consC eq run) =
  stepC (trans (recv-client l d x q) eq) (expand-client t run)
expand-client (Local.evLabel _ (apiLPev _ _ _) x ∷ t) run = stepC refl (expand-client t run)
expand-client (Local.evLabel _ (doneLNP _ _) x ∷ t) run = stepC refl (expand-client t run)

-- Restore the server's application handoffs at their original trace positions.
expand-server : ∀ t {q q′} → ServerPackets q (packets t) q′ → ServerQueues q t q′
expand-server [] nilS = stopS
expand-server (Local.evLabel _ (sendLNP _ _) x ∷ t) (consS eq run) = stepS eq (expand-server t run)
expand-server (Local.evLabel _ (receiveLNP l d) x ∷ t) {q} (consS eq run) =
  stepS (trans (recv-server l d x q) eq) (expand-server t run)
expand-server (Local.evLabel _ (apiLPev _ _ _) x ∷ t) run = stepS refl (expand-server t run)
expand-server (Local.evLabel _ (doneLNP _ _) x ∷ t) run = stepS refl (expand-server t run)

-- A local macro containing one exact packet lifts whenever that packet passes.
one-client : ∀ t {e q q′} → packets t ≡ e ∷ [] → clientPacket e q ≡ just q′ → ClientQueues q t q′
one-client t eq gate = expand-client t (subst (λ es → ClientPackets _ es _) (sym eq) (consC gate nilC))

-- The symmetric exact-packet lifting obligation for the server.
one-server : ∀ t {e q q′} → packets t ≡ e ∷ [] → serverPacket e q ≡ just q′ → ServerQueues q t q′
one-server t eq gate = expand-server t (subst (λ es → ServerPackets _ es _) (sym eq) (consS gate nilS))

-- Foreign payloads have no Notify summary observation.
payloadMessage : Payload → Maybe N.Msg
payloadMessage (_ , _ , _ , leiosNotifyP m) = just (canonical m)
payloadMessage _ = nothing

-- Abstract a concrete FIFO by retaining only its Notify summary kinds.
queue : List Payload → List N.Msg
queue = mapMaybe payloadMessage

-- Packet classification agrees with the existing local replay observation.
packetMessage : Packet → Maybe N.E
packetMessage (d , x) = map (d ,_) (payloadMessage x)

-- The abstract medium action, independently of either local protocol state.
data BufferStep : Role → List N.Msg → List N.Msg → Maybe N.E →
  List N.Msg → List N.Msg → Set where
  unchanged : ∀ {r cs sc} → BufferStep r cs sc nothing cs sc
  sentC : ∀ {cs sc m} → BufferStep client cs sc (just (Send , m)) (cs ∷ʳ m) sc
  recvC : ∀ {cs sc m} → BufferStep client cs (m ∷ sc) (just (Recv , m)) cs sc
  sentS : ∀ {cs sc m} → BufferStep server cs sc (just (Send , m)) cs (sc ∷ʳ m)
  recvS : ∀ {cs sc m} → BufferStep server (m ∷ cs) sc (just (Recv , m)) cs sc

-- Sending one packet appends precisely its retained observation, if any.
queue-snoc : ∀ xs x → queue (xs ∷ʳ x) ≡ queue xs ++ queue (x ∷ [])
queue-snoc xs x = mapMaybe-++ payloadMessage xs (x ∷ [])

-- A successful concrete client packet induces the corresponding abstract move.
client-packet-sound : ∀ e {q q′} → clientPacket e q ≡ just q′ →
  BufferStep client (queue (clientToServer q)) (queue (serverToClient q)) (packetMessage e)
    (queue (clientToServer q′)) (queue (serverToClient q′))
client-packet-sound (Send , x) {queues cs sc} refl rewrite queue-snoc cs x with payloadMessage x
... | just m = sentC
... | nothing rewrite Data.List.Properties.++-identityʳ (queue cs) = unchanged
client-packet-sound (Recv , x) {queues cs []} ()
client-packet-sound (Recv , x) {queues cs (y ∷ ys)} eq with x ≟ y
... | no _ with () ← eq
... | yes refl with just-injective eq
...   | refl with payloadMessage x
...     | just m = recvC
...     | nothing = unchanged

-- The concrete server gate has the opposite abstract FIFO orientation.
server-packet-sound : ∀ e {q q′} → serverPacket e q ≡ just q′ →
  BufferStep server (queue (clientToServer q)) (queue (serverToClient q)) (packetMessage e)
    (queue (clientToServer q′)) (queue (serverToClient q′))
server-packet-sound (Send , x) {queues cs sc} refl rewrite queue-snoc sc x with payloadMessage x
... | just m = sentS
... | nothing rewrite Data.List.Properties.++-identityʳ (queue sc) = unchanged
server-packet-sound (Recv , x) {queues [] sc} ()
server-packet-sound (Recv , x) {queues (y ∷ ys) sc} eq with x ≟ y
... | no _ with () ← eq
... | yes refl with just-injective eq
...   | refl with payloadMessage x
...     | just m = recvS
...     | nothing = unchanged

-- Lift the client packet result to every concrete local event, including APIs.
client-gate-sound : ∀ e {q q′} → clientGate e q ≡ just q′ →
  BufferStep client (queue (clientToServer q)) (queue (serverToClient q)) (cls e)
    (queue (clientToServer q′)) (queue (serverToClient q′))
client-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , leiosNotifyP m)) {q} {q′} eq = client-packet-sound (Send , x) {q = q} {q′ = q′} eq
client-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , keepAlive m)) {q} {q′} eq = client-packet-sound (Send , x) {q = q} {q′ = q′} eq
client-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , blockFetch m)) {q} {q′} eq = client-packet-sound (Send , x) {q = q} {q′ = q′} eq
client-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , txSubmission m)) {q} {q′} eq = client-packet-sound (Send , x) {q = q} {q′ = q′} eq
client-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , leiosNotify m)) {q} {q′} eq = client-packet-sound (Send , x) {q = q} {q′ = q′} eq
client-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , leiosFetch m)) {q} {q′} eq = client-packet-sound (Send , x) {q = q} {q′ = q′} eq
client-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , chainSync m)) {q} {q′} eq = client-packet-sound (Send , x) {q = q} {q′ = q′} eq
client-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , leiosFetchP m)) {q} {q′} eq = client-packet-sound (Send , x) {q = q} {q′ = q′} eq
client-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , leiosNotifyP m)) {q} {q′} eq = client-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-client l d x q)) eq)
client-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , keepAlive m)) {q} {q′} eq = client-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-client l d x q)) eq)
client-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , blockFetch m)) {q} {q′} eq = client-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-client l d x q)) eq)
client-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , txSubmission m)) {q} {q′} eq = client-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-client l d x q)) eq)
client-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , leiosNotify m)) {q} {q′} eq = client-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-client l d x q)) eq)
client-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , leiosFetch m)) {q} {q′} eq = client-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-client l d x q)) eq)
client-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , chainSync m)) {q} {q′} eq = client-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-client l d x q)) eq)
client-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , leiosFetchP m)) {q} {q′} eq = client-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-client l d x q)) eq)
client-gate-sound (Local.evLabel _ (apiLPev _ _ _) a) eq with refl ← just-injective eq = unchanged
client-gate-sound (Local.evLabel _ (doneLNP _ _) a) eq with refl ← just-injective eq = unchanged

-- Lift the server packet result without changing its observation granularity.
server-gate-sound : ∀ e {q q′} → serverGate e q ≡ just q′ →
  BufferStep server (queue (clientToServer q)) (queue (serverToClient q)) (cls e)
    (queue (clientToServer q′)) (queue (serverToClient q′))
server-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , leiosNotifyP m)) {q} {q′} eq = server-packet-sound (Send , x) {q = q} {q′ = q′} eq
server-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , keepAlive m)) {q} {q′} eq = server-packet-sound (Send , x) {q = q} {q′ = q′} eq
server-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , blockFetch m)) {q} {q′} eq = server-packet-sound (Send , x) {q = q} {q′ = q′} eq
server-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , txSubmission m)) {q} {q′} eq = server-packet-sound (Send , x) {q = q} {q′ = q′} eq
server-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , leiosNotify m)) {q} {q′} eq = server-packet-sound (Send , x) {q = q} {q′ = q′} eq
server-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , leiosFetch m)) {q} {q′} eq = server-packet-sound (Send , x) {q = q} {q′ = q′} eq
server-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , chainSync m)) {q} {q′} eq = server-packet-sound (Send , x) {q = q} {q′ = q′} eq
server-gate-sound (Local.evLabel _ (sendLNP l d) x@(tm , md , ln , leiosFetchP m)) {q} {q′} eq = server-packet-sound (Send , x) {q = q} {q′ = q′} eq
server-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , leiosNotifyP m)) {q} {q′} eq = server-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-server l d x q)) eq)
server-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , keepAlive m)) {q} {q′} eq = server-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-server l d x q)) eq)
server-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , blockFetch m)) {q} {q′} eq = server-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-server l d x q)) eq)
server-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , txSubmission m)) {q} {q′} eq = server-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-server l d x q)) eq)
server-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , leiosNotify m)) {q} {q′} eq = server-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-server l d x q)) eq)
server-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , leiosFetch m)) {q} {q′} eq = server-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-server l d x q)) eq)
server-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , chainSync m)) {q} {q′} eq = server-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-server l d x q)) eq)
server-gate-sound (Local.evLabel _ (receiveLNP l d) x@(tm , md , ln , leiosFetchP m)) {q} {q′} eq = server-packet-sound (Recv , x) {q = q} {q′ = q′} (trans (sym (recv-server l d x q)) eq)
server-gate-sound (Local.evLabel _ (apiLPev _ _ _) a) eq with refl ← just-injective eq = unchanged
server-gate-sound (Local.evLabel _ (doneLNP _ _) a) eq with refl ← just-injective eq = unchanged

{-# OPTIONS --safe #-}

-- Two endpoint inputs have distinct typed alphabets; foreign-role rows cannot be silently reclassified.
module Cardano_network.LeiosNotifyPipeLookahead.DriverRows
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; map; mapMaybe; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D

-- The client records its commands and its received server responses.
data ClientRow : Set where
  sendCommand : D.ClientMessage → ClientRow
  receiveResponse : D.ServerMessage → ClientRow

-- The server records its received commands and its own responses.
data ServerRow : Set where
  receiveCommand : D.ClientMessage → ServerRow
  sendResponse : D.ServerMessage → ServerRow

-- Embedding keeps exact packet payloads and the client endpoint identity.
clientEvent : ClientRow → D.Event
clientEvent (sendCommand message) = D.clientSend message
clientEvent (receiveResponse message) = D.clientRecv message

-- The server embedding is disjoint from both client event constructors.
serverEvent : ServerRow → D.Event
serverEvent (receiveCommand message) = D.serverRecv message
serverEvent (sendResponse message) = D.serverSend message

-- Local projection is explicit; this is not permission for raw parsing to discard a row.
clientPart : D.Event → Maybe ClientRow
clientPart (D.clientSend message) = just (sendCommand message)
clientPart (D.clientRecv message) = just (receiveResponse message)
clientPart _ = nothing

-- The complementary projection retains server agency and exact messages.
serverPart : D.Event → Maybe ServerRow
serverPart (D.serverRecv message) = just (receiveCommand message)
serverPart (D.serverSend message) = just (sendResponse message)
serverPart _ = nothing

-- Every typed client row survives its own projection exactly.
client-roundtrip : ∀ row → clientPart (clientEvent row) ≡ just row
client-roundtrip (sendCommand _) = refl
client-roundtrip (receiveResponse _) = refl

-- Every typed server row survives its own projection exactly.
server-roundtrip : ∀ row → serverPart (serverEvent row) ≡ just row
server-roundtrip (receiveCommand _) = refl
server-roundtrip (sendResponse _) = refl

-- A server event cannot masquerade as a client event in the two-list search.
client-foreign : ∀ row → clientPart (serverEvent row) ≡ nothing
client-foreign (receiveCommand _) = refl
client-foreign (sendResponse _) = refl

-- Client events are likewise absent from the declared server projection.
server-foreign : ∀ row → serverPart (clientEvent row) ≡ nothing
server-foreign (sendCommand _) = refl
server-foreign (receiveResponse _) = refl

-- Concatenation supplies a whole-input payload inventory, not a proposed causal merge.
input : List ClientRow → List ServerRow → List D.Event
input client server = map clientEvent client ++ map serverEvent server

-- A merge chooses an endpoint at every row and preserves both endpoint orders.
data Merge : List ClientRow → List ServerRow → List D.Event → Set where
  empty : Merge [] [] []
  client : ∀ {row rows server events} → Merge rows server events →
    Merge (row ∷ rows) server (clientEvent row ∷ events)
  server : ∀ {client row rows events} → Merge client rows events →
    Merge client (row ∷ rows) (serverEvent row ∷ events)

-- Inserting a server head after the client inventory retains every previous occurrence.
insert : ∀ {A : Set} (prefix : List A) (value : A) {suffix item} →
  item ∈ (prefix ++ suffix) → item ∈ (prefix ++ (value ∷ suffix))
insert [] value member = there member
insert (_ ∷ prefix) value (here equal) = here equal
insert (_ ∷ prefix) value (there member) = there (insert prefix value member)

-- Every merged row is covered by the fixed whole-input inventory, independent of merge order.
covered : ∀ {client server events} → Merge client server events →
  ∀ {event} → event ∈ events → event ∈ input client server
covered empty ()
covered (client merged) (here equal) = here equal
covered (client merged) (there member) = there (covered merged member)
covered (server {client = clientRows} merged) (here equal) =
  ∈-++⁺ʳ (map clientEvent clientRows) (here equal)
covered (server {client = clientRows} {row = row} merged) (there member) =
  insert (map clientEvent clientRows) (serverEvent row) (covered merged member)

-- Projecting an actual merge yields exactly the original client prefix.
client-projection : ∀ {client server events} → Merge client server events →
  mapMaybe clientPart events ≡ client
client-projection empty = refl
client-projection (client {row = row} merged) rewrite client-roundtrip row =
  cong (row ∷_) (client-projection merged)
client-projection (server {row = row} merged) rewrite client-foreign row = client-projection merged

-- The same merged witness preserves every server row and duplicate occurrence.
server-projection : ∀ {client server events} → Merge client server events →
  mapMaybe serverPart events ≡ server
server-projection empty = refl
server-projection (client {row = row} merged) rewrite server-foreign row = server-projection merged
server-projection (server {row = row} merged) rewrite server-roundtrip row =
  cong (row ∷_) (server-projection merged)

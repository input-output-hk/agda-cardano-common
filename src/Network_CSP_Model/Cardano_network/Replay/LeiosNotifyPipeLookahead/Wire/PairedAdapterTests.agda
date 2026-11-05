{-# OPTIONS --guardedness #-}

-- Paired normalized inputs retain fields, endpoint locations and exhaustive prefix decisions.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapterTests where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as P
import Cardano_network.LeiosNotifyPipeLookahead.Model P.Notification as S
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as A
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Client

-- A concrete tag distinguishes malformed input from rejection of every source merge/schedule.
data Kind : Set where
  invalid rejected accepted : Kind

-- The adapter's accepted branch still retains complete mapping and source witnesses.
kind : ∀ {contract cr ci sr si} → A.Verdict contract cr ci sr si → Kind
kind (A.invalidInput _ _) = invalid
kind (A.protocolRejected _ _ _ _ _) = rejected
kind (A.accepted _) = accepted

-- Both empty files are valid fresh prefixes.
empty-prefix : A.Accepted S.nodeNext Log.client [] Log.server []
empty-prefix = toWitness {a? = A.decide S.nodeNext Log.client [] Log.server []} tt

-- A final client Request Send requires no fabricated server receive row at EOF.
request-server-eof : A.Accepted S.nodeNext Log.client
  (A.present ((Log.Send , Log.RequestNext) ∷ [])) Log.server []
request-server-eof = toWitness {a? = A.decide S.nodeNext Log.client _ Log.server _} tt

-- The server may record its Request Receive before the client's delayed Send record.
receive-client-eof : A.Accepted S.nodeNext Log.client [] Log.server
  (A.present ((Log.Recv , Log.RequestNext) ∷ []))
receive-client-eof = toWitness {a? = A.decide S.nodeNext Log.client _ Log.server _} tt

-- Valid normalized agency does not invent a missing physical server response.
unmatched-reply : kind (A.check-normalized S.nodeNext Log.client
  ((Log.Recv , Log.Canceled) ∷ []) Log.server []) ≡ rejected
unmatched-reply = refl

-- Wrong declared client role is invalid even if both lists are empty.
wrong-client-role : kind (A.check-normalized S.nodeNext Log.server [] Log.server []) ≡ invalid
wrong-client-role = refl

-- The server role is independently validated rather than inferred from message shape.
wrong-server-role : kind (A.check-normalized S.nodeNext Log.client [] Log.client []) ≡ invalid
wrong-server-role = refl

-- Inappropriate client command direction cannot be silently discarded.
wrong-agency : kind (A.check-normalized S.nodeNext Log.client
  ((Log.Recv , Log.Quit) ∷ []) Log.server []) ≡ invalid
wrong-agency = refl

-- Extracting a diagnostic observes only failure metadata, never inventing capture coordinates.
failure-location : ∀ {contract cr ci sr si} → A.Verdict contract cr ci sr si → A.Side × ℕ
failure-location (A.invalidInput failure _) = A.side failure , A.position failure
failure-location _ = A.clientInput , 99

-- The second server row is retained even though its predecessor is a valid request.
server-row-index : failure-location (A.check S.nodeNext Log.client [] Log.server
  (just (Log.Recv , Log.RequestNext) ∷ nothing ∷ [])) ≡ (A.serverInput , 1)
server-row-index = refl

-- Matching exact payloads can arrive before either pending client Send record is published.
exact-payload : A.Accepted S.genericNext Log.client
  (A.present ((Log.Recv , Log.BlockOffer 17 23 31) ∷ [])) Log.server
  (A.present ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.BlockOffer 17 23 31) ∷ []))
exact-payload = toWitness {a? = A.decide S.genericNext Log.client _ Log.server _} tt

-- Distinct retained hash fields are rejected despite identical message kind and agency.
payload-mismatch : A.Accepted S.genericNext Log.client
  (A.present ((Log.Recv , Log.BlockOffer 19 23 31) ∷ [])) Log.server
  (A.present ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.BlockOffer 17 23 31) ∷ [])) → ⊥
payload-mismatch = toWitnessFalse {a? = A.decide S.genericNext Log.client _ Log.server _} tt

-- Successful adaptation re-encodes every client row exactly.
exact-client-roundtrip : ∀ {client server} → A.Valid Log.client
  (A.present ((Log.Recv , Log.BlockOffer 17 23 31) ∷ [])) Log.server
  (A.present ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.BlockOffer 17 23 31) ∷ [])) client server →
  map (λ row → just (Client.encode (A.clientWire row))) client ≡
    A.present ((Log.Recv , Log.BlockOffer 17 23 31) ∷ [])
exact-client-roundtrip = A.client-roundtrip

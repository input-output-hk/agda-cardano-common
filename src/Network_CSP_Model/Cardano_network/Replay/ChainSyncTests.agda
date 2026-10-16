{-# OPTIONS --safe #-}

-- Inhabited replay runs and negative controls for both endpoint roles.
module Cardano_network.Replay.ChainSyncTests where

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.ChainSyncSession
open import Cardano_network.Replay.SessionReport using (reportChainSync; reportWithAllDepths)

-- Two requests overlap AwaitReply, then drain before intersection and Done.
rounds : List E
rounds = (Send , requestNext) ∷ (Recv , awaitReply) ∷
  (Send , requestNext) ∷ (Recv , rollForward) ∷
  (Recv , awaitReply) ∷ (Recv , rollBackward) ∷
  (Send , findIntersect) ∷ (Recv , intersectFound) ∷ (Send , doneK) ∷ []

-- Positive acceptance includes a concrete run, not just an unused premise.
rounds-run : Spec.HasTrace 2 client initial rounds
rounds-run = toWitness {a? = Spec.check 2 client rounds} tt

-- Reducing the bound rules out the overlapping request.
too-shallow : False (Spec.check 1 client rounds)
too-shallow = tt

-- A sequential server handles both reply phases and intersection results.
server-rounds : List E
server-rounds = (Recv , findIntersect) ∷ (Send , intersectNotFound) ∷
  (Recv , requestNext) ∷ (Send , awaitReply) ∷ (Send , rollForward) ∷
  (Recv , requestNext) ∷ (Send , rollBackward) ∷ (Recv , doneK) ∷ []

-- A zero client bound does not disable server reception.
server-run : Spec.HasTrace 0 server initial server-rounds
server-run = toWitness {a? = Spec.check 0 server server-rounds} tt

-- A pipeline cannot be reversed to obtain a legal sequential server trace.
server-not-pipelined : False (Spec.check 300 server (map reverse rounds))
server-not-pipelined = tt

-- AwaitReply leaves the request outstanding and forbids another AwaitReply.
repeated-await : False (Spec.check 2 client
  ((Send , requestNext) ∷ (Recv , awaitReply) ∷ (Recv , awaitReply) ∷ []))
repeated-await = tt

-- Without a request no roll response can be consumed.
unsolicited : False (Spec.check 2 client ((Recv , rollForward) ∷ []))
unsolicited = tt

-- Done cannot discard an outstanding response.
busy-done : False (Spec.check 2 client ((Send , requestNext) ∷ (Send , doneK) ∷ []))
busy-done = tt

-- Intersection must wait until the RequestNext pipeline drains.
busy-intersect : False (Spec.check 2 client ((Send , requestNext) ∷ (Send , findIntersect) ∷ []))
busy-intersect = tt

-- No new request is issued while negotiating an intersection.
intersect-exclusive : False (Spec.check 2 client ((Send , findIntersect) ∷ (Send , requestNext) ∷ []))
intersect-exclusive = tt

-- Intersection results cannot complete a RequestNext operation.
wrong-response : False (Spec.check 2 client ((Send , requestNext) ∷ (Recv , intersectFound) ∷ []))
wrong-response = tt

-- Wire direction is enforced independently of the message kind.
wrong-agency : False (Spec.check 2 client ((Recv , requestNext) ∷ []))
wrong-agency = tt

-- Closed generations accept no later events.
closed-session : False (Spec.check 2 client ((Send , doneK) ∷ (Send , requestNext) ∷ []))
closed-session = tt

-- EOF may occur while waiting for a mandatory response.
await-prefix : Spec.HasTrace 1 client initial ((Send , requestNext) ∷ (Recv , awaitReply) ∷ [])
await-prefix = toWitness {a? = Spec.check 1 client ((Send , requestNext) ∷ (Recv , awaitReply) ∷ [])} tt

-- The zero bound prohibits requests but allows an idle close.
zero-request : False (Spec.check 0 client ((Send , requestNext) ∷ []))
zero-request = tt

-- Namespace rows and role dispatch use the same certified checker.
parse-and-check : reportChainSync 0 "role server\nChainSync.Remote.Receive.FindIntersect\nChainSync.Remote.Send.IntersectFound\nChainSync.Remote.Receive.Done\n" ≡ "accepted (3 events, 1 sessions)"
parse-and-check = refl

-- A different protocol's RequestNext namespace is rejected by parsing.
wrong-namespace : reportChainSync 2 "role client\nLeiosNotify.Remote.Send.RequestNext\n" ≡ "parse error at line 2: LeiosNotify.Remote.Send.RequestNext"
wrong-namespace = refl

-- Payload tokens are explicitly outside this control-only grammar.
extra-payload : reportChainSync 2 "role client\nRecv RollForward ab\n" ≡ "parse error at line 2: Recv RollForward ab"
extra-payload = refl

-- One session's request cannot license another session's response.
isolation : reportWithAllDepths 1 1 1 2 "sessions chainsync:client chainsync:client\n0 Send RequestNext\n1 Recv RollForward\n" ≡
  "rejected at index 2 (session 1): Recv RollForward\nmodel session state after 1 events: chainsync client outstanding 0, can-await"
isolation = refl

-- All four protocol bounds can differ in the same globally ordered replay.
mixed : reportWithAllDepths 0 0 0 2 "sessions fetch:client notify:client blockfetch:client chainsync:client chainsync:server\n3 Send RequestNext\n4 Recv FindIntersect\n3 Send RequestNext\n4 Send IntersectNotFound\n3 Recv RollForward\n3 Recv RollBackward\n" ≡ "accepted (6 events, 5 sessions)"
mixed = refl

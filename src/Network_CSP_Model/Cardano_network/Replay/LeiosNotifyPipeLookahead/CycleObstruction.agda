{-# OPTIONS --safe #-}

-- A source-independent merge cut turns every-prefix transport bounds into an obstruction.
-- No paired search or Notification equality is used; all original source executions are excluded.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstruction
  (Notification Return : Set) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Product using (Σ-syntax; _×_; _,_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification Return as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification Return as History
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PrefixTransport Notification Return as Prefix

-- A second recorded Receive cannot precede every peer Send when only one Send hook may be pending.
two-not-one : 2 ≤ 1 → ⊥
two-not-one (s≤s ())

-- Three recorded Receives similarly require at least two recorded peer Sends.
three-not-two : 3 ≤ 2 → ⊥
three-not-two (s≤s (s≤s ()))

-- This stronger cut depends only on row directions, not payload equality, callbacks or source policy.
module Pattern (firstReply secondReply : D.ServerMessage)
  (command firstRequest secondRequest thirdRequest : D.ClientMessage)
  (clientTail : List Rows.ClientRow) (serverTail : List Rows.ServerRow) where

  -- Once each endpoint has consumed its first two rows, either next head violates a transport bound.
  blocked : ∀ {events} →
    Rows.Merge (Rows.receiveResponse secondReply ∷ clientTail)
      (Rows.receiveCommand thirdRequest ∷ serverTail) events →
    Prefix.Bounded (History.history (command ∷ []) (firstRequest ∷ secondRequest ∷ []) [] (firstReply ∷ [])) events → ⊥
  blocked (Rows.client merged) (Prefix.next (_ , bound) rest) = two-not-one bound
  blocked (Rows.server merged) (Prefix.next (bound , _) rest) = three-not-two bound

  -- With one server Request observed, a second client Receive is already impossible.
  server-one : ∀ {events} →
    Rows.Merge (Rows.receiveResponse secondReply ∷ clientTail)
      (Rows.receiveCommand secondRequest ∷ Rows.receiveCommand thirdRequest ∷ serverTail) events →
    Prefix.Bounded (History.history (command ∷ []) (firstRequest ∷ []) [] (firstReply ∷ [])) events → ⊥
  server-one (Rows.client merged) (Prefix.next (_ , bound) rest) = two-not-one bound
  server-one (Rows.server merged) (Prefix.next bounds rest) = blocked merged rest

  -- With no server Request recorded, only its first Request can advance this frontier.
  server-zero : ∀ {events} →
    Rows.Merge (Rows.receiveResponse secondReply ∷ clientTail)
      (Rows.receiveCommand firstRequest ∷ Rows.receiveCommand secondRequest ∷ Rows.receiveCommand thirdRequest ∷ serverTail) events →
    Prefix.Bounded (History.history (command ∷ []) [] [] (firstReply ∷ [])) events → ⊥
  server-zero (Rows.client merged) (Prefix.next (_ , bound) rest) = two-not-one bound
  server-zero (Rows.server merged) (Prefix.next bounds rest) = server-one merged rest

  -- Before the client's first Send, the server cannot record a second Request.
  client-received-server-one : ∀ {events} →
    Rows.Merge (Rows.sendCommand command ∷ Rows.receiveResponse secondReply ∷ clientTail)
      (Rows.receiveCommand secondRequest ∷ Rows.receiveCommand thirdRequest ∷ serverTail) events →
    Prefix.Bounded (History.history [] (firstRequest ∷ []) [] (firstReply ∷ [])) events → ⊥
  client-received-server-one (Rows.client merged) (Prefix.next bounds rest) = server-one merged rest
  client-received-server-one (Rows.server merged) (Prefix.next (bound , _) rest) = two-not-one bound

  -- Consuming the first client Send or first server Receive leads to an already blocked frontier.
  client-received-server-zero : ∀ {events} →
    Rows.Merge (Rows.sendCommand command ∷ Rows.receiveResponse secondReply ∷ clientTail)
      (Rows.receiveCommand firstRequest ∷ Rows.receiveCommand secondRequest ∷ Rows.receiveCommand thirdRequest ∷ serverTail) events →
    Prefix.Bounded (History.history [] [] [] (firstReply ∷ [])) events → ⊥
  client-received-server-zero (Rows.client merged) (Prefix.next bounds rest) = server-zero merged rest
  client-received-server-zero (Rows.server merged) (Prefix.next bounds rest) = client-received-server-one merged rest

  -- An initial server Receive cannot be followed by a second one before the first client Send.
  client-zero-server-one : ∀ {events} →
    Rows.Merge (Rows.receiveResponse firstReply ∷ Rows.sendCommand command ∷ Rows.receiveResponse secondReply ∷ clientTail)
      (Rows.receiveCommand secondRequest ∷ Rows.receiveCommand thirdRequest ∷ serverTail) events →
    Prefix.Bounded (History.history [] (firstRequest ∷ []) [] []) events → ⊥
  client-zero-server-one (Rows.client merged) (Prefix.next bounds rest) = client-received-server-one merged rest
  client-zero-server-one (Rows.server merged) (Prefix.next (bound , _) rest) = two-not-one bound

  -- Every merge begins with one endpoint head; all possible frontiers contradict a bound.
  impossible : ∀ {events} →
    Rows.Merge (Rows.receiveResponse firstReply ∷ Rows.sendCommand command ∷ Rows.receiveResponse secondReply ∷ clientTail)
      (Rows.receiveCommand firstRequest ∷ Rows.receiveCommand secondRequest ∷ Rows.receiveCommand thirdRequest ∷ serverTail) events →
    Prefix.Bounded History.empty events → ⊥
  impossible (Rows.client merged) (Prefix.next bounds rest) = client-received-server-zero merged rest
  impossible (Rows.server merged) (Prefix.next bounds rest) = client-zero-server-one merged rest

-- The cut applies to the unchanged original driver source through its every-prefix invariant.
prefix-impossible : ∀ {contract events target} firstReply secondReply command firstRequest secondRequest thirdRequest clientTail serverTail →
  Rows.Merge (Rows.receiveResponse firstReply ∷ Rows.sendCommand command ∷ Rows.receiveResponse secondReply ∷ clientTail)
    (Rows.receiveCommand firstRequest ∷ Rows.receiveCommand secondRequest ∷ Rows.receiveCommand thirdRequest ∷ serverTail) events →
  D.Run contract D.initial events target → ⊥
prefix-impossible firstReply secondReply command firstRequest secondRequest thirdRequest clientTail serverTail merged source =
  Pattern.impossible firstReply secondReply command firstRequest secondRequest thirdRequest clientTail serverTail merged (Prefix.necessary source)

-- A client family repeatedly receives a normal before recording its corresponding Request Send.
client : Notification → ℕ → List Rows.ClientRow
client value zero = []
client value (suc n) = Rows.receiveResponse (D.reply (S.normal value)) ∷ Rows.sendCommand D.request ∷ client value n

-- The server first records every Request, retaining each occurrence independently.
requests : ℕ → List Rows.ServerRow
requests zero = []
requests (suc n) = Rows.receiveCommand D.request ∷ requests n

-- Exact repeated normal responses follow only after the entire recorded Request block.
responses : Notification → ℕ → List Rows.ServerRow
responses value zero = []
responses value (suc n) = Rows.sendResponse (D.reply (S.normal value)) ∷ responses value n

-- The server family preserves all Request rows followed by all exact normal Send rows.
server : Notification → ℕ → List Rows.ServerRow
server value n = requests n ++ responses value n

-- Every family member of size at least three has the stronger contradictory prefix pattern.
cycle-impossible : ∀ {contract n events target} value → 3 ≤ n →
  Rows.Merge (client value n) (server value n) events →
  D.Run contract D.initial events target → ⊥
cycle-impossible {n = zero} value ()
cycle-impossible {n = suc zero} value (s≤s ())
cycle-impossible {n = suc (suc zero)} value (s≤s (s≤s ()))
cycle-impossible {n = suc (suc (suc n))} value bound merged source =
  prefix-impossible (D.reply (S.normal value)) (D.reply (S.normal value))
    D.request D.request D.request D.request
    (Rows.sendCommand D.request ∷ client value (suc n))
    (requests n ++ responses value (suc (suc (suc n)))) merged source

-- This is exactly the original existential merge/run proposition, with no checker or finite-basis premise.
SourceTrace : S.Contract → List Rows.ClientRow → List Rows.ServerRow → Set
SourceTrace contract clientRows serverRows = Σ[ events ∈ List D.Event ]
  (Rows.Merge clientRows serverRows events × Σ[ target ∈ D.State ] D.Run contract D.initial events target)

-- All matching original source executions are refuted for arbitrary Notification, Return and both contracts.
no-source : ∀ contract value n → 3 ≤ n → SourceTrace contract (client value n) (server value n) → ⊥
no-source contract value n bound (events , merged , target , source) = cycle-impossible value bound merged source

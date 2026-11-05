{-# OPTIONS --guardedness #-}

-- Unique callback candidates preserve complete repeated records and the exact internal Votes list.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverUniqueTests where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification ⊤ as Conservation
import Cardano_network.Replay.LeiosNotifyPipeLookahead.UniqueBasisAdequacy Notification ⊤ as Unique
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Notification notificationEq (votes []) as Check
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideNative exactParams as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideNativeTests as Delayed

-- Packet equality includes the final repeated vote and its original position.
sample : Notification
sample = votes ((17 , 23) ∷ (31 , 37) ∷ (17 , 23) ∷ [])

-- This altered value has discarded a vote inside one payload, not a redundant candidate.
trimmed : Notification
trimmed = votes ((17 , 23) ∷ (31 , 37) ∷ [])

-- This other alteration keeps the cardinality but changes the exact vote ordering.
reordered : Notification
reordered = votes ((31 , 37) ∷ (17 , 23) ∷ (17 , 23) ∷ [])

-- Concatenation preserves every visible occurrence and every hidden source operation.
append : ∀ {contract s events t later u} → D.Run contract s events t →
  D.Run contract t later u → D.Run contract s (events ++ later) u
append D.stop suffix = suffix
append (D.internal step rest) suffix = D.internal step (append rest suffix)
append (D.visible step rest) suffix = D.visible step (append rest suffix)

-- This witness family works for any entire Notification value and either server callback contract.
module Repeated (value : Notification) where
  -- A completed exchange leaves the client reusable and one additional server completion token.
  ready : S.Reader → ℕ → D.State
  ready reader completed = D.pair C.initial (S.state reader 0 S.idle completed false)
    [] [] nothing nothing nothing nothing

  -- Each round contributes all four records even when its payload equals every earlier payload.
  events : List D.Event
  events = D.clientSend D.request ∷ D.serverRecv D.request ∷
    D.serverSend (D.reply (S.normal value)) ∷ D.clientRecv (D.reply (S.normal value)) ∷ []

  -- Actual registration/transport/handling/collection realizes an exchange without any search assumption.
  round : ∀ contract {reader} → S.Reading reader → (completed : ℕ) →
    D.Run contract (ready reader completed) events (ready S.awaitNext (suc completed))
  round contract reading completed =
    D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
    D.internal (D.clientInternal C.registerResponse) $
    D.internal (D.clientInternal (C.startResponse refl)) $
    D.internal (D.commitClient C.sentRequest) $
    D.visible (D.clientSent C.sentRequest) $
    D.internal (D.decodeServer (S.receiveRequest reading)) $
    D.visible (D.serverReceived (S.receiveRequest reading)) $
    D.internal (D.serverInternal S.admitted) $
    D.internal (D.serverInternal S.registered) $
    D.internal (D.serverInternal (S.claim refl)) $
    D.internal (D.serverCallback (S.choose refl refl)) $
    D.internal (D.commitServer (S.send refl)) $
    D.visible (D.serverSent (S.send refl)) $
    D.internal (D.serverInternal (S.retire refl)) $
    D.internal (D.decodeClient (C.receivedReply refl)) $
    D.visible (D.clientReceived (C.receivedReply refl)) $
    D.internal (D.clientInternal (C.keepReply refl)) $
    D.internal (D.clientCallback D.handled (C.delivered refl)) $
    D.internal (D.clientInternal (C.countArrival refl)) $
    D.internal (D.clientInternal (C.publishResponse refl)) $
    D.internal (D.clientCallback (D.continue {k = + 2}) (C.continueBelow refl)) $
    D.internal (D.clientInternal C.optionalResult) $
    D.internal (D.clientInternal C.adjustArrival) D.stop

  -- Both complete exchanges are retained, despite having identical notification values.
  twice : ∀ contract → D.Run contract D.initial (events ++ events) (ready S.awaitNext 2)
  twice contract = append (round contract S.atFirst 0) (round contract S.atNext 1)

  -- Repeated client records remain distinct input positions.
  client : List Rows.ClientRow
  client = Rows.sendCommand D.request ∷ Rows.receiveResponse (D.reply (S.normal value)) ∷
    Rows.sendCommand D.request ∷ Rows.receiveResponse (D.reply (S.normal value)) ∷ []

  -- The server likewise retains both Request receives and both reply sends.
  server : List Rows.ServerRow
  server = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal value)) ∷
    Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal value)) ∷ []

  -- Endpoint order agrees with the explicit eight-record history; no row is removed by deduplication.
  merged : Rows.Merge client server (events ++ events)
  merged = Rows.client (Rows.server (Rows.server (Rows.client
    (Rows.client (Rows.server (Rows.server (Rows.client Rows.empty)))))))

  -- Fresh source acceptance is inhabited for every exact value and both callback contracts.
  source : ∀ contract → Check.SourceTrace contract client server
  source contract = events ++ events , merged , ready S.awaitNext 2 , twice contract

  -- EOF here is unfinished server operation, with two retained completions and no Quit.
  prefix-not-closed : S.reader (D.serverState (ready S.awaitNext 2)) ≡ S.closed → ⊥
  prefix-not-closed ()

module Votes = Repeated sample
module Empty = Repeated (votes [])
module Collision = Unique.ForInput notificationEq sample (Rows.input Votes.client Votes.server)
module EmptyCollision = Unique.ForInput notificationEq (votes []) (Rows.input Empty.client Empty.server)

-- The occurrence inventory contains the representative and four observed occurrences of one value.
original-candidates : length Collision.Original.basis ≡ 5
original-candidates = refl

-- Removing only duplicate whole candidates leaves the entire repeated Votes value unchanged.
one-candidate : Collision.basis ≡ sample ∷ []
one-candidate = refl

-- Representative collision also works for the exact empty Votes native fallback.
empty-one-candidate : EmptyCollision.basis ≡ votes [] ∷ []
empty-one-candidate = refl

-- Candidate reduction does not reduce the eight endpoint log records or their repeated inner vote.
all-visible-records : length (Votes.events ++ Votes.events) ≡ 8
all-visible-records = refl

-- The deduplicated restriction admits the same actual source history, for either server contract.
restricted : ∀ contract → Collision.B.Run contract D.initial (Votes.events ++ Votes.events)
  (Collision.M.state (Votes.ready S.awaitNext 2))
restricted contract = Collision.adequate-covered (Rows.covered Votes.merged) (Votes.twice contract)

-- Transporting back preserves the complete recorded list, not merely its set of values.
roundtrip : ∀ contract → D.Run contract D.initial (Votes.events ++ Votes.events)
  (Collision.M.state (Votes.ready S.awaitNext 2))
roundtrip contract = Collision.B.sound (restricted contract)

-- Native realization retains every repeated record at the same fixed fresh endpoint coordinates.
native : ∀ contract → Native.At.NativeTrace contract fzero fzero hi hi Votes.client Votes.server
native contract = Native.At.realize contract fzero fzero hi hi (Votes.source contract)

-- This two-row computed prefix collides exactly with the native fallback candidate.
small-client : List Rows.ClientRow
small-client = Rows.receiveResponse (D.reply (S.normal (votes []))) ∷ []

-- Both Send hooks may remain hidden at EOF while the matching Request receive was recorded.
small-server : List Rows.ServerRow
small-server = Rows.receiveCommand D.request ∷ []

-- The public node-contract decision accepts the unfinished exact representative prefix.
computed-node-prefix : Check.SourceTrace S.nodeNext small-client small-server
computed-node-prefix = toWitness {a? = Check.decide S.nodeNext _ _} tt

-- The same representative-collision prefix also computes under the generic callback contract.
computed-generic-prefix : Check.SourceTrace S.genericNext small-client small-server
computed-generic-prefix = toWitness {a? = Check.decide S.genericNext _ _} tt

-- The pending Send race remains inhabited after source/basis/native transport.
delayed-send : Delayed.B.NativeTrace Delayed.clientRows Delayed.serverRows
delayed-send = Delayed.B.realize Delayed.paired-source

-- A sole client receive has the altered exact value and its Request Send may still be pending.
wrong-client : Notification → List Rows.ClientRow
wrong-client value = Rows.receiveResponse (D.reply (S.normal value)) ∷ []

-- The only recorded server reply has the original unmodified internal Votes list.
right-server : List Rows.ServerRow
right-server = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal sample)) ∷ []

-- Removing an internal duplicate vote contradicts packet conservation in every possible endpoint merge.
cannot-trim : ∀ contract → Check.SourceTrace contract (wrong-client trimmed) right-server → ⊥
cannot-trim contract (_ , Rows.client (Rows.server (Rows.server Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()
cannot-trim contract (_ , Rows.server (Rows.client (Rows.server Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()
cannot-trim contract (_ , Rows.server (Rows.server (Rows.client Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()

-- Reordering the same vote multiset likewise fails, independently of search behavior or basis order.
cannot-reorder : ∀ contract → Check.SourceTrace contract (wrong-client reordered) right-server → ⊥
cannot-reorder contract (_ , Rows.client (Rows.server (Rows.server Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()
cannot-reorder contract (_ , Rows.server (Rows.client (Rows.server Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()
cannot-reorder contract (_ , Rows.server (Rows.server (Rows.client Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()

-- Exhaustive native rejection follows from the same conservation proof, not from an observed failed run.
native-cannot-trim : ∀ contract → Native.At.NativeTrace contract fzero fzero hi hi
  (wrong-client trimmed) right-server → ⊥
native-cannot-trim contract native = cannot-trim contract (Native.At.sound contract fzero fzero hi hi native)

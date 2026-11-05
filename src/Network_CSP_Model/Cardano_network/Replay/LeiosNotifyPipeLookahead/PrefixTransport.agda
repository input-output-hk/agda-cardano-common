{-# OPTIONS --safe #-}

-- Every visible prefix retains the one-pending-Send receive bound, with hidden source operations erased.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PrefixTransport
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (_+_; _≤_; _≤?_; z≤n)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification Return as Conservation
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketCountPrecheck Notification Return as Counts

-- The four exact packet histories remain available to proofs without payload equality or a finite carrier.
module History = Conservation

-- Each receiver may lead its peer's recorded Sends by one pending hook; Send excess is unrestricted.
Bounds : History.History → Set
Bounds past =
  length (History.serverReceives past) ≤ length (History.clientSends past) + 1 ×
  length (History.clientReceives past) ≤ length (History.serverSends past) + 1

-- The numerical predicate is decidable independently of the source model's hidden choices.
bounds? : (past : History.History) → Dec (Bounds past)
bounds? past =
  (length (History.serverReceives past) ≤? length (History.clientSends past) + 1) ×-dec
  (length (History.clientReceives past) ≤? length (History.serverSends past) + 1)

-- Every actual balanced history inherits both bounds, including pending Receive and FIFO suffixes.
from-balanced : ∀ {past state} → History.Balanced past state → Bounds past
from-balanced {past} {state} accounted =
  Counts.Commands.receive-bound (History.clientSends past) (History.serverReceives past)
    {ps = D.pendingClientSend state} {pr = D.pendingServerRecv state} {queue = D.clientToServer state}
    (History.to-server accounted) ,
  Counts.Responses.receive-bound (History.serverSends past) (History.clientReceives past)
    {ps = D.pendingServerSend state} {pr = D.pendingClientRecv state} {queue = D.serverToClient state}
    (History.to-client accounted)

-- This certificate retains every exact event and enforces the bound after every visible operation.
data Bounded (past : History.History) : List D.Event → Set where
  done : Bounded past []
  next : ∀ {event events} → Bounds (History.advance event past) →
    Bounded (History.advance event past) events → Bounded past (event ∷ events)

-- Source τ steps change no recorded history; visible steps preserve actual conservation and its bounds.
transport : ∀ {contract start events target past} → D.Run contract start events target →
  History.Balanced past start → Bounded past events
transport D.stop accounted = done
transport (D.internal step rest) accounted = transport rest (History.tau-balance step accounted)
transport (D.visible step rest) accounted = next (from-balanced (History.step-balance step accounted))
  (transport rest (History.step-balance step accounted))

-- Fresh source executions therefore satisfy every prefix constraint without any extra capture premise.
necessary : ∀ {contract events target} → D.Run contract D.initial events target → Bounded History.empty events
necessary source = transport source History.initial-balanced

-- A fixed visible order has a simple structural check; no search over merges or source states is performed.
decide : (past : History.History) (events : List D.Event) → Dec (Bounded past events)
decide past [] = yes done
decide past (event ∷ events) with bounds? (History.advance event past)
... | no absent = no λ { (next bound rest) → absent bound }
... | yes bound with decide (History.advance event past) events
...   | yes rest = yes (next bound rest)
...   | no absent = no λ { (next _ rest) → absent rest }

-- Any cut of a prefix-valid merged order remains prefix-valid with the same original events.
cut : ∀ {past after} (before : List D.Event) → Bounded past (before ++ after) → Bounded past before
cut [] bounded = done
cut (event ∷ before) (next bound rest) = next bound (cut before rest)

-- Empty fresh history already satisfies the bound, without assuming an inhabited Return type.
initial-bounds : Bounds History.empty
initial-bounds = z≤n , z≤n

-- A certificate yields the exact bound at every supplied cut, not only at the final history.
prefix-bounds : ∀ {past after} (before : List D.Event) → Bounds past → Bounded past (before ++ after) →
  Bounds (History.observe before past)
prefix-bounds [] initial bounded = initial
prefix-bounds (event ∷ before) initial (next bound rest) = prefix-bounds before bound rest

-- The public cut theorem transports every original fresh source prefix directly to its recorded counts.
source-prefix-bounds : ∀ {contract after target} (before : List D.Event) →
  D.Run contract D.initial (before ++ after) target → Bounds (History.observe before History.empty)
source-prefix-bounds before source = prefix-bounds before initial-bounds (necessary source)

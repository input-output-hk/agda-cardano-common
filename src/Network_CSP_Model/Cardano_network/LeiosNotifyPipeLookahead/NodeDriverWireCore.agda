{-# OPTIONS --safe #-}

-- Exact wire-only normalization removes external flag snapshots and dropped-offer stuttering.
-- Protocol state, including the client's stopFlag, queue and local failure flag, stays intact.
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore (Notification : Set) where

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node

-- Only external forecast/termination snapshots are absent from the retained full protocol state.
record State : Set where
  constructor core
  field
    driverState : D.State
    queueState : Q.State
    clientAlive : Bool
open State public

-- Erasure leaves every driver field, actual client stop flag and queued notification unchanged.
erase : Node.State → State
erase (Node.nodeDriver raw queue live forecast halt) = core raw queue live

-- Any external snapshot can accompany the same exact retained protocol state.
embed : State → Bool → Bool → Node.State
embed (core raw queue live) forecast halt = Node.nodeDriver raw queue live forecast halt

-- Embedding cannot change any retained protocol field.
erase-embed : ∀ state forecast halt → erase (embed state forecast halt) ≡ state
erase-embed (core _ _ _) _ _ = refl

-- Restoring the original external snapshots reconstructs the exact original source state.
embed-erase : ∀ state → embed (erase state) (Node.forecastReady state) (Node.terminateRequested state) ≡ state
embed-erase (Node.nodeDriver _ _ _ _ _) = refl

-- A fixed false/false representative is used only where the source action ignores snapshots.
canonical : State → Node.State
canonical state = embed state false false

-- Visible wire rules are the independent original node rules with unchanged packet fields.
Visible : State → D.Event → State → Set
Visible s row t = Node.Step (canonical s) (Node.wire row) (canonical t)

-- Only productive non-wire effects remain hidden; flag writes and dropped offers are absent.
data Tau : State → State → Set where
  operational : ∀ {s t forecast halt} →
    Node.Tau (embed s forecast halt) (embed t forecast halt) → Tau s t
  offered : ∀ {s t msg} → Node.Step (canonical s) (Node.eligible msg) (canonical t) →
    Q.free (queueState s) ≢ zero → Tau s t
  handled : ∀ {s t msg} → Node.Step (canonical s) (Node.handledNormal msg) (canonical t) → Tau s t
  rejected : ∀ {s t} → Node.Step (canonical s) Node.rejectedCancel (canonical t) → Tau s t

-- Finite wire prefixes preserve their actual retained target, including graceful and failed states.
data Run : State → List D.Event → State → Set where
  stop : ∀ {s} → Run s [] s
  internal : ∀ {s t u rows} → Tau s t → Run t rows u → Run s rows u
  visible : ∀ {s t u row rows} → Visible s row t → Run t rows u → Run s (row ∷ rows) u

-- The wire core begins with exactly the original fresh protocol fields.
initial : State
initial = erase Node.initial

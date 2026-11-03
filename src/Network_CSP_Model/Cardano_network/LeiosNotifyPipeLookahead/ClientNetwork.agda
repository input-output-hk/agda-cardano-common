{-# OPTIONS --guardedness #-}

-- Native LNPEv client with internal checkDone choices and exact source control state.
-- This is the generic successful-callback contract, not the separate node fault policy.
open import Cardano_network.Params using (Params)
module Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork (p : Params) (Return : Set) where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (PTree; AnyTypes; ContinueType; ret; react)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyP p using (LNPEv)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientTree Notification Return notificationEq as Source
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification Return notificationEq as Exec
open import Cardano_network.LeiosNotifyPipeLookahead.Selection using (select; select-complete)
import Semantics.LTS
import Semantics.Deadlock

-- Internal choices contain executable data, including the dynamic depth or return value.
data Choice : Set where
  driver : ℕ → Choice
  callbackValue : C.Action → Choice

-- This scheduler can carry an arbitrary callback result without extending LNPEv.
data Branches : Set → Set₁ where
  schedule : Branches Choice

import Cardano_network.LeiosNotifyPipeLookahead.ClientEvents p Return Branches as Events

-- The observed client's hidden relation includes exactly the declared erased callbacks.
data Tau : C.State → C.State → Set where
  scheduled : ∀ {s t} → C.Tau s t → Tau s t
  callback : ∀ {s a t} → Events.Hidden a → C.Step s a t → Tau s t

-- Native visible events use the existing network and API alphabet.
Proc : Set₁
Proc = PTree LNPEv Branches Return

-- Native traces and steps retain their own internal choice family.
module LTS = Semantics.LTS {E = LNPEv} {I = Branches}
module Traces = Semantics.Deadlock {E = LNPEv} {I = Branches}

-- Certified hidden execution cannot hide a wire row or a normal API delivery.
hidden : (s : C.State) → Choice → Maybe (Σ[ t ∈ C.State ] Tau s t)
hidden s (driver n) with select (Exec.internalMoves s) n
... | nothing = nothing
... | just (t , pr) = just (t , scheduled pr)
hidden s (callbackValue a) with Events.classify a | Exec.lookup a s
... | just hiddenAction | just (t , pr) = just (t , callback hiddenAction pr)
... | _ | _ = nothing

-- The finite driver menu retains its exact selected continuation.
driver-target : ∀ {s t n} {pr : C.Tau s t} → select (Exec.internalMoves s) n ≡ just (t , pr) →
  map proj₁ (hidden s (driver n)) ≡ just t
driver-target eq rewrite eq = refl

-- A declared successful callback retains its exact independently checked target.
callback-target : ∀ {s a t} {h : Events.Hidden a} {pr : C.Step s a t} →
  Events.classify a ≡ just h → Exec.lookup a s ≡ just (t , pr) →
  map proj₁ (hidden s (callbackValue a)) ≡ just t
callback-target classified eq rewrite classified | eq = refl

-- Every independent observed hidden rule has a concrete data-only selector.
hidden-complete : ∀ {s t} → Tau s t → Σ[ choice ∈ Choice ] map proj₁ (hidden s choice) ≡ just t
hidden-complete (scheduled {s = s} pr) with select-complete (Exec.target-complete pr)
... | n , eq with select (Exec.internalMoves s) n in chosen | eq
...   | just (_ , _) | refl = driver n , driver-target chosen
hidden-complete (callback {s = s} {a = a} Events.checking pr) with Exec.lookup a s in chosen | Exec.next-complete pr
... | just (_ , _) | refl = callbackValue a , callback-target refl chosen
hidden-complete (callback {s = s} {a = a} Events.stopping pr) with Exec.lookup a s in chosen | Exec.next-complete pr
... | just (_ , _) | refl = callbackValue a , callback-target refl chosen
hidden-complete (callback {s = s} {a = a} Events.canceledHandler pr) with Exec.lookup a s in chosen | Exec.next-complete pr
... | just (_ , _) | refl = callbackValue a , callback-target refl chosen

-- Hidden progress is impossible after the stored checkDone result has been returned.
tau-live : ∀ {s t} → Tau s t → Source.outcome s ≡ nothing
tau-live (scheduled pr) = Source.tau-live pr
tau-live (callback _ pr) = Source.step-live pr

-- One native client instance fixes the endpoint while retaining all callback choices.
module At (l : Link) (d : Dir) where
  open Events.At l d using (decode; observe; project) public

  -- Visible targets reuse the independently certified source interpreter after decode.
  next : C.State → LTS.Event → Maybe C.State
  next s e with decode e
  ... | nothing = nothing
  ... | just a = Exec.next s a

  -- Forward declarations retain productive simultaneous visible and hidden offers.
  tree : C.State → Proc
  offers : (s : C.State) (at : AnyTypes LNPEv) → ContinueType at (Maybe Proc)
  branches : (s : C.State) (at : AnyTypes Branches) → ContinueType at (Maybe Proc)

  -- The closed client returns the precise value selected by checkDone's terminating branch.
  PTree.force (tree s) with Source.outcome s
  ... | just value = ret value
  ... | nothing = react (offers s) (branches s)

  -- Receiver and main-thread wire/API operations remain independently enabled.
  offers s (X , ch) value with next s (LTS.evLabel X ch value)
  ... | nothing = nothing
  ... | just t = just (tree t)

  -- The scheduler uses certificates from either source scheduling or erased callbacks.
  branches s (_ , schedule) choice with hidden s choice
  ... | nothing = nothing
  ... | just (t , pr) = just (tree t)

  -- Fresh native client entry point before the first checkDone decision.
  client : Proc
  client = tree C.initial

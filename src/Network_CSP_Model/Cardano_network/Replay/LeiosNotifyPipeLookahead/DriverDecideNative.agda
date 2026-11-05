{-# OPTIONS --guardedness #-}

-- Decide exact native paired prefix realizability by transporting the unrestricted source decision.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideNative (p : Params) where

open import Data.List using (List; _∷_; []; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p ⊤ as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p ⊤ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverEndpointBridge p ⊤ as Endpoint
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Notification notificationEq (votes []) as Check
open Native using (module LTS; module Traces)

-- Endpoint coordinates and the declared abstract server contract stay fixed throughout a trace.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  module Product = Native.At contract cl sl cd sd
  module Proof = Bridge.At contract cl sl cd sd
  module Endpoints = Endpoint.At contract cl sl cd sd

  -- Exact decoding gives one source row list for any actual native event list.
  matches-unique : ∀ {events rows other} → Proof.Matches events rows →
    Proof.Matches events other → rows ≡ other
  matches-unique Proof.empty Proof.empty = refl
  matches-unique (Proof.matched first rest) (Proof.matched second later) =
    cong₂ _∷_ (just-injective (trans (sym first) second)) (matches-unique rest later)

  -- Native evidence retains every event, its exact decoded rows and the actual PTree execution.
  NativeTrace : List Rows.ClientRow → List Rows.ServerRow → Set₁
  NativeTrace client server = Σ[ events ∈ List LTS.Event ] Σ[ rows ∈ List D.Event ]
    Σ[ target ∈ D.State ]
      (Rows.Merge client server rows × Proof.Matches events rows ×
        Product.tree D.initial Traces.⟹∖√⟨ events ⟩ Product.tree target)

  -- Canonical packet realization gives a native witness for each accepted source merge.
  realize : ∀ {client server} → Check.SourceTrace contract client server → NativeTrace client server
  realize (rows , merged , target , source) =
    map Product.encode rows , rows , target , merged , Proof.canonical-matches rows , Proof.realize source

  -- Every actual native witness reconstructs an unrestricted source run with the same supplied rows.
  sound : ∀ {client server} → NativeTrace client server → Check.SourceTrace contract client server
  sound (events , rows , target , merged , matches , native) with Proof.sound native
  ... | actual , reached , actualMatches , source , same = rows , merged , reached ,
    subst (λ exact → D.Run contract D.initial exact reached)
      (sym (matches-unique matches actualMatches)) source

  -- No canonical-witness assumption is required in the native-to-source direction.
  equivalence : ∀ client server →
    (Check.SourceTrace contract client server → NativeTrace client server) ×
    (NativeTrace client server → Check.SourceTrace contract client server)
  equivalence client server = realize , sound

  -- The decision refutes all matching native paired executions, not merely a selected event encoding.
  decide : (client : List Rows.ClientRow) (server : List Rows.ServerRow) → Dec (NativeTrace client server)
  decide client server with Check.decide contract client server
  ... | yes source = yes (realize source)
  ... | no absent = no λ native → absent (sound native)

  -- Acceptance also yields actual local native client/server executions with matching wire order.
  local-endpoints : ∀ {client server} → Check.SourceTrace contract client server →
    Σ[ rows ∈ List D.Event ] Σ[ target ∈ D.State ]
      (Rows.Merge client server rows × Endpoints.Endpoints D.initial rows target)
  local-endpoints (rows , merged , target , source) =
    rows , target , merged , Endpoints.realize-endpoints source

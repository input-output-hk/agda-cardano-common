{-# OPTIONS --guardedness #-}

-- The full-policy paired decision transports to actual native PTree paths.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverDecideNative (p : Params) where

open import Data.List using (List; [])
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p using (Notification; notificationEq; votes)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverDecide Notification notificationEq (votes []) as Source
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverNetworkBridge p as Bridge

-- Native observation fixes both endpoint coordinates before any trace search.
module At (cl sl : Link) (cd sd : Dir) where
  module B = Bridge.At cl sl cd sd

  -- Compatibility means an actual full-policy path whose wire rows merge the supplied endpoint inputs.
  NativePair : List Rows.ClientRow → List Rows.ServerRow → Set₁
  NativePair client server = Σ[ rows ∈ List D.Event ]
    (Rows.Merge client server rows × B.NativeWireTrace Node.initial rows)

  -- An accepted source decision supplies every erased input action and its exact native realization.
  source-to-native : ∀ {client server} → Source.SourceTrace client server → NativePair client server
  source-to-native (rows , merged , target , actions , run , observed) =
    rows , merged , B.source-wire-to-native (actions , target , run , observed)

  -- Arbitrary native paths recover original full node rules without assuming tree injectivity.
  native-to-source : ∀ {client server} → NativePair client server → Source.SourceTrace client server
  native-to-source (rows , merged , native) with B.native-wire-to-source native
  ... | actions , target , run , observed = rows , merged , target , actions , run , observed

  -- Both implications concern finite wire observations of the unchanged native policy tree.
  equivalence : ∀ client server →
    (Source.SourceTrace client server → NativePair client server) ×
    (NativePair client server → Source.SourceTrace client server)
  equivalence client server = source-to-native , native-to-source

  -- A negative decision rules out every compatible actual native path, not just a selected schedule.
  decide : (client : List Rows.ClientRow) (server : List Rows.ServerRow) → Dec (NativePair client server)
  decide client server with Source.decide client server
  ... | yes witness = yes (source-to-native witness)
  ... | no absent = no λ native → absent (native-to-source native)

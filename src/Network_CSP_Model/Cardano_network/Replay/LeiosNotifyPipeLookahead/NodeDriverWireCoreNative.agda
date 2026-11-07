{-# OPTIONS --guardedness #-}

-- The normalized core preserves the existing exact full-policy native wire language.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverWireCoreNative (p : Params) where

open import Data.List using (List; map; mapMaybe)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p using (Notification)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBridge Notification as Reduction
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverNetwork p as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverNetworkBridge p as Bridge
open Native using (module LTS; module Traces)

-- Fixed endpoint coordinates match the original full-policy native bridge.
module At (cl sl : Link) (cd sd : Dir) where
  module N = Native.At cl sl cd sd
  module B = Bridge.At cl sl cd sd

  -- Rehydration retains specified original endpoints and every wire row before native realization.
  realize : ∀ {s rows t} → Core.Run (Core.erase s) rows (Core.erase t) →
    Σ[ actions ∈ List Node.Action ]
      (Node.Run s actions t × Node.wireRows actions ≡ rows ×
       N.tree s Traces.⟹∖√⟨ map N.encode actions ⟩ N.tree t)
  realize {s} {rows} {t} reduced with Reduction.core-to-source {s = s} {rows = rows} {t = t} reduced
  ... | actions , source , same = actions , source , same , B.realize source

  -- Every actual native path normalizes to the same observed wire order and retained target fields.
  normalize : ∀ {s es P} → N.tree s Traces.⟹∖√⟨ es ⟩ P →
    Σ[ target ∈ Node.State ]
      (Core.Run (Core.erase s) (mapMaybe N.observe es) (Core.erase target) × P ≡ N.tree target)
  normalize {s} {es} {P} path with B.sound {s = s} {es = es} {P = P} path
  ... | actions , target , matches , source , same = target ,
    subst (λ rows → Core.Run (Core.erase s) rows (Core.erase target))
      (sym (B.wire-observation matches)) (Reduction.erase-run source) , same

  -- The target keeps an original-state witness, with arbitrary external snapshots permitted.
  CoreWire : Node.State → List D.Event → Set
  CoreWire s rows = Σ[ target ∈ Node.State ] Core.Run (Core.erase s) rows (Core.erase target)

  -- A reduced wire run supplies an actual native path of the unchanged full-policy tree.
  core-to-native : ∀ {s rows} → CoreWire s rows → B.NativeWireTrace s rows
  core-to-native {s} {rows} (target , reduced) with Reduction.core-to-source {s = s} {rows = rows} {t = target} reduced
  ... | actions , source , same = B.source-wire-to-native (actions , target , source , same)

  -- Actual native compatibility recovers an independent reduced run without dropping wire rows.
  native-to-core : ∀ {s rows} → B.NativeWireTrace s rows → CoreWire s rows
  native-to-core native with B.native-wire-to-source native
  ... | actions , target , source , same = target , Reduction.source-to-core (actions , source , same)

  -- This is finite wire-trace equivalence; divergent erased input histories are not equated.
  wire-equivalence : ∀ s rows →
    (CoreWire s rows → B.NativeWireTrace s rows) × (B.NativeWireTrace s rows → CoreWire s rows)
  wire-equivalence s rows = core-to-native , native-to-core

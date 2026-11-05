{-# OPTIONS --guardedness #-}

-- Transport an explicitly declared deletion observation through the existing exact native server bridge.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.WireNative (p : Params) where

open import Data.List using (List; []; _∷_; map; mapMaybe)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyP p using (LNPEv)
import Cardano_network.LeiosNotifyPipe p as Payloads
import Cardano_network.LeiosNotifyPipeLookahead p as Native
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as Source
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents p as Events
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerBridge p as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerEventsBridge p as Encoding
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS
import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} as Traces

-- The observer declares exactly which source actions and payload fields are retained.
module For (Row : Set) (observeAction : Source.Action → Maybe Row)
  (contract : Source.Contract) (l : Link) (d : Dir) where
  module Machine = Native.Machine contract l d
  module Exact = Bridge.For contract l d
  module Canonical = Encoding.For contract l d

  -- Decode at the fixed endpoint before applying the caller's observation.
  observe : LTS.Event → Maybe Row
  observe event with Machine.decode event
  ... | nothing = nothing
  ... | just action = observeAction action

  -- An abstract observation is witnessed by real source operations from the fresh state.
  SourceTrace : List Row → Set
  SourceTrace rows = Σ[ actions ∈ List Source.Action ] Σ[ target ∈ Source.State ]
    (Source.Run contract Source.initial actions target × mapMaybe observeAction actions ≡ rows)

  -- Native evidence retains the complete unprojected event list and its actual PTree path.
  NativeTrace : List Row → Set₁
  NativeTrace rows = Σ[ events ∈ List LTS.Event ] Σ[ target ∈ Source.State ]
    (Machine.tree Source.initial Traces.⟹∖√⟨ events ⟩ Machine.tree target × mapMaybe observe events ≡ rows)

  -- A successful exact decode makes the native and source observations identical.
  observe-decoded : ∀ {event action} → Machine.decode event ≡ just action →
    observe event ≡ observeAction action
  observe-decoded {event} decoded rewrite decoded = refl

  -- The existing exact native/source matching relation preserves every declared observation.
  matches-observation : ∀ {events actions} → Exact.Matches events actions →
    mapMaybe observe events ≡ mapMaybe observeAction actions
  matches-observation Exact.empty = refl
  matches-observation {events = event ∷ events} {actions = action ∷ actions}
    (Exact.matched decoded matches)
    with observe event | observeAction action | observe-decoded {event = event} {action = action} decoded
  ... | nothing | .nothing | refl = matches-observation {events = events} {actions = actions} matches
  ... | just row | .(just row) | refl =
    cong (row ∷_) (matches-observation {events = events} {actions = actions} matches)

  -- Canonical event realization keeps exact values; erased API actions remain in the native witness.
  canonical-observation : ∀ actions →
    mapMaybe observe (map (Events.encode l d) actions) ≡ mapMaybe observeAction actions
  canonical-observation actions = matches-observation (Exact.canonical-matches actions)

  -- Every source-observed prefix has a real exact-payload native execution.
  realize : ∀ {rows} → SourceTrace rows → NativeTrace rows
  realize (actions , target , execution , same) =
    map (Events.encode l d) actions , target , Exact.realize execution ,
    trans (canonical-observation actions) same

  -- Every native execution reconstructs a source-observed prefix, even with callback APIs erased.
  source-from-native : ∀ {events target} →
    Machine.tree Source.initial Traces.⟹∖√⟨ events ⟩ target →
    SourceTrace (mapMaybe observe events)
  source-from-native execution with Exact.sound execution
  ... | actions , reached , matches , source , same =
    actions , reached , source , sym (matches-observation matches)

  -- Native observation cannot add a wire history absent from the independent source model.
  sound : ∀ {rows} → NativeTrace rows → SourceTrace rows
  sound (events , target , execution , same) with source-from-native execution
  ... | actions , reached , source , projected = actions , reached , source , trans projected same

  -- Both prefix languages coincide for this explicit observer; termination ticks remain excluded.
  equivalence : ∀ rows → (SourceTrace rows → NativeTrace rows) × (NativeTrace rows → SourceTrace rows)
  equivalence rows = realize , sound

{-# OPTIONS --guardedness #-}

-- Exact native client wire observation, deleting callback/API observations explicitly.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.WireClientNative
  (p : Params) (Return : Set) where

open import Data.List using (List; []; _∷_; mapMaybe)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p using (Notification)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork p Return as N
import Cardano_network.LeiosNotifyPipeLookahead.ClientEvents p Return N.Branches as Events
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientNetworkBridge p Return as ExactBridge
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as W
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientQuotient Notification Return as Quotient
module Wire = W.Observation Return
open N using (module LTS; module Traces)

-- Generic deletion transport requires an explicit proof that native hidden callbacks stay erased.
module Transport (Row : Set) (observeAction : C.Action → Maybe Row)
  (hidden-erased : ∀ {action} → Events.Hidden action → observeAction action ≡ nothing)
  (l : Link) (d : Dir) where
  module Machine = N.At l d
  module Exact = ExactBridge.At l d

  -- Decode at this fixed endpoint, retaining only the caller's declared source observation.
  observe : LTS.Event → Maybe Row
  observe event with Machine.decode event
  ... | nothing = nothing
  ... | just action = observeAction action

  -- Source evidence retains all callback choices and an actual independent fresh source execution.
  SourceTrace : List Row → Set
  SourceTrace rows = Σ[ actions ∈ List C.Action ] Σ[ target ∈ C.State ]
    (C.Run C.initial actions target × mapMaybe observeAction actions ≡ rows)

  -- A native witness retains every visible API/network event and an arbitrary actual PTree endpoint.
  NativeTrace : List Row → Set₁
  NativeTrace rows = Σ[ events ∈ List LTS.Event ] Σ[ target ∈ N.Proc ]
    (Machine.tree C.initial Traces.⟹∖√⟨ events ⟩ target × mapMaybe observe events ≡ rows)

  -- Successful exact decode identifies the same declared observation on either side.
  observe-decoded : ∀ {event action} → Machine.decode event ≡ just action →
    observe event ≡ observeAction action
  observe-decoded {event} decoded rewrite decoded = refl

  -- Matching permits both genuinely quiet callbacks and visible normal API callbacks later deleted.
  matches-observation : ∀ {events actions} → Exact.Matches events actions →
    mapMaybe observe events ≡ mapMaybe observeAction actions
  matches-observation Exact.empty = refl
  matches-observation (Exact.quiet hidden matches) rewrite hidden-erased hidden = matches-observation matches
  matches-observation {events = event ∷ events} {actions = action ∷ actions}
    (Exact.emitted decoded matches)
    with observe event | observeAction action | observe-decoded {event = event} {action = action} decoded
  ... | nothing | .nothing | refl = matches-observation {events = events} {actions = actions} matches
  ... | just row | .(just row) | refl =
    cong (row ∷_) (matches-observation {events = events} {actions = actions} matches)

  -- Canonical projection includes every normal delivery API event even when its wire observation is empty.
  canonical-observation : ∀ actions →
    mapMaybe observe (Machine.project actions) ≡ mapMaybe observeAction actions
  canonical-observation actions = matches-observation (Exact.canonical-matches actions)

  -- Every source-observed prefix realizes an actual native path using the existing exact bridge.
  realize : ∀ {rows} → SourceTrace rows → NativeTrace rows
  realize (actions , target , execution , same) =
    Machine.project actions , Machine.tree target , Exact.realize execution ,
    trans (canonical-observation actions) same

  -- Every actual native path, including noncanonical scheduling and arbitrary endpoints, reconstructs source evidence.
  source-from-native : ∀ {events target} →
    Machine.tree C.initial Traces.⟹∖√⟨ events ⟩ target → SourceTrace (mapMaybe observe events)
  source-from-native execution with Exact.sound execution
  ... | actions , reached , matches , source , same =
    actions , reached , source , sym (matches-observation matches)

  -- Native observations cannot acquire a prefix absent from the independent source model.
  sound : ∀ {rows} → NativeTrace rows → SourceTrace rows
  sound (events , target , execution , same) with source-from-native execution
  ... | actions , reached , source , projected = actions , reached , source , trans projected same

  -- Both finite no-return-tick observation languages coincide for the declared callback deletion.
  equivalence : ∀ rows → (SourceTrace rows → NativeTrace rows) × (NativeTrace rows → SourceTrace rows)
  equivalence rows = realize , sound

-- The quotient projection is precisely the declared mapMaybe deletion of all successful callbacks.
wire-mapMaybe : ∀ actions → Wire.wire actions ≡ mapMaybe Wire.observe actions
wire-mapMaybe [] = refl
wire-mapMaybe (C.sendRequest ∷ actions) rewrite wire-mapMaybe actions = refl
wire-mapMaybe (C.sendQuit ∷ actions) rewrite wire-mapMaybe actions = refl
wire-mapMaybe (C.recvReply _ ∷ actions) rewrite wire-mapMaybe actions = refl
wire-mapMaybe (C.recvDone ∷ actions) rewrite wire-mapMaybe actions = refl
wire-mapMaybe (C.continue _ ∷ actions) = wire-mapMaybe actions
wire-mapMaybe (C.terminate _ ∷ actions) = wire-mapMaybe actions
wire-mapMaybe (C.handled _ ∷ actions) = wire-mapMaybe actions

-- Existing silent checkDone/termination/Canceled handling agrees with the stronger wire deletion.
wire-hidden : ∀ {action} → Events.Hidden action → Wire.observe action ≡ nothing
wire-hidden Events.checking = refl
wire-hidden Events.stopping = refl
wire-hidden Events.canceledHandler = refl

-- Each endpoint reuses the exact generic client quotient, retaining its receive-ahead Lead state.
module At (l : Link) (d : Dir) where
  module Observation = Transport W.Wire Wire.observe wire-hidden l d

  -- This is the already certified exact source wire language, with callback decisions retained in its witness.
  SourceTrace : List W.Wire → Set
  SourceTrace = Quotient.SourceTrace

  -- Native observations retain full API-inclusive paths to arbitrary actual native endpoints.
  NativeTrace : List W.Wire → Set₁
  NativeTrace = Observation.NativeTrace

  -- Projection equality adapts exact source witnesses without rescheduling any source operation.
  source-observation : ∀ {rows} → SourceTrace rows → Observation.SourceTrace rows
  source-observation (actions , target , source , same) = actions , target , source ,
    trans (sym (wire-mapMaybe actions)) same

  -- The inverse projection transport retains the original source actions and endpoint.
  observation-source : ∀ {rows} → Observation.SourceTrace rows → SourceTrace rows
  observation-source (actions , target , source , same) = actions , target , source ,
    trans (wire-mapMaybe actions) same

  -- Accepted source prefixes have real native paths, with visible normal handlers deleted only observationally.
  realize : ∀ {rows} → SourceTrace rows → NativeTrace rows
  realize source = Observation.realize (source-observation source)

  -- Every actual native wire observation reconstructs an exact independent source witness.
  sound : ∀ {rows} → NativeTrace rows → SourceTrace rows
  sound native = observation-source (Observation.sound native)

  -- Arbitrary actual native paths are sound even when their target was not supplied as a source tree.
  source-from-native : ∀ {events target} →
    N.At.tree l d C.initial Traces.⟹∖√⟨ events ⟩ target →
    SourceTrace (mapMaybe Observation.observe events)
  source-from-native path = observation-source (Observation.source-from-native path)

  -- Native-to-quotient transport needs no inhabitance premise on Return.
  native→quotient : ∀ {rows} → NativeTrace rows → W.HasTrace W.initial rows
  native→quotient native = Quotient.source→quotient (sound native)

  -- Native synthesis from the quotient explicitly supplies a successful termination return value.
  quotient→native : Return → ∀ {rows} → W.HasTrace W.initial rows → NativeTrace rows
  quotient→native value admitted = realize (Quotient.quotient→source value admitted)

  -- Exact source/native wire prefix languages coincide without claiming a return tick was observed.
  equivalence : ∀ rows → (SourceTrace rows → NativeTrace rows) × (NativeTrace rows → SourceTrace rows)
  equivalence rows = realize , sound

  -- Exhaustive source rejection transports to all native paths rather than one canonical realization.
  decide : Return → (rows : List W.Wire) → Dec (NativeTrace rows)
  decide value rows with Quotient.decide-source value rows
  ... | yes source = yes (realize source)
  ... | no absent = no λ native → absent (sound native)

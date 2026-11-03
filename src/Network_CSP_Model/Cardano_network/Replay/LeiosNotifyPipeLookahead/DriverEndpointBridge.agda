{-# OPTIONS --guardedness #-}

-- A paired driver witness yields actual native executions of both local endpoints.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverEndpointBridge (p : Params) (Return : Set) where

open import Data.List using (List; []; _∷_; map; mapMaybe)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Process_Trees using (ExtI)
open import Cardano_network.LeiosNotifyP p using (LNPEv)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification Return as Projection
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as Pair
import Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork p Return as Client
import Cardano_network.LeiosNotifyPipeLookahead.ClientEvents p Return Client.Branches as CE
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents p as SE
import Cardano_network.LeiosNotifyPipeLookahead p as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientNetworkBridge p Return as CB
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientEventsBridge p Return as CEncoding
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerBridge p as SB
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerEventsBridge p as SEncoding
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p Return as PB
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS
import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} as Traces

-- Native endpoint instances are fixed while the product interleaves their driver work.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  module ClientTree = Client.At cl cd
  module ClientProof = CB.At cl cd
  module ClientEncoding = CEncoding.At cl cd
  module ServerTree = Server.Machine contract sl sd
  module ServerProof = SB.For contract sl sd
  module ServerEncoding = SEncoding.For contract sl sd
  module Product = Pair.At contract cl sl cd sd
  module ProductProof = PB.At contract cl sl cd sd
  module Sources = Projection.For contract

  -- Decode only local client wire rows; normal API deliveries remain outside driver logs.
  clientRow : Client.LTS.Event → Maybe D.Event
  clientRow event with ClientTree.decode event
  ... | nothing = nothing
  ... | just action = Projection.clientWire action

  -- Server readiness API events likewise contribute no driver wire record.
  serverRow : LTS.Event → Maybe D.Event
  serverRow event with ServerTree.decode event
  ... | nothing = nothing
  ... | just action = Projection.serverWire action

  -- Declared erased client actions are all invisible in the wire-record profile too.
  client-hidden-wire : ∀ {a} → CE.Hidden a → Projection.clientWire a ≡ nothing
  client-hidden-wire CE.checking = refl
  client-hidden-wire CE.stopping = refl
  client-hidden-wire CE.canceledHandler = refl

  -- Native client realization preserves precisely its source wire record order.
  client-wire-projection : ∀ actions →
    mapMaybe clientRow (ClientTree.project actions) ≡ mapMaybe Projection.clientWire actions
  client-wire-projection [] = refl
  client-wire-projection (a ∷ actions) with ClientEncoding.view a
  ... | ClientEncoding.quiet h erased rewrite erased | client-hidden-wire h = client-wire-projection actions
  ... | ClientEncoding.emitted event observed decoded rewrite observed | decoded
    with Projection.clientWire a
  ...   | nothing = client-wire-projection actions
  ...   | just row = cong (row ∷_) (client-wire-projection actions)

  -- Native server realization preserves its source wire records while retaining APIs locally.
  server-wire-projection : ∀ actions →
    mapMaybe serverRow (map (SE.encode sl sd) actions) ≡ mapMaybe Projection.serverWire actions
  server-wire-projection [] = refl
  server-wire-projection (a ∷ actions) rewrite ServerEncoding.decode-encode a with Projection.serverWire a
  ... | nothing = server-wire-projection actions
  ... | just row = cong (row ∷_) (server-wire-projection actions)

  -- Local native executions share the product's exact endpoint states and wire histories.
  record Endpoints (start : D.State) (rows : List D.Event) (finish : D.State) : Set₁ where
    constructor endpoints
    field
      clientActions : List C.Action
      serverActions : List S.Action
      clientNative : ClientTree.tree (D.clientState start)
        Client.Traces.⟹∖√⟨ ClientTree.project clientActions ⟩ ClientTree.tree (D.clientState finish)
      serverNative : ServerTree.tree (D.serverState start)
        Traces.⟹∖√⟨ map (SE.encode sl sd) serverActions ⟩ ServerTree.tree (D.serverState finish)
      clientRecords : mapMaybe clientRow (ClientTree.project clientActions) ≡ Projection.clientRows rows
      serverRecords : mapMaybe serverRow (map (SE.encode sl sd) serverActions) ≡ Projection.serverRows rows

  -- Every independently witnessed product execution supplies both native endpoint runs.
  realize-endpoints : ∀ {s rows t} → D.Run contract s rows t → Endpoints s rows t
  realize-endpoints run with Sources.client run | Sources.server run
  ... | clientActions , clientRun , clientWire | serverActions , serverRun , serverWire =
    endpoints clientActions serverActions (ClientProof.realize clientRun) (ServerProof.realize serverRun)
      (trans (client-wire-projection clientActions) clientWire)
      (trans (server-wire-projection serverActions) serverWire)

  -- Every actual native paired trace has endpoint witnesses with exactly its decoded rows.
  native-endpoints : ∀ {s es P} → Product.tree s Pair.Traces.⟹∖√⟨ es ⟩ P →
    Σ[ rows ∈ List D.Event ] Σ[ t ∈ D.State ]
      (ProductProof.Matches es rows × Endpoints s rows t × P ≡ Product.tree t)
  native-endpoints run with ProductProof.sound run
  ... | rows , t , matches , source , same = rows , t , matches , realize-endpoints source , same

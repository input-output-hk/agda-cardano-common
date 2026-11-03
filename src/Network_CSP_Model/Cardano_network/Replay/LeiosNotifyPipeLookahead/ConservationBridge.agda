{-# OPTIONS --guardedness #-}

-- Universal finite native paired traces inherit conservation through source inversion.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ConservationBridge
  (p : Params) (Return : Set) where

open import Data.List using (List; mapMaybe)
open import Data.Nat using (_+_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as Native
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification Return as Transport
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification Return as Projection
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p Return as Bridge

-- Each theorem fixes its callback contract and both observed endpoint coordinates.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- The native paired tree retains the selected endpoint coordinates.
  module Tree = Native.At contract cl sl cd sd
  -- Existing inversion reconstructs source records and the exact final product state.
  module Proof = Bridge.At contract cl sl cd sd
  -- Endpoint extraction retains every server wire record.
  module Endpoint = Projection.For contract

  -- Actual native traces reconstruct matching records, exact FIFO balance and owed work.
  conservation : ∀ {es P} → Tree.tree D.initial Native.Traces.⟹∖√⟨ es ⟩ P →
    Σ[ rows ∈ List D.Event ] Σ[ t ∈ D.State ] Σ[ actions ∈ List S.Action ]
      (Proof.Matches es rows × P ≡ Tree.tree t ×
       Transport.Balanced (Transport.observe rows Transport.empty) t ×
       S.Run contract S.initial actions (D.serverState t) ×
       mapMaybe Projection.serverWire actions ≡ Projection.serverRows rows ×
       Server.requests actions ≡ Server.replies actions + S.owed (D.serverState t))
  conservation trace with Proof.sound trace
  ... | rows , t , matching , source , same with Endpoint.server source
  ...   | actions , server , wire = rows , t , actions , matching , same ,
    Transport.initial-conservation source , server , wire , Server.initial-balance server

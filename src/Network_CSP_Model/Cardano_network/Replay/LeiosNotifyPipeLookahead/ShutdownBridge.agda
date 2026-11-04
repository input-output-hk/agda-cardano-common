{-# OPTIONS --guardedness #-}

-- Native step/trace inversion transports exact shutdown and Done guarantees.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownBridge (p : Params) (Return : Set) where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as Native
import Cardano_network.LeiosNotifyPipeLookahead.ClientShutdown Notification Return as Client
import Cardano_network.LeiosNotifyPipeLookahead.ServerShutdown Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.DriverShutdown Notification Return as Driver
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p Return as Bridge

-- Exact endpoint tags and callback policy remain fixed throughout each native continuation.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- The native source tree keeps its original alphabet and transition rules.
  module Tree = Native.At contract cl sl cd sd
  -- Existing inversion reconstructs every actual hidden or visible source operation.
  module Proof = Bridge.At contract cl sl cd sd
  -- The paired safety results use the identical responder callback contract.
  module Paired = Driver.For contract
  open Native using (module LTS; module Traces)

  -- A native Quit record enters persistent client shutdown at its actual source target.
  quit-starts : ∀ {s e P} → Tree.decode e ≡ just (D.clientSend D.quit) →
    Tree.tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P →
    Σ[ t ∈ D.State ] (P ≡ Tree.tree t × Client.stopping (C.main (D.clientState t)) ≡ true)
  quit-starts observed step with Proof.visible-elim step
  ... | row , t , decoded , source , same with just-injective (trans (sym decoded) observed)
  ...   | refl with source
  ...     | D.clientSent pr = t , same , Client.quit-starts pr

  -- No actual native continuation after shutdown can publish a new RequestNext record.
  no-request-after : ∀ {s es P e Q} → Client.stopping (C.main (D.clientState s)) ≡ true →
    Tree.tree s Traces.⟹∖√⟨ es ⟩ P → Tree.decode e ≡ just (D.clientSend D.request) →
    P LTS.─[ LTS.ev (LTS.evl e) ]─► Q → ⊥
  no-request-after stopped trace observed step with Proof.sound trace
  ... | rows , t , matching , source , refl with Proof.visible-elim step
  ...   | row , u , decoded , next , same with just-injective (trans (sym decoded) observed)
  ...     | refl = Driver.no-client-request (Paired.client-stays-stopping source stopped) next

  -- The exact target of a native hidden step can newly select only cancellation after the flag.
  new-selection-after-flag : ∀ {s P} → S.quitFlag (D.serverState s) ≡ true →
    S.sender (D.serverState s) ≡ S.claimed → Tree.tree s LTS.─[ LTS.τ ]─► P →
    Σ[ t ∈ D.State ] (P ≡ Tree.tree t ×
      (∀ {msg} → S.sender (D.serverState t) ≡ S.selected msg → msg ≡ S.canceled))
  new-selection-after-flag flag before step with Proof.hidden-elim step
  ... | t , source , same = t , same , Driver.new-selection-after-flag source flag before

  -- Native continuations retain publication, so the new-selection rule applies at all later prefixes.
  flag-stays : ∀ {s es P} → S.quitFlag (D.serverState s) ≡ true →
    Tree.tree s Traces.⟹∖√⟨ es ⟩ P →
    Σ[ t ∈ D.State ] (P ≡ Tree.tree t × S.quitFlag (D.serverState t) ≡ true)
  flag-stays published trace with Proof.sound trace
  ... | rows , t , matching , source , same = t , same , Paired.server-stays-flagged source published

  -- A native server Done hook requires a drained server, allowing outstanding client work.
  sent-done : ∀ {s e P} → Tree.decode e ≡ just (D.serverSend D.done) →
    Tree.tree s LTS.─[ LTS.ev (LTS.evl e) ]─► P →
    Σ[ t ∈ D.State ] (P ≡ Tree.tree t × Server.Final (D.serverState s) × Server.Final (D.serverState t))
  sent-done observed step with Proof.visible-elim step
  ... | row , t , decoded , source , same with just-injective (trans (sym decoded) observed)
  ...   | refl with Driver.server-done-final source
  ...     | before , after = t , same , before , after

  -- A fresh native Done receive certifies both peers' completed source work and return value.
  received-done : ∀ {es P e Q} → Tree.tree D.initial Traces.⟹∖√⟨ es ⟩ P →
    Tree.decode e ≡ just (D.clientRecv D.done) → P LTS.─[ LTS.ev (LTS.evl e) ]─► Q →
    Σ[ t ∈ D.State ] (Q ≡ Tree.tree t × Driver.Completed t)
  received-done trace observed step with Proof.sound trace
  ... | rows , s , matching , source , refl with Proof.visible-elim step
  ...   | row , t , decoded , next , same with just-injective (trans (sym decoded) observed)
  ...     | refl = t , same , Paired.client-done-completed source next

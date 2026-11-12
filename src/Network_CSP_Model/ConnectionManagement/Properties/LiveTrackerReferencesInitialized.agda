{-# OPTIONS --guardedness #-}

-- Empty pending CM continuations suffice for every physical handler's original
-- references. Birth inversion recovers allocation and fork occurrences; resource
-- and promise retention then transport their evidence to the current state.
module ConnectionManagement.Properties.LiveTrackerReferencesInitialized where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List using (_∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst)
open import ConnectionManagement.Domain using (ErrorId; HandleId; PromiseId)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
import ConnectionManagement.State as S
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.Properties.LiveTrackerReferences as Statement
import ConnectionManagement.Properties.LivePromiseFrontend as Promise
import ConnectionManagement.Properties.HandlerBirthBacking as Birth
import ConnectionManagement.Properties.CollectedInboundOrigin as Inbound
import ConnectionManagement.Properties.CollectedOutboundOrigin as Outbound
import ConnectionManagement.Properties.InboundOriginRuntime as InboundRuntime
import ConnectionManagement.Properties.OutboundOriginFrontend as OutboundRuntime
import ConnectionManagement.Properties.OutboundBirthResources as OutboundBirth

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 open Model.Protocols b io capability using (Runtime; Runs; initialize; more; stop)
 open Statement.Frontend b io capability public using (PhysicalReferences; physicalState; shared)
 open Birth.Frontend b io capability using (initialized-birth)
 open Outbound.Frontend b io capability using (from-backing)
 open InboundRuntime.Frontend.Located b io capability using () renaming (from-runs to from-inbound-runs)
 open OutboundRuntime.Frontend b io capability using () renaming (from-runs to from-outbound-runs)
 private
  module I = Inbound.Frontend.InboundOrigin
  module F = InboundRuntime.Frontend.Located.ForkOrigin b io capability
  module Selection = InboundRuntime.Frontend.Located.History.SelectedOrigin b io capability
  module Origin = OutboundRuntime.Frontend.History.Origin b io capability
  module Packet = Outbound.Frontend.BirthPacket
  module Result = Outbound.Frontend.OutboundOrigin
  module Owner = OutboundBirth.Frontend.Outbound

 -- The observer carries membership through any actual frontend suffix.
 retain-promise : ∀ p {before events after} → Runs before events after →
   p ∈ S.promises (shared before) → p ∈ S.promises (shared after)
 retain-promise p = Promise.Frontend.run-preserves b io p capability

 -- The inbound packet's promise is allocated before selection. Its actual
 -- allocation gap, selection event, fork gap, fork and suffix all retain it.
 inbound-promise : ∀ {input governor start current events worker captured} →
   Inbound.Frontend.InboundOrigin b io capability input governor start current events worker captured →
   S.handlerPromise captured ∈ S.promises (shared current)
 inbound-promise {current = current} origin = subst (λ p → p ∈ S.promises (shared current))
   (sym (cong S.handlerPromise (I.descriptor origin)))
   (retain-promise _ (I.suffix-run origin)
     (retain-promise _ (more {s = I.before origin} {a = I.label origin} (F.fork-event recovered) stop)
       (retain-promise _ (from-inbound-runs (Selection.fork-gap-run selected))
         (retain-promise _ (more {s = Selection.selectionBefore selected} {a = Selection.selectionLabel selected} (Selection.selection-event selected) stop)
           (retain-promise _ (from-inbound-runs (Selection.allocation-gap-run selected))
             (I.promise-allocated origin))))))
   where
   recovered = I.reconstructed origin
   selected = F.selection recovered

 -- The outbound allocation-to-fork gap likewise retains the original cell.
 outbound-promise : ∀ {input governor start current events worker captured} →
   Outbound.Frontend.OutboundOrigin b io capability input governor start current events worker captured →
   S.handlerPromise captured ∈ S.promises (shared current)
 outbound-promise {current = current} origin = subst (λ p → p ∈ S.promises (shared current))
   (sym (cong S.handlerPromise (Owner.descriptor (Packet.owner packet))))
   (retain-promise _ (Result.suffix-run origin)
     (retain-promise _ (more {s = Packet.before packet} {a = Packet.label packet} (Packet.actual packet) stop)
       (retain-promise _ (from-outbound-runs (Origin.fork-gap-run (Packet.reconstructed packet)))
         (Packet.promise-allocated packet))))
   where packet = Result.packet origin

 -- No heap bound, live map binding, open socket, governor registration or
 -- completion premise is added. Terminal physical rows are included too.
 from-initial : ∀ c₀ g {start events s} →
   initialize (O.initial c₀) g ≡ just start → Runs start events s → PhysicalReferences s
 from-initial c₀ g initialized path w thread found with
   from-backing c₀ g initialized (initialized-birth initialized path found)
 ... | inj₁ origin = I.retained origin , inbound-promise origin
 ... | inj₂ origin = Result.retained origin , outbound-promise origin

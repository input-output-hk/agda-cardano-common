{-# OPTIONS --guardedness #-}

-- Publication-failure snapshots have their own exact descriptors, resources
-- and negotiated chains at every initialized frontend state.
module ConnectionManagement.Properties.LiveTrackerFailuresInitialized where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.Properties.LiveTrackerFailureContent as Failure
import ConnectionManagement.Properties.LiveTrackerFailureFrontend as FailureFront
import ConnectionManagement.Properties.LiveTrackerFrameContent as Content
import ConnectionManagement.Properties.LiveTrackerChainSteps as Chain
import ConnectionManagement.Properties.LiveTrackerChainsInitialized as Chains
import ConnectionManagement.Properties.LiveTrackerSnapshotsInitialized as Snapshot
import ConnectionManagement.Properties.LiveTrackerReferencesInitialized as Physical

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 open Model.Protocols b io capability using (Runtime; Runs; initialize; base; publication; sourceOf)
 private module N = Publication b using (Failure; captured; failures)
 open Snapshot.Frontend b io capability using (DescriptorReferences; resolve)

 record References (w : ConnectionManagement.Domain.WorkerId) (saved : N.Failure) (s : Runtime) : Set where
  field descriptor : DescriptorReferences w (P.U.captured (N.captured saved)) s
        allocation : Chain.AllocationAt (N.captured saved) (sourceOf s)
        published-result : Chain.PublicationAt (N.captured saved) (sourceOf s)

 Validity : Runtime → Set
 Validity s = ∀ w saved → lookup w (N.failures (publication (base s))) ≡ just saved → References w saved s

 from-initial : ∀ c₀ g {start events s} → initialize (O.initial c₀) g ≡ just start → Runs start events s → Validity s
 from-initial c₀ g {s = s} initialized path w saved found = record
   { descriptor = descriptor
   ; allocation = Content.as-chain w (N.captured saved) (sourceOf s) (Failure.negotiated entry)
   ; published-result = Chains.Frontend.result-for-capture b io capability w (N.captured saved) (sourceOf s)
       (proj₁ (proj₁ (proj₂ (proj₂ (proj₂ descriptor))))) (Failure.negotiated entry) }
   where
   covered = FailureFront.Frontend.from-initial b io capability (O.initial c₀) g initialized path
   entry = Failure.at b _ _ (sourceOf s) (Failure.snapshots covered) w saved found
   descriptor = resolve w (P.U.captured (N.captured saved)) s
     (Physical.Frontend.from-initial b io capability c₀ g initialized path) (Failure.descriptor entry)

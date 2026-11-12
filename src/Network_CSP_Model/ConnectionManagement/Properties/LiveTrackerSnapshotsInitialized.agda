{-# OPTIONS --guardedness #-}

-- Snapshot agreement supplies physical resource certificates for the exact
-- descriptors stored in the live mux, exit and startup-fault tables.
module ConnectionManagement.Properties.LiveTrackerSnapshotsInitialized where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (ErrorId; HandleId; WorkerId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
import ConnectionManagement.State as S
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.Properties.HandlerBirthEffects as Birth
import ConnectionManagement.Properties.LiveTrackerReferencesInitialized as Physical
import ConnectionManagement.Properties.LiveTrackerOwnersInitialized as Prior
import ConnectionManagement.Properties.LiveTrackerCaptureExit as Capture
import ConnectionManagement.Properties.LiveTrackerCaptureFrontend as Front

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 open Model.Protocols b io capability using (Runtime; Runs; initialize; base; physical)
 open Physical.Frontend b io capability using (PhysicalReferences; physicalState; shared)
 open Front.Frontend b io capability using (unwind; view; present-thread; initialized-valid; run-preserves)
 private
  module R = Unwind b
  module W = Exit b
  module C = Capture.Unwind b

 -- This identifies the actual physical capture; only its phase may differ.
 DescriptorReferences : WorkerId → S.HandlerStart → Runtime → Set
 DescriptorReferences w h s = Σ H.Thread (λ thread →
   lookup w (B.threads (physicalState s)) ≡ just thread ×
   H.captured thread ≡ h × Facts w h (shared s) ×
   S.handlerPromise h ∈ S.promises (shared s))

 -- A functional capture lookup determines the descriptor of its real thread.
 resolve : ∀ w h s → PhysicalReferences s → Capture.Ref w h (view s) → DescriptorReferences w h s
 resolve w h s valid captured with present-thread w s (h , captured)
 ... | thread , found = thread , found , same ,
   subst (λ descriptor → Facts w descriptor (shared s) × S.handlerPromise descriptor ∈ S.promises (shared s)) same (valid w thread found)
   where
   projected = trans (Birth.lookup-captures w (B.threads (physicalState s))) (cong (Data.Maybe.map H.captured) found)
   same = just-injective (trans (sym projected) captured)

 -- Universal snapshot content, in addition to all previous owner/phase facts.
 record Validity (s : Runtime) : Set where
  field
   prior : Prior.Frontend.Validity b io capability s
   mux : ∀ w f → lookup w (P.U.frames (P.base (physical (base s)))) ≡ just f → DescriptorReferences w (P.U.captured f) s
   exits : ∀ w f → lookup w (W.exits (R.base (unwind s))) ≡ just f → DescriptorReferences w (W.captured f) s
   faults : ∀ w f → lookup w (R.faults (unwind s)) ≡ just f → DescriptorReferences w (R.captured f) s

 -- O.initial is needed only for the resources; exact snapshot agreement itself
 -- follows from every successful broad initializer and its actual execution.
 from-initial : ∀ c₀ g {start events s} →
   initialize (O.initial c₀) g ≡ just start → Runs start events s → Validity s
 from-initial c₀ g {s = s} initialized path = record
   { prior = Prior.Frontend.from-initial b io capability c₀ g initialized path
   ; mux = λ w f found → resolve w (P.U.captured f) s physical-valid
       (Capture.covers-at (C.frames-present {s = unwind s} (proj₁ captures)) w f found)
   ; exits = λ w f found → resolve w (W.captured f) s physical-valid
       (Capture.covers-at (C.exits-present {s = unwind s} (proj₁ captures)) w f found)
   ; faults = λ w f found → resolve w (R.captured f) s physical-valid
       (Capture.covers-at (C.faults-present {s = unwind s} (proj₁ captures)) w f found) }
   where
   physical-valid = Physical.Frontend.from-initial b io capability c₀ g initialized path
   captures = run-preserves path (initialized-valid (O.initial c₀) g initialized)

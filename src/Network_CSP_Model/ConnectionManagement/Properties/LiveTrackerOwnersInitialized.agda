{-# OPTIONS --guardedness #-}

-- Referenced mux/exit/fault owners have actual physical threads and the full
-- physical resource certificate. This does not identify a frame's captured
-- descriptor with that thread, or establish its handle/mux/publication chain.
module ConnectionManagement.Properties.LiveTrackerOwnersInitialized where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
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
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.Properties.LiveTrackerReferencesInitialized as Physical
import ConnectionManagement.Properties.HandlerAuxFrontend as Auxiliary
import ConnectionManagement.Properties.HandlerAuxBacking as Backing
import ConnectionManagement.Properties.FrontendPhaseCleanup as Phase

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 open Model.Protocols b io capability using (Runtime; Runs; initialize; base; physical)
 open Physical.Frontend b io capability public using (PhysicalReferences; physicalState; shared)
 open Auxiliary.Frontend b io capability using (unwind; view; present-thread; initialized-valid; run-preserves)
 private
  module R = Unwind b
  module W = Exit b
  open Backing.Unwind b using (frames-present; exits-present; faults-present)

 -- The certificate concerns the actual physical capture of the named worker.
 OwnerReferences : WorkerId → Runtime → Set
 OwnerReferences w s = Σ H.Thread (λ thread →
   lookup w (B.threads (physicalState s)) ≡ just thread ×
   Facts w (H.captured thread) (shared s) ×
   S.handlerPromise (H.captured thread) ∈ S.promises (shared s))
 -- Turn historical owner backing into the full physical resource certificate.
 owner-resources : ∀ w s → PhysicalReferences s → Backing.Present w (view s) → OwnerReferences w s
 owner-resources w s valid present with present-thread w s present
 ... | thread , found = thread , found , valid w thread found

 -- These three live tables and the acknowledged CM collection refer to real
 -- historical owners. Equality of their separate snapshots is not asserted.
 record Owners (s : Runtime) : Set where
  field
   mux : ∀ w f → lookup w (P.U.frames (P.base (physical (base s)))) ≡ just f → OwnerReferences w s
   exits : ∀ w f → lookup w (W.exits (R.base (unwind s))) ≡ just f → OwnerReferences w s
   faults : ∀ w f → lookup w (R.faults (unwind s)) ≡ just f → OwnerReferences w s
   collected : ∀ w → w ∈ Close.collected (W.shutdown (R.base (unwind s))) → OwnerReferences w s

 -- Retain the existing phase/cleanup guarantee beside the new references.
 record Validity (s : Runtime) : Set where
  field
   physical-references : PhysicalReferences s
   owner-references : Owners s
   phase-cleanup : Phase.Frontend.Valid b io capability s

 -- Initialization and actual execution discharge every certificate internally.
 from-initial : ∀ c₀ g {start events s} →
   initialize (O.initial c₀) g ≡ just start → Runs start events s → Validity s
 from-initial c₀ g {s = s} initialized path = record
   { physical-references = references
   ; owner-references = record
     { mux = λ w f found → owner-resources w s references (frames-present {s = unwind s} (proj₁ backed) w f found)
     ; exits = λ w f found → owner-resources w s references (exits-present {s = unwind s} (proj₁ backed) w f found)
     ; faults = λ w f found → owner-resources w s references (faults-present {s = unwind s} (proj₁ backed) w f found)
     ; collected = λ w member → owner-resources w s references (proj₂ backed member) }
   ; phase-cleanup = Phase.Frontend.from-initial b io capability (O.initial c₀) g initialized path }
   where
   references = Physical.Frontend.from-initial b io capability c₀ g initialized path
   backed = run-preserves path (initialized-valid (O.initial c₀) g initialized)

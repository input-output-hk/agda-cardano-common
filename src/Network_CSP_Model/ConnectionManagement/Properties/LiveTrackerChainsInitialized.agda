{-# OPTIONS --guardedness #-}

-- Universal current-frame allocation and original-promise publication chains.
module ConnectionManagement.Properties.LiveTrackerChainsInitialized where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.Properties.LiveTrackerFrameContent as Content
import ConnectionManagement.Properties.LiveTrackerContentFrontend as Frames
import ConnectionManagement.Properties.LiveTrackerSnapshotsInitialized as Snapshot
import ConnectionManagement.Properties.LiveTrackerChainSteps as Chain

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 open Model.Protocols b io capability using (Runtime; Runs; initialize; base; physical; sourceOf)
 open Snapshot.Frontend b io capability using (DescriptorReferences)

 -- The retained registration of the actual publication writer is identified
 -- with this frame's original descriptor by initialized resource/capture facts.
 result-for-capture : ∀ w f c →
   lookup w (S.handlers (M.world (O.core c))) ≡ just (P.U.captured f) →
   Content.Content w f c → Chain.PublicationAt f c
 result-for-capture w (P.U.frame h origin ps flow P.U.returnedSuccess startup setup) c registered good = tt
 result-for-capture w (P.U.frame h origin ps flow (P.U.handleAllocated hid mid) startup setup) c registered good = tt
 result-for-capture w (P.U.frame h origin ps flow (P.U.promisePublished hid mid) startup setup) c registered good
   with Content.publication good
 ... | actual , found , result = subst
   (λ h′ → lookup (S.handlerPromise h′) (S.handshakeResults (M.world (O.core c))) ≡ just (S.negotiated hid flow))
   (just-injective (trans (sym found) registered)) result

 -- One combined certificate for both remaining mux-frame chains and all
 -- previously established physical/descriptor/phase/cleanup references.
 record Validity (s : Runtime) : Set where
  field
   snapshots : Snapshot.Frontend.Validity b io capability s
   allocation : Chain.AllocationReferences (P.base (physical (base s)))
   publication : Chain.PublicationReferences (P.base (physical (base s)))

 from-initial : ∀ c₀ g {start events s} →
   initialize (O.initial c₀) g ≡ just start → Runs start events s → Validity s
 from-initial c₀ g {s = s} initialized path = record
   { snapshots = snapshots
   ; allocation = λ w f found → Content.as-chain w f (sourceOf s)
       (Content.at _ (sourceOf s) contents w f found)
   ; publication = λ w f found → result-for-capture w f (sourceOf s)
       (proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (Snapshot.Frontend.Validity.mux snapshots w f found))))))
       (Content.at _ (sourceOf s) contents w f found) }
   where
   contents = Frames.Frontend.from-initial b io capability (O.initial c₀) g initialized path
   snapshots = Snapshot.Frontend.from-initial b io capability c₀ g initialized path

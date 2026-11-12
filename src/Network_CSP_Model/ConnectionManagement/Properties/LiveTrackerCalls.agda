{-# OPTIONS --guardedness #-}

-- Saved-call insertion and transport use actual published frame lookups.
-- No owner evidence is obtained from a default frame or an untyped mux lookup.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerCalls
 (b io : ErrorId → Bool) where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; map)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import ConnectionManagement.Domain using (HandleId; WorkerId; MuxId; RunId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; apart-lookup; lookup-head)
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Properties.LiveTrackerAuxBirth as Birth
import ConnectionManagement.Properties.LiveTrackerAuxContent as Content
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
module A = Content b
module K = Model b io
module U = P.U
module Tr = Transport b

module Front (capability : HandleId → ℕ → Bool) where
 open Model.Protocols b io capability using (Call; Runtime; front; calls; physical; base; owner; mux; ownerFor; nextRequest; worker; peer; protocol; enqueue; call; Request; request; descriptor; byThread; thread)
 open Birth.Front b io capability public using (CallOwner; Calls)
 -- Transport preserves the exact saved mux, not merely some published owner.
 rows-kept : ∀ (rows : ConnectionManagement.Store.Store RunId Call) {s t} → Tr.Retains s t →
   All (λ { (rid , saved) → CallOwner saved s }) rows →
   All (λ { (rid , saved) → CallOwner saved t }) rows
 rows-kept rows kept = All.map (λ { {rid , saved} (own , same) →
   let next = Tr.Retains.owners kept (owner saved) own in
   proj₁ next , trans (Tr.OwnerKept.same-mux (proj₂ next)) same })

 -- Traversal selection and lookup agree because initialized frame keys are unique.
 ownerFor-found : ∀ p rows {w} → UniqueKeys rows → ownerFor p rows ≡ just w →
   Σ U.Frame (λ f → lookup w rows ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p))
 ownerFor-found p [] unique ()
 ownerFor-found p ((q , first) ∷ rows) {w} (apart ∷ unique) eq with U.progress first in progress
 ... | U.promisePublished hid mid with Peer.handleRef p ≟ hid | Peer.muxRef p ≟ mid
 ...   | yes refl | yes refl = case just-injective eq of λ { refl → first , lookup-head q first rows , progress }
 ...   | yes _ | no _ = tail-found (ownerFor-found p rows unique eq)
  where
  tail-found : Σ U.Frame (λ f → lookup w rows ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p)) →
    Σ U.Frame (λ f → lookup w ((q , first) ∷ rows) ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p))
  tail-found (f , found , published) with w ≟ q
  ... | yes refl = case trans (sym (apart-lookup q rows apart)) found of λ ()
  ... | no _ = f , found , published
 ...   | no _ | _ = tail-found (ownerFor-found p rows unique eq)
  where
  tail-found : Σ U.Frame (λ f → lookup w rows ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p)) →
    Σ U.Frame (λ f → lookup w ((q , first) ∷ rows) ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p))
  tail-found (f , found , published) with w ≟ q
  ... | yes refl = case trans (sym (apart-lookup q rows apart)) found of λ ()
  ... | no _ = f , found , published
 ownerFor-found p ((q , first) ∷ rows) {w} (apart ∷ unique) eq | U.returnedSuccess = tail-found (ownerFor-found p rows unique eq)
  where
  tail-found : Σ U.Frame (λ f → lookup w rows ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p)) →
    Σ U.Frame (λ f → lookup w ((q , first) ∷ rows) ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p))
  tail-found (f , found , published) with w ≟ q
  ... | yes refl = case trans (sym (apart-lookup q rows apart)) found of λ ()
  ... | no _ = f , found , published
 ownerFor-found p ((q , first) ∷ rows) {w} (apart ∷ unique) eq | U.handleAllocated hid mid = tail-found (ownerFor-found p rows unique eq)
  where
  tail-found : Σ U.Frame (λ f → lookup w rows ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p)) →
    Σ U.Frame (λ f → lookup w ((q , first) ∷ rows) ≡ just f × U.progress f ≡ U.promisePublished (Peer.handleRef p) (Peer.muxRef p))
  tail-found (f , found , published) with w ≟ q
  ... | yes refl = case trans (sym (apart-lookup q rows apart)) found of λ ()
  ... | no _ = f , found , published

 import ConnectionManagement.Subsystem as Sub
 import ConnectionManagement.Rules.PeerJobs as J
 import ConnectionManagement.PeerContext as PeerContext
 import ConnectionManagement.PeerSupervision as Supervision
 import ConnectionManagement.Rules.MuxRuntime as Mux
 open import ConnectionManagement.IGTypes using (number)
 module C = PeerContext io
 module PS = Supervision io
 -- Request creation must have selected this exact current published owner.
 request-owner : ∀ j s {req} → UniqueKeys (U.frames (P.base (physical s))) → nextRequest j s ≡ just req →
   Σ (A.Owner (worker req) (physical s)) (λ own → A.Owner.mux own ≡ Peer.muxRef (peer req))
 request-owner j s unique actual with lookup j (Sub.jobs (PS.machine (K.peers s)))
 ... | nothing = case actual of λ ()
 ... | just jf with J.pc (Sub.execution jf)
 ...   | J.startBundle temp (n ∷ ns) with lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context s)))
 ...     | nothing = case actual of λ ()
 ...     | just p with ownerFor p (U.frames (P.base (physical s))) in found
 ...       | nothing = case actual of λ ()
 ...       | just w with Mux.findProtocol n (Data.List.map Peer.descriptor (Peer.runs p))
 ...         | nothing = case actual of λ ()
 ...         | just proto = case just-injective actual of λ { refl →
   let backing = ownerFor-found p (U.frames (P.base (physical s))) unique found in
   A.owner (proj₁ backing) (Peer.handleRef p) (Peer.muxRef p) (proj₁ (proj₂ backing)) (proj₂ (proj₂ backing)) , refl }
 request-owner j s unique actual | just jf | J.startBundle temp [] = case actual of λ ()
 request-owner j s unique actual | just jf | J.begin = case actual of λ ()
 request-owner j s unique actual | just jf | J.awaitAcquire = case actual of λ ()
 request-owner j s unique actual | just jf | J.publishBundle t = case actual of λ ()
 request-owner j s unique actual | just jf | J.markWarm = case actual of λ ()
 request-owner j s unique actual | just jf | J.forkMonitor = case actual of λ ()
 request-owner j s unique actual | just jf | J.finishActivation = case actual of λ ()
 request-owner j s unique actual | just jf | J.callRelease = case actual of λ ()
 request-owner j s unique actual | just jf | J.awaitRelease = case actual of λ ()
 request-owner j s unique actual | just jf | J.awaitHot = case actual of λ ()
 request-owner j s unique actual | just jf | J.awaitAll = case actual of λ ()
 request-owner j s unique actual | just jf | J.delayFailure = case actual of λ ()
 request-owner j s unique actual | just jf | J.awaitCold result = case actual of λ ()
 request-owner j s unique actual | just jf | J.complete result = case actual of λ ()
 request-owner j s unique actual | just jf | J.acquirePolicy fault = case actual of λ ()
 request-owner j s unique actual | just jf | J.nodeDelivery fault = case actual of λ ()
 request-owner j s unique actual | just jf | J.nodeRethrow fault = case actual of λ ()

 -- Enqueue is the only insertion of a newly saved owner/mux pair.
 enqueue-backed : ∀ j rid req m s → UniqueKeys (U.frames (P.base (physical (base s)))) →
   nextRequest j (base s) ≡ just req → Calls s →
   All (λ { (gen , saved) → CallOwner saved (physical (base s)) }) (calls (enqueue rid req m (front s)))
 enqueue-backed j rid req m s unique actual valid = request-owner j (base s) unique actual ∷ valid

 -- byThread is a traversal selector, so shadowed calls are covered as well.
 byThread-backed : ∀ j rows s {rid r} → byThread j rows ≡ just (rid , r) →
   All (λ { (gen , saved) → CallOwner saved s }) rows → CallOwner r s
 byThread-backed j [] s () valid
 byThread-backed j ((gen , saved) ∷ rows) s actual (good ∷ valid) with thread saved
 ... | nothing = byThread-backed j rows s actual valid
 ... | just k with j ≟ k
 ...   | yes _ = case just-injective actual of λ { refl → good }
 ...   | no _ = byThread-backed j rows s actual valid

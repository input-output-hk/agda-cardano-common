{-# OPTIONS --guardedness #-}

-- Plan-local preservation of NoForeign, alongside the unchanged source Reach.
-- Arbitrary read/caller plans are not certified: the existing selector shapes
-- supply their exact job/followup continuations in OwnedCallersSelection.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallersRuntime
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (HandleId)
open import ConnectionManagement.IGTypes using (number)
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Properties.OwnedCallersBase as Base
import ConnectionManagement.Properties.OwnedCallersExecution as SharedFacts
import ConnectionManagement.Properties.OwnedCallersPeers as PeerFacts
import ConnectionManagement.Properties.OwnedFramesRead as ReadFacts
import ConnectionManagement.Variants.OwnedCallers as Variant
open Base isBearerClosed isIOManagerError using
  (module K; module PS; module GP; module C; NF; job-update)
private
  module Shared = SharedFacts isBearerClosed isIOManagerError
  module Peers = PeerFacts isBearerClosed isIOManagerError
  module Read = ReadFacts isBearerClosed isIOManagerError
  module VariantBase = Variant isBearerClosed isIOManagerError

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  module V = VariantBase.Protocols canInitiate
  private module T = K.Protocols canInitiate

  -- Keep the complete source Reach as the first clause of the runtime invariant.
  Inv : T.Runtime → Set
  Inv s = Shared.Inv (T.base s)

  -- A selected plan is safe for the additional invariant under guarded enact.
  record Safe (s : T.Runtime) (p : T.Plan) : Set where
    constructor safe
    field policy : V.planAllowed p ≡ true
          preserves : ∀ {t} → V.enact′ p s ≡ just t → Inv s → NF (T.base t)

  -- Result caching changes peer rows, keeping source frames and both owner tables.
  cache-nf : ∀ rid r result f b → NF b → NF (T.cacheResult rid r result f b)
  cache-nf rid r result f b held with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
  ... | nothing = held
  ... | just (current , _) with current ≟ rid
  ...   | no _ = held
  ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
  ...     | nothing = held
  ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
  ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
  ...         | nothing = held
  ...         | just rs = held
  cache-nf rid r result f b held | just (current , _) | yes _ | just peer | no _ | _ = held
  cache-nf rid r result f b held | just (current , _) | yes _ | just peer | yes _ | no _ = held

  -- Direct caller and read plans require their selector-specific certificates.
  Simple : T.Plan → Bool
  Simple (T.caller _ _) = false
  Simple (T.reading _) = false
  Simple (T.inherit a f) = V.planAllowed (T.inherit a f)
  Simple (T.complete a rid r result) = V.planAllowed (T.complete a rid r result)
  Simple (T.local _) = true
  Simple (T.traceFault _ _ _ _) = true
  Simple (T.deliverTraceFault _ _ _ _ _) = true
  Simple (T.birth _ _ _ _ _ _ _) = true

  -- Non-read plans either delegate to the guarded shared step or keep observations.
  simple : ∀ p s → Simple p ≡ true → Safe s p
  simple (T.inherit a f) s ok = safe ok λ eq held → inherit eq held
    where
    inherit : ∀ {t} → V.enact′ (T.inherit a f) s ≡ just t → Inv s → NF (T.base t)
    inherit eq held with V.enact-view (T.inherit a f) s eq
    ... | allowed , original with K.step a (T.base s) in stepped
    ...   | nothing = case original of λ ()
    ...   | just b = case just-injective original of λ { refl → proj₂
      (Shared.step-inv a (T.base s) (VariantBase.step-build a (T.base s) allowed stepped) held) }
  simple (T.complete a rid r result) s ok = safe ok λ eq held → complete eq held
    where
    complete : ∀ {t} → V.enact′ (T.complete a rid r result) s ≡ just t → Inv s → NF (T.base t)
    complete eq held with V.enact-view (T.complete a rid r result) s eq
    ... | allowed , original with K.step a (T.base s) in stepped
    ...   | nothing = case original of λ ()
    ...   | just b = case just-injective original of λ { refl → cache-nf rid r result (T.front s) b
      (proj₂ (Shared.step-inv a (T.base s) (VariantBase.step-build a (T.base s) allowed stepped) held)) }
  simple (T.caller a f) s ()
  simple (T.reading r) s ()
  simple (T.local f) s ok = safe refl λ eq held → case just-injective eq of λ { refl → proj₂ held }
  simple (T.traceFault w rid result fs) s ok = safe refl λ eq held → case just-injective eq of λ { refl → proj₂ held }
  simple (T.deliverTraceFault w rid result fs coordinator) s ok = safe refl λ eq held → case just-injective eq of λ { refl → proj₂ held }
  simple (T.birth w captured pool j rid r f) s ok = safe refl λ eq held → case just-injective eq of λ { refl → proj₂ held }

  -- startNext selects the concrete job continuation; it cannot select a raw begin.
  caller : ∀ j f s → Safe s (T.caller (PS.run (GP.run (Sub.jobStep j J.runNext))) f)
  caller j f s = safe refl λ eq held → proof (proj₂ (V.enact-view (T.caller (PS.run (GP.run (Sub.jobStep j J.runNext))) f) s eq)) held
    where
    proof : ∀ {t} → T.enact (T.caller (PS.run (GP.run (Sub.jobStep j J.runNext))) f) s ≡ just t → Inv s → NF (T.base t)
    proof eq held with PS.step (PS.run (GP.run (Sub.jobStep j J.runNext))) (K.peers (T.base s)) in stepped
    ... | nothing = case eq of λ ()
    ... | just p = case just-injective eq of λ { refl → Peers.peer-safe (PS.run (GP.run (Sub.jobStep j J.runNext))) (K.peers (T.base s)) refl stepped
      (proj₁ (proj₁ held)) (proj₂ (proj₂ (proj₁ held))) (proj₂ held) }

  -- Poll-result reads edit only peer diagnostic rows.
  poll-read : ∀ ref peer s → Safe s (T.reading (record (T.readStateOf (T.base s))
    { peerRows = put ref (Peer.cool peer) (T.ReadState.peerRows (T.readStateOf (T.base s))) }))
  poll-read ref peer s = safe refl λ eq held → case just-injective eq of λ { refl → proj₂ held }

  -- The job read replaces an existing row without changing its caller identity.
  job-read : ∀ j jf peer s → lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s)))) ≡ just jf →
    Read.NotAwait (Sub.execution jf) → Safe s (T.reading (record (T.readStateOf (T.base s))
    { peerRows = put (J.connectionRef (Sub.execution jf)) (T.failedPeer (Sub.execution jf) peer) (T.ReadState.peerRows (T.readStateOf (T.base s)))
    ; jobRows = put j (record jf { execution = T.failedFrame (Sub.execution jf) }) (T.ReadState.jobRows (T.readStateOf (T.base s))) }))
  job-read j jf peer s found away = safe refl λ eq held → case just-injective eq of λ { refl →
    job-update (T.sourceOf s) (K.context (T.base s)) j jf (record jf { execution = T.failedFrame (Sub.execution jf) }) found refl (proj₂ held) }

  -- Followup-row reads keep the historical physical monitor table unchanged.
  follow-read : ∀ ref f peer s → lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s)))) ≡ just f →
    Read.NotAwait f → Safe s (T.reading (record (T.readStateOf (T.base s))
    { peerRows = put (J.connectionRef f) (T.failedPeer f peer) (T.ReadState.peerRows (T.readStateOf (T.base s)))
    ; followups = put ref (T.failedFrame f) (T.ReadState.followups (T.readStateOf (T.base s))) }))
  follow-read ref f peer s found away = safe refl λ eq held → case just-injective eq of λ { refl → proj₂ held }

  -- The physical initializer delegates to the same empty-CM shared initializer.
  initial-inv : ∀ c g {s} → T.initialize (O.initial c) g ≡ just s → Inv s
  initial-inv c g eq with K.initial (O.initial c) g in initialized
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → Shared.initial-inv c g initialized }

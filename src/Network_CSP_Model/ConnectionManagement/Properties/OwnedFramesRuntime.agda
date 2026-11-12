{-# OPTIONS --guardedness #-}

-- Component proofs for the physical frontend. Selection-sensitive reads and
-- caller actions are certified separately from arbitrary local plans.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesRuntime
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
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
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesRead as ReadFacts
import ConnectionManagement.Properties.OwnedFramesExecution as ExecutionFacts
import ConnectionManagement.Properties.OwnedFramesJobSteps as JobFacts
import ConnectionManagement.Properties.OwnedFramesJobNames as NamesFacts
import ConnectionManagement.Properties.OwnedFramesFollowStep as FollowFacts
open Frames isBearerClosed isIOManagerError using (module K; module PS; module GP; module C)
private
  module Read = ReadFacts isBearerClosed isIOManagerError
  module Execution = ExecutionFacts isBearerClosed isIOManagerError
  module Jobs = JobFacts isBearerClosed isIOManagerError
  module Names = NamesFacts isBearerClosed isIOManagerError
  module Follow = FollowFacts isBearerClosed isIOManagerError
  module N = Publication isBearerClosed

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  private module T = K.Protocols canInitiate

  -- The strengthened K invariant is retained, without a new runtime premise.
  Inv : T.Runtime → Set
  Inv s = Execution.Reach (T.base s)

  -- A certified plan preserves the full invariant whenever enact succeeds.
  record Safe (s : T.Runtime) (p : T.Plan) : Set where
    constructor safe
    field preserves : ∀ {t} → T.enact p s ≡ just t → Inv s → Inv t

  -- Peer-result caching changes none of the six ownership observations.
  peer-rows : ∀ c k rows → Read.Held c k → Read.Held c
    (record k { subsystem = record (C.subsystem k) { peers = rows } })
  peer-rows c k rows = Read.copy-held c k _ refl

  -- The cache write has no source, caller, pool-handle, or thread effect.
  cache-reach : ∀ rid r result f b → Execution.Reach b → Execution.Reach (T.cacheResult rid r result f b)
  cache-reach rid r result f b held with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
  ... | nothing = held
  ... | just (current , _) with current ≟ rid
  ...   | no _ = held
  ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
  ...     | nothing = held
  ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
  ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
  ...         | nothing = held
  ...         | just rs = peer-rows (K.source b) (K.context b) _ held
  cache-reach rid r result f b held | just (current , _) | yes _ | just peer | no _ | _ = held
  cache-reach rid r result f b held | just (current , _) | yes _ | just peer | yes _ | no _ = held

  -- Reads and direct callers need their selector's more precise certificate.
  Simple : T.Plan → Bool
  Simple (T.caller _ _) = false
  Simple (T.reading _) = false
  Simple (T.inherit _ _) = true
  Simple (T.local _) = true
  Simple (T.birth _ _ _ _ _ _ _) = true
  Simple (T.complete _ _ _ _) = true
  Simple (T.traceFault _ _ _ _) = true
  Simple (T.deliverTraceFault _ _ _ _ _) = true

  -- Physical births edit mux metadata only; fault writes edit the enclosing
  -- fault/coordinator metadata only. Neither edits the source or peer context.
  simple : ∀ p s → Simple p ≡ true → Safe s p
  simple (T.inherit a f) s ok = safe λ eq held → inherit eq held
    where
    inherit : ∀ {t} → T.enact (T.inherit a f) s ≡ just t → Inv s → Inv t
    inherit eq held with K.step a (T.base s) in stepped
    ... | nothing = case eq of λ ()
    ... | just b = case just-injective eq of λ { refl → Execution.step-reach a (T.base s) stepped held }
  simple (T.caller a f) s ()
  simple (T.reading r) s ()
  simple (T.local f) s ok = safe λ eq held → case just-injective eq of λ { refl → held }
  simple (T.traceFault w rid result fs) s ok = safe λ eq held → case just-injective eq of λ { refl → held }
  simple (T.deliverTraceFault w rid result fs coordinator) s ok = safe λ eq held → case just-injective eq of λ { refl → held }
  simple (T.birth w captured pool j rid r f) s ok = safe λ eq held → case just-injective eq of λ { refl → held }
  simple (T.complete a rid r result) s ok = safe λ eq held → complete eq held
    where
    complete : ∀ {t} → T.enact (T.complete a rid r result) s ≡ just t → Inv s → Inv t
    complete eq held with K.step a (T.base s) in stepped
    ... | nothing = case eq of λ ()
    ... | just b = case just-injective eq of λ { refl → cache-reach rid r result (T.front s) b
      (Execution.step-reach a (T.base s) stepped held) }

  -- The frontend caller bypasses K's empty-bundle guard, but is exactly a
  -- real PS jobStep runNext; its existing component proof has no such guard.
  caller : ∀ j f s → Safe s (T.caller (PS.run (GP.run (Sub.jobStep j J.runNext))) f)
  caller j f s = safe proof
    where
    proof : ∀ {t} → T.enact (T.caller (PS.run (GP.run (Sub.jobStep j J.runNext))) f) s ≡ just t → Inv s → Inv t
    proof eq held with PS.step (PS.run (GP.run (Sub.jobStep j J.runNext))) (K.peers (T.base s)) in stepped
    ... | nothing = case eq of λ ()
    ... | just p = case just-injective eq of λ { refl → Jobs.job-step j J.runNext (K.peers (T.base s)) stepped held }

  -- Polling a failed physical result changes only a peer's status.
  poll-read : ∀ ref peer s → Safe s (T.reading (record (T.readStateOf (T.base s))
    { peerRows = put ref (Peer.cool peer) (T.ReadState.peerRows (T.readStateOf (T.base s))) }))
  poll-read ref peer s = safe λ eq held → case just-injective eq of λ { refl →
    peer-rows (T.sourceOf s) (K.context (T.base s)) _ held }

  -- Failed job reads preserve callers and edit only a non-CM-wait continuation.
  job-read : ∀ j jf peer s → lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s)))) ≡ just jf →
    Read.NotAwait (Sub.execution jf) → Safe s (T.reading (record (T.readStateOf (T.base s))
    { peerRows = put (J.connectionRef (Sub.execution jf)) (T.failedPeer (Sub.execution jf) peer) (T.ReadState.peerRows (T.readStateOf (T.base s)))
    ; jobRows = put j (record jf { execution = T.failedFrame (Sub.execution jf) }) (T.ReadState.jobRows (T.readStateOf (T.base s))) }))
  job-read j jf peer s found away = safe λ eq held → case just-injective eq of λ { refl →
    peer-rows (T.sourceOf s) (Names.job-context (K.context (T.base s)) _) _
      (Read.job-read (T.sourceOf s) (K.context (T.base s)) j jf
        (record jf { execution = T.failedFrame (Sub.execution jf) }) found away refl held) }

  -- Monitor reads keep the existing physical observing-thread witness.
  follow-read : ∀ ref f peer s → lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s)))) ≡ just f →
    Read.NotAwait f → Safe s (T.reading (record (T.readStateOf (T.base s))
    { peerRows = put (J.connectionRef f) (T.failedPeer f peer) (T.ReadState.peerRows (T.readStateOf (T.base s)))
    ; followups = put ref (T.failedFrame f) (T.ReadState.followups (T.readStateOf (T.base s))) }))
  follow-read ref f peer s found away = safe λ eq held → case just-injective eq of λ { refl →
    peer-rows (T.sourceOf s) (Follow.follow-context (K.context (T.base s)) ref (T.failedFrame f)) _
      (Read.follow-read (T.sourceOf s) (K.context (T.base s)) ref f (T.failedFrame f) found away refl held) }

  -- The runtime initialization delegates to the accepted empty-table K state.
  initial-inv : ∀ c g {s} → T.initialize (O.initial c) g ≡ just s → Inv s
  initial-inv c g eq with K.initial (O.initial c) g in initialized
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → Execution.initial-reach c g initialized }

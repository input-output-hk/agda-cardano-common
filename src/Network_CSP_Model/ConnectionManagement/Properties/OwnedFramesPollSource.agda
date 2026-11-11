{-# OPTIONS --guardedness #-}

-- Exact raw poll effects: a peer-world-only write or one fresh logical followup.
module ConnectionManagement.Properties.OwnedFramesPollSource where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (PeerConnectionId; WorkerId; remote; ident)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.IGTypes using (clean; errored)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Machine as Inbound

-- The fresh row retains its actual caller and source absence guard.
data Change (ref : PeerConnectionId) (caller : WorkerId) (before after : Store PeerConnectionId J.Frame) : Set where
  unchanged : after ≡ before → Change ref caller before after
  started : ∀ f → lookup ref before ≡ nothing → J.caller f ≡ caller → after ≡ put ref f before → Change ref caller before after

-- Source CM and logical job rows remain exactly the same in every raw poll.
record Effect (ref : PeerConnectionId) (caller : WorkerId) (c d : Sub.Configuration) : Set where
  field
    source : J.cm (Sub.world d) ≡ J.cm (Sub.world c)
    jobs : Sub.jobs d ≡ Sub.jobs c
    follows : Change ref caller (Sub.monitors c) (Sub.monitors d)

-- This tree mirrors all successful and unavailable pollPeer cases.
poll-effect : ∀ ref caller c {d} → Sub.advance (Sub.pollPeer ref caller) c ≡ just d → Effect ref caller c d
poll-effect ref caller c eq with lookup ref (J.peers (Sub.world c)) | lookup ref (Sub.monitors c) in empty
... | just peer | nothing with P.monitorStarted peer | P.status peer
...   | true | P.peerCooling with P.step P.monitorCooling peer
  (Inbound.inboundGovernor (CM.core (J.cm (Sub.world c)))) (Inbound.world (CM.core (J.cm (Sub.world c))))
...     | nothing = case eq of λ ()
...     | just (next , ig) = case just-injective eq of λ { refl → record { source = refl; jobs = refl; follows = unchanged refl } }
poll-effect ref caller c eq | just peer | nothing | true | P.peerCold = case just-injective eq of λ { refl → record { source = refl; jobs = refl; follows = unchanged refl } }
poll-effect ref caller c eq | just peer | nothing | true | P.peerWarm with Sub.firstResult peer
... | nothing = case eq of λ ()
... | just (kind , errored err) = case just-injective eq of λ { refl → record { source = refl; jobs = refl; follows = unchanged refl } }
... | just (kind , clean) with Sub.workerFree caller c
...   | false = case eq of λ ()
...   | true = case just-injective eq of λ { refl → record
  { source = refl; jobs = refl; follows = started (J.frame (G.job kind (remote (P.key peer)) (just ref)) caller caller (ident 0) ref J.begin) empty refl refl } }
poll-effect ref caller c eq | just peer | nothing | true | P.peerHot with Sub.firstResult peer
... | nothing = case eq of λ ()
... | just (kind , errored err) = case just-injective eq of λ { refl → record { source = refl; jobs = refl; follows = unchanged refl } }
... | just (kind , clean) with Sub.workerFree caller c
...   | false = case eq of λ ()
...   | true = case just-injective eq of λ { refl → record
  { source = refl; jobs = refl; follows = started (J.frame (G.job kind (remote (P.key peer)) (just ref)) caller caller (ident 0) ref J.begin) empty refl refl } }
poll-effect ref caller c eq | just peer | nothing | false | status = case eq of λ ()
poll-effect ref caller c eq | just peer | just f with J.pc f
... | J.awaitCold result with P.step P.monitorCooling peer
  (Inbound.inboundGovernor (CM.core (J.cm (Sub.world c)))) (Inbound.world (CM.core (J.cm (Sub.world c))))
...   | nothing = case eq of λ ()
...   | just (next , ig) = case just-injective eq of λ { refl → record { source = refl; jobs = refl; follows = unchanged refl } }
poll-effect ref caller c eq | just peer | just f | J.begin = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.awaitAcquire = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | (J.startBundle t ns) = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | (J.publishBundle t) = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.markWarm = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.forkMonitor = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.finishActivation = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.awaitHot = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.awaitAll = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.callRelease = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.awaitRelease = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | J.delayFailure = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | (J.complete result) = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | (J.acquirePolicy fault) = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | (J.nodeDelivery fault) = case eq of λ ()
poll-effect ref caller c eq | just peer | just f | (J.nodeRethrow fault) = case eq of λ ()
poll-effect ref caller c eq | nothing | follow = case eq of λ ()

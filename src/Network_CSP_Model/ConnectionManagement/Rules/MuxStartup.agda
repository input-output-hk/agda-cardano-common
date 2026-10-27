{-# OPTIONS --guardedness #-}

-- Successful-handshake startup prerequisite at the fixed network pin:
-- ConnectionHandler.hs:377-380,449-452; Mux.hs:248-270; JobPool.hs:122-145.
-- Publication is an observed boundary input here, not a coupled handler proof.
-- Ready mux status is neither physical startup nor a pool-join certificate.
module ConnectionManagement.Rules.MuxStartup (Result : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain
import ConnectionManagement.Rules.JobPoolKernel as Kernel
module Pool = Kernel Result true

data PC : Set where
  awaitPublication published bufferReady bearerReady runEntered startingTraced
    egressReady poolReady : PC
  muxerForked muxerRegistered : JobId → PC
  demuxerForked demuxerRegistered matureTraced monitoring : JobId → JobId → PC

record State : Set where
  constructor startupState
  field phase : PC
        pool : Pool.State
open State public

-- No physical thread or pool snapshot is adopted by the initializer.
initial : State
initial = startupState awaitPublication Pool.initial

-- Child completion may outrun the masked parent's insertion. Deregistration
-- still waits for that insertion through the actual JobPool registry guard.
data ChildAction : Set where
  bodyReturned : JobId → Result → ChildAction
  publishCompletion deregister publishAsyncResult : JobId → ChildAction
poolAction : ChildAction → Pool.Action
poolAction (bodyReturned j result) = Pool.bodyReturnedWith j result
poolAction (publishCompletion j) = Pool.publishCompletion j
poolAction (deregister j) = Pool.deregister j
poolAction (publishAsyncResult j) = Pool.publishAsyncResult j

data Action : Set where
  observePublication allocateBuffer createBearer enterRun traceStarting
    allocateEgress openPool registerMuxer registerDemuxer traceMature enterMonitor : Action
  forkMuxer forkDemuxer : JobId → Action
  child : ChildAction → Action

-- Pool transitions are real existing fork/register/child transitions. Metadata
-- boundaries remain separate, so another actor can run between all these steps.
via : PC → Pool.Action → State → Maybe State
via pc action s with Pool.step action (pool s)
... | nothing = nothing
... | just next = just (startupState pc next)

step : Action → State → Maybe State
step observePublication s with phase s
... | awaitPublication = just (record s { phase = published })
... | _ = nothing
step allocateBuffer s with phase s
... | published = just (record s { phase = bufferReady })
... | _ = nothing
step createBearer s with phase s
... | bufferReady = just (record s { phase = bearerReady })
... | _ = nothing
step enterRun s with phase s
... | bearerReady = just (record s { phase = runEntered })
... | _ = nothing
step traceStarting s with phase s
... | runEntered = just (record s { phase = startingTraced })
... | _ = nothing
step allocateEgress s with phase s
... | startingTraced = just (record s { phase = egressReady })
... | _ = nothing
step openPool s with phase s
... | egressReady = just (record s { phase = poolReady })
... | _ = nothing
step (forkMuxer j) s with phase s
... | poolReady = via (muxerForked j) (Pool.fork j) s
... | _ = nothing
step registerMuxer s with phase s
... | muxerForked j = via (muxerRegistered j) Pool.register s
... | _ = nothing
step (forkDemuxer j) s with phase s
... | muxerRegistered muxer = via (demuxerForked muxer j) (Pool.fork j) s
... | _ = nothing
step registerDemuxer s with phase s
... | demuxerForked muxer demuxer = via (demuxerRegistered muxer demuxer) Pool.register s
... | _ = nothing
step traceMature s with phase s
... | demuxerRegistered muxer demuxer = just (record s { phase = matureTraced muxer demuxer })
... | _ = nothing
step enterMonitor s with phase s
... | matureTraced muxer demuxer = just (record s { phase = monitoring muxer demuxer })
... | _ = nothing
step (child action) s = via (phase s) (poolAction action) s

-- The startup interface exposes no close/join action. The same queued pool is
-- retained for subsequent mini-protocol actors and eventual verified shutdown.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

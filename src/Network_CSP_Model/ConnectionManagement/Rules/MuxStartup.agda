{-# OPTIONS --guardedness #-}

-- Successful-handshake startup prerequisite; configured draft targets network
-- 2f1c154f248659b89523d5679ca532f442e7ed2a, Mux.hs:408-434,442-483;
-- unchanged JobPool.hs:122-145. Legacy plain constructor/action API is retained.
-- Publication is an observed boundary input here, not a coupled handler proof.
-- Ready mux status is neither physical startup nor a pool-join certificate.
module ConnectionManagement.Rules.MuxStartup (Result : Set) where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; drop; map)
open import Data.Product using (_,_; proj₂)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxEgress as E
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain
import ConnectionManagement.Rules.JobPoolKernel as Kernel
module Pool = Kernel Result true

-- This additive continuation shares State.pool with all existing actors.
-- The immutable layout determines the only role order; a caller supplies no role.
data ConfiguredStage : Set where
  cfgBeforePool cfgReady cfgMature cfgMonitoring : ConfiguredStage
  cfgRegistering : Types.Role → JobId → ConfiguredStage
record ConfiguredFrame : Set where
  constructor configuredFrame
  field layout : E.Layout
        cursor : ℕ
        bindings : Store Types.Role JobId
        stage : ConfiguredStage
open ConfiguredFrame public

data PC : Set where
  awaitPublication published bufferReady bearerReady runEntered startingTraced
    egressReady poolReady : PC
  muxerForked muxerRegistered : JobId → PC
  demuxerForked demuxerRegistered matureTraced monitoring : JobId → JobId → PC
  configured : ConfiguredFrame → PC

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
  configureStartup : E.Layout → Action
  forkConfigured : JobId → Action
  registerConfigured traceConfiguredMature enterConfiguredMonitor : Action

-- Pool transitions are real existing fork/register/child transitions. Metadata
-- boundaries remain separate, so another actor can run between all these steps.
via : PC → Pool.Action → State → Maybe State
via pc action s with Pool.step action (pool s)
... | nothing = nothing
... | just next = just (startupState pc next)

-- Expose actual historical births, including the parent insertion gap.
infraBindings : PC → Store Types.Role JobId
infraBindings (muxerForked m) = (Types.muxer , m) ∷ []
infraBindings (muxerRegistered m) = (Types.muxer , m) ∷ []
infraBindings (demuxerForked m d) = (Types.muxer , m) ∷ (Types.demuxer , d) ∷ []
infraBindings (demuxerRegistered m d) = (Types.muxer , m) ∷ (Types.demuxer , d) ∷ []
infraBindings (matureTraced m d) = (Types.muxer , m) ∷ (Types.demuxer , d) ∷ []
infraBindings (monitoring m d) = (Types.muxer , m) ∷ (Types.demuxer , d) ∷ []
infraBindings (configured f) = bindings f
infraBindings _ = []
roleId : Types.Role → PC → Maybe JobId
roleId role pc = lookup role (infraBindings pc)
infraIds : PC → List JobId
infraIds pc = map proj₂ (infraBindings pc)
monitoringPC : PC → Bool
monitoringPC (monitoring _ _) = true
monitoringPC (configured f) with stage f
... | cfgMonitoring = true
... | _ = false
monitoringPC _ = false

-- Fork is real Pool.fork, and the binding is retained BEFORE registration.
configuredFork : JobId → ConfiguredFrame → State → Maybe State
configuredFork j f s with stage f | drop (cursor f) (Types.infraPlan (layout f))
... | cfgReady | role ∷ rest with lookup role (bindings f) | Pool.step (Pool.fork j) (pool s)
...   | nothing | just next = just (startupState (configured (record f
  { cursor = suc (cursor f); bindings = put role j (bindings f); stage = cfgRegistering role j })) next)
...   | _ | _ = nothing
configuredFork j f s | _ | _ = nothing

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
... | configured f with stage f
...   | cfgBeforePool = just (record s { phase = configured (record f { stage = cfgReady }) })
...   | _ = nothing
step openPool s | _ = nothing
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
step (configureStartup plan) s with phase s
... | egressReady = just (record s { phase = configured (configuredFrame plan 0 [] cfgBeforePool) })
... | _ = nothing
step (forkConfigured j) s with phase s
... | configured f = configuredFork j f s
... | _ = nothing
step registerConfigured s with phase s
... | configured f with stage f
...   | cfgRegistering role j = via (configured (record f { stage = cfgReady })) Pool.register s
...   | _ = nothing
step registerConfigured s | _ = nothing
step traceConfiguredMature s with phase s
... | configured f with stage f | drop (cursor f) (Types.infraPlan (layout f))
...   | cfgReady | [] = just (record s { phase = configured (record f { stage = cfgMature }) })
...   | _ | _ = nothing
step traceConfiguredMature s | _ = nothing
step enterConfiguredMonitor s with phase s
... | configured f with stage f
...   | cfgMature = just (record s { phase = configured (record f { stage = cfgMonitoring }) })
...   | _ = nothing
step enterConfiguredMonitor s | _ = nothing

-- The startup interface exposes no close/join action. The same queued pool is
-- retained for subsequent mini-protocol actors and eventual verified shutdown.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

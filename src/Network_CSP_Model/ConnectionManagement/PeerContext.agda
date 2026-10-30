{-# OPTIONS --guardedness #-}

-- A CM-free peer-supervision context. Reassembly supplies the one current CM
-- configuration; no saved peer-side copy can overwrite intervening Server work.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.PeerContext (isIOManagerError : ErrorId → Bool) where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.AsyncScope as Scope
private
  module PS = Supervision isIOManagerError
  module GP = PS.GP

-- These are precisely the subsystem fields other than World.cm.
record SubContext : Set where
  field
    peers : Peer.Runtime
    privateState publicState : G.State
    pc : Sub.PC
    now : ℕ
    targetInput : G.Targets
    jobs : Store JobId Sub.JobFrame
    pool : List JobId
    completions : List G.Completion
    monitors : Store PeerConnectionId J.Frame
    nextJob nextPeer maxRetries clearFailDelay : ℕ
    wakeupAt : Maybe ℕ
    wakeupReady : Bool

-- Physical pools, detached calls and the policy/scopes retain exact identities.
record Context : Set where
  field
    subsystem : SubContext
    policyStage : Policy.Stage
    governorPool : GP.Pool.State
    regions : Store WorkerId Cancel.Context
    unwinding : Store JobId Cancel.Frame
    monitors : Store JobId PS.Thread
    monitorPool : PS.Pool.State
    scopes : Scope.State
open Context public

captureSub : Sub.Configuration → SubContext
captureSub s = record
  { peers = J.peers (Sub.world s)
  ; privateState = Sub.privateState s; publicState = Sub.publicState s
  ; pc = Sub.pc s; now = Sub.now s; targetInput = Sub.targetInput s
  ; jobs = Sub.jobs s; pool = Sub.pool s; completions = Sub.completions s
  ; monitors = Sub.monitors s; nextJob = Sub.nextJob s; nextPeer = Sub.nextPeer s
  ; maxRetries = Sub.maxRetries s; clearFailDelay = Sub.clearFailDelay s
  ; wakeupAt = Sub.wakeupAt s; wakeupReady = Sub.wakeupReady s }
assembleSub : O.Configuration → SubContext → Sub.Configuration
assembleSub c k = record
  { world = J.world c (SubContext.peers k)
  ; privateState = SubContext.privateState k; publicState = SubContext.publicState k
  ; pc = SubContext.pc k; now = SubContext.now k; targetInput = SubContext.targetInput k
  ; jobs = SubContext.jobs k; pool = SubContext.pool k; completions = SubContext.completions k
  ; monitors = SubContext.monitors k; nextJob = SubContext.nextJob k; nextPeer = SubContext.nextPeer k
  ; maxRetries = SubContext.maxRetries k; clearFailDelay = SubContext.clearFailDelay k
  ; wakeupAt = SubContext.wakeupAt k; wakeupReady = SubContext.wakeupReady k }
capture : PS.State → Context
capture s = record
  { subsystem = captureSub (PS.machine s)
  ; policyStage = Policy.stage (GP.source (PS.governor s))
  ; governorPool = GP.pool (PS.governor s); regions = GP.regions (PS.governor s)
  ; unwinding = GP.unwinding (PS.governor s); monitors = PS.monitors s
  ; monitorPool = PS.monitorPool s; scopes = PS.scopes s }
assemble : O.Configuration → Context → PS.State
assemble c k = PS.supervising
  (GP.supervised (Policy.observed (assembleSub c (subsystem k)) (policyStage k))
    (governorPool k) (regions k) (unwinding k))
  (monitors k) (monitorPool k) (scopes k)

-- Lens laws hold for arbitrary contexts, without a synchronization invariant.
source-exact : ∀ c k → PS.cm (assemble c k) ≡ c
source-exact c k = refl
context-roundtrip : ∀ c k → capture (assemble c k) ≡ k
context-roundtrip c k = refl
state-roundtrip : ∀ s → assemble (PS.cm s) (capture s) ≡ s
state-roundtrip s = refl
rebase : ∀ c s → assemble c (capture s) ≡ record s { governor = GP.setCM c (PS.governor s) }
rebase c s = refl

{-# OPTIONS --guardedness #-}

-- SI5: complete shutdown of the outermost composition (pool relays around the
-- Server/peer runtime). Every initialized run that reaches the finished relays
-- state has a returned Server, a closed peer side with all snapshot jobs and
-- scopes terminal or joined, and, on a node that forked relays, joined relays.
-- This is a finite-trace safety certificate; it asserts no eventuality.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerShutdownComplete
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (HandleId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.IGTypes using (number)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerPeersRelays as Relays
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Rules.JobPoolKernel as Kernel
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Properties.PeerSupervision as PeerFacts
import ConnectionManagement.Properties.ServerPeers as SharedFacts
import ConnectionManagement.Properties.ServerStageEntry as Entry
import ConnectionManagement.Properties.PoolRelays as RelaysFacts
private
  module K = Combined isBearerClosed isIOManagerError
  module S = Server isBearerClosed
  module E = Exit isBearerClosed
  module N = Publication isBearerClosed
  module PS = Supervision isIOManagerError
  module C = Context isIOManagerError
  module P = PeerFacts isIOManagerError
  module Facts = SharedFacts isBearerClosed isIOManagerError
  module Stage = Entry isBearerClosed
  module SR = Relays isBearerClosed isIOManagerError

-- A closed job pool stays closed: every phase writer needs an earlier phase.
module ClosedPool (Result : Set) (queued : Bool) where
  module Pool = Kernel Result queued
  concurrent-fork : ∀ b k c {c′} → Pool.phase c ≡ Pool.closedPool → Pool.concurrentFork b k c ≡ just c′ →
    Pool.phase c′ ≡ Pool.closedPool
  concurrent-fork true k c closed ()
  concurrent-fork false k c closed eq rewrite closed = case eq of λ ()
  concurrent-register : ∀ b k c {c′} → Pool.phase c ≡ Pool.closedPool → Pool.concurrentRegister b k c ≡ just c′ →
    Pool.phase c′ ≡ Pool.closedPool
  concurrent-register true k c closed ()
  concurrent-register false k c closed eq rewrite closed = case eq of λ ()
  publish : ∀ b k c {c′} → Pool.phase c ≡ Pool.closedPool → Pool.publishQueued b k c ≡ just c′ →
    Pool.phase c′ ≡ Pool.closedPool
  publish false k c closed ()
  publish true k c closed eq with lookup k (Pool.handles c)
  ... | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → closed }
  ... | nothing = case eq of λ ()
  ... | just Pool.bodyRunning = case eq of λ ()
  ... | just Pool.bodyUnwinding = case eq of λ ()
  ... | just (Pool.deregisterPending ex) = case eq of λ ()
  ... | just (Pool.deregistered ex) = case eq of λ ()
  ... | just (Pool.resultAvailable ex) = case eq of λ ()
  consume : ∀ b c {c′} → Pool.phase c ≡ Pool.closedPool → Pool.consumeQueued b c ≡ just c′ →
    Pool.phase c′ ≡ Pool.closedPool
  consume false c closed ()
  consume true c closed eq rewrite closed = case eq of λ ()
  stays : ∀ a c {c′} → Pool.phase c ≡ Pool.closedPool → Pool.step a c ≡ just c′ → Pool.phase c′ ≡ Pool.closedPool
  stays (Pool.fork k) c closed eq rewrite closed = case eq of λ ()
  stays Pool.register c closed eq rewrite closed = case eq of λ ()
  stays (Pool.forkConcurrent k) c closed eq = concurrent-fork queued k c closed eq
  stays (Pool.registerConcurrent k) c closed eq = concurrent-register queued k c closed eq
  stays (Pool.bodyReturnedWith k result) c closed eq with lookup k (Pool.handles c)
  ... | just Pool.bodyRunning = case just-injective eq of λ { refl → closed }
  ... | nothing = case eq of λ ()
  ... | just (Pool.bodyReturned value) = case eq of λ ()
  ... | just Pool.bodyUnwinding = case eq of λ ()
  ... | just (Pool.deregisterPending ex) = case eq of λ ()
  ... | just (Pool.deregistered ex) = case eq of λ ()
  ... | just (Pool.resultAvailable ex) = case eq of λ ()
  stays (Pool.publishCompletion k) c closed eq = publish queued k c closed eq
  stays Pool.consumeCompletion c closed eq = consume queued c closed eq
  stays (Pool.interruptJob k) c closed eq rewrite closed = case eq of λ ()
  stays (Pool.bodyUnwound k) c closed eq with lookup k (Pool.handles c)
  ... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → closed }
  ... | nothing = case eq of λ ()
  ... | just Pool.bodyRunning = case eq of λ ()
  ... | just (Pool.bodyReturned value) = case eq of λ ()
  ... | just (Pool.deregisterPending ex) = case eq of λ ()
  ... | just (Pool.deregistered ex) = case eq of λ ()
  ... | just (Pool.resultAvailable ex) = case eq of λ ()
  stays (Pool.resumeAfterUnwindError k) c closed eq with lookup k (Pool.handles c)
  ... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → closed }
  ... | nothing = case eq of λ ()
  ... | just Pool.bodyRunning = case eq of λ ()
  ... | just (Pool.bodyReturned value) = case eq of λ ()
  ... | just (Pool.deregisterPending ex) = case eq of λ ()
  ... | just (Pool.deregistered ex) = case eq of λ ()
  ... | just (Pool.resultAvailable ex) = case eq of λ ()
  stays (Pool.deregister k) c closed eq with lookup k (Pool.handles c) | Pool.member k (Pool.registered c)
  ... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl → closed }
  ... | nothing | _ = case eq of λ ()
  ... | just (Pool.deregisterPending exit) | false = case eq of λ ()
  ... | just Pool.bodyRunning | _ = case eq of λ ()
  ... | just (Pool.bodyReturned value) | _ = case eq of λ ()
  ... | just Pool.bodyUnwinding | _ = case eq of λ ()
  ... | just (Pool.deregistered ex) | _ = case eq of λ ()
  ... | just (Pool.resultAvailable ex) | _ = case eq of λ ()
  stays (Pool.publishAsyncResult k) c closed eq with lookup k (Pool.handles c)
  ... | just (Pool.deregistered exit) = case just-injective eq of λ { refl → closed }
  ... | nothing = case eq of λ ()
  ... | just Pool.bodyRunning = case eq of λ ()
  ... | just (Pool.bodyReturned value) = case eq of λ ()
  ... | just Pool.bodyUnwinding = case eq of λ ()
  ... | just (Pool.deregisterPending ex) = case eq of λ ()
  ... | just (Pool.resultAvailable ex) = case eq of λ ()
  stays (Pool.beginClose order) c closed eq rewrite closed = case eq of λ ()
  stays Pool.requestCancel c closed eq rewrite closed = case eq of λ ()
  stays Pool.deliverCancel c closed eq rewrite closed = case eq of λ ()
  stays Pool.join c closed eq rewrite closed = case eq of λ ()
  stays Pool.finishClose c closed eq rewrite closed = case eq of λ ()
  exec-stays : ∀ {c as c′} → Pool.Executes c as c′ → Pool.phase c ≡ Pool.closedPool → Pool.phase c′ ≡ Pool.closedPool
  exec-stays Pool.done closed = closed
  exec-stays (Pool.next {s = c} {a = a} eq rest) closed = exec-stays rest (stays a c closed eq)

private
  module GAbsorb = ClosedPool PS.GP.Body true
  module BAbsorb = ClosedPool (Maybe ErrorId) false

-- A finished scope coordinator admits no step.
scope-none : ∀ gate a s {s′} → Scope.cursor s ≡ Scope.finishedScope → Scope.step gate a s ≡ just s′ → ⊥
scope-none gate a s closed eq rewrite closed = case eq of λ ()
scope-stays : ∀ {s as s′} → Scope.Executes s as s′ → Scope.cursor s ≡ Scope.finishedScope →
  Scope.cursor s′ ≡ Scope.finishedScope
scope-stays Scope.done closed = closed
scope-stays (Scope.next eq rest) closed = ⊥-elim (scope-none _ _ _ closed eq)

-- Peer closure is absorbing along the projected pool and scope traces.
reclose : ∀ t → PS.GP.Pool.phase (C.governorPool (K.context t)) ≡ PS.GP.Pool.closedPool →
  PS.Pool.phase (C.monitorPool (K.context t)) ≡ PS.Pool.closedPool →
  Scope.cursor (C.scopes (K.context t)) ≡ Scope.finishedScope → K.peerClosed t ≡ true
reclose t gov bg scopes rewrite gov | bg | scopes = refl
closed-paths : ∀ s t → P.Paths (Facts.view s) (Facts.view t) → K.peerClosed s ≡ true → K.peerClosed t ≡ true
closed-paths s t (P.paths (_ , gp) (_ , bp) (_ , sp)) closed with Facts.closure-observation s closed
... | gov , bg , scopes = reclose t (GAbsorb.exec-stays gp gov) (BAbsorb.exec-stays bp bg) (scope-stays sp scopes)

-- Server stage of the shared state.
stageK : K.State → S.Stage
stageK s = S.stage (E.base (K.server s))

core-not-scope : ∀ a x → K.coreAction a ≢ E.run (S.scope x)
core-not-scope (O.beginAcquire _ _) x ()
core-not-scope (O.acquire _ _) x ()
core-not-scope (O.beginRelease _ _) x ()
core-not-scope (O.release _ _) x ()
core-not-scope (O.inbound _) x ()

-- Only a Server scope action changes the shared Server stage.
shared-stage : ∀ a s {t} → K.step a s ≡ just t →
  stageK t ≡ stageK s ⊎ Σ S.ScopeAction (λ x → a ≡ K.serverStep (E.run (S.scope x)))
shared-stage (K.serverStep a) s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s) in actual
...   | nothing = case eq of λ ()
...   | just e with Stage.ig-step-stage a (K.server s) actual
...     | inj₁ same = case just-injective eq of λ { refl → inj₁ same }
...     | inj₂ (x , refl) = inj₂ (x , refl)
shared-stage (K.peerStep a) s eq with K.peerOpen s ∧ K.peerAllowed a s
... | false = case eq of λ ()
... | true with PS.step a (K.peers s)
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → inj₁ refl }
shared-stage (K.coreStep a) s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s) in actual
...   | nothing = case eq of λ ()
...   | just e with Stage.ig-step-stage (K.coreAction a) (K.server s) actual
...     | inj₁ same = case just-injective eq of λ { refl → inj₁ same }
...     | inj₂ (x , scoped) = ⊥-elim (core-not-scope a x scoped)

-- A shared Server scope step passed its permission and ran the scope plan.
scope-gate : ∀ x s {b} → K.step (K.serverStep (E.run (S.scope x))) s ≡ just b →
  K.serverAllowed (E.run (S.scope x)) s ≡ true × S.scopeAdvance x (E.base (K.server s)) ≡ just (E.base (K.server b))
scope-gate x s eq with K.serverAllowed (E.run (S.scope x)) s
... | false = case eq of λ ()
... | true with E.step (E.run (S.scope x)) (K.server s) in actual
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → refl , Stage.run-step (S.scope x) (K.server s) actual }

returned-stage : ∀ b → SR.returned b ≡ true → stageK b ≡ S.serverReturned
returned-stage b eq with S.stage (E.base (K.server b))
... | S.serverReturned = refl
... | S.serving = case eq of λ ()
... | S.actionBodyExited = case eq of λ ()
... | S.actionResultAvailable = case eq of λ ()
... | S.closingAccept = case eq of λ ()
... | S.acceptCancelRequested = case eq of λ ()
... | S.acceptCancelDelivered = case eq of λ ()
... | S.acceptFailed = case eq of λ ()
... | (S.acceptForkClosing _ _) = case eq of λ ()
... | S.acceptBodyExited = case eq of λ ()
... | S.acceptResultAvailable = case eq of λ ()
... | S.acceptJoined = case eq of λ ()
... | S.serverStopped = case eq of λ ()
... | S.actionJoined = case eq of λ ()
... | S.igCancelRequested = case eq of λ ()
... | S.igJoined = case eq of λ ()
... | S.closingCM = case eq of λ ()

-- Initialization starts the Server serving.
server-initial : ∀ c {s} → S.initial c ≡ just s → S.stage s ≡ S.serving
server-initial c eq with Shared.admissions (Machine.world (O.core c)) | Shared.sockets (Machine.world (O.core c)) | N.initial c
... | [] | [] | just n = case just-injective eq of λ { refl → refl }
... | [] | [] | nothing = case eq of λ ()
... | [] | _ ∷ _ | _ = case eq of λ ()
... | _ ∷ _ | _ | _ = case eq of λ ()
ig-initial : ∀ c {s} → E.initial c ≡ just s → S.stage (E.base s) ≡ S.serving
ig-initial c eq with Machine.inboundRelease (O.core c) | Machine.remoteCall (O.core c) | S.initial c in initialized
... | nothing | nothing | just server = case just-injective eq of λ { refl → server-initial c initialized }
... | nothing | nothing | nothing = case eq of λ ()
... | nothing | just _ | _ = case eq of λ ()
... | just _ | _ | _ = case eq of λ ()
shared-initial : ∀ c g {s} → K.initial c g ≡ just s → stageK s ≡ S.serving
shared-initial c g eq with E.initial c in initialized
... | nothing = case eq of λ ()
... | just e = case just-injective eq of λ { refl → ig-initial c initialized }

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  private
    module T = K.Protocols canInitiate
    module Runtime = Facts.Protocols canInitiate
    module Outer = SR.Protocols canInitiate
    module Certified = RelaysFacts.Certified T.advance Outer.runtimeReturned

  stageT : T.Runtime → S.Stage
  stageT s = stageK (T.base s)

  -- Result caching writes only the peer context.
  cache-server : ∀ rid r result f b → K.server (T.cacheResult rid r result f b) ≡ K.server b
  cache-server rid r result f b with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
  ... | nothing = refl
  ... | just (current , _) with current ≟ rid
  ...   | no _ = refl
  ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
  ...     | nothing = refl
  ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
  ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
  ...         | nothing = refl
  ...         | just rs = refl
  cache-server rid r result f b | just (current , _) | yes _ | just peer | no _ | _ = refl
  cache-server rid r result f b | just (current , _) | yes _ | just peer | yes _ | no _ = refl

  -- A runtime step keeps the stage, or is a shared Server scope step.
  ScopeStep : T.Runtime → T.Runtime → Set
  ScopeStep s t = Σ S.ScopeAction (λ x → Σ K.State (λ b →
    K.step (K.serverStep (E.run (S.scope x))) (T.base s) ≡ just b × stageT t ≡ stageK b))
  enact-stage : ∀ p s {t} → T.enact p s ≡ just t → stageT t ≡ stageT s ⊎ ScopeStep s t
  enact-stage (T.inherit a f) s eq with K.step a (T.base s) in actual
  ... | nothing = case eq of λ ()
  ... | just b with shared-stage a (T.base s) actual
  ...   | inj₁ same = case just-injective eq of λ { refl → inj₁ same }
  ...   | inj₂ (x , refl) = case just-injective eq of λ { refl → inj₂ (x , b , actual , refl) }
  enact-stage (T.caller a f) s eq with PS.step a (K.peers (T.base s))
  ... | nothing = case eq of λ ()
  ... | just p = case just-injective eq of λ { refl → inj₁ refl }
  enact-stage (T.local f) s eq = case just-injective eq of λ { refl → inj₁ refl }
  enact-stage (T.reading r) s eq = case just-injective eq of λ { refl → inj₁ refl }
  enact-stage (T.traceFault w rid result fs) s eq = case just-injective eq of λ { refl → inj₁ refl }
  enact-stage (T.deliverTraceFault w rid result fs coordinator) s eq = case just-injective eq of λ { refl → inj₁ refl }
  enact-stage (T.birth w capturedFrame pool j rid r f) s eq = case just-injective eq of λ { refl → inj₁ refl }
  enact-stage (T.complete a rid r result) s eq with K.step a (T.base s) in actual
  ... | nothing = case eq of λ ()
  ... | just b with shared-stage a (T.base s) actual
  ...   | inj₁ same = case just-injective eq of λ { refl → inj₁
    (trans (cong (λ e → S.stage (E.base e)) (cache-server rid r result (T.front s) b)) same) }
  ...   | inj₂ (x , refl) = case just-injective eq of λ { refl → inj₂ (x , b , actual ,
    cong (λ e → S.stage (E.base e)) (cache-server rid r result (T.front s) b)) }
  advance-stage : ∀ a s {t} → T.advance a s ≡ just t → stageT t ≡ stageT s ⊎ ScopeStep s t
  advance-stage a s eq with T.choose a s
  ... | nothing = case eq of λ ()
  ... | just p = enact-stage p s eq

  -- Invariant: once the action thread is cancelled and joined, the peer side
  -- (both pools and the scope coordinator) is closed.
  Inv : T.Runtime → Set
  Inv s = Stage.post (stageT s) ≡ true → K.peerClosed (T.base s) ≡ true
  closed-before : ∀ a s {t} → T.advance a s ≡ just t → Inv s → Stage.post (stageT t) ≡ true →
    K.peerClosed (T.base s) ≡ true
  closed-before a s eq inv entered with advance-stage a s eq
  ... | inj₁ same = inv (subst (λ st → Stage.post st ≡ true) same entered)
  ... | inj₂ (x , b , stepped , same) with scope-gate x (T.base s) stepped
  ...   | allowed , scoped with Stage.scope-entry x (E.base (K.server (T.base s))) scoped
    (subst (λ st → Stage.post st ≡ true) same entered)
  ...     | inj₁ before = inv before
  ...     | inj₂ refl = allowed
  advance-preserves : ∀ a s {t} → T.advance a s ≡ just t → Inv s → Inv t
  advance-preserves a s {t} eq inv entered = closed-paths (T.base s) (T.base t)
    (Runtime.advance-projects a s eq) (closed-before a s eq inv entered)
  runs-preserve : ∀ {s as t} → T.Runs s as t → Inv s → Inv t
  runs-preserve T.stop inv = inv
  runs-preserve (T.more {s = s} {a = a} eq rest) inv = runs-preserve rest (advance-preserves a s eq inv)
  initial-inv : ∀ c g {s} → T.initialize c g ≡ just s → Inv s
  initial-inv c g eq with K.initial c g in initialized
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → λ entered →
    case subst (λ st → Stage.post st ≡ true) (shared-initial c g initialized) entered of λ () }

  -- The inner runtime trace of an outer run.
  InnerRun : T.Runtime → T.Runtime → Set
  InnerRun s t = Σ (List T.Event) (λ events → T.Runs s events t)
  outer-inner : ∀ a s {s′} → Outer.outerStep a s ≡ just s′ → InnerRun (Outer.inner s) (Outer.inner s′)
  outer-inner (Outer.innerAct a) (Outer.outer i (RR.relaysState t RR.inside)) eq with T.advance a i in moved
  ... | just i′ = case just-injective eq of λ { refl → (a ∷ []) , T.more moved T.stop }
  ... | nothing = case eq of λ ()
  outer-inner (Outer.innerAct a) (Outer.outer i (RR.relaysState t RR.cancelling)) ()
  outer-inner (Outer.innerAct a) (Outer.outer i (RR.relaysState t RR.finished)) ()
  outer-inner (Outer.relaysAct a) (Outer.outer i r) eq with RR.step (Outer.runtimeReturned i) a r
  ... | just r′ = case just-injective eq of λ { refl → [] , T.stop }
  ... | nothing = case eq of λ ()
  outer-runs : ∀ {s as s′} → Outer.Executes s as s′ → InnerRun (Outer.inner s) (Outer.inner s′)
  outer-runs Outer.done = [] , T.stop
  outer-runs (Outer.next {s = s} {a = a} eq rest) with outer-inner a s eq | outer-runs rest
  ... | first , path | others , remaining = (first ++ others) , Runtime.append-protocols path remaining

  -- Relays are joined exactly when the node forked them.
  Joined : Bool → Maybe RR.ThreadPhase → Set
  Joined scheduled t = (scheduled ≡ false × t ≡ nothing) ⊎ (scheduled ≡ true × t ≡ just RR.joined)
  relays-joined : ∀ scheduled t → RelaysFacts.present (RR.relaysState t RR.finished) ≡ RelaysFacts.present (RR.initial scheduled) →
    t ≡ nothing ⊎ t ≡ just RR.joined → Joined scheduled t
  relays-joined false .nothing same (inj₁ refl) = inj₁ (refl , refl)
  relays-joined false .(just RR.joined) () (inj₂ refl)
  relays-joined true .nothing () (inj₁ refl)
  relays-joined true .(just RR.joined) same (inj₂ refl) = inj₂ (refl , refl)

  -- The SI5 shutdown certificate at the finished state of the outer scope.
  record Complete (scheduled : Bool) (final : T.Runtime) (t : Maybe RR.ThreadPhase) : Set where
    field
      serverReturned : stageT final ≡ S.serverReturned
      peerClosed : K.peerClosed (T.base final) ≡ true
      peerComponents : Facts.Certificates (T.base final)
      relays : Joined scheduled t

  complete : ∀ {c g start scheduled as final t} → T.initialize c g ≡ just start →
    Outer.Executes (Outer.outer start (RR.initial scheduled)) as (Outer.outer final (RR.relaysState t RR.finished)) →
    Complete scheduled final t
  complete {c} {g} {start} {scheduled} {final = final} {t} initialized path
    with Certified.from-initial start scheduled path | outer-runs path
  ... | returned , joined | events , run with returned-stage (T.base final) returned
  ...   | atReturn with runs-preserve run (initial-inv c g initialized)
    (subst (λ st → Stage.post st ≡ true) (sym atReturn) refl)
  ...     | closed with Facts.closure-observation (T.base final) closed
  ...       | gov , bg , scopes = record
    { serverReturned = atReturn
    ; peerClosed = closed
    ; peerComponents = Runtime.initial-components initialized run gov bg scopes
    ; relays = relays-joined scheduled t (Certified.present-preserved path) joined }

{-# OPTIONS --guardedness #-}

-- Historical physical monitor exits in initialized frontend traces. WithoutQueue
-- erases normal/error payloads, so retain the actual source event and thread.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersMonitorReturns
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import ConnectionManagement.Domain using (HandleId; JobId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Properties.ServerPeers as Shared
import ConnectionManagement.Properties.ServerPeersContinuations as Continuations
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.OutboundMachine as O
private
 module K = Combined isBearerClosed isIOManagerError
 module PS = Supervision isIOManagerError
 module Pool = PS.Pool
 module Earlier = Continuations isBearerClosed isIOManagerError

-- An exception handled by the monitor returns normally from its Async body;
-- cancellation instead completes the distinct body-unwind operation.
data Kind : Set where
 normal exceptional cancelled : Kind
action : Kind → JobId → PS.Action
action normal tid = PS.finishMonitor tid
action exceptional tid = PS.finishMonitorError tid
action cancelled tid = PS.monitorBodyUnwound tid
exit : Kind → Pool.Exit
exit normal = Pool.normalExit
exit exceptional = Pool.normalExit
exit cancelled = Pool.cancelledExit

data Cause : Kind → PS.Thread → Set where
 normal-ready : ∀ {t} → PS.pc t ≡ PS.normalFinishing → Cause normal t
 error-ready : ∀ {t} → (err : ErrorId) → PS.pc t ≡ PS.errorFinishing err → Cause exceptional t
 unwound : ∀ {t} → PS.pc t ≡ PS.cancelling → (f : Cancel.Frame) →
   PS.interrupted t ≡ just f → Cancel.pc f ≡ Cancel.finished Cancel.abandoned → Cause cancelled t

operation : ∀ {kind t} → Cause kind t → JobId → Pool.Action
operation (normal-ready _) tid = Pool.bodyReturnedWith tid nothing
operation (error-ready err _) tid = Pool.bodyReturnedWith tid (just err)
operation (unwound _ _ _ _) tid = Pool.bodyUnwound tid

record BodyExit (kind : Kind) (tid : JobId) (s t : PS.State) : Set where
 constructor body-exit
 field
  thread : PS.Thread
  found : lookup tid (PS.monitors s) ≡ just thread
  cause : Cause kind thread
  bodyStep : Pool.step (operation cause tid) (PS.monitorPool s) ≡ just (PS.monitorPool t)
  exited : lookup tid (PS.monitors t) ≡ just (record thread { pc = PS.exited })

-- Derive the captured thread and real body operation from each enabled exit.
physical-exit : ∀ kind tid s {t} → PS.step (action kind tid) s ≡ just t → BodyExit kind tid s t
physical-exit normal tid s eq with Earlier.physical-monitor-return tid s eq
... | Earlier.monitor-body-return capturedThread found ready stepped exited pool =
 body-exit capturedThread found (normal-ready ready) stepped exited
physical-exit exceptional tid s eq with lookup tid (PS.monitors s) in found
... | nothing = case eq of λ ()
... | just capturedThread with PS.pc capturedThread in ready
...   | PS.errorFinishing actual with Pool.step (Pool.bodyReturnedWith tid (just actual)) (PS.monitorPool s) in returned
...     | nothing = case eq of λ ()
...     | just pool = case just-injective eq of λ { refl →
 body-exit capturedThread found (error-ready actual ready) returned
   (lookup-put tid (record capturedThread { pc = PS.exited }) (PS.monitors s)) }
physical-exit exceptional tid s eq | just capturedThread | PS.observing = case eq of λ ()
physical-exit exceptional tid s eq | just capturedThread | PS.normalFinishing = case eq of λ ()
physical-exit exceptional tid s eq | just capturedThread | PS.cancelling = case eq of λ ()
physical-exit exceptional tid s eq | just capturedThread | PS.exited = case eq of λ ()
physical-exit exceptional tid s eq | just capturedThread | PS.errorWait _ = case eq of λ ()
physical-exit cancelled tid s eq with lookup tid (PS.monitors s) in found
... | nothing = case eq of λ ()
... | just capturedThread with PS.pc capturedThread in ready | PS.interrupted capturedThread in interrupted
...   | PS.cancelling | just f with Cancel.pc f in complete
...     | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound tid) (PS.monitorPool s) in returned
...       | nothing = case eq of λ ()
...       | just pool = case just-injective eq of λ { refl →
 body-exit capturedThread found (unwound ready f interrupted complete) returned
   (lookup-put tid (record capturedThread { pc = PS.exited }) (PS.monitors s)) }
physical-exit cancelled tid s eq | just capturedThread | PS.cancelling | just f | Cancel.cleaning _ = case eq of λ ()
physical-exit cancelled tid s eq | just capturedThread | PS.cancelling | just f | Cancel.finished Cancel.cleanupComplete = case eq of λ ()
physical-exit cancelled tid s eq | just capturedThread | PS.cancelling | just f | Cancel.finished (Cancel.socketCloseFailed _) = case eq of λ ()
physical-exit cancelled tid s eq | just capturedThread | PS.cancelling | nothing = case eq of λ ()
physical-exit cancelled tid s eq | just capturedThread | PS.observing | _ = case eq of λ ()
physical-exit cancelled tid s eq | just capturedThread | PS.normalFinishing | _ = case eq of λ ()
physical-exit cancelled tid s eq | just capturedThread | PS.exited | _ = case eq of λ ()
physical-exit cancelled tid s eq | just capturedThread | PS.errorWait _ | _ = case eq of λ ()
physical-exit cancelled tid s eq | just capturedThread | PS.errorFinishing _ | _ = case eq of λ ()

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private module T = K.Protocols canInitiate
 peers : T.Runtime → PS.State
 peers s = K.peers (T.base s)
 event : Kind → JobId → T.Event
 event kind tid = T.dispatch (K.peerStep (action kind tid))

 -- Lower the actual enabled frontend event, retaining the original guards.
 finish : ∀ kind tid s t → T.advance (event kind tid) s ≡ just t → BodyExit kind tid (peers s) (peers t)
 finish kind tid s t eq with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate
   (K.peerStep (action kind tid)) s eq
 ... | next , advanced , same with same
 ...   | refl with Shared.peer-step isBearerClosed isIOManagerError (action kind tid) (T.base s) advanced
 ...     | p , stepped , samePeer , source = subst (BodyExit kind tid (peers s)) (sym samePeer)
   (physical-exit kind tid (peers s) stepped)

 record Initialized (start : T.Runtime) : Set where
  constructor initialized
  field
   configuration : O.Configuration
   governor : G.State
   initializer : T.initialize configuration governor ≡ just start

 -- This is an occurrence theorem, not inversion of a later terminal lookup.
 -- Both the initialized prefix and the exact enabled exit are in the trace.
 record Origin (start current : T.Runtime) (tid : JobId) (kind : Kind) : Set where
  constructor origin
  field
   initialization : Initialized start
   before after : T.Runtime
   prefix suffix : List T.Event
   reached : T.Runs start prefix before
   advanced : T.advance (event kind tid) before ≡ just after
   continued : T.Runs after suffix current
   body : BodyExit kind tid (peers before) (peers after)

 at-event : ∀ {start current} prefix suffix a → T.Runs start (prefix ++ (a ∷ suffix)) current →
   Σ T.Runtime (λ before → Σ T.Runtime (λ after → T.Runs start prefix before ×
     (T.advance a before ≡ just after) × T.Runs after suffix current))
 at-event [] suffix a (T.more {s = before} {t = after} stepped rest) = before , after , T.stop , stepped , rest
 at-event (a ∷ prefix) suffix target (T.more stepped rest) with at-event prefix suffix target rest
 ... | before , after , reached , advanced , continued = before , after , T.more stepped reached , advanced , continued

 initialized-occurrence : ∀ {c g start current} kind tid prefix suffix →
   T.initialize c g ≡ just start → T.Runs start (prefix ++ (event kind tid ∷ suffix)) current → Origin start current tid kind
 initialized-occurrence {c} {g} kind tid prefix suffix init path with at-event prefix suffix (event kind tid) path
 ... | before , after , reached , advanced , continued =
   origin (initialized c g init) before after prefix suffix reached advanced continued (finish kind tid before after advanced)

 -- The final event need not be searched for when a caller already has its
 -- initialized prefix and enabled edge.
 initialized-exit : ∀ {c g start before after prefix} kind tid →
   T.initialize c g ≡ just start → T.Runs start prefix before →
   T.advance (event kind tid) before ≡ just after → Origin start after tid kind
 initialized-exit {c} {g} {before = before} {after} {prefix} kind tid init reached advanced =
   origin (initialized c g init) before after prefix [] reached advanced T.stop (finish kind tid before after advanced)

 -- Histories retain their exact captured peer/worker/parent across arbitrary
 -- later enabled events, including registry removal and Async publication.
 extend : ∀ {start s t tid kind actions} → T.Runs s actions t → Origin start s tid kind → Origin start t tid kind
 extend {actions = actions} path (origin init before after prefix suffix reached advanced continued body) =
   origin init before after prefix (suffix ++ actions) reached advanced
     (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate continued path) body

 -- The two post-body operations have separate primitive certificates. Neither
 -- manufactures a body-exit witness from registry membership or Async state.
 deregister : ∀ tid s t → T.advance (T.dispatch (K.peerStep (PS.deregisterMonitor tid))) s ≡ just t →
   Pool.step (Pool.deregister tid) (PS.monitorPool (peers s)) ≡ just (PS.monitorPool (peers t))
 deregister tid s t eq with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate
   (K.peerStep (PS.deregisterMonitor tid)) s eq
 ... | next , advanced , same with same
 ...   | refl with Shared.peer-step isBearerClosed isIOManagerError (PS.deregisterMonitor tid) (T.base s) advanced
 ...     | p , stepped , samePeer , source with lookup tid (Pool.handles (PS.monitorPool (peers s))) | Pool.member tid (Pool.registered (PS.monitorPool (peers s)))
 ...       | just (Pool.deregisterPending ex) | true = case just-injective stepped of λ { refl → cong (λ q → just (PS.monitorPool q)) (sym samePeer) }
 ...       | nothing | _ = case stepped of λ ()
 ...       | just Pool.bodyRunning | _ = case stepped of λ ()
 ...       | just (Pool.bodyReturned _) | _ = case stepped of λ ()
 ...       | just Pool.bodyUnwinding | _ = case stepped of λ ()
 ...       | just (Pool.deregistered _) | _ = case stepped of λ ()
 ...       | just (Pool.resultAvailable _) | _ = case stepped of λ ()
 ...       | just (Pool.deregisterPending _) | false = case stepped of λ ()

 publish : ∀ tid s t → T.advance (T.dispatch (K.peerStep (PS.publishMonitorResult tid))) s ≡ just t →
   Pool.step (Pool.publishAsyncResult tid) (PS.monitorPool (peers s)) ≡ just (PS.monitorPool (peers t))
 publish tid s t eq with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate
   (K.peerStep (PS.publishMonitorResult tid)) s eq
 ... | next , advanced , same with same
 ...   | refl with Shared.peer-step isBearerClosed isIOManagerError (PS.publishMonitorResult tid) (T.base s) advanced
 ...     | p , stepped , samePeer , source with lookup tid (Pool.handles (PS.monitorPool (peers s)))
 ...       | just (Pool.deregistered ex) = case just-injective stepped of λ { refl → cong (λ q → just (PS.monitorPool q)) (sym samePeer) }
 ...       | nothing = case stepped of λ ()
 ...       | just Pool.bodyRunning = case stepped of λ ()
 ...       | just (Pool.bodyReturned _) = case stepped of λ ()
 ...       | just Pool.bodyUnwinding = case stepped of λ ()
 ...       | just (Pool.deregisterPending _) = case stepped of λ ()
 ...       | just (Pool.resultAvailable _) = case stepped of λ ()

 -- Each stage stores its own enabled source event and primitive pool step.
 -- Histories do not assert that a thread eventually reaches any later stage.
 record Removed (start current : T.Runtime) (tid : JobId) (kind : Kind) : Set where
  constructor removed
  field
   before after : T.Runtime
   body : Origin start before tid kind
   advanced : T.advance (T.dispatch (K.peerStep (PS.deregisterMonitor tid))) before ≡ just after
   poolStep : Pool.step (Pool.deregister tid) (PS.monitorPool (peers before)) ≡ just (PS.monitorPool (peers after))
   suffix : List T.Event
   continued : T.Runs after suffix current
 remove-origin : ∀ {start s t tid kind} → Origin start s tid kind →
   T.advance (T.dispatch (K.peerStep (PS.deregisterMonitor tid))) s ≡ just t → Removed start t tid kind
 remove-origin {s = s} {t} {tid} history stepped = removed s t history stepped (deregister tid s t stepped) [] T.stop

 record Published (start current : T.Runtime) (tid : JobId) (kind : Kind) : Set where
  constructor published
  field
   before after : T.Runtime
   removal : Removed start before tid kind
   advanced : T.advance (T.dispatch (K.peerStep (PS.publishMonitorResult tid))) before ≡ just after
   poolStep : Pool.step (Pool.publishAsyncResult tid) (PS.monitorPool (peers before)) ≡ just (PS.monitorPool (peers after))
   suffix : List T.Event
   continued : T.Runs after suffix current
 publish-origin : ∀ {start s t tid kind} → Removed start s tid kind →
   T.advance (T.dispatch (K.peerStep (PS.publishMonitorResult tid))) s ≡ just t → Published start t tid kind
 publish-origin {s = s} {t} {tid} history stepped = published s t history stepped (publish tid s t stepped) [] T.stop
 extend-published : ∀ {start s t tid kind actions} → T.Runs s actions t → Published start s tid kind → Published start t tid kind
 extend-published {actions = actions} path (published before after removal advanced poolStep suffix continued) =
   published before after removal advanced poolStep (suffix ++ actions)
     (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate continued path)

 -- A run containing these three consecutive events supplies all three
 -- certificates, with an arbitrary initialized prefix and continuing suffix.
 initialized-lifecycle : ∀ {c g start current} kind tid prefix suffix →
   T.initialize c g ≡ just start →
   T.Runs start (prefix ++ (event kind tid ∷ T.dispatch (K.peerStep (PS.deregisterMonitor tid)) ∷
     T.dispatch (K.peerStep (PS.publishMonitorResult tid)) ∷ suffix)) current → Published start current tid kind
 initialized-lifecycle kind tid prefix suffix init path with at-event prefix _ (event kind tid) path
 ... | before , after , reached , returned , T.more removedStep (T.more publishedStep rest) =
   extend-published rest (publish-origin (remove-origin (initialized-exit kind tid init reached returned) removedStep) publishedStep)

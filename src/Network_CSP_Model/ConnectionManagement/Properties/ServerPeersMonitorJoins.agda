{-# OPTIONS --guardedness #-}

-- Enabled inherited monitor joins carry an initialized, ordered lifecycle.
-- This is finite provenance; it does not assert that a join eventually occurs.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersMonitorJoins
 (isBearerClosed isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ)
import Data.List.Properties
import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (HandleId; JobId; WorkerId; EntryId)
import ConnectionManagement.Store
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerAdmission as Admission
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Properties.ServerPeers as Shared
import ConnectionManagement.Properties.PeerSupervision as Projection
import ConnectionManagement.Properties.JobPoolJoinOrder as Order
import ConnectionManagement.Properties.JobPoolCloseKernel as Close
import ConnectionManagement.Properties.ServerPeersMonitorReturns as Returns
import ConnectionManagement.Properties.ServerPeersMonitorBacking as Backing
import ConnectionManagement.Properties.ServerPeersMonitorStages as Stages
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationFacts
import ConnectionManagement.Properties.MuxCatchUnwind as CatchFacts
import ConnectionManagement.Properties.MuxDeltaQ as DeltaFacts
import ConnectionManagement.Properties.MuxStartupUnwind as StartupFacts
import ConnectionManagement.Properties.MuxHandlerExit as HandlerFacts
import ConnectionManagement.Rules.CMShutdown as Shutdown
module Handler = HandlerFacts isBearerClosed using (Publication; PhysicalWait; publication-observation; physical-wait-observation)
private
 module K = Combined isBearerClosed isIOManagerError
 module E = Exit isBearerClosed
 module A = Admission isBearerClosed
 module C = Context isIOManagerError
 module PS = Supervision isIOManagerError
 module Pool = PS.Pool
 module P = Projection isIOManagerError
 module R = Returns isBearerClosed isIOManagerError
 module N = Publication isBearerClosed
 module W = N.W
 module G = N.G
module Cursor = Order (Maybe ErrorId) false
private module Closed = Close (Maybe ErrorId) false

-- Invert the real physical-supervision action, retaining its actual pool step.
pool-join : ∀ s {t} → PS.step PS.joinMonitor s ≡ just t →
 Pool.step Pool.join (PS.monitorPool s) ≡ just (PS.monitorPool t)
pool-join s eq with Pool.step Pool.join (PS.monitorPool s) in advanced
... | nothing = case eq of λ ()
... | just p = case just-injective eq of λ { refl → refl }

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate
  module H = R.Frontend canInitiate
  module B = Backing.Frontend isBearerClosed isIOManagerError canInitiate
  module S = Stages.Frontend isBearerClosed isIOManagerError canInitiate
 peers : T.Runtime → PS.State
 peers s = K.peers (T.base s)
 pool : T.Runtime → Pool.State
 pool s = PS.monitorPool (peers s)
 event : T.Event
 event = T.dispatch (K.peerStep PS.joinMonitor)

 source-join : ∀ s {t} → T.advance event s ≡ just t → PS.step PS.joinMonitor (peers s) ≡ just (peers t)
 source-join s eq with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate
   (K.peerStep PS.joinMonitor) s eq
 ... | b , advanced , same with same
 ...   | refl with Shared.peer-step isBearerClosed isIOManagerError PS.joinMonitor (T.base s) advanced
 ...     | p , stepped , samePeer , source = trans stepped (cong just (sym samePeer))
 initialized-pool-prefix : ∀ {c g start actions s} → T.initialize c g ≡ just start → T.Runs start actions s →
   Σ (List Pool.Action) (λ poolActions → Pool.Executes Pool.initial poolActions (pool s))
 initialized-pool-prefix {c} initialized path with E.initial c
 ... | nothing = case initialized of λ ()
 ... | just e with just-injective initialized
 ...   | refl = P.Paths.background (Shared.Protocols.run-projects isBearerClosed isIOManagerError canInitiate path)
 initialized-order : ∀ {c g start actions s} → T.initialize c g ≡ just start → T.Runs start actions s → Cursor.Partition (pool s)
 initialized-order initialized path = Cursor.from-initial (proj₂ (initialized-pool-prefix initialized path))

 -- All fields are derived from initialization, a finite enabled prefix and the
 -- actual join. In particular, the terminal lookup and causal history are outputs.
 record Joined (start before after : T.Runtime) : Set where
  constructor joined-history
  field
   initialization : H.Initialized start
   prefix : List T.Event
   reached : T.Runs start prefix before
   advanced : T.advance event before ≡ just after
   sourceStep : PS.step PS.joinMonitor (peers before) ≡ just (peers after)
   primitiveStep : Pool.step Pool.join (pool before) ≡ just (pool after)
   shape : Cursor.Join (pool before) (pool after)
   partition : Cursor.Partition (pool before)
   captured : Cursor.Join.current shape ∈ Pool.snapshot (pool before)
   kind : R.Kind
   agrees : R.exit kind ≡ Cursor.Head.result (Cursor.Join.head shape)
   publication : S.Publication start before (Cursor.Join.current shape) kind
 initialized-join : ∀ {c g start actions before after} → T.initialize c g ≡ just start →
   T.Runs start actions before → T.advance event before ≡ just after → Joined start before after
 initialized-join {c} {g} {start} {actions} {before} {after} init path advanced =
   make (Cursor.inspect-join (pool before) poolAdvanced) (initialized-order init path)
   where
   source = source-join before advanced
   poolAdvanced = pool-join (peers before) source
   make : (shape : Cursor.Join (pool before) (pool after)) → Cursor.Partition (pool before) → Joined start before after
   make shape partition with S.initialized-published init path (Cursor.Head.available (Cursor.Join.head shape))
   ... | kind , agrees , publication = joined-history (H.initialized c g init) actions path advanced source poolAdvanced
     shape partition (Cursor.captured partition shape) kind agrees publication

 -- The snapshot is precisely the already-joined prefix, this ID and its tail.
 -- Head.state additionally fixes the joined append, remaining tail and closing PC.
 ordered-snapshot : ∀ {start before after} (w : Joined start before after) →
   Pool.snapshot (pool before) ≡ Pool.joined (pool before) ++
     (Cursor.Join.current (Joined.shape w) ∷ Cursor.Head.tail (Cursor.Join.head (Joined.shape w)))
 ordered-snapshot {before = before} w = trans (Joined.partition w)
   (cong (Pool.joined (pool before) ++_) (Cursor.Head.head (Cursor.Join.head (Joined.shape w))))
 publication-after : ∀ {start before after} (w : Joined start before after) →
   S.Publication start after (Cursor.Join.current (Joined.shape w)) (Joined.kind w)
 publication-after w = S.extend-publication (T.more {a = event} (Joined.advanced w) T.stop) (Joined.publication w)
 exit-after : ∀ {start before after} (w : Joined start before after) →
   B.History start after (Cursor.Join.current (Joined.shape w)) (Joined.kind w)
 exit-after w = S.publication-exit (publication-after w)

 -- Observations can name the derived ID/cause without recomputing a history.
 observed-id : ∀ {start before after j tail} (w : Joined start before after) →
   Pool.remaining (pool before) ≡ j ∷ tail → Cursor.Join.current (Joined.shape w) ≡ j
 observed-id w known = Data.List.Properties.∷-injectiveˡ
   (trans (sym (Cursor.Head.head (Cursor.Join.head (Joined.shape w)))) known)
 available-exit : ∀ {a b} → Pool.resultAvailable a ≡ Pool.resultAvailable b → a ≡ b
 available-exit refl = refl
 observed-publication : ∀ {start before after} (w : Joined start before after) j ex →
   Cursor.Join.current (Joined.shape w) ≡ j →
   ConnectionManagement.Store.lookup j (Pool.handles (pool before)) ≡ just (Pool.resultAvailable ex) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × S.Publication start before j kind)
 observed-publication w .(Cursor.Join.current (Joined.shape w)) ex refl known = Joined.kind w ,
   trans (Joined.agrees w) (available-exit (just-injective
     (trans (sym (Cursor.Head.available (Cursor.Join.head (Joined.shape w)))) known))) , Joined.publication w


 -- A captured handle retains its exact exit cause and complete earlier stages.
 record SnapshotLifecycle (start current : T.Runtime) (tid : JobId) : Set where
  constructor snapshot-lifecycle
  field
   kind : R.Kind
   terminal : ConnectionManagement.Store.lookup tid (Pool.handles (pool current)) ≡ just (Pool.resultAvailable (R.exit kind))
   publication : S.Publication start current tid kind

 -- The histories follow the captured list order. This certifies a finite closed
 -- observation and does not assert eventual closure or joins of excluded handles.
 record ClosedSnapshot (start current : T.Runtime) : Set where
  constructor closed-snapshot
  field
   initialization : H.Initialized start
   prefix : List T.Event
   reached : T.Runs start prefix current
   closed : Pool.phase (pool current) ≡ Pool.closedPool
   empty : Pool.remaining (pool current) ≡ []
   order : Pool.snapshot (pool current) ≡ Pool.joined (pool current)
   histories : All.All (SnapshotLifecycle start current) (Pool.snapshot (pool current))
 initialized-closed : ∀ {c g start actions current} → T.initialize c g ≡ just start →
   T.Runs start actions current → Pool.phase (pool current) ≡ Pool.closedPool → ClosedSnapshot start current
 initialized-closed {c} {g} {start} {actions} {current} init path closed =
   closed-snapshot (H.initialized c g init) actions path closed empty order
     (All.tabulate (λ {tid} member → lifecycle tid member))
   where
   poolPath = proj₂ (initialized-pool-prefix init path)
   empty : Pool.remaining (pool current) ≡ []
   empty = Closed.exec-empty poolPath (λ ()) closed
   order : Pool.snapshot (pool current) ≡ Pool.joined (pool current)
   order = trans (Cursor.from-initial poolPath)
     (trans (cong (Pool.joined (pool current) ++_) empty) (++-identityʳ (Pool.joined (pool current))))
   lifecycle : ∀ tid → tid ∈ Pool.snapshot (pool current) → SnapshotLifecycle start current tid
   lifecycle tid member with Closed.from-initial poolPath closed tid member
   ... | ex , available with S.initialized-published init path available
   ...   | kind , agrees , publication = snapshot-lifecycle kind
     (trans available (cong (λ ex → just (Pool.resultAvailable ex)) (sym agrees))) publication

 -- Membership queries retrieve a derived history from either equal ordered list.
 captured-lifecycle : ∀ {start current tid} → ClosedSnapshot start current →
   tid ∈ Pool.snapshot (pool current) → SnapshotLifecycle start current tid
 captured-lifecycle certificate member = All.lookup (ClosedSnapshot.histories certificate) member
 histories-in-join-order : ∀ {start current} → ClosedSnapshot start current →
   All.All (SnapshotLifecycle start current) (Pool.joined (pool current))
 histories-in-join-order {start} {current} certificate =
   subst (All.All (SnapshotLifecycle start current)) (ClosedSnapshot.order certificate) (ClosedSnapshot.histories certificate)
 joined-lifecycle : ∀ {start current tid} → ClosedSnapshot start current →
   tid ∈ Pool.joined (pool current) → SnapshotLifecycle start current tid
 joined-lifecycle certificate member = All.lookup (histories-in-join-order certificate) member
 lifecycle-exit : ∀ {start current tid} (w : SnapshotLifecycle start current tid) → B.History start current tid (SnapshotLifecycle.kind w)
 lifecycle-exit w = S.publication-exit (SnapshotLifecycle.publication w)
 cancelled-lifecycle : ∀ {start current tid} → SnapshotLifecycle start current tid →
   ConnectionManagement.Store.lookup tid (Pool.handles (pool current)) ≡ just (Pool.resultAvailable Pool.cancelledExit) →
   S.Publication start current tid R.cancelled
 cancelled-lifecycle w known = S.cancelled-publication (SnapshotLifecycle.kind w ,
   available-exit (just-injective (trans (sym (SnapshotLifecycle.terminal w)) known)) , SnapshotLifecycle.publication w)


 -- A continuing execution with the same whole pool preserves the original
 -- cause and publication/removal/exit history; only its suffix is extended.
 extend-lifecycle : ∀ {start before after actions tid} → T.Runs before actions after →
   pool after ≡ pool before → SnapshotLifecycle start before tid → SnapshotLifecycle start after tid
 extend-lifecycle {tid = tid} path same w = snapshot-lifecycle (SnapshotLifecycle.kind w)
   (trans (cong (λ p → ConnectionManagement.Store.lookup tid (Pool.handles p)) same) (SnapshotLifecycle.terminal w))
   (S.extend-publication path (SnapshotLifecycle.publication w))
 extend-closed : ∀ {start before after actions} → T.Runs before actions after →
   pool after ≡ pool before → ClosedSnapshot start before → ClosedSnapshot start after
 extend-closed {start} {before} {after} {actions} path same w = closed-snapshot
   (ClosedSnapshot.initialization w) (ClosedSnapshot.prefix w ++ actions)
   (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate (ClosedSnapshot.reached w) path)
   (trans (cong Pool.phase same) (ClosedSnapshot.closed w))
   (trans (cong Pool.remaining same) (ClosedSnapshot.empty w))
   (trans (cong Pool.snapshot same) (trans (ClosedSnapshot.order w) (sym (cong Pool.joined same))))
   (subst (All.All (SnapshotLifecycle start after)) (sym (cong Pool.snapshot same))
     (All.map (extend-lifecycle path same) (ClosedSnapshot.histories w)))

 callback-action : K.Action
 callback-action = K.serverStep (E.run (A.scope A.returnAction))
 callback-event : T.Event
 callback-event = T.dispatch callback-action
 record CallbackExit (start before after : T.Runtime) : Set where
  constructor callback-exit
  field
   initialization : H.Initialized start
   prefix : List T.Event
   reached : T.Runs start prefix before
   returned : T.advance callback-event before ≡ just after
   sharedStep : K.step callback-action (T.base before) ≡ just (T.base after)
   contextSame : K.context (T.base after) ≡ K.context (T.base before)
   gate : K.peerClosed (T.base before) ≡ true
   components : Shared.Certificates isBearerClosed isIOManagerError (T.base before)
   monitors : ClosedSnapshot start before

 -- The actual callback supplies all closure gates. No closed-phase observation
 -- or previously constructed lifecycle certificate is required from its caller.
 initialized-callback : ∀ {c g start actions before after} → T.initialize c g ≡ just start →
   T.Runs start actions before → T.advance callback-event before ≡ just after → CallbackExit start before after
 initialized-callback {c} {g} {start} {actions} {before} {after} init path returned with
   Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate callback-action before returned
 ... | next , advanced , same with same
 ...   | refl with Shared.server-step isBearerClosed isIOManagerError (E.run (A.scope A.returnAction)) (T.base before) advanced
 ...     | e , stepped , sameServer , sameContext with Shared.closure-observation isBearerClosed isIOManagerError
     (T.base before) (Shared.callback-gate isBearerClosed isIOManagerError (T.base before) advanced)
 ...       | gov , bg , scopes = callback-exit (H.initialized c g init) actions path returned advanced sameContext
     (Shared.callback-gate isBearerClosed isIOManagerError (T.base before) advanced)
     (Shared.Protocols.initial-components isBearerClosed isIOManagerError canInitiate init path gov bg scopes)
     (initialized-closed init path bg)

 -- The post-state certificate extends these same histories, rather than making
 -- an independent choice of causes at another terminal lookup.
 callback-pool-same : ∀ {start before after} → CallbackExit start before after → pool after ≡ pool before
 callback-pool-same w = cong C.monitorPool (CallbackExit.contextSame w)
 callback-monitors-after : ∀ {start before after} → CallbackExit start before after → ClosedSnapshot start after
 callback-monitors-after w = extend-closed (T.more {a = callback-event} (CallbackExit.returned w) T.stop)
   (callback-pool-same w) (CallbackExit.monitors w)
 transport-components : ∀ {s t} → K.context t ≡ K.context s →
   Shared.Certificates isBearerClosed isIOManagerError s → Shared.Certificates isBearerClosed isIOManagerError t
 transport-components same certificates rewrite same = certificates
 callback-components-after : ∀ {start before after} → CallbackExit start before after →
   Shared.Certificates isBearerClosed isIOManagerError (T.base after)
 callback-components-after {before = before} {after} w = transport-components {s = T.base before} {t = T.base after}
   (CallbackExit.contextSame w) (CallbackExit.components w)


 -- Each suffix event executes a real Server/IG action with its original guards.
 server-event : E.Action → T.Event
 server-event a = T.dispatch (K.serverStep a)
 data ServerRuns : T.Runtime → List E.Action → T.Runtime → Set where
  serverDone : ∀ {s} → ServerRuns s [] s
  serverNext : ∀ {s t u a actions} → T.advance (server-event a) s ≡ just t →
    ServerRuns t actions u → ServerRuns s (a ∷ actions) u
 server-runs : ∀ {s actions t} → ServerRuns s actions t → T.Runs s (map server-event actions) t
 server-runs serverDone = T.stop
 server-runs (serverNext {a = a} advanced rest) = T.more {a = server-event a} advanced (server-runs rest)
 -- Reuse an existing enabled runtime trace when its events are these actions.
 server-runs-from : ∀ {s actions t} → T.Runs s (map server-event actions) t → ServerRuns s actions t
 server-runs-from {actions = []} T.stop = serverDone
 server-runs-from {actions = a ∷ actions} (T.more advanced rest) = serverNext {a = a} advanced (server-runs-from rest)
 server-step-context : ∀ a s {t} → T.advance (server-event a) s ≡ just t →
   K.context (T.base t) ≡ K.context (T.base s)
 server-step-context a s advanced with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate
   (K.serverStep a) s advanced
 ... | b , stepped , same with same
 ...   | refl with Shared.server-step isBearerClosed isIOManagerError a (T.base s) stepped
 ...     | e , actual , sameServer , sameContext = sameContext
 server-context : ∀ {s actions t} → ServerRuns s actions t → K.context (T.base t) ≡ K.context (T.base s)
 server-context serverDone = refl
 server-context (serverNext {s = s} {a = a} advanced rest) = trans (server-context rest) (server-step-context a s advanced)

 -- A real CM-entry action reaches closingCM; no stage observation is supplied.
 admission-entry-stage : ∀ s {t} → A.step (A.scope A.beginCM) s ≡ just t → A.stage t ≡ A.closingCM
 admission-entry-stage s eq with A.stage s
 ... | A.igJoined = case just-injective eq of λ { refl → refl }
 ... | A.serving = case eq of λ ()
 ... | A.actionBodyExited = case eq of λ ()
 ... | A.actionResultAvailable = case eq of λ ()
 ... | A.closingAccept = case eq of λ ()
 ... | A.acceptCancelRequested = case eq of λ ()
 ... | A.acceptCancelDelivered = case eq of λ ()
 ... | A.acceptFailed = case eq of λ ()
 ... | A.acceptBodyExited = case eq of λ ()
 ... | A.acceptResultAvailable = case eq of λ ()
 ... | A.acceptJoined = case eq of λ ()
 ... | A.serverStopped = case eq of λ ()
 ... | A.actionJoined = case eq of λ ()
 ... | A.igCancelRequested = case eq of λ ()
 ... | A.closingCM = case eq of λ ()
 ... | A.serverReturned = case eq of λ ()
 entry-stage : ∀ s {t} → E.step (E.run (A.scope A.beginCM)) s ≡ just t → A.stage (E.base t) ≡ A.closingCM
 entry-stage s eq with A.step (A.scope A.beginCM) (E.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just server = case just-injective eq of λ { refl → admission-entry-stage (E.base s) actual }
 cm-action : K.Action
 cm-action = K.serverStep (E.run (A.scope A.beginCM))
 cm-event : T.Event
 cm-event = T.dispatch cm-action
 shared-entry-stage : ∀ s {t} → K.step cm-action s ≡ just t → A.stage (E.base (K.server t)) ≡ A.closingCM
 shared-entry-stage s advanced with Shared.server-step isBearerClosed isIOManagerError (E.run (A.scope A.beginCM)) s advanced
 ... | e , actual , sameServer , sameContext = trans (cong (λ e → A.stage (E.base e)) sameServer) (entry-stage (K.server s) actual)
 cm-stage : ∀ s {t} → T.advance cm-event s ≡ just t → A.stage (E.base (K.server (T.base t))) ≡ A.closingCM
 cm-stage s advanced with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate cm-action s advanced
 ... | b , actual , same = trans (cong (λ b → A.stage (E.base (K.server b))) same) (shared-entry-stage (T.base s) actual)

 -- The retained callback and actual Server/IG suffix identify CM entry, while
 -- keeping entry separate from completion of CM, handlers or raw admissions.
 record CMEntry (start current : T.Runtime) : Set where
  constructor cm-entry
  field
   callbackBefore callbackAfter beforeEntry : T.Runtime
   callback : CallbackExit start callbackBefore callbackAfter
   actions : List E.Action
   cleanup : ServerRuns callbackAfter actions beforeEntry
   entered : T.advance cm-event beforeEntry ≡ just current
   atCM : A.stage (E.base (K.server (T.base current))) ≡ A.closingCM
 initialized-cm-entry : ∀ {c g start prefix callbackBefore callbackAfter actions beforeEntry current} →
   T.initialize c g ≡ just start → T.Runs start prefix callbackBefore →
   T.advance callback-event callbackBefore ≡ just callbackAfter → ServerRuns callbackAfter actions beforeEntry →
   T.advance cm-event beforeEntry ≡ just current → CMEntry start current
 initialized-cm-entry {callbackBefore = before} {callbackAfter = after} {actions} {beforeEntry} init prefix returned cleanup entered =
   cm-entry before after beforeEntry (initialized-callback init prefix returned) actions cleanup entered (cm-stage beforeEntry entered)
 cm-cleanup : ∀ {start current} (w : CMEntry start current) →
   ServerRuns (CMEntry.callbackAfter w) (CMEntry.actions w ++ (E.run (A.scope A.beginCM) ∷ [])) current
 cm-cleanup w = append-entry (CMEntry.cleanup w) (CMEntry.entered w)
   where
   append-entry : ∀ {s actions t u} → ServerRuns s actions t → T.advance cm-event t ≡ just u →
     ServerRuns s (actions ++ (E.run (A.scope A.beginCM) ∷ [])) u
   append-entry serverDone entered = serverNext {a = E.run (A.scope A.beginCM)} entered serverDone
   append-entry (serverNext advanced rest) entered = serverNext advanced (append-entry rest entered)
 cm-context-same : ∀ {start current} (w : CMEntry start current) →
   K.context (T.base current) ≡ K.context (T.base (CMEntry.callbackAfter w))
 cm-context-same w = server-context (cm-cleanup w)
 cm-monitors : ∀ {start current} → CMEntry start current → ClosedSnapshot start current
 cm-monitors w = extend-closed (server-runs (cm-cleanup w)) (cong C.monitorPool (cm-context-same w))
   (callback-monitors-after (CMEntry.callback w))
 cm-components : ∀ {start current} → CMEntry start current → Shared.Certificates isBearerClosed isIOManagerError (T.base current)
 cm-components {current = current} w = transport-components {s = T.base (CMEntry.callbackAfter w)} {t = T.base current}
   (cm-context-same w) (callback-components-after (CMEntry.callback w))


 -- A suffix ending in beginCM exposes its actual predecessor and entry step.
 private
  record EntryTail (s : T.Runtime) (actions : List E.Action) (current : T.Runtime) : Set where
   constructor entry-tail
   field before : T.Runtime
         cleanup : ServerRuns s actions before
         entered : T.advance cm-event before ≡ just current
  split-entry : ∀ {s actions current} → ServerRuns s (actions ++ (E.run (A.scope A.beginCM) ∷ [])) current → EntryTail s actions current
  split-entry {s} {actions = []} (serverNext advanced serverDone) = entry-tail s serverDone advanced
  split-entry {actions = a ∷ actions} (serverNext advanced rest) with split-entry {actions = actions} rest
  ... | entry-tail before cleanup entered = entry-tail before (serverNext {a = a} advanced cleanup) entered
 initialized-cm-entry-run : ∀ {c g start prefix callbackBefore callbackAfter actions current} →
   T.initialize c g ≡ just start → T.Runs start prefix callbackBefore →
   T.advance callback-event callbackBefore ≡ just callbackAfter →
   ServerRuns callbackAfter (actions ++ (E.run (A.scope A.beginCM) ∷ [])) current → CMEntry start current
 initialized-cm-entry-run {actions = actions} init prefix returned cleanup with split-entry {actions = actions} cleanup
 ... | entry-tail before steps entered = initialized-cm-entry init prefix returned steps entered


 -- Inherited handler actions retain every existing wrapper permission.
 handler-action : W.Action → E.Action
 handler-action a = E.run (A.run (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run a))))))
 handler-event : W.Action → T.Event
 handler-event a = server-event (handler-action a)
 physical : T.Runtime → W.State
 physical s = N.R.base (N.raw (A.base (E.base (K.server (T.base s)))))
 admission-network : ∀ a s {t} → A.step (A.run a) s ≡ just t → N.step a (A.base s) ≡ just (A.base t)
 admission-network a s eq with A.allowed a s
 ... | false = case eq of λ ()
 ... | true with N.step a (A.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → refl }
 ig-network : ∀ a s {t} → E.step (E.run (A.run a)) s ≡ just t →
   N.step a (A.base (E.base s)) ≡ just (A.base (E.base t))
 ig-network a s eq with E.runAllowed (A.run a) s
 ... | false = case eq of λ ()
 ... | true with A.step (A.run a) (E.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just server = case just-injective eq of λ { refl → admission-network a (E.base s) actual }
 network-physical : ∀ a s {t} → N.step (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run a))))) s ≡ just t →
   W.step a (N.R.base (N.raw s)) ≡ just (N.R.base (N.raw t))
 network-physical a s eq with PublicationFacts.inherited-observation isBearerClosed (N.C.run (N.D.run (N.R.run (N.D.X.run a)))) s eq
 ... | c , actual , refl with CatchFacts.inherited-observation isBearerClosed (N.D.run (N.R.run (N.D.X.run a))) (N.base s) actual
 ...   | d , actual , refl with DeltaFacts.inherited-observation isBearerClosed (N.R.run (N.D.X.run a)) (N.C.base (N.base s)) actual
 ...     | r , actual , refl with StartupFacts.inherited-observation isBearerClosed (N.D.X.run a) (N.raw s) actual
 ...       | x , actual , refl = actual
 physical-lower : ∀ a s {t} → T.advance (handler-event a) s ≡ just t → W.step a (physical s) ≡ just (physical t)
 physical-lower a s eq with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate (K.serverStep (handler-action a)) s eq
 ... | b , actual , same with same
 ...   | refl with Shared.server-step isBearerClosed isIOManagerError (handler-action a) (T.base s) actual
 ...     | e , actual , sameServer , sameContext with sameServer
 ...       | refl = network-physical a (A.base (E.base (K.server (T.base s))))
     (ig-network (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run a))))) (K.server (T.base s)) actual)

 -- A mux receipt acknowledges delivery to the captured worker; it does not
 -- manufacture a handler result or satisfy CM's collective wait.
 record MuxReceipt (err : ErrorId) (before after : W.State) : Set where
  constructor mux-receipt
  field
   entry : EntryId
   worker : WorkerId
   next : G.State
   awaiting : Shutdown.phase (W.shutdown before) ≡ Shutdown.awaitDelivery entry worker
   aborted : G.step (G.abortOwner worker err) (W.base before) ≡ just next
   acknowledged : W.control Shutdown.acknowledgeDelivery (record before { base = next }) ≡ just after
 mux-receipt-observation : ∀ err s {t} → W.step (W.deliverShutdownMux err) s ≡ just t → MuxReceipt err s t
 mux-receipt-observation err s eq with Shutdown.phase (W.shutdown s) in awaited
 ... | Shutdown.awaitDelivery e w with G.step (G.abortOwner w err) (W.base s) in aborted
 ...   | nothing = case eq of λ ()
 ...   | just g = mux-receipt e w g awaited aborted eq
 mux-receipt-observation err s eq | Shutdown.initial = case eq of λ ()
 mux-receipt-observation err s eq | Shutdown.reading = case eq of λ ()
 mux-receipt-observation err s eq | Shutdown.sendReady _ _ = case eq of λ ()
 mux-receipt-observation err s eq | Shutdown.awaitResults = case eq of λ ()
 mux-receipt-observation err s eq | Shutdown.closed = case eq of λ ()
 physical-receipt : ∀ err s {t} → T.advance (handler-event (W.deliverShutdownMux err)) s ≡ just t → MuxReceipt err (physical s) (physical t)
 physical-receipt err s eq = mux-receipt-observation err (physical s) (physical-lower (W.deliverShutdownMux err) s eq)
 physical-publication : ∀ worker s {t} → T.advance (handler-event (W.publishAsyncResult worker)) s ≡ just t → Handler.Publication worker (physical s) (physical t)
 physical-publication worker s eq = Handler.publication-observation worker (physical s) (physical-lower (W.publishAsyncResult worker) s eq)
 physical-wait : ∀ s {t} → T.advance (handler-event (W.shutdownStep Shutdown.finishClose)) s ≡ just t → Handler.PhysicalWait (physical s) (physical t)
 physical-wait s eq = Handler.physical-wait-observation (physical s) (physical-lower (W.shutdownStep Shutdown.finishClose) s eq)

 -- All these guarded Server actions preserve the already-closed peer scopes.
 follow-monitors : ∀ {start entry current actions} → CMEntry start entry → ServerRuns entry actions current → ClosedSnapshot start current
 follow-monitors entry path = extend-closed (server-runs path) (cong C.monitorPool (server-context path)) (cm-monitors entry)
 follow-components : ∀ {start entry current actions} → CMEntry start entry → ServerRuns entry actions current → Shared.Certificates isBearerClosed isIOManagerError (T.base current)
 follow-components {entry = entry} {current} certificate path = transport-components {s = T.base entry} {t = T.base current}
   (server-context path) (cm-components certificate)
 server-append : ∀ {s as t bs u} → ServerRuns s as t → ServerRuns t bs u → ServerRuns s (as ++ bs) u
 server-append serverDone tail = tail
 server-append (serverNext advanced rest) tail = serverNext advanced (server-append rest tail)
 record CMResultWait (start before after : T.Runtime) : Set where
  constructor cm-result-wait
  field
   entryPoint : T.Runtime
   entry : CMEntry start entryPoint
   actions : List E.Action
   cleanup : ServerRuns entryPoint actions before
   waited : T.advance (handler-event (W.shutdownStep Shutdown.finishClose)) before ≡ just after
   observed : Handler.PhysicalWait (physical before) (physical after)
 result-wait : ∀ {start entry before after actions} → CMEntry start entry → ServerRuns entry actions before →
   T.advance (handler-event (W.shutdownStep Shutdown.finishClose)) before ≡ just after → CMResultWait start before after
 result-wait {entry = entry} {before = before} certificate path waited = cm-result-wait entry certificate _ path waited (physical-wait before waited)
 initialized-cm-result-wait : ∀ {c g start prefix callbackBefore callbackAfter entryActions entry before actions after} →
   T.initialize c g ≡ just start → T.Runs start prefix callbackBefore → T.advance callback-event callbackBefore ≡ just callbackAfter →
   ServerRuns callbackAfter (entryActions ++ (E.run (A.scope A.beginCM) ∷ [])) entry → ServerRuns entry actions before →
   T.advance (handler-event (W.shutdownStep Shutdown.finishClose)) before ≡ just after → CMResultWait start before after
 initialized-cm-result-wait {entryActions = entryActions} init prefix returned entered cleanup waited =
   result-wait (initialized-cm-entry-run {actions = entryActions} init prefix returned entered) cleanup waited
 wait-monitors-before : ∀ {start before after} → CMResultWait start before after → ClosedSnapshot start before
 wait-monitors-before w = follow-monitors (CMResultWait.entry w) (CMResultWait.cleanup w)
 wait-cleanup : ∀ {start before after} (w : CMResultWait start before after) →
   ServerRuns (CMResultWait.entryPoint w) (CMResultWait.actions w ++ (handler-action (W.shutdownStep Shutdown.finishClose) ∷ [])) after
 wait-cleanup w = server-append (CMResultWait.cleanup w) (serverNext {a = handler-action (W.shutdownStep Shutdown.finishClose)} (CMResultWait.waited w) serverDone)
 wait-monitors-after : ∀ {start before after} → CMResultWait start before after → ClosedSnapshot start after
 wait-monitors-after w = follow-monitors (CMResultWait.entry w) (wait-cleanup w)
 wait-components-after : ∀ {start before after} → CMResultWait start before after → Shared.Certificates isBearerClosed isIOManagerError (T.base after)
 wait-components-after w = follow-components (CMResultWait.entry w) (wait-cleanup w)


 -- A completion can update the peer cache while these three scopes stay fixed.
 frame-view : T.Runtime → P.View
 frame-view s = Shared.Protocols.protocol-view isBearerClosed isIOManagerError canInitiate s
 server-plan : T.Plan → Bool
 server-plan (T.inherit (K.serverStep a) f) = true
 server-plan (T.complete (K.serverStep a) rid r result) = true
 server-plan _ = false
 framed : T.Event → T.Runtime → Bool
 framed event s with T.choose event s
 ... | nothing = false
 ... | just plan = server-plan plan
 view-context : ∀ s t → K.context (T.base t) ≡ K.context (T.base s) → frame-view t ≡ frame-view s
 view-context s t same rewrite same = refl
 shared-server-view : ∀ a s {t} → K.step (K.serverStep a) s ≡ just t → Shared.view isBearerClosed isIOManagerError t ≡ Shared.view isBearerClosed isIOManagerError s
 shared-server-view a s actual with Shared.server-step isBearerClosed isIOManagerError a s actual
 ... | e , stepped , sameServer , sameContext rewrite sameContext = refl
 enact-frame : ∀ plan s {t} → server-plan plan ≡ true → T.enact plan s ≡ just t → frame-view t ≡ frame-view s
 enact-frame (T.inherit (K.serverStep a) f) s safe eq with K.step (K.serverStep a) (T.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → shared-server-view a (T.base s) actual }
 enact-frame (T.complete (K.serverStep a) rid r result) s safe eq with K.step (K.serverStep a) (T.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → trans
   (Shared.Protocols.cache-view isBearerClosed isIOManagerError canInitiate rid r result (T.front s) b)
   (shared-server-view a (T.base s) actual) }
 enact-frame (T.inherit (K.peerStep a) f) s () eq
 enact-frame (T.inherit (K.coreStep a) f) s () eq
 enact-frame (T.complete (K.peerStep a) rid r result) s () eq
 enact-frame (T.complete (K.coreStep a) rid r result) s () eq
 enact-frame (T.caller a f) s () eq
 enact-frame (T.local f) s () eq
 enact-frame (T.reading r) s () eq
 enact-frame (T.traceFault w rid result fs) s () eq
 enact-frame (T.deliverTraceFault w rid result fs coordinator) s () eq
 enact-frame (T.birth w capturedFrame protocolPool j rid r f) s () eq
 advance-frame : ∀ event s {t} → framed event s ≡ true → T.advance event s ≡ just t → frame-view t ≡ frame-view s
 advance-frame event s safe eq with T.choose event s
 ... | nothing = case safe of λ ()
 ... | just plan = enact-frame plan s safe eq

 -- Canonical release operations preserve the complete peer context. Their
 -- source writes and caller permissions are still checked by the real step.
 core-release-context : ∀ caller action s {t} →
   K.step (K.coreStep (O.release caller action)) s ≡ just t → K.context t ≡ K.context s
 core-release-context caller action s eq with K.coreAllowed (O.release caller action) s
 ... | false = case eq of λ ()
 ... | true with E.step (K.coreAction (O.release caller action)) (K.server s)
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → refl }
 core-release-view : ∀ caller action s {t} →
   T.advance (T.dispatch (K.coreStep (O.release caller action))) s ≡ just t →
   frame-view t ≡ frame-view s
 core-release-view caller action s {t} actual with
   Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate
     (K.coreStep (O.release caller action)) s actual
 ... | next , advanced , same = view-context s t
   (trans (cong K.context same) (core-release-context caller action (T.base s) advanced))

 -- Every edge retains its actual event/guard and selected-plan restriction.
 data FramedRuns : T.Runtime → List T.Event → T.Runtime → Set where
  frameDone : ∀ {s} → FramedRuns s [] s
  frameNext : ∀ {s t u event events} → framed event s ≡ true → T.advance event s ≡ just t →
    FramedRuns t events u → FramedRuns s (event ∷ events) u
  -- A core release retains its own canonical label; it is not relabelled as
  -- an inherited Server action merely to obtain a closure certificate.
  frameRelease : ∀ {s t u caller action events} →
    T.advance (T.dispatch (K.coreStep (O.release caller action))) s ≡ just t →
    FramedRuns t events u →
    FramedRuns s (T.dispatch (K.coreStep (O.release caller action)) ∷ events) u
 framed-runs : ∀ {s events t} → FramedRuns s events t → T.Runs s events t
 framed-runs frameDone = T.stop
 framed-runs (frameNext {event = event} safe actual rest) = T.more {a = event} actual (framed-runs rest)
 framed-runs (frameRelease {caller = caller} {action = action} actual rest) =
   T.more {a = T.dispatch (K.coreStep (O.release caller action))} actual (framed-runs rest)
 framed-view : ∀ {s events t} → FramedRuns s events t → frame-view t ≡ frame-view s
 framed-view frameDone = refl
 framed-view (frameNext {s = s} {event = event} safe actual rest) = trans (framed-view rest) (advance-frame event s safe actual)
 framed-view (frameRelease {s = s} {caller = caller} {action = action} actual rest) =
   trans (framed-view rest) (core-release-view caller action s actual)
 server-framed : ∀ a s {t} → T.advance (server-event a) s ≡ just t → framed (server-event a) s ≡ true
 server-framed a s actual with T.inheritAllowed (K.serverStep a) s
 ... | false = case actual of λ ()
 ... | true = refl
 framed-server : ∀ {s actions t} → ServerRuns s actions t → FramedRuns s (map server-event actions) t
 framed-server serverDone = frameDone
 framed-server (serverNext {s = s} {a = a} actual rest) = frameNext {event = server-event a} (server-framed a s actual) actual (framed-server rest)
 framed-append : ∀ {s as t bs u} → FramedRuns s as t → FramedRuns t bs u → FramedRuns s (as ++ bs) u
 framed-append frameDone tail = tail
 framed-append (frameNext safe actual rest) tail = frameNext safe actual (framed-append rest tail)
 framed-append (frameRelease actual rest) tail = frameRelease actual (framed-append rest tail)
 transport-frame-components : ∀ {s t} → frame-view t ≡ frame-view s →
   Shared.Certificates isBearerClosed isIOManagerError (T.base s) → Shared.Certificates isBearerClosed isIOManagerError (T.base t)
 transport-frame-components same certificates rewrite cong P.gov same | cong P.bg same | cong P.scopes same = certificates
 framed-monitors : ∀ {start entry current events} → CMEntry start entry → FramedRuns entry events current → ClosedSnapshot start current
 framed-monitors entry path = extend-closed (framed-runs path) (cong P.bg (framed-view path)) (cm-monitors entry)
 framed-components : ∀ {start entry current events} → CMEntry start entry → FramedRuns entry events current → Shared.Certificates isBearerClosed isIOManagerError (T.base current)
 framed-components {entry = entry} {current} certificate path = transport-frame-components {s = entry} {t = current} (framed-view path) (cm-components certificate)

 -- The real physical oracle is unchanged by generalizing the cleanup suffix.
 record FramedCMResultWait (start before after : T.Runtime) : Set where
  constructor framed-cm-result-wait
  field
   entryPoint : T.Runtime
   entry : CMEntry start entryPoint
   events : List T.Event
   cleanup : FramedRuns entryPoint events before
   waited : T.advance (handler-event (W.shutdownStep Shutdown.finishClose)) before ≡ just after
   observed : Handler.PhysicalWait (physical before) (physical after)
 framed-result-wait : ∀ {start entry before after events} → CMEntry start entry → FramedRuns entry events before →
   T.advance (handler-event (W.shutdownStep Shutdown.finishClose)) before ≡ just after → FramedCMResultWait start before after
 framed-result-wait {entry = entry} {before = before} certificate path actual = framed-cm-result-wait entry certificate _ path actual (physical-wait before actual)
 initialized-framed-result-wait : ∀ {c g start prefix callbackBefore callbackAfter entryActions entry before events after} →
   T.initialize c g ≡ just start → T.Runs start prefix callbackBefore → T.advance callback-event callbackBefore ≡ just callbackAfter →
   ServerRuns callbackAfter (entryActions ++ (E.run (A.scope A.beginCM) ∷ [])) entry → FramedRuns entry events before →
   T.advance (handler-event (W.shutdownStep Shutdown.finishClose)) before ≡ just after → FramedCMResultWait start before after
 initialized-framed-result-wait {entryActions = entryActions} init prefix returned entered cleanup actual =
   framed-result-wait (initialized-cm-entry-run {actions = entryActions} init prefix returned entered) cleanup actual
 framed-wait-cleanup : ∀ {start before after} (w : FramedCMResultWait start before after) →
   FramedRuns (FramedCMResultWait.entryPoint w) (FramedCMResultWait.events w ++ (handler-event (W.shutdownStep Shutdown.finishClose) ∷ [])) after
 framed-wait-cleanup {before = before} w = framed-append (FramedCMResultWait.cleanup w)
   (frameNext {event = handler-event (W.shutdownStep Shutdown.finishClose)}
     (server-framed (handler-action (W.shutdownStep Shutdown.finishClose)) before (FramedCMResultWait.waited w))
     (FramedCMResultWait.waited w) frameDone)
 framed-wait-monitors : ∀ {start before after} → FramedCMResultWait start before after → ClosedSnapshot start after
 framed-wait-monitors w = framed-monitors (FramedCMResultWait.entry w) (framed-wait-cleanup w)
 framed-wait-components : ∀ {start before after} → FramedCMResultWait start before after → Shared.Certificates isBearerClosed isIOManagerError (T.base after)
 framed-wait-components w = framed-components (FramedCMResultWait.entry w) (framed-wait-cleanup w)

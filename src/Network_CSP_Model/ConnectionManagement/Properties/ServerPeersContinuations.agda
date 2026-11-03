{-# OPTIONS --guardedness #-}

-- Read and governor continuations, with separate publication and Async evidence.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersContinuations
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (HandleId; JobId; WorkerId; PeerConnectionId)
open import ConnectionManagement.IGTypes using (clean; errored; hot; warm; established)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.ServerPeers as Shared
import ConnectionManagement.Properties.ServerPeersResults as Readers
import ConnectionManagement.Properties.ServerPeersCache as Captures
import ConnectionManagement.MuxPublicationUnwind as Publication
private
  module K = Combined isBearerClosed isIOManagerError
  module C = Context isIOManagerError
  module PS = Supervision isIOManagerError
  module GP = PS.GP
  module N = Publication isBearerClosed

machine : K.State → Sub.Configuration
machine b = PS.machine (K.peers b)
peers : K.State → Peer.Runtime
peers b = C.SubContext.peers (C.subsystem (K.context b))
jobs : K.State → _
jobs b = C.SubContext.jobs (C.subsystem (K.context b))
monitors : K.State → _
monitors b = C.SubContext.monitors (C.subsystem (K.context b))

-- These projections keep the actual guarded lower step, including pool return
-- bookkeeping; no source transition is reconstructed from a desired outcome.
governor-lower : ∀ a s {t} → GP.step (GP.run a) s ≡ just t →
  Σ Policy.State (λ source → GP.Production.step (Policy.dispatch a) (GP.source s) ≡ just source × GP.machine t ≡ Policy.machine source)
governor-lower a s eq with GP.normalPool a s | GP.Production.step (Policy.dispatch a) (GP.source s) in moved
... | just p | just source with GP.noteReturn a (Policy.machine source) p
...   | just returned = case just-injective eq of λ { refl → source , refl , refl }
...   | nothing = case eq of λ ()
governor-lower a s eq | nothing | _ = case eq of λ ()
governor-lower a s eq | just _ | nothing = case eq of λ ()
peer-lower : ∀ a s {t} →
  (∀ before after → PS.noteGovernor (GP.run a) before after ≡ after) → PS.step (PS.run (GP.run a)) s ≡ just t →
  Σ GP.State (λ g → GP.step (GP.run a) (PS.governor s) ≡ just g × PS.machine t ≡ GP.machine g)
peer-lower a s quiet eq with PS.governorAllowed (GP.run a) s
... | false = case eq of λ ()
... | true with GP.step (GP.run a) (PS.governor s) in moved
...   | nothing = case eq of λ ()
...   | just g = case just-injective eq of λ { refl → g , refl , cong PS.machine (quiet s (record s { governor = g })) }
subsystem-lower : ∀ a b {t} →
  (∀ before after → PS.noteGovernor (GP.run a) before after ≡ after) →
  K.step (K.peerStep (PS.run (GP.run a))) b ≡ just t →
  Σ Sub.Configuration (λ next → Sub.advance a (machine b) ≡ just next × machine t ≡ next)
subsystem-lower a b quiet eq with Shared.peer-step isBearerClosed isIOManagerError (PS.run (GP.run a)) b eq
... | p , stepped , same , source with peer-lower a (K.peers b) quiet stepped
...   | g , advanced , sameP with governor-lower a (PS.governor (K.peers b)) advanced
...     | policy , dispatched , sameG with GP.Production.step-projects (Policy.dispatch a) (GP.source (PS.governor (K.peers b))) dispatched
...       | Sub.next moved Sub.done = Policy.machine policy , moved , trans (cong PS.machine same) (trans sameP sameG)

-- Wait continuations can succeed, proceed to release, or await failed demotion.
data WaitPC : J.PC → Set where
  hot-succeeded : WaitPC (J.complete G.succeeded)
  close-release : WaitPC J.callRelease
  failed-demotion : WaitPC (J.awaitCold G.failed)
finished : J.PC → Bool
finished (J.complete G.succeeded) = true
finished J.callRelease = true
finished _ = false
hot-status : Peer.Status → Peer.Status
hot-status Peer.peerHot = Peer.peerWarm
hot-status status = status
success-peer : J.PC → Peer.Status → Peer.Peer → Peer.Peer
success-peer J.awaitHot status p = record p { status = hot-status status; runs = Peer.retireHot (Peer.runs p); promotedAt = nothing }
success-peer _ status p = p
record WaitShape (beforePC : J.PC) (beforeStatus : Peer.Status) (before : J.Frame) (peer : Peer.Peer)
  (after : J.Frame) (world : J.World) : Set where
  constructor shape
  field
    frame : after ≡ record before { pc = J.pc after }
    pc : WaitPC (J.pc after)
    successfulPeer : finished (J.pc after) ≡ true →
      lookup (J.connectionRef before) (J.peers world) ≡ just (success-peer beforePC beforeStatus peer)
hot-shape : ∀ f w p {f′ w′} → J.pc f ≡ J.awaitHot → lookup (J.connectionRef f) (J.peers w) ≡ just p →
  J.step J.observeHot f w ≡ just (f′ , w′) → WaitShape (J.pc f) (Peer.status p) f p f′ w′
hot-shape f w p pcEq found eq rewrite pcEq | found with Peer.all hot (Peer.runs p) | J.peerStep Peer.finishDeactivate f w
... | just clean | just middle with Peer.status p
...   | Peer.peerCold = case just-injective eq of λ { refl → shape refl hot-succeeded (λ _ → lookup-put (J.connectionRef f) (success-peer J.awaitHot Peer.peerCold p) (J.peers middle)) }
...   | Peer.peerCooling = case just-injective eq of λ { refl → shape refl hot-succeeded (λ _ → lookup-put (J.connectionRef f) (success-peer J.awaitHot Peer.peerCooling p) (J.peers middle)) }
...   | Peer.peerWarm = case just-injective eq of λ { refl → shape refl hot-succeeded (λ _ → lookup-put (J.connectionRef f) (success-peer J.awaitHot Peer.peerWarm p) (J.peers middle)) }
...   | Peer.peerHot = case just-injective eq of λ { refl → shape refl hot-succeeded (λ _ → lookup-put (J.connectionRef f) (success-peer J.awaitHot Peer.peerHot p) (J.peers middle)) }
hot-shape f w p pcEq found eq | just (errored err) | just middle = case just-injective eq of λ { refl → shape refl failed-demotion (λ ()) }
hot-shape f w p pcEq found eq | nothing | _ = case eq of λ ()
hot-shape f w p pcEq found eq | just clean | nothing = case eq of λ ()
hot-shape f w p pcEq found eq | just (errored _) | nothing = case eq of λ ()
all-shape : ∀ f w p {f′ w′} → J.pc f ≡ J.awaitAll → lookup (J.connectionRef f) (J.peers w) ≡ just p →
  J.step J.observeAll f w ≡ just (f′ , w′) → WaitShape (J.pc f) (Peer.status p) f p f′ w′
all-shape f w p pcEq found eq rewrite pcEq | found with Peer.all hot (Peer.runs p) | Peer.all warm (Peer.runs p) | Peer.all established (Peer.runs p)
... | just clean | just clean | just clean = case just-injective eq of λ { refl → shape refl close-release (λ _ → found) }
... | just clean | just clean | just (errored _) = case just-injective eq of λ { refl → shape refl failed-demotion (λ ()) }
... | just clean | just (errored _) | just clean = case just-injective eq of λ { refl → shape refl failed-demotion (λ ()) }
... | just clean | just (errored _) | just (errored _) = case just-injective eq of λ { refl → shape refl failed-demotion (λ ()) }
... | just (errored _) | just clean | just clean = case just-injective eq of λ { refl → shape refl failed-demotion (λ ()) }
... | just (errored _) | just clean | just (errored _) = case just-injective eq of λ { refl → shape refl failed-demotion (λ ()) }
... | just (errored _) | just (errored _) | just clean = case just-injective eq of λ { refl → shape refl failed-demotion (λ ()) }
... | just (errored _) | just (errored _) | just (errored _) = case just-injective eq of λ { refl → shape refl failed-demotion (λ ()) }
... | nothing | _ | _ = case eq of λ ()
... | just clean | nothing | _ = case eq of λ ()
... | just (errored _) | nothing | _ = case eq of λ ()
... | just clean | just clean | nothing = case eq of λ ()
... | just clean | just (errored _) | nothing = case eq of λ ()
... | just (errored _) | just clean | nothing = case eq of λ ()
... | just (errored _) | just (errored _) | nothing = case eq of λ ()

-- A quiet shared governor action retains physical monitor bookkeeping while
-- exposing the exact governor transition on the reconstructed shared state.
quiet-governor : ∀ a b {t} →
  (∀ before after → PS.noteGovernor a before after ≡ after) →
  K.step (K.peerStep (PS.run a)) b ≡ just t →
  GP.step a (PS.governor (K.peers b)) ≡ just (PS.governor (K.peers t)) ×
  PS.monitors (K.peers t) ≡ PS.monitors (K.peers b) ×
  PS.monitorPool (K.peers t) ≡ PS.monitorPool (K.peers b)
quiet-governor a b quiet eq with K.peerOpen b ∧ K.peerAllowed (PS.run a) b
... | false = case eq of λ ()
... | true with PS.governorAllowed a (K.peers b)
...   | false = case eq of λ ()
...   | true with GP.step a (PS.governor (K.peers b)) in moved
...     | nothing = case eq of λ ()
...     | just g rewrite quiet (K.peers b) (record (K.peers b) { governor = g }) =
  case just-injective eq of λ { refl → refl , refl , refl }

-- The real governor step records this exact body's return as soon as its
-- resulting job PC is complete. It performs no completion-queue publication.
governor-job-return : ∀ j a s {t} jf result → GP.step (GP.run (Sub.jobStep j a)) s ≡ just t →
  lookup j (Sub.jobs (GP.machine t)) ≡ just jf → J.pc (Sub.execution jf) ≡ J.complete result →
  GP.Pool.step (GP.Pool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool s) ≡ just (GP.pool t)
governor-job-return j a s jf result eq found complete with GP.running j (GP.pool s)
... | false = case eq of λ ()
... | true with GP.Production.step (Policy.dispatch (Sub.jobStep j a)) (GP.source s)
...   | nothing = case eq of λ ()
...   | just source with GP.noteReturn (Sub.jobStep j a) (Policy.machine source) (GP.pool s) in returned
...     | nothing = case eq of λ ()
...     | just pool with just-injective eq
...       | refl rewrite found | complete = returned

-- A returned queued body is still registered and has no Async result yet.
returned-pool : ∀ j result p {q} → GP.Pool.step (GP.Pool.bodyReturnedWith j result) p ≡ just q →
  q ≡ record p { handles = put j (GP.Pool.bodyReturned result) (GP.Pool.handles p) }
returned-pool j result p eq with lookup j (GP.Pool.handles p)
... | just GP.Pool.bodyRunning = just-injective (sym eq)
... | nothing = case eq of λ ()
... | just (GP.Pool.bodyReturned _) = case eq of λ ()
... | just GP.Pool.bodyUnwinding = case eq of λ ()
... | just (GP.Pool.deregisterPending _) = case eq of λ ()
... | just (GP.Pool.deregistered _) = case eq of λ ()
... | just (GP.Pool.resultAvailable _) = case eq of λ ()

-- A raw monitor followup changes no governor pool state, even at complete.
governor-monitor-pool : ∀ ref a s {t} → GP.step (GP.run (Sub.monitorStep ref a)) s ≡ just t → GP.pool t ≡ GP.pool s
governor-monitor-pool ref a s eq with GP.Production.step (Policy.dispatch (Sub.monitorStep ref a)) (GP.source s)
... | nothing = case eq of λ ()
... | just source = case just-injective eq of λ { refl → refl }

-- Actual queued publication selects an already returned body and checks it
-- against the source continuation before appending the captured pool result.
governor-publication : ∀ j delay s {t} → GP.step (GP.run (Sub.enqueueCompletion j delay)) s ≡ just t →
  Σ GP.Body (λ captured → lookup j (GP.Pool.handles (GP.pool s)) ≡ just (GP.Pool.bodyReturned captured) ×
    GP.returnedBody j (GP.machine s) captured ≡ true ×
    GP.Pool.step (GP.Pool.publishCompletion j) (GP.pool s) ≡ just (GP.pool t))
governor-publication j delay s eq with lookup j (GP.Pool.handles (GP.pool s)) in found
... | just (GP.Pool.bodyReturned captured) with GP.returnedBody j (GP.machine s) captured in agrees
...   | false = case eq of λ ()
...   | true with GP.Production.step (Policy.dispatch (Sub.enqueueCompletion j delay)) (GP.source s)
...     | nothing rewrite found = case eq of λ ()
...     | just source rewrite found = case just-injective eq of λ { refl → captured , refl , agrees , refl }
governor-publication j delay s eq | nothing = case eq of λ ()
governor-publication j delay s eq | just GP.Pool.bodyRunning = case eq of λ ()
governor-publication j delay s eq | just GP.Pool.bodyUnwinding = case eq of λ ()
governor-publication j delay s eq | just (GP.Pool.deregisterPending _) = case eq of λ ()
governor-publication j delay s eq | just (GP.Pool.deregistered _) = case eq of λ ()
governor-publication j delay s eq | just (GP.Pool.resultAvailable _) = case eq of λ ()

-- Source and pool queues remain separate: source publication includes delay,
-- whereas the captured body carries the actual operation result.
sub-publication : ∀ j delay c {next} jf result → lookup j (Sub.jobs c) ≡ just jf →
  Sub.queued jf ≡ false → J.pc (Sub.execution jf) ≡ J.complete result →
  Sub.advance (Sub.enqueueCompletion j delay) c ≡ just next →
  Sub.validCompletionDelay (J.work (Sub.execution jf)) result delay ≡ true ×
  lookup j (Sub.jobs next) ≡ just (record jf { queued = true }) ×
  Sub.completions next ≡ Sub.completions c ++ (G.completion (J.work (Sub.execution jf)) result delay ∷ [])
sub-publication j delay c jf result found queued complete eq rewrite found | queued | complete
  with Sub.validCompletionDelay (J.work (Sub.execution jf)) result delay
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl , lookup-put j _ (Sub.jobs c) , refl }

-- WithQueue publication changes only its handle phase and appends the selected
-- captured body; it neither deregisters nor exposes an Async result.
published-pool : ∀ j captured p {q} → lookup j (GP.Pool.handles p) ≡ just (GP.Pool.bodyReturned captured) →
  GP.Pool.step (GP.Pool.publishCompletion j) p ≡ just q →
  q ≡ record p { handles = put j (GP.Pool.deregisterPending GP.Pool.normalExit) (GP.Pool.handles p)
    ; completions = GP.Pool.completions p ++ (captured ∷ []) }
published-pool j captured p found eq rewrite found = just-injective (sym eq)

-- WithoutQueue discards the returned monitor value and proceeds directly to
-- deregistration. Registry membership and Async publication remain separate.
monitor-returned-pool : ∀ tid p {q} → PS.Pool.step (PS.Pool.bodyReturnedWith tid nothing) p ≡ just q →
  q ≡ record p { handles = put tid (PS.Pool.deregisterPending PS.Pool.normalExit) (PS.Pool.handles p) }
monitor-returned-pool tid p eq with lookup tid (PS.Pool.handles p)
... | just PS.Pool.bodyRunning = just-injective (sym eq)
... | nothing = case eq of λ ()
... | just (PS.Pool.bodyReturned _) = case eq of λ ()
... | just PS.Pool.bodyUnwinding = case eq of λ ()
... | just (PS.Pool.deregisterPending _) = case eq of λ ()
... | just (PS.Pool.deregistered _) = case eq of λ ()
... | just (PS.Pool.resultAvailable _) = case eq of λ ()

record MonitorBodyReturn (tid : JobId) (s t : PS.State) : Set where
  constructor monitor-body-return
  field
    thread : PS.Thread
    found : lookup tid (PS.monitors s) ≡ just thread
    ready : PS.pc thread ≡ PS.normalFinishing
    bodyStep : PS.Pool.step (PS.Pool.bodyReturnedWith tid nothing) (PS.monitorPool s) ≡ just (PS.monitorPool t)
    exited : lookup tid (PS.monitors t) ≡ just (record thread { pc = PS.exited })
    pool : PS.monitorPool t ≡ record (PS.monitorPool s)
      { handles = put tid (PS.Pool.deregisterPending PS.Pool.normalExit) (PS.Pool.handles (PS.monitorPool s)) }
physical-monitor-return : ∀ tid s {t} → PS.step (PS.finishMonitor tid) s ≡ just t → MonitorBodyReturn tid s t
physical-monitor-return tid s eq with lookup tid (PS.monitors s) in found
... | nothing = case eq of λ ()
... | just observedThread with PS.pc observedThread in ready | PS.Pool.step (PS.Pool.bodyReturnedWith tid nothing) (PS.monitorPool s) in returned
...   | PS.normalFinishing | just pool = case just-injective eq of λ { refl → monitor-body-return observedThread found ready returned
  (lookup-put tid (record observedThread { pc = PS.exited }) (PS.monitors s)) (monitor-returned-pool tid _ returned) }
...   | PS.normalFinishing | nothing = case eq of λ ()
...   | PS.observing | _ = case eq of λ ()
...   | PS.cancelling | _ = case eq of λ ()
...   | PS.exited | _ = case eq of λ ()
...   | PS.errorWait _ | _ = case eq of λ ()
...   | PS.errorFinishing _ | _ = case eq of λ ()

-- An enabled selection consumes exactly the current FIFO head, after the
-- higher-priority connection monitor has no change to report.
record CompletionSelection (before after : Sub.Configuration) : Set where
  constructor completion-selection
  field
    result : G.Completion
    rest : List G.Completion
    selecting : Sub.pc before ≡ Sub.selecting
    noMonitor : Sub.noMonitor before ≡ true
    fifo : Sub.completions before ≡ result ∷ rest
    state : after ≡ record before { pc = Sub.selectionPC before (Sub.completion result); completions = rest }
select-completion : ∀ c d → Sub.advance Sub.selectCompletion c ≡ just d → CompletionSelection c d
select-completion c d eq with Sub.pc c in chosen | Sub.noMonitor c in idle | Sub.completions c in fifo
... | Sub.selecting | true | result ∷ rest = completion-selection result rest chosen idle fifo (sym (just-injective eq))
... | Sub.selecting | false | _ = case eq of λ ()
... | Sub.selecting | true | [] = case eq of λ ()
... | Sub.publishPublic | _ | _ = case eq of λ ()
... | Sub.sampleInputs | _ | _ = case eq of λ ()
... | Sub.prepareWait | _ | _ = case eq of λ ()
... | Sub.cancelTimer _ | _ | _ = case eq of λ ()
... | Sub.apply _ | _ | _ = case eq of λ ()
... | Sub.publishView _ | _ | _ = case eq of λ ()
... | Sub.traceDecision _ | _ | _ = case eq of λ ()
... | Sub.launch _ | _ | _ = case eq of λ ()
... | Sub.register _ _ | _ | _ = case eq of λ ()
... | Sub.completionAssertionFailed _ | _ | _ = case eq of λ ()

-- Application interprets the captured completion against the actual current
-- private state and application time, with the source assertion left explicit.
data CompletionEffect (time : ℕ) (result : G.Completion) (before after : Sub.Configuration) : Set where
  completion-applied : G.completionAssertion result (Sub.privateState before) ≡ true →
    after ≡ record before { now = time; privateState = G.complete (Sub.maxRetries before) (Sub.clearFailDelay before) time result (Sub.privateState before)
      ; pc = Sub.publishView [] } → CompletionEffect time result before after
  completion-rejected : G.completionAssertion result (Sub.privateState before) ≡ false →
    after ≡ record before { now = time; pc = Sub.completionAssertionFailed result } → CompletionEffect time result before after
record CompletionApplication (time : ℕ) (result : G.Completion) (before after : Sub.Configuration) : Set where
  constructor completion-application
  field
    monotone : Sub.now before ≤ time
    effect : CompletionEffect time result before after
apply-completion : ∀ time result c d → Sub.pc c ≡ Sub.apply (Sub.completion result) →
  Sub.advance (Sub.applyAt time) c ≡ just d → CompletionApplication time result c d
apply-completion time result c d chosen eq rewrite chosen with Sub.now c ≤? time
... | no _ = case eq of λ ()
... | yes later with G.completionAssertion result (Sub.privateState c) in assertion
...   | true = completion-application later (completion-applied assertion (sym (just-injective eq)))
...   | false = completion-application later (completion-rejected assertion (sym (just-injective eq)))

-- Application leaves public state unchanged, including at assertion failure.
application-public : ∀ time result c d → CompletionApplication time result c d → Sub.publicState d ≡ Sub.publicState c
application-public time result c d (completion-application later (completion-applied assertion refl)) = refl
application-public time result c d (completion-application later (completion-rejected assertion refl)) = refl
application-current : ∀ time result c d → CompletionApplication time result c d →
  G.completionAssertion result (Sub.privateState c) ≡ true →
  Sub.privateState d ≡ G.complete (Sub.maxRetries c) (Sub.clearFailDelay c) time result (Sub.privateState c)
application-current time result c d (completion-application later (completion-applied assertion refl)) ok = refl
application-current time result c d (completion-application later (completion-rejected assertion state)) ok = case trans (sym assertion) ok of λ ()
application-rejection : ∀ time result c d → CompletionApplication time result c d →
  G.completionAssertion result (Sub.privateState c) ≡ false →
  Sub.pc d ≡ Sub.completionAssertionFailed result × Sub.privateState d ≡ Sub.privateState c
application-rejection time result c d (completion-application later (completion-rejected assertion refl)) bad = refl , refl
application-rejection time result c d (completion-application later (completion-applied assertion state)) bad = case trans (sym assertion) bad of λ ()

-- A selected live timer must pass its separate cancellation action before the
-- completion can be applied; this step does not update either governor view.
cancel-completion-timer : ∀ result c d → Sub.pc c ≡ Sub.cancelTimer (Sub.completion result) →
  Sub.advance Sub.cancelWakeup c ≡ just d →
  d ≡ record c { pc = Sub.apply (Sub.completion result); wakeupAt = nothing; wakeupReady = false }
cancel-completion-timer result c d chosen eq rewrite chosen = sym (just-injective eq)

-- The public-state write is its own loop boundary, after the previous decision
-- has completed its counter/trace/launch sequence.
record PublicStatePublication (before after : Sub.Configuration) : Set where
  constructor public-state-publication
  field
    ready : Sub.pc before ≡ Sub.publishPublic
    state : after ≡ record before { publicState = Sub.privateState before; pc = Sub.sampleInputs }
publish-public-state : ∀ c d → Sub.advance Sub.publishPublicState c ≡ just d → PublicStatePublication c d
publish-public-state c d eq with Sub.pc c in chosen
... | Sub.publishPublic = public-state-publication chosen (sym (just-injective eq))
... | Sub.sampleInputs = case eq of λ ()
... | Sub.prepareWait = case eq of λ ()
... | Sub.selecting = case eq of λ ()
... | Sub.cancelTimer _ = case eq of λ ()
... | Sub.apply _ = case eq of λ ()
... | Sub.publishView _ = case eq of λ ()
... | Sub.traceDecision _ = case eq of λ ()
... | Sub.launch _ = case eq of λ ()
... | Sub.register _ _ = case eq of λ ()
... | Sub.completionAssertionFailed _ = case eq of λ ()

-- A ready completion excludes lower-priority target/policy/wakeup alternatives.
completion-nonempty : ∀ c result rest → Sub.completions c ≡ result ∷ rest → Sub.noCompletions c ≡ false
completion-nonempty c result rest fifo rewrite fifo = refl
completion-priority : ∀ c d → CompletionSelection c d →
  Sub.advance Sub.selectTargets c ≡ nothing ×
  (∀ picked → Sub.advance (Sub.selectPolicy picked) c ≡ nothing) × Sub.advance Sub.selectWakeup c ≡ nothing
completion-priority c d selected rewrite CompletionSelection.selecting selected | CompletionSelection.noMonitor selected |
  completion-nonempty c (CompletionSelection.result selected) (CompletionSelection.rest selected) (CompletionSelection.fifo selected) =
  refl , (λ _ → refl) , refl

-- These owner operations leave the pool publication ledger untouched. They
-- consume/update the source subsystem only, not a second physical result queue.
data CompletionOwner : Sub.Action → Set where
  owner-select : CompletionOwner Sub.selectCompletion
  owner-apply : ∀ time → CompletionOwner (Sub.applyAt time)
  owner-cancel : CompletionOwner Sub.cancelWakeup
  owner-public : CompletionOwner Sub.publishPublicState
open-owner-pool : GP.State → Maybe GP.Pool.State
open-owner-pool s with GP.ownerOpen (GP.pool s)
... | true = just (GP.pool s)
... | false = nothing
owner-normal : ∀ {a} → CompletionOwner a → ∀ s → GP.normalPool a s ≡ open-owner-pool s
owner-normal owner-select s with GP.ownerOpen (GP.pool s)
... | true = refl
... | false = refl
owner-normal (owner-apply time) s with GP.ownerOpen (GP.pool s)
... | true = refl
... | false = refl
owner-normal owner-cancel s with GP.ownerOpen (GP.pool s)
... | true = refl
... | false = refl
owner-normal owner-public s with GP.ownerOpen (GP.pool s)
... | true = refl
... | false = refl
owner-note : ∀ {a} → CompletionOwner a → ∀ c p → GP.noteReturn a c p ≡ just p
owner-note owner-select c p = refl
owner-note (owner-apply time) c p = refl
owner-note owner-cancel c p = refl
owner-note owner-public c p = refl
governor-owner-pool : ∀ a → CompletionOwner a → ∀ s {t} → GP.step (GP.run a) s ≡ just t →
  GP.ownerOpen (GP.pool s) ≡ true × GP.pool t ≡ GP.pool s
governor-owner-pool a owned s eq rewrite owner-normal owned s
  with GP.ownerOpen (GP.pool s) | GP.Production.step (Policy.dispatch a) (GP.source s)
... | false | _ = case eq of λ ()
... | true | nothing = case eq of λ ()
... | true | just source rewrite owner-note owned (Policy.machine source) (GP.pool s) =
  case just-injective eq of λ { refl → refl , refl }

-- The physical monitor annotation path is also quiet for these owner actions.
quiet-owner : ∀ {a} → CompletionOwner a → ∀ before after → PS.noteGovernor (GP.run a) before after ≡ after
quiet-owner owner-select before after = refl
quiet-owner (owner-apply time) before after = refl
quiet-owner owner-cancel before after = refl
quiet-owner owner-public before after = refl

module Frontend (canInitiate : HandleId → ℕ → Bool) where
  private
    module T = K.Protocols canInitiate
    module Read = Readers.Observations isBearerClosed isIOManagerError canInitiate
    module Physical = Captures.Frontend isBearerClosed isIOManagerError canInitiate
  Waiting : J.Frame → Set
  Waiting f = J.pc f ≡ J.awaitHot ⊎ J.pc f ≡ J.awaitAll
  waiting : ∀ f p s results → T.waitResults f p s ≡ just results → Waiting f
  waiting f p s results eq with J.pc f
  ... | J.awaitHot = inj₁ refl
  ... | J.awaitAll = inj₂ refl
  ... | J.begin = case eq of λ ()
  ... | J.awaitAcquire = case eq of λ ()
  ... | J.startBundle _ _ = case eq of λ ()
  ... | J.publishBundle _ = case eq of λ ()
  ... | J.markWarm = case eq of λ ()
  ... | J.forkMonitor = case eq of λ ()
  ... | J.finishActivation = case eq of λ ()
  ... | J.callRelease = case eq of λ ()
  ... | J.awaitRelease = case eq of λ ()
  ... | J.delayFailure = case eq of λ ()
  ... | J.awaitCold _ = case eq of λ ()
  ... | J.complete _ = case eq of λ ()
  ... | J.acquirePolicy _ = case eq of λ ()
  ... | J.nodeDelivery _ = case eq of λ ()
  ... | J.nodeRethrow _ = case eq of λ ()
  wait-hot-action : ∀ f → J.pc f ≡ J.awaitHot → T.waitAction f ≡ J.observeHot
  wait-hot-action f eq rewrite eq = refl
  wait-all-action : ∀ f → J.pc f ≡ J.awaitAll → T.waitAction f ≡ J.observeAll
  wait-all-action f eq rewrite eq = refl
  wait-shape : ∀ f w p {f′ w′} → Waiting f → lookup (J.connectionRef f) (J.peers w) ≡ just p →
    J.step (T.waitAction f) f w ≡ just (f′ , w′) → WaitShape (J.pc f) (Peer.status p) f p f′ w′
  wait-shape f w p {f′} {w′} (inj₁ pcEq) found eq = hot-shape f w p pcEq found
    (subst (λ a → J.step a f w ≡ just (f′ , w′)) (wait-hot-action f pcEq) eq)
  wait-shape f w p {f′} {w′} (inj₂ pcEq) found eq = all-shape f w p pcEq found
    (subst (λ a → J.step a f w ≡ just (f′ , w′)) (wait-all-action f pcEq) eq)

  -- Actual inherited peer work cannot rewrite the physical protocol-job table.
  protocol-jobs : T.Runtime → _
  protocol-jobs s = N.P.jobs (T.physical (T.base s))
  peer-job-table : ∀ a b {t} → K.step (K.peerStep a) b ≡ just t →
    N.P.jobs (T.physical t) ≡ N.P.jobs (T.physical b)
  peer-job-table a b eq with K.peerOpen b ∧ K.peerAllowed a b
  ... | false = case eq of λ ()
  ... | true with PS.step a (K.peers b)
  ...   | nothing = case eq of λ ()
  ...   | just p = case just-injective eq of λ { refl → refl }
  record FailureEffects (s t : T.Runtime) : Set where
    constructor failure-effects
    field
      source : T.sourceOf t ≡ T.sourceOf s
      physical : T.physical (T.base t) ≡ T.physical (T.base s)
      frontend : T.front t ≡ T.front s
      server : K.server (T.base t) ≡ K.server (T.base s)
      monitorThreads : C.monitors (K.context (T.base t)) ≡ C.monitors (K.context (T.base s))
      governorPool : C.governorPool (K.context (T.base t)) ≡ C.governorPool (K.context (T.base s))
      monitorPool : C.monitorPool (K.context (T.base t)) ≡ C.monitorPool (K.context (T.base s))
      scopes : C.scopes (K.context (T.base t)) ≡ C.scopes (K.context (T.base s))

  -- Extract each real updated row from a successful raw subsystem transition.
  sub-job : ∀ j a c jf {next} → lookup j (Sub.jobs c) ≡ just jf → Sub.advance (Sub.jobStep j a) c ≡ just next →
    Σ J.Frame (λ f′ → Σ J.World (λ w′ → J.step a (Sub.execution jf) (Sub.world c) ≡ just (f′ , w′) ×
      lookup j (Sub.jobs next) ≡ just (record jf { execution = f′ }) × J.peers (Sub.world next) ≡ J.peers w′))
  sub-job j a c (Sub.jobFrame f queued deregistered) found eq rewrite found with queued | J.step a f (Sub.world c)
  ... | false | just (f′ , w′) = case just-injective eq of λ { refl → f′ , w′ , refl , lookup-put j (Sub.jobFrame f′ false deregistered) (Sub.jobs c) , refl }
  ... | true | _ = case eq of λ ()
  ... | false | nothing = case eq of λ ()
  sub-monitor : ∀ ref a c f {next} → lookup ref (Sub.monitors c) ≡ just f → Sub.advance (Sub.monitorStep ref a) c ≡ just next →
    Σ J.Frame (λ f′ → Σ J.World (λ w′ → J.step a f (Sub.world c) ≡ just (f′ , w′) ×
      lookup ref (Sub.monitors next) ≡ just f′ × J.peers (Sub.world next) ≡ J.peers w′))
  sub-monitor ref a c f found eq rewrite found with J.step a f (Sub.world c)
  ... | just (f′ , w′) = case just-injective eq of λ { refl → f′ , w′ , refl , lookup-put ref f′ (Sub.monitors c) , refl }
  ... | nothing = case eq of λ ()
  record ForwardedJob (j : JobId) (jf : Sub.JobFrame) (p : Peer.Peer) (s t : T.Runtime) : Set where
    constructor forwarded-job
    field
      afterFrame : J.Frame
      afterWorld : J.World
      inherited : K.step (K.peerStep (PS.run (GP.run (Sub.jobStep j (T.waitAction (Sub.execution jf)))))) (T.base s) ≡ just (T.base t)
      logical : J.step (T.waitAction (Sub.execution jf)) (Sub.execution jf) (Sub.world (machine (T.base s))) ≡ just (afterFrame , afterWorld)
      afterJob : lookup j (jobs (T.base t)) ≡ just (record jf { execution = afterFrame })
      afterPeers : peers (T.base t) ≡ J.peers afterWorld
      continuation : WaitShape (J.pc (Sub.execution jf)) (Peer.status p) (Sub.execution jf) p afterFrame afterWorld
      sameFront : T.front t ≡ T.front s
      sameProtocolJobs : protocol-jobs t ≡ protocol-jobs s
  forward-job : ∀ j jf p s t → Waiting (Sub.execution jf) → lookup j (jobs (T.base s)) ≡ just jf →
    lookup (J.connectionRef (Sub.execution jf)) (peers (T.base s)) ≡ just p →
    K.step (K.peerStep (PS.run (GP.run (Sub.jobStep j (T.waitAction (Sub.execution jf)))))) (T.base s) ≡ just (T.base t) →
    T.front t ≡ T.front s → ForwardedJob j jf p s t
  forward-job j jf p s t ready found peerFound moved sameFront with subsystem-lower
    (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s) (λ _ _ → refl) moved
  ... | next , advanced , same with sub-job j (T.waitAction (Sub.execution jf)) (machine (T.base s)) jf found advanced
  ...   | f′ , w′ , logical , afterJob , afterPeers = forwarded-job f′ w′ moved logical
    (trans (cong (λ c → lookup j (Sub.jobs c)) same) afterJob)
    (trans (cong (λ c → J.peers (Sub.world c)) same) afterPeers)
    (wait-shape (Sub.execution jf) (Sub.world (machine (T.base s))) p ready peerFound logical) sameFront (peer-job-table _ (T.base s) moved)
  record ForwardedMonitor (ref : PeerConnectionId) (f : J.Frame) (p : Peer.Peer) (s t : T.Runtime) : Set where
    constructor forwarded-monitor
    field
      afterFrame : J.Frame
      afterWorld : J.World
      inherited : K.step (K.peerStep (PS.run (GP.run (Sub.monitorStep ref (T.waitAction f))))) (T.base s) ≡ just (T.base t)
      logical : J.step (T.waitAction f) f (Sub.world (machine (T.base s))) ≡ just (afterFrame , afterWorld)
      afterMonitor : lookup ref (monitors (T.base t)) ≡ just afterFrame
      afterPeers : peers (T.base t) ≡ J.peers afterWorld
      continuation : WaitShape (J.pc f) (Peer.status p) f p afterFrame afterWorld
      sameFront : T.front t ≡ T.front s
      sameProtocolJobs : protocol-jobs t ≡ protocol-jobs s
  forward-monitor : ∀ ref f p s t → Waiting f → lookup ref (monitors (T.base s)) ≡ just f →
    lookup (J.connectionRef f) (peers (T.base s)) ≡ just p →
    K.step (K.peerStep (PS.run (GP.run (Sub.monitorStep ref (T.waitAction f))))) (T.base s) ≡ just (T.base t) →
    T.front t ≡ T.front s → ForwardedMonitor ref f p s t
  forward-monitor ref f p s t ready found peerFound moved sameFront with subsystem-lower
    (Sub.monitorStep ref (T.waitAction f)) (T.base s) (λ _ _ → refl) moved
  ... | next , advanced , same with sub-monitor ref (T.waitAction f) (machine (T.base s)) f found advanced
  ...   | f′ , w′ , logical , afterMonitor , afterPeers = forwarded-monitor f′ w′ moved logical
    (trans (cong (λ c → lookup ref (Sub.monitors c)) same) afterMonitor)
    (trans (cong (λ c → J.peers (Sub.world c)) same) afterPeers)
    (wait-shape f (Sub.world (machine (T.base s))) p ready peerFound logical) sameFront (peer-job-table _ (T.base s) moved)

  -- The two plan decisions are proved from all original selector guards.
  job-decision : JobId → Sub.JobFrame → Peer.Peer → T.Runtime → Bool → T.Plan
  job-decision j jf p s true = T.inherit (K.peerStep (PS.run (GP.run (Sub.jobStep j (T.waitAction (Sub.execution jf)))))) (T.front s)
  job-decision j jf p s false = T.reading (record (T.readStateOf (T.base s))
    { peerRows = put (J.connectionRef (Sub.execution jf)) (T.failedPeer (Sub.execution jf) p) (peers (T.base s))
    ; jobRows = put j (record jf { execution = T.failedFrame (Sub.execution jf) }) (jobs (T.base s)) })
  job-selection : ∀ j jf p s results → lookup j (jobs (T.base s)) ≡ just jf → Sub.queued jf ≡ false →
    lookup (J.connectionRef (Sub.execution jf)) (peers (T.base s)) ≡ just p →
    T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s) ≡ true →
    T.waitResults (Sub.execution jf) p s ≡ just results → T.choose (T.waitJobResults j) s ≡ just (job-decision j jf p s (T.allClean results))
  job-selection j jf p s results found queued peerFound allowed selected rewrite found | queued | peerFound | allowed | selected with T.allClean results
  ... | true = refl
  ... | false = refl
  monitor-decision : PeerConnectionId → J.Frame → Peer.Peer → T.Runtime → Bool → T.Plan
  monitor-decision ref f p s true = T.inherit (K.peerStep (PS.run (GP.run (Sub.monitorStep ref (T.waitAction f))))) (T.front s)
  monitor-decision ref f p s false = T.reading (record (T.readStateOf (T.base s))
    { peerRows = put (J.connectionRef f) (T.failedPeer f p) (peers (T.base s))
    ; followups = put ref (T.failedFrame f) (monitors (T.base s)) })
  monitor-selection : ∀ ref f p s results → lookup ref (monitors (T.base s)) ≡ just f →
    lookup (J.connectionRef f) (peers (T.base s)) ≡ just p →
    T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s) ≡ true →
    T.waitResults f p s ≡ just results → T.choose (T.waitMonitorResults ref) s ≡ just (monitor-decision ref f p s (T.allClean results))
  monitor-selection ref f p s results found peerFound allowed selected rewrite found | peerFound | allowed | selected with T.allClean results
  ... | true = refl
  ... | false = refl
  on-choice : ∀ a s plan {t} → T.choose a s ≡ just plan → T.advance a s ≡ just t → T.enact plan s ≡ just t
  on-choice a s plan chosen advanced rewrite chosen = advanced
  data JobOutcome (j : JobId) (jf : Sub.JobFrame) (p : Peer.Peer) (results : List (ℕ × T.Observation)) (s t : T.Runtime) : Set where
    job-failed : T.allClean results ≡ false →
      lookup j (jobs (T.base t)) ≡ just (record jf { execution = T.failedFrame (Sub.execution jf) }) →
      lookup (J.connectionRef (Sub.execution jf)) (peers (T.base t)) ≡ just (T.failedPeer (Sub.execution jf) p) →
      FailureEffects s t → JobOutcome j jf p results s t
    job-forwarded : T.allClean results ≡ true → ForwardedJob j jf p s t → JobOutcome j jf p results s t
  job-outcome : ∀ j jf p s {t} results → lookup j (jobs (T.base s)) ≡ just jf → Sub.queued jf ≡ false →
    lookup (J.connectionRef (Sub.execution jf)) (peers (T.base s)) ≡ just p →
    T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s) ≡ true →
    T.waitResults (Sub.execution jf) p s ≡ just results → T.advance (T.waitJobResults j) s ≡ just t → JobOutcome j jf p results s t
  job-outcome j jf p s {t} results found queued peerFound allowed selected advanced with T.allClean results in decision |
    on-choice (T.waitJobResults j) s (job-decision j jf p s (T.allClean results))
      (job-selection j jf p s results found queued peerFound allowed selected) advanced
  ... | false | enacted = case just-injective enacted of λ { refl → job-failed decision (lookup-put j _ (jobs (T.base s)))
    (lookup-put (J.connectionRef (Sub.execution jf)) _ (peers (T.base s))) (failure-effects refl refl refl refl refl refl refl refl) }
  ... | true | enacted with K.step (K.peerStep (PS.run (GP.run (Sub.jobStep j (T.waitAction (Sub.execution jf)))))) (T.base s) in moved
  ...   | nothing = case enacted of λ ()
  ...   | just b = case just-injective enacted of λ { refl → job-forwarded decision
    (forward-job j jf p s _ (waiting (Sub.execution jf) p s results selected) found peerFound moved refl) }
  data MonitorOutcome (ref : PeerConnectionId) (f : J.Frame) (p : Peer.Peer) (results : List (ℕ × T.Observation)) (s t : T.Runtime) : Set where
    monitor-failed : T.allClean results ≡ false → lookup ref (monitors (T.base t)) ≡ just (T.failedFrame f) →
      lookup (J.connectionRef f) (peers (T.base t)) ≡ just (T.failedPeer f p) → FailureEffects s t → MonitorOutcome ref f p results s t
    monitor-forwarded : T.allClean results ≡ true → ForwardedMonitor ref f p s t → MonitorOutcome ref f p results s t
  monitor-outcome : ∀ ref f p s {t} results → lookup ref (monitors (T.base s)) ≡ just f →
    lookup (J.connectionRef f) (peers (T.base s)) ≡ just p →
    T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s) ≡ true →
    T.waitResults f p s ≡ just results → T.advance (T.waitMonitorResults ref) s ≡ just t → MonitorOutcome ref f p results s t
  monitor-outcome ref f p s {t} results found peerFound allowed selected advanced with T.allClean results in decision |
    on-choice (T.waitMonitorResults ref) s (monitor-decision ref f p s (T.allClean results))
      (monitor-selection ref f p s results found peerFound allowed selected) advanced
  ... | false | enacted = case just-injective enacted of λ { refl → monitor-failed decision (lookup-put ref _ (monitors (T.base s)))
    (lookup-put (J.connectionRef f) _ (peers (T.base s))) (failure-effects refl refl refl refl refl refl refl refl) }
  ... | true | enacted with K.step (K.peerStep (PS.run (GP.run (Sub.monitorStep ref (T.waitAction f))))) (T.base s) in moved
  ...   | nothing = case enacted of λ ()
  ...   | just b = case just-injective enacted of λ { refl → monitor-forwarded decision
    (forward-monitor ref f p s _ (waiting f p s results selected) found peerFound moved refl) }

  -- Physical failures cool active peers without launching a logical followup.
  Active : Peer.Peer → Set
  Active p = Peer.status p ≡ Peer.peerWarm ⊎ Peer.status p ≡ Peer.peerHot
  cool-active : ∀ p → Active p → Peer.status (Peer.cool p) ≡ Peer.peerCooling
  cool-active p (inj₁ eq) rewrite eq = refl
  cool-active p (inj₂ eq) rewrite eq = refl
  data PollCause (ref : PeerConnectionId) (p : Peer.Peer) (s : T.Runtime) : Set where
    cold-path : Peer.status p ≡ Peer.peerCold → lookup ref (monitors (T.base s)) ≡ nothing → PollCause ref p s
    cooling-path : Peer.status p ≡ Peer.peerCooling → lookup ref (monitors (T.base s)) ≡ nothing → PollCause ref p s
    followup-path : ∀ f → lookup ref (monitors (T.base s)) ≡ just f → PollCause ref p s
    clean-path : ∀ kind observation → Active p → lookup ref (monitors (T.base s)) ≡ nothing →
      T.firstPeer ref p s ≡ just (kind , observation) → T.cleanObservation observation ≡ true → PollCause ref p s
  data PollChoice (ref : PeerConnectionId) (w : WorkerId) (s : T.Runtime) : T.Plan → Set where
    poll-inherit : ∀ p → lookup ref (peers (T.base s)) ≡ just p → PollCause ref p s →
      PollChoice ref w s (T.inherit (K.peerStep (PS.run (GP.run (Sub.pollPeer ref w)))) (T.front s))
    poll-read : ∀ p kind observation → lookup ref (peers (T.base s)) ≡ just p → Active p →
      T.firstPeer ref p s ≡ just (kind , observation) → T.cleanObservation observation ≡ false →
      PollChoice ref w s (T.reading (record (T.readStateOf (T.base s)) { peerRows = put ref (Peer.cool p) (peers (T.base s)) }))
  poll-choice : ∀ ref w s plan → T.pollResultsPlan ref w s ≡ just plan → PollChoice ref w s plan
  poll-choice ref w s plan eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
    lookup ref (peers (T.base s)) in found | lookup ref (monitors (T.base s)) in monitored
  ... | true | just p | nothing with Peer.status p in status
  ...   | Peer.peerCold = case just-injective eq of λ { refl → poll-inherit p found (cold-path status monitored) }
  ...   | Peer.peerCooling = case just-injective eq of λ { refl → poll-inherit p found (cooling-path status monitored) }
  ...   | Peer.peerWarm with T.firstPeer ref p s in selected
  ...     | nothing = case eq of λ ()
  ...     | just (kind , observation) with T.cleanObservation observation in decision
  ...       | true = case just-injective eq of λ { refl → poll-inherit p found (clean-path kind observation (inj₁ status) monitored selected decision) }
  ...       | false = case just-injective eq of λ { refl → poll-read p kind observation found (inj₁ status) selected decision }
  poll-choice ref w s plan eq | true | just p | nothing | Peer.peerHot with T.firstPeer ref p s in selected
  ... | nothing = case eq of λ ()
  ... | just (kind , observation) with T.cleanObservation observation in decision
  ...   | true = case just-injective eq of λ { refl → poll-inherit p found (clean-path kind observation (inj₂ status) monitored selected decision) }
  ...   | false = case just-injective eq of λ { refl → poll-read p kind observation found (inj₂ status) selected decision }
  poll-choice ref w s plan eq | true | just p | just f = case just-injective eq of λ { refl → poll-inherit p found (followup-path f monitored) }
  poll-choice ref w s plan eq | false | _ | _ = case eq of λ ()
  poll-choice ref w s plan eq | true | nothing | _ = case eq of λ ()
  data PollOutcome (ref : PeerConnectionId) (w : WorkerId) (s t : T.Runtime) : Set where
    poll-forwarded : ∀ p → lookup ref (peers (T.base s)) ≡ just p → PollCause ref p s →
      K.step (K.peerStep (PS.run (GP.run (Sub.pollPeer ref w)))) (T.base s) ≡ just (T.base t) →
      T.front t ≡ T.front s → protocol-jobs t ≡ protocol-jobs s → PollOutcome ref w s t
    poll-failed : ∀ p kind observation → lookup ref (peers (T.base s)) ≡ just p → Active p →
      T.firstPeer ref p s ≡ just (kind , observation) → T.cleanObservation observation ≡ false →
      lookup ref (peers (T.base t)) ≡ just (Peer.cool p) →
      jobs (T.base t) ≡ jobs (T.base s) → monitors (T.base t) ≡ monitors (T.base s) →
      FailureEffects s t → PollOutcome ref w s t
  poll-outcome : ∀ ref w s {t} → T.advance (T.pollResults ref w) s ≡ just t → PollOutcome ref w s t
  poll-outcome ref w s {t} advanced with T.pollResultsPlan ref w s in selected
  ... | nothing = case advanced of λ ()
  ... | just plan with poll-choice ref w s plan selected
  ...   | poll-read p kind observation found active chosen bad = case just-injective advanced of λ { refl →
    poll-failed p kind observation found active chosen bad (lookup-put ref _ (peers (T.base s))) refl refl (failure-effects refl refl refl refl refl refl refl refl) }
  ...   | poll-inherit p found cause with K.step (K.peerStep (PS.run (GP.run (Sub.pollPeer ref w)))) (T.base s) in moved
  ...     | nothing = case advanced of λ ()
  ...     | just b = case just-injective advanced of λ { refl → poll-forwarded p found cause moved refl (peer-job-table _ (T.base s) moved) }

  -- Public initialized agreements retain all physical observation certificates.
  record JobAgreement (j : JobId) (s t : T.Runtime) : Set where
    constructor job-agreement
    field
      observations : Physical.PhysicalJobWait j s
      outcome : JobOutcome j (Read.JobRead.frame (Physical.PhysicalJobWait.reader observations))
        (Read.JobRead.peer (Physical.PhysicalJobWait.reader observations)) (Read.JobRead.results (Physical.PhysicalJobWait.reader observations)) s t
  record MonitorAgreement (ref : PeerConnectionId) (s t : T.Runtime) : Set where
    constructor monitor-agreement
    field
      observations : Physical.PhysicalMonitorWait ref s
      outcome : MonitorOutcome ref (Read.MonitorRead.frame (Physical.PhysicalMonitorWait.reader observations))
        (Read.MonitorRead.peer (Physical.PhysicalMonitorWait.reader observations)) (Read.MonitorRead.results (Physical.PhysicalMonitorWait.reader observations)) s t
  record PollAgreement (ref : PeerConnectionId) (w : WorkerId) (s t : T.Runtime) : Set where
    constructor poll-agreement
    field
      observations : Physical.PhysicalPoll ref w s
      outcome : PollOutcome ref w s t
  initialized-job-agreement : ∀ {c g start as s t} j → T.initialize c g ≡ just start → T.Runs start as s →
    T.advance (T.waitJobResults j) s ≡ just t → JobAgreement j s t
  initialized-job-agreement j initialized path advanced = job-agreement observations
    (job-outcome j (Read.JobRead.frame reader) (Read.JobRead.peer reader) _ (Read.JobRead.results reader)
      (Read.JobRead.foundJob reader) (Read.JobRead.notQueued reader) (Read.JobRead.foundPeer reader)
      (Read.JobRead.allowed reader) (Read.JobRead.selected reader) advanced)
    where
    observations = Physical.initialized-physical-job-wait j initialized path advanced
    reader = Physical.PhysicalJobWait.reader observations
  initialized-monitor-agreement : ∀ {c g start as s t} ref → T.initialize c g ≡ just start → T.Runs start as s →
    T.advance (T.waitMonitorResults ref) s ≡ just t → MonitorAgreement ref s t
  initialized-monitor-agreement ref initialized path advanced = monitor-agreement observations
    (monitor-outcome ref (Read.MonitorRead.frame reader) (Read.MonitorRead.peer reader) _ (Read.MonitorRead.results reader)
      (Read.MonitorRead.foundMonitor reader) (Read.MonitorRead.foundPeer reader)
      (Read.MonitorRead.allowed reader) (Read.MonitorRead.selected reader) advanced)
    where
    observations = Physical.initialized-physical-monitor-wait ref initialized path advanced
    reader = Physical.PhysicalMonitorWait.reader observations
  initialized-poll-agreement : ∀ {c g start as s t} ref w → T.initialize c g ≡ just start → T.Runs start as s →
    T.advance (T.pollResults ref w) s ≡ just t → PollAgreement ref w s t
  initialized-poll-agreement ref w initialized path advanced = poll-agreement
    (Physical.initialized-physical-poll ref w initialized path advanced) (poll-outcome ref w _ advanced)

  -- A completed operation or release continuation cannot come from a failed
  -- physical read. Clean observations alone do not assert that it completes.
  job-success-clean : ∀ j s t (agreement : JobAgreement j s t) jf → lookup j (jobs (T.base t)) ≡ just jf →
    finished (J.pc (Sub.execution jf)) ≡ true →
    T.allClean (Read.JobRead.results (Physical.PhysicalJobWait.reader (JobAgreement.observations agreement))) ≡ true
  job-success-clean j s t (job-agreement observations (job-forwarded decision forwarded)) jf found succeeded = decision
  job-success-clean j s t (job-agreement observations (job-failed decision afterJob afterPeer effects)) jf found succeeded
    with just-injective (trans (sym afterJob) found)
  ... | refl = case succeeded of λ ()
  monitor-success-clean : ∀ ref s t (agreement : MonitorAgreement ref s t) f → lookup ref (monitors (T.base t)) ≡ just f →
    finished (J.pc f) ≡ true →
    T.allClean (Read.MonitorRead.results (Physical.PhysicalMonitorWait.reader (MonitorAgreement.observations agreement))) ≡ true
  monitor-success-clean ref s t (monitor-agreement observations (monitor-forwarded decision forwarded)) f found succeeded = decision
  monitor-success-clean ref s t (monitor-agreement observations (monitor-failed decision afterMonitor afterPeer effects)) f found succeeded
    with just-injective (trans (sym afterMonitor) found)
  ... | refl = case succeeded of λ ()
  captured-clean : ∀ s ref p (results : List (ℕ × T.Observation)) → T.allClean results ≡ true →
    All (λ { (n , observation) → Physical.PhysicalObservation s ref p n observation }) results →
    All (λ { (n , observation) → Physical.Historical s ref (Peer.handleRef p) (Peer.muxRef p) n clean }) results
  captured-clean s ref p [] eq [] = []
  captured-clean s ref p ((n , T.localResult clean) ∷ results) eq ((Physical.local-capture .clean history) ∷ rest) =
    history ∷ captured-clean s ref p results eq rest
  captured-clean s ref p ((n , T.localResult (errored err)) ∷ results) () evidence
  captured-clean s ref p ((n , T.shutdownResult status) ∷ results) () evidence

  -- Successful wait continuations have every observed protocol result clean,
  -- with the original historical physical captures still attached.
  job-reader : ∀ {j s t} → JobAgreement j s t → Read.JobRead j s
  job-reader agreement = Physical.PhysicalJobWait.reader (JobAgreement.observations agreement)
  monitor-reader : ∀ {ref s t} → MonitorAgreement ref s t → Read.MonitorRead ref s
  monitor-reader agreement = Physical.PhysicalMonitorWait.reader (MonitorAgreement.observations agreement)
  job-success-captures : ∀ j s t (agreement : JobAgreement j s t) jf → lookup j (jobs (T.base t)) ≡ just jf →
    finished (J.pc (Sub.execution jf)) ≡ true → All (λ { (n , observation) → Physical.Historical s
      (J.connectionRef (Sub.execution (Read.JobRead.frame (job-reader agreement))))
      (Peer.handleRef (Read.JobRead.peer (job-reader agreement))) (Peer.muxRef (Read.JobRead.peer (job-reader agreement))) n clean })
      (Read.JobRead.results (job-reader agreement))
  job-success-captures j s t agreement jf found succeeded = captured-clean s _ _ _
    (job-success-clean j s t agreement jf found succeeded) (Physical.PhysicalJobWait.backing (JobAgreement.observations agreement))
  monitor-success-captures : ∀ ref s t (agreement : MonitorAgreement ref s t) f → lookup ref (monitors (T.base t)) ≡ just f →
    finished (J.pc f) ≡ true → All (λ { (n , observation) → Physical.Historical s
      (J.connectionRef (Read.MonitorRead.frame (monitor-reader agreement)))
      (Peer.handleRef (Read.MonitorRead.peer (monitor-reader agreement))) (Peer.muxRef (Read.MonitorRead.peer (monitor-reader agreement))) n clean })
      (Read.MonitorRead.results (monitor-reader agreement))
  monitor-success-captures ref s t agreement f found succeeded = captured-clean s _ _ _
    (monitor-success-clean ref s t agreement f found succeeded) (Physical.PhysicalMonitorWait.backing (MonitorAgreement.observations agreement))
  job-success-peer : ∀ j s t (agreement : JobAgreement j s t) jf → lookup j (jobs (T.base t)) ≡ just jf →
    finished (J.pc (Sub.execution jf)) ≡ true →
    lookup (J.connectionRef (Sub.execution (Read.JobRead.frame (job-reader agreement)))) (peers (T.base t)) ≡ just
      (success-peer (J.pc (Sub.execution (Read.JobRead.frame (job-reader agreement))))
        (Peer.status (Read.JobRead.peer (job-reader agreement))) (Read.JobRead.peer (job-reader agreement)))
  job-success-peer j s t (job-agreement observations (job-forwarded decision forwarded)) jf found succeeded
    with just-injective (trans (sym (ForwardedJob.afterJob forwarded)) found)
  ... | refl = trans (cong (lookup _) (ForwardedJob.afterPeers forwarded)) (WaitShape.successfulPeer (ForwardedJob.continuation forwarded) succeeded)
  job-success-peer j s t (job-agreement observations (job-failed decision afterJob afterPeer effects)) jf found succeeded
    with just-injective (trans (sym afterJob) found)
  ... | refl = case succeeded of λ ()
  monitor-success-peer : ∀ ref s t (agreement : MonitorAgreement ref s t) f → lookup ref (monitors (T.base t)) ≡ just f →
    finished (J.pc f) ≡ true → lookup (J.connectionRef (Read.MonitorRead.frame (monitor-reader agreement))) (peers (T.base t)) ≡ just
      (success-peer (J.pc (Read.MonitorRead.frame (monitor-reader agreement)))
        (Peer.status (Read.MonitorRead.peer (monitor-reader agreement))) (Read.MonitorRead.peer (monitor-reader agreement)))
  monitor-success-peer ref s t (monitor-agreement observations (monitor-forwarded decision forwarded)) f found succeeded
    with just-injective (trans (sym (ForwardedMonitor.afterMonitor forwarded)) found)
  ... | refl = trans (cong (lookup _) (ForwardedMonitor.afterPeers forwarded)) (WaitShape.successfulPeer (ForwardedMonitor.continuation forwarded) succeeded)
  monitor-success-peer ref s t (monitor-agreement observations (monitor-failed decision afterMonitor afterPeer effects)) f found succeeded
    with just-injective (trans (sym afterMonitor) found)
  ... | refl = case succeeded of λ ()

  -- Failure consumers can inspect the exact next row and unchanged resources
  -- without unfolding an initialized reader certificate.
  job-nonclean : ∀ j s t (agreement : JobAgreement j s t) →
    T.allClean (Read.JobRead.results (job-reader agreement)) ≡ false →
    lookup j (jobs (T.base t)) ≡ just (record (Read.JobRead.frame (job-reader agreement))
      { execution = T.failedFrame (Sub.execution (Read.JobRead.frame (job-reader agreement))) }) ×
    lookup (J.connectionRef (Sub.execution (Read.JobRead.frame (job-reader agreement)))) (peers (T.base t)) ≡
      just (T.failedPeer (Sub.execution (Read.JobRead.frame (job-reader agreement))) (Read.JobRead.peer (job-reader agreement))) × FailureEffects s t
  job-nonclean j s t (job-agreement observations (job-failed decision afterJob afterPeer effects)) bad = afterJob , afterPeer , effects
  job-nonclean j s t (job-agreement observations (job-forwarded decision forwarded)) bad = case trans (sym decision) bad of λ ()
  monitor-nonclean : ∀ ref s t (agreement : MonitorAgreement ref s t) →
    T.allClean (Read.MonitorRead.results (monitor-reader agreement)) ≡ false →
    lookup ref (monitors (T.base t)) ≡ just (T.failedFrame (Read.MonitorRead.frame (monitor-reader agreement))) ×
    lookup (J.connectionRef (Read.MonitorRead.frame (monitor-reader agreement))) (peers (T.base t)) ≡
      just (T.failedPeer (Read.MonitorRead.frame (monitor-reader agreement)) (Read.MonitorRead.peer (monitor-reader agreement))) × FailureEffects s t
  monitor-nonclean ref s t (monitor-agreement observations (monitor-failed decision afterMonitor afterPeer effects)) bad = afterMonitor , afterPeer , effects
  monitor-nonclean ref s t (monitor-agreement observations (monitor-forwarded decision forwarded)) bad = case trans (sym decision) bad of λ ()

  active-inactive : ∀ p → Active p → (Peer.status p ≡ Peer.peerCold ⊎ Peer.status p ≡ Peer.peerCooling) → ⊥
  active-inactive p (inj₁ warmEq) (inj₁ coldEq) = case trans (sym warmEq) coldEq of λ ()
  active-inactive p (inj₁ warmEq) (inj₂ coolingEq) = case trans (sym warmEq) coolingEq of λ ()
  active-inactive p (inj₂ hotEq) (inj₁ coldEq) = case trans (sym hotEq) coldEq of λ ()
  active-inactive p (inj₂ hotEq) (inj₂ coolingEq) = case trans (sym hotEq) coolingEq of λ ()
  poll-nonclean : ∀ ref w s t (agreement : PollAgreement ref w s t) p kind observation →
    lookup ref (peers (T.base s)) ≡ just p → Active p → lookup ref (monitors (T.base s)) ≡ nothing →
    T.firstPeer ref p s ≡ just (kind , observation) → T.cleanObservation observation ≡ false →
    lookup ref (peers (T.base t)) ≡ just (Peer.cool p) ×
    monitors (T.base t) ≡ monitors (T.base s) × jobs (T.base t) ≡ jobs (T.base s) × FailureEffects s t
  poll-nonclean ref w s t (poll-agreement observations (poll-failed old kind′ observation′ foundOld activeOld selectedOld badOld afterPeer sameJobs sameMonitors effects))
    p kind observation found active noMonitor selected bad with just-injective (trans (sym foundOld) found)
  ... | refl = afterPeer , sameMonitors , sameJobs , effects
  poll-nonclean ref w s t (poll-agreement observations (poll-forwarded old foundOld cause moved sameFront sameJobs))
    p kind observation found active noMonitor selected bad with just-injective (trans (sym foundOld) found)
  ... | refl with cause
  ...   | cold-path status absent = case active-inactive p active (inj₁ status) of λ ()
  ...   | cooling-path status absent = case active-inactive p active (inj₂ status) of λ ()
  ...   | followup-path f monitored = case trans (sym monitored) noMonitor of λ ()
  ...   | clean-path kind′ observation′ activeOld absent chosen good with just-injective (trans (sym chosen) selected)
  ...     | refl = case trans (sym good) bad of λ ()

  -- Successful governor hot waits return their own captured body in the same
  -- transition. This exact pool equation leaves queues and registry untouched.
  job-success-return : ∀ j s t (agreement : JobAgreement j s t) jf →
    lookup j (jobs (T.base t)) ≡ just jf → J.pc (Sub.execution jf) ≡ J.complete G.succeeded →
    C.governorPool (K.context (T.base t)) ≡ record (C.governorPool (K.context (T.base s)))
      { handles = put j (GP.Pool.bodyReturned (GP.body j (J.work (Sub.execution jf)) G.succeeded))
        (GP.Pool.handles (C.governorPool (K.context (T.base s)))) }
  job-success-return j s t (job-agreement observations (job-forwarded decision forwarded)) jf found complete =
    returned-pool j _ _ (governor-job-return j _ (PS.governor (K.peers (T.base s))) jf G.succeeded
      (proj₁ (quiet-governor _ (T.base s) (λ _ _ → refl) (ForwardedJob.inherited forwarded))) found complete)
  job-success-return j s t (job-agreement observations (job-failed decision afterJob afterPeer effects)) jf found complete
    with just-injective (trans (sym afterJob) found)
  ... | refl = case complete of λ ()

  -- Both successful and failed wait events leave the job unqueued. Publication
  -- must still execute its own guarded source operation.
  job-wait-unqueued : ∀ j s t (agreement : JobAgreement j s t) jf →
    lookup j (jobs (T.base t)) ≡ just jf → Sub.queued jf ≡ false
  job-wait-unqueued j s t (job-agreement observations (job-forwarded decision forwarded)) jf found
    with just-injective (trans (sym (ForwardedJob.afterJob forwarded)) found)
  ... | refl = Read.JobRead.notQueued (Physical.PhysicalJobWait.reader observations)
  job-wait-unqueued j s t (job-agreement observations (job-failed decision afterJob afterPeer effects)) jf found
    with just-injective (trans (sym afterJob) found)
  ... | refl = Read.JobRead.notQueued (Physical.PhysicalJobWait.reader observations)

  -- Completing a logical followup is not returning its physical monitor loop.
  record MonitorWaitEffects (s t : T.Runtime) : Set where
    constructor monitor-wait-effects
    field
      governor : C.governorPool (K.context (T.base t)) ≡ C.governorPool (K.context (T.base s))
      threads : C.monitors (K.context (T.base t)) ≡ C.monitors (K.context (T.base s))
      pool : C.monitorPool (K.context (T.base t)) ≡ C.monitorPool (K.context (T.base s))
  monitor-wait-preserves : ∀ ref s t → MonitorAgreement ref s t → MonitorWaitEffects s t
  monitor-wait-preserves ref s t (monitor-agreement observations (monitor-failed decision afterMonitor afterPeer effects)) =
    monitor-wait-effects (FailureEffects.governorPool effects) (FailureEffects.monitorThreads effects) (FailureEffects.monitorPool effects)
  monitor-wait-preserves ref s t (monitor-agreement observations (monitor-forwarded decision forwarded))
    with quiet-governor (GP.run (Sub.monitorStep ref (T.waitAction (Read.MonitorRead.frame (Physical.PhysicalMonitorWait.reader observations))))) (T.base s) (λ _ _ → refl) (ForwardedMonitor.inherited forwarded)
  ... | advanced , threads , pool = monitor-wait-effects
    (governor-monitor-pool ref (T.waitAction (Read.MonitorRead.frame (Physical.PhysicalMonitorWait.reader observations))) (PS.governor (K.peers (T.base s))) advanced) threads pool

  -- The two completion ledgers and actual publication guard are all retained.
  -- The boolean agreement is precisely returnedBody's existing source check.
  record CompletionPublication (j : JobId) (delay : ℕ) (jf : Sub.JobFrame) (result : G.Outcome) (s t : T.Runtime) : Set where
    constructor completion-publication
    field
      captured : GP.Body
      body : lookup j (GP.Pool.handles (C.governorPool (K.context (T.base s)))) ≡ just (GP.Pool.bodyReturned captured)
      agrees : GP.returnedBody j (machine (T.base s)) captured ≡ true
      delayAllowed : Sub.validCompletionDelay (J.work (Sub.execution jf)) result delay ≡ true
      queued : lookup j (jobs (T.base t)) ≡ just (record jf { queued = true })
      sourceQueue : Sub.completions (machine (T.base t)) ≡ Sub.completions (machine (T.base s)) ++
        (G.completion (J.work (Sub.execution jf)) result delay ∷ [])
      poolStep : GP.Pool.step (GP.Pool.publishCompletion j) (C.governorPool (K.context (T.base s))) ≡ just (C.governorPool (K.context (T.base t)))
      pool : C.governorPool (K.context (T.base t)) ≡ record (C.governorPool (K.context (T.base s)))
        { handles = put j (GP.Pool.deregisterPending GP.Pool.normalExit) (GP.Pool.handles (C.governorPool (K.context (T.base s))))
        ; completions = GP.Pool.completions (C.governorPool (K.context (T.base s))) ++ (captured ∷ []) }
      physicalJobs : protocol-jobs t ≡ protocol-jobs s
  publish-completion : ∀ j delay s t jf result → lookup j (jobs (T.base s)) ≡ just jf →
    Sub.queued jf ≡ false → J.pc (Sub.execution jf) ≡ J.complete result →
    T.advance (T.dispatch (K.peerStep (PS.run (GP.run (Sub.enqueueCompletion j delay))))) s ≡ just t →
    CompletionPublication j delay jf result s t
  publish-completion j delay s t jf result found unqueued complete eq
    with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate (K.peerStep (PS.run (GP.run (Sub.enqueueCompletion j delay)))) s eq
  ... | next , advanced , same with just-injective (cong just same)
  ...   | refl with quiet-governor (GP.run (Sub.enqueueCompletion j delay)) (T.base s) (λ _ _ → refl) advanced |
    subsystem-lower (Sub.enqueueCompletion j delay) (T.base s) (λ _ _ → refl) advanced
  ...     | governed , threads , monitorPool | c , stepped , sameMachine
    with governor-publication j delay (PS.governor (K.peers (T.base s))) governed | sub-publication j delay (machine (T.base s)) jf result found unqueued complete stepped
  ...       | captured , body , agrees , poolStep | delayOK , queued , sourceQueue =
    completion-publication captured body agrees delayOK
      (trans (cong (λ c → lookup j (Sub.jobs c)) sameMachine) queued)
      (trans (cong Sub.completions sameMachine) sourceQueue) poolStep (published-pool j captured _ body poolStep)
      (peer-job-table (PS.run (GP.run (Sub.enqueueCompletion j delay))) (T.base s) advanced)

  -- A physical normal monitor return requires its own enabled action after the
  -- loop reaches normalFinishing; a completed followup supplies no such step.
  finish-monitor-body : ∀ tid s t → T.advance (T.dispatch (K.peerStep (PS.finishMonitor tid))) s ≡ just t →
    MonitorBodyReturn tid (K.peers (T.base s)) (K.peers (T.base t))
  finish-monitor-body tid s t eq
    with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate (K.peerStep (PS.finishMonitor tid)) s eq
  ... | next , advanced , same with same
  ...   | refl with Shared.peer-step isBearerClosed isIOManagerError (PS.finishMonitor tid) (T.base s) advanced
  ...     | p , stepped , samePeer , source = subst (MonitorBodyReturn tid (K.peers (T.base s))) (sym samePeer)
    (physical-monitor-return tid (K.peers (T.base s)) stepped)

  -- The immediate publication after a successful certified wait selects exactly
  -- the body returned by that wait, not a merely matching supplied result.
  job-published-body : ∀ j delay s t u (agreement : JobAgreement j s t) jf →
    lookup j (jobs (T.base t)) ≡ just jf → J.pc (Sub.execution jf) ≡ J.complete G.succeeded →
    (publication : CompletionPublication j delay jf G.succeeded t u) →
    CompletionPublication.captured publication ≡ GP.body j (J.work (Sub.execution jf)) G.succeeded
  job-published-body j delay s t u agreement jf found complete publication
    with just-injective (trans
      (sym (trans (cong (λ p → lookup j (GP.Pool.handles p)) (job-success-return j s t agreement jf found complete))
        (lookup-put j (GP.Pool.bodyReturned (GP.body j (J.work (Sub.execution jf)) G.succeeded))
          (GP.Pool.handles (C.governorPool (K.context (T.base s)))))))
      (CompletionPublication.body publication))
  ... | refl = refl

  -- Queue publication is still the normal pending-deregistration phase, even
  -- when the operation and both completion ledgers already hold their results.
  publication-handle : ∀ j delay jf result s t → CompletionPublication j delay jf result s t →
    lookup j (GP.Pool.handles (C.governorPool (K.context (T.base t)))) ≡ just (GP.Pool.deregisterPending GP.Pool.normalExit)
  publication-handle j delay jf result s t publication = trans
    (cong (λ p → lookup j (GP.Pool.handles p)) (CompletionPublication.pool publication))
    (lookup-put j (GP.Pool.deregisterPending GP.Pool.normalExit) (GP.Pool.handles (C.governorPool (K.context (T.base s)))))

  -- Owner bookkeeping is projected from the actual enabled shared frontend
  -- step. Its source queue can shrink while the pool body ledger stays intact.
  record OwnerEffects (a : Sub.Action) (s t : T.Runtime) : Set where
    constructor owner-state-effects
    field
      sourceStep : Sub.advance a (machine (T.base s)) ≡ just (machine (T.base t))
      ownerOpen : GP.ownerOpen (C.governorPool (K.context (T.base s))) ≡ true
      ledger : C.governorPool (K.context (T.base t)) ≡ C.governorPool (K.context (T.base s))
      threads : C.monitors (K.context (T.base t)) ≡ C.monitors (K.context (T.base s))
      monitorPool : C.monitorPool (K.context (T.base t)) ≡ C.monitorPool (K.context (T.base s))
      physicalJobs : protocol-jobs t ≡ protocol-jobs s
  owner-bookkeeping : ∀ a → CompletionOwner a → ∀ s t →
    T.advance (T.dispatch (K.peerStep (PS.run (GP.run a)))) s ≡ just t → OwnerEffects a s t
  owner-bookkeeping a owned s t eq
    with Shared.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate (K.peerStep (PS.run (GP.run a))) s eq
  ... | next , advanced , same with same
  ...   | refl with quiet-governor (GP.run a) (T.base s) (quiet-owner owned) advanced |
    subsystem-lower a (T.base s) (quiet-owner owned) advanced
  ...     | governed , threads , monitorPool | c , stepped , sameMachine
    with governor-owner-pool a owned (PS.governor (K.peers (T.base s))) governed
  ...       | opened , ledger = owner-state-effects
    (subst (λ c → Sub.advance a (machine (T.base s)) ≡ just c) (sym sameMachine) stepped)
    opened ledger threads monitorPool (peer-job-table (PS.run (GP.run a)) (T.base s) advanced)

  -- Selection/application/publication certificates expose the actual source
  -- guards and effects together with unchanged physical supervision resources.
  selected-completion : ∀ s t → T.advance (T.dispatch (K.peerStep (PS.run (GP.run Sub.selectCompletion)))) s ≡ just t →
    CompletionSelection (machine (T.base s)) (machine (T.base t)) × OwnerEffects Sub.selectCompletion s t
  selected-completion s t eq = select-completion (machine (T.base s)) (machine (T.base t)) (OwnerEffects.sourceStep effects) , effects
    where effects = owner-bookkeeping Sub.selectCompletion owner-select s t eq
  applied-completion : ∀ time result s t → Sub.pc (machine (T.base s)) ≡ Sub.apply (Sub.completion result) →
    T.advance (T.dispatch (K.peerStep (PS.run (GP.run (Sub.applyAt time))))) s ≡ just t →
    CompletionApplication time result (machine (T.base s)) (machine (T.base t)) × OwnerEffects (Sub.applyAt time) s t
  applied-completion time result s t chosen eq = apply-completion time result (machine (T.base s)) (machine (T.base t)) chosen
    (OwnerEffects.sourceStep effects) , effects
    where effects = owner-bookkeeping (Sub.applyAt time) (owner-apply time) s t eq
  cancelled-completion-timer : ∀ result s t → Sub.pc (machine (T.base s)) ≡ Sub.cancelTimer (Sub.completion result) →
    T.advance (T.dispatch (K.peerStep (PS.run (GP.run Sub.cancelWakeup)))) s ≡ just t →
    machine (T.base t) ≡ record (machine (T.base s))
      { pc = Sub.apply (Sub.completion result); wakeupAt = nothing; wakeupReady = false } × OwnerEffects Sub.cancelWakeup s t
  cancelled-completion-timer result s t chosen eq = cancel-completion-timer result (machine (T.base s)) (machine (T.base t)) chosen
    (OwnerEffects.sourceStep effects) , effects
    where effects = owner-bookkeeping Sub.cancelWakeup owner-cancel s t eq
  public-governor-state : ∀ s t → T.advance (T.dispatch (K.peerStep (PS.run (GP.run Sub.publishPublicState)))) s ≡ just t →
    PublicStatePublication (machine (T.base s)) (machine (T.base t)) × OwnerEffects Sub.publishPublicState s t
  public-governor-state s t eq = publish-public-state (machine (T.base s)) (machine (T.base t)) (OwnerEffects.sourceStep effects) , effects
    where effects = owner-bookkeeping Sub.publishPublicState owner-public s t eq

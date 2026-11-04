{-# OPTIONS --guardedness #-}

-- Every terminal physical-monitor handle in an initialized frontend execution
-- has an actual earlier source exit. No return history is supplied as a premise.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersMonitorBacking
  (isBearerClosed isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (HandleId; JobId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.IGTypes using (number)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Properties.ServerPeers as Shared
import ConnectionManagement.Properties.MonitorPoolEffects as Effects
import ConnectionManagement.Properties.ServerPeersMonitorReturns as Returns
import ConnectionManagement.Rules.PeerActions as Peer
private
 module K = Combined isBearerClosed isIOManagerError
 module E = Exit isBearerClosed
 module PS = Supervision isIOManagerError
 module Pool = PS.Pool
 module C = Context isIOManagerError
 module F = Effects isBearerClosed isIOManagerError
 module R = Returns isBearerClosed isIOManagerError

view : K.State → Pool.State
view s = PS.monitorPool (K.peers s)
SharedExit : K.State → K.Action → R.Kind → JobId → Set
SharedExit s a kind tid = a ≡ K.peerStep (R.action kind tid) × F.PhysicalExit (K.peers s) kind tid
shared-change : ∀ a s {t} → K.step a s ≡ just t → F.Change (SharedExit s a) (view s) (view t)
shared-change (K.serverStep a) s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → F.same refl }
shared-change (K.coreStep a) s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → F.same refl }
shared-change (K.peerStep a) s eq with K.peerOpen s | K.peerAllowed a s
... | false | _ = case eq of λ ()
... | true | false = case eq of λ ()
... | true | true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → F.map-exit (λ kind tid located → cong K.peerStep (proj₁ located) , proj₂ located)
  (F.located-change a (K.peers s) advanced) }

-- Terminal exits are unique even when a normal return's payload was discarded.
terminal-exit : ∀ {phase ex ex′} → F.Terminal phase ex → F.Terminal phase ex′ → ex ≡ ex′
terminal-exit F.isPending F.isPending = refl
terminal-exit F.isRemoved F.isRemoved = refl
terminal-exit F.isAvailable F.isAvailable = refl
active-not-terminal : ∀ {phase ex} → F.Active phase → F.Terminal phase ex → ⊥
active-not-terminal F.running ()
active-not-terminal F.unwinding ()
written-lookup : ∀ k phase before after → Pool.handles after ≡ put k phase (Pool.handles before) →
 lookup k (Pool.handles after) ≡ just phase
written-lookup k phase before after same = trans (cong (lookup k) same) (lookup-put k phase (Pool.handles before))
old-lookup : ∀ {phase} k j value before after → k ≢ j →
 Pool.handles after ≡ put k value (Pool.handles before) → lookup j (Pool.handles after) ≡ just phase →
 lookup j (Pool.handles before) ≡ just phase
old-lookup k j value before after apart same found =
 trans (sym (trans (cong (lookup j) same) (lookup-put-other k j value (Pool.handles before) (λ eq → apart (sym eq))))) found

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate
  module H = R.Frontend canInitiate
 peers : T.Runtime → PS.State
 peers s = K.peers (T.base s)
 pool : T.Runtime → Pool.State
 pool s = view (T.base s)

 -- Protocol caching changes peer cells, preserving the entire monitor pool.
 cache-view : ∀ rid r result f b → view (T.cacheResult rid r result f b) ≡ view b
 cache-view rid r result f b with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
 ... | nothing = refl
 ... | just (current , _) with current ≟ rid
 ...   | no _ = refl
 ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
 ...     | nothing = refl
 ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
 ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
 ...         | nothing = refl
 ...         | just rs = refl
 cache-view rid r result f b | just (current , _) | yes _ | just peer | no _ | _ = refl
 cache-view rid r result f b | just (current , _) | yes _ | just peer | yes _ | no _ = refl
 -- These are exactly the plan forms that execute a physical source action.
 data SelectedExit (kind : R.Kind) (tid : JobId) : T.Plan → Set where
  inherited : ∀ f → SelectedExit kind tid (T.inherit (K.peerStep (R.action kind tid)) f)
  called : ∀ f → SelectedExit kind tid (T.caller (R.action kind tid) f)
  completed : ∀ rid r result → SelectedExit kind tid (T.complete (K.peerStep (R.action kind tid)) rid r result)
 PlannedExit : T.Runtime → T.Plan → R.Kind → JobId → Set
 PlannedExit s plan kind tid = SelectedExit kind tid plan × F.PhysicalExit (peers s) kind tid
 inherit-exit : ∀ a f s kind tid → SharedExit (T.base s) a kind tid → PlannedExit s (T.inherit a f) kind tid
 inherit-exit a f s kind tid (refl , witness) = inherited f , witness
 caller-exit : ∀ a f s kind tid → a ≡ R.action kind tid × F.PhysicalExit (peers s) kind tid → PlannedExit s (T.caller a f) kind tid
 caller-exit a f s kind tid (refl , witness) = called f , witness
 complete-exit : ∀ a rid r result s kind tid → SharedExit (T.base s) a kind tid → PlannedExit s (T.complete a rid r result) kind tid
 complete-exit a rid r result s kind tid (refl , witness) = completed rid r result , witness
 enact-change : ∀ plan s {t} → T.enact plan s ≡ just t → F.Change (PlannedExit s plan) (pool s) (pool t)
 enact-change (T.inherit a f) s eq with K.step a (T.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → F.map-exit (inherit-exit a f s) (shared-change a (T.base s) advanced) }
 enact-change (T.caller a f) s eq with PS.step a (peers s) in advanced
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → F.map-exit (caller-exit a f s) (F.located-change a (peers s) advanced) }
 enact-change (T.local f) s eq = case just-injective eq of λ { refl → F.same refl }
 enact-change (T.reading r) s eq = case just-injective eq of λ { refl → F.same refl }
 enact-change (T.traceFault w rid result fs) s eq = case just-injective eq of λ { refl → F.same refl }
 enact-change (T.deliverTraceFault w rid result fs coordinator) s eq = case just-injective eq of λ { refl → F.same refl }
 enact-change (T.birth w capturedFrame protocolPool j rid r f) s eq = case just-injective eq of λ { refl → F.same refl }
 enact-change (T.complete a rid r result) s eq with K.step a (T.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → F.right-pool (sym (cache-view rid r result (T.front s) b))
   (F.map-exit (complete-exit a rid r result s) (shared-change a (T.base s) advanced)) }
 advance-change : ∀ a s {t} → T.advance a s ≡ just t →
   Σ T.Plan (λ plan → T.choose a s ≡ just plan × F.Change (PlannedExit s plan) (pool s) (pool t))
 advance-change a s eq with T.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just plan = plan , refl , enact-change plan s eq

 -- The actual frontend selector and actual lower source step are both retained.
 -- Caching may subsequently update peer cells; it cannot change these handles.
 record History (start current : T.Runtime) (tid : JobId) (kind : R.Kind) : Set where
  constructor history
  field
   initialization : H.Initialized start
   before after : T.Runtime
   prefix suffix : List T.Event
   event : T.Event
   plan : T.Plan
   reached : T.Runs start prefix before
   chosen : T.choose event before ≡ just plan
   advanced : T.advance event before ≡ just after
   continued : T.Runs after suffix current
   selected : SelectedExit kind tid plan
   physical : F.PhysicalExit (peers before) kind tid
   wrote : Pool.handles (pool after) ≡ put tid (Pool.deregisterPending (R.exit kind)) (Pool.handles (pool before))
 Backed : T.Runtime → T.Runtime → Set
 Backed start current = ∀ tid phase ex → lookup tid (Pool.handles (pool current)) ≡ just phase →
   F.Terminal phase ex → Σ R.Kind (λ kind → R.exit kind ≡ ex × History start current tid kind)

 extend : ∀ {start s t tid kind actions} → T.Runs s actions t → History start s tid kind → History start t tid kind
 extend {actions = actions} path (history init before after prefix suffix event plan reached chosen advanced continued selected exitEvidence wrote) =
   history init before after prefix (suffix ++ actions) event plan reached chosen advanced
     (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate continued path) selected exitEvidence wrote
 extend-result : ∀ {start s t tid ex actions} → T.Runs s actions t →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × History start s tid kind) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × History start t tid kind)
 extend-result path (kind , agrees , origin) = kind , agrees , extend path origin

 -- Induction on enabled execution transports old histories for unrelated keys,
 -- and creates a new one only at a source-certified return/unwind write.
 step-backed : ∀ {start prefix s t} → H.Initialized start → ∀ a → T.Runs start prefix s →
   T.advance a s ≡ just t → Backed start s → Backed start t
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j phase ex found terminal with advance-change a s advanced
 ... | plan , chosen , F.same same = extend-result (T.more {a = a} advanced T.stop)
   (backed j phase ex (trans (sym (cong (lookup j) same)) found) terminal)
 ... | plan , chosen , F.active k value act same with k ≟ j
 ...   | yes refl = ⊥-elim (active-not-terminal act
   (subst (λ p → F.Terminal p ex) (sym (just-injective (trans (sym (written-lookup j value (pool s) (pool t) same)) found))) terminal))
 ...   | no apart = extend-result (T.more {a = a} advanced T.stop)
   (backed j phase ex (old-lookup k j value (pool s) (pool t) apart same found) terminal)
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j phase ex found terminal | plan , chosen , F.carry k oldExit old next was now oldFound same with k ≟ j
 ... | yes refl with backed j old oldExit oldFound was
 ...   | kind , agrees , origin = kind , trans agrees
   (terminal-exit (subst (λ p → F.Terminal p oldExit)
     (just-injective (trans (sym (written-lookup j next (pool s) (pool t) same)) found)) now) terminal) ,
   extend (T.more {a = a} advanced T.stop) origin
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j phase ex found terminal | plan , chosen , F.carry k oldExit old next was now oldFound same | no apart =
   extend-result (T.more {a = a} advanced T.stop) (backed j phase ex (old-lookup k j next (pool s) (pool t) apart same found) terminal)
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j phase ex found terminal | plan , chosen , F.ending k kind (selected , exitEvidence) same with k ≟ j
 ... | yes refl = kind , terminal-exit
   (subst (λ p → F.Terminal p (R.exit kind))
     (just-injective (trans (sym (written-lookup j (Pool.deregisterPending (R.exit kind)) (pool s) (pool t) same)) found)) F.isPending) terminal ,
   history init s t prefix [] a plan reached chosen advanced T.stop selected exitEvidence same
 ... | no apart = extend-result (T.more {a = a} advanced T.stop)
   (backed j phase ex (old-lookup k j (Pool.deregisterPending (R.exit kind)) (pool s) (pool t) apart same found) terminal)
 run-backed : ∀ {start prefix s actions t} → H.Initialized start → T.Runs start prefix s →
   Backed start s → T.Runs s actions t → Backed start t
 run-backed init reached backed T.stop = backed
 run-backed {prefix = prefix} init reached backed (T.more {a = a} advanced rest) =
   run-backed init (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate reached (T.more {a = a} advanced T.stop))
     (step-backed init a reached advanced backed) rest
 -- The initializer supplies an empty physical pool independently of its
 -- arbitrarily supplied CM/governor inputs; no extra initial invariant is used.
 initial-empty : ∀ {c g start} → T.initialize c g ≡ just start → Pool.handles (pool start) ≡ []
 initial-empty {c} init with E.initial c
 ... | nothing = case init of λ ()
 ... | just e with just-injective init
 ...   | refl = refl
 initialized-backed : ∀ {c g start actions current} → T.initialize c g ≡ just start →
   T.Runs start actions current → Backed start current
 initialized-backed {c} {g} init path = run-backed (H.initialized c g init) T.stop
   (λ j phase ex found terminal → case trans (sym (cong (lookup j) (initial-empty init))) found of λ ()) path

 initialized-terminal : ∀ {c g start actions current} → T.initialize c g ≡ just start → T.Runs start actions current →
   ∀ tid phase ex → lookup tid (Pool.handles (pool current)) ≡ just phase → F.Terminal phase ex →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × History start current tid kind)
 initialized-terminal init path = initialized-backed init path
 initialized-pending : ∀ {c g start actions current tid ex} → T.initialize c g ≡ just start → T.Runs start actions current →
   lookup tid (Pool.handles (pool current)) ≡ just (Pool.deregisterPending ex) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × History start current tid kind)
 initialized-pending {tid = tid} {ex} init path found = initialized-terminal init path tid _ ex found F.isPending
 initialized-removed : ∀ {c g start actions current tid ex} → T.initialize c g ≡ just start → T.Runs start actions current →
   lookup tid (Pool.handles (pool current)) ≡ just (Pool.deregistered ex) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × History start current tid kind)
 initialized-removed {tid = tid} {ex} init path found = initialized-terminal init path tid _ ex found F.isRemoved
 initialized-published : ∀ {c g start actions current tid ex} → T.initialize c g ≡ just start → T.Runs start actions current →
   lookup tid (Pool.handles (pool current)) ≡ just (Pool.resultAvailable ex) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × History start current tid kind)
 initialized-published {tid = tid} {ex} init path found = initialized-terminal init path tid _ ex found F.isAvailable

 -- A cancelled terminal handle requires the unwind cause; a handled error's
 -- normal pool exit cannot be substituted for it.
 cancelled-history : ∀ {start current tid} →
   Σ R.Kind (λ kind → R.exit kind ≡ Pool.cancelledExit × History start current tid kind) → History start current tid R.cancelled
 cancelled-history (R.normal , () , origin)
 cancelled-history (R.exceptional , () , origin)
 cancelled-history (R.cancelled , refl , origin) = origin

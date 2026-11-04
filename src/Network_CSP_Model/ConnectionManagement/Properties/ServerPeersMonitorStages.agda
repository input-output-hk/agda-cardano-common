{-# OPTIONS --guardedness #-}

-- Initialized terminal queries retain the ordered physical exit, registry
-- removal and Async publication events, including arbitrary intervening steps.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersMonitorStages
 (isBearerClosed isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (HandleId; JobId)
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Properties.ServerPeers as Shared
import ConnectionManagement.Properties.MonitorPoolEffects as Effects
import ConnectionManagement.Properties.ServerPeersMonitorReturns as Returns
import ConnectionManagement.Properties.ServerPeersMonitorBacking as Backing
private
 module K = Combined isBearerClosed isIOManagerError
 module E = Exit isBearerClosed
 module PS = Supervision isIOManagerError
 module Pool = PS.Pool
 module F = Effects isBearerClosed isIOManagerError
 module D = F.Detailed
 module R = Returns isBearerClosed isIOManagerError
 module M = Backing isBearerClosed isIOManagerError

-- Stage and exit are separate indices; normal/error payloads remain historical.
data Stage : Set where
 returnedStage removedStage availableStage : Stage
phase : Stage → Pool.Exit → Pool.ThreadPhase
phase returnedStage ex = Pool.deregisterPending ex
phase removedStage ex = Pool.deregistered ex
phase availableStage ex = Pool.resultAvailable ex
beforeStage : F.Move → Stage
beforeStage F.deregistering = returnedStage
beforeStage F.publishing = removedStage
afterStage : F.Move → Stage
afterStage F.deregistering = removedStage
afterStage F.publishing = availableStage
phase-from : ∀ move ex → phase (beforeStage move) ex ≡ F.fromPhase move ex
phase-from F.deregistering ex = refl
phase-from F.publishing ex = refl
phase-to : ∀ move ex → phase (afterStage move) ex ≡ F.toPhase move ex
phase-to F.deregistering ex = refl
phase-to F.publishing ex = refl
phase-index : ∀ {a b ex ex′} → phase a ex ≡ phase b ex′ → (a ≡ b) × (ex ≡ ex′)
phase-index {returnedStage} {returnedStage} refl = refl , refl
phase-index {returnedStage} {removedStage} ()
phase-index {returnedStage} {availableStage} ()
phase-index {removedStage} {returnedStage} ()
phase-index {removedStage} {removedStage} refl = refl , refl
phase-index {removedStage} {availableStage} ()
phase-index {availableStage} {returnedStage} ()
phase-index {availableStage} {removedStage} ()
phase-index {availableStage} {availableStage} refl = refl , refl
terminal : ∀ stage ex → F.Terminal (phase stage ex) ex
terminal returnedStage ex = F.isPending
terminal removedStage ex = F.isRemoved
terminal availableStage ex = F.isAvailable

SharedMove : K.State → K.Action → F.Move → JobId → Set
SharedMove s a move tid = a ≡ K.peerStep (F.moveAction move tid) × F.PhysicalMove (K.peers s) move tid
shared-change : ∀ a s {t} → K.step a s ≡ just t →
 D.Effect (M.SharedExit s a) (SharedMove s a) (M.view s) (M.view t)
shared-change (K.serverStep a) s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → D.kept refl }
shared-change (K.coreStep a) s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → D.kept refl }
shared-change (K.peerStep a) s eq with K.peerOpen s | K.peerAllowed a s
... | false | _ = case eq of λ ()
... | true | false = case eq of λ ()
... | true | true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → D.map-evidence
 (λ kind tid located → cong K.peerStep (proj₁ located) , proj₂ located)
 (λ move tid located → cong K.peerStep (proj₁ located) , proj₂ located)
 (F.full-located-change a (K.peers s) advanced) }

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate
  module B = M.Frontend canInitiate
  module H = R.Frontend canInitiate
 peers : T.Runtime → PS.State
 peers = B.peers
 pool : T.Runtime → Pool.State
 pool = B.pool

 -- SelectedMove states which actual frontend plan executes this exact move.
 data SelectedMove (move : F.Move) (tid : JobId) : T.Plan → Set where
  inheritedMove : ∀ f → SelectedMove move tid (T.inherit (K.peerStep (F.moveAction move tid)) f)
  calledMove : ∀ f → SelectedMove move tid (T.caller (F.moveAction move tid) f)
  completedMove : ∀ rid r result → SelectedMove move tid (T.complete (K.peerStep (F.moveAction move tid)) rid r result)
 PlannedMove : T.Runtime → T.Plan → F.Move → JobId → Set
 PlannedMove s plan move tid = SelectedMove move tid plan × F.PhysicalMove (peers s) move tid
 inherit-move : ∀ a f s move tid → SharedMove (T.base s) a move tid → PlannedMove s (T.inherit a f) move tid
 inherit-move a f s move tid (refl , witness) = inheritedMove f , witness
 caller-move : ∀ a f s move tid → a ≡ F.moveAction move tid × F.PhysicalMove (peers s) move tid → PlannedMove s (T.caller a f) move tid
 caller-move a f s move tid (refl , witness) = calledMove f , witness
 complete-move : ∀ a rid r result s move tid → SharedMove (T.base s) a move tid → PlannedMove s (T.complete a rid r result) move tid
 complete-move a rid r result s move tid (refl , witness) = completedMove rid r result , witness
 enact-change : ∀ plan s {t} → T.enact plan s ≡ just t → D.Effect (B.PlannedExit s plan) (PlannedMove s plan) (pool s) (pool t)
 enact-change (T.inherit a f) s eq with K.step a (T.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → D.map-evidence (B.inherit-exit a f s) (inherit-move a f s) (shared-change a (T.base s) advanced) }
 enact-change (T.caller a f) s eq with PS.step a (peers s) in advanced
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → D.map-evidence (B.caller-exit a f s) (caller-move a f s) (F.full-located-change a (peers s) advanced) }
 enact-change (T.local f) s eq = case just-injective eq of λ { refl → D.kept refl }
 enact-change (T.reading r) s eq = case just-injective eq of λ { refl → D.kept refl }
 enact-change (T.traceFault w rid result fs) s eq = case just-injective eq of λ { refl → D.kept refl }
 enact-change (T.deliverTraceFault w rid result fs coordinator) s eq = case just-injective eq of λ { refl → D.kept refl }
 enact-change (T.birth w capturedFrame protocolPool j rid r f) s eq = case just-injective eq of λ { refl → D.kept refl }
 enact-change (T.complete a rid r result) s eq with K.step a (T.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → D.retarget (sym (B.cache-view rid r result (T.front s) b))
   (D.map-evidence (B.complete-exit a rid r result s) (complete-move a rid r result s) (shared-change a (T.base s) advanced)) }
 advance-change : ∀ a s {t} → T.advance a s ≡ just t →
   Σ T.Plan (λ plan → T.choose a s ≡ just plan × D.Effect (B.PlannedExit s plan) (PlannedMove s plan) (pool s) (pool t))
 advance-change a s eq with T.choose a s
 ... | nothing = case eq of λ ()
 ... | just plan = plan , refl , enact-change plan s eq

 -- Actual source results coincide with the whole runtime pool, including its
 -- registry. Completion caching is handled explicitly rather than assumed.
 shared-move-pool : ∀ move tid s t (witness : F.PhysicalMove (K.peers s) move tid) →
   K.step (K.peerStep (F.moveAction move tid)) s ≡ just t → M.view t ≡ PS.monitorPool (F.PhysicalMove.after witness)
 shared-move-pool move tid s t witness advanced with Shared.peer-step isBearerClosed isIOManagerError (F.moveAction move tid) s advanced
 ... | p , stepped , samePeer , source with just-injective (trans (sym stepped) (F.PhysicalMove.advanced witness))
 ...   | refl = cong PS.monitorPool samePeer
 enact-move-pool : ∀ {plan} move tid s t → SelectedMove move tid plan → (witness : F.PhysicalMove (peers s) move tid) →
   T.enact plan s ≡ just t → pool t ≡ PS.monitorPool (F.PhysicalMove.after witness)
 enact-move-pool move tid s t (inheritedMove f) witness eq with K.step (K.peerStep (F.moveAction move tid)) (T.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → shared-move-pool move tid (T.base s) b witness advanced }
 enact-move-pool move tid s t (calledMove f) witness eq with PS.step (F.moveAction move tid) (peers s) in advanced
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → cong PS.monitorPool (just-injective (trans (sym advanced) (F.PhysicalMove.advanced witness))) }
 enact-move-pool move tid s t (completedMove rid r result) witness eq with K.step (K.peerStep (F.moveAction move tid)) (T.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → trans (B.cache-view rid r result (T.front s) b)
   (shared-move-pool move tid (T.base s) b witness advanced) }
 realized-pool : ∀ {s t plan event move tid} → SelectedMove move tid plan → (witness : F.PhysicalMove (peers s) move tid) →
   T.choose event s ≡ just plan → T.advance event s ≡ just t → pool t ≡ PS.monitorPool (F.PhysicalMove.after witness)
 realized-pool {s} {t} {move = move} {tid} selected witness chosen advanced rewrite chosen =
   enact-move-pool move tid s t selected witness advanced

 record Removal (start current : T.Runtime) (tid : JobId) (kind : R.Kind) : Set where
  constructor removal-history
  field
   before after : T.Runtime
   body : B.History start before tid kind
   event : T.Event
   plan : T.Plan
   chosen : T.choose event before ≡ just plan
   advanced : T.advance event before ≡ just after
   selected : SelectedMove F.deregistering tid plan
   physical : F.PhysicalMove (peers before) F.deregistering tid
   matchedPool : pool after ≡ PS.monitorPool (F.PhysicalMove.after physical)
   registry : Pool.registered (pool after) ≡ Pool.remove tid (Pool.registered (pool before))
   oldLookup : lookup tid (Pool.handles (pool before)) ≡ just (Pool.deregisterPending (R.exit kind))
   wrote : Pool.handles (pool after) ≡ put tid (Pool.deregistered (R.exit kind)) (Pool.handles (pool before))
   suffix : List T.Event
   continued : T.Runs after suffix current
 record Publication (start current : T.Runtime) (tid : JobId) (kind : R.Kind) : Set where
  constructor publication-history
  field
   before after : T.Runtime
   removal : Removal start before tid kind
   event : T.Event
   plan : T.Plan
   chosen : T.choose event before ≡ just plan
   advanced : T.advance event before ≡ just after
   selected : SelectedMove F.publishing tid plan
   physical : F.PhysicalMove (peers before) F.publishing tid
   matchedPool : pool after ≡ PS.monitorPool (F.PhysicalMove.after physical)
   registry : Pool.registered (pool after) ≡ Pool.registered (pool before)
   oldLookup : lookup tid (Pool.handles (pool before)) ≡ just (Pool.deregistered (R.exit kind))
   wrote : Pool.handles (pool after) ≡ put tid (Pool.resultAvailable (R.exit kind)) (Pool.handles (pool before))
   suffix : List T.Event
   continued : T.Runs after suffix current

 -- A stage ledger retains its exact causal predecessors, never just a terminal
 -- phase assertion. Extension affects only the actual continuing suffix.
 Ledger : Stage → T.Runtime → T.Runtime → JobId → R.Kind → Set
 Ledger returnedStage = B.History
 Ledger removedStage = Removal
 Ledger availableStage = Publication
 extend-removal : ∀ {start s t tid kind actions} → T.Runs s actions t → Removal start s tid kind → Removal start t tid kind
 extend-removal {actions = actions} path (removal-history before after body event plan chosen advanced selected witness matched registry oldLookup wrote suffix continued) =
   removal-history before after body event plan chosen advanced selected witness matched registry oldLookup wrote (suffix ++ actions)
     (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate continued path)
 extend-publication : ∀ {start s t tid kind actions} → T.Runs s actions t → Publication start s tid kind → Publication start t tid kind
 extend-publication {actions = actions} path (publication-history before after prior event plan chosen advanced selected witness matched registry oldLookup wrote suffix continued) =
   publication-history before after prior event plan chosen advanced selected witness matched registry oldLookup wrote (suffix ++ actions)
     (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate continued path)
 extend : ∀ stage {start s t tid kind actions} → T.Runs s actions t → Ledger stage start s tid kind → Ledger stage start t tid kind
 extend returnedStage = B.extend
 extend removedStage = extend-removal
 extend availableStage = extend-publication

 -- New causal stage records are created only at the corresponding selected
 -- move, with its actual whole-pool match and registry effect.
 make-move : ∀ move {start s t tid kind ex event plan} → R.exit kind ≡ ex →
   Ledger (beforeStage move) start s tid kind → T.choose event s ≡ just plan → T.advance event s ≡ just t →
   SelectedMove move tid plan → F.PhysicalMove (peers s) move tid →
   lookup tid (Pool.handles (pool s)) ≡ just (F.fromPhase move ex) →
   Pool.handles (pool t) ≡ put tid (F.toPhase move ex) (Pool.handles (pool s)) → Ledger (afterStage move) start t tid kind
 make-move F.deregistering {s = s} {t} {tid = tid} {event = event} {plan} refl prior chosen advanced selected witness found wrote =
   removal-history s t prior event plan chosen advanced selected witness matched
     (trans (cong Pool.registered matched) (F.PhysicalMove.registry witness)) found wrote [] T.stop
   where
   matched : pool t ≡ PS.monitorPool (F.PhysicalMove.after witness)
   matched = realized-pool {s = s} {t = t} {plan = plan} {event = event} selected witness chosen advanced
 make-move F.publishing {s = s} {t} {tid = tid} {event = event} {plan} refl prior chosen advanced selected witness found wrote =
   publication-history s t prior event plan chosen advanced selected witness matched
     (trans (cong Pool.registered matched) (F.PhysicalMove.registry witness)) found wrote [] T.stop
   where
   matched : pool t ≡ PS.monitorPool (F.PhysicalMove.after witness)
   matched = realized-pool {s = s} {t = t} {plan = plan} {event = event} selected witness chosen advanced

 Backed : T.Runtime → T.Runtime → Set
 Backed start current = ∀ tid stage ex → lookup tid (Pool.handles (pool current)) ≡ just (phase stage ex) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × Ledger stage start current tid kind)
 extend-result : ∀ stage {start s t tid ex actions} → T.Runs s actions t →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × Ledger stage start s tid kind) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × Ledger stage start t tid kind)
 extend-result stage path (kind , agrees , prior) = kind , agrees , extend stage path prior

 -- One induction covers all stages and all source/frontend interleavings.
 -- In particular, neither removal nor publication needs a supplied predecessor.
 step-backed : ∀ {start prefix s t} → H.Initialized start → ∀ a → T.Runs start prefix s →
   T.advance a s ≡ just t → Backed start s → Backed start t
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j stage ex found with advance-change a s advanced
 ... | plan , chosen , D.kept same = extend-result stage (T.more {a = a} advanced T.stop)
   (backed j stage ex (trans (sym (cong (lookup j) same)) found))
 ... | plan , chosen , D.written k value act same with k ≟ j
 ...   | yes refl = ⊥-elim (M.active-not-terminal act
   (subst (λ p → F.Terminal p ex)
     (sym (just-injective (trans (sym (M.written-lookup j value (pool s) (pool t) same)) found))) (terminal stage ex)))
 ...   | no apart = extend-result stage (T.more {a = a} advanced T.stop)
   (backed j stage ex (M.old-lookup k j value (pool s) (pool t) apart same found))
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j stage ex found | plan , chosen , D.moved k move oldExit (selected , witness) oldFound wrote with k ≟ j
 ... | yes refl with phase-index (trans (phase-to move oldExit)
   (just-injective (trans (sym (M.written-lookup j (F.toPhase move oldExit) (pool s) (pool t) wrote)) found)))
 ...   | refl , refl with backed j (beforeStage move) oldExit (trans oldFound (cong just (sym (phase-from move oldExit))))
 ...     | kind , agrees , prior = kind , agrees , make-move move {start = start} {s = s} {t = t} {tid = j} {kind = kind} {ex = oldExit} {event = a} {plan = plan} agrees prior chosen advanced selected witness oldFound wrote
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j stage ex found | plan , chosen , D.moved k move oldExit witness oldFound wrote | no apart =
   extend-result stage (T.more {a = a} advanced T.stop)
     (backed j stage ex (M.old-lookup k j (F.toPhase move oldExit) (pool s) (pool t) apart wrote found))
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j stage ex found | plan , chosen , D.returnedStep k kind (selected , witness) wrote with k ≟ j
 ... | yes refl with phase-index (just-injective
   (trans (sym (M.written-lookup j (Pool.deregisterPending (R.exit kind)) (pool s) (pool t) wrote)) found))
 ...   | refl , refl = kind , refl , B.history init s t prefix [] a plan reached chosen advanced T.stop selected witness wrote
 step-backed {start} {prefix} {s} {t} init a reached advanced backed j stage ex found | plan , chosen , D.returnedStep k kind witness wrote | no apart =
   extend-result stage (T.more {a = a} advanced T.stop)
     (backed j stage ex (M.old-lookup k j (Pool.deregisterPending (R.exit kind)) (pool s) (pool t) apart wrote found))
 run-backed : ∀ {start prefix s actions t} → H.Initialized start → T.Runs start prefix s →
   Backed start s → T.Runs s actions t → Backed start t
 run-backed init reached backed T.stop = backed
 run-backed init reached backed (T.more {a = a} advanced rest) = run-backed init
   (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate reached (T.more {a = a} advanced T.stop))
   (step-backed init a reached advanced backed) rest
 initialized-backed : ∀ {c g start actions current} → T.initialize c g ≡ just start → T.Runs start actions current → Backed start current
 initialized-backed {c} {g} init path = run-backed (H.initialized c g init) T.stop
   (λ j stage ex found → case trans (sym (cong (lookup j) (B.initial-empty init))) found of λ ()) path

 initialized-pending : ∀ {c g start actions current tid ex} → T.initialize c g ≡ just start → T.Runs start actions current →
   lookup tid (Pool.handles (pool current)) ≡ just (Pool.deregisterPending ex) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × B.History start current tid kind)
 initialized-pending {tid = tid} {ex} init path found = initialized-backed init path tid returnedStage ex found
 initialized-removed : ∀ {c g start actions current tid ex} → T.initialize c g ≡ just start → T.Runs start actions current →
   lookup tid (Pool.handles (pool current)) ≡ just (Pool.deregistered ex) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × Removal start current tid kind)
 initialized-removed {tid = tid} {ex} init path found = initialized-backed init path tid removedStage ex found
 initialized-published : ∀ {c g start actions current tid ex} → T.initialize c g ≡ just start → T.Runs start actions current →
   lookup tid (Pool.handles (pool current)) ≡ just (Pool.resultAvailable ex) →
   Σ R.Kind (λ kind → R.exit kind ≡ ex × Publication start current tid kind)
 initialized-published {tid = tid} {ex} init path found = initialized-backed init path tid availableStage ex found
 cancelled-publication : ∀ {start current tid} →
   Σ R.Kind (λ kind → R.exit kind ≡ Pool.cancelledExit × Publication start current tid kind) → Publication start current tid R.cancelled
 cancelled-publication (R.normal , () , prior)
 cancelled-publication (R.exceptional , () , prior)
 cancelled-publication (R.cancelled , refl , prior) = prior

 -- Forgetting the new stages retains the increment-45 actual exit, extended
 -- through the recorded removal/publication and their continuing suffixes.
 removal-exit : ∀ {start current tid kind} → Removal start current tid kind → B.History start current tid kind
 removal-exit (removal-history before after body event plan chosen advanced selected witness matched registry oldLookup wrote suffix continued) =
   B.extend (T.more {a = event} advanced continued) body
 publication-exit : ∀ {start current tid kind} → Publication start current tid kind → B.History start current tid kind
 publication-exit (publication-history before after prior event plan chosen advanced selected witness matched registry oldLookup wrote suffix continued) =
   B.extend (T.more {a = event} advanced continued) (removal-exit prior)

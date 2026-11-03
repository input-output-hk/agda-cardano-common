{-# OPTIONS --guardedness #-}

-- Initialized historical provenance of consumed and pending governor results.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersCompletions
  (isBearerClosed isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (HandleId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.IGTypes using (number)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Properties.GovernorCompletions as Lower
import ConnectionManagement.Properties.ServerPeers as Shared
import ConnectionManagement.Properties.ServerPeersContinuations as Continuations
import ConnectionManagement.Properties.PeerSupervision as Projection
import ConnectionManagement.Properties.JobPoolReturnHistory as ReturnHistory
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.PeerActions as Peer
private
 module K = Combined isBearerClosed isIOManagerError
 module C = Context isIOManagerError
 module E = Exit isBearerClosed
 module PS = Supervision isIOManagerError
 module GP = PS.GP
 module Q = Lower isIOManagerError
 module History = ReturnHistory GP.Body

view : K.State → Q.View
view s = Q.view (K.peers s)

-- Shared Server/CM work cannot write the peer completion queue. Actual peer
-- actions inherit the total lower classification, with all original guards.
shared-change : ∀ a s {t} → K.step a s ≡ just t → Q.Change (view s) (view t)
shared-change (K.serverStep a) s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → Q.kept refl }
shared-change (K.coreStep a) s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → Q.kept refl }
shared-change (K.peerStep a) s eq with K.peerOpen s | K.peerAllowed a s
... | Data.Bool.false | _ = case eq of λ ()
... | Data.Bool.true | Data.Bool.false = case eq of λ ()
... | Data.Bool.true | Data.Bool.true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → Q.supervision-change a (K.peers s) advanced }

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate
 runtime-view : T.Runtime → Q.View
 runtime-view s = view (T.base s)

 -- Local protocol caching updates peer cells; it cannot publish an OG result.
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
 enact-change : ∀ plan s {t} → T.enact plan s ≡ just t → Q.Change (runtime-view s) (runtime-view t)
 enact-change (T.inherit a f) s eq with K.step a (T.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → shared-change a (T.base s) advanced }
 enact-change (T.caller a f) s eq with PS.step a (K.peers (T.base s)) in advanced
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → Q.supervision-change a (K.peers (T.base s)) advanced }
 enact-change (T.local f) s eq = case just-injective eq of λ { refl → Q.kept refl }
 enact-change (T.reading r) s eq = case just-injective eq of λ { refl → Q.kept refl }
 enact-change (T.traceFault w rid result fs) s eq = case just-injective eq of λ { refl → Q.kept refl }
 enact-change (T.deliverTraceFault w rid result fs coordinator) s eq = case just-injective eq of λ { refl → Q.kept refl }
 enact-change (T.birth w capturedFrame pool j rid r f) s eq = case just-injective eq of λ { refl → Q.kept refl }
 enact-change (T.complete a rid r result) s eq with K.step a (T.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → Q.right-view (sym (cache-view rid r result (T.front s) b)) (shared-change a (T.base s) advanced) }
 advance-change : ∀ a s {t} → T.advance a s ≡ just t → Q.Change (runtime-view s) (runtime-view t)
 advance-change a s eq with T.choose a s
 ... | nothing = case eq of λ ()
 ... | just plan = enact-change plan s eq

 -- Prefix and suffix histories anchor the publication on an execution from
 -- the same initializer to the queried state, retaining its original job/body.
 record Origin (start current : T.Runtime) (result : G.Completion) : Set where
  constructor origin
  field
   before after : T.Runtime
   prefix suffix : List T.Event
   event : T.Event
   reached : T.Runs start prefix before
   advanced : T.advance event before ≡ just after
   continued : T.Runs after suffix current
   published : Q.Publication (runtime-view before) result
   appended : Q.View.pending (runtime-view after) ≡ Q.View.pending (runtime-view before) ++ (result ∷ [])
   poolStep : GP.Pool.step (GP.Pool.publishCompletion (Q.Publication.job published))
     (Q.View.pool (runtime-view before)) ≡ just (Q.View.pool (runtime-view after))
 Backed : T.Runtime → T.Runtime → Set
 Backed start current = All (Origin start current) (Q.View.pending (runtime-view current))

 -- Every existing history extends through the next actual frontend event.
 extend-origin : ∀ {start s t result a} → T.advance a s ≡ just t → Origin start s result → Origin start t result
 extend-origin {a = a} eq (origin before after prefix suffix event reached advanced continued published appended poolStep) =
  origin before after prefix (suffix ++ (a ∷ [])) event reached advanced
   (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate continued (T.more {a = a} eq T.stop)) published appended poolStep
 step-backed : ∀ {start prefix s t} a → T.Runs start prefix s → T.advance a s ≡ just t → Backed start s → Backed start t
 step-backed {start} {prefix} {s} {t} a reached advanced backed with advance-change a s advanced
 ... | Q.kept same = subst (All (Origin start t)) (sym same) (All.map (extend-origin {a = a} advanced) backed)
 ... | Q.taken result rest fifo tail with subst (All (Origin start s)) fifo backed
 ...   | history ∷ histories = subst (All (Origin start t)) (sym tail) (All.map (extend-origin {a = a} advanced) histories)
 step-backed {start} {prefix} {s} {t} a reached advanced backed | Q.added result published appended poolStep =
  subst (All (Origin start t)) (sym appended)
   (++⁺ (All.map (extend-origin {a = a} advanced) backed) (origin s t prefix [] a reached advanced T.stop published appended poolStep ∷ []))
 run-backed : ∀ {start prefix s suffix t} → T.Runs start prefix s → Backed start s → T.Runs s suffix t → Backed start t
 run-backed reached backed T.stop = backed
 run-backed {prefix = prefix} reached backed (T.more {a = a} eq rest) = run-backed
  (Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate reached (T.more {a = a} eq T.stop)) (step-backed a reached eq backed) rest
 initialized-backed : ∀ {c g start actions s} → T.initialize c g ≡ just start → T.Runs start actions s → Backed start s
 initialized-backed {c} {g} initialized path with E.initial c
 ... | nothing = case initialized of λ ()
 ... | just e with just-injective initialized
 ...   | refl = run-backed T.stop [] path

 -- Each queried FIFO member has an actual historical publication, not merely
 -- a matching arbitrary logical frame or a guessed current-generation result.
 member-backed : ∀ {start current result} → Backed start current → result ∈ Q.View.pending (runtime-view current) → Origin start current result
 member-backed backed member = All.lookup backed member
 initialized-pending : ∀ {c g start actions s result} → T.initialize c g ≡ just start → T.Runs start actions s →
  result ∈ Q.View.pending (runtime-view s) → Origin start s result
 initialized-pending initialized path member = member-backed (initialized-backed initialized path) member
 initialized-consumed : ∀ {c g start actions s t} → T.initialize c g ≡ just start → T.Runs start actions s →
  (advanced : T.advance (T.dispatch (K.peerStep (PS.run (GP.run Sub.selectCompletion)))) s ≡ just t) →
  Origin start s (Continuations.CompletionSelection.result
    (proj₁ (Continuations.Frontend.selected-completion isBearerClosed isIOManagerError canInitiate s t advanced)))
 initialized-consumed {start = start} {s = s} {t} initialized path advanced
  with proj₁ (Continuations.Frontend.selected-completion isBearerClosed isIOManagerError canInitiate s t advanced)
 ... | selected with subst (All (Origin start s)) (Continuations.CompletionSelection.fifo selected) (initialized-backed initialized path)
 ...   | history ∷ histories = history

 -- The projection is an actual primitive pool execution from its empty
 -- initializer, not an assumption that an arbitrary returned cell is genuine.
 initialized-pool-prefix : ∀ {c g start actions s} → T.initialize c g ≡ just start → T.Runs start actions s →
  Σ (List GP.Pool.Action) (λ poolActions → GP.Pool.Executes GP.Pool.initial poolActions (Q.View.pool (runtime-view s)))
 initialized-pool-prefix {c} initialized path with E.initial c
 ... | nothing = case initialized of λ ()
 ... | just e with just-injective initialized
 ...   | refl = Projection.Paths.governor
   (Shared.Protocols.run-projects isBearerClosed isIOManagerError canInitiate path)
 origin-returned : ∀ {c g start current result} → T.initialize c g ≡ just start →
  (history : Origin start current result) → History.Returned GP.Pool.initial
   (Q.Publication.job (Origin.published history)) (Q.Publication.payload (Origin.published history))
   (Q.View.pool (runtime-view (Origin.before history)))
 origin-returned initialized history with initialized-pool-prefix initialized (Origin.reached history)
 ... | poolActions , prefix = History.from-initial prefix (Q.Publication.job (Origin.published history))
   (Q.Publication.payload (Origin.published history)) (Q.Publication.returned (Origin.published history))
 origin-agreement : ∀ {start current result} (history : Origin start current result) →
  GP.identity (Q.Publication.payload (Origin.published history)) ≡ Q.Publication.job (Origin.published history) ×
  GP.work (Q.Publication.payload (Origin.published history)) ≡ G.work result ×
  GP.outcome (Q.Publication.payload (Origin.published history)) ≡ G.outcome result
 origin-agreement history = Q.publication-agreement _ _ (Origin.published history)

 -- Keep the same publication witness after its queue entry has been consumed.
 extend-through : ∀ {start s actions t result} → T.Runs s actions t → Origin start s result → Origin start t result
 extend-through T.stop history = history
 extend-through (T.more {a = a} advanced rest) history = extend-through rest (extend-origin {a = a} advanced history)
 origin-returned-current : ∀ {c g start current result} → T.initialize c g ≡ just start →
  (history : Origin start current result) → History.Returned GP.Pool.initial
   (Q.Publication.job (Origin.published history)) (Q.Publication.payload (Origin.published history)) (Q.View.pool (runtime-view current))
 origin-returned-current initialized history with Projection.Paths.governor
  (Shared.Protocols.run-projects isBearerClosed isIOManagerError canInitiate
    (T.more {a = Origin.event history} (Origin.advanced history) (Origin.continued history)))
 ... | poolActions , suffix = History.extend suffix (origin-returned initialized history)

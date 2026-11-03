{-# OPTIONS --guardedness #-}
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersDeactivation (isBearerClosed isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List.Relation.Unary.All using (All)
open import ConnectionManagement.IGTypes using (clean)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Properties.ServerPeersResults as Readers
import ConnectionManagement.Properties.ServerPeersCache as Captures
import ConnectionManagement.Properties.ServerPeers as Shared
import ConnectionManagement.Properties.ServerPeersContinuations as Continuations
import ConnectionManagement.Properties.ServerPeersCompletions as Completions
import ConnectionManagement.Properties.GovernorCompletions as QueueFacts
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Subsystem as Sub
import Data.Empty
import ConnectionManagement.Properties.PeerJobControl as Control
import ConnectionManagement.Properties.PeerJobFrames as FrameFacts
import ConnectionManagement.Properties.ServerPeersJobFrames as FrontFacts
private
 module K = Combined isBearerClosed isIOManagerError
 module Root = Continuations isBearerClosed isIOManagerError
 module E = Exit isBearerClosed
 module PS = Supervision isIOManagerError
 module GP = PS.GP
 module F = FrameFacts isIOManagerError
 module Adapter = FrontFacts isBearerClosed isIOManagerError
 module Queue = QueueFacts isIOManagerError
 module CompletionOrigins = Completions isBearerClosed isIOManagerError

-- This functional store invariant needs neither unique keys nor a supply premise.
write-valid : ∀ (P : JobId → Sub.JobFrame → Set) k row xs → P k row →
 (∀ j f → lookup j xs ≡ just f → P j f) →
 ∀ j f → lookup j (put k row xs) ≡ just f → P j f
write-valid P k row xs valid retained j f found with j ≟ k
... | yes refl = subst (P k) (just-injective (trans (sym (lookup-put k row xs)) found)) valid
... | no apart = retained j f (trans (sym (lookup-put-other k j row xs apart)) found)

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate
  module A = Adapter.Frontend canInitiate
  module Cont = Continuations.Frontend isBearerClosed isIOManagerError canInitiate
  module Origins = CompletionOrigins.Frontend canInitiate
  module Read = Readers.Observations isBearerClosed isIOManagerError canInitiate
  module Physical = Captures.Frontend isBearerClosed isIOManagerError canInitiate
  append = Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate
 rows : T.Runtime → Store JobId Sub.JobFrame
 rows s = F.View.rows (A.runtime-view s)
 peers : T.Runtime → Peer.Runtime
 peers s = F.View.peers (A.runtime-view s)

 -- Certificates retain the exact physical handle/mux/protocol and capture
 -- history of every observed local clean result, including retired runs.
 CleanReads : ∀ {j s t} → Cont.JobAgreement j s t → Set
 CleanReads {s = s} agreement = All (λ { (n , observation) → Physical.Historical s
   (J.connectionRef (Sub.execution (Read.JobRead.frame (Cont.job-reader agreement))))
   (Peer.handleRef (Read.JobRead.peer (Cont.job-reader agreement)))
   (Peer.muxRef (Read.JobRead.peer (Cont.job-reader agreement))) n clean })
   (Read.JobRead.results (Cont.job-reader agreement))

 -- The early return retains the exact captured frame, Warm peer, actual plan
 -- and logical body step. A waited return carries the initialized physical-read
 -- agreement and the completed row from that same frontend transition.
 data Cause (j : JobId) (work : G.Job) (s t : T.Runtime) (event : T.Event) (plan : T.Plan) : Set where
  alreadyWarm : ∀ old next w w′ peer →
   lookup j (rows s) ≡ just old → J.peers w ≡ peers s →
   J.step J.enter (Sub.execution old) w ≡ just (next , w′) →
   A.planTag plan ≡ F.jobStep j J.enter →
   J.pc (Sub.execution old) ≡ J.begin →
   lookup (J.connectionRef (Sub.execution old)) (J.peers w) ≡ just peer →
   Peer.status peer ≡ Peer.peerWarm →
   J.work next ≡ work → J.pc next ≡ J.complete G.succeeded →
   lookup j (rows t) ≡ just (record old { execution = next }) → Cause j work s t event plan
  cleanWait : ∀ old returned → lookup j (rows s) ≡ just old → J.pc (Sub.execution old) ≡ J.awaitHot → event ≡ T.waitJobResults j → (agreement : Cont.JobAgreement j s t) → CleanReads agreement →
   lookup j (rows t) ≡ just returned → J.pc (Sub.execution returned) ≡ J.complete G.succeeded →
   J.work (Sub.execution returned) ≡ work → Cause j work s t event plan
 record History (start current : T.Runtime) (j : JobId) (work : G.Job) : Set where
  constructor history
  field before after : T.Runtime
        prefix suffix : List T.Event
        event : T.Event
        plan : T.Plan
        reached : T.Runs start prefix before
        advanced : T.advance event before ≡ just after
        continued : T.Runs after suffix current
        chosen : T.choose event before ≡ just plan
        cause : Cause j work before after event plan
 extend : ∀ {start s t j work a} → T.advance a s ≡ just t → History start s j work → History start t j work
 extend {a = a} eq (history before after prefix suffix event plan reached advanced continued chosen cause) =
  history before after prefix (suffix ++ (a ∷ [])) event plan reached advanced
   (append continued (T.more {a = a} eq T.stop)) chosen cause
 extend-through : ∀ {start s t j work actions} → T.Runs s actions t → History start s j work → History start t j work
 extend-through T.stop h = h
 extend-through (T.more {a = a} eq rest) h = extend-through rest (extend {a = a} eq h)

 RowValid : T.Runtime → T.Runtime → JobId → J.Frame → Set
 RowValid start current j f = G.kind (J.work f) ≡ G.deactivate →
  Control.DeactivatePC (J.pc f) × (J.pc f ≡ J.complete G.succeeded → History start current j (J.work f))
 Valid : T.Runtime → T.Runtime → Set
 Valid start current = ∀ j row → lookup j (rows current) ≡ just row → RowValid start current j (Sub.execution row)
 advance-row : ∀ {start s t j f a} → T.advance a s ≡ just t → RowValid start s j f → RowValid start t j f
 advance-row {a = a} eq valid kind = proj₁ (valid kind) , (λ success → extend {a = a} eq (proj₂ (valid kind) success))
 initial-row : ∀ {start current j f} → J.pc f ≡ J.begin → RowValid start current j f
 initial-row pc kind = subst Control.DeactivatePC (sym pc) Control.initial-PC , (λ success → case trans (sym pc) success of λ ())
 failed-row : ∀ {start current j f old} → f ≡ record old { pc = J.awaitCold G.failed } → RowValid start current j f
 failed-row refl kind = Control.failed-PC , (λ ())
 no-establishment : ∀ {pc} → Control.DeactivatePC pc → pc ≡ J.forkMonitor → Data.Empty.⊥
 no-establishment Control.initial-PC ()
 no-establishment Control.hot-PC ()
 no-establishment Control.failed-PC ()
 no-establishment (Control.done-PC outcome) ()

 -- Lift one actual body transition, retaining its real frontend event.
 tick-row : ∀ {c g start prefix s t event plan} j a old next w w′ →
  T.initialize c g ≡ just start → T.Runs start prefix s → T.advance event s ≡ just t →
  T.choose event s ≡ just plan → A.Permit event s plan →
  lookup j (rows s) ≡ just old → J.peers w ≡ peers s →
  J.step a (Sub.execution old) w ≡ just (next , w′) →
  rows t ≡ put j (record old { execution = next }) (rows s) →
  A.planTag plan ≡ F.jobStep j a → RowValid start s j (Sub.execution old) → RowValid start t j next
 tick-row {start = start} {prefix} {s} {t} {event} {plan} j a old next w w′ initialized reached advanced chosen permitted found world stepped table tag valid kind =
  proj₁ progress , (λ success → history s t prefix [] event plan reached advanced T.stop chosen (explain success (proj₂ progress success)))
  where
  sameWork = Control.step-work a (Sub.execution old) w stepped
  oldKind = trans (sym (cong G.kind sameWork)) kind
  progress = Control.deact-progress a (Sub.execution old) w oldKind (proj₁ (valid oldKind)) stepped
  nextFound : lookup j (rows t) ≡ just (record old { execution = next })
  nextFound = trans (cong (lookup j) table) (lookup-put j (record old { execution = next }) (rows s))
  explain : J.pc next ≡ J.complete G.succeeded → Control.Success a (Sub.execution old) w →
    Cause j (J.work next) s t event plan
  explain success (Control.early-warm peer refl atPC peerFound warm) = alreadyWarm old next w w′ peer
    found world stepped tag atPC peerFound warm refl success nextFound
  explain success (Control.hot-wait refl atPC) = cleanWait old (record old { execution = next }) found atPC eventEq
    agreement (Cont.job-success-captures j s t agreement (record old { execution = next }) nextFound
      (subst (λ pc → Root.finished pc ≡ true) (sym success) refl)) nextFound success refl
    where
    eventEq = A.Permit.hot permitted j tag
    agreement = Cont.initialized-job-agreement j initialized reached
      (subst (λ ev → T.advance ev s ≡ just t) eventEq advanced)

 step-effect : ∀ {c g start prefix s t event plan} →
  T.initialize c g ≡ just start → T.Runs start prefix s → T.advance event s ≡ just t →
  T.choose event s ≡ just plan → A.Permit event s plan →
  F.Effect (A.planTag plan) (A.runtime-view s) (A.runtime-view t) → Valid start s → Valid start t
 step-effect {s = s} {t} {event} initialized reached advanced chosen permitted (F.same table) valid j row found =
  advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid j row (trans (sym (cong (lookup j) table)) found))
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.born k next pc table) valid j row found =
  write-valid (λ k row → RowValid start t k (Sub.execution row)) k next (rows s) (initial-row {f = Sub.execution next} pc)
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) found)
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.flags k old next found exec table) valid j row selected =
  write-valid (λ k row → RowValid start t k (Sub.execution row)) k next (rows s)
   (subst (RowValid start t k) (sym exec) (advance-row {s = s} {t = t} {f = Sub.execution old} {a = event} advanced (valid k old found)))
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) selected)
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.tick k a old next w w′ found world shared stepped table tag) valid j row selected =
  write-valid (λ k row → RowValid start t k (Sub.execution row)) k (record old { execution = next }) (rows s)
   (tick-row k a old next w w′ initialized reached advanced chosen permitted found world stepped table tag (valid k old found))
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) selected)
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.established k old next found pc work table) valid j row selected =
  write-valid (λ k row → RowValid start t k (Sub.execution row)) k next (rows s)
   (λ kind → Data.Empty.⊥-elim (no-establishment (proj₁ (valid k old found (trans (sym (cong G.kind work)) kind))) pc))
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) selected)
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.failed k old next found exec table) valid j row selected =
  write-valid (λ k row → RowValid start t k (Sub.execution row)) k next (rows s) (failed-row {f = Sub.execution next} {old = Sub.execution old} exec)
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) selected)

 step-valid : ∀ {c g start prefix s t} event → T.initialize c g ≡ just start → T.Runs start prefix s →
  T.advance event s ≡ just t → Valid start s → Valid start t
 advance-enact : ∀ event s plan → T.choose event s ≡ just plan → T.advance event s ≡ T.enact plan s
 advance-enact event s plan chosen rewrite chosen = refl
 step-valid {s = s} {t} event initialized reached advanced valid with T.choose event s in chosen
 ... | nothing = case advanced of λ ()
 ... | just plan = step-effect initialized reached (trans (advance-enact event s plan chosen) advanced) chosen (A.permit-choose-change event s plan chosen)
   (A.enact-change plan s (A.Permit.reading (A.permit-choose-change event s plan chosen)) advanced) valid
 run-valid : ∀ {c g start prefix s suffix t} → T.initialize c g ≡ just start → T.Runs start prefix s →
  Valid start s → T.Runs s suffix t → Valid start t
 run-valid initialized reached valid T.stop = valid
 run-valid {prefix = prefix} initialized reached valid (T.more {a = a} eq rest) = run-valid initialized
  (append reached (T.more {a = a} eq T.stop)) (step-valid a initialized reached eq valid) rest
 initial-empty : ∀ {c g start} → T.initialize c g ≡ just start → rows start ≡ []
 initial-empty {c} initialized with E.initial c
 ... | nothing = case initialized of λ ()
 ... | just e with just-injective initialized
 ...   | refl = refl
 initialized-valid : ∀ {c g start actions current} → T.initialize c g ≡ just start → T.Runs start actions current → Valid start current
 initialized-valid initialized path = run-valid initialized T.stop
  (λ j row found → case trans (sym (cong (lookup j) (initial-empty initialized))) found of λ ()) path

 -- Completion provenance supplies the exact historical row; apply the frame
 -- invariant there, then retain the same success history past publication.
 origin-success : ∀ {c g start current result} → T.initialize c g ≡ just start →
  (publicationHistory : Origins.Origin start current result) → G.kind (G.work result) ≡ G.deactivate →
  G.outcome result ≡ G.succeeded → History start current (Queue.Publication.job (Origins.Origin.published publicationHistory)) (G.work result)
 origin-success initialized publicationHistory deactivation success = extend-through
  (T.more {a = Origins.Origin.event publicationHistory} (Origins.Origin.advanced publicationHistory) (Origins.Origin.continued publicationHistory))
  (subst (History _ _ _) work (proj₂ (initialized-valid initialized (Origins.Origin.reached publicationHistory) j row found
   (trans (cong G.kind work) deactivation)) (trans completed (cong J.complete success))))
  where
  publication = Origins.Origin.published publicationHistory
  j = Queue.Publication.job publication
  row = Queue.Publication.frame publication
  found = Queue.Publication.found publication
  work = Queue.Publication.work publication
  completed = Queue.Publication.completed publication

 -- The selected source head inherits exactly its initialized publication's
 -- success history; consumption itself performs no protocol-result read.
 consumed-success : ∀ {c g start actions s t} (initialized : T.initialize c g ≡ just start)
  (path : T.Runs start actions s)
  (selected : T.advance (T.dispatch (K.peerStep (PS.run (GP.run Sub.selectCompletion)))) s ≡ just t) →
  let publicationHistory = Origins.initialized-consumed initialized path selected
      result = Continuations.CompletionSelection.result
        (proj₁ (Cont.selected-completion s t selected))
  in G.kind (G.work result) ≡ G.deactivate → G.outcome result ≡ G.succeeded →
   History start s (Queue.Publication.job (Origins.Origin.published publicationHistory)) (G.work result)
 consumed-success initialized path selected = origin-success initialized (Origins.initialized-consumed initialized path selected)

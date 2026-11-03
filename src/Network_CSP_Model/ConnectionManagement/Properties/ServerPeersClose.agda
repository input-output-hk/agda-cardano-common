{-# OPTIONS --guardedness #-}
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersClose (isBearerClosed isIOManagerError : ErrorId → Bool) where
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
import Data.Sum
import ConnectionManagement.Properties.PeerJobControl as WorkFacts
import ConnectionManagement.Properties.PeerJobCloseControl as Control
import ConnectionManagement.Properties.ServerPeersDeactivation as Deactivation
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundRelease as R
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
 module Deact = Deactivation isBearerClosed isIOManagerError

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate
  module A = Adapter.Frontend canInitiate
  module Cont = Continuations.Frontend isBearerClosed isIOManagerError canInitiate
  module Origins = CompletionOrigins.Frontend canInitiate
  module D = Deact.Frontend canInitiate
  append = Shared.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate
 rows = D.rows
 peers = D.peers

 -- One actual body operation, located in an initialized prefix and a suffix to
 -- the queried state. Its world projects the real shared CM and peer rows.
 record Step (start current : T.Runtime) (j : JobId) (work : G.Job) (action : J.Action) : Set where
  constructor bodyStep
  field before after : T.Runtime
        prefix suffix : List T.Event
        event : T.Event
        plan : T.Plan
        reached : T.Runs start prefix before
        advanced : T.advance event before ≡ just after
        continued : T.Runs after suffix current
        chosen : T.choose event before ≡ just plan
        old : Sub.JobFrame
        next : J.Frame
        world world′ : J.World
        found : lookup j (rows before) ≡ just old
        peerWorld : J.peers world ≡ peers before
        sharedWorld : J.cm world ≡ F.View.cm (A.runtime-view before)
        stepped : J.step action (Sub.execution old) world ≡ just (next , world′)
        tag : A.planTag plan ≡ F.jobStep j action
        oldWork : J.work (Sub.execution old) ≡ work
        nextWork : J.work next ≡ work
        nextFound : lookup j (rows after) ≡ just (record old { execution = next })
 extend-step : ∀ {start s t j work action event} → T.advance event s ≡ just t → Step start s j work action → Step start t j work action
 extend-step {event = event} eq (bodyStep before after prefix suffix selected plan reached advanced continued chosen old next w w′ found peerWorld sharedWorld stepped tag oldWork nextWork nextFound) =
  bodyStep before after prefix (suffix ++ (event ∷ [])) selected plan reached advanced
   (append continued (T.more {a = event} eq T.stop)) chosen old next w w′ found peerWorld sharedWorld stepped tag oldWork nextWork nextFound

 -- The clean all-temperature wait is certified against actual physical reads.
 record Waited (start current : T.Runtime) (j : JobId) (work : G.Job) : Set where
  constructor waited
  field step : Step start current j work J.observeAll
        atAll : J.pc (Sub.execution (Step.old step)) ≡ J.awaitAll
        atCall : J.pc (Step.next step) ≡ J.callRelease
        actualWait : Step.event step ≡ T.waitJobResults j
        agreement : Cont.JobAgreement j (Step.before step) (Step.after step)
        captures : D.CleanReads agreement
 record Requested (start current : T.Runtime) (j : JobId) (work : G.Job) : Set where
  constructor requested
  field step : Step start current j work J.requestRelease
        cleanWait : Waited start (Step.before step) j work
        atCall : J.pc (Sub.execution (Step.old step)) ≡ J.callRelease
        atRelease : J.pc (Step.next step) ≡ J.awaitRelease
        peer : Peer.Peer
        cmAfter : CM.Configuration
        peerFound : lookup (J.connectionRef (Sub.execution (Step.old step))) (J.peers (Step.world step)) ≡ just peer
        cmRequest : CM.advance (CM.beginRelease (J.caller (Sub.execution (Step.old step))) (Peer.key peer))
          (J.cm (Step.world step)) ≡ just cmAfter
 -- Unsupported and success results are retained separately; assertion failure
 -- does not enter the successful Cold wait.
 data Accepted (f : J.Frame) (w : J.World) : Set where
  success-result : ∀ state → lookup (J.caller f) (CM.released (J.cm w)) ≡ just (R.success state) → Accepted f w
  unsupported-result : ∀ state → lookup (J.caller f) (CM.released (J.cm w)) ≡ just (R.unsupported state) → Accepted f w
 record Released (start current : T.Runtime) (j : JobId) (work : G.Job) : Set where
  constructor released
  field step : Step start current j work J.collectRelease
        request : Requested start (Step.before step) j work
        atRelease : J.pc (Sub.execution (Step.old step)) ≡ J.awaitRelease
        atCold : J.pc (Step.next step) ≡ J.awaitCold G.succeeded
        result : Accepted (Sub.execution (Step.old step)) (Step.world step)
 data Route (start current : T.Runtime) (j : JobId) (work : G.Job) : Set where
  entry : (step : Step start current j work J.enter) →
   J.pc (Sub.execution (Step.old step)) ≡ J.begin → J.pc (Step.next step) ≡ J.awaitCold G.succeeded →
   ∀ peer → lookup (J.connectionRef (Sub.execution (Step.old step))) (J.peers (Step.world step)) ≡ just peer →
   (Peer.status peer ≡ Peer.peerCold Data.Sum.⊎ Peer.status peer ≡ Peer.peerCooling) → Route start current j work
  timeout : (step : Step start current j work J.operationTimeout) →
   J.pc (Sub.execution (Step.old step)) ≡ J.awaitAll → J.pc (Step.next step) ≡ J.awaitCold G.succeeded → Route start current j work
  release : Released start current j work → Route start current j work
 record History (start current : T.Runtime) (j : JobId) (work : G.Job) : Set where
  constructor closed
  field step : Step start current j work J.observeCold
        route : Route start (Step.before step) j work
        atCold : J.pc (Sub.execution (Step.old step)) ≡ J.awaitCold G.succeeded
        atSuccess : J.pc (Step.next step) ≡ J.complete G.succeeded
        peer : Peer.Peer
        peerFound : lookup (J.connectionRef (Sub.execution (Step.old step))) (J.peers (Step.world step)) ≡ just peer
        cold : Peer.status peer ≡ Peer.peerCold

 -- Extending a history changes only the suffix of its last actual operation.
 extend-wait : ∀ {start s t j work event} → T.advance event s ≡ just t → Waited start s j work → Waited start t j work
 extend-wait {event = event} eq (waited h atAll atCall actual agreement captures) = waited (extend-step {event = event} eq h) atAll atCall actual agreement captures
 extend-request : ∀ {start s t j work event} → T.advance event s ≡ just t → Requested start s j work → Requested start t j work
 extend-request {event = event} eq (requested h cleanWait atCall atRelease peer cmAfter found request) = requested (extend-step {event = event} eq h) cleanWait atCall atRelease peer cmAfter found request
 extend-release : ∀ {start s t j work event} → T.advance event s ≡ just t → Released start s j work → Released start t j work
 extend-release {event = event} eq (released h request atRelease atCold result) = released (extend-step {event = event} eq h) request atRelease atCold result
 extend-route : ∀ {start s t j work event} → T.advance event s ≡ just t → Route start s j work → Route start t j work
 extend-route {event = event} eq (entry h atBegin atCold peer found status) = entry (extend-step {event = event} eq h) atBegin atCold peer found status
 extend-route {event = event} eq (timeout h atAll atCold) = timeout (extend-step {event = event} eq h) atAll atCold
 extend-route {event = event} eq (release h) = release (extend-release {event = event} eq h)
 extend : ∀ {start s t j work event} → T.advance event s ≡ just t → History start s j work → History start t j work
 extend {event = event} eq (closed h route atCold atSuccess peer found cold) = closed (extend-step {event = event} eq h) route atCold atSuccess peer found cold
 extend-through : ∀ {start s t j work actions} → T.Runs s actions t → History start s j work → History start t j work
 extend-through T.stop h = h
 extend-through (T.more {a = event} eq rest) h = extend-through rest (extend {event = event} eq h)

 -- Progress is derived for every stored close frame, not assumed by consumers.
 data Progress (start current : T.Runtime) (j : JobId) (work : G.Job) : J.PC → Set where
  initial-PC : Progress start current j work J.begin
  all-PC : Progress start current j work J.awaitAll
  call-PC : Waited start current j work → Progress start current j work J.callRelease
  release-PC : Requested start current j work → Progress start current j work J.awaitRelease
  cold-PC : ∀ result → (result ≡ G.succeeded → Route start current j work) → Progress start current j work (J.awaitCold result)
  done-PC : ∀ result → (result ≡ G.succeeded → History start current j work) → Progress start current j work (J.complete result)
 control : ∀ {start current j work pc} → Progress start current j work pc → Control.ClosePC pc
 control initial-PC = Control.initial-PC
 control all-PC = Control.all-PC
 control (call-PC _) = Control.call-PC
 control (release-PC _) = Control.release-PC
 control (cold-PC result _) = Control.cold-PC result
 control (done-PC result _) = Control.done-PC result
 extend-progress : ∀ {start s t j work pc event} → T.advance event s ≡ just t → Progress start s j work pc → Progress start t j work pc
 extend-progress eq initial-PC = initial-PC
 extend-progress eq all-PC = all-PC
 extend-progress {event = event} eq (call-PC h) = call-PC (extend-wait {event = event} eq h)
 extend-progress {event = event} eq (release-PC h) = release-PC (extend-request {event = event} eq h)
 extend-progress {event = event} eq (cold-PC result h) = cold-PC result (λ success → extend-route {event = event} eq (h success))
 extend-progress {event = event} eq (done-PC result h) = done-PC result (λ success → extend {event = event} eq (h success))
 RowValid : T.Runtime → T.Runtime → JobId → J.Frame → Set
 RowValid start current j f = G.kind (J.work f) ≡ G.close → Progress start current j (J.work f) (J.pc f)
 Valid : T.Runtime → T.Runtime → Set
 Valid start current = ∀ j row → lookup j (rows current) ≡ just row → RowValid start current j (Sub.execution row)
 initial-row : ∀ {start current j f} → J.pc f ≡ J.begin → RowValid start current j f
 initial-row eq kind = subst (Progress _ _ _ _) (sym eq) initial-PC
 failed-row : ∀ {start current j f old} → f ≡ record old { pc = J.awaitCold G.failed } → RowValid start current j f
 failed-row refl kind = cold-PC G.failed (λ ())
 advance-row : ∀ {start s t j f a} → T.advance a s ≡ just t → RowValid start s j f → RowValid start t j f
 advance-row {a = a} eq valid kind = extend-progress {event = a} eq (valid kind)
 no-establishment : ∀ {pc} → Control.ClosePC pc → pc ≡ J.forkMonitor → Data.Empty.⊥
 no-establishment Control.initial-PC ()
 no-establishment Control.all-PC ()
 no-establishment Control.call-PC ()
 no-establishment Control.release-PC ()
 no-establishment (Control.cold-PC _) ()
 no-establishment (Control.done-PC _) ()

 -- Accessors use exact PCs, so an activation or failure continuation cannot
 -- be substituted for an actual close stage.
 get-call : ∀ {start current j work pc} → Progress start current j work pc → pc ≡ J.callRelease → Waited start current j work
 get-call p refl with p
 ... | call-PC h = h
 get-request : ∀ {start current j work pc} → Progress start current j work pc → pc ≡ J.awaitRelease → Requested start current j work
 get-request p refl with p
 ... | release-PC h = h
 get-cold : ∀ {start current j work pc result} → Progress start current j work pc → pc ≡ J.awaitCold result → result ≡ G.succeeded → Route start current j work
 get-cold p refl success with p
 ... | cold-PC _ h = h success
 get-success : ∀ {start current j work pc} → Progress start current j work pc → pc ≡ J.complete G.succeeded → History start current j work
 get-success p refl with p
 ... | done-PC _ h = h refl

 -- Each new stage is anchored to the actual selected operation; previous
 -- stages retain suffixes ending at this operation's before-state.
 tick-row : ∀ {c g start prefix s t event plan} j a old next w w′ →
  T.initialize c g ≡ just start → T.Runs start prefix s → T.advance event s ≡ just t →
  T.choose event s ≡ just plan → A.Permit event s plan →
  lookup j (rows s) ≡ just old → J.peers w ≡ peers s → J.cm w ≡ F.View.cm (A.runtime-view s) →
  J.step a (Sub.execution old) w ≡ just (next , w′) →
  rows t ≡ put j (record old { execution = next }) (rows s) →
  A.planTag plan ≡ F.jobStep j a → RowValid start s j (Sub.execution old) → RowValid start t j next
 tick-row {start = start} {prefix} {s} {t} {event} {plan} j a old next w w′ initialized reached advanced chosen permitted found peerWorld sharedWorld stepped table tag valid kind =
  subst (λ work → Progress start t j work (J.pc next)) (sym sameWork)
    (explain (Control.classify a (Sub.execution old) w oldKind (control previous) stepped))
  where
  sameWork = WorkFacts.step-work a (Sub.execution old) w stepped
  oldKind = trans (sym (cong G.kind sameWork)) kind
  previous = valid oldKind
  nextFound : lookup j (rows t) ≡ just (record old { execution = next })
  nextFound = trans (cong (lookup j) table) (lookup-put j (record old { execution = next }) (rows s))
  make-step : ∀ {action} → a ≡ action → Step start t j (J.work (Sub.execution old)) action
  make-step refl = bodyStep s t prefix [] event plan reached advanced T.stop chosen old next w w′
    found peerWorld sharedWorld stepped tag refl sameWork nextFound
  at-next : ∀ {pc} → J.pc next ≡ pc → Progress start t j (J.work (Sub.execution old)) pc →
    Progress start t j (J.work (Sub.execution old)) (J.pc next)
  at-next pc progress = subst (Progress start t j (J.work (Sub.execution old))) (sym pc) progress
  explain : Control.Move a (Sub.execution old) w next → Progress start t j (J.work (Sub.execution old)) (J.pc next)
  explain (Control.entry-skip p refl begin cold foundPeer status) = at-next cold
    (cold-PC G.succeeded (λ _ → entry (make-step refl) begin cold p foundPeer status))
  explain (Control.entry-wait refl begin all) = at-next all all-PC
  explain (Control.clean-all refl all call) = at-next call (call-PC
    (waited (make-step refl) all call eventEq agreement
      (Cont.job-success-captures j s t agreement (record old { execution = next }) nextFound
        (subst (λ pc → Root.finished pc ≡ true) (sym call) refl))))
    where
    eventEq = A.Permit.allResults permitted j tag
    agreement = Cont.initialized-job-agreement j initialized reached
      (subst (λ ev → T.advance ev s ≡ just t) eventEq advanced)
  explain (Control.failed-all refl all cold) = at-next cold (cold-PC G.failed (λ ()))
  explain (Control.requested p c refl call releaseEq foundPeer cmStep) = at-next releaseEq (release-PC
    (requested (make-step refl) (get-call previous call) call releaseEq p c foundPeer cmStep))
  explain (Control.collected-success state refl releasePC cold foundResult) = at-next cold
    (cold-PC G.succeeded (λ _ → release (released (make-step refl) (get-request previous releasePC)
      releasePC cold (success-result state foundResult))))
  explain (Control.collected-unsupported state refl releasePC cold foundResult) = at-next cold
    (cold-PC G.succeeded (λ _ → release (released (make-step refl) (get-request previous releasePC)
      releasePC cold (unsupported-result state foundResult))))
  explain (Control.collected-failure refl releasePC cold) = at-next cold (cold-PC G.failed (λ ()))
  explain (Control.operation-expired refl all cold) = at-next cold
    (cold-PC G.succeeded (λ _ → timeout (make-step refl) all cold))
  explain (Control.observed-cold result p refl cold completed foundPeer status) = at-next completed
    (done-PC result (λ success → closed (make-step refl) (get-cold previous cold success)
      (trans cold (cong J.awaitCold success)) (trans completed (cong J.complete success)) p foundPeer status))
  explain (Control.demotion-expired result refl cold completed) = at-next completed
    (done-PC G.demotionTimedOut (λ ()))
 step-effect : ∀ {c g start prefix s t event plan} →
  T.initialize c g ≡ just start → T.Runs start prefix s → T.advance event s ≡ just t →
  T.choose event s ≡ just plan → A.Permit event s plan →
  F.Effect (A.planTag plan) (A.runtime-view s) (A.runtime-view t) → Valid start s → Valid start t
 step-effect {s = s} {t} {event} initialized reached advanced chosen permitted (F.same table) valid j row found =
  advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid j row (trans (sym (cong (lookup j) table)) found))
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.born k next pc table) valid j row found =
  Deact.write-valid (λ k row → RowValid start t k (Sub.execution row)) k next (rows s) (initial-row {f = Sub.execution next} pc)
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) found)
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.flags k old next found exec table) valid j row selected =
  Deact.write-valid (λ k row → RowValid start t k (Sub.execution row)) k next (rows s)
   (subst (RowValid start t k) (sym exec) (advance-row {s = s} {t = t} {f = Sub.execution old} {a = event} advanced (valid k old found)))
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) selected)
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.tick k a old next w w′ found world shared stepped table tag) valid j row selected =
  Deact.write-valid (λ k row → RowValid start t k (Sub.execution row)) k (record old { execution = next }) (rows s)
   (tick-row k a old next w w′ initialized reached advanced chosen permitted found world shared stepped table tag (valid k old found))
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) selected)
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.established k old next found pc work table) valid j row selected =
  Deact.write-valid (λ k row → RowValid start t k (Sub.execution row)) k next (rows s)
   (λ kind → Data.Empty.⊥-elim (no-establishment (control (valid k old found (trans (sym (cong G.kind work)) kind))) pc))
   (λ k row found → advance-row {s = s} {t = t} {f = Sub.execution row} {a = event} advanced (valid k row found)) j row (trans (sym (cong (lookup j) table)) selected)
 step-effect {start = start} {s = s} {t} {event} initialized reached advanced chosen permitted (F.failed k old next found exec table) valid j row selected =
  Deact.write-valid (λ k row → RowValid start t k (Sub.execution row)) k next (rows s) (failed-row {f = Sub.execution next} {old = Sub.execution old} exec)
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
  (publicationHistory : Origins.Origin start current result) → G.kind (G.work result) ≡ G.close →
  G.outcome result ≡ G.succeeded → History start current (Queue.Publication.job (Origins.Origin.published publicationHistory)) (G.work result)
 origin-success initialized publicationHistory closing success = extend-through
  (T.more {a = Origins.Origin.event publicationHistory} (Origins.Origin.advanced publicationHistory) (Origins.Origin.continued publicationHistory))
  (subst (History _ _ _) work (get-success (initialized-valid initialized (Origins.Origin.reached publicationHistory) j row found
   (trans (cong G.kind work) closing)) (trans completed (cong J.complete success))))
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
  in G.kind (G.work result) ≡ G.close → G.outcome result ≡ G.succeeded →
   History start s (Queue.Publication.job (Origins.Origin.published publicationHistory)) (G.work result)
 consumed-success initialized path selected = origin-success initialized (Origins.initialized-consumed initialized path selected)

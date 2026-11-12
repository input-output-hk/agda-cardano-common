{-# OPTIONS --guardedness #-}

-- Initialized safety for the registry + owned admission/caller variant.
-- Source erasure relabels registry delivery to existing physical observations;
-- it does not assert that the pinned implementation has a registry today.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerOwnedHandlers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; HandleId)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Properties.ServerShutdownCoordinator as SI5
import ConnectionManagement.Properties.ServerShutdownComplete as Shutdown
import ConnectionManagement.Variants.ServerOwnedHandlers as Variant
open Variant isBearerClosed isIOManagerError using
  (module B; module N; module S; module E; module K; Registry; Sweep; unread; scanning; sending; waited;
   register; register-old; register-covers; Site)

-- Boolean conjunction exposes both checked waits.
and-true : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
and-true true true refl = refl , refl
and-true true false ()
and-true false b ()

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  open Variant.Protocols isBearerClosed isIOManagerError canInitiate
  private
    module Original = SI5.Protocols isBearerClosed isIOManagerError canInitiate
    module ShutdownFacts = Shutdown isBearerClosed isIOManagerError
    module Done = Shutdown.Protocols isBearerClosed isIOManagerError canInitiate

  -- Phase B joins stutter; every other phase B event is one source event.
  eraseWorkerEvent : W.Event → List T.Event
  eraseWorkerEvent (W.run a) = a ∷ []
  eraseWorkerEvent (W.joinWorker w) = []
  worker-projection : ∀ a b {c} → W.advance′ a b ≡ just c →
    T.Runs (W.source b) (eraseWorkerEvent a) (W.source c)
  worker-projection (W.run a) b eq = T.more (W.advance-erasure a b eq) T.stop
  worker-projection (W.joinWorker w) b eq = subst (λ c → T.Runs (W.source b) [] c)
    (sym (proj₁ (W.join-effect w b eq))) T.stop

  -- Erased inner labels depend on the actual target selected by the sweep.
  project : Event → Runtime → List T.Event
  project (sourceEvent a) s = eraseWorkerEvent a
  project (cancelHandler site err) s with sweep s
  ... | sending _ w _ = delivery site w err ∷ []
  ... | _ = []
  project _ s = []

  -- Every selected ordinary plan retains its actual source write.
  choose-projection : ∀ a s {b pc} → choose a s ≡ just (b , pc) →
    T.Runs (W.source (base s)) (project a s) (W.source b)
  choose-projection (sourceEvent a) s eq with advanceSource a (base s) in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → worker-projection a (base s) (advanceSource-erasure a (base s) actual) }
  choose-projection readRegistry s eq with S.stage (server (base s)) | sweep s
  ... | S.closingCM | unread = case just-injective eq of λ { refl → T.stop }
  choose-projection readRegistry s eq | S.serving | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.actionBodyExited | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.actionResultAvailable | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.closingAccept | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.acceptCancelRequested | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.acceptCancelDelivered | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.acceptFailed | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.acceptBodyExited | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.acceptResultAvailable | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.acceptJoined | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.serverStopped | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.actionJoined | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.igCancelRequested | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.igJoined | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.serverReturned | _ = case eq of λ ()
  choose-projection readRegistry s eq | S.closingCM | scanning _ _ = case eq of λ ()
  choose-projection readRegistry s eq | S.closingCM | sending _ _ _ = case eq of λ ()
  choose-projection readRegistry s eq | S.closingCM | waited _ = case eq of λ ()
  choose-projection requestHandler s eq with sweep s
  ... | scanning snapshot (w ∷ rest) with ready (base s) w
  ...   | true = case just-injective eq of λ { refl → T.stop }
  ...   | false = case just-injective eq of λ { refl → T.stop }
  choose-projection requestHandler s eq | scanning snapshot [] = case eq of λ ()
  choose-projection requestHandler s eq | unread = case eq of λ ()
  choose-projection requestHandler s eq | sending _ _ _ = case eq of λ ()
  choose-projection requestHandler s eq | waited _ = case eq of λ ()
  choose-projection (cancelHandler site err) s eq with sweep s
  ... | sending snapshot w rest with advanceSource (W.run (delivery site w err)) (base s) in actual
  ...   | nothing = case eq of λ ()
  ...   | just b = case just-injective eq of λ { refl → worker-projection (W.run (delivery site w err)) (base s)
    (advanceSource-erasure (W.run (delivery site w err)) (base s) actual) }
  choose-projection (cancelHandler site err) s eq | unread = case eq of λ ()
  choose-projection (cancelHandler site err) s eq | scanning _ _ = case eq of λ ()
  choose-projection (cancelHandler site err) s eq | waited _ = case eq of λ ()
  choose-projection acknowledgeHandler s eq with sweep s
  ... | sending snapshot w rest with ready (base s) w
  ...   | true = case just-injective eq of λ { refl → T.stop }
  ...   | false = case eq of λ ()
  choose-projection acknowledgeHandler s eq | unread = case eq of λ ()
  choose-projection acknowledgeHandler s eq | scanning _ _ = case eq of λ ()
  choose-projection acknowledgeHandler s eq | waited _ = case eq of λ ()
  choose-projection waitHandlers s eq with sweep s
  ... | scanning snapshot [] with allReady (base s) (registry s)
  ...   | true = case just-injective eq of λ { refl → T.stop }
  ...   | false = case eq of λ ()
  choose-projection waitHandlers s eq | scanning snapshot (_ ∷ _) = case eq of λ ()
  choose-projection waitHandlers s eq | unread = case eq of λ ()
  choose-projection waitHandlers s eq | sending _ _ _ = case eq of λ ()
  choose-projection waitHandlers s eq | waited _ = case eq of λ ()

  -- Erasing a successful registry edge yields that concrete source run.
  advance-projection : ∀ a s {t} → advance a s ≡ just t →
    T.Runs (W.source (base s)) (project a s) (W.source (base t))
  advance-projection a s eq with choose a s in chosen
  ... | nothing = case eq of λ ()
  ... | just (b , pc) with gate-view b (registry s) pc eq
  ...   | refl , ok = choose-projection a s chosen

  -- Source outer states retain the original CM coordinator and relays state.
  eraseOuter : Outer → SourceOuter.Outer
  eraseOuter (outer s r) = SourceOuter.outer (W.source (base s)) r

  -- Expose the inner executable edge before reducing the outer wrapper.
  source-inner-step : ∀ a s {t} r → T.advance a s ≡ just t →
    SourceOuter.outerStep (SourceOuter.innerAct a) (SourceOuter.outer s (RR.relaysState r RR.inside)) ≡
      just (SourceOuter.outer t (RR.relaysState r RR.inside))
  source-inner-step a s r eq with T.advance a s
  ... | nothing = case eq of λ ()
  ... | just t = cong (λ x → just (SourceOuter.outer x (RR.relaysState r RR.inside))) (just-injective eq)

  -- Lift an erased inner run while the real outer relays owner is inside.
  lift-inner : ∀ {s as t} r → T.Runs s as t →
    SourceOuter.Executes (SourceOuter.outer s (RR.relaysState r RR.inside))
      (map SourceOuter.innerAct as) (SourceOuter.outer t (RR.relaysState r RR.inside))
  lift-inner r T.stop = SourceOuter.done
  lift-inner r (T.more {s = s} {a = a} eq rest) = SourceOuter.next (source-inner-step a s r eq) (lift-inner r rest)

  -- One variant edge erases either to stuttering or to its source label(s).
  outer-edge : ∀ a s {t} → outerStep a s ≡ just t →
    Σ (List SourceOuter.OuterAction) (λ as → SourceOuter.Executes (eraseOuter s) as (eraseOuter t))
  outer-edge (innerAct a) (outer s (RR.relaysState r RR.inside)) eq with advance a s in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → _ , lift-inner r (advance-projection a s actual) }
  outer-edge (innerAct a) (outer s (RR.relaysState r RR.cancelling)) eq = case eq of λ ()
  outer-edge (innerAct a) (outer s (RR.relaysState r RR.finished)) eq = case eq of λ ()
  outer-edge (relaysAct a) (outer s r) eq with RR.step (returned s) a r in actual
  ... | nothing = case eq of λ ()
  ... | just r′ = case just-injective eq of λ { refl → SourceOuter.relaysAct a ∷ [] , SourceOuter.next (source actual) SourceOuter.done }
    where
    source : ∀ {r′} → RR.step (returned s) a r ≡ just r′ →
      SourceOuter.outerStep (SourceOuter.relaysAct a) (eraseOuter (outer s r)) ≡ just (eraseOuter (outer s r′))
    source actual rewrite actual = refl

  -- Concatenate real source executions, without normalizing concrete runtimes.
  append : ∀ {s as t bs u} → SourceOuter.Executes s as t → SourceOuter.Executes t bs u → SourceOuter.Executes s (as ++ bs) u
  append SourceOuter.done rest = rest
  append (SourceOuter.next eq path) rest = SourceOuter.next eq (append path rest)

  -- Explicit event erasure/relabeling into the unchanged open source model.
  outer-erasure : ∀ {s as t} → Executes s as t →
    Σ (List SourceOuter.OuterAction) (λ bs → SourceOuter.Executes (eraseOuter s) bs (eraseOuter t))
  outer-erasure done = [] , SourceOuter.done
  outer-erasure (next {s = s} {a = a} eq rest) with outer-edge a s eq | outer-erasure rest
  ... | front , p | back , q = front ++ back , append p q

  -- The entire original SI5 certificate transports, including its physical wait.
  si5 : ∀ {c₀ g start scheduled as final t} → T.initialize (O.initial c₀) g ≡ just start →
    Executes (outer (initial start) (RR.initial scheduled)) as (outer final (RR.relaysState t RR.finished)) →
    Original.Complete scheduled (W.source (base final)) t
  si5 initialized path = Original.complete initialized (proj₂ (outer-erasure path))

  -- Both executable shutdown waits form a simple invariant.
  Gates : Runtime → Set
  Gates s = workerGate (base s) ∧ cmGate (base s) (registry s) (sweep s) ≡ true
  initial-stage : ∀ c g {s} → T.initialize c g ≡ just s → S.stage (server (W.runtime s [])) ≡ S.serving
  initial-stage c g eq with K.initial c g in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → ShutdownFacts.shared-initial c g actual }
  initial-gates : ∀ c g {s} → T.initialize c g ≡ just s → Gates (initial s)
  initial-gates c g eq rewrite initial-stage c g eq | Original.init-T c g eq = refl

  -- Inner steps establish the gates; relays steps retain the inner state.
  outer-gates : ∀ a s {t} → outerStep a s ≡ just t → Gates (inner s) → Gates (inner t)
  outer-gates (innerAct a) (outer s (RR.relaysState r RR.inside)) eq held with advance a s in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → advance-gates a s actual }
  outer-gates (innerAct a) (outer s (RR.relaysState r RR.cancelling)) eq held = case eq of λ ()
  outer-gates (innerAct a) (outer s (RR.relaysState r RR.finished)) eq held = case eq of λ ()
  outer-gates (relaysAct a) (outer s r) eq held with RR.step (returned s) a r
  ... | nothing = case eq of λ ()
  ... | just r′ = case just-injective eq of λ { refl → held }
  runs-gates : ∀ {s as t} → Executes s as t → Gates (inner s) → Gates (inner t)
  runs-gates done held = held
  runs-gates (next {s = s} {a = a} eq rest) held = runs-gates rest (outer-gates a s eq held)
  initialized-gates : ∀ {c₀ g start scheduled as final} → T.initialize (O.initial c₀) g ≡ just start →
    Executes (outer (initial start) (RR.initial scheduled)) as final → Gates (inner final)
  initialized-gates {c₀} {g} initialized path = runs-gates path (initial-gates (O.initial c₀) g initialized)

  -- Every physical thread, including a fork before map publication, is covered.
  Covered : Runtime → Set
  Covered s = ∀ w h → lookup w (threads (base s)) ≡ just h → w ∈ registry s
  advance-covered : ∀ a s {t} → advance a s ≡ just t → Covered t
  advance-covered a s eq with choose a s
  ... | nothing = case eq of λ ()
  ... | just (b , pc) with gate-view b (registry s) pc eq
  ...   | refl , ok = register-covers (threads b) (registry s)
  outer-covered : ∀ a s {t} → outerStep a s ≡ just t → Covered (inner s) → Covered (inner t)
  outer-covered (innerAct a) (outer s (RR.relaysState r RR.inside)) eq held with advance a s in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → advance-covered a s actual }
  outer-covered (innerAct a) (outer s (RR.relaysState r RR.cancelling)) eq held = case eq of λ ()
  outer-covered (innerAct a) (outer s (RR.relaysState r RR.finished)) eq held = case eq of λ ()
  outer-covered (relaysAct a) (outer s r) eq held with RR.step (returned s) a r
  ... | nothing = case eq of λ ()
  ... | just r′ = case just-injective eq of λ { refl → held }
  runs-covered : ∀ {s as t} → Executes s as t → Covered (inner s) → Covered (inner t)
  runs-covered done held = held
  runs-covered (next {s = s} {a = a} eq rest) held = runs-covered rest (outer-covered a s eq held)
  initialized-covered : ∀ {start scheduled as final} →
    Executes (outer (initial start) (RR.initial scheduled)) as final → Covered (inner final)
  initialized-covered {start} path = runs-covered path (register-covers (threads (W.runtime start [])) [])

  -- Covers the strongest boundary and the later returned-Server state.
  data ClosedStage : S.Stage → Set where
    inCM : ClosedStage S.closingCM
    returnedServer : ClosedStage S.serverReturned
  boundary-workers : ∀ b → ClosedStage (S.stage (server b)) → workerGate b ≡ true → workersReady b ≡ true
  boundary-workers b inCM held = held
  boundary-workers b returnedServer held = held

  -- Every raw worker, rather than only each metadata row, was actually joined.
  Joined : Runtime → Set
  Joined s = ∀ w t → lookup w (S.workers (server (base s))) ≡ just t →
    lookup w (W.owned (base s)) ≡ just true × Σ S.Result (λ r → S.pc t ≡ S.resultAvailable r)
  rows-joined : ∀ rows owned → joinedRows rows owned ≡ true → ∀ w t → lookup w rows ≡ just t →
    lookup w owned ≡ just true × Σ S.Result (λ r → S.pc t ≡ S.resultAvailable r)
  rows-joined [] owned held w t ()
  rows-joined ((v , worker) ∷ rows) owned held w t found with lookup v owned in joined | S.pc worker in phase
  ... | just true | S.resultAvailable r with w ≟ v
  ...   | yes refl = case just-injective found of λ { refl → joined , r , phase }
  ...   | no _ = rows-joined rows owned held w t found
  rows-joined ((v , worker) ∷ rows) owned held w t found | just true | S.calling = case held of λ ()
  rows-joined ((v , worker) ∷ rows) owned held w t found | just true | S.closeDisconnected = case held of λ ()
  rows-joined ((v , worker) ∷ rows) owned held w t found | just true | S.closeException _ = case held of λ ()
  rows-joined ((v , worker) ∷ rows) owned held w t found | just true | S.closePrefix _ _ = case held of λ ()
  rows-joined ((v , worker) ∷ rows) owned held w t found | just true | S.bodyExited _ = case held of λ ()
  rows-joined ((v , worker) ∷ rows) owned held w t found | just false | _ = case held of λ ()
  rows-joined ((v , worker) ∷ rows) owned held w t found | nothing | _ = case held of λ ()

  -- Universal initialized no-late-admission, from entry to closingCM onwards.
  no-late-admission : ∀ {c₀ g start scheduled as final} → T.initialize (O.initial c₀) g ≡ just start →
    Executes (outer (initial start) (RR.initial scheduled)) as final →
    ClosedStage (S.stage (server (base (inner final)))) →
    B.allJoined (W.owned (base (inner final))) ≡ true × Joined (inner final)
  no-late-admission {final = final} initialized path closed with
    boundary-workers (base (inner final)) closed
      (proj₁ (and-true _ _ (initialized-gates initialized path)))
  ... | workers = proj₁ checked , rows-joined
    (S.workers (server (base (inner final)))) (W.owned (base (inner final))) (proj₂ checked)
    where checked = and-true (B.allJoined (W.owned (base (inner final))))
            (joinedRows (S.workers (server (base (inner final)))) (W.owned (base (inner final)))) workers

  -- A joined raw worker is no longer a running include caller.
  joined-not-running : ∀ s → Joined s → ∀ w → S.running w (server (base s)) ≡ false
  joined-not-running s joined w with lookup w (S.workers (server (base s))) in found
  ... | nothing = refl
  ... | just t with joined w t found
  ...   | yesJoined , r , phase rewrite phase = refl

  -- These are the actual source-reusing admission operations, not a label ban.
  joined-refuses-fork : ∀ s → Joined s → ∀ w →
    S.inherit (S.runMachine (Machine.admissionStep w Admission.take)) (server (base s)) ≡ nothing ×
    S.inherit (S.runMachine (Machine.admissionStep w Admission.fork)) (server (base s)) ≡ nothing
  joined-refuses-fork s joined w rewrite joined-not-running s joined w = refl , refl

  -- Registry membership is historical across every successful transition.
  advance-history : ∀ a s {t} → advance a s ≡ just t → ∀ w → w ∈ registry s → w ∈ registry t
  advance-history a s eq w held with choose a s
  ... | nothing = case eq of λ ()
  ... | just (b , pc) with gate-view b (registry s) pc eq
  ...   | refl , ok = register-old (threads b) (registry s) held
  outer-history : ∀ a s {t} → outerStep a s ≡ just t → ∀ w → w ∈ registry (inner s) → w ∈ registry (inner t)
  outer-history (innerAct a) (outer s (RR.relaysState r RR.inside)) eq w held with advance a s in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → advance-history a s actual w held }
  outer-history (innerAct a) (outer s (RR.relaysState r RR.cancelling)) eq w held = case eq of λ ()
  outer-history (innerAct a) (outer s (RR.relaysState r RR.finished)) eq w held = case eq of λ ()
  outer-history (relaysAct a) (outer s r) eq w held with RR.step (returned s) a r
  ... | nothing = case eq of λ ()
  ... | just r′ = case just-injective eq of λ { refl → held }
  runs-history : ∀ {s as t} → Executes s as t → ∀ w → w ∈ registry (inner s) → w ∈ registry (inner t)
  runs-history done w held = held
  runs-history (next {s = s} {a = a} eq rest) w held = runs-history rest w (outer-history a s eq w held)

  -- A true collective wait provides each individual physical Async result.
  ready-member : ∀ b rs w → allReady b rs ≡ true → w ∈ rs → ready b w ≡ true
  ready-member b [] w held ()
  ready-member b (v ∷ rest) w held (here refl) = proj₁ (and-true _ _ held)
  ready-member b (v ∷ rest) w held (there member) = ready-member b rest w (proj₂ (and-true _ _ held)) member

  -- A closed source coordinator additionally certifies the registry wait.
  cmGate-closed : ∀ b rs pc → Close.phase (coordinator b) ≡ Close.closed →
    cmGate b rs pc ≡ completed pc ∧ allReady b rs
  cmGate-closed b rs pc eq rewrite eq = refl
  closed-registry : ∀ s → Gates s → Close.phase (coordinator (base s)) ≡ Close.closed →
    completed (sweep s) ≡ true × allReady (base s) (registry s) ≡ true
  closed-registry s held closed = and-true (completed (sweep s)) (allReady (base s) (registry s))
    (trans (sym (cmGate-closed (base s) (registry s) (sweep s) closed))
      (proj₂ (and-true (workerGate (base s)) (cmGate (base s) (registry s) (sweep s)) held)))

  -- Strong quiescence retains every admitted worker and every historical handler.
  record Quiescent (s : Runtime) : Set where
    field
      workersJoined : Joined s
      ownershipJoined : B.allJoined (W.owned (base s)) ≡ true
      registeredResults : ∀ w → w ∈ registry s → ready (base s) w ≡ true
      noLiveHandler : ∀ w h → lookup w (threads (base s)) ≡ just h → ready (base s) w ≡ true

  -- Universal initialized finished-run theorem, with the original premises.
  quiescence : ∀ {c₀ g start scheduled as final t} → T.initialize (O.initial c₀) g ≡ just start →
    Executes (outer (initial start) (RR.initial scheduled)) as (outer final (RR.relaysState t RR.finished)) →
    Quiescent final
  quiescence {final = final} initialized path = record
    { workersJoined = proj₂ joined
    ; ownershipJoined = proj₁ joined
    ; registeredResults = λ w → ready-member (base final) (registry final) w results
    ; noLiveHandler = λ w h found → ready-member (base final) (registry final) w results (initialized-covered path w h found) }
    where
    certificate = si5 initialized path
    held = initialized-gates initialized path
    closed = Original.CMClosed.closed (Original.Complete.cm certificate)
    results = proj₂ (closed-registry final held closed)
    returnedStage = Done.Complete.serverReturned (Original.Complete.shutdown certificate)
    joined = no-late-admission initialized path (subst ClosedStage (sym returnedStage) returnedServer)

  -- The original physical live-coverage statement follows from the stronger form.
  LiveCovered : Runtime → Set
  LiveCovered s = ∀ w h → lookup w (threads (base s)) ≡ just h →
    ready (base s) w ≡ false → w ∈ Close.collected (coordinator (base s))
  quiescent-covered : ∀ s → Quiescent s → LiveCovered s
  quiescent-covered s q w h found live = ⊥-elim (impossible (trans (sym (Quiescent.noLiveHandler q w h found)) live))
    where impossible : true ≡ false → ⊥
          impossible ()

  -- Full source SI5 plus the extra completed, physically checked registry sweep.
  registry-si5 : ∀ {c₀ g start scheduled as final t} → T.initialize (O.initial c₀) g ≡ just start →
    Executes (outer (initial start) (RR.initial scheduled)) as (outer final (RR.relaysState t RR.finished)) →
    Original.Complete scheduled (W.source (base final)) t ×
    completed (sweep final) ≡ true × allReady (base final) (registry final) ≡ true
  registry-si5 {final = final} initialized path = certificate ,
    closed-registry final (initialized-gates initialized path) (Original.CMClosed.closed (Original.Complete.cm certificate))
    where certificate = si5 initialized path

  -- Initialized refusal at both source admission birth-enabling boundaries.
  no-late-fork : ∀ {c₀ g start scheduled as final} → T.initialize (O.initial c₀) g ≡ just start →
    Executes (outer (initial start) (RR.initial scheduled)) as final →
    ClosedStage (S.stage (server (base (inner final)))) → ∀ w →
    S.inherit (S.runMachine (Machine.admissionStep w Admission.take)) (server (base (inner final))) ≡ nothing ×
    S.inherit (S.runMachine (Machine.admissionStep w Admission.fork)) (server (base (inner final))) ≡ nothing
  no-late-fork {final = final} initialized path closed = joined-refuses-fork (inner final)
    (proj₂ (no-late-admission initialized path closed))

  -- Concatenation retains the actual intermediate state and all source guards.
  append-variant : ∀ {s as t bs u} → Executes s as t → Executes t bs u → Executes s (as ++ bs) u
  append-variant done rest = rest
  append-variant (next eq path) rest = next eq (append-variant path rest)

  -- Every handler registered at ANY earlier state has a result at the end.
  historical-quiescence : ∀ {c₀ g start scheduled prefix middle suffix final t} →
    T.initialize (O.initial c₀) g ≡ just start →
    Executes (outer (initial start) (RR.initial scheduled)) prefix middle →
    Executes middle suffix (outer final (RR.relaysState t RR.finished)) →
    ∀ w → w ∈ registry (inner middle) → ready (base final) w ≡ true
  historical-quiescence initialized before after w held =
    Quiescent.registeredResults (quiescence initialized (append-variant before after)) w (runs-history after w held)

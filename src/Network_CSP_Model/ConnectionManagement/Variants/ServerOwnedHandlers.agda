{-# OPTIONS --guardedness #-}

-- Phase B plus a historical CM handler registry and a second shutdown sweep.
-- Foreign CM call starts are excluded by the accepted OwnedCallers policy.
-- Source steps, including cancellation delivery and physical results, are reused.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Variants.ServerOwnedHandlers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; HandleId)
open import Data.List.Membership.DecPropositional {A = WorkerId} _≟_ using (_∈?_)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundHandlerSupervision as Physical
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Variants.ServerOwnedWorkers as Workers
import ConnectionManagement.Variants.OwnedCallers as Callers
module B = Workers isBearerClosed isIOManagerError
module N = Publication isBearerClosed
open B public using (module S; module E; module K)

-- The registry is a set of historical physical Async identities.
Registry = List WorkerId

-- Retain an existing identity, or register it at the same atomic source edge.
insert : WorkerId → Registry → Registry
insert w rs with w ∈? rs
... | yes _ = rs
... | no _ = w ∷ rs

-- Register every physical child visible after an edge; existing rows are inert.
register : Store WorkerId H.Thread → Registry → Registry
register [] rs = rs
register ((w , _) ∷ rows) rs = insert w (register rows rs)

-- Insertion preserves all old registry members.
insert-old : ∀ w rs {v} → v ∈ rs → v ∈ insert w rs
insert-old w rs held with w ∈? rs
... | yes _ = held
... | no _ = there held

-- The identity inserted is always retained.
insert-new : ∀ w rs → w ∈ insert w rs
insert-new w rs with w ∈? rs
... | yes held = held
... | no _ = here refl

-- Every registered identity is historical, even after later births.
register-old : ∀ rows rs {w} → w ∈ rs → w ∈ register rows rs
register-old [] rs held = held
register-old ((v , _) ∷ rows) rs held = insert-old v (register rows rs) (register-old rows rs held)

-- Each physical lookup is covered, without a map-membership assumption.
register-covers : ∀ rows rs w h → lookup w rows ≡ just h → w ∈ register rows rs
register-covers [] rs w h ()
register-covers ((v , t) ∷ rows) rs w h found with w ≟ v
... | yes refl = insert-new w (register rows rs)
... | no _ = insert-old v (register rows rs) (register-covers rows rs w h found)

-- Snapshot and remaining targets are retained independently of the CM map.
data Sweep : Set where
  unread : Sweep
  scanning : Registry → Registry → Sweep
  sending : Registry → WorkerId → Registry → Sweep
  waited : Registry → Sweep

-- These sites reuse the existing masking-sensitive standalone deliveries.
data Site : Set where
  handshake blockedSetup : Site
  startup : N.R.DeliverySite → Site
  catchBody : N.C.DeliverySite → Site
  exitWindow : N.D.X.Window → Site
  publication : N.Site → Site
  muxBody deltaQ initiatorDeltaQ : Site

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  open B.Protocols canInitiate public using (module T; module SourceOuter)
  module W = B.Protocols canInitiate
  module Policy = Callers.Protocols isBearerClosed isIOManagerError canInitiate

  -- The raw physical table is already historical and contains both fork routes.
  physical : W.Runtime → N.W.State
  physical b = N.R.base (N.raw (S.base (E.base (K.server (T.base (W.source b))))))
  threads : W.Runtime → Store WorkerId H.Thread
  threads b = Physical.threads (N.W.physical (physical b))
  ready : W.Runtime → WorkerId → Bool
  ready b w = N.W.resultReady w (physical b)
  coordinator : W.Runtime → Close.State
  coordinator b = N.W.shutdown (physical b)
  server : W.Runtime → S.State
  server b = E.base (K.server (T.base (W.source b)))

  -- Executable metadata is separate from physical and logical source state.
  record Runtime : Set where
    constructor runtime
    field base : W.Runtime
          registry : Registry
          sweep : Sweep
  open Runtime public

  -- A physical birth and its registration are one successful variant edge.
  pack : W.Runtime → Registry → Sweep → Runtime
  pack b rs pc = runtime b (register (threads b) rs) pc

  -- Initialization does not adopt logical handlers; source initialization has
  -- no physical thread history. The pack also makes coverage explicit.
  initial : T.Runtime → Runtime
  initial s = pack (W.runtime s []) [] unread

  -- Check the actual raw worker table as well as the retained join flags.
  -- This is the executable meaning of waiting for EVERY admission worker.
  joinedRows : Store WorkerId S.Worker → B.Ownership → Bool
  joinedRows [] owned = true
  joinedRows ((w , worker) ∷ rows) owned with lookup w owned | S.pc worker
  ... | just true | S.resultAvailable _ = joinedRows rows owned
  ... | _ | _ = false
  workersReady : W.Runtime → Bool
  workersReady b = B.allJoined (W.owned b) ∧ joinedRows (S.workers (server b)) (W.owned b)
  workerGate : W.Runtime → Bool
  workerGate b with S.stage (server b)
  ... | S.closingCM = workersReady b
  ... | S.serverReturned = workersReady b
  ... | _ = true

  -- CM retains its original map certificate and additionally waits for the
  -- historical registry. Rechecking at closed states preserves that obligation.
  allReady : W.Runtime → Registry → Bool
  allReady b = Close.allAvailable (ready b)
  completed : Sweep → Bool
  completed (waited _) = true
  completed _ = false
  cmGate : W.Runtime → Registry → Sweep → Bool
  cmGate b rs pc with Close.phase (coordinator b)
  ... | Close.closed = completed pc ∧ allReady b rs
  ... | _ = true

  -- Both conditions are shutdown waits; no worker cancellation is introduced.
  gate : W.Runtime → Registry → Sweep → Maybe Runtime
  gate b rs pc with workerGate b ∧ cmGate b (register (threads b) rs) pc
  ... | false = nothing
  ... | true = just (pack b rs pc)

  -- Successful gates expose both concrete waits and the exact state write.
  gate-view : ∀ b rs pc {t} → gate b rs pc ≡ just t →
    t ≡ pack b rs pc × workerGate (base t) ∧ cmGate (base t) (registry t) (sweep t) ≡ true
  gate-view b rs pc eq with workerGate b ∧ cmGate b (register (threads b) rs) pc in passed
  ... | false = case eq of λ ()
  ... | true = case just-injective eq of λ { refl → refl , passed }

  -- Selection and both shared-action plan wrappers obey OwnedCallers.
  advanceSource : W.Event → W.Runtime → Maybe W.Runtime
  advanceSource (W.run a) b with T.choose a (W.source b)
  ... | nothing = nothing
  ... | just p with Policy.planAllowed p
  ...   | false = nothing
  ...   | true = W.enact′ p b
  advanceSource (W.joinWorker w) b = W.advance′ (W.joinWorker w) b

  -- This extra policy changes no successful phase B write.
  advanceSource-erasure : ∀ a b {c} → advanceSource a b ≡ just c → W.advance′ a b ≡ just c
  advanceSource-erasure (W.run a) b eq with T.choose a (W.source b)
  ... | nothing = case eq of λ ()
  ... | just p with Policy.planAllowed p
  ...   | false = case eq of λ ()
  ...   | true = eq
  advanceSource-erasure (W.joinWorker w) b eq = eq

  -- Standalone cancellation has the same physical writes as the source
  -- coordinator's delivery, without acknowledging its unrelated map snapshot.
  delivery : Site → WorkerId → ErrorId → T.Event
  physicalEvent : N.Action → T.Event
  physicalEvent a = T.dispatch (K.serverStep (E.run (S.run a)))
  runH : H.Action → N.Action
  runH a = N.run (N.C.run (N.D.run (N.R.run (N.D.X.run (N.W.run
    (N.G.run (N.M.run (N.P.run (N.U.run (Physical.handler a))))))))))
  delivery handshake w err = physicalEvent (runH (H.deliverHandshakeCancellation w err))
  delivery blockedSetup w err = physicalEvent (runH (H.deliverBlockedSetupCancellation w err))
  delivery (startup site) w err = physicalEvent (N.run (N.C.run (N.D.run (N.R.observeCancellation w site err))))
  delivery (catchBody site) w err = physicalEvent (N.run (N.C.observeCancellation w site err))
  delivery (exitWindow site) w err = physicalEvent (N.run (N.C.run (N.D.run (N.R.run (N.D.X.observeCancellation site w err)))))
  delivery (publication site) w err = physicalEvent (N.observeFailure w site (N.R.async err))
  delivery muxBody w err = physicalEvent (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run (N.W.run (N.G.abortOwner w err)))))))
  delivery deltaQ w err = physicalEvent (N.run (N.C.run (N.D.observeException w (N.R.async err))))
  delivery initiatorDeltaQ w err = physicalEvent (N.run (N.C.run (N.D.observeInitiatorException w (N.R.async err))))

  -- New scope operations; all handler body/cleanup/result edges stay ordinary.
  data Event : Set where
    sourceEvent : W.Event → Event
    readRegistry requestHandler acknowledgeHandler waitHandlers : Event
    cancelHandler : Site → ErrorId → Event

  -- Read once in closingCM; historical handles include already-purged entries.
  choose : Event → Runtime → Maybe (W.Runtime × Sweep)
  choose (sourceEvent a) s with advanceSource a (base s)
  ... | nothing = nothing
  ... | just b = just (b , sweep s)
  choose readRegistry s with S.stage (server (base s)) | sweep s
  ... | S.closingCM | unread = just (base s , scanning (registry s) (registry s))
  ... | _ | _ = nothing
  choose requestHandler s with sweep s
  ... | scanning snapshot (w ∷ rest) with ready (base s) w
  ...   | true = just (base s , scanning snapshot rest)
  ...   | false = just (base s , sending snapshot w rest)
  choose requestHandler s | _ = nothing
  choose (cancelHandler site err) s with sweep s
  ... | sending snapshot w rest with advanceSource (W.run (delivery site w err)) (base s)
  ...   | nothing = nothing
  ...   | just b = just (b , scanning snapshot rest)
  choose (cancelHandler site err) s | _ = nothing
  choose acknowledgeHandler s with sweep s
  ... | sending snapshot w rest with ready (base s) w
  ...   | true = just (base s , scanning snapshot rest)
  ...   | false = nothing
  choose acknowledgeHandler s | _ = nothing
  choose waitHandlers s with sweep s
  ... | scanning snapshot [] with allReady (base s) (registry s)
  ...   | true = just (base s , waited snapshot)
  ...   | false = nothing
  choose waitHandlers s | _ = nothing

  -- Every successful transition ends with the same two concrete scope waits.
  advance : Event → Runtime → Maybe Runtime
  advance a s with choose a s
  ... | nothing = nothing
  ... | just (b , pc) = gate b (registry s) pc

  -- The checked target satisfies both waits, independently of its predecessor.
  advance-gates : ∀ a s {t} → advance a s ≡ just t →
    workerGate (base t) ∧ cmGate (base t) (registry t) (sweep t) ≡ true
  advance-gates a s eq with choose a s
  ... | nothing = case eq of λ ()
  ... | just (b , pc) = proj₂ (gate-view b (registry s) pc eq)

  -- The outer return predicate is EXACTLY the phase B/source predicate.
  returned : Runtime → Bool
  returned s = W.returned (base s)
  open RR.Outer advance returned public

  -- Metadata operations erase to stuttering; cancellation is a source event.
  eraseEvent : Event → Runtime → List W.Event
  eraseEvent (sourceEvent a) s = a ∷ []
  eraseEvent (cancelHandler site err) s with sweep s
  ... | sending _ w _ = W.run (delivery site w err) ∷ []
  ... | _ = []
  eraseEvent _ s = []

  -- Exact registration effect of any ordinary event, including either fork.
  source-effect : ∀ a s {t} → advance (sourceEvent a) s ≡ just t →
    W.advance′ a (base s) ≡ just (base t) ×
    registry t ≡ register (threads (base t)) (registry s) × sweep t ≡ sweep s
  source-effect a s eq with advanceSource a (base s) in actual
  ... | nothing = case eq of λ ()
  ... | just b with gate-view b (registry s) (sweep s) eq
  ...   | refl , ok = advanceSource-erasure a (base s) actual , refl , refl

  -- Atomic registry-read effect: snapshot ALL historical handles, map ignored.
  read-effect : ∀ s {t} → advance readRegistry s ≡ just t →
    base t ≡ base s × registry t ≡ register (threads (base s)) (registry s) ×
    sweep t ≡ scanning (registry s) (registry s)
  read-effect s eq with S.stage (server (base s)) | sweep s
  ... | S.closingCM | unread with gate-view (base s) (registry s) (scanning (registry s) (registry s)) eq
  ...   | refl , ok = refl , refl , refl
  read-effect s eq | S.serving | _ = case eq of λ ()
  read-effect s eq | S.actionBodyExited | _ = case eq of λ ()
  read-effect s eq | S.actionResultAvailable | _ = case eq of λ ()
  read-effect s eq | S.closingAccept | _ = case eq of λ ()
  read-effect s eq | S.acceptCancelRequested | _ = case eq of λ ()
  read-effect s eq | S.acceptCancelDelivered | _ = case eq of λ ()
  read-effect s eq | S.acceptFailed | _ = case eq of λ ()
  read-effect s eq | S.acceptBodyExited | _ = case eq of λ ()
  read-effect s eq | S.acceptResultAvailable | _ = case eq of λ ()
  read-effect s eq | S.acceptJoined | _ = case eq of λ ()
  read-effect s eq | S.serverStopped | _ = case eq of λ ()
  read-effect s eq | S.actionJoined | _ = case eq of λ ()
  read-effect s eq | S.igCancelRequested | _ = case eq of λ ()
  read-effect s eq | S.igJoined | _ = case eq of λ ()
  read-effect s eq | S.serverReturned | _ = case eq of λ ()
  read-effect s eq | S.closingCM | scanning _ _ = case eq of λ ()
  read-effect s eq | S.closingCM | sending _ _ _ = case eq of λ ()
  read-effect s eq | S.closingCM | waited _ = case eq of λ ()

  -- Requesting cancellation of a live target changes ONLY the sweep cursor.
  request-live : ∀ s snapshot w rest → sweep s ≡ scanning snapshot (w ∷ rest) →
    ready (base s) w ≡ false → advance requestHandler s ≡
    gate (base s) (registry s) (sending snapshot w rest)
  request-live s snapshot w rest pc live rewrite pc | live = refl

  -- An already available result needs no exception delivery.
  request-finished : ∀ s snapshot w rest → sweep s ≡ scanning snapshot (w ∷ rest) →
    ready (base s) w ≡ true → advance requestHandler s ≡
    gate (base s) (registry s) (scanning snapshot rest)
  request-finished s snapshot w rest pc available rewrite pc | available = refl

  -- Delivery is exactly an existing physical source event, then registration.
  cancel-effect : ∀ site err s snapshot w rest {t} → sweep s ≡ sending snapshot w rest →
    advance (cancelHandler site err) s ≡ just t →
    T.advance (delivery site w err) (W.source (base s)) ≡ just (W.source (base t)) ×
    registry t ≡ register (threads (base t)) (registry s) × sweep t ≡ scanning snapshot rest
  cancel-effect site err s snapshot w rest pc eq rewrite pc with advanceSource (W.run (delivery site w err)) (base s) in actual
  ... | nothing = case eq of λ ()
  ... | just b with gate-view b (registry s) (scanning snapshot rest) eq
  ...   | refl , ok = W.advance-erasure (delivery site w err) (base s)
    (advanceSource-erasure (W.run (delivery site w err)) (base s) actual) , refl , refl

  -- Uninterruptible cleanup is never acknowledged merely because cancel waits.
  acknowledge-ready : ∀ s snapshot w rest → sweep s ≡ sending snapshot w rest →
    ready (base s) w ≡ true → advance acknowledgeHandler s ≡
    gate (base s) (registry s) (scanning snapshot rest)
  acknowledge-ready s snapshot w rest pc available rewrite pc | available = refl

  -- The final wait tests actual Async results, not cleanup PCs or map absence.
  wait-ready : ∀ s snapshot → sweep s ≡ scanning snapshot [] → allReady (base s) (registry s) ≡ true →
    advance waitHandlers s ≡ gate (base s) (registry s) (waited snapshot)
  wait-ready s snapshot pc results rewrite pc | results = refl

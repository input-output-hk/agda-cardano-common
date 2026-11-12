{-# OPTIONS --guardedness #-}

-- Recover immutable job descriptors at the actual group snapshot boundary.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxControls (b : ErrorId → Bool) where
open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import ConnectionManagement.Domain using (WorkerId; JobId; DecEq-Id)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Properties.LiveTrackerAuxContent as Content
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
module G = Group b
module A = Content b
module T = Transport b
module Up = Updates b
module Pool = P.Pool

Snapshot : WorkerId → P.State → JobId → Set
Snapshot w s j = Σ Types.ProtocolJob (λ job → lookup j (P.jobs s) ≡ just job × Types.owner job ≡ w × A.JobContent j job s)
Controls : G.State → Set
Controls s = All (λ { (w , row) → A.ControlContent w row (G.protocolState s) }) (G.controls s)

-- Boolean snapshot permutation guards supply membership in the real traversal.
and-left : ∀ a c → a ∧ c ≡ true → a ≡ true
and-left true c eq = refl
and-left false c ()
and-right : ∀ a c → a ∧ c ≡ true → c ≡ true
and-right true c eq = eq
and-right false c ()
member-good : ∀ (C : JobId → Set) j rows → Pool.member j rows ≡ true → All C rows → C j
member-good C j [] () good
member-good C j (k ∷ rows) eq (good ∷ rest) with j ≟ k
... | yes refl = good
... | no _ = member-good C j rows eq rest
members-good : ∀ (C : JobId → Set) xs ys → Pool.allMembers xs ys ≡ true → All C ys → All C xs
members-good C [] ys eq good = []
members-good C (j ∷ xs) ys eq good = member-good C j ys (and-left _ _ eq) good ∷ members-good C xs ys (and-right _ _ eq) good
snapshot-good : ∀ (C : JobId → Set) order current → Pool.sameSnapshot order current ≡ true → All C current → All C order
snapshot-good C order current eq = members-good C order current
 (and-left (Pool.allMembers order current) (Pool.allMembers current order)
   (and-right (Pool.unique current) (Pool.allMembers order current ∧ Pool.allMembers current order)
     (and-right (Pool.unique order) (Pool.unique current ∧ Pool.allMembers order current ∧ Pool.allMembers current order) eq)))

-- miniEntries filters by exact current job lookup and owner equality.
mini-good : ∀ w rows s → Up.Valid (G.protocolState s) → All (Snapshot w (G.protocolState s)) (G.miniEntries w rows s)
mini-good w [] s core = []
mini-good w (j ∷ rows) s core with lookup j (P.jobs (G.protocolState s)) in found
... | nothing = mini-good w rows s core
... | just job with w ≟ Types.owner job
...   | yes refl = (job , found , refl , Up.at (Up.Valid.jobs core) j job found) ∷ mini-good w rows s core
...   | no _ = mini-good w rows s core
registered-good : ∀ w s → Up.Valid (G.protocolState s) → All (Snapshot w (G.protocolState s)) (G.registeredMini w s)
registered-good w s = mini-good w (Pool.registered (G.poolAt w s)) s
physical : ∀ w s j → Snapshot w s j → Σ Pool.ThreadPhase (λ phase → lookup j (Pool.handles (P.poolAt w s)) ≡ just phase)
physical w s j (job , found , refl , good) = A.JobContent.physical-phase good , A.JobContent.physical-found good

-- A non-idle control cannot be the absent-row default initialFrame.
current : ∀ w s → G.phase (G.frameAt w s) ≢ G.idle → Controls s → A.ControlContent w (G.frameAt w s) (G.protocolState s)
current w s active good with lookup w (G.controls s) in found
... | nothing = case active refl of λ ()
... | just row = T.Rows.at (λ w row → A.ControlContent w row (G.protocolState s)) (G.controls s) good w row found
capture-preserves : ∀ w order s {t} → G.captureMini w order s ≡ just t →
 Up.Valid (G.protocolState s) → Controls s → Controls t
capture-preserves w order s actual core good with G.phase (G.frameAt w s) in stage | Pool.sameSnapshot order (G.registeredMini w s) in exact | P.noParent (G.poolAt w s)
... | G.stoppingWritten | true | true = case just-injective actual of λ { refl →
 T.Rows.insert (λ q row → A.ControlContent q row (G.protocolState s)) w (G.frame G.groupClosing order order [] G.ready) (G.controls s)
   (record { owner-reference = A.ControlContent.owner-reference prior
           ; cancellation-backed = tt; snapshot-backed = selected
           ; remaining-backed = All.map (λ { {j} → physical w (G.protocolState s) j }) selected; joined-backed = [] }) good }
 where
 prior = current w s (λ idle → case trans (sym stage) idle of λ ()) good
 selected = snapshot-good (Snapshot w (G.protocolState s)) order (G.registeredMini w s) exact (registered-good w s core)
... | G.stoppingWritten | false | _ = case actual of λ ()
... | G.stoppingWritten | true | false = case actual of λ ()
capture-preserves w order s actual core good | G.idle | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.shutdownSelected | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.stoppingTraced | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.groupClosing | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.draining | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.drainReady | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.stoppedTrace | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.stoppedTracing | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.monitorReturnedNormal | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.ownerAborting err | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.wholeClosing outcome | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.wholeClosed outcome | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.scopeDone outcome | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.asyncFailureWritten err | _ | _ = case actual of λ ()
capture-preserves w order s actual core good | G.asyncDeadTracing err | _ | _ = case actual of λ ()

-- All old control rows can be carried through any certified physical change.
rows-kept : ∀ (rows : Store WorkerId G.Frame) {s t} → T.Retains s t →
 All (λ { (w , row) → A.ControlContent w row s }) rows →
 All (λ { (w , row) → A.ControlContent w row t }) rows
rows-kept rows kept = All.map (λ { {w , row} → T.control-kept kept w row })

-- Phase-only writers retain all four reference-bearing fields exactly.
phase-content : ∀ w row pc s → A.ControlContent w row s → A.ControlContent w (record row { phase = pc }) s
phase-content w row pc s good = record
 { owner-reference = A.ControlContent.owner-reference good
 ; cancellation-backed = A.ControlContent.cancellation-backed good
 ; snapshot-backed = A.ControlContent.snapshot-backed good
 ; remaining-backed = A.ControlContent.remaining-backed good
 ; joined-backed = A.ControlContent.joined-backed good }
cancel-content : ∀ w row pc s → A.ControlContent w row s → A.CancelContent w pc s →
 A.ControlContent w (record row { cancelPC = pc }) s
cancel-content w row pc s good backed = record
 { owner-reference = A.ControlContent.owner-reference good
 ; cancellation-backed = backed; snapshot-backed = A.ControlContent.snapshot-backed good
 ; remaining-backed = A.ControlContent.remaining-backed good; joined-backed = A.ControlContent.joined-backed good }

-- Even the absent-row default may only acquire a control when a real published
-- owner was selected by the writer; existing reference fields come from coverage.
current-with-owner : ∀ w s → A.Owner w (G.protocolState s) → Controls s →
 A.ControlContent w (G.frameAt w s) (G.protocolState s)
current-with-owner w s own good with lookup w (G.controls s) in found
... | nothing = record { owner-reference = own; cancellation-backed = tt; snapshot-backed = []; remaining-backed = []; joined-backed = [] }
... | just row = T.Rows.at (λ q saved → A.ControlContent q saved (G.protocolState s)) (G.controls s) good w row found
phase-preserves : ∀ w pc s → A.Owner w (G.protocolState s) → Controls s → Controls (G.setPhase w pc s)
phase-preserves w pc s own good = T.Rows.insert (λ q row → A.ControlContent q row (G.protocolState s)) w
 (record (G.frameAt w s) { phase = pc }) (G.controls s)
 (phase-content w (G.frameAt w s) pc (G.protocolState s) (current-with-owner w s own good)) good

-- A requested cancel names the real physical handle of the remaining head.
request-preserves : ∀ w s {t} → G.requestGroup w s ≡ just t → Controls s → Controls t
request-preserves w s actual good with G.phase (G.frameAt w s) in stage | G.cancelPC (G.frameAt w s) | G.remaining (G.frameAt w s) in remaining
... | G.groupClosing | G.ready | j ∷ rest = case just-injective actual of λ { refl →
 T.Rows.insert (λ q row → A.ControlContent q row (G.protocolState s)) w
 (record (G.frameAt w s) { cancelPC = G.requested j }) (G.controls s)
 (cancel-content w (G.frameAt w s) (G.requested j) (G.protocolState s) prior
   (All.head (subst (All (λ j → Σ Pool.ThreadPhase (λ phase → lookup j (Pool.handles (P.poolAt w (G.protocolState s))) ≡ just phase))) remaining (A.ControlContent.remaining-backed prior)))) good }
 where prior = current w s (λ idle → case trans (sym stage) idle of λ ()) good
... | G.groupClosing | G.ready | [] = case actual of λ ()
... | G.groupClosing | G.requested j | _ = case actual of λ ()
... | G.groupClosing | G.delivered j | _ = case actual of λ ()
request-preserves w s actual good | G.idle | _ | _ = case actual of λ ()
request-preserves w s actual good | G.shutdownSelected | _ | _ = case actual of λ ()
request-preserves w s actual good | G.stoppingTraced | _ | _ = case actual of λ ()
request-preserves w s actual good | G.stoppingWritten | _ | _ = case actual of λ ()
request-preserves w s actual good | G.draining | _ | _ = case actual of λ ()
request-preserves w s actual good | G.drainReady | _ | _ = case actual of λ ()
request-preserves w s actual good | G.stoppedTrace | _ | _ = case actual of λ ()
request-preserves w s actual good | G.stoppedTracing | _ | _ = case actual of λ ()
request-preserves w s actual good | G.monitorReturnedNormal | _ | _ = case actual of λ ()
request-preserves w s actual good | G.ownerAborting err | _ | _ = case actual of λ ()
request-preserves w s actual good | G.wholeClosing outcome | _ | _ = case actual of λ ()
request-preserves w s actual good | G.wholeClosed outcome | _ | _ = case actual of λ ()
request-preserves w s actual good | G.scopeDone outcome | _ | _ = case actual of λ ()
request-preserves w s actual good | G.asyncFailureWritten err | _ | _ = case actual of λ ()
request-preserves w s actual good | G.asyncDeadTracing err | _ | _ = case actual of λ ()

append : ∀ {C : JobId → Set} {xs ys} → All C xs → All C ys → All C (xs ++ ys)
append [] right = right
append (first ∷ rest) right = first ∷ append rest right
current-with-head : ∀ w s j rest → G.remaining (G.frameAt w s) ≡ j ∷ rest → Controls s →
 A.ControlContent w (G.frameAt w s) (G.protocolState s)
current-with-head w s j rest nonempty good with lookup w (G.controls s) in found
... | nothing = case nonempty of λ ()
... | just row = T.Rows.at (λ q saved → A.ControlContent q saved (G.protocolState s)) (G.controls s) good w row found
join-head-preserves : ∀ w j s {t} → G.joinMiniHead w j s ≡ just t → Controls s → Controls t
join-head-preserves w j s actual good with G.remaining (G.frameAt w s) in remaining | lookup j (Pool.handles (G.poolAt w s)) in found
... | head ∷ rest | just (Pool.resultAvailable exit) with j ≟ head
...   | yes refl = case just-injective actual of λ { refl → T.Rows.insert (λ q row → A.ControlContent q row (G.protocolState s)) w
 (record (G.frameAt w s) { remaining = rest; joined = G.joined (G.frameAt w s) ++ (j ∷ []); cancelPC = G.ready }) (G.controls s)
 (record { owner-reference = A.ControlContent.owner-reference prior; cancellation-backed = tt
         ; snapshot-backed = A.ControlContent.snapshot-backed prior
         ; remaining-backed = All.tail (subst (All (λ k → Σ Pool.ThreadPhase (λ phase → lookup k (Pool.handles (P.poolAt w (G.protocolState s))) ≡ just phase))) remaining (A.ControlContent.remaining-backed prior))
         ; joined-backed = append (A.ControlContent.joined-backed prior) ((Pool.resultAvailable exit , found) ∷ []) }) good }
 where prior = current-with-head w s j rest remaining good
...   | no _ = case actual of λ ()
join-head-preserves w j s actual good | [] | _ = case actual of λ ()
join-head-preserves w j s actual good | _ ∷ _ | nothing = case actual of λ ()
join-head-preserves w j s actual good | _ ∷ _ | just Pool.bodyRunning = case actual of λ ()
join-head-preserves w j s actual good | _ ∷ _ | just Pool.bodyUnwinding = case actual of λ ()
join-head-preserves w j s actual good | _ ∷ _ | just (Pool.bodyReturned item) = case actual of λ ()
join-head-preserves w j s actual good | _ ∷ _ | just (Pool.deregisterPending exit) = case actual of λ ()
join-head-preserves w j s actual good | _ ∷ _ | just (Pool.deregistered exit) = case actual of λ ()

import ConnectionManagement.Properties.LiveTrackerAuxMonitor as MonitorFacts
-- Any actual pool primitive keeps all old control references, including an
-- in-flight cancel target, even as physical handle phases change.
via-pool-kept : ∀ w action s {t} → G.viaPool w action s ≡ just t → T.Retains (G.protocolState s) (G.protocolState t)
via-pool-kept w action s eq with G.ownerContext w s in context
... | nothing = case eq of λ ()
... | just (f , mid) with Pool.step action (G.poolAt w s) in actual
...   | nothing = case eq of λ ()
...   | just pool = case just-injective eq of λ { refl → Up.pool-retains w f pool (G.protocolState s)
 (MonitorFacts.owner-frame b w (G.base s) context) (Up.Kernel.handles-retained action (G.poolAt w s) actual) }
via-pool-controls : ∀ w action s {t} → G.viaPool w action s ≡ just t → G.controls t ≡ G.controls s
via-pool-controls w action s eq with G.ownerContext w s
... | nothing = case eq of λ ()
... | just (f , mid) with Pool.step action (G.poolAt w s)
...   | nothing = case eq of λ ()
...   | just pool = case just-injective eq of λ { refl → refl }
via-pool-preserves : ∀ w action s {t} → G.viaPool w action s ≡ just t → Controls s → Controls t
via-pool-preserves w action s {t} actual good = subst
 (All (λ { (q , row) → A.ControlContent q row (G.protocolState t) })) (sym (via-pool-controls w action s actual))
 (rows-kept (G.controls s) (via-pool-kept w action s actual) good)

-- Current control lookup depends only on the control store, not the pool.
frame-at-same : ∀ w s t → G.controls t ≡ G.controls s → G.frameAt w t ≡ G.frameAt w s
frame-at-same w s t same with lookup w (G.controls s) in found
... | nothing rewrite trans (Relation.Binary.PropositionalEquality.cong (lookup w) same) found = refl
... | just row rewrite trans (Relation.Binary.PropositionalEquality.cong (lookup w) same) found = refl

join-preserves : ∀ w s {s′} → G.joinMini w s ≡ just s′ → Controls s → Controls s′
join-preserves w s eq good with G.phase (G.frameAt w s) | G.cancelPC (G.frameAt w s)
... | G.groupClosing | G.requested j = join-head-preserves w j s eq good
... | G.groupClosing | G.delivered j = join-head-preserves w j s eq good
... | G.groupClosing | G.ready = case eq of λ ()
join-preserves w s eq good | G.idle | _ = case eq of λ ()
join-preserves w s eq good | G.shutdownSelected | _ = case eq of λ ()
join-preserves w s eq good | G.stoppingTraced | _ = case eq of λ ()
join-preserves w s eq good | G.stoppingWritten | _ = case eq of λ ()
join-preserves w s eq good | G.draining | _ = case eq of λ ()
join-preserves w s eq good | G.drainReady | _ = case eq of λ ()
join-preserves w s eq good | G.stoppedTrace | _ = case eq of λ ()
join-preserves w s eq good | G.stoppedTracing | _ = case eq of λ ()
join-preserves w s eq good | G.monitorReturnedNormal | _ = case eq of λ ()
join-preserves w s eq good | G.ownerAborting err | _ = case eq of λ ()
join-preserves w s eq good | G.wholeClosing outcome | _ = case eq of λ ()
join-preserves w s eq good | G.wholeClosed outcome | _ = case eq of λ ()
join-preserves w s eq good | G.asyncFailureWritten err | _ = case eq of λ ()
join-preserves w s eq good | G.asyncDeadTracing err | _ = case eq of λ ()
join-preserves w s eq good | G.scopeDone outcome | _ = case eq of λ ()

-- request/delivery retain one physical target; delivery does not invent it.
delivered-preserves : ∀ w j rest s → G.remaining (G.frameAt w s) ≡ j ∷ rest →
 G.cancelPC (G.frameAt w s) ≡ G.requested j → Controls s →
 Controls (G.setFrame w (record (G.frameAt w s) { cancelPC = G.delivered j }) s)
delivered-preserves w j rest s remaining cancelled good = T.Rows.insert
 (λ q row → A.ControlContent q row (G.protocolState s)) w
 (record (G.frameAt w s) { cancelPC = G.delivered j }) (G.controls s)
 (cancel-content w (G.frameAt w s) (G.delivered j) (G.protocolState s) prior
   (subst (λ pc → A.CancelContent w pc (G.protocolState s)) cancelled (A.ControlContent.cancellation-backed prior))) good
 where prior = current-with-head w s j rest remaining good

deliver-preserves : ∀ w s {s′} → G.deliverMini w s ≡ just s′ → Controls s → Controls s′
deliver-preserves w s eq good with G.phase (G.frameAt w s) | G.cancelPC (G.frameAt w s) in cancelled | G.remaining (G.frameAt w s) in remaining
... | G.groupClosing | G.requested j | current ∷ rest with j ≟ current | G.miniMember w j s | G.childEligible j s
...   | yes refl | true | true with G.viaPool w (Pool.interruptJob j) s in advanced
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → delivered-preserves w j rest next
  (trans (Relation.Binary.PropositionalEquality.cong G.remaining (frame-at-same w s next (via-pool-controls w (Pool.interruptJob j) s advanced))) remaining)
  (trans (Relation.Binary.PropositionalEquality.cong G.cancelPC (frame-at-same w s next (via-pool-controls w (Pool.interruptJob j) s advanced))) cancelled)
  (via-pool-preserves w (Pool.interruptJob j) s advanced good) }
deliver-preserves w s eq good | G.groupClosing | G.requested j | current ∷ rest | no apart | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.groupClosing | G.requested j | current ∷ rest | yes same | false | _ = case eq of λ ()
deliver-preserves w s eq good | G.groupClosing | G.requested j | current ∷ rest | yes same | true | false = case eq of λ ()
deliver-preserves w s eq good | G.groupClosing | G.requested j | [] = case eq of λ ()
deliver-preserves w s eq good | G.groupClosing | G.ready | _ = case eq of λ ()
deliver-preserves w s eq good | G.groupClosing | G.delivered j | _ = case eq of λ ()
deliver-preserves w s eq good | G.idle | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.shutdownSelected | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.stoppingTraced | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.stoppingWritten | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.draining | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.drainReady | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.stoppedTrace | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.stoppedTracing | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.monitorReturnedNormal | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.ownerAborting err | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.wholeClosing outcome | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.wholeClosed outcome | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.asyncFailureWritten err | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.asyncDeadTracing err | _ | _ = case eq of λ ()
deliver-preserves w s eq good | G.scopeDone outcome | _ | _ = case eq of λ ()

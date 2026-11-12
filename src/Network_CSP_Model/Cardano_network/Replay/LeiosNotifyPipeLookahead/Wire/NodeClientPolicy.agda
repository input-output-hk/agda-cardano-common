{-# OPTIONS --safe #-}

-- Exact local node-client control language: fixed depth, unit return and Cancel failure.
-- Forecast/stop are retained existential input actions, not claims about NodeDriver inputs.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodeClientPolicy
  (Notification : Set) (notificationEq : DecidableEquality Notification) where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.List using (List; []; _∷_; _++_; map; mapMaybe; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _<_; s≤s; z≤n; _+_; _*_; _%_)
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Nat.Properties as Nat
open import Data.Nat.Induction using (<-wellFounded-fast)
import Data.Integer.Properties as Int
import Data.Maybe.Properties as Maybe
import Data.Product.Properties as Product
import Data.Unit.Properties as Unit
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as N
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientExecution Notification ⊤ notificationEq as NX
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification ⊤ as Cost
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank Notification ⊤ as Rank
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as W
import Semantics.Replay as R
import Semantics.Replay.Decide as Decide
import Semantics.Replay.Frontier as Frontier

-- The same existing typed wire alphabet retains every notification value.
Wire : Set
Wire = W.Wire

-- Each wire row names exactly the source action whose driver hook was observed.
action : Wire → C.Action
action W.request = C.sendRequest
action W.quit = C.sendQuit
action W.done = C.recvDone
action (W.reply value) = C.recvReply value

-- Node callbacks are erased only observationally; their original rules remain witnesses.
observe : N.Action → Maybe Wire
observe (N.wire a) = W.Observation.observe ⊤ a
observe _ = nothing

-- Projection retains row order and cannot fabricate callback records.
wire : List N.Action → List Wire
wire = mapMaybe observe

-- Canonical wire actions observe to their original exact typed row.
observe-action : ∀ row → observe (N.wire (action row)) ≡ just row
observe-action W.request = refl
observe-action W.quit = refl
observe-action W.done = refl
observe-action (W.reply _) = refl

-- Prepending an observed source action retains exactly its original wire position.
wire-prepend : ∀ row actions → wire (N.wire (action row) ∷ actions) ≡ row ∷ wire actions
wire-prepend W.request actions = refl
wire-prepend W.quit actions = refl
wire-prepend W.done actions = refl
wire-prepend (W.reply _) actions = refl

-- Only source scheduling and the four explicitly classified policy callbacks are hidden.
data Hidden : N.State → N.State → Set where
  scheduled : ∀ {s t} → N.Tau s t → Hidden s t
  forecasted : ∀ {s t} → N.Step s N.forecastAllows t → Hidden s t
  terminated : ∀ {s t} → N.Step s (N.stopRequested tt) t → Hidden s t
  handled : ∀ {s t msg} → N.Step s (N.handledNormal msg) t → Hidden s t
  rejected : ∀ {s t} → N.Step s N.handlerRejectedCancel t → Hidden s t

-- Visible successors use the independent source Step without replacing its guards.
Visible : N.State → Wire → N.State → Set
Visible s row t = N.Step s (N.wire (action row)) t

-- A source-action lookup has at most one target, with its independent evidence.
actionTargets : N.State → N.Action → List N.State
actionTargets s a with NX.lookup a s
... | nothing = []
... | just (t , _) = t ∷ []

-- Every listed source-action target carries the actual policy step.
action-sound : ∀ {s a t} → t ∈ actionTargets s a → N.Step s a t
action-sound {s} {a} with NX.lookup a s
... | nothing = λ ()
... | just (t , pr) = λ { (here refl) → pr ; (there ()) }

-- Executable policy lookup omits no independent target or fault outcome.
action-complete : ∀ {s a t} → N.Step s a t → t ∈ actionTargets s a
action-complete {s} {a} pr with NX.lookup a s | NX.next-complete pr
... | just (_ , _) | refl = here refl

-- Node scheduling targets are exact wrapped generic-client scheduling targets.
scheduleTargets : N.State → List N.State
scheduleTargets = NX.targets

-- Normal handling can select only the payload actually stored in the receiver.
normalTargets : N.State → List N.State
normalTargets s@(N.running (C.client m (C.handling (S.normal msg)) js rs n a q v)) =
  actionTargets s (N.handledNormal msg)
normalTargets _ = []

-- Existing source scheduling and fixed policy callbacks form one finite adequate menu.
taus : N.State → List N.State
taus s = scheduleTargets s ++ (actionTargets s N.forecastAllows ++
  (actionTargets s (N.stopRequested tt) ++
    (normalTargets s ++ actionTargets s N.handlerRejectedCancel)))

-- A listed normal handler retains its exact selected message and source guard.
normal-sound : ∀ {s t} → t ∈ normalTargets s → Hidden s t
normal-sound {N.running (C.client m (C.handling (S.normal msg)) js rs n a q v)} mem =
  handled (action-sound mem)
normal-sound {N.running (C.client m C.idle js rs n a q v)} ()
normal-sound {N.running (C.client m C.awaiting js rs n a q v)} ()
normal-sound {N.running (C.client m C.bumpArrival js rs n a q v)} ()
normal-sound {N.running (C.client m (C.inspect _) js rs n a q v)} ()
normal-sound {N.running (C.client m (C.handling S.canceled) js rs n a q v)} ()
normal-sound {N.running (C.client m (C.publish _) js rs n a q v)} ()
normal-sound {N.unexpectedCancel c} ()

-- Every actual normal-handler target is supplied by its one pending-payload lookup.
normal-complete : ∀ {s t msg} → N.Step s (N.handledNormal msg) t → t ∈ normalTargets s
normal-complete pr@(N.handled (C.delivered _)) = action-complete pr

-- Every menu member is one of the independent hidden source transitions.
taus-sound : ∀ {s t} → t ∈ taus s → Hidden s t
taus-sound {s} mem with ∈-++⁻ (scheduleTargets s) mem
... | inj₁ first = scheduled (NX.target-sound first)
... | inj₂ rest with ∈-++⁻ (actionTargets s N.forecastAllows) rest
...   | inj₁ first = forecasted (action-sound first)
...   | inj₂ rest with ∈-++⁻ (actionTargets s (N.stopRequested tt)) rest
...     | inj₁ first = terminated (action-sound first)
...     | inj₂ rest with ∈-++⁻ (normalTargets s) rest
...       | inj₁ first = normal-sound first
...       | inj₂ last = rejected (action-sound last)

-- No scheduling, fixed-depth forecast, stop, normal handling or abnormal exit is omitted.
taus-complete : ∀ {s t} → Hidden s t → t ∈ taus s
taus-complete {s} (scheduled pr) = ∈-++⁺ˡ (NX.target-complete pr)
taus-complete {s} (forecasted pr) = ∈-++⁺ʳ (scheduleTargets s) (∈-++⁺ˡ (action-complete pr))
taus-complete {s} (terminated pr) = ∈-++⁺ʳ (scheduleTargets s)
  (∈-++⁺ʳ (actionTargets s N.forecastAllows) (∈-++⁺ˡ (action-complete pr)))
taus-complete {s} (handled pr) = ∈-++⁺ʳ (scheduleTargets s)
  (∈-++⁺ʳ (actionTargets s N.forecastAllows)
    (∈-++⁺ʳ (actionTargets s (N.stopRequested tt)) (∈-++⁺ˡ (normal-complete pr))))
taus-complete {s} (rejected pr) = ∈-++⁺ʳ (scheduleTargets s)
  (∈-++⁺ʳ (actionTargets s N.forecastAllows)
    (∈-++⁺ʳ (actionTargets s (N.stopRequested tt)) (∈-++⁺ʳ (normalTargets s) (action-complete pr))))

-- Wire equality preserves constructor agency and complete normal/cancellation values.
wireEq : DecidableEquality Wire
wireEq W.request W.request = yes refl
wireEq W.request W.quit = no λ ()
wireEq W.request W.done = no λ ()
wireEq W.request (W.reply _) = no λ ()
wireEq W.quit W.request = no λ ()
wireEq W.quit W.quit = yes refl
wireEq W.quit W.done = no λ ()
wireEq W.quit (W.reply _) = no λ ()
wireEq W.done W.request = no λ ()
wireEq W.done W.quit = no λ ()
wireEq W.done W.done = yes refl
wireEq W.done (W.reply _) = no λ ()
wireEq (W.reply _) W.request = no λ ()
wireEq (W.reply _) W.quit = no λ ()
wireEq (W.reply _) W.done = no λ ()
wireEq (W.reply a) (W.reply b) with S.Executable.replyEq notificationEq a b
... | yes refl = yes refl
... | no unequal = no λ { refl → unequal refl }

-- Decidable equality transfers along a coding with a left inverse.
viaCode : {A B : Set} (code : A → B) (decode : B → A) →
  (∀ a → decode (code a) ≡ a) → DecidableEquality B → DecidableEquality A
viaCode code decode inverse _≟B_ a a′ with code a ≟B code a′
... | yes same = yes (trans (sym (inverse a)) (trans (cong decode same) (inverse a′)))
... | no different = no λ same → different (cong code same)

-- Main-thread positions are numbered; the Quit writer's marker bit is part of the number.
mainCode : C.Main → ℕ
mainCode C.poll = 0
mainCode C.issue = 1
mainCode C.writingRequest = 2
mainCode C.stopPending = 3
mainCode C.registerQuit = 4
mainCode C.collectingMaybe = 5
mainCode C.collectingWait = 6
mainCode C.adjustCollected = 7
mainCode C.draining = 8
mainCode C.awaitDone = 9
mainCode C.closed = 10
mainCode (C.writingQuit false) = 11
mainCode (C.writingQuit true) = 12

-- Every main-thread number below 13 names its position; other numbers are unused.
mainDecode : ℕ → C.Main
mainDecode 0 = C.poll
mainDecode 1 = C.issue
mainDecode 2 = C.writingRequest
mainDecode 3 = C.stopPending
mainDecode 4 = C.registerQuit
mainDecode 5 = C.collectingMaybe
mainDecode 6 = C.collectingWait
mainDecode 7 = C.adjustCollected
mainDecode 8 = C.draining
mainDecode 9 = C.awaitDone
mainDecode 10 = C.closed
mainDecode 11 = C.writingQuit false
mainDecode 12 = C.writingQuit true
mainDecode _ = C.poll

-- Decoding inverts the main-thread numbering.
mainDecode-code : ∀ m → mainDecode (mainCode m) ≡ m
mainDecode-code C.poll = refl
mainDecode-code C.issue = refl
mainDecode-code C.writingRequest = refl
mainDecode-code C.stopPending = refl
mainDecode-code C.registerQuit = refl
mainDecode-code C.collectingMaybe = refl
mainDecode-code C.collectingWait = refl
mainDecode-code C.adjustCollected = refl
mainDecode-code C.draining = refl
mainDecode-code C.awaitDone = refl
mainDecode-code C.closed = refl
mainDecode-code (C.writingQuit false) = refl
mainDecode-code (C.writingQuit true) = refl

-- Main-thread positions have decidable equality.
mainEq : DecidableEquality C.Main
mainEq = viaCode mainCode mainDecode mainDecode-code Nat._≟_

-- Receiver positions are coded by a tag, an optional held reply and the publish marker bit.
receiverCode : C.Receiver → ℕ × Maybe S.Reply × Bool
receiverCode C.idle = 0 , nothing , false
receiverCode C.awaiting = 1 , nothing , false
receiverCode C.bumpArrival = 2 , nothing , false
receiverCode (C.inspect reply) = 3 , just reply , false
receiverCode (C.handling reply) = 4 , just reply , false
receiverCode (C.publish marker) = 5 , nothing , marker

-- Receiver codes decode to their position; unused codes are irrelevant.
receiverDecode : ℕ × Maybe S.Reply × Bool → C.Receiver
receiverDecode (1 , _ , _) = C.awaiting
receiverDecode (2 , _ , _) = C.bumpArrival
receiverDecode (3 , just reply , _) = C.inspect reply
receiverDecode (4 , just reply , _) = C.handling reply
receiverDecode (5 , _ , marker) = C.publish marker
receiverDecode _ = C.idle

-- Decoding inverts the receiver coding.
receiverDecode-code : ∀ r → receiverDecode (receiverCode r) ≡ r
receiverDecode-code C.idle = refl
receiverDecode-code C.awaiting = refl
receiverDecode-code C.bumpArrival = refl
receiverDecode-code (C.inspect _) = refl
receiverDecode-code (C.handling _) = refl
receiverDecode-code (C.publish _) = refl

-- Receiver positions, including held replies, have decidable equality.
receiverEq : DecidableEquality C.Receiver
receiverEq = viaCode receiverCode receiverDecode receiverDecode-code
  (Product.≡-dec Nat._≟_ (Product.≡-dec (Maybe.≡-dec (S.Executable.replyEq notificationEq)) Bool._≟_))

-- Allocation-free list comparison from an element test.
listᵇ : {A : Set} → (A → A → Bool) → List A → List A → Bool
listᵇ f [] [] = true
listᵇ f [] (_ ∷ _) = false
listᵇ f (_ ∷ _) [] = false
listᵇ f (x ∷ xs) (y ∷ ys) with f x y
... | true = listᵇ f xs ys
... | false = false

-- A sound element test gives a sound list test.
listᵇ-sound : {A : Set} (f : A → A → Bool) → (∀ x y → f x y ≡ true → x ≡ y) →
  ∀ xs ys → listᵇ f xs ys ≡ true → xs ≡ ys
listᵇ-sound f sound [] [] _ = refl
listᵇ-sound f sound (x ∷ xs) (y ∷ ys) eq with f x y in same
... | true = cong₂ _∷_ (sound x y same) (listᵇ-sound f sound xs ys eq)

-- A reflexive element test gives a reflexive list test.
listᵇ-refl : {A : Set} (f : A → A → Bool) → (∀ x → f x x ≡ true) → ∀ xs → listᵇ f xs xs ≡ true
listᵇ-refl f reflexive [] = refl
listᵇ-refl f reflexive (x ∷ xs) with f x x | reflexive x
... | true | _ = listᵇ-refl f reflexive xs

-- List equality decided by the allocation-free test.
listEq : {A : Set} (f : A → A → Bool) → (∀ x y → f x y ≡ true → x ≡ y) → (∀ x → f x x ≡ true) →
  DecidableEquality (List A)
listEq f sound reflexive xs ys with listᵇ f xs ys in eq
... | true = yes (listᵇ-sound f sound xs ys eq)
... | false = no λ { refl → false≢true (trans (sym eq) (listᵇ-refl f reflexive xs)) }
  where
  false≢true : false ≡ true → ⊥
  false≢true ()

-- Boolean job comparison.
jobᵇ : C.Job → C.Job → Bool
jobᵇ C.responseJob C.responseJob = true
jobᵇ C.quitMarker C.quitMarker = true
jobᵇ _ _ = false

-- Job comparison is sound.
jobᵇ-sound : ∀ x y → jobᵇ x y ≡ true → x ≡ y
jobᵇ-sound C.responseJob C.responseJob _ = refl
jobᵇ-sound C.quitMarker C.quitMarker _ = refl
jobᵇ-sound C.responseJob C.quitMarker ()
jobᵇ-sound C.quitMarker C.responseJob ()

-- Job comparison is reflexive.
jobᵇ-refl : ∀ x → jobᵇ x x ≡ true
jobᵇ-refl C.responseJob = refl
jobᵇ-refl C.quitMarker = refl

-- Boolean token comparison.
tokenᵇ : C.Token → C.Token → Bool
tokenᵇ C.responseToken C.responseToken = true
tokenᵇ C.markerToken C.markerToken = true
tokenᵇ _ _ = false

-- Token comparison is sound.
tokenᵇ-sound : ∀ x y → tokenᵇ x y ≡ true → x ≡ y
tokenᵇ-sound C.responseToken C.responseToken _ = refl
tokenᵇ-sound C.markerToken C.markerToken _ = refl
tokenᵇ-sound C.responseToken C.markerToken ()
tokenᵇ-sound C.markerToken C.responseToken ()

-- Token comparison is reflexive.
tokenᵇ-refl : ∀ x → tokenᵇ x x ≡ true
tokenᵇ-refl C.responseToken = refl
tokenᵇ-refl C.markerToken = refl

-- Client states are equal field by field; the long job list is compared last.
clientEq : DecidableEquality C.State
clientEq (C.client m r js rs n a q v) (C.client m′ r′ js′ rs′ n′ a′ q′ v′) with mainEq m m′
... | no different = no λ same → different (cong C.main same)
... | yes refl with receiverEq r r′
...   | no different = no λ same → different (cong C.receiver same)
...   | yes refl with n Nat.≟ n′
...     | no different = no λ same → different (cong C.inFlight same)
...     | yes refl with a Int.≟ a′
...       | no different = no λ same → different (cong C.arrived same)
...       | yes refl with q Bool.≟ q′
...         | no different = no λ same → different (cong C.stopFlag same)
...         | yes refl with Maybe.≡-dec Unit._≟_ v v′
...           | no different = no λ same → different (cong C.returnValue same)
...           | yes refl with listEq tokenᵇ tokenᵇ-sound tokenᵇ-refl rs rs′
...             | no different = no λ same → different (cong C.results same)
...             | yes refl with listEq jobᵇ jobᵇ-sound jobᵇ-refl js js′
...               | no different = no λ same → different (cong C.jobs same)
...               | yes refl = yes refl

-- Node policy states have decidable equality.
stateEq : DecidableEquality N.State
stateEq (N.running c) (N.running c′) with clientEq c c′
... | yes refl = yes refl
... | no different = no λ { refl → different refl }
stateEq (N.running _) (N.unexpectedCancel _) = no λ ()
stateEq (N.unexpectedCancel _) (N.running _) = no λ ()
stateEq (N.unexpectedCancel c) (N.unexpectedCancel c′) with clientEq c c′
... | yes refl = yes refl
... | no different = no λ { refl → different refl }

-- Signed arrival counts are coded injectively by sign and magnitude.
arrivedCode : ℤ → ℕ
arrivedCode (+ n) = 2 * n
arrivedCode -[1+ n ] = suc (2 * n)

-- A cheap bucket hash from the short client fields; the job list is not traversed.
clientHash : C.State → ℕ
clientHash c =
  ((((mainCode (C.main c) * 7 + proj₁ (receiverCode (C.receiver c))) * 1009 + C.inFlight c) * 1013
    + arrivedCode (C.arrived c)) * 1019 + length (C.results c)) * 2 + stopBit (C.stopFlag c)
  where
  stopBit : Bool → ℕ
  stopBit true = 1
  stopBit false = 0

-- Node policy states hash by their client fields; the abnormal exit gets its own residue.
stateHash : N.State → ℕ
stateHash (N.running c) = clientHash c % 4093
stateHash (N.unexpectedCancel c) = suc (clientHash c) % 4093

-- The generic replay decision is instantiated rather than reimplemented.
replay : R.Replay 0ℓ N.State Wire
replay = record
  { _-[_]→_ = Visible
  ; _-τ→_ = Hidden
  ; _≟E_ = wireEq
  ; after = λ s row → actionTargets s (N.wire (action row))
  ; taus = taus
  ; after-sound = action-sound
  ; taus-sound = taus-sound
  ; after-complete = action-complete
  ; taus-complete = taus-complete
  }

-- Trace evidence is the existing generic semantics over the exact policy menus.
module Trace = R.Traces replay
module Decision = Decide.Decider replay
module Search = Frontier.Decider replay stateEq stateHash

-- Failure has zero residual potential; every running source state retains one credit.
potential : N.State → ℕ
potential (N.running c) = suc (Cost.clientCost c)
potential (N.unexpectedCancel c) = zero

-- All hidden callbacks reuse the established client potential, including Cancel exit.
decreases : ∀ {s t} → Hidden s t → potential t < potential s
decreases (scheduled (N.schedule pr)) = s≤s (Rank.client-decreases pr)
decreases (forecasted (N.continueAtDepth pr)) = s≤s (Rank.client-callback D.continue pr)
decreases (terminated (N.terminate pr)) = s≤s (Rank.client-callback D.terminate pr)
decreases (handled (N.handled pr)) = s≤s (Rank.client-callback D.handled pr)
decreases (rejected (N.rejectedCancel _ _)) = s≤s z≤n

-- Natural accessibility transports directly to the generic hidden-closure certificate.
from-rank : ∀ s → Acc _<_ (potential s) → Decision.τAcc s
from-rank s (acc smaller) = Decision.acc λ {t} step → from-rank t (smaller (decreases step))

-- Every policy state has a terminating hidden closure; no guessed fuel or graph bound is used.
tau-accessible : ∀ s → Decision.τAcc s
tau-accessible s = from-rank s (<-wellFounded-fast (potential s))

-- The named unit-return policy profile starts in the existing fresh node client state.
initial : N.State
initial = N.initial

-- Source compatibility retains every erased callback and its independent source execution.
SourceTrace : List Wire → Set
SourceTrace rows = Σ[ actions ∈ List N.Action ] Σ[ target ∈ N.State ]
  (N.Run initial actions target × wire actions ≡ rows)

-- Every source policy run projects to an exact generic weak trace.
from-source : ∀ {s actions t} → N.Run s actions t → Trace._⇒⟨_⟩_ s (wire actions) t
from-source N.stop = Trace.done
from-source (N.internal pr rest) = Trace.tau (scheduled pr) (from-source rest)
from-source (N.visible (N.wireRecord N.request pr) rest) = Trace.vis (N.wireRecord N.request pr) (from-source rest)
from-source (N.visible (N.wireRecord N.quit pr) rest) = Trace.vis (N.wireRecord N.quit pr) (from-source rest)
from-source (N.visible (N.wireRecord N.done pr) rest) = Trace.vis (N.wireRecord N.done pr) (from-source rest)
from-source (N.visible (N.wireRecord N.reply pr) rest) = Trace.vis (N.wireRecord N.reply pr) (from-source rest)
from-source (N.visible pr@(N.continueAtDepth _) rest) = Trace.tau (forecasted pr) (from-source rest)
from-source (N.visible pr@(N.terminate _) rest) = Trace.tau (terminated pr) (from-source rest)
from-source (N.visible pr@(N.handled _) rest) = Trace.tau (handled pr) (from-source rest)
from-source (N.visible pr@(N.rejectedCancel _ _) rest) = Trace.tau (rejected pr) (from-source rest)

-- Reconstructing a weak trace retains its original target and all policy choices.
to-source : ∀ {s rows t} → Trace._⇒⟨_⟩_ s rows t →
  Σ[ actions ∈ List N.Action ] (N.Run s actions t × wire actions ≡ rows)
to-source Trace.done = [] , N.stop , refl
to-source (Trace.tau (scheduled pr) rest) with to-source rest
... | actions , run , same = actions , N.internal pr run , same
to-source (Trace.tau (forecasted pr) rest) with to-source rest
... | actions , run , same = N.forecastAllows ∷ actions , N.visible pr run , same
to-source (Trace.tau (terminated pr) rest) with to-source rest
... | actions , run , same = N.stopRequested tt ∷ actions , N.visible pr run , same
to-source (Trace.tau (handled {msg = msg} pr) rest) with to-source rest
... | actions , run , same = N.handledNormal msg ∷ actions , N.visible pr run , same
to-source (Trace.tau (rejected pr) rest) with to-source rest
... | actions , run , same = N.handlerRejectedCancel ∷ actions , N.visible pr run , same
to-source (Trace.vis {e = row} pr rest) with to-source rest
... | actions , run , same = N.wire (action row) ∷ actions , N.visible pr run ,
  trans (wire-prepend row actions) (cong (row ∷_) same)

-- Actual source witnesses imply replay membership without additional policy premises.
source→replay : ∀ {rows} → SourceTrace rows → Trace.HasTrace initial rows
source→replay (actions , target , run , same) =
  subst (Trace.HasTrace initial) same (target , from-source run)

-- Replay acceptance reconstructs an independent source policy witness, including failure prefixes.
replay→source : ∀ {rows} → Trace.HasTrace initial rows → SourceTrace rows
replay→source (target , run) with to-source run
... | actions , source , same = actions , target , source , same

-- Both fresh prefix languages coincide for this explicitly named local node-control scope.
equivalence : ∀ rows → (SourceTrace rows → Trace.HasTrace initial rows) ×
  (Trace.HasTrace initial rows → SourceTrace rows)
equivalence rows = source→replay , replay→source

-- Acceptance builds a source run; rejection excludes every allowed hidden scheduling choice.
-- The frontier decider expands each distinct hidden-closure state once per row.
decide-source : (rows : List Wire) → Dec (SourceTrace rows)
decide-source rows with Search.hasTrace? tau-accessible initial rows
... | yes accepted = yes (replay→source accepted)
... | no denied = no λ source → denied (source→replay source)

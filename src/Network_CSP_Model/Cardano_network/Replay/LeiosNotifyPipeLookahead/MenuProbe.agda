{-# OPTIONS --guardedness #-}

-- Diagnostic calls of actual basis/menu/order functions; no trace acceptance is reported.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.MenuProbe where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_,_; proj₁)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (Notification; notificationEq; votes)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecution Notification notificationEq as Raw
import Cardano_network.LeiosNotifyPipeLookahead.DriverSearchOrder Notification notificationEq as Old
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ReadyGateOrder Notification notificationEq as Gated
import Cardano_network.Replay.LeiosNotifyPipeLookahead.UniqueBasisAdequacy Notification ⊤ as Unique
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CostProbe as Cost

-- The runtime record caches the actual whole-input unique basis for all subsequent calls.
record Prepared : Set where
  constructor prepared
  field
    typedPair : Cost.TypedPair
    normalBasis : List Notification
open Prepared public

-- No substitute/deduplicator is introduced: this is the production whole-input basis.
prepare : Cost.TypedPair → Prepared
prepare pair = prepared pair A.basis
  where
  module A = Unique.ForInput notificationEq (votes [])
    (Rows.input (Cost.clientRows pair) (Cost.serverRows pair))

-- Every state probes the same supplied whole-input lists as a ranking context, not inferred suffixes.
data Snapshot : Set where
  initial claimed selected afterQuit closed inactiveReaderClaimed : Snapshot

-- Snapshot names are stable diagnostic identifiers rather than reachability assertions.
showSnapshot : Snapshot → String
showSnapshot initial = "initial"
showSnapshot claimed = "claimed"
showSnapshot selected = "selected"
showSnapshot afterQuit = "after-quit"
showSnapshot closed = "closed"
showSnapshot inactiveReaderClaimed = "inactive-reader-claimed"

-- A claimed callback anchor follows one actually recorded Request with its client Send still pending.
claimedState : D.State
claimedState = D.pair
  (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
  (S.state S.awaitNext 0 S.claimed 0 false) [] [] (just D.request) nothing nothing nothing

-- Selection retains the actual chosen normal without executing its physical Send.
selectedState : D.State
selectedState = D.pair
  (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
  (S.state S.awaitNext 0 (S.selected (S.normal (votes []))) 0 false)
  [] [] (just D.request) nothing nothing nothing

-- The flag-disabled anchor keeps a real outstanding job and the client's Quit marker.
afterQuitState : D.State
afterQuitState = D.pair
  (C.client C.draining C.awaiting (C.quitMarker ∷ []) [] 2 (+ 0) true (just tt))
  (S.state S.flushing 0 S.claimed 0 true) [] [] nothing nothing nothing nothing

-- Both peers have completed idle shutdown and every channel/hook is empty.
closedState : D.State
closedState = D.pair
  (C.client C.closed C.idle [] [] 0 (+ 0) true (just tt))
  (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing

-- This anchor is deliberately arbitrary: closed reader plus claimed/false still exercises old lookup.
inactiveReaderState : D.State
inactiveReaderState = D.pair
  (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
  (S.state S.closed 0 S.claimed 0 false) [] [] (just D.request) nothing nothing nothing

-- Source-reachable anchor states and the explicit arbitrary negative control stay distinct.
anchor : Snapshot → D.State
anchor initial = D.initial
anchor claimed = claimedState
anchor selected = selectedState
anchor afterQuit = afterQuitState
anchor closed = closedState
anchor inactiveReaderClaimed = inactiveReaderState

-- The initial anchor is exactly the original zero-operation fresh state.
initial-reachable : ∀ contract → D.Run contract D.initial [] (anchor initial)
initial-reachable contract = D.stop

-- Ordinary channel/source operations reach the first callback under either contract.
through-claimed : ∀ {contract events target} → D.Run contract claimedState events target →
  D.Run contract D.initial (D.serverRecv D.request ∷ events) target
through-claimed continuation =
  D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.serverInternal (S.claim refl)) continuation

-- These witness only the anchor states, not a supplied benchmark input plus matching remaining suffixes.
claimed-reachable : ∀ contract → D.Run contract D.initial (D.serverRecv D.request ∷ []) claimedState
claimed-reachable contract = through-claimed D.stop

-- The selected anchor chooses the existing representative through the original successful callback.
selected-reachable : ∀ contract → D.Run contract D.initial (D.serverRecv D.request ∷ []) selectedState
selected-reachable contract = through-claimed (D.internal (D.serverCallback (S.choose refl refl)) D.stop)

-- A real Request/Quit path publishes the flag while the sender remains claimed.
afterQuit-reachable : ∀ contract → D.Run contract D.initial
  (D.serverRecv D.request ∷ D.clientSend D.request ∷ D.clientSend D.quit ∷ D.serverRecv D.quit ∷ []) afterQuitState
afterQuit-reachable contract = through-claimed $
  D.visible (D.clientSent C.sentRequest) $
  D.internal (D.clientCallback D.terminate C.stopRequested) $
  D.internal (D.clientInternal C.setStopBusy) $
  D.internal (D.clientInternal C.registerMarker) $
  D.internal (D.commitClient C.sentQuitBusy) $
  D.visible (D.clientSent C.sentQuitBusy) $
  D.internal (D.decodeServer (S.receiveQuit S.atNext)) $
  D.visible (D.serverReceived (S.receiveQuit S.atNext)) $
  D.internal (D.serverInternal S.setQuit) D.stop

-- The fully inactive anchor has an independent direct source witness, without paired search.
closed-reachable : ∀ contract → D.Run contract D.initial
  (D.clientSend D.quit ∷ D.serverRecv D.quit ∷ D.serverSend D.done ∷ D.clientRecv D.done ∷ []) closedState
closed-reachable contract =
  D.internal (D.clientCallback D.terminate C.stopRequested) $
  D.internal (D.clientInternal C.setStopIdle) $
  D.internal (D.commitClient C.sentQuitIdle) $
  D.visible (D.clientSent C.sentQuitIdle) $
  D.internal (D.decodeServer (S.receiveQuit S.atFirst)) $
  D.visible (D.serverReceived (S.receiveQuit S.atFirst)) $
  D.internal (D.serverInternal S.setQuit) $
  D.internal (D.serverInternal S.drained) $
  D.internal (D.commitServer S.finish) $
  D.visible (D.serverSent S.finish) $
  D.internal (D.decodeClient C.receivedDone) $
  D.visible (D.clientReceived C.receivedDone) D.stop

-- No later perturbation is advertised as reachable merely because its zero-nonce anchor has a witness.
nonceScope : Snapshot → String
nonceScope initial = "anchor-0-source-witnessed;positive-nonces-arbitrary-raw"
nonceScope claimed = "anchor-0-source-witnessed;positive-nonces-arbitrary-raw"
nonceScope selected = "anchor-0-source-witnessed;positive-nonces-arbitrary-raw"
nonceScope afterQuit = "anchor-0-source-witnessed;positive-nonces-arbitrary-raw"
nonceScope closed = "anchor-0-source-witnessed;positive-nonces-arbitrary-raw"
nonceScope inactiveReaderClaimed = "all-nonces-arbitrary-raw"

-- Source-level calls vary a scalar that is forced whenever targets are nonempty.
-- Empty results cannot force this scalar; no universal compiler anti-hoisting guarantee is claimed.
withNonce : ℕ → D.State → D.State
withNonce nonce (D.pair clientState (S.state r w sender completed flag) cs sc pc ps rc rs) =
  D.pair clientState (S.state r w sender (completed + nonce) flag) cs sc pc ps rc rs

-- Every Boolean field is forced through an explicit constructor split.
touchBool : Bool → ℕ
touchBool false = 1
touchBool true = 2

-- Signed client arrival counters retain their sign constructor and complete magnitude.
touchInteger : ℤ → ℕ
touchInteger (+ n) = 1 + n
touchInteger -[1+ n ] = 2 + n

-- Reuse the production summary encoder and existing complete payload forcing.
touchReply : S.Reply → ℕ
touchReply S.canceled = 1
touchReply (S.normal value) = Cost.touchServer (Rows.sendResponse (D.reply (S.normal value)) ∷ [])

-- Main-thread control, including the parameterized Quit case, is part of the forced state.
touchMain : C.Main → ℕ
touchMain C.poll = 1
touchMain C.issue = 2
touchMain C.writingRequest = 3
touchMain C.stopPending = 4
touchMain C.registerQuit = 5
touchMain C.collectingMaybe = 6
touchMain C.collectingWait = 7
touchMain C.adjustCollected = 8
touchMain C.draining = 9
touchMain C.awaitDone = 10
touchMain C.closed = 11
touchMain (C.writingQuit marker) = 12 + touchBool marker

-- Receiver selection and handling retain their actual response payload values.
touchReceiver : C.Receiver → ℕ
touchReceiver C.idle = 1
touchReceiver C.awaiting = 2
touchReceiver C.bumpArrival = 3
touchReceiver (C.inspect reply) = 4 + touchReply reply
touchReceiver (C.handling reply) = 5 + touchReply reply
touchReceiver (C.publish marker) = 6 + touchBool marker

-- Each registered response or Quit marker is visited as an individual occurrence.
touchJobs : List C.Job → ℕ
touchJobs [] = 0
touchJobs (C.responseJob ∷ rest) = 1 + touchJobs rest
touchJobs (C.quitMarker ∷ rest) = 2 + touchJobs rest

-- Completed response/marker tokens remain distinct and all list spines are forced.
touchTokens : List C.Token → ℕ
touchTokens [] = 0
touchTokens (C.responseToken ∷ rest) = 1 + touchTokens rest
touchTokens (C.markerToken ∷ rest) = 2 + touchTokens rest

-- The only return carrier here is unit; absence and a real present value are still distinguished.
touchReturn : Maybe ⊤ → ℕ
touchReturn nothing = 0
touchReturn (just tt) = 1

-- All client fields participate in the diagnostic sum, not merely its outer state constructor.
touchClient : C.State → ℕ
touchClient (C.client main receiver jobs results count arrived stopped returned) =
  touchMain main + touchReceiver receiver + touchJobs jobs + touchTokens results +
  count + touchInteger arrived + touchBool stopped + touchReturn returned

-- Every independent reader control constructor is inspected.
touchReader : S.Reader → ℕ
touchReader S.first = 1
touchReader S.admit = 2
touchReader S.register = 3
touchReader S.awaitNext = 4
touchReader S.signalQuit = 5
touchReader S.flushing = 6
touchReader S.doneReady = 7
touchReader S.closed = 8
touchReader S.raising = 9
touchReader S.failed = 10

-- Selected server packets force all represented notification fields as well as the phase.
touchSender : S.Sender → ℕ
touchSender S.idle = 1
touchSender S.claimed = 2
touchSender S.sent = 3
touchSender (S.selected reply) = 4 + touchReply reply

-- Waiting/completed counters and publication flag are forced alongside server control.
touchServer : S.State → ℕ
touchServer (S.state reader waiting sender completed flag) =
  touchReader reader + waiting + touchSender sender + completed + touchBool flag

-- Request and Quit remain distinct in physical queues and pending hooks.
touchCommand : D.ClientMessage → ℕ
touchCommand D.request = 1
touchCommand D.quit = 2

-- Physical normal/Canceled packets and final Done retain their exact summary observations.
touchResponse : D.ServerMessage → ℕ
touchResponse (D.reply reply) = 1 + touchReply reply
touchResponse D.done = 2

-- The generic forcing fold visits every physical queued occurrence in order.
touchList : ∀ {A : Set} → (A → ℕ) → List A → ℕ
touchList f [] = 0
touchList f (value ∷ rest) = 1 + f value + touchList f rest

-- Both absence and a present pending packet are forced, including its full retained fields.
touchMaybe : ∀ {A : Set} → (A → ℕ) → Maybe A → ℕ
touchMaybe f nothing = 0
touchMaybe f (just value) = 1 + f value

-- Every source/queue/hook field is common to old and gated target forcing; no proof irrelevance is assumed.
touchState : D.State → ℕ
touchState (D.pair clientState serverState cs sc pc ps rc rs) = touchClient clientState + touchServer serverState +
  touchList touchCommand cs + touchList touchResponse sc + touchMaybe touchCommand pc +
  touchMaybe touchResponse ps + touchMaybe touchResponse rc + touchMaybe touchCommand rs

-- These are collision-prone forcing totals, not hashes or source-language certificates.
record Totals : Set where
  constructor totals
  field
    count stateSum positionSum : ℕ
open Totals public

-- Summaries retain all counts while accumulating fully forced target-state fields.
combine : Totals → Totals → Totals
combine (totals a b c) (totals x y z) = totals (a + x) (b + y) (c + z)

-- A position-weighted fold also forces exact target order without claiming an injective fingerprint.
forceTargetsAt : ℕ → List D.State → Totals
forceTargetsAt position [] = totals 0 0 0
forceTargetsAt position (target ∷ rest) = combine
  (totals 1 (touchState target) (position * touchState target))
  (forceTargetsAt (suc position) rest)

-- All selected mode targets cross the same explicit full-state forcing boundary.
forceTargets : List D.State → Totals
forceTargets = forceTargetsAt 1

-- Modes select real existing functions; basis-only does not construct a target menu.
data Mode : Set where
  basisOnly rawReady gatedReady rawMenu gatedMenu orderedOld orderedGated : Mode

-- Stable names are diagnostic vocabulary, never accepted-prefix verdicts.
showMode : Mode → String
showMode basisOnly = "basis-only"
showMode rawReady = "raw-ready"
showMode gatedReady = "ready-gated"
showMode rawMenu = "raw-menu"
showMode gatedMenu = "menu-gated"
showMode orderedOld = "ordered-old"
showMode orderedGated = "ordered-gated"

-- Only the actual raw menu and old/candidate ordered-target functions are measured.
targets : Mode → S.Contract → D.State → Prepared → List D.State
targets basisOnly contract state preparedInput = []
targets rawReady contract state preparedInput = map proj₁ (Menu.readyMoves contract state)
  where
  module Menu = Raw (normalBasis preparedInput)
targets gatedReady contract state preparedInput = map proj₁ (Menu.readyMoves contract state)
  where
  module Menu = Gated (normalBasis preparedInput)
targets rawMenu contract state preparedInput = Menu.targets contract state
  where
  module Menu = Raw (normalBasis preparedInput)
targets gatedMenu contract state preparedInput = Menu.targets contract state
  where
  module Menu = Gated (normalBasis preparedInput)
targets orderedOld contract state preparedInput = Order.orderedTargets contract state
  (Cost.clientRows (typedPair preparedInput)) (Cost.serverRows (typedPair preparedInput))
  where
  module Order = Old (normalBasis preparedInput)
targets orderedGated contract state preparedInput = Order.orderedTargets contract state
  (Cost.clientRows (typedPair preparedInput)) (Cost.serverRows (typedPair preparedInput))
  where
  module Order = Gated (normalBasis preparedInput)

-- Isolated readiness comparison observes the exact original proof-list projection in both modes.
ready-targets-exact : ∀ contract state preparedInput →
  targets gatedReady contract state preparedInput ≡ targets rawReady contract state preparedInput
ready-targets-exact contract state preparedInput = cong (map proj₁) (Menu.readyMoves-exact contract state)
  where
  module Menu = Gated (normalBasis preparedInput)

-- Full unsorted menu comparison likewise preserves exact state order and multiplicity.
menu-targets-exact : ∀ contract state preparedInput →
  targets gatedMenu contract state preparedInput ≡ targets rawMenu contract state preparedInput
menu-targets-exact contract state preparedInput = Menu.targets-exact contract state
  where
  module Menu = Gated (normalBasis preparedInput)

-- Explicit stage parsing never falls back to another measurement mode.
parseMode : String → Maybe Mode
parseMode "basis-only" = just basisOnly
parseMode "raw-ready" = just rawReady
parseMode "ready-gated" = just gatedReady
parseMode "raw-menu" = just rawMenu
parseMode "menu-gated" = just gatedMenu
parseMode "ordered-old" = just orderedOld
parseMode "ordered-gated" = just orderedGated
parseMode _ = nothing

-- Snapshot selection is explicit, including the deliberately arbitrary reader-inactive control.
parseSnapshot : String → Maybe Snapshot
parseSnapshot "initial" = just initial
parseSnapshot "claimed" = just claimed
parseSnapshot "selected" = just selected
parseSnapshot "after-quit" = just afterQuit
parseSnapshot "closed" = just closed
parseSnapshot "inactive-reader-claimed" = just inactiveReaderClaimed
parseSnapshot _ = nothing

-- Exact gate equality implies identical complete target lists at every arbitrary nonce state/context.
ordered-targets-exact : ∀ contract state preparedInput →
  targets orderedGated contract state preparedInput ≡ targets orderedOld contract state preparedInput
ordered-targets-exact contract state preparedInput = Order.orderedTargets-exact contract state
  (Cost.clientRows (typedPair preparedInput)) (Cost.serverRows (typedPair preparedInput))
  where
  module Order = Gated (normalBasis preparedInput)

-- Each source-level invocation receives a different completed counter.
-- Generated call structure and compiler settings qualify measurements, especially for empty targets.
iterations : Mode → S.Contract → Snapshot → Prepared → ℕ → ℕ → Totals
iterations mode contract snapshot preparedInput zero nonce = totals 0 0 0
iterations mode contract snapshot preparedInput (suc remaining) nonce = combine
  (forceTargets (targets mode contract (withNonce nonce (anchor snapshot)) preparedInput))
  (iterations mode contract snapshot preparedInput remaining (suc nonce))

-- Old and gated modes have identical forced aggregate outputs without a reachability premise.
iterations-exact : ∀ contract snapshot preparedInput repetitions nonce →
  iterations orderedGated contract snapshot preparedInput repetitions nonce ≡
  iterations orderedOld contract snapshot preparedInput repetitions nonce
iterations-exact contract snapshot preparedInput zero nonce = refl
iterations-exact contract snapshot preparedInput (suc n) nonce = cong₂ combine
  (cong forceTargets (ordered-targets-exact contract (withNonce nonce (anchor snapshot)) preparedInput))
  (iterations-exact contract snapshot preparedInput n (suc nonce))

-- The basis forcing loop reuses the exact production payload-to-summary mapping.
touchBasis : List Notification → ℕ
touchBasis [] = 0
touchBasis (value ∷ rest) = touchReply (S.normal value) + touchBasis rest

-- Printing this before iteration forces the one cached basis spine and every retained field once.
basisReady : Prepared → String
basisReady preparedInput = "basis-ready\nbasis-count=" ++ showℕ (length (normalBasis preparedInput)) ++
  ";basis-sum=" ++ showℕ (touchBasis (normalBasis preparedInput))

-- Basis-only is the one-time common preparation baseline, regardless of requested menu repetition count.
executed : Mode → ℕ → ℕ
executed basisOnly repetitions = 0
executed _ repetitions = repetitions

-- An explicit constructor argument evaluates one aggregate, rather than repeating a source-level let.
renderTotals : Mode → Snapshot → ℕ → Totals → String
renderTotals mode snapshot repetitions (totals targetCount summedStates summedPositions) =
  "menu-probe-complete\nstage=" ++ showMode mode ++ ";snapshot=" ++ showSnapshot snapshot ++
  ";requested-iterations=" ++ showℕ repetitions ++ ";executed-iterations=" ++ showℕ (executed mode repetitions) ++
  ";targets=" ++ showℕ targetCount ++ ";state-sum=" ++ showℕ summedStates ++
  ";position-sum=" ++ showℕ summedPositions ++ "\ncontext=whole-input-ranking-only\nnonce-scope=" ++ nonceScope snapshot

-- Pass the measured aggregate once across a runtime function boundary before printing its fields.
report : Mode → S.Contract → Snapshot → ℕ → Prepared → String
report mode contract snapshot repetitions preparedInput = renderTotals mode snapshot repetitions
  (iterations mode contract snapshot preparedInput (executed mode repetitions) 0)

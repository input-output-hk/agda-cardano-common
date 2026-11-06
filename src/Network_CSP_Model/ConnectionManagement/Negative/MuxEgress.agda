{-# OPTIONS --guardedness #-}

-- Source-distinguishing finite component controls. These are actual kernel
-- paths, not whole-node or protocol/handler reachability witnesses. Grant
-- ledgers/refunds and native bearer behavior remain explicit M4/M6 obligations.
module ConnectionManagement.Negative.MuxEgress where

open import Data.Bool using (true; false)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq.Instances using (DecEq-ℕ)
import ConnectionManagement.Store as Store
import ConnectionManagement.Rules.MuxEgress as Model
import ConnectionManagement.Properties.MuxEgress as Facts
open Model using (directLane; scheduledLane; sliceLane; plainLayout; scheduledLayout)
module E = Model.Kernel ℕ
module P = Facts.Kernel ℕ

-- Concrete successors are obtained by guarded execution. Each asserted Runs
-- certificate below also proves that the corresponding execution returned just.
at : E.State → List E.Action → E.State
at start actions = fromMaybe start (P.execute actions start)
held : ℕ → E.State → Maybe ℤ
held k s = map E.keyHeld (Store.lookup k (E.cells s))
sent : ℕ → E.State → Maybe ℕ
sent k s = map E.sent (Store.lookup k (E.cells s))

start : E.State
start = E.state (scheduledLayout false) 16 1000
 ((0 , E.cell directLane (+ 0) 0) ∷ (1 , E.cell directLane (+ 0) 0) ∷
  (2 , E.cell directLane (+ 0) 0) ∷ []) []
 ((directLane , []) ∷ (scheduledLane , []) ∷ []) [] (+ 0) 0
actual-initial : E.initial (scheduledLayout false) 16 1000
 ((0 , directLane) ∷ (1 , directLane) ∷ (2 , directLane) ∷ []) ≡ just start
actual-initial = refl
setup : List E.Action
setup = E.createWanton 0 0 ∷ E.createWanton 1 1 ∷ E.createWanton 2 2 ∷ []
twoSends firstActions bothActions repeatedActions readyActions writtenActions : List E.Action
twoSends = setup ++ (E.appendPayload 0 10 ∷ E.appendPayload 1 5 ∷ [])
firstActions = twoSends ++ (E.takeFirst directLane ∷ [])
bothActions = firstActions ++ (E.selectDemand 0 ∷ E.takeFragment 0 ∷ [])
repeatedActions = bothActions ++ (E.appendPayload 0 3 ∷ E.selectDemand 0 ∷ E.takeFragment 0 ∷ [])
readyActions = repeatedActions ++ (E.selectDemand 0 ∷ [])
writtenActions = readyActions ++ (E.writeAccount 0 ∷ [])
first both repeated ready written : E.State
first = at start firstActions
both = at start bothActions
repeated = at start repeatedActions
ready = at start readyActions
written = at start writtenActions
abstract
 actual-multi-key : P.Runs start bothActions both
 actual-multi-key = P.execute-runs bothActions start refl
 actual-repeated-key : P.Runs start repeatedActions repeated
 actual-repeated-key = P.execute-runs repeatedActions start refl
 actual-success : P.Runs start writtenActions written
 actual-success = P.execute-runs writtenActions start refl

-- One batch containing two keys is not the sum of its membership counters.
multi-global-one : E.runHeld both ≡ + 1
multi-global-one = refl
multi-key-a-one : held 0 both ≡ just (+ 1)
multi-key-a-one = refl
multi-key-b-one : held 1 both ≡ just (+ 1)
multi-key-b-one = refl
repeated-key-not-two : held 0 repeated ≡ just (+ 1)
repeated-key-not-two = refl
repeated-global-one : E.runHeld repeated ≡ + 1
repeated-global-one = refl
empty-want-held-not-ready : E.protocolReady 0 first ≡ false
empty-want-held-not-ready = refl
empty-queues-held-not-drained : E.drainReady repeated ≡ false
empty-queues-held-not-drained = refl
no-write-before-seal : E.step (E.writeAccount 0) repeated ≡ nothing
no-write-before-seal = refl
success-global-zero : E.runHeld written ≡ + 0
success-global-zero = refl
success-a-bytes-with-headers : sent 0 written ≡ just 29
success-a-bytes-with-headers = refl
success-b-bytes-with-headers : sent 1 written ≡ just 13
success-b-bytes-with-headers = refl
success-protocol-ready : E.protocolReady 0 written ≡ true
success-protocol-ready = refl
success-drained : E.drainReady written ≡ true
success-drained = refl
actual-readiness : P.ProtocolReady 0 written
actual-readiness = P.protocol-ready 0 written success-protocol-ready
actual-drain : P.DrainReady written
actual-drain = P.drain-ready written success-drained
no-second-release : E.step (E.writeAccount 0) written ≡ nothing
no-second-release = refl
no-foreign-batch : E.step (E.writeAccount 999) ready ≡ nothing
no-foreign-batch = refl
no-absent-lane : E.step (E.takeFirst sliceLane) start ≡ nothing
no-absent-lane = refl
no-unknown-key : E.step (E.createWanton 99 99) start ≡ nothing
no-unknown-key = refl
unknown-not-ready : E.protocolReady 99 start ≡ false
unknown-not-ready = refl

-- Empty observation is a history boundary, not a write-time queue recheck.
afterSeal = at start (readyActions ++ (E.appendPayload 1 1 ∷ []))
afterSealWritten = at start (readyActions ++ (E.appendPayload 1 1 ∷ E.writeAccount 0 ∷ []))
sealed-write-after-enqueue : E.step (E.writeAccount 0) afterSeal ≡ just afterSealWritten
sealed-write-after-enqueue = refl
queued-after-write-not-drained : E.drainReady afterSealWritten ≡ false
queued-after-write-not-drained = refl

failed = at start (readyActions ++ (E.writeFailed 0 ∷ []))
fail-step : E.step (E.writeFailed 0) ready ≡ just failed
fail-step = refl
failure-observed : P.Failure 0 ready failed
failure-observed = P.failure 0 ready fail-step
failed-held-retained : E.runHeld failed ≡ + 1
failed-held-retained = refl
failed-sent-not-credited : E.cells failed ≡ E.cells ready
failed-sent-not-credited = refl
failed-not-writable : E.step (E.writeAccount 0) failed ≡ nothing
failed-not-writable = refl
failed-not-drained : E.drainReady failed ≡ false
failed-not-drained = refl
failedBusy = at start (readyActions ++ (E.writeFailed 0 ∷ E.appendPayload 0 1 ∷ []))
failed-lane-cannot-open-next : E.step (E.takeFirst directLane) failedBusy ≡ nothing
failed-lane-cannot-open-next = refl

-- A distinct wanton shares its source key cell; no per-generation reset.
secondWanton = at start (firstActions ++ (E.createWanton 42 0 ∷ []))
second-wanton-shared-held : held 0 secondWanton ≡ just (+ 1)
second-wanton-shared-held = refl
second-wanton-not-ready : E.protocolReady 42 secondWanton ≡ false
second-wanton-not-ready = refl

-- The byte threshold is checked before adding the next SDU. Overshoot is legal.
capStart = record start { batchLimit = 20 }
capBoth = at capStart bothActions
capReady = at capStart (bothActions ++ (E.finishBatch 0 ∷ []))
cap-write = at capStart (bothActions ++ (E.finishBatch 0 ∷ E.writeAccount 0 ∷ []))
cap-wire-overshoot : map (λ b → E.wireTotal (E.members b)) (Store.lookup 0 (E.batches capBoth)) ≡ just 31
cap-wire-overshoot = refl
cap-no-further-selection : E.step (E.selectDemand 0) capBoth ≡ nothing
cap-no-further-selection = refl
cap-seals : E.step (E.finishBatch 0) capBoth ≡ just capReady
cap-seals = refl
cap-write-succeeds : E.step (E.writeAccount 0) capReady ≡ just cap-write
cap-write-succeeds = refl
no-early-cap-seal : E.step (E.finishBatch 0) first ≡ nothing
no-early-cap-seal = refl

-- Plain still has held readiness, without grant scheduling.
plainStart = E.state plainLayout 16 1000 ((0 , E.cell scheduledLane (+ 0) 0) ∷ []) []
 ((scheduledLane , []) ∷ []) [] (+ 0) 0
plain-initial : E.initial plainLayout 16 1000 ((0 , directLane) ∷ []) ≡ just plainStart
plain-initial = refl
emptySend = at plainStart (E.createWanton 0 0 ∷ E.appendPayload 0 0 ∷ [])
twoEmpty = at plainStart (E.createWanton 0 0 ∷ E.appendPayload 0 0 ∷ E.appendPayload 0 0 ∷ [])
empty-send-data-ready : E.protocolReady 0 emptySend ≡ true
empty-send-data-ready = refl
empty-demand-not-drained : E.drainReady emptySend ≡ false
empty-demand-not-drained = refl
empty-send-repeat-queue : Store.lookup scheduledLane (E.queues twoEmpty) ≡ just (0 ∷ 0 ∷ [])
empty-send-repeat-queue = refl
plainHeld = at plainStart (E.createWanton 0 0 ∷ E.appendPayload 0 1 ∷ E.takeFirst scheduledLane ∷ [])
plain-held-not-ready : E.protocolReady 0 plainHeld ≡ false
plain-held-not-ready = refl
plain-held-not-drained : E.drainReady plainHeld ≡ false
plain-held-not-drained = refl

fallbackStart = E.state (scheduledLayout false) 16 1000 ((0 , E.cell directLane (+ 0) 0) ∷ []) []
 ((directLane , []) ∷ (scheduledLane , []) ∷ []) [] (+ 0) 0
fallback-initial : E.initial (scheduledLayout false) 16 1000 ((0 , sliceLane) ∷ []) ≡ just fallbackStart
fallback-initial = refl

-- At most one unreleased batch per lane; global drain observes all lanes.
lanedStart = record start { cells =
 (0 , E.cell directLane (+ 0) 0) ∷ (1 , E.cell scheduledLane (+ 0) 0) ∷
 (2 , E.cell directLane (+ 0) 0) ∷ [] }
laned-initial : E.initial (scheduledLayout false) 16 1000
 ((0 , directLane) ∷ (1 , scheduledLane) ∷ (2 , directLane) ∷ []) ≡ just lanedStart
laned-initial = refl
lanedActions = setup ++ (E.appendPayload 0 1 ∷ E.appendPayload 1 2 ∷
 E.takeFirst directLane ∷ E.takeFirst scheduledLane ∷ E.selectDemand 0 ∷ E.selectDemand 1 ∷ [])
laned = at lanedStart lanedActions
lanedOne = at lanedStart (lanedActions ++ (E.writeAccount 0 ∷ []))
lanedBoth = at lanedStart (lanedActions ++ (E.writeAccount 0 ∷ E.writeAccount 1 ∷ []))
abstract
 actual-two-lanes : P.Runs lanedStart lanedActions laned
 actual-two-lanes = P.execute-runs lanedActions lanedStart refl
 actual-two-writes : P.Runs lanedStart (lanedActions ++ (E.writeAccount 0 ∷ E.writeAccount 1 ∷ [])) lanedBoth
 actual-two-writes = P.execute-runs (lanedActions ++ (E.writeAccount 0 ∷ E.writeAccount 1 ∷ [])) lanedStart refl
lanes-global-two : E.runHeld laned ≡ + 2
lanes-global-two = refl
one-write-global-one : E.runHeld lanedOne ≡ + 1
one-write-global-one = refl
one-write-other-key-held : held 1 lanedOne ≡ just (+ 1)
one-write-other-key-held = refl
one-write-not-drained : E.drainReady lanedOne ≡ false
one-write-not-drained = refl
both-writes-drained : E.drainReady lanedBoth ≡ true
both-writes-drained = refl
laneBusyState = at lanedStart (lanedActions ++ (E.appendPayload 0 1 ∷ []))
second-batch-same-lane-refused : E.step (E.takeFirst directLane) laneBusyState ≡ nothing
second-batch-same-lane-refused = refl

-- The queue may refill after selectDemand. Required requeue retries the whole
-- fragment transaction, while a no-remainder fragment does not need capacity.
pendingActions : ℕ → List E.Action
pendingActions bytes = setup ++ (E.appendPayload 0 1 ∷ E.appendPayload 1 bytes ∷
 E.takeFirst directLane ∷ E.selectDemand 0 ∷ [])
refillActions = replicate 100 (E.appendPayload 2 0)
fullActions = pendingActions 20 ++ refillActions
full = at start fullActions
noRemainderActions = pendingActions 16 ++ refillActions
fullNoRemainder = at start noRemainderActions
fullTaken = at start (noRemainderActions ++ (E.takeFragment 0 ∷ []))
abstract
 actual-refill : P.Runs start fullActions full
 actual-refill = P.execute-runs fullActions start refl
 actual-no-remainder : P.Runs start (noRemainderActions ++ (E.takeFragment 0 ∷ [])) fullTaken
 actual-no-remainder = P.execute-runs (noRemainderActions ++ (E.takeFragment 0 ∷ [])) start refl
full-queue-count : map length (Store.lookup directLane (E.queues full)) ≡ just 100
full-queue-count = refl
requeue-full-refused : E.step (E.takeFragment 0) full ≡ nothing
requeue-full-refused = refl
pending-want-not-consumed : map E.payload (Store.lookup 1 (E.wantons full)) ≡ just 20
pending-want-not-consumed = refl
pending-key-not-held-yet : held 1 full ≡ just (+ 0)
pending-key-not-held-yet = refl
no-remainder-full-succeeds : E.step (E.takeFragment 0) fullNoRemainder ≡ just fullTaken
no-remainder-full-succeeds = refl
no-overfull-queue : map length (Store.lookup directLane (E.queues fullTaken)) ≡ just 100
no-overfull-queue = refl

sliceStart = E.state (scheduledLayout true) 16 1000 ((0 , E.cell sliceLane (+ 0) 0) ∷ []) []
 ((directLane , []) ∷ (scheduledLane , []) ∷ (sliceLane , []) ∷ []) [] (+ 0) 0
slice-initial : E.initial (scheduledLayout true) 16 1000 ((0 , sliceLane) ∷ []) ≡ just sliceStart
slice-initial = refl
sliceHeld = at sliceStart (E.createWanton 0 0 ∷ E.appendPayload 0 1 ∷ E.takeFirst sliceLane ∷ [])
slice-held-not-drained : E.drainReady sliceHeld ≡ false
slice-held-not-drained = refl

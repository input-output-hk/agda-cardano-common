{-# OPTIONS --guardedness #-}
-- Source close control, including timeout-to-Cold and non-asserting CM results.
module ConnectionManagement.Properties.PeerJobCloseControl where
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (DecEq-Id)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Rules.PeerJobs
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.OutboundMachine as CM

-- There is no acquisition, activation or monitor-fork PC on a close job.
data ClosePC : PC → Set where
 initial-PC : ClosePC begin
 all-PC : ClosePC awaitAll
 call-PC : ClosePC callRelease
 release-PC : ClosePC awaitRelease
 cold-PC : ∀ result → ClosePC (awaitCold result)
 done-PC : ∀ result → ClosePC (complete result)

-- Keep source branch evidence independently of frontend read certificates.
data Move (a : Action) (f : Frame) (w : World) (next : Frame) : Set where
 entry-skip : ∀ p → a ≡ enter → pc f ≡ begin → pc next ≡ awaitCold G.succeeded →
  lookup (connectionRef f) (peers w) ≡ just p →
  (P.status p ≡ P.peerCold ⊎ P.status p ≡ P.peerCooling) → Move a f w next
 entry-wait : a ≡ enter → pc f ≡ begin → pc next ≡ awaitAll → Move a f w next
 clean-all : a ≡ observeAll → pc f ≡ awaitAll → pc next ≡ callRelease → Move a f w next
 failed-all : a ≡ observeAll → pc f ≡ awaitAll → pc next ≡ awaitCold G.failed → Move a f w next
 requested : ∀ p c → a ≡ requestRelease → pc f ≡ callRelease → pc next ≡ awaitRelease →
  lookup (connectionRef f) (peers w) ≡ just p →
  CM.advance (CM.beginRelease (caller f) (P.key p)) (cm w) ≡ just c → Move a f w next
 collected-success : ∀ state → a ≡ collectRelease → pc f ≡ awaitRelease → pc next ≡ awaitCold G.succeeded →
  lookup (caller f) (CM.released (cm w)) ≡ just (R.success state) → Move a f w next
 collected-unsupported : ∀ state → a ≡ collectRelease → pc f ≡ awaitRelease → pc next ≡ awaitCold G.succeeded →
  lookup (caller f) (CM.released (cm w)) ≡ just (R.unsupported state) → Move a f w next
 collected-failure : a ≡ collectRelease → pc f ≡ awaitRelease → pc next ≡ awaitCold G.failed → Move a f w next
 operation-expired : a ≡ operationTimeout → pc f ≡ awaitAll → pc next ≡ awaitCold G.succeeded → Move a f w next
 observed-cold : ∀ result p → a ≡ observeCold → pc f ≡ awaitCold result → pc next ≡ complete result →
  lookup (connectionRef f) (peers w) ≡ just p → P.status p ≡ P.peerCold → Move a f w next
 demotion-expired : ∀ result → a ≡ demotionTimeout → pc f ≡ awaitCold result → pc next ≡ complete G.demotionTimedOut → Move a f w next

-- Classify every enabled action on an admissible close PC. Actual world/step
-- equality is supplied by the shared frame-effect proof.
classify : ∀ a f w {next w′} → G.kind (work f) ≡ G.close → ClosePC (pc f) →
 step a f w ≡ just (next , w′) → Move a f w next
classify enter (frame capturedWork actor child sock ref begin) w kind initial-PC eq rewrite kind
 with lookup ref (peers w) in found | peerStep P.close (frame capturedWork actor child sock ref begin) w
... | nothing | _ = case eq of λ ()
... | just p | nothing = case eq of λ ()
... | just p | just next with P.status p in status
...   | P.peerCold = case just-injective eq of λ { refl → entry-skip p refl refl refl found (inj₁ status) }
...   | P.peerCooling = case just-injective eq of λ { refl → entry-skip p refl refl refl found (inj₂ status) }
...   | P.peerWarm = case just-injective eq of λ { refl → entry-wait refl refl refl }
...   | P.peerHot = case just-injective eq of λ { refl → entry-wait refl refl refl }
classify observeAll (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq
 with lookup ref (peers w)
... | nothing = case eq of λ ()
... | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) |
 P.all ConnectionManagement.IGTypes.warm (P.runs p) | P.all ConnectionManagement.IGTypes.established (P.runs p)
...   | just clean | just clean | just clean = case just-injective eq of λ { refl → clean-all refl refl refl }
...   | just (errored err) | just warm | just established = case just-injective eq of λ { refl → failed-all refl refl refl }
...   | just clean | just (errored err) | just established = case just-injective eq of λ { refl → failed-all refl refl refl }
...   | just clean | just clean | just (errored err) = case just-injective eq of λ { refl → failed-all refl refl refl }
...   | nothing | _ | _ = case eq of λ ()
...   | just clean | nothing | _ = case eq of λ ()
...   | just (errored err) | nothing | _ = case eq of λ ()
...   | just clean | just clean | nothing = case eq of λ ()
...   | just clean | just (errored err) | nothing = case eq of λ ()
...   | just (errored err) | just warm | nothing = case eq of λ ()
classify requestRelease (frame capturedWork actor child sock ref callRelease) w kind call-PC eq
 with lookup ref (peers w) in found
... | nothing = case eq of λ ()
... | just p with CM.advance (CM.beginRelease actor (P.key p)) (cm w) in advanced
...   | nothing = case eq of λ ()
...   | just c = case just-injective eq of λ { refl → requested p c refl refl refl found advanced }
classify collectRelease (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq
 with lookup actor (CM.released (cm w)) in found
... | nothing = case eq of λ ()
... | just R.assertionFailure = case just-injective eq of λ { refl → collected-failure refl refl refl }
... | just (R.success state) = case just-injective eq of λ { refl → collected-success state refl refl refl found }
... | just (R.unsupported state) = case just-injective eq of λ { refl → collected-unsupported state refl refl refl found }
classify operationTimeout (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq
 with peerStep P.timeoutClose (frame capturedWork actor child sock ref awaitAll) w
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → operation-expired refl refl refl }
classify observeCold (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq
 with lookup ref (peers w) in found
... | nothing = case eq of λ ()
... | just p with P.status p in status
...   | P.peerCold = case just-injective eq of λ { refl → observed-cold result p refl refl refl found status }
...   | P.peerCooling = case eq of λ ()
...   | P.peerWarm = case eq of λ ()
...   | P.peerHot = case eq of λ ()
classify demotionTimeout (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq =
 case just-injective eq of λ { refl → demotion-expired result refl refl refl }
classify collectAcquire (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify runNext (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify publishStarted (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify markEstablished (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify launchMonitor (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify (finishHotAt time) (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify observeHot (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify observeAll (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify requestRelease (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify collectRelease (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify observeCold (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify operationTimeout (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify demotionTimeout (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify failureDelayElapsed (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify (startFailed err) (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify choosePeerPolicy (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify chooseNodePolicy (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify deliverNodeException (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify rethrowNodeException (frame capturedWork actor child sock ref begin) w kind initial-PC eq = case eq of λ ()
classify enter (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify collectAcquire (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify runNext (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify publishStarted (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify markEstablished (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify launchMonitor (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify (finishHotAt time) (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify observeHot (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify requestRelease (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify collectRelease (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify observeCold (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify demotionTimeout (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify failureDelayElapsed (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify (startFailed err) (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify choosePeerPolicy (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify chooseNodePolicy (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify deliverNodeException (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify rethrowNodeException (frame capturedWork actor child sock ref awaitAll) w kind all-PC eq = case eq of λ ()
classify enter (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify collectAcquire (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify runNext (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify publishStarted (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify markEstablished (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify launchMonitor (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify (finishHotAt time) (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify observeHot (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify observeAll (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify collectRelease (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify observeCold (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify operationTimeout (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify demotionTimeout (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify failureDelayElapsed (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify (startFailed err) (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify choosePeerPolicy (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify chooseNodePolicy (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify deliverNodeException (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify rethrowNodeException (frame capturedWork actor child sock ref callRelease) w kind call-PC eq = case eq of λ ()
classify enter (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify collectAcquire (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify runNext (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify publishStarted (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify markEstablished (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify launchMonitor (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify (finishHotAt time) (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify observeHot (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify observeAll (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify requestRelease (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify observeCold (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify operationTimeout (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify demotionTimeout (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify failureDelayElapsed (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify (startFailed err) (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify choosePeerPolicy (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify chooseNodePolicy (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify deliverNodeException (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify rethrowNodeException (frame capturedWork actor child sock ref awaitRelease) w kind release-PC eq = case eq of λ ()
classify enter (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify collectAcquire (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify runNext (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify publishStarted (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify markEstablished (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify launchMonitor (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify (finishHotAt time) (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify observeHot (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify observeAll (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify requestRelease (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify collectRelease (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify operationTimeout (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify failureDelayElapsed (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify (startFailed err) (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify choosePeerPolicy (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify chooseNodePolicy (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify deliverNodeException (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify rethrowNodeException (frame capturedWork actor child sock ref (awaitCold result)) w kind (cold-PC .result) eq = case eq of λ ()
classify enter (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify collectAcquire (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify runNext (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify publishStarted (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify markEstablished (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify launchMonitor (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify (finishHotAt time) (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify observeHot (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify observeAll (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify requestRelease (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify collectRelease (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify observeCold (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify operationTimeout (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify demotionTimeout (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify failureDelayElapsed (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify (startFailed err) (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify choosePeerPolicy (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify chooseNodePolicy (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify deliverNodeException (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()
classify rethrowNodeException (frame capturedWork actor child sock ref (complete result)) w kind (done-PC .result) eq = case eq of λ ()

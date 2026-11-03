{-# OPTIONS --guardedness #-}
module ConnectionManagement.Properties.PeerJobControl where
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Rules.PeerJobs
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.IGRegistration as IG
start-work : ∀ t f w {out} → start t f w ≡ just out → work (proj₁ out) ≡ work f
start-work t f w with lookup (connectionRef f) (peers w)
... | nothing = λ ()
... | just p = λ { refl → refl }
failed-work : ∀ f w → work (proj₁ (failedEstablishment f w)) ≡ work f
failed-work f w with lookup (connectionRef f) (peers w)
... | nothing = refl
... | just p = refl
step-work : ∀ a f w {out} → step a f w ≡ just out → work (proj₁ out) ≡ work f
step-work enter f w with pc f | G.kind (work f)
... | begin | G.establish with CM.advance (CM.beginAcquire (caller f) (A.acquireRequest (G.peer (work f)) (child f) (socketRef f) outbound nothing)) (cm w) in advanced
...   | nothing = λ ()
...   | just c = λ { refl → refl }
step-work enter f w | begin | G.activate with peerStep P.activate f w in moved
... | nothing = λ { refl → refl }
... | just w′ = λ eq → start-work ConnectionManagement.IGTypes.hot f w′ eq
step-work enter f w | begin | G.deactivate with lookup (connectionRef f) (peers w)
... | nothing = λ ()
... | just p with P.status p
...   | P.peerWarm = λ { refl → refl }
...   | P.peerHot with peerStep P.deactivate f w in moved
...     | nothing = λ ()
...     | just w′ = λ { refl → refl }
step-work enter f w | begin | G.deactivate | just p | P.peerCold = λ { refl → refl }
step-work enter f w | begin | G.deactivate | just p | P.peerCooling = λ { refl → refl }
step-work enter f w | begin | G.close with lookup (connectionRef f) (peers w) | peerStep P.close f w
... | just p | just w′ with P.status p
...   | P.peerCooling = λ { refl → refl }
...   | P.peerCold = λ { refl → refl }
...   | P.peerWarm = λ { refl → refl }
...   | P.peerHot = λ { refl → refl }
step-work enter f w | begin | G.close | nothing | _ = λ ()
step-work enter f w | begin | G.close | just p | nothing = λ ()
step-work enter f w | begin | G.forget = λ ()
step-work enter f w | awaitAcquire | _ = λ ()
step-work enter f w | (startBundle t ns) | _ = λ ()
step-work enter f w | (publishBundle t) | _ = λ ()
step-work enter f w | markWarm | _ = λ ()
step-work enter f w | forkMonitor | _ = λ ()
step-work enter f w | finishActivation | _ = λ ()
step-work enter f w | awaitHot | _ = λ ()
step-work enter f w | awaitAll | _ = λ ()
step-work enter f w | callRelease | _ = λ ()
step-work enter f w | awaitRelease | _ = λ ()
step-work enter f w | delayFailure | _ = λ ()
step-work enter f w | (awaitCold result) | _ = λ ()
step-work enter f w | (complete result) | _ = λ ()
step-work enter f w | (acquirePolicy fault) | _ = λ ()
step-work enter f w | (nodeDelivery fault) | _ = λ ()
step-work enter f w | (nodeRethrow fault) | _ = λ ()
step-work collectAcquire f w with pc f | lookup (caller f) (CM.acquired (cm w))
... | awaitAcquire | just (Cases.connected k flow h) with lookup h (IG.handles (IG.execution (Inbound.inboundGovernor (CM.core (cm w))))) | lookup (connectionRef f) (peers w)
...   | just hd | nothing = λ eq → start-work ConnectionManagement.IGTypes.warm f (record w { peers = put (connectionRef f) (P.initialPeer k h hd) (peers w) }) eq
...   | nothing | _ = λ ()
...   | just hd | just p = λ ()
step-work collectAcquire f w | awaitAcquire | just (Cases.raised _) = λ { refl → refl }
step-work collectAcquire f w | awaitAcquire | just (Cases.disconnected k reason) = λ { refl → failed-work f w }
step-work collectAcquire f w | awaitAcquire | nothing = λ ()
step-work collectAcquire f w | begin | _ = λ ()
step-work collectAcquire f w | (startBundle t ns) | _ = λ ()
step-work collectAcquire f w | (publishBundle t) | _ = λ ()
step-work collectAcquire f w | markWarm | _ = λ ()
step-work collectAcquire f w | forkMonitor | _ = λ ()
step-work collectAcquire f w | finishActivation | _ = λ ()
step-work collectAcquire f w | awaitHot | _ = λ ()
step-work collectAcquire f w | awaitAll | _ = λ ()
step-work collectAcquire f w | callRelease | _ = λ ()
step-work collectAcquire f w | awaitRelease | _ = λ ()
step-work collectAcquire f w | delayFailure | _ = λ ()
step-work collectAcquire f w | (awaitCold result) | _ = λ ()
step-work collectAcquire f w | (complete result) | _ = λ ()
step-work collectAcquire f w | (acquirePolicy fault) | _ = λ ()
step-work collectAcquire f w | (nodeDelivery fault) | _ = λ ()
step-work collectAcquire f w | (nodeRethrow fault) | _ = λ ()
step-work runNext f w with pc f
... | startBundle t [] = λ { refl → refl }
... | startBundle t (n ∷ ns) with peerStep (P.startProtocol t n) f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-work runNext f w | begin = λ ()
step-work runNext f w | awaitAcquire = λ ()
step-work runNext f w | (publishBundle t) = λ ()
step-work runNext f w | markWarm = λ ()
step-work runNext f w | forkMonitor = λ ()
step-work runNext f w | finishActivation = λ ()
step-work runNext f w | awaitHot = λ ()
step-work runNext f w | awaitAll = λ ()
step-work runNext f w | callRelease = λ ()
step-work runNext f w | awaitRelease = λ ()
step-work runNext f w | delayFailure = λ ()
step-work runNext f w | (awaitCold result) = λ ()
step-work runNext f w | (complete result) = λ ()
step-work runNext f w | (acquirePolicy fault) = λ ()
step-work runNext f w | (nodeDelivery fault) = λ ()
step-work runNext f w | (nodeRethrow fault) = λ ()
step-work publishStarted f w with pc f
... | publishBundle t with peerStep (P.publishProtocols t) f w in moved
...   | nothing = λ ()
...   | just w′ with t
...     | ConnectionManagement.IGTypes.warm = λ eq → start-work ConnectionManagement.IGTypes.established f w′ eq
...     | ConnectionManagement.IGTypes.established = λ { refl → refl }
...     | ConnectionManagement.IGTypes.hot = λ { refl → refl }
step-work publishStarted f w | begin = λ ()
step-work publishStarted f w | awaitAcquire = λ ()
step-work publishStarted f w | (startBundle t ns) = λ ()
step-work publishStarted f w | markWarm = λ ()
step-work publishStarted f w | forkMonitor = λ ()
step-work publishStarted f w | finishActivation = λ ()
step-work publishStarted f w | awaitHot = λ ()
step-work publishStarted f w | awaitAll = λ ()
step-work publishStarted f w | callRelease = λ ()
step-work publishStarted f w | awaitRelease = λ ()
step-work publishStarted f w | delayFailure = λ ()
step-work publishStarted f w | (awaitCold result) = λ ()
step-work publishStarted f w | (complete result) = λ ()
step-work publishStarted f w | (acquirePolicy fault) = λ ()
step-work publishStarted f w | (nodeDelivery fault) = λ ()
step-work publishStarted f w | (nodeRethrow fault) = λ ()
step-work markEstablished f w with pc f
... | markWarm with peerStep P.markWarm f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-work markEstablished f w | begin = λ ()
step-work markEstablished f w | awaitAcquire = λ ()
step-work markEstablished f w | (startBundle t ns) = λ ()
step-work markEstablished f w | (publishBundle t) = λ ()
step-work markEstablished f w | forkMonitor = λ ()
step-work markEstablished f w | finishActivation = λ ()
step-work markEstablished f w | awaitHot = λ ()
step-work markEstablished f w | awaitAll = λ ()
step-work markEstablished f w | callRelease = λ ()
step-work markEstablished f w | awaitRelease = λ ()
step-work markEstablished f w | delayFailure = λ ()
step-work markEstablished f w | (awaitCold result) = λ ()
step-work markEstablished f w | (complete result) = λ ()
step-work markEstablished f w | (acquirePolicy fault) = λ ()
step-work markEstablished f w | (nodeDelivery fault) = λ ()
step-work markEstablished f w | (nodeRethrow fault) = λ ()
step-work launchMonitor f w with pc f
... | forkMonitor with peerStep P.forkMonitor f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-work launchMonitor f w | begin = λ ()
step-work launchMonitor f w | awaitAcquire = λ ()
step-work launchMonitor f w | (startBundle t ns) = λ ()
step-work launchMonitor f w | (publishBundle t) = λ ()
step-work launchMonitor f w | markWarm = λ ()
step-work launchMonitor f w | finishActivation = λ ()
step-work launchMonitor f w | awaitHot = λ ()
step-work launchMonitor f w | awaitAll = λ ()
step-work launchMonitor f w | callRelease = λ ()
step-work launchMonitor f w | awaitRelease = λ ()
step-work launchMonitor f w | delayFailure = λ ()
step-work launchMonitor f w | (awaitCold result) = λ ()
step-work launchMonitor f w | (complete result) = λ ()
step-work launchMonitor f w | (acquirePolicy fault) = λ ()
step-work launchMonitor f w | (nodeDelivery fault) = λ ()
step-work launchMonitor f w | (nodeRethrow fault) = λ ()
step-work (finishHotAt time) f w with pc f
... | finishActivation with peerStep (P.markPromoted time) f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-work (finishHotAt time) f w | begin = λ ()
step-work (finishHotAt time) f w | awaitAcquire = λ ()
step-work (finishHotAt time) f w | (startBundle t ns) = λ ()
step-work (finishHotAt time) f w | (publishBundle t) = λ ()
step-work (finishHotAt time) f w | markWarm = λ ()
step-work (finishHotAt time) f w | forkMonitor = λ ()
step-work (finishHotAt time) f w | awaitHot = λ ()
step-work (finishHotAt time) f w | awaitAll = λ ()
step-work (finishHotAt time) f w | callRelease = λ ()
step-work (finishHotAt time) f w | awaitRelease = λ ()
step-work (finishHotAt time) f w | delayFailure = λ ()
step-work (finishHotAt time) f w | (awaitCold result) = λ ()
step-work (finishHotAt time) f w | (complete result) = λ ()
step-work (finishHotAt time) f w | (acquirePolicy fault) = λ ()
step-work (finishHotAt time) f w | (nodeDelivery fault) = λ ()
step-work (finishHotAt time) f w | (nodeRethrow fault) = λ ()
step-work observeHot f w with pc f | lookup (connectionRef f) (peers w)
... | awaitHot | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | peerStep P.finishDeactivate f w
...   | just clean | just w′ = λ { refl → refl }
...   | just (errored _) | just w′ = λ { refl → refl }
...   | nothing | _ = λ ()
...   | just clean | nothing = λ ()
...   | just (errored err) | nothing = λ ()
step-work observeHot f w | awaitHot | nothing = λ ()
step-work observeHot f w | begin | _ = λ ()
step-work observeHot f w | awaitAcquire | _ = λ ()
step-work observeHot f w | (startBundle t ns) | _ = λ ()
step-work observeHot f w | (publishBundle t) | _ = λ ()
step-work observeHot f w | markWarm | _ = λ ()
step-work observeHot f w | forkMonitor | _ = λ ()
step-work observeHot f w | finishActivation | _ = λ ()
step-work observeHot f w | awaitAll | _ = λ ()
step-work observeHot f w | callRelease | _ = λ ()
step-work observeHot f w | awaitRelease | _ = λ ()
step-work observeHot f w | delayFailure | _ = λ ()
step-work observeHot f w | (awaitCold result) | _ = λ ()
step-work observeHot f w | (complete result) | _ = λ ()
step-work observeHot f w | (acquirePolicy fault) | _ = λ ()
step-work observeHot f w | (nodeDelivery fault) | _ = λ ()
step-work observeHot f w | (nodeRethrow fault) | _ = λ ()
step-work observeAll f w with pc f | lookup (connectionRef f) (peers w)
... | awaitAll | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | P.all ConnectionManagement.IGTypes.warm (P.runs p) | P.all ConnectionManagement.IGTypes.established (P.runs p)
...   | just clean | just clean | just clean = λ { refl → refl }
...   | just clean | just clean | just (errored e₃) = λ { refl → refl }
...   | just clean | just (errored e₂) | just clean = λ { refl → refl }
...   | just clean | just (errored e₂) | just (errored e₃) = λ { refl → refl }
...   | just (errored e₁) | just clean | just clean = λ { refl → refl }
...   | just (errored e₁) | just clean | just (errored e₃) = λ { refl → refl }
...   | just (errored e₁) | just (errored e₂) | just clean = λ { refl → refl }
...   | just (errored e₁) | just (errored e₂) | just (errored e₃) = λ { refl → refl }
...   | nothing | _ | _ = λ ()
...   | just clean | nothing | _ = λ ()
...   | just (errored e) | nothing | _ = λ ()
...   | just clean | just clean | nothing = λ ()
...   | just clean | just (errored e₂) | nothing = λ ()
...   | just (errored e₁) | just clean | nothing = λ ()
...   | just (errored e₁) | just (errored e₂) | nothing = λ ()
step-work observeAll f w | awaitAll | nothing = λ ()
step-work observeAll f w | begin | _ = λ ()
step-work observeAll f w | awaitAcquire | _ = λ ()
step-work observeAll f w | (startBundle t ns) | _ = λ ()
step-work observeAll f w | (publishBundle t) | _ = λ ()
step-work observeAll f w | markWarm | _ = λ ()
step-work observeAll f w | forkMonitor | _ = λ ()
step-work observeAll f w | finishActivation | _ = λ ()
step-work observeAll f w | awaitHot | _ = λ ()
step-work observeAll f w | callRelease | _ = λ ()
step-work observeAll f w | awaitRelease | _ = λ ()
step-work observeAll f w | delayFailure | _ = λ ()
step-work observeAll f w | (awaitCold result) | _ = λ ()
step-work observeAll f w | (complete result) | _ = λ ()
step-work observeAll f w | (acquirePolicy fault) | _ = λ ()
step-work observeAll f w | (nodeDelivery fault) | _ = λ ()
step-work observeAll f w | (nodeRethrow fault) | _ = λ ()
step-work requestRelease f w with pc f | lookup (connectionRef f) (peers w)
... | callRelease | just p with CM.advance (CM.beginRelease (caller f) (P.key p)) (cm w) in advanced
...   | nothing = λ ()
...   | just c = λ { refl → refl }
step-work requestRelease f w | callRelease | nothing = λ ()
step-work requestRelease f w | begin | _ = λ ()
step-work requestRelease f w | awaitAcquire | _ = λ ()
step-work requestRelease f w | (startBundle t ns) | _ = λ ()
step-work requestRelease f w | (publishBundle t) | _ = λ ()
step-work requestRelease f w | markWarm | _ = λ ()
step-work requestRelease f w | forkMonitor | _ = λ ()
step-work requestRelease f w | finishActivation | _ = λ ()
step-work requestRelease f w | awaitHot | _ = λ ()
step-work requestRelease f w | awaitAll | _ = λ ()
step-work requestRelease f w | awaitRelease | _ = λ ()
step-work requestRelease f w | delayFailure | _ = λ ()
step-work requestRelease f w | (awaitCold result) | _ = λ ()
step-work requestRelease f w | (complete result) | _ = λ ()
step-work requestRelease f w | (acquirePolicy fault) | _ = λ ()
step-work requestRelease f w | (nodeDelivery fault) | _ = λ ()
step-work requestRelease f w | (nodeRethrow fault) | _ = λ ()
step-work collectRelease f w with pc f | lookup (caller f) (CM.released (cm w))
... | awaitRelease | just R.assertionFailure = λ { refl → refl }
... | awaitRelease | just (R.success state) = λ { refl → refl }
... | awaitRelease | just (R.unsupported state) = λ { refl → refl }
... | awaitRelease | nothing = λ ()
step-work collectRelease f w | begin | _ = λ ()
step-work collectRelease f w | awaitAcquire | _ = λ ()
step-work collectRelease f w | (startBundle t ns) | _ = λ ()
step-work collectRelease f w | (publishBundle t) | _ = λ ()
step-work collectRelease f w | markWarm | _ = λ ()
step-work collectRelease f w | forkMonitor | _ = λ ()
step-work collectRelease f w | finishActivation | _ = λ ()
step-work collectRelease f w | awaitHot | _ = λ ()
step-work collectRelease f w | awaitAll | _ = λ ()
step-work collectRelease f w | callRelease | _ = λ ()
step-work collectRelease f w | delayFailure | _ = λ ()
step-work collectRelease f w | (awaitCold result) | _ = λ ()
step-work collectRelease f w | (complete result) | _ = λ ()
step-work collectRelease f w | (acquirePolicy fault) | _ = λ ()
step-work collectRelease f w | (nodeDelivery fault) | _ = λ ()
step-work collectRelease f w | (nodeRethrow fault) | _ = λ ()
step-work observeCold f w with pc f | lookup (connectionRef f) (peers w)
... | awaitCold result | just p with P.status p
...   | P.peerCold = λ { refl → refl }
...   | P.peerHot = λ ()
...   | P.peerWarm = λ ()
...   | P.peerCooling = λ ()
step-work observeCold f w | awaitCold result | nothing = λ ()
step-work observeCold f w | begin | _ = λ ()
step-work observeCold f w | awaitAcquire | _ = λ ()
step-work observeCold f w | (startBundle t ns) | _ = λ ()
step-work observeCold f w | (publishBundle t) | _ = λ ()
step-work observeCold f w | markWarm | _ = λ ()
step-work observeCold f w | forkMonitor | _ = λ ()
step-work observeCold f w | finishActivation | _ = λ ()
step-work observeCold f w | awaitHot | _ = λ ()
step-work observeCold f w | awaitAll | _ = λ ()
step-work observeCold f w | callRelease | _ = λ ()
step-work observeCold f w | awaitRelease | _ = λ ()
step-work observeCold f w | delayFailure | _ = λ ()
step-work observeCold f w | (complete result) | _ = λ ()
step-work observeCold f w | (acquirePolicy fault) | _ = λ ()
step-work observeCold f w | (nodeDelivery fault) | _ = λ ()
step-work observeCold f w | (nodeRethrow fault) | _ = λ ()
step-work operationTimeout f w with pc f
... | awaitHot with peerStep P.timeoutDeactivate f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-work operationTimeout f w | awaitAll with peerStep P.timeoutClose f w in moved
... | nothing = λ ()
... | just w′ = λ { refl → refl }
step-work operationTimeout f w | begin = λ ()
step-work operationTimeout f w | awaitAcquire = λ ()
step-work operationTimeout f w | (startBundle t ns) = λ ()
step-work operationTimeout f w | (publishBundle t) = λ ()
step-work operationTimeout f w | markWarm = λ ()
step-work operationTimeout f w | forkMonitor = λ ()
step-work operationTimeout f w | finishActivation = λ ()
step-work operationTimeout f w | callRelease = λ ()
step-work operationTimeout f w | awaitRelease = λ ()
step-work operationTimeout f w | delayFailure = λ ()
step-work operationTimeout f w | (awaitCold result) = λ ()
step-work operationTimeout f w | (complete result) = λ ()
step-work operationTimeout f w | (acquirePolicy fault) = λ ()
step-work operationTimeout f w | (nodeDelivery fault) = λ ()
step-work operationTimeout f w | (nodeRethrow fault) = λ ()
step-work demotionTimeout f w with pc f
... | awaitCold _ = λ { refl → refl }
step-work demotionTimeout f w | begin = λ ()
step-work demotionTimeout f w | awaitAcquire = λ ()
step-work demotionTimeout f w | (startBundle t ns) = λ ()
step-work demotionTimeout f w | (publishBundle t) = λ ()
step-work demotionTimeout f w | markWarm = λ ()
step-work demotionTimeout f w | forkMonitor = λ ()
step-work demotionTimeout f w | finishActivation = λ ()
step-work demotionTimeout f w | awaitHot = λ ()
step-work demotionTimeout f w | awaitAll = λ ()
step-work demotionTimeout f w | callRelease = λ ()
step-work demotionTimeout f w | awaitRelease = λ ()
step-work demotionTimeout f w | delayFailure = λ ()
step-work demotionTimeout f w | (complete result) = λ ()
step-work demotionTimeout f w | (acquirePolicy fault) = λ ()
step-work demotionTimeout f w | (nodeDelivery fault) = λ ()
step-work demotionTimeout f w | (nodeRethrow fault) = λ ()
step-work failureDelayElapsed f w with pc f
... | delayFailure = λ { refl → refl }
step-work failureDelayElapsed f w | begin = λ ()
step-work failureDelayElapsed f w | awaitAcquire = λ ()
step-work failureDelayElapsed f w | (startBundle t ns) = λ ()
step-work failureDelayElapsed f w | (publishBundle t) = λ ()
step-work failureDelayElapsed f w | markWarm = λ ()
step-work failureDelayElapsed f w | forkMonitor = λ ()
step-work failureDelayElapsed f w | finishActivation = λ ()
step-work failureDelayElapsed f w | awaitHot = λ ()
step-work failureDelayElapsed f w | awaitAll = λ ()
step-work failureDelayElapsed f w | callRelease = λ ()
step-work failureDelayElapsed f w | awaitRelease = λ ()
step-work failureDelayElapsed f w | (awaitCold result) = λ ()
step-work failureDelayElapsed f w | (complete result) = λ ()
step-work failureDelayElapsed f w | (acquirePolicy fault) = λ ()
step-work failureDelayElapsed f w | (nodeDelivery fault) = λ ()
step-work failureDelayElapsed f w | (nodeRethrow fault) = λ ()
step-work (startFailed err) f w with pc f | G.kind (work f)
... | startBundle t (n ∷ _) | G.establish with peerStep (P.startProtocol t n) f w in moved
...   | nothing = λ { refl → failed-work f w }
...   | just _ = λ ()
step-work (startFailed err) f w | startBundle t (n ∷ _) | G.activate with peerStep (P.startProtocol t n) f w in moved
... | nothing = λ { refl → refl }
... | just _ = λ ()
step-work (startFailed err) f w | startBundle t [] | _ = λ ()
step-work (startFailed err) f w | startBundle t (n ∷ ns) | G.forget = λ ()
step-work (startFailed err) f w | startBundle t (n ∷ ns) | G.close = λ ()
step-work (startFailed err) f w | startBundle t (n ∷ ns) | G.deactivate = λ ()
step-work (startFailed err) f w | begin | _ = λ ()
step-work (startFailed err) f w | awaitAcquire | _ = λ ()
step-work (startFailed err) f w | (publishBundle t) | _ = λ ()
step-work (startFailed err) f w | markWarm | _ = λ ()
step-work (startFailed err) f w | forkMonitor | _ = λ ()
step-work (startFailed err) f w | finishActivation | _ = λ ()
step-work (startFailed err) f w | awaitHot | _ = λ ()
step-work (startFailed err) f w | awaitAll | _ = λ ()
step-work (startFailed err) f w | callRelease | _ = λ ()
step-work (startFailed err) f w | awaitRelease | _ = λ ()
step-work (startFailed err) f w | delayFailure | _ = λ ()
step-work (startFailed err) f w | (awaitCold result) | _ = λ ()
step-work (startFailed err) f w | (complete result) | _ = λ ()
step-work (startFailed err) f w | (acquirePolicy fault) | _ = λ ()
step-work (startFailed err) f w | (nodeDelivery fault) | _ = λ ()
step-work (startFailed err) f w | (nodeRethrow fault) | _ = λ ()
step-work choosePeerPolicy f w with pc f
... | (acquirePolicy fault) = λ { refl → failed-work f w }
step-work choosePeerPolicy f w | begin = λ ()
step-work choosePeerPolicy f w | awaitAcquire = λ ()
step-work choosePeerPolicy f w | (startBundle t ns) = λ ()
step-work choosePeerPolicy f w | (publishBundle t) = λ ()
step-work choosePeerPolicy f w | markWarm = λ ()
step-work choosePeerPolicy f w | forkMonitor = λ ()
step-work choosePeerPolicy f w | finishActivation = λ ()
step-work choosePeerPolicy f w | awaitHot = λ ()
step-work choosePeerPolicy f w | awaitAll = λ ()
step-work choosePeerPolicy f w | callRelease = λ ()
step-work choosePeerPolicy f w | awaitRelease = λ ()
step-work choosePeerPolicy f w | delayFailure = λ ()
step-work choosePeerPolicy f w | (awaitCold result) = λ ()
step-work choosePeerPolicy f w | (complete result) = λ ()
step-work choosePeerPolicy f w | (nodeDelivery fault) = λ ()
step-work choosePeerPolicy f w | (nodeRethrow fault) = λ ()
step-work chooseNodePolicy f w with pc f
... | (acquirePolicy fault) = λ { refl → refl }
step-work chooseNodePolicy f w | begin = λ ()
step-work chooseNodePolicy f w | awaitAcquire = λ ()
step-work chooseNodePolicy f w | (startBundle t ns) = λ ()
step-work chooseNodePolicy f w | (publishBundle t) = λ ()
step-work chooseNodePolicy f w | markWarm = λ ()
step-work chooseNodePolicy f w | forkMonitor = λ ()
step-work chooseNodePolicy f w | finishActivation = λ ()
step-work chooseNodePolicy f w | awaitHot = λ ()
step-work chooseNodePolicy f w | awaitAll = λ ()
step-work chooseNodePolicy f w | callRelease = λ ()
step-work chooseNodePolicy f w | awaitRelease = λ ()
step-work chooseNodePolicy f w | delayFailure = λ ()
step-work chooseNodePolicy f w | (awaitCold result) = λ ()
step-work chooseNodePolicy f w | (complete result) = λ ()
step-work chooseNodePolicy f w | (nodeDelivery fault) = λ ()
step-work chooseNodePolicy f w | (nodeRethrow fault) = λ ()
step-work deliverNodeException f w with pc f
... | (nodeDelivery fault) = λ { refl → refl }
step-work deliverNodeException f w | begin = λ ()
step-work deliverNodeException f w | awaitAcquire = λ ()
step-work deliverNodeException f w | (startBundle t ns) = λ ()
step-work deliverNodeException f w | (publishBundle t) = λ ()
step-work deliverNodeException f w | markWarm = λ ()
step-work deliverNodeException f w | forkMonitor = λ ()
step-work deliverNodeException f w | finishActivation = λ ()
step-work deliverNodeException f w | awaitHot = λ ()
step-work deliverNodeException f w | awaitAll = λ ()
step-work deliverNodeException f w | callRelease = λ ()
step-work deliverNodeException f w | awaitRelease = λ ()
step-work deliverNodeException f w | delayFailure = λ ()
step-work deliverNodeException f w | (awaitCold result) = λ ()
step-work deliverNodeException f w | (complete result) = λ ()
step-work deliverNodeException f w | (acquirePolicy fault) = λ ()
step-work deliverNodeException f w | (nodeRethrow fault) = λ ()
step-work rethrowNodeException f w with pc f
... | (nodeRethrow fault) = λ { refl → failed-work f w }
step-work rethrowNodeException f w | begin = λ ()
step-work rethrowNodeException f w | awaitAcquire = λ ()
step-work rethrowNodeException f w | (startBundle t ns) = λ ()
step-work rethrowNodeException f w | (publishBundle t) = λ ()
step-work rethrowNodeException f w | markWarm = λ ()
step-work rethrowNodeException f w | forkMonitor = λ ()
step-work rethrowNodeException f w | finishActivation = λ ()
step-work rethrowNodeException f w | awaitHot = λ ()
step-work rethrowNodeException f w | awaitAll = λ ()
step-work rethrowNodeException f w | callRelease = λ ()
step-work rethrowNodeException f w | awaitRelease = λ ()
step-work rethrowNodeException f w | delayFailure = λ ()
step-work rethrowNodeException f w | (awaitCold result) = λ ()
step-work rethrowNodeException f w | (complete result) = λ ()
step-work rethrowNodeException f w | (acquirePolicy fault) = λ ()
step-work rethrowNodeException f w | (nodeDelivery fault) = λ ()

-- Deactivation has no activation, acquisition or release continuation. The
-- failed Cold wait cannot turn into a successful completion.
data DeactivatePC : PC → Set where
 initial-PC : DeactivatePC begin
 hot-PC : DeactivatePC awaitHot
 failed-PC : DeactivatePC (awaitCold G.failed)
 done-PC : ∀ outcome → DeactivatePC (complete outcome)
data Success (a : Action) (f : Frame) (w : World) : Set where
 early-warm : ∀ p → a ≡ enter → pc f ≡ begin → lookup (connectionRef f) (peers w) ≡ just p →
  P.status p ≡ P.peerWarm → Success a f w
 hot-wait : a ≡ observeHot → pc f ≡ awaitHot → Success a f w
deact-progress : ∀ a f w {out} → G.kind (work f) ≡ G.deactivate → DeactivatePC (pc f) →
 step a f w ≡ just out → DeactivatePC (pc (proj₁ out)) × (pc (proj₁ out) ≡ complete G.succeeded → Success a f w)
deact-progress enter (frame capturedWork caller child sock ref begin) w kind initial-PC eq rewrite kind with lookup ref (peers w) in found
... | nothing = case eq of λ ()
... | just peer with P.status peer in status
...   | P.peerWarm = case just-injective eq of λ { refl → done-PC G.succeeded , (λ _ → early-warm peer refl refl found status) }
...   | P.peerHot with peerStep P.deactivate (frame capturedWork caller child sock ref begin) w
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → hot-PC , (λ ()) }
deact-progress enter (frame capturedWork caller child sock ref begin) w kind initial-PC eq | just peer | P.peerCold =
 case just-injective eq of λ { refl → failed-PC , (λ ()) }
deact-progress enter (frame capturedWork caller child sock ref begin) w kind initial-PC eq | just peer | P.peerCooling =
 case just-injective eq of λ { refl → failed-PC , (λ ()) }
deact-progress observeHot (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq with lookup ref (peers w)
... | nothing = case eq of λ ()
... | just peer with P.all ConnectionManagement.IGTypes.hot (P.runs peer) | peerStep P.finishDeactivate (frame capturedWork caller child sock ref awaitHot) w
...   | just clean | just next = case just-injective eq of λ { refl → done-PC G.succeeded , (λ _ → hot-wait refl refl) }
...   | just (errored err) | just next = case just-injective eq of λ { refl → failed-PC , (λ ()) }
...   | nothing | _ = case eq of λ ()
...   | just clean | nothing = case eq of λ ()
...   | just (errored err) | nothing = case eq of λ ()
deact-progress operationTimeout (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq with peerStep P.timeoutDeactivate (frame capturedWork caller child sock ref awaitHot) w
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → failed-PC , (λ ()) }
deact-progress observeCold (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq with lookup ref (peers w)
... | nothing = case eq of λ ()
... | just peer with P.status peer
...   | P.peerCold = case just-injective eq of λ { refl → done-PC G.failed , (λ ()) }
...   | P.peerCooling = case eq of λ ()
...   | P.peerWarm = case eq of λ ()
...   | P.peerHot = case eq of λ ()
deact-progress demotionTimeout (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq =
 case just-injective eq of λ { refl → done-PC G.demotionTimedOut , (λ ()) }
deact-progress collectAcquire (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress runNext (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress publishStarted (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress markEstablished (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress launchMonitor (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress (finishHotAt time) (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress observeHot (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress observeAll (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress requestRelease (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress collectRelease (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress observeCold (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress operationTimeout (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress demotionTimeout (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress failureDelayElapsed (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress (startFailed err) (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress choosePeerPolicy (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress chooseNodePolicy (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress deliverNodeException (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress rethrowNodeException (frame capturedWork caller child sock ref begin) w kind initial-PC eq = case eq of λ ()
deact-progress enter (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress collectAcquire (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress runNext (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress publishStarted (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress markEstablished (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress launchMonitor (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress (finishHotAt time) (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress observeAll (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress requestRelease (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress collectRelease (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress observeCold (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress demotionTimeout (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress failureDelayElapsed (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress (startFailed err) (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress choosePeerPolicy (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress chooseNodePolicy (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress deliverNodeException (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress rethrowNodeException (frame capturedWork caller child sock ref awaitHot) w kind hot-PC eq = case eq of λ ()
deact-progress enter (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress collectAcquire (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress runNext (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress publishStarted (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress markEstablished (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress launchMonitor (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress (finishHotAt time) (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress observeHot (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress observeAll (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress requestRelease (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress collectRelease (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress operationTimeout (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress failureDelayElapsed (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress (startFailed err) (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress choosePeerPolicy (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress chooseNodePolicy (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress deliverNodeException (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress rethrowNodeException (frame capturedWork caller child sock ref (awaitCold G.failed)) w kind failed-PC eq = case eq of λ ()
deact-progress enter (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress collectAcquire (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress runNext (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress publishStarted (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress markEstablished (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress launchMonitor (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress (finishHotAt time) (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress observeHot (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress observeAll (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress requestRelease (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress collectRelease (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress observeCold (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress operationTimeout (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress demotionTimeout (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress failureDelayElapsed (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress (startFailed err) (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress choosePeerPolicy (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress chooseNodePolicy (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress deliverNodeException (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()
deact-progress rethrowNodeException (frame capturedWork caller child sock ref (complete outcome)) w kind (done-PC .outcome) eq = case eq of λ ()

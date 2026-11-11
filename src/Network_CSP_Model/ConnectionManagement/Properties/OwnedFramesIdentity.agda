{-# OPTIONS --guardedness #-}

-- Peer-job steps keep their captured caller and resource identities. Only the
-- continuation PC changes, even when a call or peer-world write is performed.
module ConnectionManagement.Properties.OwnedFramesIdentity where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import ConnectionManagement.Domain using (WorkerId; SocketId; PeerConnectionId; outbound)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.IGTypes using (clean; errored)
import ConnectionManagement.IGTypes
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Rules.PeerJobs using
  (Frame; World; Action; caller; child; socketRef; connectionRef; work; pc; cm; peers;
   step; start; peerStep; failedEstablishment; begin; awaitAcquire; startBundle;
   publishBundle; markWarm; forkMonitor; finishActivation; awaitHot; awaitAll;
   callRelease; awaitRelease; delayFailure; awaitCold; complete; acquirePolicy;
   nodeDelivery; nodeRethrow; enter; collectAcquire; runNext; publishStarted;
   markEstablished; launchMonitor; finishHotAt; observeHot; observeAll;
   requestRelease; collectRelease; observeCold; operationTimeout; demotionTimeout;
   failureDelayElapsed; startFailed; choosePeerPolicy; chooseNodePolicy;
   deliverNodeException; rethrowNodeException)

-- The stamp deliberately excludes the mutable continuation.
stamp : Frame → G.Job × WorkerId × WorkerId × SocketId × PeerConnectionId
stamp f = work f , caller f , child f , socketRef f , connectionRef f

-- Starting a bundle keeps its caller and captured resource identities.
start-stamp : ∀ t f w {out} → start t f w ≡ just out → stamp (proj₁ out) ≡ stamp f
start-stamp t f w with lookup (connectionRef f) (peers w)
... | nothing = λ ()
... | just p = λ { refl → refl }

-- Failure restores the peer status and changes only the continuation.
failed-stamp : ∀ f w → stamp (proj₁ (failedEstablishment f w)) ≡ stamp f
failed-stamp f w with lookup (connectionRef f) (peers w)
... | nothing = refl
... | just p = refl

-- This exhaustive tree follows PeerJobs.step, including all failure branches.
step-stamp : ∀ a f w {out} → step a f w ≡ just out → stamp (proj₁ out) ≡ stamp f
step-stamp enter f w with pc f | G.kind (work f)
... | begin | G.establish with CM.advance (CM.beginAcquire (caller f) (A.acquireRequest (G.peer (work f)) (child f) (socketRef f) outbound nothing)) (cm w) in advanced
...   | nothing = λ ()
...   | just c = λ { refl → refl }
step-stamp enter f w | begin | G.activate with peerStep P.activate f w in moved
... | nothing = λ { refl → refl }
... | just w′ = λ eq → start-stamp ConnectionManagement.IGTypes.hot f w′ eq
step-stamp enter f w | begin | G.deactivate with lookup (connectionRef f) (peers w)
... | nothing = λ ()
... | just p with P.status p
...   | P.peerWarm = λ { refl → refl }
...   | P.peerHot with peerStep P.deactivate f w in moved
...     | nothing = λ ()
...     | just w′ = λ { refl → refl }
step-stamp enter f w | begin | G.deactivate | just p | P.peerCold = λ { refl → refl }
step-stamp enter f w | begin | G.deactivate | just p | P.peerCooling = λ { refl → refl }
step-stamp enter f w | begin | G.close with lookup (connectionRef f) (peers w) | peerStep P.close f w
... | just p | just w′ with P.status p
...   | P.peerCooling = λ { refl → refl }
...   | P.peerCold = λ { refl → refl }
...   | P.peerWarm = λ { refl → refl }
...   | P.peerHot = λ { refl → refl }
step-stamp enter f w | begin | G.close | nothing | _ = λ ()
step-stamp enter f w | begin | G.close | just p | nothing = λ ()
step-stamp enter f w | begin | G.forget = λ ()
step-stamp enter f w | awaitAcquire | _ = λ ()
step-stamp enter f w | (startBundle t ns) | _ = λ ()
step-stamp enter f w | (publishBundle t) | _ = λ ()
step-stamp enter f w | markWarm | _ = λ ()
step-stamp enter f w | forkMonitor | _ = λ ()
step-stamp enter f w | finishActivation | _ = λ ()
step-stamp enter f w | awaitHot | _ = λ ()
step-stamp enter f w | awaitAll | _ = λ ()
step-stamp enter f w | callRelease | _ = λ ()
step-stamp enter f w | awaitRelease | _ = λ ()
step-stamp enter f w | delayFailure | _ = λ ()
step-stamp enter f w | (awaitCold result) | _ = λ ()
step-stamp enter f w | (complete result) | _ = λ ()
step-stamp enter f w | (acquirePolicy fault) | _ = λ ()
step-stamp enter f w | (nodeDelivery fault) | _ = λ ()
step-stamp enter f w | (nodeRethrow fault) | _ = λ ()
step-stamp collectAcquire f w with pc f | lookup (caller f) (CM.acquired (cm w))
... | awaitAcquire | just (Cases.connected k flow h) with lookup h (IG.handles (IG.execution (Inbound.inboundGovernor (CM.core (cm w))))) | lookup (connectionRef f) (peers w)
...   | just hd | nothing = λ eq → start-stamp ConnectionManagement.IGTypes.warm f (record w { peers = put (connectionRef f) (P.initialPeer k h hd) (peers w) }) eq
...   | nothing | _ = λ ()
...   | just hd | just p = λ ()
step-stamp collectAcquire f w | awaitAcquire | just (Cases.raised _) = λ { refl → refl }
step-stamp collectAcquire f w | awaitAcquire | just (Cases.disconnected k reason) = λ { refl → failed-stamp f w }
step-stamp collectAcquire f w | awaitAcquire | nothing = λ ()
step-stamp collectAcquire f w | begin | _ = λ ()
step-stamp collectAcquire f w | (startBundle t ns) | _ = λ ()
step-stamp collectAcquire f w | (publishBundle t) | _ = λ ()
step-stamp collectAcquire f w | markWarm | _ = λ ()
step-stamp collectAcquire f w | forkMonitor | _ = λ ()
step-stamp collectAcquire f w | finishActivation | _ = λ ()
step-stamp collectAcquire f w | awaitHot | _ = λ ()
step-stamp collectAcquire f w | awaitAll | _ = λ ()
step-stamp collectAcquire f w | callRelease | _ = λ ()
step-stamp collectAcquire f w | awaitRelease | _ = λ ()
step-stamp collectAcquire f w | delayFailure | _ = λ ()
step-stamp collectAcquire f w | (awaitCold result) | _ = λ ()
step-stamp collectAcquire f w | (complete result) | _ = λ ()
step-stamp collectAcquire f w | (acquirePolicy fault) | _ = λ ()
step-stamp collectAcquire f w | (nodeDelivery fault) | _ = λ ()
step-stamp collectAcquire f w | (nodeRethrow fault) | _ = λ ()
step-stamp runNext f w with pc f
... | startBundle t [] = λ { refl → refl }
... | startBundle t (n ∷ ns) with peerStep (P.startProtocol t n) f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-stamp runNext f w | begin = λ ()
step-stamp runNext f w | awaitAcquire = λ ()
step-stamp runNext f w | (publishBundle t) = λ ()
step-stamp runNext f w | markWarm = λ ()
step-stamp runNext f w | forkMonitor = λ ()
step-stamp runNext f w | finishActivation = λ ()
step-stamp runNext f w | awaitHot = λ ()
step-stamp runNext f w | awaitAll = λ ()
step-stamp runNext f w | callRelease = λ ()
step-stamp runNext f w | awaitRelease = λ ()
step-stamp runNext f w | delayFailure = λ ()
step-stamp runNext f w | (awaitCold result) = λ ()
step-stamp runNext f w | (complete result) = λ ()
step-stamp runNext f w | (acquirePolicy fault) = λ ()
step-stamp runNext f w | (nodeDelivery fault) = λ ()
step-stamp runNext f w | (nodeRethrow fault) = λ ()
step-stamp publishStarted f w with pc f
... | publishBundle t with peerStep (P.publishProtocols t) f w in moved
...   | nothing = λ ()
...   | just w′ with t
...     | ConnectionManagement.IGTypes.warm = λ eq → start-stamp ConnectionManagement.IGTypes.established f w′ eq
...     | ConnectionManagement.IGTypes.established = λ { refl → refl }
...     | ConnectionManagement.IGTypes.hot = λ { refl → refl }
step-stamp publishStarted f w | begin = λ ()
step-stamp publishStarted f w | awaitAcquire = λ ()
step-stamp publishStarted f w | (startBundle t ns) = λ ()
step-stamp publishStarted f w | markWarm = λ ()
step-stamp publishStarted f w | forkMonitor = λ ()
step-stamp publishStarted f w | finishActivation = λ ()
step-stamp publishStarted f w | awaitHot = λ ()
step-stamp publishStarted f w | awaitAll = λ ()
step-stamp publishStarted f w | callRelease = λ ()
step-stamp publishStarted f w | awaitRelease = λ ()
step-stamp publishStarted f w | delayFailure = λ ()
step-stamp publishStarted f w | (awaitCold result) = λ ()
step-stamp publishStarted f w | (complete result) = λ ()
step-stamp publishStarted f w | (acquirePolicy fault) = λ ()
step-stamp publishStarted f w | (nodeDelivery fault) = λ ()
step-stamp publishStarted f w | (nodeRethrow fault) = λ ()
step-stamp markEstablished f w with pc f
... | markWarm with peerStep P.markWarm f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-stamp markEstablished f w | begin = λ ()
step-stamp markEstablished f w | awaitAcquire = λ ()
step-stamp markEstablished f w | (startBundle t ns) = λ ()
step-stamp markEstablished f w | (publishBundle t) = λ ()
step-stamp markEstablished f w | forkMonitor = λ ()
step-stamp markEstablished f w | finishActivation = λ ()
step-stamp markEstablished f w | awaitHot = λ ()
step-stamp markEstablished f w | awaitAll = λ ()
step-stamp markEstablished f w | callRelease = λ ()
step-stamp markEstablished f w | awaitRelease = λ ()
step-stamp markEstablished f w | delayFailure = λ ()
step-stamp markEstablished f w | (awaitCold result) = λ ()
step-stamp markEstablished f w | (complete result) = λ ()
step-stamp markEstablished f w | (acquirePolicy fault) = λ ()
step-stamp markEstablished f w | (nodeDelivery fault) = λ ()
step-stamp markEstablished f w | (nodeRethrow fault) = λ ()
step-stamp launchMonitor f w with pc f
... | forkMonitor with peerStep P.forkMonitor f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-stamp launchMonitor f w | begin = λ ()
step-stamp launchMonitor f w | awaitAcquire = λ ()
step-stamp launchMonitor f w | (startBundle t ns) = λ ()
step-stamp launchMonitor f w | (publishBundle t) = λ ()
step-stamp launchMonitor f w | markWarm = λ ()
step-stamp launchMonitor f w | finishActivation = λ ()
step-stamp launchMonitor f w | awaitHot = λ ()
step-stamp launchMonitor f w | awaitAll = λ ()
step-stamp launchMonitor f w | callRelease = λ ()
step-stamp launchMonitor f w | awaitRelease = λ ()
step-stamp launchMonitor f w | delayFailure = λ ()
step-stamp launchMonitor f w | (awaitCold result) = λ ()
step-stamp launchMonitor f w | (complete result) = λ ()
step-stamp launchMonitor f w | (acquirePolicy fault) = λ ()
step-stamp launchMonitor f w | (nodeDelivery fault) = λ ()
step-stamp launchMonitor f w | (nodeRethrow fault) = λ ()
step-stamp (finishHotAt time) f w with pc f
... | finishActivation with peerStep (P.markPromoted time) f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-stamp (finishHotAt time) f w | begin = λ ()
step-stamp (finishHotAt time) f w | awaitAcquire = λ ()
step-stamp (finishHotAt time) f w | (startBundle t ns) = λ ()
step-stamp (finishHotAt time) f w | (publishBundle t) = λ ()
step-stamp (finishHotAt time) f w | markWarm = λ ()
step-stamp (finishHotAt time) f w | forkMonitor = λ ()
step-stamp (finishHotAt time) f w | awaitHot = λ ()
step-stamp (finishHotAt time) f w | awaitAll = λ ()
step-stamp (finishHotAt time) f w | callRelease = λ ()
step-stamp (finishHotAt time) f w | awaitRelease = λ ()
step-stamp (finishHotAt time) f w | delayFailure = λ ()
step-stamp (finishHotAt time) f w | (awaitCold result) = λ ()
step-stamp (finishHotAt time) f w | (complete result) = λ ()
step-stamp (finishHotAt time) f w | (acquirePolicy fault) = λ ()
step-stamp (finishHotAt time) f w | (nodeDelivery fault) = λ ()
step-stamp (finishHotAt time) f w | (nodeRethrow fault) = λ ()
step-stamp observeHot f w with pc f | lookup (connectionRef f) (peers w)
... | awaitHot | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | peerStep P.finishDeactivate f w
...   | just clean | just w′ = λ { refl → refl }
...   | just (errored _) | just w′ = λ { refl → refl }
...   | nothing | _ = λ ()
...   | just clean | nothing = λ ()
...   | just (errored err) | nothing = λ ()
step-stamp observeHot f w | awaitHot | nothing = λ ()
step-stamp observeHot f w | begin | _ = λ ()
step-stamp observeHot f w | awaitAcquire | _ = λ ()
step-stamp observeHot f w | (startBundle t ns) | _ = λ ()
step-stamp observeHot f w | (publishBundle t) | _ = λ ()
step-stamp observeHot f w | markWarm | _ = λ ()
step-stamp observeHot f w | forkMonitor | _ = λ ()
step-stamp observeHot f w | finishActivation | _ = λ ()
step-stamp observeHot f w | awaitAll | _ = λ ()
step-stamp observeHot f w | callRelease | _ = λ ()
step-stamp observeHot f w | awaitRelease | _ = λ ()
step-stamp observeHot f w | delayFailure | _ = λ ()
step-stamp observeHot f w | (awaitCold result) | _ = λ ()
step-stamp observeHot f w | (complete result) | _ = λ ()
step-stamp observeHot f w | (acquirePolicy fault) | _ = λ ()
step-stamp observeHot f w | (nodeDelivery fault) | _ = λ ()
step-stamp observeHot f w | (nodeRethrow fault) | _ = λ ()
step-stamp observeAll f w with pc f | lookup (connectionRef f) (peers w)
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
step-stamp observeAll f w | awaitAll | nothing = λ ()
step-stamp observeAll f w | begin | _ = λ ()
step-stamp observeAll f w | awaitAcquire | _ = λ ()
step-stamp observeAll f w | (startBundle t ns) | _ = λ ()
step-stamp observeAll f w | (publishBundle t) | _ = λ ()
step-stamp observeAll f w | markWarm | _ = λ ()
step-stamp observeAll f w | forkMonitor | _ = λ ()
step-stamp observeAll f w | finishActivation | _ = λ ()
step-stamp observeAll f w | awaitHot | _ = λ ()
step-stamp observeAll f w | callRelease | _ = λ ()
step-stamp observeAll f w | awaitRelease | _ = λ ()
step-stamp observeAll f w | delayFailure | _ = λ ()
step-stamp observeAll f w | (awaitCold result) | _ = λ ()
step-stamp observeAll f w | (complete result) | _ = λ ()
step-stamp observeAll f w | (acquirePolicy fault) | _ = λ ()
step-stamp observeAll f w | (nodeDelivery fault) | _ = λ ()
step-stamp observeAll f w | (nodeRethrow fault) | _ = λ ()
step-stamp requestRelease f w with pc f | lookup (connectionRef f) (peers w)
... | callRelease | just p with CM.advance (CM.beginRelease (caller f) (P.key p)) (cm w) in advanced
...   | nothing = λ ()
...   | just c = λ { refl → refl }
step-stamp requestRelease f w | callRelease | nothing = λ ()
step-stamp requestRelease f w | begin | _ = λ ()
step-stamp requestRelease f w | awaitAcquire | _ = λ ()
step-stamp requestRelease f w | (startBundle t ns) | _ = λ ()
step-stamp requestRelease f w | (publishBundle t) | _ = λ ()
step-stamp requestRelease f w | markWarm | _ = λ ()
step-stamp requestRelease f w | forkMonitor | _ = λ ()
step-stamp requestRelease f w | finishActivation | _ = λ ()
step-stamp requestRelease f w | awaitHot | _ = λ ()
step-stamp requestRelease f w | awaitAll | _ = λ ()
step-stamp requestRelease f w | awaitRelease | _ = λ ()
step-stamp requestRelease f w | delayFailure | _ = λ ()
step-stamp requestRelease f w | (awaitCold result) | _ = λ ()
step-stamp requestRelease f w | (complete result) | _ = λ ()
step-stamp requestRelease f w | (acquirePolicy fault) | _ = λ ()
step-stamp requestRelease f w | (nodeDelivery fault) | _ = λ ()
step-stamp requestRelease f w | (nodeRethrow fault) | _ = λ ()
step-stamp collectRelease f w with pc f | lookup (caller f) (CM.released (cm w))
... | awaitRelease | just R.assertionFailure = λ { refl → refl }
... | awaitRelease | just (R.success state) = λ { refl → refl }
... | awaitRelease | just (R.unsupported state) = λ { refl → refl }
... | awaitRelease | nothing = λ ()
step-stamp collectRelease f w | begin | _ = λ ()
step-stamp collectRelease f w | awaitAcquire | _ = λ ()
step-stamp collectRelease f w | (startBundle t ns) | _ = λ ()
step-stamp collectRelease f w | (publishBundle t) | _ = λ ()
step-stamp collectRelease f w | markWarm | _ = λ ()
step-stamp collectRelease f w | forkMonitor | _ = λ ()
step-stamp collectRelease f w | finishActivation | _ = λ ()
step-stamp collectRelease f w | awaitHot | _ = λ ()
step-stamp collectRelease f w | awaitAll | _ = λ ()
step-stamp collectRelease f w | callRelease | _ = λ ()
step-stamp collectRelease f w | delayFailure | _ = λ ()
step-stamp collectRelease f w | (awaitCold result) | _ = λ ()
step-stamp collectRelease f w | (complete result) | _ = λ ()
step-stamp collectRelease f w | (acquirePolicy fault) | _ = λ ()
step-stamp collectRelease f w | (nodeDelivery fault) | _ = λ ()
step-stamp collectRelease f w | (nodeRethrow fault) | _ = λ ()
step-stamp observeCold f w with pc f | lookup (connectionRef f) (peers w)
... | awaitCold result | just p with P.status p
...   | P.peerCold = λ { refl → refl }
...   | P.peerHot = λ ()
...   | P.peerWarm = λ ()
...   | P.peerCooling = λ ()
step-stamp observeCold f w | awaitCold result | nothing = λ ()
step-stamp observeCold f w | begin | _ = λ ()
step-stamp observeCold f w | awaitAcquire | _ = λ ()
step-stamp observeCold f w | (startBundle t ns) | _ = λ ()
step-stamp observeCold f w | (publishBundle t) | _ = λ ()
step-stamp observeCold f w | markWarm | _ = λ ()
step-stamp observeCold f w | forkMonitor | _ = λ ()
step-stamp observeCold f w | finishActivation | _ = λ ()
step-stamp observeCold f w | awaitHot | _ = λ ()
step-stamp observeCold f w | awaitAll | _ = λ ()
step-stamp observeCold f w | callRelease | _ = λ ()
step-stamp observeCold f w | awaitRelease | _ = λ ()
step-stamp observeCold f w | delayFailure | _ = λ ()
step-stamp observeCold f w | (complete result) | _ = λ ()
step-stamp observeCold f w | (acquirePolicy fault) | _ = λ ()
step-stamp observeCold f w | (nodeDelivery fault) | _ = λ ()
step-stamp observeCold f w | (nodeRethrow fault) | _ = λ ()
step-stamp operationTimeout f w with pc f
... | awaitHot with peerStep P.timeoutDeactivate f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → refl }
step-stamp operationTimeout f w | awaitAll with peerStep P.timeoutClose f w in moved
... | nothing = λ ()
... | just w′ = λ { refl → refl }
step-stamp operationTimeout f w | begin = λ ()
step-stamp operationTimeout f w | awaitAcquire = λ ()
step-stamp operationTimeout f w | (startBundle t ns) = λ ()
step-stamp operationTimeout f w | (publishBundle t) = λ ()
step-stamp operationTimeout f w | markWarm = λ ()
step-stamp operationTimeout f w | forkMonitor = λ ()
step-stamp operationTimeout f w | finishActivation = λ ()
step-stamp operationTimeout f w | callRelease = λ ()
step-stamp operationTimeout f w | awaitRelease = λ ()
step-stamp operationTimeout f w | delayFailure = λ ()
step-stamp operationTimeout f w | (awaitCold result) = λ ()
step-stamp operationTimeout f w | (complete result) = λ ()
step-stamp operationTimeout f w | (acquirePolicy fault) = λ ()
step-stamp operationTimeout f w | (nodeDelivery fault) = λ ()
step-stamp operationTimeout f w | (nodeRethrow fault) = λ ()
step-stamp demotionTimeout f w with pc f
... | awaitCold _ = λ { refl → refl }
step-stamp demotionTimeout f w | begin = λ ()
step-stamp demotionTimeout f w | awaitAcquire = λ ()
step-stamp demotionTimeout f w | (startBundle t ns) = λ ()
step-stamp demotionTimeout f w | (publishBundle t) = λ ()
step-stamp demotionTimeout f w | markWarm = λ ()
step-stamp demotionTimeout f w | forkMonitor = λ ()
step-stamp demotionTimeout f w | finishActivation = λ ()
step-stamp demotionTimeout f w | awaitHot = λ ()
step-stamp demotionTimeout f w | awaitAll = λ ()
step-stamp demotionTimeout f w | callRelease = λ ()
step-stamp demotionTimeout f w | awaitRelease = λ ()
step-stamp demotionTimeout f w | delayFailure = λ ()
step-stamp demotionTimeout f w | (complete result) = λ ()
step-stamp demotionTimeout f w | (acquirePolicy fault) = λ ()
step-stamp demotionTimeout f w | (nodeDelivery fault) = λ ()
step-stamp demotionTimeout f w | (nodeRethrow fault) = λ ()
step-stamp failureDelayElapsed f w with pc f
... | delayFailure = λ { refl → refl }
step-stamp failureDelayElapsed f w | begin = λ ()
step-stamp failureDelayElapsed f w | awaitAcquire = λ ()
step-stamp failureDelayElapsed f w | (startBundle t ns) = λ ()
step-stamp failureDelayElapsed f w | (publishBundle t) = λ ()
step-stamp failureDelayElapsed f w | markWarm = λ ()
step-stamp failureDelayElapsed f w | forkMonitor = λ ()
step-stamp failureDelayElapsed f w | finishActivation = λ ()
step-stamp failureDelayElapsed f w | awaitHot = λ ()
step-stamp failureDelayElapsed f w | awaitAll = λ ()
step-stamp failureDelayElapsed f w | callRelease = λ ()
step-stamp failureDelayElapsed f w | awaitRelease = λ ()
step-stamp failureDelayElapsed f w | (awaitCold result) = λ ()
step-stamp failureDelayElapsed f w | (complete result) = λ ()
step-stamp failureDelayElapsed f w | (acquirePolicy fault) = λ ()
step-stamp failureDelayElapsed f w | (nodeDelivery fault) = λ ()
step-stamp failureDelayElapsed f w | (nodeRethrow fault) = λ ()
step-stamp (startFailed err) f w with pc f | G.kind (work f)
... | startBundle t (n ∷ _) | G.establish with peerStep (P.startProtocol t n) f w in moved
...   | nothing = λ { refl → failed-stamp f w }
...   | just _ = λ ()
step-stamp (startFailed err) f w | startBundle t (n ∷ _) | G.activate with peerStep (P.startProtocol t n) f w in moved
... | nothing = λ { refl → refl }
... | just _ = λ ()
step-stamp (startFailed err) f w | startBundle t [] | _ = λ ()
step-stamp (startFailed err) f w | startBundle t (n ∷ ns) | G.forget = λ ()
step-stamp (startFailed err) f w | startBundle t (n ∷ ns) | G.close = λ ()
step-stamp (startFailed err) f w | startBundle t (n ∷ ns) | G.deactivate = λ ()
step-stamp (startFailed err) f w | begin | _ = λ ()
step-stamp (startFailed err) f w | awaitAcquire | _ = λ ()
step-stamp (startFailed err) f w | (publishBundle t) | _ = λ ()
step-stamp (startFailed err) f w | markWarm | _ = λ ()
step-stamp (startFailed err) f w | forkMonitor | _ = λ ()
step-stamp (startFailed err) f w | finishActivation | _ = λ ()
step-stamp (startFailed err) f w | awaitHot | _ = λ ()
step-stamp (startFailed err) f w | awaitAll | _ = λ ()
step-stamp (startFailed err) f w | callRelease | _ = λ ()
step-stamp (startFailed err) f w | awaitRelease | _ = λ ()
step-stamp (startFailed err) f w | delayFailure | _ = λ ()
step-stamp (startFailed err) f w | (awaitCold result) | _ = λ ()
step-stamp (startFailed err) f w | (complete result) | _ = λ ()
step-stamp (startFailed err) f w | (acquirePolicy fault) | _ = λ ()
step-stamp (startFailed err) f w | (nodeDelivery fault) | _ = λ ()
step-stamp (startFailed err) f w | (nodeRethrow fault) | _ = λ ()
step-stamp choosePeerPolicy f w with pc f
... | (acquirePolicy fault) = λ { refl → failed-stamp f w }
step-stamp choosePeerPolicy f w | begin = λ ()
step-stamp choosePeerPolicy f w | awaitAcquire = λ ()
step-stamp choosePeerPolicy f w | (startBundle t ns) = λ ()
step-stamp choosePeerPolicy f w | (publishBundle t) = λ ()
step-stamp choosePeerPolicy f w | markWarm = λ ()
step-stamp choosePeerPolicy f w | forkMonitor = λ ()
step-stamp choosePeerPolicy f w | finishActivation = λ ()
step-stamp choosePeerPolicy f w | awaitHot = λ ()
step-stamp choosePeerPolicy f w | awaitAll = λ ()
step-stamp choosePeerPolicy f w | callRelease = λ ()
step-stamp choosePeerPolicy f w | awaitRelease = λ ()
step-stamp choosePeerPolicy f w | delayFailure = λ ()
step-stamp choosePeerPolicy f w | (awaitCold result) = λ ()
step-stamp choosePeerPolicy f w | (complete result) = λ ()
step-stamp choosePeerPolicy f w | (nodeDelivery fault) = λ ()
step-stamp choosePeerPolicy f w | (nodeRethrow fault) = λ ()
step-stamp chooseNodePolicy f w with pc f
... | (acquirePolicy fault) = λ { refl → refl }
step-stamp chooseNodePolicy f w | begin = λ ()
step-stamp chooseNodePolicy f w | awaitAcquire = λ ()
step-stamp chooseNodePolicy f w | (startBundle t ns) = λ ()
step-stamp chooseNodePolicy f w | (publishBundle t) = λ ()
step-stamp chooseNodePolicy f w | markWarm = λ ()
step-stamp chooseNodePolicy f w | forkMonitor = λ ()
step-stamp chooseNodePolicy f w | finishActivation = λ ()
step-stamp chooseNodePolicy f w | awaitHot = λ ()
step-stamp chooseNodePolicy f w | awaitAll = λ ()
step-stamp chooseNodePolicy f w | callRelease = λ ()
step-stamp chooseNodePolicy f w | awaitRelease = λ ()
step-stamp chooseNodePolicy f w | delayFailure = λ ()
step-stamp chooseNodePolicy f w | (awaitCold result) = λ ()
step-stamp chooseNodePolicy f w | (complete result) = λ ()
step-stamp chooseNodePolicy f w | (nodeDelivery fault) = λ ()
step-stamp chooseNodePolicy f w | (nodeRethrow fault) = λ ()
step-stamp deliverNodeException f w with pc f
... | (nodeDelivery fault) = λ { refl → refl }
step-stamp deliverNodeException f w | begin = λ ()
step-stamp deliverNodeException f w | awaitAcquire = λ ()
step-stamp deliverNodeException f w | (startBundle t ns) = λ ()
step-stamp deliverNodeException f w | (publishBundle t) = λ ()
step-stamp deliverNodeException f w | markWarm = λ ()
step-stamp deliverNodeException f w | forkMonitor = λ ()
step-stamp deliverNodeException f w | finishActivation = λ ()
step-stamp deliverNodeException f w | awaitHot = λ ()
step-stamp deliverNodeException f w | awaitAll = λ ()
step-stamp deliverNodeException f w | callRelease = λ ()
step-stamp deliverNodeException f w | awaitRelease = λ ()
step-stamp deliverNodeException f w | delayFailure = λ ()
step-stamp deliverNodeException f w | (awaitCold result) = λ ()
step-stamp deliverNodeException f w | (complete result) = λ ()
step-stamp deliverNodeException f w | (acquirePolicy fault) = λ ()
step-stamp deliverNodeException f w | (nodeRethrow fault) = λ ()
step-stamp rethrowNodeException f w with pc f
... | (nodeRethrow fault) = λ { refl → failed-stamp f w }
step-stamp rethrowNodeException f w | begin = λ ()
step-stamp rethrowNodeException f w | awaitAcquire = λ ()
step-stamp rethrowNodeException f w | (startBundle t ns) = λ ()
step-stamp rethrowNodeException f w | (publishBundle t) = λ ()
step-stamp rethrowNodeException f w | markWarm = λ ()
step-stamp rethrowNodeException f w | forkMonitor = λ ()
step-stamp rethrowNodeException f w | finishActivation = λ ()
step-stamp rethrowNodeException f w | awaitHot = λ ()
step-stamp rethrowNodeException f w | awaitAll = λ ()
step-stamp rethrowNodeException f w | callRelease = λ ()
step-stamp rethrowNodeException f w | awaitRelease = λ ()
step-stamp rethrowNodeException f w | delayFailure = λ ()
step-stamp rethrowNodeException f w | (awaitCold result) = λ ()
step-stamp rethrowNodeException f w | (complete result) = λ ()
step-stamp rethrowNodeException f w | (acquirePolicy fault) = λ ()
step-stamp rethrowNodeException f w | (nodeDelivery fault) = λ ()

-- Caller equality is the projection needed for job/followup separation.
step-caller : ∀ a f w {out} → step a f w ≡ just out → caller (proj₁ out) ≡ caller f
step-caller a f w eq = cong (λ x → proj₁ (proj₂ x)) (step-stamp a f w eq)

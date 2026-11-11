{-# OPTIONS --guardedness #-}

-- Exact source effects of every PeerJobs.step: unchanged caller keys, or a
-- begin action that installs its matching await continuation.
module ConnectionManagement.Properties.OwnedFramesJobSource where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import ConnectionManagement.Domain using (WorkerId; SocketId; PeerConnectionId; ConnectionKey; outbound)
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

open import ConnectionManagement.Properties.OutboundKeys using (KeySame; same-refl; same-trans; fields-same)

-- The only key-changing job writers are the two actual call initializers.
data Effect (f : Frame) (w : World) (out : Frame × World) : Set where
  same : KeySame (cm w) (cm (proj₂ out)) → Effect f w out
  acquired : ∀ request → CM.advance (CM.beginAcquire (caller f) request) (cm w) ≡ just (cm (proj₂ out)) →
    pc (proj₁ out) ≡ awaitAcquire → Effect f w out
  released : ∀ key → CM.advance (CM.beginRelease (caller f) key) (cm w) ≡ just (cm (proj₂ out)) →
    pc (proj₁ out) ≡ awaitRelease → Effect f w out

-- Peer-only writers change the dispatcher core and retain all caller tables.
peer-trans : ∀ a f w {w′ c} → peerStep a f w ≡ just w′ → KeySame c (cm w) → KeySame c (cm w′)
peer-trans a f w with lookup (connectionRef f) (peers w)
... | nothing = λ ()
... | just p with P.step a p (Inbound.inboundGovernor (CM.core (cm w))) (Inbound.world (CM.core (cm w)))
...   | nothing = λ ()
...   | just (p′ , ig′) = λ { refl before → same-trans before (fields-same _ _ refl refl refl refl) }

-- Starting a protocol bundle leaves the source exactly unchanged.
start-trans : ∀ t f w {out c} → start t f w ≡ just out → KeySame c (cm w) → KeySame c (cm (proj₂ out))
start-trans t f w with lookup (connectionRef f) (peers w)
... | nothing = λ ()
... | just p = λ { refl before → before }

-- Failure restoration changes peer status, outside the caller-table observer.
failed-trans : ∀ f w {c} → KeySame c (cm w) → KeySame c (cm (proj₂ (failedEstablishment f w)))
failed-trans f w before with lookup (connectionRef f) (peers w)
... | nothing = before
... | just p = before

-- The exhaustive with-tree includes every J action and its unavailable cases.
step-effect : ∀ a f w {out} → step a f w ≡ just out → Effect f w out
step-effect enter f w with pc f | G.kind (work f)
... | begin | G.establish with CM.advance (CM.beginAcquire (caller f) (A.acquireRequest (G.peer (work f)) (child f) (socketRef f) outbound nothing)) (cm w) in advanced
...   | nothing = λ ()
...   | just c = λ { refl → acquired (A.acquireRequest (G.peer (work f)) (child f) (socketRef f) outbound nothing) advanced refl }
step-effect enter f w | begin | G.activate with peerStep P.activate f w in moved
... | nothing = λ { refl → same ((same-refl (cm w))) }
... | just w′ = λ eq → same (start-trans ConnectionManagement.IGTypes.hot f w′ eq (peer-trans _ f w moved (same-refl (cm w))))
step-effect enter f w | begin | G.deactivate with lookup (connectionRef f) (peers w)
... | nothing = λ ()
... | just p with P.status p
...   | P.peerWarm = λ { refl → same ((same-refl (cm w))) }
...   | P.peerHot with peerStep P.deactivate f w in moved
...     | nothing = λ ()
...     | just w′ = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
step-effect enter f w | begin | G.deactivate | just p | P.peerCold = λ { refl → same ((same-refl (cm w))) }
step-effect enter f w | begin | G.deactivate | just p | P.peerCooling = λ { refl → same ((same-refl (cm w))) }
step-effect enter f w | begin | G.close with lookup (connectionRef f) (peers w) | peerStep P.close f w | (λ (out : World) → peer-trans P.close f w {w′ = out} {c = cm w})
... | just p | just w′ | retained with P.status p
...   | P.peerCooling = λ { refl → same (retained w′ refl (same-refl (cm w))) }
...   | P.peerCold = λ { refl → same (retained w′ refl (same-refl (cm w))) }
...   | P.peerWarm = λ { refl → same (retained w′ refl (same-refl (cm w))) }
...   | P.peerHot = λ { refl → same (retained w′ refl (same-refl (cm w))) }
step-effect enter f w | begin | G.close | nothing | _ | _ = λ ()
step-effect enter f w | begin | G.close | just p | nothing | _ = λ ()
step-effect enter f w | begin | G.forget = λ ()
step-effect enter f w | awaitAcquire | _ = λ ()
step-effect enter f w | (startBundle t ns) | _ = λ ()
step-effect enter f w | (publishBundle t) | _ = λ ()
step-effect enter f w | markWarm | _ = λ ()
step-effect enter f w | forkMonitor | _ = λ ()
step-effect enter f w | finishActivation | _ = λ ()
step-effect enter f w | awaitHot | _ = λ ()
step-effect enter f w | awaitAll | _ = λ ()
step-effect enter f w | callRelease | _ = λ ()
step-effect enter f w | awaitRelease | _ = λ ()
step-effect enter f w | delayFailure | _ = λ ()
step-effect enter f w | (awaitCold result) | _ = λ ()
step-effect enter f w | (complete result) | _ = λ ()
step-effect enter f w | (acquirePolicy fault) | _ = λ ()
step-effect enter f w | (nodeDelivery fault) | _ = λ ()
step-effect enter f w | (nodeRethrow fault) | _ = λ ()
step-effect collectAcquire f w with pc f | lookup (caller f) (CM.acquired (cm w))
... | awaitAcquire | just (Cases.connected k flow h) with lookup h (IG.handles (IG.execution (Inbound.inboundGovernor (CM.core (cm w))))) | lookup (connectionRef f) (peers w)
...   | just hd | nothing = λ eq → same (start-trans ConnectionManagement.IGTypes.warm f (record w { peers = put (connectionRef f) (P.initialPeer k h hd) (peers w) }) eq (same-refl (cm w)))
...   | nothing | _ = λ ()
...   | just hd | just p = λ ()
step-effect collectAcquire f w | awaitAcquire | just (Cases.raised _) = λ { refl → same ((same-refl (cm w))) }
step-effect collectAcquire f w | awaitAcquire | just (Cases.disconnected k reason) = λ { refl → same (failed-trans f w (same-refl (cm w))) }
step-effect collectAcquire f w | awaitAcquire | nothing = λ ()
step-effect collectAcquire f w | begin | _ = λ ()
step-effect collectAcquire f w | (startBundle t ns) | _ = λ ()
step-effect collectAcquire f w | (publishBundle t) | _ = λ ()
step-effect collectAcquire f w | markWarm | _ = λ ()
step-effect collectAcquire f w | forkMonitor | _ = λ ()
step-effect collectAcquire f w | finishActivation | _ = λ ()
step-effect collectAcquire f w | awaitHot | _ = λ ()
step-effect collectAcquire f w | awaitAll | _ = λ ()
step-effect collectAcquire f w | callRelease | _ = λ ()
step-effect collectAcquire f w | awaitRelease | _ = λ ()
step-effect collectAcquire f w | delayFailure | _ = λ ()
step-effect collectAcquire f w | (awaitCold result) | _ = λ ()
step-effect collectAcquire f w | (complete result) | _ = λ ()
step-effect collectAcquire f w | (acquirePolicy fault) | _ = λ ()
step-effect collectAcquire f w | (nodeDelivery fault) | _ = λ ()
step-effect collectAcquire f w | (nodeRethrow fault) | _ = λ ()
step-effect runNext f w with pc f
... | startBundle t [] = λ { refl → same ((same-refl (cm w))) }
... | startBundle t (n ∷ ns) with peerStep (P.startProtocol t n) f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
step-effect runNext f w | begin = λ ()
step-effect runNext f w | awaitAcquire = λ ()
step-effect runNext f w | (publishBundle t) = λ ()
step-effect runNext f w | markWarm = λ ()
step-effect runNext f w | forkMonitor = λ ()
step-effect runNext f w | finishActivation = λ ()
step-effect runNext f w | awaitHot = λ ()
step-effect runNext f w | awaitAll = λ ()
step-effect runNext f w | callRelease = λ ()
step-effect runNext f w | awaitRelease = λ ()
step-effect runNext f w | delayFailure = λ ()
step-effect runNext f w | (awaitCold result) = λ ()
step-effect runNext f w | (complete result) = λ ()
step-effect runNext f w | (acquirePolicy fault) = λ ()
step-effect runNext f w | (nodeDelivery fault) = λ ()
step-effect runNext f w | (nodeRethrow fault) = λ ()
step-effect publishStarted f w with pc f
... | publishBundle t with peerStep (P.publishProtocols t) f w in moved
...   | nothing = λ ()
...   | just w′ with t
...     | ConnectionManagement.IGTypes.warm = λ eq → same (start-trans ConnectionManagement.IGTypes.established f w′ eq (peer-trans _ f w moved (same-refl (cm w))))
...     | ConnectionManagement.IGTypes.established = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
...     | ConnectionManagement.IGTypes.hot = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
step-effect publishStarted f w | begin = λ ()
step-effect publishStarted f w | awaitAcquire = λ ()
step-effect publishStarted f w | (startBundle t ns) = λ ()
step-effect publishStarted f w | markWarm = λ ()
step-effect publishStarted f w | forkMonitor = λ ()
step-effect publishStarted f w | finishActivation = λ ()
step-effect publishStarted f w | awaitHot = λ ()
step-effect publishStarted f w | awaitAll = λ ()
step-effect publishStarted f w | callRelease = λ ()
step-effect publishStarted f w | awaitRelease = λ ()
step-effect publishStarted f w | delayFailure = λ ()
step-effect publishStarted f w | (awaitCold result) = λ ()
step-effect publishStarted f w | (complete result) = λ ()
step-effect publishStarted f w | (acquirePolicy fault) = λ ()
step-effect publishStarted f w | (nodeDelivery fault) = λ ()
step-effect publishStarted f w | (nodeRethrow fault) = λ ()
step-effect markEstablished f w with pc f
... | markWarm with peerStep P.markWarm f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
step-effect markEstablished f w | begin = λ ()
step-effect markEstablished f w | awaitAcquire = λ ()
step-effect markEstablished f w | (startBundle t ns) = λ ()
step-effect markEstablished f w | (publishBundle t) = λ ()
step-effect markEstablished f w | forkMonitor = λ ()
step-effect markEstablished f w | finishActivation = λ ()
step-effect markEstablished f w | awaitHot = λ ()
step-effect markEstablished f w | awaitAll = λ ()
step-effect markEstablished f w | callRelease = λ ()
step-effect markEstablished f w | awaitRelease = λ ()
step-effect markEstablished f w | delayFailure = λ ()
step-effect markEstablished f w | (awaitCold result) = λ ()
step-effect markEstablished f w | (complete result) = λ ()
step-effect markEstablished f w | (acquirePolicy fault) = λ ()
step-effect markEstablished f w | (nodeDelivery fault) = λ ()
step-effect markEstablished f w | (nodeRethrow fault) = λ ()
step-effect launchMonitor f w with pc f
... | forkMonitor with peerStep P.forkMonitor f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
step-effect launchMonitor f w | begin = λ ()
step-effect launchMonitor f w | awaitAcquire = λ ()
step-effect launchMonitor f w | (startBundle t ns) = λ ()
step-effect launchMonitor f w | (publishBundle t) = λ ()
step-effect launchMonitor f w | markWarm = λ ()
step-effect launchMonitor f w | finishActivation = λ ()
step-effect launchMonitor f w | awaitHot = λ ()
step-effect launchMonitor f w | awaitAll = λ ()
step-effect launchMonitor f w | callRelease = λ ()
step-effect launchMonitor f w | awaitRelease = λ ()
step-effect launchMonitor f w | delayFailure = λ ()
step-effect launchMonitor f w | (awaitCold result) = λ ()
step-effect launchMonitor f w | (complete result) = λ ()
step-effect launchMonitor f w | (acquirePolicy fault) = λ ()
step-effect launchMonitor f w | (nodeDelivery fault) = λ ()
step-effect launchMonitor f w | (nodeRethrow fault) = λ ()
step-effect (finishHotAt time) f w with pc f
... | finishActivation with peerStep (P.markPromoted time) f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
step-effect (finishHotAt time) f w | begin = λ ()
step-effect (finishHotAt time) f w | awaitAcquire = λ ()
step-effect (finishHotAt time) f w | (startBundle t ns) = λ ()
step-effect (finishHotAt time) f w | (publishBundle t) = λ ()
step-effect (finishHotAt time) f w | markWarm = λ ()
step-effect (finishHotAt time) f w | forkMonitor = λ ()
step-effect (finishHotAt time) f w | awaitHot = λ ()
step-effect (finishHotAt time) f w | awaitAll = λ ()
step-effect (finishHotAt time) f w | callRelease = λ ()
step-effect (finishHotAt time) f w | awaitRelease = λ ()
step-effect (finishHotAt time) f w | delayFailure = λ ()
step-effect (finishHotAt time) f w | (awaitCold result) = λ ()
step-effect (finishHotAt time) f w | (complete result) = λ ()
step-effect (finishHotAt time) f w | (acquirePolicy fault) = λ ()
step-effect (finishHotAt time) f w | (nodeDelivery fault) = λ ()
step-effect (finishHotAt time) f w | (nodeRethrow fault) = λ ()
step-effect observeHot f w with pc f | lookup (connectionRef f) (peers w)
... | awaitHot | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | peerStep P.finishDeactivate f w | (λ (out : World) → peer-trans P.finishDeactivate f w {w′ = out} {c = cm w})
...   | just clean | just w′ | retained = λ { refl → same (retained w′ refl (same-refl (cm w))) }
...   | just (errored _) | just w′ | retained = λ { refl → same (retained w′ refl (same-refl (cm w))) }
...   | nothing | _ | _ = λ ()
...   | just clean | nothing | _ = λ ()
...   | just (errored err) | nothing | _ = λ ()
step-effect observeHot f w | awaitHot | nothing = λ ()
step-effect observeHot f w | begin | _ = λ ()
step-effect observeHot f w | awaitAcquire | _ = λ ()
step-effect observeHot f w | (startBundle t ns) | _ = λ ()
step-effect observeHot f w | (publishBundle t) | _ = λ ()
step-effect observeHot f w | markWarm | _ = λ ()
step-effect observeHot f w | forkMonitor | _ = λ ()
step-effect observeHot f w | finishActivation | _ = λ ()
step-effect observeHot f w | awaitAll | _ = λ ()
step-effect observeHot f w | callRelease | _ = λ ()
step-effect observeHot f w | awaitRelease | _ = λ ()
step-effect observeHot f w | delayFailure | _ = λ ()
step-effect observeHot f w | (awaitCold result) | _ = λ ()
step-effect observeHot f w | (complete result) | _ = λ ()
step-effect observeHot f w | (acquirePolicy fault) | _ = λ ()
step-effect observeHot f w | (nodeDelivery fault) | _ = λ ()
step-effect observeHot f w | (nodeRethrow fault) | _ = λ ()
step-effect observeAll f w with pc f | lookup (connectionRef f) (peers w)
... | awaitAll | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | P.all ConnectionManagement.IGTypes.warm (P.runs p) | P.all ConnectionManagement.IGTypes.established (P.runs p)
...   | just clean | just clean | just clean = λ { refl → same ((same-refl (cm w))) }
...   | just clean | just clean | just (errored e₃) = λ { refl → same ((same-refl (cm w))) }
...   | just clean | just (errored e₂) | just clean = λ { refl → same ((same-refl (cm w))) }
...   | just clean | just (errored e₂) | just (errored e₃) = λ { refl → same ((same-refl (cm w))) }
...   | just (errored e₁) | just clean | just clean = λ { refl → same ((same-refl (cm w))) }
...   | just (errored e₁) | just clean | just (errored e₃) = λ { refl → same ((same-refl (cm w))) }
...   | just (errored e₁) | just (errored e₂) | just clean = λ { refl → same ((same-refl (cm w))) }
...   | just (errored e₁) | just (errored e₂) | just (errored e₃) = λ { refl → same ((same-refl (cm w))) }
...   | nothing | _ | _ = λ ()
...   | just clean | nothing | _ = λ ()
...   | just (errored e) | nothing | _ = λ ()
...   | just clean | just clean | nothing = λ ()
...   | just clean | just (errored e₂) | nothing = λ ()
...   | just (errored e₁) | just clean | nothing = λ ()
...   | just (errored e₁) | just (errored e₂) | nothing = λ ()
step-effect observeAll f w | awaitAll | nothing = λ ()
step-effect observeAll f w | begin | _ = λ ()
step-effect observeAll f w | awaitAcquire | _ = λ ()
step-effect observeAll f w | (startBundle t ns) | _ = λ ()
step-effect observeAll f w | (publishBundle t) | _ = λ ()
step-effect observeAll f w | markWarm | _ = λ ()
step-effect observeAll f w | forkMonitor | _ = λ ()
step-effect observeAll f w | finishActivation | _ = λ ()
step-effect observeAll f w | awaitHot | _ = λ ()
step-effect observeAll f w | callRelease | _ = λ ()
step-effect observeAll f w | awaitRelease | _ = λ ()
step-effect observeAll f w | delayFailure | _ = λ ()
step-effect observeAll f w | (awaitCold result) | _ = λ ()
step-effect observeAll f w | (complete result) | _ = λ ()
step-effect observeAll f w | (acquirePolicy fault) | _ = λ ()
step-effect observeAll f w | (nodeDelivery fault) | _ = λ ()
step-effect observeAll f w | (nodeRethrow fault) | _ = λ ()
step-effect requestRelease f w with pc f | lookup (connectionRef f) (peers w)
... | callRelease | just p with CM.advance (CM.beginRelease (caller f) (P.key p)) (cm w) in advanced
...   | nothing = λ ()
...   | just c = λ { refl → released (P.key p) advanced refl }
step-effect requestRelease f w | callRelease | nothing = λ ()
step-effect requestRelease f w | begin | _ = λ ()
step-effect requestRelease f w | awaitAcquire | _ = λ ()
step-effect requestRelease f w | (startBundle t ns) | _ = λ ()
step-effect requestRelease f w | (publishBundle t) | _ = λ ()
step-effect requestRelease f w | markWarm | _ = λ ()
step-effect requestRelease f w | forkMonitor | _ = λ ()
step-effect requestRelease f w | finishActivation | _ = λ ()
step-effect requestRelease f w | awaitHot | _ = λ ()
step-effect requestRelease f w | awaitAll | _ = λ ()
step-effect requestRelease f w | awaitRelease | _ = λ ()
step-effect requestRelease f w | delayFailure | _ = λ ()
step-effect requestRelease f w | (awaitCold result) | _ = λ ()
step-effect requestRelease f w | (complete result) | _ = λ ()
step-effect requestRelease f w | (acquirePolicy fault) | _ = λ ()
step-effect requestRelease f w | (nodeDelivery fault) | _ = λ ()
step-effect requestRelease f w | (nodeRethrow fault) | _ = λ ()
step-effect collectRelease f w with pc f | lookup (caller f) (CM.released (cm w))
... | awaitRelease | just R.assertionFailure = λ { refl → same ((same-refl (cm w))) }
... | awaitRelease | just (R.success state) = λ { refl → same ((same-refl (cm w))) }
... | awaitRelease | just (R.unsupported state) = λ { refl → same ((same-refl (cm w))) }
... | awaitRelease | nothing = λ ()
step-effect collectRelease f w | begin | _ = λ ()
step-effect collectRelease f w | awaitAcquire | _ = λ ()
step-effect collectRelease f w | (startBundle t ns) | _ = λ ()
step-effect collectRelease f w | (publishBundle t) | _ = λ ()
step-effect collectRelease f w | markWarm | _ = λ ()
step-effect collectRelease f w | forkMonitor | _ = λ ()
step-effect collectRelease f w | finishActivation | _ = λ ()
step-effect collectRelease f w | awaitHot | _ = λ ()
step-effect collectRelease f w | awaitAll | _ = λ ()
step-effect collectRelease f w | callRelease | _ = λ ()
step-effect collectRelease f w | delayFailure | _ = λ ()
step-effect collectRelease f w | (awaitCold result) | _ = λ ()
step-effect collectRelease f w | (complete result) | _ = λ ()
step-effect collectRelease f w | (acquirePolicy fault) | _ = λ ()
step-effect collectRelease f w | (nodeDelivery fault) | _ = λ ()
step-effect collectRelease f w | (nodeRethrow fault) | _ = λ ()
step-effect observeCold f w with pc f | lookup (connectionRef f) (peers w)
... | awaitCold result | just p with P.status p
...   | P.peerCold = λ { refl → same ((same-refl (cm w))) }
...   | P.peerHot = λ ()
...   | P.peerWarm = λ ()
...   | P.peerCooling = λ ()
step-effect observeCold f w | awaitCold result | nothing = λ ()
step-effect observeCold f w | begin | _ = λ ()
step-effect observeCold f w | awaitAcquire | _ = λ ()
step-effect observeCold f w | (startBundle t ns) | _ = λ ()
step-effect observeCold f w | (publishBundle t) | _ = λ ()
step-effect observeCold f w | markWarm | _ = λ ()
step-effect observeCold f w | forkMonitor | _ = λ ()
step-effect observeCold f w | finishActivation | _ = λ ()
step-effect observeCold f w | awaitHot | _ = λ ()
step-effect observeCold f w | awaitAll | _ = λ ()
step-effect observeCold f w | callRelease | _ = λ ()
step-effect observeCold f w | awaitRelease | _ = λ ()
step-effect observeCold f w | delayFailure | _ = λ ()
step-effect observeCold f w | (complete result) | _ = λ ()
step-effect observeCold f w | (acquirePolicy fault) | _ = λ ()
step-effect observeCold f w | (nodeDelivery fault) | _ = λ ()
step-effect observeCold f w | (nodeRethrow fault) | _ = λ ()
step-effect operationTimeout f w with pc f
... | awaitHot with peerStep P.timeoutDeactivate f w in moved
...   | nothing = λ ()
...   | just w′ = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
step-effect operationTimeout f w | awaitAll with peerStep P.timeoutClose f w in moved
... | nothing = λ ()
... | just w′ = λ { refl → same (peer-trans _ f w moved (same-refl (cm w))) }
step-effect operationTimeout f w | begin = λ ()
step-effect operationTimeout f w | awaitAcquire = λ ()
step-effect operationTimeout f w | (startBundle t ns) = λ ()
step-effect operationTimeout f w | (publishBundle t) = λ ()
step-effect operationTimeout f w | markWarm = λ ()
step-effect operationTimeout f w | forkMonitor = λ ()
step-effect operationTimeout f w | finishActivation = λ ()
step-effect operationTimeout f w | callRelease = λ ()
step-effect operationTimeout f w | awaitRelease = λ ()
step-effect operationTimeout f w | delayFailure = λ ()
step-effect operationTimeout f w | (awaitCold result) = λ ()
step-effect operationTimeout f w | (complete result) = λ ()
step-effect operationTimeout f w | (acquirePolicy fault) = λ ()
step-effect operationTimeout f w | (nodeDelivery fault) = λ ()
step-effect operationTimeout f w | (nodeRethrow fault) = λ ()
step-effect demotionTimeout f w with pc f
... | awaitCold _ = λ { refl → same ((same-refl (cm w))) }
step-effect demotionTimeout f w | begin = λ ()
step-effect demotionTimeout f w | awaitAcquire = λ ()
step-effect demotionTimeout f w | (startBundle t ns) = λ ()
step-effect demotionTimeout f w | (publishBundle t) = λ ()
step-effect demotionTimeout f w | markWarm = λ ()
step-effect demotionTimeout f w | forkMonitor = λ ()
step-effect demotionTimeout f w | finishActivation = λ ()
step-effect demotionTimeout f w | awaitHot = λ ()
step-effect demotionTimeout f w | awaitAll = λ ()
step-effect demotionTimeout f w | callRelease = λ ()
step-effect demotionTimeout f w | awaitRelease = λ ()
step-effect demotionTimeout f w | delayFailure = λ ()
step-effect demotionTimeout f w | (complete result) = λ ()
step-effect demotionTimeout f w | (acquirePolicy fault) = λ ()
step-effect demotionTimeout f w | (nodeDelivery fault) = λ ()
step-effect demotionTimeout f w | (nodeRethrow fault) = λ ()
step-effect failureDelayElapsed f w with pc f
... | delayFailure = λ { refl → same ((same-refl (cm w))) }
step-effect failureDelayElapsed f w | begin = λ ()
step-effect failureDelayElapsed f w | awaitAcquire = λ ()
step-effect failureDelayElapsed f w | (startBundle t ns) = λ ()
step-effect failureDelayElapsed f w | (publishBundle t) = λ ()
step-effect failureDelayElapsed f w | markWarm = λ ()
step-effect failureDelayElapsed f w | forkMonitor = λ ()
step-effect failureDelayElapsed f w | finishActivation = λ ()
step-effect failureDelayElapsed f w | awaitHot = λ ()
step-effect failureDelayElapsed f w | awaitAll = λ ()
step-effect failureDelayElapsed f w | callRelease = λ ()
step-effect failureDelayElapsed f w | awaitRelease = λ ()
step-effect failureDelayElapsed f w | (awaitCold result) = λ ()
step-effect failureDelayElapsed f w | (complete result) = λ ()
step-effect failureDelayElapsed f w | (acquirePolicy fault) = λ ()
step-effect failureDelayElapsed f w | (nodeDelivery fault) = λ ()
step-effect failureDelayElapsed f w | (nodeRethrow fault) = λ ()
step-effect (startFailed err) f w with pc f | G.kind (work f)
... | startBundle t (n ∷ _) | G.establish with peerStep (P.startProtocol t n) f w in moved
...   | nothing = λ { refl → same (failed-trans f w (same-refl (cm w))) }
...   | just _ = λ ()
step-effect (startFailed err) f w | startBundle t (n ∷ _) | G.activate with peerStep (P.startProtocol t n) f w in moved
... | nothing = λ { refl → same ((same-refl (cm w))) }
... | just _ = λ ()
step-effect (startFailed err) f w | startBundle t [] | _ = λ ()
step-effect (startFailed err) f w | startBundle t (n ∷ ns) | G.forget = λ ()
step-effect (startFailed err) f w | startBundle t (n ∷ ns) | G.close = λ ()
step-effect (startFailed err) f w | startBundle t (n ∷ ns) | G.deactivate = λ ()
step-effect (startFailed err) f w | begin | _ = λ ()
step-effect (startFailed err) f w | awaitAcquire | _ = λ ()
step-effect (startFailed err) f w | (publishBundle t) | _ = λ ()
step-effect (startFailed err) f w | markWarm | _ = λ ()
step-effect (startFailed err) f w | forkMonitor | _ = λ ()
step-effect (startFailed err) f w | finishActivation | _ = λ ()
step-effect (startFailed err) f w | awaitHot | _ = λ ()
step-effect (startFailed err) f w | awaitAll | _ = λ ()
step-effect (startFailed err) f w | callRelease | _ = λ ()
step-effect (startFailed err) f w | awaitRelease | _ = λ ()
step-effect (startFailed err) f w | delayFailure | _ = λ ()
step-effect (startFailed err) f w | (awaitCold result) | _ = λ ()
step-effect (startFailed err) f w | (complete result) | _ = λ ()
step-effect (startFailed err) f w | (acquirePolicy fault) | _ = λ ()
step-effect (startFailed err) f w | (nodeDelivery fault) | _ = λ ()
step-effect (startFailed err) f w | (nodeRethrow fault) | _ = λ ()
step-effect choosePeerPolicy f w with pc f
... | (acquirePolicy fault) = λ { refl → same (failed-trans f w (same-refl (cm w))) }
step-effect choosePeerPolicy f w | begin = λ ()
step-effect choosePeerPolicy f w | awaitAcquire = λ ()
step-effect choosePeerPolicy f w | (startBundle t ns) = λ ()
step-effect choosePeerPolicy f w | (publishBundle t) = λ ()
step-effect choosePeerPolicy f w | markWarm = λ ()
step-effect choosePeerPolicy f w | forkMonitor = λ ()
step-effect choosePeerPolicy f w | finishActivation = λ ()
step-effect choosePeerPolicy f w | awaitHot = λ ()
step-effect choosePeerPolicy f w | awaitAll = λ ()
step-effect choosePeerPolicy f w | callRelease = λ ()
step-effect choosePeerPolicy f w | awaitRelease = λ ()
step-effect choosePeerPolicy f w | delayFailure = λ ()
step-effect choosePeerPolicy f w | (awaitCold result) = λ ()
step-effect choosePeerPolicy f w | (complete result) = λ ()
step-effect choosePeerPolicy f w | (nodeDelivery fault) = λ ()
step-effect choosePeerPolicy f w | (nodeRethrow fault) = λ ()
step-effect chooseNodePolicy f w with pc f
... | (acquirePolicy fault) = λ { refl → same ((same-refl (cm w))) }
step-effect chooseNodePolicy f w | begin = λ ()
step-effect chooseNodePolicy f w | awaitAcquire = λ ()
step-effect chooseNodePolicy f w | (startBundle t ns) = λ ()
step-effect chooseNodePolicy f w | (publishBundle t) = λ ()
step-effect chooseNodePolicy f w | markWarm = λ ()
step-effect chooseNodePolicy f w | forkMonitor = λ ()
step-effect chooseNodePolicy f w | finishActivation = λ ()
step-effect chooseNodePolicy f w | awaitHot = λ ()
step-effect chooseNodePolicy f w | awaitAll = λ ()
step-effect chooseNodePolicy f w | callRelease = λ ()
step-effect chooseNodePolicy f w | awaitRelease = λ ()
step-effect chooseNodePolicy f w | delayFailure = λ ()
step-effect chooseNodePolicy f w | (awaitCold result) = λ ()
step-effect chooseNodePolicy f w | (complete result) = λ ()
step-effect chooseNodePolicy f w | (nodeDelivery fault) = λ ()
step-effect chooseNodePolicy f w | (nodeRethrow fault) = λ ()
step-effect deliverNodeException f w with pc f
... | (nodeDelivery fault) = λ { refl → same ((same-refl (cm w))) }
step-effect deliverNodeException f w | begin = λ ()
step-effect deliverNodeException f w | awaitAcquire = λ ()
step-effect deliverNodeException f w | (startBundle t ns) = λ ()
step-effect deliverNodeException f w | (publishBundle t) = λ ()
step-effect deliverNodeException f w | markWarm = λ ()
step-effect deliverNodeException f w | forkMonitor = λ ()
step-effect deliverNodeException f w | finishActivation = λ ()
step-effect deliverNodeException f w | awaitHot = λ ()
step-effect deliverNodeException f w | awaitAll = λ ()
step-effect deliverNodeException f w | callRelease = λ ()
step-effect deliverNodeException f w | awaitRelease = λ ()
step-effect deliverNodeException f w | delayFailure = λ ()
step-effect deliverNodeException f w | (awaitCold result) = λ ()
step-effect deliverNodeException f w | (complete result) = λ ()
step-effect deliverNodeException f w | (acquirePolicy fault) = λ ()
step-effect deliverNodeException f w | (nodeRethrow fault) = λ ()
step-effect rethrowNodeException f w with pc f
... | (nodeRethrow fault) = λ { refl → same (failed-trans f w (same-refl (cm w))) }
step-effect rethrowNodeException f w | begin = λ ()
step-effect rethrowNodeException f w | awaitAcquire = λ ()
step-effect rethrowNodeException f w | (startBundle t ns) = λ ()
step-effect rethrowNodeException f w | (publishBundle t) = λ ()
step-effect rethrowNodeException f w | markWarm = λ ()
step-effect rethrowNodeException f w | forkMonitor = λ ()
step-effect rethrowNodeException f w | finishActivation = λ ()
step-effect rethrowNodeException f w | awaitHot = λ ()
step-effect rethrowNodeException f w | awaitAll = λ ()
step-effect rethrowNodeException f w | callRelease = λ ()
step-effect rethrowNodeException f w | awaitRelease = λ ()
step-effect rethrowNodeException f w | delayFailure = λ ()
step-effect rethrowNodeException f w | (awaitCold result) = λ ()
step-effect rethrowNodeException f w | (complete result) = λ ()
step-effect rethrowNodeException f w | (acquirePolicy fault) = λ ()
step-effect rethrowNodeException f w | (nodeDelivery fault) = λ ()


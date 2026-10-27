{-# OPTIONS --guardedness #-}

-- Lift a runtime/world invariant through every source peer-job action.
module ConnectionManagement.Properties.PeerJobInvariant where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (Temperature; RunResult; clean; errored; number)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.IGRegistration as IG

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Rules.PeerJobs
import ConnectionManagement.State as S

-- Peer/IG-only edits are invisible to this runtime/world predicate.
module Lift
  (Predicate : A.Runtime → S.State → Set)
  (preserve : ∀ a c {c′} → CM.advance a c ≡ just c′ →
    Predicate (CM.acquiring c) (Inbound.world (CM.core c)) →
    Predicate (CM.acquiring c′) (Inbound.world (CM.core c′))) where

  -- The selected predicate observes the acquisition runtime and shared world.
  Valid : World → Set
  Valid w = Predicate (CM.acquiring (cm w)) (Inbound.world (CM.core (cm w)))

  -- Protocol actions change peers and IG, preserving the observed components.
  peer-preserves : ∀ a f w {w′} → peerStep a f w ≡ just w′ → Valid w → Valid w′
  peer-preserves a f w with lookup (connectionRef f) (peers w)
  ... | nothing = λ ()
  ... | just p with P.step a p (Inbound.inboundGovernor (CM.core (cm w))) (Inbound.world (CM.core (cm w)))
  ...   | nothing = λ ()
  ...   | just (p′ , ig′) = λ { refl v → v }

  -- Starting a bundle changes only the job frame.
  start-preserves : ∀ t f w {out} → start t f w ≡ just out → Valid w → Valid (proj₂ out)
  start-preserves t f w with lookup (connectionRef f) (peers w)
  ... | nothing = λ ()
  ... | just p = λ { refl v → v }

  -- Failed establishment changes only the peer status.
  failed-preserves : ∀ f w → Valid w → Valid (proj₂ (failedEstablishment f w))
  failed-preserves f w with lookup (connectionRef f) (peers w)
  ... | nothing = λ v → v
  ... | just p = λ v → v

  -- Every source job action preserves the predicate, including CM calls.
  step-preserves : ∀ a f w → Valid w → ∀ {out} → step a f w ≡ just out → Valid (proj₂ out)
  step-preserves enter f w v with pc f | G.kind (work f)
  ... | begin | G.establish with CM.advance (CM.beginAcquire (caller f) (A.acquireRequest (G.peer (work f)) (child f) (socketRef f) outbound nothing)) (cm w) in advanced
  ...   | nothing = λ ()
  ...   | just c = λ { refl → preserve (CM.beginAcquire (caller f)
      (A.acquireRequest (G.peer (work f)) (child f) (socketRef f) outbound nothing)) (cm w) advanced v }
  step-preserves enter f w v | begin | G.activate with peerStep P.activate f w in moved
  ... | nothing = λ { refl → v }
  ... | just w′ = λ eq → start-preserves ConnectionManagement.IGTypes.hot f w′ eq (peer-preserves _ f w moved v)
  step-preserves enter f w v | begin | G.deactivate with lookup (connectionRef f) (peers w)
  ... | nothing = λ ()
  ... | just p with P.status p
  ...   | P.peerWarm = λ { refl → v }
  ...   | P.peerHot with peerStep P.deactivate f w in moved
  ...     | nothing = λ ()
  ...     | just w′ = λ { refl → peer-preserves _ f w moved v }
  step-preserves enter f w v | begin | G.deactivate | just p | P.peerCold = λ { refl → v }
  step-preserves enter f w v | begin | G.deactivate | just p | P.peerCooling = λ { refl → v }
  step-preserves enter f w v | begin | G.close with lookup (connectionRef f) (peers w) | peerStep P.close f w | peer-preserves P.close f w
  ... | just p | just w′ | retained with P.status p
  ...   | P.peerCooling = λ { refl → retained refl v }
  ...   | P.peerCold = λ { refl → retained refl v }
  ...   | P.peerWarm = λ { refl → retained refl v }
  ...   | P.peerHot = λ { refl → retained refl v }
  step-preserves enter f w v | begin | G.close | nothing | _ | _ = λ ()
  step-preserves enter f w v | begin | G.close | just p | nothing | _ = λ ()
  step-preserves enter f w v | begin | G.forget = λ ()
  step-preserves enter f w v | awaitAcquire | _ = λ ()
  step-preserves enter f w v | (startBundle t ns) | _ = λ ()
  step-preserves enter f w v | (publishBundle t) | _ = λ ()
  step-preserves enter f w v | markWarm | _ = λ ()
  step-preserves enter f w v | forkMonitor | _ = λ ()
  step-preserves enter f w v | finishActivation | _ = λ ()
  step-preserves enter f w v | awaitHot | _ = λ ()
  step-preserves enter f w v | awaitAll | _ = λ ()
  step-preserves enter f w v | callRelease | _ = λ ()
  step-preserves enter f w v | awaitRelease | _ = λ ()
  step-preserves enter f w v | delayFailure | _ = λ ()
  step-preserves enter f w v | (awaitCold result) | _ = λ ()
  step-preserves enter f w v | (complete result) | _ = λ ()
  step-preserves enter f w v | (acquirePolicy fault) | _ = λ ()
  step-preserves enter f w v | (nodeDelivery fault) | _ = λ ()
  step-preserves enter f w v | (nodeRethrow fault) | _ = λ ()
  step-preserves collectAcquire f w v with pc f | lookup (caller f) (CM.acquired (cm w))
  ... | awaitAcquire | just (Cases.connected k flow h) with lookup h (IG.handles (IG.execution (Inbound.inboundGovernor (CM.core (cm w))))) | lookup (connectionRef f) (peers w)
  ...   | just hd | nothing = λ eq → start-preserves ConnectionManagement.IGTypes.warm f (record w { peers = put (connectionRef f) (P.initialPeer k h hd) (peers w) }) eq (v)
  ...   | nothing | _ = λ ()
  ...   | just hd | just p = λ ()
  step-preserves collectAcquire f w v | awaitAcquire | just (Cases.raised _) = λ { refl → v }
  step-preserves collectAcquire f w v | awaitAcquire | just (Cases.disconnected k reason) = λ { refl → failed-preserves f w v }
  step-preserves collectAcquire f w v | awaitAcquire | nothing = λ ()
  step-preserves collectAcquire f w v | begin | _ = λ ()
  step-preserves collectAcquire f w v | (startBundle t ns) | _ = λ ()
  step-preserves collectAcquire f w v | (publishBundle t) | _ = λ ()
  step-preserves collectAcquire f w v | markWarm | _ = λ ()
  step-preserves collectAcquire f w v | forkMonitor | _ = λ ()
  step-preserves collectAcquire f w v | finishActivation | _ = λ ()
  step-preserves collectAcquire f w v | awaitHot | _ = λ ()
  step-preserves collectAcquire f w v | awaitAll | _ = λ ()
  step-preserves collectAcquire f w v | callRelease | _ = λ ()
  step-preserves collectAcquire f w v | awaitRelease | _ = λ ()
  step-preserves collectAcquire f w v | delayFailure | _ = λ ()
  step-preserves collectAcquire f w v | (awaitCold result) | _ = λ ()
  step-preserves collectAcquire f w v | (complete result) | _ = λ ()
  step-preserves collectAcquire f w v | (acquirePolicy fault) | _ = λ ()
  step-preserves collectAcquire f w v | (nodeDelivery fault) | _ = λ ()
  step-preserves collectAcquire f w v | (nodeRethrow fault) | _ = λ ()
  step-preserves runNext f w v with pc f
  ... | startBundle t [] = λ { refl → v }
  ... | startBundle t (n ∷ ns) with peerStep (P.startProtocol t n) f w in moved
  ...   | nothing = λ ()
  ...   | just w′ = λ { refl → peer-preserves _ f w moved v }
  step-preserves runNext f w v | begin = λ ()
  step-preserves runNext f w v | awaitAcquire = λ ()
  step-preserves runNext f w v | (publishBundle t) = λ ()
  step-preserves runNext f w v | markWarm = λ ()
  step-preserves runNext f w v | forkMonitor = λ ()
  step-preserves runNext f w v | finishActivation = λ ()
  step-preserves runNext f w v | awaitHot = λ ()
  step-preserves runNext f w v | awaitAll = λ ()
  step-preserves runNext f w v | callRelease = λ ()
  step-preserves runNext f w v | awaitRelease = λ ()
  step-preserves runNext f w v | delayFailure = λ ()
  step-preserves runNext f w v | (awaitCold result) = λ ()
  step-preserves runNext f w v | (complete result) = λ ()
  step-preserves runNext f w v | (acquirePolicy fault) = λ ()
  step-preserves runNext f w v | (nodeDelivery fault) = λ ()
  step-preserves runNext f w v | (nodeRethrow fault) = λ ()
  step-preserves publishStarted f w v with pc f
  ... | publishBundle t with peerStep (P.publishProtocols t) f w in moved
  ...   | nothing = λ ()
  ...   | just w′ with t
  ...     | ConnectionManagement.IGTypes.warm = λ eq → start-preserves ConnectionManagement.IGTypes.established f w′ eq (peer-preserves _ f w moved v)
  ...     | ConnectionManagement.IGTypes.established = λ { refl → peer-preserves _ f w moved v }
  ...     | ConnectionManagement.IGTypes.hot = λ { refl → peer-preserves _ f w moved v }
  step-preserves publishStarted f w v | begin = λ ()
  step-preserves publishStarted f w v | awaitAcquire = λ ()
  step-preserves publishStarted f w v | (startBundle t ns) = λ ()
  step-preserves publishStarted f w v | markWarm = λ ()
  step-preserves publishStarted f w v | forkMonitor = λ ()
  step-preserves publishStarted f w v | finishActivation = λ ()
  step-preserves publishStarted f w v | awaitHot = λ ()
  step-preserves publishStarted f w v | awaitAll = λ ()
  step-preserves publishStarted f w v | callRelease = λ ()
  step-preserves publishStarted f w v | awaitRelease = λ ()
  step-preserves publishStarted f w v | delayFailure = λ ()
  step-preserves publishStarted f w v | (awaitCold result) = λ ()
  step-preserves publishStarted f w v | (complete result) = λ ()
  step-preserves publishStarted f w v | (acquirePolicy fault) = λ ()
  step-preserves publishStarted f w v | (nodeDelivery fault) = λ ()
  step-preserves publishStarted f w v | (nodeRethrow fault) = λ ()
  step-preserves markEstablished f w v with pc f
  ... | markWarm with peerStep P.markWarm f w in moved
  ...   | nothing = λ ()
  ...   | just w′ = λ { refl → peer-preserves _ f w moved v }
  step-preserves markEstablished f w v | begin = λ ()
  step-preserves markEstablished f w v | awaitAcquire = λ ()
  step-preserves markEstablished f w v | (startBundle t ns) = λ ()
  step-preserves markEstablished f w v | (publishBundle t) = λ ()
  step-preserves markEstablished f w v | forkMonitor = λ ()
  step-preserves markEstablished f w v | finishActivation = λ ()
  step-preserves markEstablished f w v | awaitHot = λ ()
  step-preserves markEstablished f w v | awaitAll = λ ()
  step-preserves markEstablished f w v | callRelease = λ ()
  step-preserves markEstablished f w v | awaitRelease = λ ()
  step-preserves markEstablished f w v | delayFailure = λ ()
  step-preserves markEstablished f w v | (awaitCold result) = λ ()
  step-preserves markEstablished f w v | (complete result) = λ ()
  step-preserves markEstablished f w v | (acquirePolicy fault) = λ ()
  step-preserves markEstablished f w v | (nodeDelivery fault) = λ ()
  step-preserves markEstablished f w v | (nodeRethrow fault) = λ ()
  step-preserves launchMonitor f w v with pc f
  ... | forkMonitor with peerStep P.forkMonitor f w in moved
  ...   | nothing = λ ()
  ...   | just w′ = λ { refl → peer-preserves _ f w moved v }
  step-preserves launchMonitor f w v | begin = λ ()
  step-preserves launchMonitor f w v | awaitAcquire = λ ()
  step-preserves launchMonitor f w v | (startBundle t ns) = λ ()
  step-preserves launchMonitor f w v | (publishBundle t) = λ ()
  step-preserves launchMonitor f w v | markWarm = λ ()
  step-preserves launchMonitor f w v | finishActivation = λ ()
  step-preserves launchMonitor f w v | awaitHot = λ ()
  step-preserves launchMonitor f w v | awaitAll = λ ()
  step-preserves launchMonitor f w v | callRelease = λ ()
  step-preserves launchMonitor f w v | awaitRelease = λ ()
  step-preserves launchMonitor f w v | delayFailure = λ ()
  step-preserves launchMonitor f w v | (awaitCold result) = λ ()
  step-preserves launchMonitor f w v | (complete result) = λ ()
  step-preserves launchMonitor f w v | (acquirePolicy fault) = λ ()
  step-preserves launchMonitor f w v | (nodeDelivery fault) = λ ()
  step-preserves launchMonitor f w v | (nodeRethrow fault) = λ ()
  step-preserves (finishHotAt time) f w v with pc f
  ... | finishActivation with peerStep (P.markPromoted time) f w in moved
  ...   | nothing = λ ()
  ...   | just w′ = λ { refl → peer-preserves _ f w moved v }
  step-preserves (finishHotAt time) f w v | begin = λ ()
  step-preserves (finishHotAt time) f w v | awaitAcquire = λ ()
  step-preserves (finishHotAt time) f w v | (startBundle t ns) = λ ()
  step-preserves (finishHotAt time) f w v | (publishBundle t) = λ ()
  step-preserves (finishHotAt time) f w v | markWarm = λ ()
  step-preserves (finishHotAt time) f w v | forkMonitor = λ ()
  step-preserves (finishHotAt time) f w v | awaitHot = λ ()
  step-preserves (finishHotAt time) f w v | awaitAll = λ ()
  step-preserves (finishHotAt time) f w v | callRelease = λ ()
  step-preserves (finishHotAt time) f w v | awaitRelease = λ ()
  step-preserves (finishHotAt time) f w v | delayFailure = λ ()
  step-preserves (finishHotAt time) f w v | (awaitCold result) = λ ()
  step-preserves (finishHotAt time) f w v | (complete result) = λ ()
  step-preserves (finishHotAt time) f w v | (acquirePolicy fault) = λ ()
  step-preserves (finishHotAt time) f w v | (nodeDelivery fault) = λ ()
  step-preserves (finishHotAt time) f w v | (nodeRethrow fault) = λ ()
  step-preserves observeHot f w v with pc f | lookup (connectionRef f) (peers w)
  ... | awaitHot | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | peerStep P.finishDeactivate f w | peer-preserves P.finishDeactivate f w
  ...   | just clean | just w′ | retained = λ { refl → retained refl v }
  ...   | just (errored _) | just w′ | retained = λ { refl → retained refl v }
  ...   | nothing | _ | _ = λ ()
  ...   | just clean | nothing | _ = λ ()
  ...   | just (errored err) | nothing | _ = λ ()
  step-preserves observeHot f w v | awaitHot | nothing = λ ()
  step-preserves observeHot f w v | begin | _ = λ ()
  step-preserves observeHot f w v | awaitAcquire | _ = λ ()
  step-preserves observeHot f w v | (startBundle t ns) | _ = λ ()
  step-preserves observeHot f w v | (publishBundle t) | _ = λ ()
  step-preserves observeHot f w v | markWarm | _ = λ ()
  step-preserves observeHot f w v | forkMonitor | _ = λ ()
  step-preserves observeHot f w v | finishActivation | _ = λ ()
  step-preserves observeHot f w v | awaitAll | _ = λ ()
  step-preserves observeHot f w v | callRelease | _ = λ ()
  step-preserves observeHot f w v | awaitRelease | _ = λ ()
  step-preserves observeHot f w v | delayFailure | _ = λ ()
  step-preserves observeHot f w v | (awaitCold result) | _ = λ ()
  step-preserves observeHot f w v | (complete result) | _ = λ ()
  step-preserves observeHot f w v | (acquirePolicy fault) | _ = λ ()
  step-preserves observeHot f w v | (nodeDelivery fault) | _ = λ ()
  step-preserves observeHot f w v | (nodeRethrow fault) | _ = λ ()
  step-preserves observeAll f w v with pc f | lookup (connectionRef f) (peers w)
  ... | awaitAll | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | P.all ConnectionManagement.IGTypes.warm (P.runs p) | P.all ConnectionManagement.IGTypes.established (P.runs p)
  ...   | just clean | just clean | just clean = λ { refl → v }
  ...   | just clean | just clean | just (errored e₃) = λ { refl → v }
  ...   | just clean | just (errored e₂) | just clean = λ { refl → v }
  ...   | just clean | just (errored e₂) | just (errored e₃) = λ { refl → v }
  ...   | just (errored e₁) | just clean | just clean = λ { refl → v }
  ...   | just (errored e₁) | just clean | just (errored e₃) = λ { refl → v }
  ...   | just (errored e₁) | just (errored e₂) | just clean = λ { refl → v }
  ...   | just (errored e₁) | just (errored e₂) | just (errored e₃) = λ { refl → v }
  ...   | nothing | _ | _ = λ ()
  ...   | just clean | nothing | _ = λ ()
  ...   | just (errored e) | nothing | _ = λ ()
  ...   | just clean | just clean | nothing = λ ()
  ...   | just clean | just (errored e₂) | nothing = λ ()
  ...   | just (errored e₁) | just clean | nothing = λ ()
  ...   | just (errored e₁) | just (errored e₂) | nothing = λ ()
  step-preserves observeAll f w v | awaitAll | nothing = λ ()
  step-preserves observeAll f w v | begin | _ = λ ()
  step-preserves observeAll f w v | awaitAcquire | _ = λ ()
  step-preserves observeAll f w v | (startBundle t ns) | _ = λ ()
  step-preserves observeAll f w v | (publishBundle t) | _ = λ ()
  step-preserves observeAll f w v | markWarm | _ = λ ()
  step-preserves observeAll f w v | forkMonitor | _ = λ ()
  step-preserves observeAll f w v | finishActivation | _ = λ ()
  step-preserves observeAll f w v | awaitHot | _ = λ ()
  step-preserves observeAll f w v | callRelease | _ = λ ()
  step-preserves observeAll f w v | awaitRelease | _ = λ ()
  step-preserves observeAll f w v | delayFailure | _ = λ ()
  step-preserves observeAll f w v | (awaitCold result) | _ = λ ()
  step-preserves observeAll f w v | (complete result) | _ = λ ()
  step-preserves observeAll f w v | (acquirePolicy fault) | _ = λ ()
  step-preserves observeAll f w v | (nodeDelivery fault) | _ = λ ()
  step-preserves observeAll f w v | (nodeRethrow fault) | _ = λ ()
  step-preserves requestRelease f w v with pc f | lookup (connectionRef f) (peers w)
  ... | callRelease | just p with CM.advance (CM.beginRelease (caller f) (P.key p)) (cm w) in advanced
  ...   | nothing = λ ()
  ...   | just c = λ { refl → preserve (CM.beginRelease (caller f) (P.key p)) (cm w) advanced v }
  step-preserves requestRelease f w v | callRelease | nothing = λ ()
  step-preserves requestRelease f w v | begin | _ = λ ()
  step-preserves requestRelease f w v | awaitAcquire | _ = λ ()
  step-preserves requestRelease f w v | (startBundle t ns) | _ = λ ()
  step-preserves requestRelease f w v | (publishBundle t) | _ = λ ()
  step-preserves requestRelease f w v | markWarm | _ = λ ()
  step-preserves requestRelease f w v | forkMonitor | _ = λ ()
  step-preserves requestRelease f w v | finishActivation | _ = λ ()
  step-preserves requestRelease f w v | awaitHot | _ = λ ()
  step-preserves requestRelease f w v | awaitAll | _ = λ ()
  step-preserves requestRelease f w v | awaitRelease | _ = λ ()
  step-preserves requestRelease f w v | delayFailure | _ = λ ()
  step-preserves requestRelease f w v | (awaitCold result) | _ = λ ()
  step-preserves requestRelease f w v | (complete result) | _ = λ ()
  step-preserves requestRelease f w v | (acquirePolicy fault) | _ = λ ()
  step-preserves requestRelease f w v | (nodeDelivery fault) | _ = λ ()
  step-preserves requestRelease f w v | (nodeRethrow fault) | _ = λ ()
  step-preserves collectRelease f w v with pc f | lookup (caller f) (CM.released (cm w))
  ... | awaitRelease | just R.assertionFailure = λ { refl → v }
  ... | awaitRelease | just (R.success state) = λ { refl → v }
  ... | awaitRelease | just (R.unsupported state) = λ { refl → v }
  ... | awaitRelease | nothing = λ ()
  step-preserves collectRelease f w v | begin | _ = λ ()
  step-preserves collectRelease f w v | awaitAcquire | _ = λ ()
  step-preserves collectRelease f w v | (startBundle t ns) | _ = λ ()
  step-preserves collectRelease f w v | (publishBundle t) | _ = λ ()
  step-preserves collectRelease f w v | markWarm | _ = λ ()
  step-preserves collectRelease f w v | forkMonitor | _ = λ ()
  step-preserves collectRelease f w v | finishActivation | _ = λ ()
  step-preserves collectRelease f w v | awaitHot | _ = λ ()
  step-preserves collectRelease f w v | awaitAll | _ = λ ()
  step-preserves collectRelease f w v | callRelease | _ = λ ()
  step-preserves collectRelease f w v | delayFailure | _ = λ ()
  step-preserves collectRelease f w v | (awaitCold result) | _ = λ ()
  step-preserves collectRelease f w v | (complete result) | _ = λ ()
  step-preserves collectRelease f w v | (acquirePolicy fault) | _ = λ ()
  step-preserves collectRelease f w v | (nodeDelivery fault) | _ = λ ()
  step-preserves collectRelease f w v | (nodeRethrow fault) | _ = λ ()
  step-preserves observeCold f w v with pc f | lookup (connectionRef f) (peers w)
  ... | awaitCold result | just p with P.status p
  ...   | P.peerCold = λ { refl → v }
  ...   | P.peerHot = λ ()
  ...   | P.peerWarm = λ ()
  ...   | P.peerCooling = λ ()
  step-preserves observeCold f w v | awaitCold result | nothing = λ ()
  step-preserves observeCold f w v | begin | _ = λ ()
  step-preserves observeCold f w v | awaitAcquire | _ = λ ()
  step-preserves observeCold f w v | (startBundle t ns) | _ = λ ()
  step-preserves observeCold f w v | (publishBundle t) | _ = λ ()
  step-preserves observeCold f w v | markWarm | _ = λ ()
  step-preserves observeCold f w v | forkMonitor | _ = λ ()
  step-preserves observeCold f w v | finishActivation | _ = λ ()
  step-preserves observeCold f w v | awaitHot | _ = λ ()
  step-preserves observeCold f w v | awaitAll | _ = λ ()
  step-preserves observeCold f w v | callRelease | _ = λ ()
  step-preserves observeCold f w v | awaitRelease | _ = λ ()
  step-preserves observeCold f w v | delayFailure | _ = λ ()
  step-preserves observeCold f w v | (complete result) | _ = λ ()
  step-preserves observeCold f w v | (acquirePolicy fault) | _ = λ ()
  step-preserves observeCold f w v | (nodeDelivery fault) | _ = λ ()
  step-preserves observeCold f w v | (nodeRethrow fault) | _ = λ ()
  step-preserves operationTimeout f w v with pc f
  ... | awaitHot with peerStep P.timeoutDeactivate f w in moved
  ...   | nothing = λ ()
  ...   | just w′ = λ { refl → peer-preserves _ f w moved v }
  step-preserves operationTimeout f w v | awaitAll with peerStep P.timeoutClose f w in moved
  ... | nothing = λ ()
  ... | just w′ = λ { refl → peer-preserves _ f w moved v }
  step-preserves operationTimeout f w v | begin = λ ()
  step-preserves operationTimeout f w v | awaitAcquire = λ ()
  step-preserves operationTimeout f w v | (startBundle t ns) = λ ()
  step-preserves operationTimeout f w v | (publishBundle t) = λ ()
  step-preserves operationTimeout f w v | markWarm = λ ()
  step-preserves operationTimeout f w v | forkMonitor = λ ()
  step-preserves operationTimeout f w v | finishActivation = λ ()
  step-preserves operationTimeout f w v | callRelease = λ ()
  step-preserves operationTimeout f w v | awaitRelease = λ ()
  step-preserves operationTimeout f w v | delayFailure = λ ()
  step-preserves operationTimeout f w v | (awaitCold result) = λ ()
  step-preserves operationTimeout f w v | (complete result) = λ ()
  step-preserves operationTimeout f w v | (acquirePolicy fault) = λ ()
  step-preserves operationTimeout f w v | (nodeDelivery fault) = λ ()
  step-preserves operationTimeout f w v | (nodeRethrow fault) = λ ()
  step-preserves demotionTimeout f w v with pc f
  ... | awaitCold _ = λ { refl → v }
  step-preserves demotionTimeout f w v | begin = λ ()
  step-preserves demotionTimeout f w v | awaitAcquire = λ ()
  step-preserves demotionTimeout f w v | (startBundle t ns) = λ ()
  step-preserves demotionTimeout f w v | (publishBundle t) = λ ()
  step-preserves demotionTimeout f w v | markWarm = λ ()
  step-preserves demotionTimeout f w v | forkMonitor = λ ()
  step-preserves demotionTimeout f w v | finishActivation = λ ()
  step-preserves demotionTimeout f w v | awaitHot = λ ()
  step-preserves demotionTimeout f w v | awaitAll = λ ()
  step-preserves demotionTimeout f w v | callRelease = λ ()
  step-preserves demotionTimeout f w v | awaitRelease = λ ()
  step-preserves demotionTimeout f w v | delayFailure = λ ()
  step-preserves demotionTimeout f w v | (complete result) = λ ()
  step-preserves demotionTimeout f w v | (acquirePolicy fault) = λ ()
  step-preserves demotionTimeout f w v | (nodeDelivery fault) = λ ()
  step-preserves demotionTimeout f w v | (nodeRethrow fault) = λ ()
  step-preserves failureDelayElapsed f w v with pc f
  ... | delayFailure = λ { refl → v }
  step-preserves failureDelayElapsed f w v | begin = λ ()
  step-preserves failureDelayElapsed f w v | awaitAcquire = λ ()
  step-preserves failureDelayElapsed f w v | (startBundle t ns) = λ ()
  step-preserves failureDelayElapsed f w v | (publishBundle t) = λ ()
  step-preserves failureDelayElapsed f w v | markWarm = λ ()
  step-preserves failureDelayElapsed f w v | forkMonitor = λ ()
  step-preserves failureDelayElapsed f w v | finishActivation = λ ()
  step-preserves failureDelayElapsed f w v | awaitHot = λ ()
  step-preserves failureDelayElapsed f w v | awaitAll = λ ()
  step-preserves failureDelayElapsed f w v | callRelease = λ ()
  step-preserves failureDelayElapsed f w v | awaitRelease = λ ()
  step-preserves failureDelayElapsed f w v | (awaitCold result) = λ ()
  step-preserves failureDelayElapsed f w v | (complete result) = λ ()
  step-preserves failureDelayElapsed f w v | (acquirePolicy fault) = λ ()
  step-preserves failureDelayElapsed f w v | (nodeDelivery fault) = λ ()
  step-preserves failureDelayElapsed f w v | (nodeRethrow fault) = λ ()
  step-preserves (startFailed err) f w v with pc f | G.kind (work f)
  ... | startBundle t (n ∷ _) | G.establish with peerStep (P.startProtocol t n) f w in moved
  ...   | nothing = λ { refl → failed-preserves f w v }
  ...   | just _ = λ ()
  step-preserves (startFailed err) f w v | startBundle t (n ∷ _) | G.activate with peerStep (P.startProtocol t n) f w in moved
  ... | nothing = λ { refl → v }
  ... | just _ = λ ()
  step-preserves (startFailed err) f w v | startBundle t [] | _ = λ ()
  step-preserves (startFailed err) f w v | startBundle t (n ∷ ns) | G.forget = λ ()
  step-preserves (startFailed err) f w v | startBundle t (n ∷ ns) | G.close = λ ()
  step-preserves (startFailed err) f w v | startBundle t (n ∷ ns) | G.deactivate = λ ()
  step-preserves (startFailed err) f w v | begin | _ = λ ()
  step-preserves (startFailed err) f w v | awaitAcquire | _ = λ ()
  step-preserves (startFailed err) f w v | (publishBundle t) | _ = λ ()
  step-preserves (startFailed err) f w v | markWarm | _ = λ ()
  step-preserves (startFailed err) f w v | forkMonitor | _ = λ ()
  step-preserves (startFailed err) f w v | finishActivation | _ = λ ()
  step-preserves (startFailed err) f w v | awaitHot | _ = λ ()
  step-preserves (startFailed err) f w v | awaitAll | _ = λ ()
  step-preserves (startFailed err) f w v | callRelease | _ = λ ()
  step-preserves (startFailed err) f w v | awaitRelease | _ = λ ()
  step-preserves (startFailed err) f w v | delayFailure | _ = λ ()
  step-preserves (startFailed err) f w v | (awaitCold result) | _ = λ ()
  step-preserves (startFailed err) f w v | (complete result) | _ = λ ()
  step-preserves (startFailed err) f w v | (acquirePolicy fault) | _ = λ ()
  step-preserves (startFailed err) f w v | (nodeDelivery fault) | _ = λ ()
  step-preserves (startFailed err) f w v | (nodeRethrow fault) | _ = λ ()
  step-preserves choosePeerPolicy f w v with pc f
  ... | (acquirePolicy fault) = λ { refl → failed-preserves f w v }
  step-preserves choosePeerPolicy f w v | begin = λ ()
  step-preserves choosePeerPolicy f w v | awaitAcquire = λ ()
  step-preserves choosePeerPolicy f w v | (startBundle t ns) = λ ()
  step-preserves choosePeerPolicy f w v | (publishBundle t) = λ ()
  step-preserves choosePeerPolicy f w v | markWarm = λ ()
  step-preserves choosePeerPolicy f w v | forkMonitor = λ ()
  step-preserves choosePeerPolicy f w v | finishActivation = λ ()
  step-preserves choosePeerPolicy f w v | awaitHot = λ ()
  step-preserves choosePeerPolicy f w v | awaitAll = λ ()
  step-preserves choosePeerPolicy f w v | callRelease = λ ()
  step-preserves choosePeerPolicy f w v | awaitRelease = λ ()
  step-preserves choosePeerPolicy f w v | delayFailure = λ ()
  step-preserves choosePeerPolicy f w v | (awaitCold result) = λ ()
  step-preserves choosePeerPolicy f w v | (complete result) = λ ()
  step-preserves choosePeerPolicy f w v | (nodeDelivery fault) = λ ()
  step-preserves choosePeerPolicy f w v | (nodeRethrow fault) = λ ()
  step-preserves chooseNodePolicy f w v with pc f
  ... | (acquirePolicy fault) = λ { refl → v }
  step-preserves chooseNodePolicy f w v | begin = λ ()
  step-preserves chooseNodePolicy f w v | awaitAcquire = λ ()
  step-preserves chooseNodePolicy f w v | (startBundle t ns) = λ ()
  step-preserves chooseNodePolicy f w v | (publishBundle t) = λ ()
  step-preserves chooseNodePolicy f w v | markWarm = λ ()
  step-preserves chooseNodePolicy f w v | forkMonitor = λ ()
  step-preserves chooseNodePolicy f w v | finishActivation = λ ()
  step-preserves chooseNodePolicy f w v | awaitHot = λ ()
  step-preserves chooseNodePolicy f w v | awaitAll = λ ()
  step-preserves chooseNodePolicy f w v | callRelease = λ ()
  step-preserves chooseNodePolicy f w v | awaitRelease = λ ()
  step-preserves chooseNodePolicy f w v | delayFailure = λ ()
  step-preserves chooseNodePolicy f w v | (awaitCold result) = λ ()
  step-preserves chooseNodePolicy f w v | (complete result) = λ ()
  step-preserves chooseNodePolicy f w v | (nodeDelivery fault) = λ ()
  step-preserves chooseNodePolicy f w v | (nodeRethrow fault) = λ ()
  step-preserves deliverNodeException f w v with pc f
  ... | (nodeDelivery fault) = λ { refl → v }
  step-preserves deliverNodeException f w v | begin = λ ()
  step-preserves deliverNodeException f w v | awaitAcquire = λ ()
  step-preserves deliverNodeException f w v | (startBundle t ns) = λ ()
  step-preserves deliverNodeException f w v | (publishBundle t) = λ ()
  step-preserves deliverNodeException f w v | markWarm = λ ()
  step-preserves deliverNodeException f w v | forkMonitor = λ ()
  step-preserves deliverNodeException f w v | finishActivation = λ ()
  step-preserves deliverNodeException f w v | awaitHot = λ ()
  step-preserves deliverNodeException f w v | awaitAll = λ ()
  step-preserves deliverNodeException f w v | callRelease = λ ()
  step-preserves deliverNodeException f w v | awaitRelease = λ ()
  step-preserves deliverNodeException f w v | delayFailure = λ ()
  step-preserves deliverNodeException f w v | (awaitCold result) = λ ()
  step-preserves deliverNodeException f w v | (complete result) = λ ()
  step-preserves deliverNodeException f w v | (acquirePolicy fault) = λ ()
  step-preserves deliverNodeException f w v | (nodeRethrow fault) = λ ()
  step-preserves rethrowNodeException f w v with pc f
  ... | (nodeRethrow fault) = λ { refl → failed-preserves f w v }
  step-preserves rethrowNodeException f w v | begin = λ ()
  step-preserves rethrowNodeException f w v | awaitAcquire = λ ()
  step-preserves rethrowNodeException f w v | (startBundle t ns) = λ ()
  step-preserves rethrowNodeException f w v | (publishBundle t) = λ ()
  step-preserves rethrowNodeException f w v | markWarm = λ ()
  step-preserves rethrowNodeException f w v | forkMonitor = λ ()
  step-preserves rethrowNodeException f w v | finishActivation = λ ()
  step-preserves rethrowNodeException f w v | awaitHot = λ ()
  step-preserves rethrowNodeException f w v | awaitAll = λ ()
  step-preserves rethrowNodeException f w v | callRelease = λ ()
  step-preserves rethrowNodeException f w v | awaitRelease = λ ()
  step-preserves rethrowNodeException f w v | delayFailure = λ ()
  step-preserves rethrowNodeException f w v | (awaitCold result) = λ ()
  step-preserves rethrowNodeException f w v | (complete result) = λ ()
  step-preserves rethrowNodeException f w v | (acquirePolicy fault) = λ ()
  step-preserves rethrowNodeException f w v | (nodeDelivery fault) = λ ()

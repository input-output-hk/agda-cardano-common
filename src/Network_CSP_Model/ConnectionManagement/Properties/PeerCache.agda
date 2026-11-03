{-# OPTIONS --guardedness #-}

-- Provenance of peer actual/published cells, independent of physical wrappers.
module ConnectionManagement.Properties.PeerCache where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import Data.Nat using (ℕ)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (RunResult; Temperature; hot; clean; errored; number)
open import ConnectionManagement.Store using (lookup; put; delete)
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.IGRegistration as IG

-- The backing relation may name an older generation; it is never latest.
module Evidence (Back : PeerConnectionId → HandleId → MuxId → ℕ → RunResult → Set) where
  Cell : PeerConnectionId → HandleId → MuxId → ℕ → P.Cell → Set
  Cell ref h m n P.notStarted = ⊤
  Cell ref h m n P.running = ⊤
  Cell ref h m n (P.returned result) = Back ref h m n result
  Cell ref h m n (P.notRunning result) = Back ref h m n result
  Run : PeerConnectionId → HandleId → MuxId → P.ProtocolRun → Set
  Run ref h m r = Cell ref h m (number (P.descriptor r)) (P.actual r) ×
    Cell ref h m (number (P.descriptor r)) (P.published r)
  Runs : PeerConnectionId → HandleId → MuxId → List P.ProtocolRun → Set
  Runs ref h m = All (Run ref h m)
  Peer : PeerConnectionId → P.Peer → Set
  Peer ref p = Runs ref (P.handleRef p) (P.muxRef p) (P.runs p)
  Runtime : P.Runtime → Set
  Runtime = All (λ { (ref , p) → Peer ref p })

  -- Store operations retain provenance for all bindings, including duplicates.
  found-peer : ∀ ref p rows → Runtime rows → lookup ref rows ≡ just p → Peer ref p
  found-peer ref p [] [] eq = case eq of λ ()
  found-peer ref p ((q , old) ∷ rows) (valid ∷ rest) eq with ref ≟ q
  ... | yes refl = case just-injective eq of λ { refl → valid }
  ... | no _ = found-peer ref p rows rest eq
  put-peer : ∀ ref p rows → Peer ref p → Runtime rows → Runtime (put ref p rows)
  put-peer ref p [] valid [] = valid ∷ []
  put-peer ref p ((q , old) ∷ rows) valid (head ∷ rest) with ref ≟ q
  ... | yes refl = valid ∷ rest
  ... | no _ = head ∷ put-peer ref p rows valid rest
  delete-peer : ∀ ref rows → Runtime rows → Runtime (delete ref rows)
  delete-peer ref [] [] = []
  delete-peer ref ((q , old) ∷ rows) (head ∷ rest) with ref ≟ q
  ... | yes _ = rest
  ... | no _ = head ∷ delete-peer ref rows rest

  -- Starting may freeze an old observed result into the published action.
  observe : ∀ ref h m r → Run ref h m r → Cell ref h m (number (P.descriptor r)) (P.observe r)
  observe ref h m r (actual , published) with P.published r
  ... | P.running = actual
  ... | P.notStarted = published
  ... | P.returned result = published
  ... | P.notRunning result = published
  start : ∀ ref h m t n rs {out} → P.startRun t n rs ≡ just out → Runs ref h m rs → Runs ref h m out
  start ref h m t n [] eq [] = case eq of λ ()
  start ref h m t n (r ∷ rs) eq (valid ∷ rest) with number (P.descriptor r) ≟ n | P.belongs t r
  ... | yes _ | true with P.actual r | observe ref h m r valid
  ...   | P.running | _ = case eq of λ ()
  ...   | P.notStarted | observed = case just-injective eq of λ { refl → (tt , observed) ∷ rest }
  ...   | P.returned _ | observed = case just-injective eq of λ { refl → (tt , observed) ∷ rest }
  ...   | P.notRunning _ | observed = case just-injective eq of λ { refl → (tt , observed) ∷ rest }
  start ref h m t n (r ∷ rs) eq (valid ∷ rest) | yes _ | false with P.startRun t n rs in moved
  ... | nothing = case eq of λ ()
  ... | just tail = case just-injective eq of λ { refl → valid ∷ start ref h m t n rs moved rest }
  start ref h m t n (r ∷ rs) eq (valid ∷ rest) | no _ | _ with P.startRun t n rs in moved
  ... | nothing = case eq of λ ()
  ... | just tail = case just-injective eq of λ { refl → valid ∷ start ref h m t n rs moved rest }
  finish : ∀ ref h m n result rs {out} → Back ref h m n result → P.finishRun n result rs ≡ just out →
    Runs ref h m rs → Runs ref h m out
  finish ref h m n result [] backed eq [] = case eq of λ ()
  finish ref h m n result (r ∷ rs) backed eq (valid ∷ rest) with number (P.descriptor r) ≟ n
  ... | yes refl with P.actual r
  ...   | P.running = case just-injective eq of λ { refl → (backed , proj₂ valid) ∷ rest }
  ...   | P.notStarted = case eq of λ ()
  ...   | P.returned _ = case eq of λ ()
  ...   | P.notRunning _ = case eq of λ ()
  finish ref h m n result (r ∷ rs) backed eq (valid ∷ rest) | no _ with P.finishRun n result rs in moved
  ...   | nothing = case eq of λ ()
  ...   | just tail = case just-injective eq of λ { refl → valid ∷ finish ref h m n result rs backed moved rest }
  publish : ∀ ref h m t rs → Runs ref h m rs → Runs ref h m (P.publishRuns t rs)
  publish ref h m t [] [] = []
  publish ref h m t (r ∷ rs) (valid ∷ rest) with P.belongs t r
  ... | true = (proj₁ valid , tt) ∷ publish ref h m t rs rest
  ... | false = valid ∷ publish ref h m t rs rest
  retire : ∀ ref h m rs → Runs ref h m rs → Runs ref h m (P.retireHot rs)
  retire ref h m [] [] = []
  retire ref h m (r ∷ rs) (valid ∷ rest) with P.belongs hot r | P.observe r in observed
  ... | true | P.returned result =
    (subst (Cell ref h m (number (P.descriptor r))) observed (observe ref h m r valid) ,
     subst (Cell ref h m (number (P.descriptor r))) observed (observe ref h m r valid)) ∷ retire ref h m rs rest
  ... | true | P.notStarted = valid ∷ retire ref h m rs rest
  ... | true | P.running = valid ∷ retire ref h m rs rest
  ... | true | P.notRunning _ = valid ∷ retire ref h m rs rest
  ... | false | _ = valid ∷ retire ref h m rs rest
  initial : ∀ ref k h hd → Peer ref (P.initialPeer k h hd)
  initial ref k h hd = initialized (M.bundle hd)
    where
    initialized : ∀ protocols → Runs ref h (M.muxRef hd)
      (map (λ protocol → P.protocolRun protocol P.notStarted P.notStarted) protocols)
    initialized [] = []
    initialized (_ ∷ protocols) = (tt , tt) ∷ initialized protocols
  cool : ∀ ref p → Peer ref p → Peer ref (P.cool p)
  cool ref p valid with P.status p
  ... | P.peerCold = valid
  ... | P.peerCooling = valid
  ... | P.peerWarm = valid
  ... | P.peerHot = valid

  -- Raw result injection has no generic proof: only a real frontend commit
  -- supplies the Back witness required by finish above.
  safe : P.Action → Bool
  safe (P.protocolResult _ _) = false
  safe _ = true
  action : ∀ a ref p ig s {out} → safe a ≡ true → P.step a p ig s ≡ just out → Peer ref p → Peer ref (proj₁ out)
  action P.activate ref p ig s permitted eq valid with P.status p
  ... | P.peerWarm = case just-injective eq of λ { refl → valid }
  ... | P.peerCold = case eq of λ ()
  ... | P.peerCooling = case eq of λ ()
  ... | P.peerHot = case eq of λ ()
  action P.deactivate ref p ig s permitted eq valid with P.status p
  ... | P.peerWarm = case just-injective eq of λ { refl → valid }
  ... | P.peerHot = case just-injective eq of λ { refl → valid }
  ... | P.peerCold = case eq of λ ()
  ... | P.peerCooling = case eq of λ ()
  action P.close ref p ig s permitted eq valid = case just-injective eq of λ { refl → cool ref p valid }
  action (P.startProtocol t n) ref p ig s permitted eq valid with lookup (P.muxRef p) (IG.muxes (IG.execution ig))
  ... | nothing = case eq of λ ()
  ... | just m with M.status m
  ...   | M.ready with P.startRun t n (P.runs p) in moved
  ...     | nothing = case eq of λ ()
  ...     | just rs = case just-injective eq of λ { refl → start ref (P.handleRef p) (P.muxRef p) t n (P.runs p) moved valid }
  action (P.startProtocol t n) ref p ig s permitted eq valid | just m | M.stopping = case eq of λ ()
  action (P.startProtocol t n) ref p ig s permitted eq valid | just m | M.stopped = case eq of λ ()
  action (P.startProtocol t n) ref p ig s permitted eq valid | just m | M.failed _ = case eq of λ ()
  action (P.publishProtocols t) ref p ig s permitted eq valid with P.started t (P.runs p)
  ... | false = case eq of λ ()
  ... | true = case just-injective eq of λ { refl → publish ref (P.handleRef p) (P.muxRef p) t (P.runs p) valid }
  action (P.protocolResult _ _) ref p ig s () eq valid
  action P.markWarm ref p ig s permitted eq valid = case just-injective eq of λ { refl → valid }
  action P.forkMonitor ref p ig s permitted eq valid with P.monitorStarted p
  ... | true = case eq of λ ()
  ... | false = case just-injective eq of λ { refl → valid }
  action (P.markPromoted _) ref p ig s permitted eq valid = case just-injective eq of λ { refl → valid }
  action P.finishDeactivate ref p ig s permitted eq valid with P.all hot (P.runs p)
  ... | nothing = case eq of λ ()
  ... | just (ConnectionManagement.IGTypes.errored _) = case just-injective eq of λ { refl → cool ref p valid }
  ... | just ConnectionManagement.IGTypes.clean with P.status p
  ...   | P.peerCold = case just-injective eq of λ { refl → retire ref (P.handleRef p) (P.muxRef p) (P.runs p) valid }
  ...   | P.peerCooling = case just-injective eq of λ { refl → retire ref (P.handleRef p) (P.muxRef p) (P.runs p) valid }
  ...   | P.peerWarm = case just-injective eq of λ { refl → retire ref (P.handleRef p) (P.muxRef p) (P.runs p) valid }
  ...   | P.peerHot = case just-injective eq of λ { refl → retire ref (P.handleRef p) (P.muxRef p) (P.runs p) valid }
  action P.timeoutDeactivate ref p ig s permitted eq valid with lookup (P.muxRef p) (IG.muxes (IG.execution ig))
  ... | nothing = case eq of λ ()
  ... | just m = case just-injective eq of λ { refl → cool ref p valid }
  action P.timeoutClose ref p ig s permitted eq valid = action P.timeoutDeactivate ref p ig s permitted eq valid
  action P.monitorCooling ref p ig s permitted eq valid with P.status p | P.demoted (P.key p) s
  ... | P.peerCooling | true = case just-injective eq of λ { refl → valid }
  ... | P.peerCold | _ = case just-injective eq of λ { refl → valid }
  ... | P.peerCooling | false = case eq of λ ()
  ... | P.peerWarm | _ = case eq of λ ()
  ... | P.peerHot | _ = case eq of λ ()
  action P.monitorError ref p ig s permitted eq valid = case just-injective eq of λ { refl → cool ref p valid }

  -- Job actions never inject a result; CM-only operations leave peers alone.
  module Jobs where
    open import ConnectionManagement.Rules.PeerJobs hiding (start)
    import ConnectionManagement.Rules.PeerJobs as J
    import ConnectionManagement.OutboundMachine as CM
    import ConnectionManagement.Machine as Inbound
    import ConnectionManagement.Rules.OutboundAcquire as A
    import ConnectionManagement.Rules.OutboundCases as Cases
    import ConnectionManagement.Rules.OutboundRelease as R
    import ConnectionManagement.Rules.OutboundGovernor as G
    Valid : World → Set
    Valid w = Runtime (peers w)
    peer-preserves : ∀ a f w {w′} → safe a ≡ true → peerStep a f w ≡ just w′ → Valid w → Valid w′
    peer-preserves a f w permitted eq valid with lookup (connectionRef f) (peers w) in found
    ... | nothing = case eq of λ ()
    ... | just p with P.step a p (Inbound.inboundGovernor (CM.core (cm w))) (Inbound.world (CM.core (cm w))) in moved
    ...   | nothing = case eq of λ ()
    ...   | just (p′ , ig′) = case just-injective eq of λ { refl → put-peer (connectionRef f) p′ (peers w)
      (action a (connectionRef f) p (Inbound.inboundGovernor (CM.core (cm w))) (Inbound.world (CM.core (cm w))) permitted moved (found-peer (connectionRef f) p (peers w) valid found)) valid }
    start-preserves : ∀ t f w {out} → J.start t f w ≡ just out → Valid w → Valid (proj₂ out)
    start-preserves t f w eq valid with lookup (connectionRef f) (peers w)
    ... | nothing = case eq of λ ()
    ... | just p = case just-injective eq of λ { refl → valid }
    failed-preserves : ∀ f w → Valid w → Valid (proj₂ (failedEstablishment f w))
    failed-preserves f w valid with lookup (connectionRef f) (peers w) in found
    ... | nothing = valid
    ... | just p = put-peer (connectionRef f) _ (peers w) (found-peer (connectionRef f) p (peers w) valid found) valid

    -- Every source job action preserves the predicate, including CM calls.
    step-preserves : ∀ a f w → Valid w → ∀ {out} → step a f w ≡ just out → Valid (proj₂ out)
    step-preserves enter f w v with pc f | G.kind (work f)
    ... | begin | G.establish with CM.advance (CM.beginAcquire (caller f) (A.acquireRequest (G.peer (work f)) (child f) (socketRef f) outbound nothing)) (cm w) in advanced
    ...   | nothing = λ ()
    ...   | just c = λ { refl → v }
    step-preserves enter f w v | begin | G.activate with peerStep P.activate f w in moved
    ... | nothing = λ { refl → v }
    ... | just w′ = λ eq → start-preserves ConnectionManagement.IGTypes.hot f w′ eq (peer-preserves _ f w refl moved v)
    step-preserves enter f w v | begin | G.deactivate with lookup (connectionRef f) (peers w)
    ... | nothing = λ ()
    ... | just p with P.status p
    ...   | P.peerWarm = λ { refl → v }
    ...   | P.peerHot with peerStep P.deactivate f w in moved
    ...     | nothing = λ ()
    ...     | just w′ = λ { refl → peer-preserves _ f w refl moved v }
    step-preserves enter f w v | begin | G.deactivate | just p | P.peerCold = λ { refl → v }
    step-preserves enter f w v | begin | G.deactivate | just p | P.peerCooling = λ { refl → v }
    step-preserves enter f w v | begin | G.close with lookup (connectionRef f) (peers w) | peerStep P.close f w | (λ (next : World) → peer-preserves P.close f w {w′ = next} refl)
    ... | just p | just w′ | retained with P.status p
    ...   | P.peerCooling = λ { refl → retained w′ refl v }
    ...   | P.peerCold = λ { refl → retained w′ refl v }
    ...   | P.peerWarm = λ { refl → retained w′ refl v }
    ...   | P.peerHot = λ { refl → retained w′ refl v }
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
    ...   | just hd | nothing = λ eq → start-preserves ConnectionManagement.IGTypes.warm f (record w { peers = put (connectionRef f) (P.initialPeer k h hd) (peers w) }) eq (put-peer (connectionRef f) (P.initialPeer k h hd) (peers w) (initial (connectionRef f) k h hd) v)
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
    ...   | just w′ = λ { refl → peer-preserves _ f w refl moved v }
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
    ...     | ConnectionManagement.IGTypes.warm = λ eq → start-preserves ConnectionManagement.IGTypes.established f w′ eq (peer-preserves _ f w refl moved v)
    ...     | ConnectionManagement.IGTypes.established = λ { refl → peer-preserves _ f w refl moved v }
    ...     | ConnectionManagement.IGTypes.hot = λ { refl → peer-preserves _ f w refl moved v }
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
    ...   | just w′ = λ { refl → peer-preserves _ f w refl moved v }
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
    ...   | just w′ = λ { refl → peer-preserves _ f w refl moved v }
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
    ...   | just w′ = λ { refl → peer-preserves _ f w refl moved v }
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
    step-preserves observeHot f w v with pc f | lookup (connectionRef f) (peers w) in found
    ... | awaitHot | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | peerStep P.finishDeactivate f w | (λ (next : World) → peer-preserves P.finishDeactivate f w {w′ = next} refl)
    ...   | just clean | just w′ | retained = λ { refl → put-peer (connectionRef f)
      _ (peers w′) (retire (connectionRef f) (P.handleRef p) (P.muxRef p) (P.runs p)
        (found-peer (connectionRef f) p (peers w) v found)) (retained w′ refl v) }
    ...   | just (errored _) | just w′ | retained = λ { refl → retained w′ refl v }
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
    ...   | just c = λ { refl → v }
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
    ...   | just w′ = λ { refl → peer-preserves _ f w refl moved v }
    step-preserves operationTimeout f w v | awaitAll with peerStep P.timeoutClose f w in moved
    ... | nothing = λ ()
    ... | just w′ = λ { refl → peer-preserves _ f w refl moved v }
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

  -- Shared subsystem steps preserve cells except for the refused raw writer.
  module Subsystem where
    open import Data.Bool using (Bool; true; false; not; _∧_)
    open import Data.Nat using (ℕ; suc; _≤?_)
    open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
    open import Data.Bool.ListAction using (any)
    open import Data.Maybe using (Maybe; just; nothing)
    open import Data.Product using (_×_; _,_)
    open import Relation.Nullary using (yes; no; does)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import Class.DecEq using (_≟_)
    open import ConnectionManagement.Domain
    open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
    import ConnectionManagement.State as S
    open import ConnectionManagement.Store using (Store; lookup; put; delete)
    import ConnectionManagement.Machine as Inbound
    import ConnectionManagement.OutboundMachine as CM
    import ConnectionManagement.Rules.PeerActions as P
    import ConnectionManagement.Rules.PeerJobs as J
    import ConnectionManagement.Rules.OutboundGovernor as G
    import ConnectionManagement.Rules.IGRegistration as IG
    import ConnectionManagement.Rules.MuxRuntime as M
    import ConnectionManagement.Rules.HandlerLifecycle as Life

    import ConnectionManagement.Rules.OutboundAcquire as A
    open import ConnectionManagement.Subsystem
    safeSub : Action → Bool
    safeSub (protocolResult _ _ _) = false
    safeSub _ = true
    Valid : Configuration → Set
    Valid c = Runtime (J.peers (world c))

    -- All enabled actions are covered; unavailable attempts provide no transition.
    advance-preserves : ∀ a c {c′} → safeSub a ≡ true → advance a c ≡ just c′ → Valid c → Valid c′
    advance-preserves (core action) c permitted with CM.advance action (J.cm (world c)) in stepped
    ... | nothing = λ ()
    ... | just cm′ = λ { refl v → v }
    advance-preserves publishPublicState c permitted with pc c
    ... | publishPublic = λ { refl v → v }
    advance-preserves publishPublicState c permitted | sampleInputs = λ ()
    advance-preserves publishPublicState c permitted | prepareWait = λ ()
    advance-preserves publishPublicState c permitted | selecting = λ ()
    advance-preserves publishPublicState c permitted | (cancelTimer selected) = λ ()
    advance-preserves publishPublicState c permitted | (apply selected) = λ ()
    advance-preserves publishPublicState c permitted | (publishView work) = λ ()
    advance-preserves publishPublicState c permitted | (traceDecision work) = λ ()
    advance-preserves publishPublicState c permitted | (launch work) = λ ()
    advance-preserves publishPublicState c permitted | (register j rest) = λ ()
    advance-preserves publishPublicState c permitted | (completionAssertionFailed result) = λ ()
    advance-preserves (sampleTime t) c permitted with pc c | now c ≤? t
    ... | sampleInputs | yes _ = λ { refl v → v }
    ... | sampleInputs | no _ = λ ()
    advance-preserves (sampleTime t) c permitted | publishPublic | _ = λ ()
    advance-preserves (sampleTime t) c permitted | prepareWait | _ = λ ()
    advance-preserves (sampleTime t) c permitted | selecting | _ = λ ()
    advance-preserves (sampleTime t) c permitted | (cancelTimer selected) | _ = λ ()
    advance-preserves (sampleTime t) c permitted | (apply selected) | _ = λ ()
    advance-preserves (sampleTime t) c permitted | (publishView work) | _ = λ ()
    advance-preserves (sampleTime t) c permitted | (traceDecision work) | _ = λ ()
    advance-preserves (sampleTime t) c permitted | (launch work) | _ = λ ()
    advance-preserves (sampleTime t) c permitted | (register j rest) | _ = λ ()
    advance-preserves (sampleTime t) c permitted | (completionAssertionFailed result) | _ = λ ()
    -- Raw target-input writes do not affect the observed CM/IG predicate.
    advance-preserves (setTargets t) c permitted = λ { refl v → v }
    advance-preserves (selectMonitor delay) c permitted with pc c | G.monitored (J.peers (world c)) (privateState c)
    ... | selecting | changes@(_ ∷ _) with completeDelays changes delay
    ...   | false = λ ()
    ...   | true = λ { refl v → v }
    advance-preserves (selectMonitor delay) c permitted | selecting | [] = λ ()
    advance-preserves (selectMonitor delay) c permitted | publishPublic | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | sampleInputs | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | prepareWait | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | (cancelTimer selected) | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | (apply selected) | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | (publishView work) | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | (traceDecision work) | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | (launch work) | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | (register j rest) | _ = λ ()
    advance-preserves (selectMonitor delay) c permitted | (completionAssertionFailed result) | _ = λ ()
    advance-preserves selectCompletion c permitted with pc c | noMonitor c | completions c
    ... | selecting | true | x ∷ xs = λ { refl v → v }
    ... | selecting | true | [] = λ ()
    ... | selecting | false | _ = λ ()
    advance-preserves selectCompletion c permitted | publishPublic | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | sampleInputs | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | prepareWait | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | (cancelTimer selected) | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | (apply selected) | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | (publishView work) | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | (traceDecision work) | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | (launch work) | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | (register j rest) | _ | _ = λ ()
    advance-preserves selectCompletion c permitted | (completionAssertionFailed result) | _ | _ = λ ()
    advance-preserves selectTargets c permitted with pc c | noMonitor c | noCompletions c | noTargets c
    ... | selecting | true | true | false = λ { refl v → v }
    advance-preserves selectTargets c permitted | selecting | true | true | true = λ ()
    advance-preserves selectTargets c permitted | selecting | true | false | true = λ ()
    advance-preserves selectTargets c permitted | selecting | true | false | false = λ ()
    advance-preserves selectTargets c permitted | selecting | false | true | true = λ ()
    advance-preserves selectTargets c permitted | selecting | false | true | false = λ ()
    advance-preserves selectTargets c permitted | selecting | false | false | true = λ ()
    advance-preserves selectTargets c permitted | selecting | false | false | false = λ ()
    advance-preserves selectTargets c permitted | publishPublic | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | sampleInputs | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | prepareWait | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | (cancelTimer selected) | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | (apply selected) | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | (publishView work) | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | (traceDecision work) | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | (launch work) | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | (register j rest) | _ | _ | _ = λ ()
    advance-preserves selectTargets c permitted | (completionAssertionFailed result) | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted with pc c | noMonitor c | noCompletions c | noTargets c
    ... | selecting | true | true | true with G.choose (now c) picked (privateState c)
    ...   | nothing = λ ()
    ...   | just d = λ { refl v → v }
    advance-preserves (selectPolicy picked) c permitted | selecting | true | true | false = λ ()
    advance-preserves (selectPolicy picked) c permitted | selecting | true | false | true = λ ()
    advance-preserves (selectPolicy picked) c permitted | selecting | true | false | false = λ ()
    advance-preserves (selectPolicy picked) c permitted | selecting | false | true | true = λ ()
    advance-preserves (selectPolicy picked) c permitted | selecting | false | true | false = λ ()
    advance-preserves (selectPolicy picked) c permitted | selecting | false | false | true = λ ()
    advance-preserves (selectPolicy picked) c permitted | selecting | false | false | false = λ ()
    advance-preserves (selectPolicy picked) c permitted | publishPublic | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | sampleInputs | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | prepareWait | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | (cancelTimer selected) | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | (apply selected) | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | (publishView work) | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | (traceDecision work) | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | (launch work) | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | (register j rest) | _ | _ | _ = λ ()
    advance-preserves (selectPolicy picked) c permitted | (completionAssertionFailed result) | _ | _ | _ = λ ()
    advance-preserves registerWakeup c permitted with pc c
    ... | prepareWait = λ { refl v → v }
    advance-preserves registerWakeup c permitted | publishPublic = λ ()
    advance-preserves registerWakeup c permitted | sampleInputs = λ ()
    advance-preserves registerWakeup c permitted | selecting = λ ()
    advance-preserves registerWakeup c permitted | (cancelTimer selected) = λ ()
    advance-preserves registerWakeup c permitted | (apply selected) = λ ()
    advance-preserves registerWakeup c permitted | (publishView work) = λ ()
    advance-preserves registerWakeup c permitted | (traceDecision work) = λ ()
    advance-preserves registerWakeup c permitted | (launch work) = λ ()
    advance-preserves registerWakeup c permitted | (register j rest) = λ ()
    advance-preserves registerWakeup c permitted | (completionAssertionFailed result) = λ ()
    advance-preserves expireWakeup c permitted with pc c | wakeupAt c | wakeupReady c
    ... | selecting | just _ | false = λ { refl v → v }
    ... | selecting | just _ | true = λ ()
    ... | selecting | nothing | _ = λ ()
    advance-preserves expireWakeup c permitted | publishPublic | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | sampleInputs | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | prepareWait | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | (cancelTimer selected) | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | (apply selected) | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | (publishView work) | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | (traceDecision work) | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | (launch work) | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | (register j rest) | _ | _ = λ ()
    advance-preserves expireWakeup c permitted | (completionAssertionFailed result) | _ | _ = λ ()
    advance-preserves cancelWakeup c permitted with pc c
    ... | cancelTimer selected = λ { refl v → v }
    advance-preserves cancelWakeup c permitted | publishPublic = λ ()
    advance-preserves cancelWakeup c permitted | sampleInputs = λ ()
    advance-preserves cancelWakeup c permitted | prepareWait = λ ()
    advance-preserves cancelWakeup c permitted | selecting = λ ()
    advance-preserves cancelWakeup c permitted | (apply selected) = λ ()
    advance-preserves cancelWakeup c permitted | (publishView work) = λ ()
    advance-preserves cancelWakeup c permitted | (traceDecision work) = λ ()
    advance-preserves cancelWakeup c permitted | (launch work) = λ ()
    advance-preserves cancelWakeup c permitted | (register j rest) = λ ()
    advance-preserves cancelWakeup c permitted | (completionAssertionFailed result) = λ ()
    advance-preserves selectWakeup c permitted with pc c | noMonitor c | noCompletions c | noTargets c | wakeupReady c | wakeupAt c | G.firstReady (now c) (privateState c)
    ... | selecting | true | true | true | true | just deadline | nothing = λ { refl v → v }
    ... | selecting | false | _ | _ | _ | _ | _ = λ ()
    ... | selecting | true | false | _ | _ | _ | _ = λ ()
    ... | selecting | true | true | false | _ | _ | _ = λ ()
    ... | selecting | true | true | true | false | _ | _ = λ ()
    ... | selecting | true | true | true | true | nothing | _ = λ ()
    ... | selecting | true | true | true | true | just deadline | just ready = λ ()
    advance-preserves selectWakeup c permitted | publishPublic | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | sampleInputs | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | prepareWait | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | (cancelTimer selected) | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | (apply selected) | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | (publishView work) | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | (traceDecision work) | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | (launch work) | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | (register j rest) | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves selectWakeup c permitted | (completionAssertionFailed result) | _ | _ | _ | _ | _ | _ = λ ()
    advance-preserves (applyAt t) c permitted with pc c | now c ≤? t
    ... | apply (policy d) | yes _ = λ { refl v → v }
    ... | apply (completion result) | yes _ with G.completionAssertion result (privateState c)
    ...   | false = λ { refl v → v }
    ...   | true = λ { refl v → v }
    advance-preserves (applyAt t) c permitted | apply (monitor changes delay) | yes _ = λ { refl v → v }
    advance-preserves (applyAt t) c permitted | apply (targets t′) | yes _ = λ { refl v → v }
    advance-preserves (applyAt t) c permitted | apply (wakeup deadline) | yes _ with deadline ≤? t
    ...   | yes _ = λ { refl v → v }
    ...   | no _ = λ ()
    advance-preserves (applyAt t) c permitted | apply (policy d) | no _ = λ ()
    advance-preserves (applyAt t) c permitted | apply (completion result) | no _ = λ ()
    advance-preserves (applyAt t) c permitted | apply (monitor changes delay) | no _ = λ ()
    advance-preserves (applyAt t) c permitted | apply (targets t′) | no _ = λ ()
    advance-preserves (applyAt t) c permitted | apply (wakeup deadline) | no _ = λ ()
    advance-preserves (applyAt t) c permitted | publishPublic | _ = λ ()
    advance-preserves (applyAt t) c permitted | sampleInputs | _ = λ ()
    advance-preserves (applyAt t) c permitted | prepareWait | _ = λ ()
    advance-preserves (applyAt t) c permitted | selecting | _ = λ ()
    advance-preserves (applyAt t) c permitted | (cancelTimer selected) | _ = λ ()
    advance-preserves (applyAt t) c permitted | (publishView work) | _ = λ ()
    advance-preserves (applyAt t) c permitted | (traceDecision work) | _ = λ ()
    advance-preserves (applyAt t) c permitted | (launch work) | _ = λ ()
    advance-preserves (applyAt t) c permitted | (register j rest) | _ = λ ()
    advance-preserves (applyAt t) c permitted | (completionAssertionFailed result) | _ = λ ()
    advance-preserves publishCounters c permitted with pc c
    ... | publishView work = λ { refl v → v }
    advance-preserves publishCounters c permitted | publishPublic = λ ()
    advance-preserves publishCounters c permitted | sampleInputs = λ ()
    advance-preserves publishCounters c permitted | prepareWait = λ ()
    advance-preserves publishCounters c permitted | selecting = λ ()
    advance-preserves publishCounters c permitted | (cancelTimer selected) = λ ()
    advance-preserves publishCounters c permitted | (apply selected) = λ ()
    advance-preserves publishCounters c permitted | (traceDecision work) = λ ()
    advance-preserves publishCounters c permitted | (launch work) = λ ()
    advance-preserves publishCounters c permitted | (register j rest) = λ ()
    advance-preserves publishCounters c permitted | (completionAssertionFailed result) = λ ()
    advance-preserves traceSelection c permitted with pc c
    ... | traceDecision work = λ { refl v → v }
    advance-preserves traceSelection c permitted | publishPublic = λ ()
    advance-preserves traceSelection c permitted | sampleInputs = λ ()
    advance-preserves traceSelection c permitted | prepareWait = λ ()
    advance-preserves traceSelection c permitted | selecting = λ ()
    advance-preserves traceSelection c permitted | (cancelTimer selected) = λ ()
    advance-preserves traceSelection c permitted | (apply selected) = λ ()
    advance-preserves traceSelection c permitted | (publishView work) = λ ()
    advance-preserves traceSelection c permitted | (launch work) = λ ()
    advance-preserves traceSelection c permitted | (register j rest) = λ ()
    advance-preserves traceSelection c permitted | (completionAssertionFailed result) = λ ()
    advance-preserves registerJob c permitted with pc c
    ... | register j rest = λ { refl v → v }
    advance-preserves registerJob c permitted | publishPublic = λ ()
    advance-preserves registerJob c permitted | sampleInputs = λ ()
    advance-preserves registerJob c permitted | prepareWait = λ ()
    advance-preserves registerJob c permitted | selecting = λ ()
    advance-preserves registerJob c permitted | (cancelTimer selected) = λ ()
    advance-preserves registerJob c permitted | (apply selected) = λ ()
    advance-preserves registerJob c permitted | (publishView work) = λ ()
    advance-preserves registerJob c permitted | (traceDecision work) = λ ()
    advance-preserves registerJob c permitted | (launch work) = λ ()
    advance-preserves registerJob c permitted | (completionAssertionFailed result) = λ ()
    advance-preserves (forkJob caller child sock) c permitted with pc c | workerFree caller c
    ... | launch [] | _ = λ ()
    ... | launch (work ∷ rest) | true = λ { refl v → v }
    ... | launch (work ∷ rest) | false = λ ()
    advance-preserves (forkJob caller child sock) c permitted | publishPublic | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | sampleInputs | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | prepareWait | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | selecting | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | (cancelTimer selected) | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | (apply selected) | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | (publishView work) | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | (traceDecision work) | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | (register j rest) | _ = λ ()
    advance-preserves (forkJob caller child sock) c permitted | (completionAssertionFailed result) | _ = λ ()
    advance-preserves finishLaunch c permitted with pc c
    ... | launch [] = λ { refl v → v }
    ... | launch (work ∷ rest) = λ ()
    advance-preserves finishLaunch c permitted | publishPublic = λ ()
    advance-preserves finishLaunch c permitted | sampleInputs = λ ()
    advance-preserves finishLaunch c permitted | prepareWait = λ ()
    advance-preserves finishLaunch c permitted | selecting = λ ()
    advance-preserves finishLaunch c permitted | (cancelTimer selected) = λ ()
    advance-preserves finishLaunch c permitted | (apply selected) = λ ()
    advance-preserves finishLaunch c permitted | (publishView work) = λ ()
    advance-preserves finishLaunch c permitted | (traceDecision work) = λ ()
    advance-preserves finishLaunch c permitted | (register j rest) = λ ()
    advance-preserves finishLaunch c permitted | (completionAssertionFailed result) = λ ()
    advance-preserves (jobStep j action) c permitted with lookup j (jobs c)
    ... | nothing = λ ()
    ... | just frame with queued frame | J.step action (execution frame) (world c) in stepped
    ...   | false | just (f′ , w′) = λ { refl v → Jobs.step-preserves action (execution frame) (world c) v stepped }
    ...   | true | _ = λ ()
    ...   | false | nothing = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted with lookup j (jobs c)
    ... | nothing = λ ()
    ... | just frame with queued frame | J.pc (execution frame)
    ...   | false | J.complete result with validCompletionDelay (J.work (execution frame)) result delay
    ...     | false = λ ()
    ...     | true = λ { refl v → v }
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | true | _ = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.begin = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.awaitAcquire = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | (J.startBundle t ns) = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | (J.publishBundle t) = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.markWarm = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.forkMonitor = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.finishActivation = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.awaitHot = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.awaitAll = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.callRelease = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.awaitRelease = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | J.delayFailure = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | (J.awaitCold result) = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | (J.acquirePolicy fault) = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | (J.nodeDelivery fault) = λ ()
    advance-preserves (enqueueCompletion j delay) c permitted | just frame | false | (J.nodeRethrow fault) = λ ()
    advance-preserves (deregisterJob j) c permitted with lookup j (jobs c)
    ... | nothing = λ ()
    ... | just frame with queued frame | deregistered frame | any (λ x → does (x ≟ j)) (pool c)
    ...   | true | true | true = λ ()
    ...   | true | true | false = λ ()
    ...   | true | false | true = λ { refl v → v }
    ...   | true | false | false = λ ()
    ...   | false | true | true = λ ()
    ...   | false | true | false = λ ()
    ...   | false | false | true = λ ()
    ...   | false | false | false = λ ()
    advance-preserves (protocolResult ref n result) c ()
    advance-preserves (publishInitiatorResult ref i) c permitted with lookup ref (J.peers (world c)) in found
    ... | nothing = λ ()
    ... | just peer with P.takePending i (P.pendingResults peer) | lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c)))))) in observed
    ...   | just ((n , result) , retained) | just observedMux with Life.muxAllowed (P.muxRef peer) Life.jobAccess (Inbound.handlerLifecycles (CM.core (J.cm (world c))))
    ...     | false = λ ()
    ...     | true = λ { refl v → put-peer ref _ (J.peers (world c)) (found-peer ref peer (J.peers (world c)) v found) v }
    advance-preserves (publishInitiatorResult ref i) c permitted | just peer | nothing | _ = λ ()
    advance-preserves (publishInitiatorResult ref i) c permitted | just peer | just selected | nothing = λ ()
    advance-preserves (observeInitiatorFailure ref) c permitted with lookup ref (J.peers (world c))
    ... | nothing = λ ()
    ... | just peer with lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
    ...   | nothing = λ ()
    ...   | just observedMux with M.completions observedMux
    ...     | M.jobResult M.initiatorJob n (errored err) ∷ rest with CM.advance
      (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c)) in stepped
    ...       | nothing = λ ()
    ...       | just cm′ = λ { refl v → v }
    advance-preserves (observeInitiatorFailure ref) c permitted | just peer | just observedMux | [] = λ ()
    advance-preserves (observeInitiatorFailure ref) c permitted | just peer | just observedMux | M.jobResult M.responderJob n outcome ∷ rest = λ ()
    advance-preserves (observeInitiatorFailure ref) c permitted | just peer | just observedMux | M.jobResult M.initiatorJob n clean ∷ rest = λ ()
    advance-preserves (pollPeer ref caller) c permitted with lookup ref (J.peers (world c)) in found | lookup ref (monitors c)
    ... | just peer | nothing with P.monitorStarted peer | P.status peer
    ...   | true | P.peerCooling with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c)))) in moved
    ...     | nothing = λ ()
    ...     | just (peer′ , _) = λ { refl v → put-peer ref peer′ (J.peers (world c))
      (action P.monitorCooling ref peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c)))) refl moved (found-peer ref peer (J.peers (world c)) v found)) v }
    advance-preserves (pollPeer ref caller) c permitted | just peer | nothing | true | P.peerCold = λ { refl v → put-peer ref _ (J.peers (world c)) (found-peer ref peer (J.peers (world c)) v found) v }
    advance-preserves (pollPeer ref caller) c permitted | just peer | nothing | true | P.peerWarm with firstResult peer
    ... | nothing = λ ()
    ... | just (_ , errored _) = λ { refl v → put-peer ref _ (J.peers (world c)) (cool ref peer (found-peer ref peer (J.peers (world c)) v found)) v }
    ... | just (kind , clean) with workerFree caller c
    ...   | false = λ ()
    ...   | true = λ { refl v → v }
    advance-preserves (pollPeer ref caller) c permitted | just peer | nothing | true | P.peerHot with firstResult peer
    ... | nothing = λ ()
    ... | just (_ , errored _) = λ { refl v → put-peer ref _ (J.peers (world c)) (cool ref peer (found-peer ref peer (J.peers (world c)) v found)) v }
    ... | just (kind , clean) with workerFree caller c
    ...   | false = λ ()
    ...   | true = λ { refl v → v }
    advance-preserves (pollPeer ref caller) c permitted | just peer | nothing | false | _ = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f with J.pc f
    ... | J.awaitCold _ with P.step P.monitorCooling peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c)))) in moved
    ...   | nothing = λ ()
    ...   | just (peer′ , _) = λ { refl v → put-peer ref peer′ (J.peers (world c))
      (action P.monitorCooling ref peer (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c)))) refl moved (found-peer ref peer (J.peers (world c)) v found)) v }
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.begin = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.awaitAcquire = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | (J.startBundle t ns) = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | (J.publishBundle t) = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.markWarm = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.forkMonitor = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.finishActivation = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.awaitHot = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.awaitAll = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.callRelease = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.awaitRelease = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | J.delayFailure = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | (J.complete result) = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | (J.acquirePolicy fault) = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | (J.nodeDelivery fault) = λ ()
    advance-preserves (pollPeer ref caller) c permitted | just peer | just f | (J.nodeRethrow fault) = λ ()
    advance-preserves (pollPeer ref caller) c permitted | nothing | _ = λ ()
    advance-preserves (monitorStep ref action) c permitted with lookup ref (monitors c)
    ... | nothing = λ ()
    ... | just f with J.step action f (world c) in stepped
    ...   | nothing = λ ()
    ...   | just (f′ , w′) = λ { refl v → Jobs.step-preserves action f (world c) v stepped }
    advance-preserves (monitorFinished ref) c permitted with lookup ref (monitors c)
    ... | nothing = λ ()
    ... | just f with J.pc f
    ...   | J.complete _ = λ { refl v → v }
    ...   | J.begin = λ ()
    ...   | J.awaitAcquire = λ ()
    ...   | (J.startBundle t ns) = λ ()
    ...   | (J.publishBundle t) = λ ()
    ...   | J.markWarm = λ ()
    ...   | J.forkMonitor = λ ()
    ...   | J.finishActivation = λ ()
    ...   | J.awaitHot = λ ()
    ...   | J.awaitAll = λ ()
    ...   | J.callRelease = λ ()
    ...   | J.awaitRelease = λ ()
    ...   | J.delayFailure = λ ()
    ...   | (J.awaitCold result) = λ ()
    ...   | (J.acquirePolicy fault) = λ ()
    ...   | (J.nodeDelivery fault) = λ ()
    ...   | (J.nodeRethrow fault) = λ ()

  -- Pool/cancellation and monitor bookkeeping preserve the peer cell evidence.
  module Supervised (isIOManagerError : ErrorId → Bool) where
    import ConnectionManagement.Subsystem as Sub
    import ConnectionManagement.Rules.PeerJobs as J
    import ConnectionManagement.Rules.OutboundGovernor as G
    import ConnectionManagement.Rules.CallerCancellation as Cancel
    import ConnectionManagement.Rules.OutboundAcquire as A
    import ConnectionManagement.OutboundMachine as CM
    import ConnectionManagement.Rules.ProductionPolicy as Policy
    import ConnectionManagement.PeerSupervision as Supervision
    private
      module PS = Supervision isIOManagerError
      module GP = PS.GP
    safeGovernor : GP.Action → Bool
    safeGovernor (GP.run a) = Subsystem.safeSub a
    safeGovernor _ = true
    safePeer : PS.Action → Bool
    safePeer (PS.run a) = safeGovernor a
    safePeer _ = true
    GovernorValid : GP.State → Set
    GovernorValid s = Subsystem.Valid (GP.machine s)
    Valid : PS.State → Set
    Valid s = Subsystem.Valid (PS.machine s)
    production-preserves : ∀ a s {t} → Subsystem.safeSub a ≡ true → GP.Production.step (Policy.dispatch a) s ≡ just t →
      Subsystem.Valid (Policy.machine s) → Subsystem.Valid (Policy.machine t)
    production-preserves a s permitted eq valid with GP.Production.step-projects (Policy.dispatch a) s eq
    ... | Sub.next moved Sub.done = Subsystem.advance-preserves a _ permitted moved valid

    module Governor where
      private
        module Pool = GP.Pool

      restore : ∀ f c → Subsystem.Valid c → Subsystem.Valid (GP.restoreCold f c)
      restore f c valid with G.kind (J.work f) | J.pc f
      ... | G.establish | J.begin = valid
      ... | G.establish | J.complete result = valid
      restore f c valid | G.establish | J.awaitAcquire with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | (J.startBundle t ns) with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | (J.publishBundle t) with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | J.markWarm with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | J.forkMonitor with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | J.finishActivation with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | J.awaitHot with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | J.awaitAll with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | J.callRelease with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | J.awaitRelease with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | J.delayFailure with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | (J.awaitCold result) with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | (J.acquirePolicy fault) with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | (J.nodeDelivery fault) with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.establish | (J.nodeRethrow fault) with lookup (J.connectionRef f) (J.peers (Sub.world c)) in found
      ... | nothing = valid
      ... | just peer = put-peer (J.connectionRef f) _ (J.peers (Sub.world c)) (found-peer (J.connectionRef f) peer (J.peers (Sub.world c)) valid found) valid
      restore f c valid | G.forget | _ = valid
      restore f c valid | G.activate | _ = valid
      restore f c valid | G.close | _ = valid
      restore f c valid | G.deactivate | _ = valid


      delivery-valid : ∀ blocked err s {t} → GP.deliver blocked err s ≡ just t → GovernorValid s → GovernorValid t
      delivery-valid blocked err s eq valid with Pool.phase (GP.pool s)
      ... | Pool.cancelPending j with lookup j (Sub.jobs (GP.machine s)) | Pool.step Pool.deliverCancel (GP.pool s)
      ...   | just jf | just next with Cancel.start (J.caller (Sub.execution jf)) err
        (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s)
      ...     | just (f , c) = case just-injective eq of λ { refl → valid }
      ...     | nothing = case eq of λ ()
      delivery-valid blocked err s eq valid | Pool.cancelPending j | nothing | _ = case eq of λ ()
      delivery-valid blocked err s eq valid | Pool.cancelPending j | just jf | nothing = case eq of λ ()
      delivery-valid blocked err s eq valid | Pool.openPool = case eq of λ ()
      delivery-valid blocked err s eq valid | Pool.closing = case eq of λ ()
      delivery-valid blocked err s eq valid | Pool.closedPool = case eq of λ ()
      delivery-valid blocked err s eq valid | Pool.joinPending j = case eq of λ ()

      step-preserves : ∀ action s {s′} → safeGovernor action ≡ true → GP.step action s ≡ just s′ → GovernorValid s → GovernorValid s′
      step-preserves (GP.run action) s permitted eq valid with GP.normalPool action s | GP.Production.step (Policy.dispatch action) (GP.source s) in sourceStep
      ... | just p′ | just source′ with GP.noteReturn action (Policy.machine source′) p′
      ...   | just p″ = case just-injective eq of λ { refl → production-preserves action (GP.source s) permitted sourceStep valid }
      ...   | nothing = case eq of λ ()
      step-preserves (GP.run action) s permitted eq valid | nothing | _ = case eq of λ ()
      step-preserves (GP.run action) s permitted eq valid | just p′ | nothing = case eq of λ ()
      step-preserves (GP.cleanup j action) s permitted eq valid with lookup j (GP.unwinding s) in found
      ... | nothing = case eq of λ ()
      ... | just f with Cancel.step action f (GP.cm s) in cleaned
      ...   | nothing = case eq of λ ()
      ...   | just (f′ , c′) = case just-injective eq of λ { refl → valid }
      step-preserves (GP.deliverCancellation err) s permitted eq valid = delivery-valid false err s eq valid
      step-preserves (GP.deliverOpenCancellation err) s permitted eq valid = delivery-valid true err s eq valid
      step-preserves (GP.handoff w) s permitted eq valid with GP.region w s | lookup w (CM.acquiring (GP.cm s))
      ... | Cancel.forkedBeforeHandoff | just f with A.pc f
      ...   | A.connectedCommit _ _ _ = case just-injective eq of λ { refl → valid }
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | A.selecting = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.count next) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.allocatePromise e) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.openSocket e pid) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.configureSocket e pid) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.bindSocket e pid) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.connectSocket e pid) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.localAddress e pid) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.updateAddress e pid key) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.forkHandler e pid key) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.awaitResult e pid key) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.commitResult e key result) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.waitingInbound e key) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.closeError e err) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.removeError e err) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | just f | (A.complete result) = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.forkedBeforeHandoff | nothing = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.ordinary | _ = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.protectedCleanup | _ = case eq of λ ()
      step-preserves (GP.handoff w) s permitted eq valid | Cancel.interruptibleOpen | _ = case eq of λ ()
      step-preserves (GP.beginClose order) s permitted eq valid with Pool.step (Pool.beginClose order) (GP.pool s) in advanced
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves GP.requestCancel s permitted eq valid with Pool.step Pool.requestCancel (GP.pool s) in advanced
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves GP.join s permitted eq valid with Pool.step Pool.join (GP.pool s) in advanced
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves GP.finishClose s permitted eq valid with Pool.step Pool.finishClose (GP.pool s) in advanced
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves (GP.publishAsyncResult j) s permitted eq valid with Pool.step (Pool.publishAsyncResult j) (GP.pool s) in advanced
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves (GP.bodyUnwound j) s permitted eq valid with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
      ... | just f | just jf with Cancel.pc f
      ...   | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
      ...     | just p′ = case just-injective eq of λ { refl → restore (Sub.execution jf) (GP.machine s) valid }
      ...     | nothing = case eq of λ ()
      step-preserves (GP.bodyUnwound j) s permitted eq valid | just f | just jf | Cancel.finished Cancel.cleanupComplete with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
      ... | just p′ = case just-injective eq of λ { refl → restore (Sub.execution jf) (GP.machine s) valid }
      ... | nothing = case eq of λ ()
      step-preserves (GP.bodyUnwound j) s permitted eq valid | just f | just jf | Cancel.cleaning active = case eq of λ ()
      step-preserves (GP.bodyUnwound j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
      step-preserves (GP.bodyUnwound j) s permitted eq valid | nothing | _ = case eq of λ ()
      step-preserves (GP.bodyUnwound j) s permitted eq valid | just f | nothing = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
      ... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
      ...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with Pool.step (Pool.resumeAfterUnwindError j) (GP.pool s) in advanced
      ...     | just p′ = case just-injective eq of λ { refl → valid }
      ...     | nothing = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.cleaning active | _ | _ = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished Cancel.abandoned | _ | _ = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished Cancel.cleanupComplete | _ | _ = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.noCaller | _ = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.releasing active | _ = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.begin = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.startBundle t ns) = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.publishBundle t) = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.markWarm = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.forkMonitor = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.finishActivation = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitHot = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitAll = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.callRelease = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitRelease = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.delayFailure = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.awaitCold result) = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.complete result) = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.acquirePolicy fault) = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeDelivery fault) = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeRethrow fault) = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | nothing | _ = case eq of λ ()
      step-preserves (GP.recoverCloseFailure j) s permitted eq valid | just f | nothing = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid with lookup j (Sub.jobs (GP.machine s)) | Pool.step (Pool.deregister j) (GP.pool s) in advanced
      ... | just jf | just p′ with lookup j (Pool.handles (GP.pool s))
      ...   | just (Pool.deregisterPending Pool.cancelledExit) = case just-injective eq of λ { refl → valid }
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | just jf | just p′ | nothing = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | just jf | just p′ | just Pool.bodyRunning = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | just jf | just p′ | just (Pool.bodyReturned result) = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | just jf | just p′ | just Pool.bodyUnwinding = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | just jf | just p′ | just (Pool.deregisterPending Pool.normalExit) = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | just jf | just p′ | just (Pool.deregistered ex) = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | just jf | just p′ | just (Pool.resultAvailable ex) = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | nothing | _ = case eq of λ ()
      step-preserves (GP.deregisterCancelled j) s permitted eq valid | just jf | nothing = case eq of λ ()



    module Monitors where
      import ConnectionManagement.Rules.AsyncScope as Scope
      private
        module Pool = PS.Pool
      finish-peer : ∀ clear ref s → Valid s → Valid (PS.finishPeer clear ref s)
      finish-peer clear ref s valid with lookup ref (J.peers (Sub.world (PS.machine s))) in found
      ... | nothing = valid
      ... | just p = put-peer ref _ (J.peers (Sub.world (PS.machine s)))
        (found-peer ref p (J.peers (Sub.world (PS.machine s))) valid found) valid
      note-poll : ∀ ref before after → Valid after → Valid (PS.notePoll ref before after)
      note-poll ref before after valid with PS.byPeer ref (PS.monitors before) |
        lookup ref (J.peers (Sub.world (PS.machine before))) | lookup ref (J.peers (Sub.world (PS.machine after))) in found
      ... | just (tid , t) | just old | just next with P.monitorStarted next
      ...   | false = put-peer ref _ (J.peers (Sub.world (PS.machine after)))
        (found-peer ref next (J.peers (Sub.world (PS.machine after))) valid found) valid
      ...   | true = valid
      note-poll ref before after valid | nothing | _ | _ = valid
      note-poll ref before after valid | just _ | nothing | _ = valid
      note-poll ref before after valid | just _ | just _ | nothing = valid

      note-governor : ∀ a before after → Valid after → Valid (PS.noteGovernor a before after)
      note-governor (GP.run (Sub.core a)) before after valid = valid
      note-governor (GP.run Sub.publishPublicState) before after valid = valid
      note-governor (GP.run (Sub.sampleTime t)) before after valid = valid
      note-governor (GP.run (Sub.applyAt t)) before after valid = valid
      note-governor (GP.run (Sub.setTargets ts)) before after valid = valid
      note-governor (GP.run (Sub.selectMonitor ds)) before after valid = valid
      note-governor (GP.run Sub.selectCompletion) before after valid = valid
      note-governor (GP.run Sub.selectTargets) before after valid = valid
      note-governor (GP.run Sub.selectWakeup) before after valid = valid
      note-governor (GP.run Sub.registerWakeup) before after valid = valid
      note-governor (GP.run Sub.expireWakeup) before after valid = valid
      note-governor (GP.run Sub.cancelWakeup) before after valid = valid
      note-governor (GP.run Sub.publishCounters) before after valid = valid
      note-governor (GP.run Sub.traceSelection) before after valid = valid
      note-governor (GP.run (Sub.selectPolicy ps)) before after valid = valid
      note-governor (GP.run (Sub.forkJob w child sock)) before after valid = valid
      note-governor (GP.run Sub.registerJob) before after valid = valid
      note-governor (GP.run Sub.finishLaunch) before after valid = valid
      note-governor (GP.run (Sub.jobStep j a)) before after valid = valid
      note-governor (GP.run (Sub.enqueueCompletion j delay)) before after valid = valid
      note-governor (GP.run (Sub.deregisterJob j)) before after valid = valid
      note-governor (GP.run (Sub.protocolResult ref n result)) before after valid = valid
      note-governor (GP.run (Sub.publishInitiatorResult ref i)) before after valid = valid
      note-governor (GP.run (Sub.pollPeer ref w)) before after valid = note-poll ref before after valid
      note-governor (GP.run (Sub.monitorStep ref a)) before after valid = valid
      note-governor (GP.run (Sub.monitorFinished ref)) before after valid = valid
      note-governor (GP.run (Sub.observeInitiatorFailure ref)) before after valid = valid
      note-governor (GP.handoff w) before after valid = valid
      note-governor (GP.beginClose order) before after valid = valid
      note-governor GP.requestCancel before after valid = valid
      note-governor GP.join before after valid = valid
      note-governor GP.finishClose before after valid = valid
      note-governor (GP.deliverCancellation err) before after valid = valid
      note-governor (GP.deliverOpenCancellation err) before after valid = valid
      note-governor (GP.cleanup j a) before after valid = valid
      note-governor (GP.bodyUnwound j) before after valid = valid
      note-governor (GP.recoverCloseFailure j) before after valid = valid
      note-governor (GP.deregisterCancelled j) before after valid = valid
      note-governor (GP.publishAsyncResult j) before after valid = valid


      fork-preserves : ∀ j w s {s′} → PS.fork j w s ≡ just s′ → Valid s → Valid s′
      fork-preserves j w s eq valid with lookup j (Sub.jobs (PS.machine s)) | PS.byParent j (PS.monitors s) | PS.freshWorker w s
      ... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) |
        J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s)) |
        PS.byPeer (J.connectionRef (Sub.execution jf)) (PS.monitors s)
      ...   | G.establish | J.forkMonitor | true | nothing with
        Sub.advance (Sub.jobStep j J.launchMonitor) (PS.machine s) in advanced |
        Pool.step (Pool.forkConcurrent (ident (serial w))) (PS.monitorPool s)
      ...     | just c′ | just p′ = case just-injective eq of λ { refl → Subsystem.advance-preserves (Sub.jobStep j J.launchMonitor) (PS.machine s) {c′ = c′} refl advanced valid }
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | nothing | any = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | just c′ | nothing = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.forget | pc | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.activate | pc | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.close | pc | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.deactivate | pc | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.begin | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.awaitAcquire | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.startBundle temp ns) | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.publishBundle temp) | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.markWarm | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.finishActivation | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.awaitHot | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.awaitAll | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.callRelease | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.awaitRelease | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.delayFailure | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.awaitCold result) | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.complete result) | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.acquirePolicy fault) | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.nodeDelivery fault) | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | (J.nodeRethrow fault) | running | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.forkMonitor | false | peer = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | true | G.establish | J.forkMonitor | true | just peer = case eq of λ ()
      fork-preserves j w s eq valid | nothing | any | fresh = case eq of λ ()
      fork-preserves j w s eq valid | just jf | just previous | fresh = case eq of λ ()
      fork-preserves j w s eq valid | just jf | nothing | false = case eq of λ ()


      detach-valid : ∀ err t s {f s′} → PS.detach err t s ≡ just (f , s′) → Valid s → Valid s′
      detach-valid err t s eq valid with lookup (PS.worker t) (CM.acquiring (PS.cm s))
      ... | just active = case eq of λ ()
      ... | nothing with lookup (PS.peerRef t) (Sub.monitors (PS.machine s))
      ...   | nothing with Cancel.start (PS.worker t) err Cancel.ordinary (PS.cm s)
      ...     | just (f , c′) = case just-injective eq of λ { refl → valid }
      ...     | nothing = case eq of λ ()
      detach-valid err t s eq valid | nothing | just follow with J.caller follow ≟ PS.worker t
      ... | no _ = case eq of λ ()
      ... | yes _ with Cancel.start (PS.worker t) err Cancel.ordinary (PS.cm s)
      ...   | nothing = case eq of λ ()
      ...   | just (f , c′) = case just-injective eq of λ { refl → valid }


      delivery-preserves : ∀ blocked err s {s′} → PS.deliverMonitor blocked err s ≡ just s′ → Valid s → Valid s′
      delivery-preserves blocked err s eq valid with Pool.phase (PS.monitorPool s)
      ... | Pool.cancelPending tid with lookup tid (PS.monitors s)
      ...   | nothing = case eq of λ ()
      ...   | just t with PS.monitorDeliverable blocked (PS.pc t) | Pool.step Pool.deliverCancel (PS.monitorPool s)
      ...     | true | just p′ with PS.detach err t s in detached
      ...       | nothing = case eq of λ ()
      ...       | just (f , s′) = case just-injective eq of λ { refl → detach-valid err t s {f = f} {s′ = s′} detached valid }
      delivery-preserves blocked err s eq valid | Pool.cancelPending tid | just t | false | any = case eq of λ ()
      delivery-preserves blocked err s eq valid | Pool.cancelPending tid | just t | true | nothing = case eq of λ ()
      delivery-preserves blocked err s eq valid | Pool.openPool = case eq of λ ()
      delivery-preserves blocked err s eq valid | Pool.closing = case eq of λ ()
      delivery-preserves blocked err s eq valid | Pool.closedPool = case eq of λ ()
      delivery-preserves blocked err s eq valid | (Pool.joinPending j) = case eq of λ ()


      step-preserves : ∀ action s {s′} → safePeer action ≡ true → PS.step action s ≡ just s′ → Valid s → Valid s′
      step-preserves (PS.run action) s permitted eq valid with PS.governorAllowed action s
      ... | false = case eq of λ ()
      ... | true with GP.step action (PS.governor s) in advanced
      ...   | nothing = case eq of λ ()
      ...   | just g′ = case just-injective eq of λ { refl →
        note-governor action s (record s { governor = g′ })
          (Governor.step-preserves action (PS.governor s) permitted advanced valid) }
      step-preserves (PS.forkMonitor j w) s permitted eq valid = fork-preserves j w s eq valid
      step-preserves (PS.registerMonitor tid) s permitted eq valid with lookup tid (PS.monitors s)
      ... | nothing = case eq of λ ()
      ... | just t with PS.parentPC t | Pool.step (Pool.registerConcurrent tid) (PS.monitorPool s)
      ...   | PS.created | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves (PS.registerMonitor tid) s permitted eq valid | just t | PS.registered | any = case eq of λ ()
      step-preserves (PS.registerMonitor tid) s permitted eq valid | just t | PS.returned | any = case eq of λ ()
      step-preserves (PS.registerMonitor tid) s permitted eq valid | just t | PS.created | nothing = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
      ... | just (tid , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s))
      ...   | PS.registered | J.forkMonitor | true = case just-injective eq of λ { refl → valid }
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.begin | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.awaitAcquire | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | (J.startBundle temp ns) | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | (J.publishBundle temp) | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.markWarm | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.finishActivation | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.awaitHot | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.awaitAll | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.callRelease | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.awaitRelease | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.delayFailure | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | (J.awaitCold result) | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | (J.complete result) | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | (J.acquirePolicy fault) | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | (J.nodeDelivery fault) | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | (J.nodeRethrow fault) | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.created | pc | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.returned | pc | running = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just (tid , t) | just jf | PS.registered | J.forkMonitor | false = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | nothing | any = case eq of λ ()
      step-preserves (PS.returnEstablishment j) s permitted eq valid | just pair | nothing = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
      ... | just pair | just jf with PS.parentPC (proj₂ pair) | J.pc (Sub.execution jf)
      ...   | PS.returned | J.complete result with GP.Pool.step
        (GP.Pool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s))
      ...     | nothing = case eq of λ ()
      ...     | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.begin = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.awaitAcquire = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | (J.startBundle temp ns) = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | (J.publishBundle temp) = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.markWarm = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.finishActivation = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.awaitHot = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.awaitAll = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.callRelease = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.awaitRelease = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.delayFailure = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | (J.awaitCold result) = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | (J.acquirePolicy fault) = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | (J.nodeDelivery fault) = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | (J.nodeRethrow fault) = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.returned | J.forkMonitor = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.created | pc = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | just jf | PS.registered | pc = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | nothing | any = case eq of λ ()
      step-preserves (PS.finishEstablishment j) s permitted eq valid | just pair | nothing = case eq of λ ()
      step-preserves (PS.monitorException tid err) s permitted eq valid with lookup tid (PS.monitors s)
      ... | nothing = case eq of λ ()
      ... | just t with PS.bodyActive tid t s | PS.detach err t s in detached
      ...   | true | just (f , s′) = case just-injective eq of λ { refl → detach-valid err t s {f = f} {s′ = s′} detached valid }
      step-preserves (PS.monitorException tid err) s permitted eq valid | just t | false | any = case eq of λ ()
      step-preserves (PS.monitorException tid err) s permitted eq valid | just t | true | nothing = case eq of λ ()
      step-preserves (PS.commitMonitorError tid) s permitted eq valid with lookup tid (PS.monitors s)
      ... | nothing = case eq of λ ()
      ... | just t with PS.pc t | lookup (PS.peerRef t) (J.peers (Sub.world (PS.machine s))) in found
      ...   | PS.errorWait err | just peer with P.demoted (P.key peer) (PS.shared s)
      ...     | false = case eq of λ ()
      ...     | true = case just-injective eq of λ { refl → put-peer (PS.peerRef t) _ (J.peers (Sub.world (PS.machine s))) (found-peer (PS.peerRef t) peer (J.peers (Sub.world (PS.machine s))) valid found) valid }
      step-preserves (PS.commitMonitorError tid) s permitted eq valid | just t | PS.observing | peer = case eq of λ ()
      step-preserves (PS.commitMonitorError tid) s permitted eq valid | just t | PS.normalFinishing | peer = case eq of λ ()
      step-preserves (PS.commitMonitorError tid) s permitted eq valid | just t | PS.cancelling | peer = case eq of λ ()
      step-preserves (PS.commitMonitorError tid) s permitted eq valid | just t | PS.exited | peer = case eq of λ ()
      step-preserves (PS.commitMonitorError tid) s permitted eq valid | just t | (PS.errorFinishing err) | peer = case eq of λ ()
      step-preserves (PS.commitMonitorError tid) s permitted eq valid | just t | PS.errorWait err | nothing = case eq of λ ()
      step-preserves (PS.finishMonitor tid) s permitted eq valid with lookup tid (PS.monitors s)
      ... | nothing = case eq of λ ()
      ... | just t with PS.pc t | Pool.step (Pool.bodyReturnedWith tid nothing) (PS.monitorPool s)
      ...   | PS.normalFinishing | just p′ = case just-injective eq of λ { refl → finish-peer true (PS.peerRef t) s valid }
      step-preserves (PS.finishMonitor tid) s permitted eq valid | just t | PS.observing | pool = case eq of λ ()
      step-preserves (PS.finishMonitor tid) s permitted eq valid | just t | PS.cancelling | pool = case eq of λ ()
      step-preserves (PS.finishMonitor tid) s permitted eq valid | just t | PS.exited | pool = case eq of λ ()
      step-preserves (PS.finishMonitor tid) s permitted eq valid | just t | (PS.errorWait err) | pool = case eq of λ ()
      step-preserves (PS.finishMonitor tid) s permitted eq valid | just t | (PS.errorFinishing err) | pool = case eq of λ ()
      step-preserves (PS.finishMonitor tid) s permitted eq valid | just t | PS.normalFinishing | nothing = case eq of λ ()
      step-preserves (PS.finishMonitorError tid) s permitted eq valid with lookup tid (PS.monitors s)
      ... | nothing = case eq of λ ()
      ... | just t with PS.pc t
      ...   | PS.errorFinishing err with Pool.step (Pool.bodyReturnedWith tid (just err)) (PS.monitorPool s)
      ...     | nothing = case eq of λ ()
      ...     | just p′ = case just-injective eq of λ { refl → finish-peer true (PS.peerRef t) s valid }
      step-preserves (PS.finishMonitorError tid) s permitted eq valid | just t | PS.observing = case eq of λ ()
      step-preserves (PS.finishMonitorError tid) s permitted eq valid | just t | PS.normalFinishing = case eq of λ ()
      step-preserves (PS.finishMonitorError tid) s permitted eq valid | just t | PS.cancelling = case eq of λ ()
      step-preserves (PS.finishMonitorError tid) s permitted eq valid | just t | PS.exited = case eq of λ ()
      step-preserves (PS.finishMonitorError tid) s permitted eq valid | just t | (PS.errorWait err) = case eq of λ ()
      step-preserves (PS.scope Scope.deliverCancel) s permitted eq valid with Scope.cursor (PS.scopes s) | GP.Pool.parentFork (GP.pool (PS.governor s))
      ... | Scope.closing Scope.governor | just j = case eq of λ ()
      step-preserves (PS.scope Scope.deliverCancel) s permitted eq valid | Scope.closing Scope.governor | nothing with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.deliverCancel) s permitted eq valid | Scope.openScope | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.deliverCancel) s permitted eq valid | Scope.readyToFinish | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.deliverCancel) s permitted eq valid | Scope.finishedScope | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.deliverCancel) s permitted eq valid | Scope.closing Scope.churn | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.deliverCancel) s permitted eq valid | Scope.closing Scope.localRoot | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.deliverCancel) s permitted eq valid | Scope.closing Scope.ledger | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.beginUnwind) s permitted eq valid with Scope.step (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.requestCancel) s permitted eq valid with Scope.step (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.join) s permitted eq valid with Scope.step (PS.governorPoolClosed s) Scope.join (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope Scope.finishClose) s permitted eq valid with Scope.step (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope (Scope.bodyExit actor)) s permitted eq valid with Scope.step (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope (Scope.publishResult actor)) s permitted eq valid with Scope.step (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.scope (Scope.beginFailure actor)) s permitted eq valid with Scope.step (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s)
      ... | nothing = case eq of λ ()
      ... | just next = case just-injective eq of λ { refl → valid }
      step-preserves (PS.beginMonitorClose order) s permitted eq valid with Scope.closed (PS.scopes s)
      ... | false = case eq of λ ()
      ... | true with Pool.step (Pool.beginClose order) (PS.monitorPool s)
      ...   | nothing = case eq of λ ()
      ...   | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves PS.requestMonitorCancel s permitted eq valid with Pool.step Pool.requestCancel (PS.monitorPool s)
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves PS.joinMonitor s permitted eq valid with Pool.step Pool.join (PS.monitorPool s)
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves PS.finishMonitorClose s permitted eq valid with Pool.step Pool.finishClose (PS.monitorPool s)
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves (PS.deregisterMonitor tid) s permitted eq valid with Pool.step (Pool.deregister tid) (PS.monitorPool s)
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves (PS.publishMonitorResult tid) s permitted eq valid with Pool.step (Pool.publishAsyncResult tid) (PS.monitorPool s)
      ... | nothing = case eq of λ ()
      ... | just p′ = case just-injective eq of λ { refl → valid }
      step-preserves (PS.deliverMonitorCancellation err) s permitted eq valid = delivery-preserves false err s eq valid
      step-preserves (PS.deliverBlockedMonitorCancellation err) s permitted eq valid = delivery-preserves true err s eq valid
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid with lookup tid (PS.monitors s)
      ... | nothing = case eq of λ ()
      ... | just t with PS.pc t | PS.interrupted t
      ...   | PS.cancelling | just f with Cancel.pc f
      ...     | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound tid) (PS.monitorPool s)
      ...       | nothing = case eq of λ ()
      ...       | just p′ = case just-injective eq of λ { refl → finish-peer false (PS.peerRef t) s valid }
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | PS.cancelling | just f | Cancel.cleaning active = case eq of λ ()
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | PS.cancelling | just f | Cancel.finished Cancel.cleanupComplete = case eq of λ ()
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | PS.cancelling | just f | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | PS.observing | interrupted = case eq of λ ()
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | PS.normalFinishing | interrupted = case eq of λ ()
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | PS.exited | interrupted = case eq of λ ()
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | (PS.errorWait err) | interrupted = case eq of λ ()
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | (PS.errorFinishing err) | interrupted = case eq of λ ()
      step-preserves (PS.monitorBodyUnwound tid) s permitted eq valid | just t | PS.cancelling | nothing = case eq of λ ()

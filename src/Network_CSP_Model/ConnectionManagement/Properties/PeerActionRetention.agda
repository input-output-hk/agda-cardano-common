{-# OPTIONS --guardedness #-}

-- Initiator peer actions preserve existing IG handles and mux keys.
module ConnectionManagement.Properties.PeerActionRetention where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)
import ConnectionManagement.IGTypes as T
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerAnchors using (anchors-refl; setMux-preserves)
open import ConnectionManagement.Properties.IGTableRetention using (Retains; from-anchors)

-- Transport the IG relation through an exact pair result.
result-retains : ∀ {ig} {pair pair′ : P.Peer × IG.Runtime} → just pair ≡ just pair′ →
  Retains ig (Data.Product.proj₂ pair) → Retains ig (Data.Product.proj₂ pair′)
result-retains {ig} eq = subst (λ pair → Retains ig (Data.Product.proj₂ pair)) (just-injective eq)

-- All non-timeout cases leave IG unchanged; timeout appends shutdown to a
-- looked-up mux while retaining its connection key and every handle lookup.
step-retains : ∀ a p ig s {out} → P.step a p ig s ≡ just out → Retains ig (Data.Product.proj₂ out)
step-retains P.activate p ig s eq with P.status p
... | P.peerWarm = result-retains eq (from-anchors (anchors-refl ig))
... | P.peerCold = case eq of λ ()
... | P.peerCooling = case eq of λ ()
... | P.peerHot = case eq of λ ()
step-retains P.deactivate p ig s eq with P.status p
... | P.peerWarm = result-retains eq (from-anchors (anchors-refl ig))
... | P.peerHot = result-retains eq (from-anchors (anchors-refl ig))
... | P.peerCold = case eq of λ ()
... | P.peerCooling = case eq of λ ()
step-retains P.close p ig s eq = result-retains eq (from-anchors (anchors-refl ig))
step-retains (P.startProtocol t n) p ig s eq with lookup (P.muxRef p) (IG.muxes (IG.execution ig))
... | nothing = case eq of λ ()
... | just m with M.status m
...   | M.ready with P.startRun t n (P.runs p)
...     | nothing = case eq of λ ()
...     | just rs = result-retains eq (from-anchors (anchors-refl ig))
step-retains (P.startProtocol t n) p ig s eq | just m | M.stopping = case eq of λ ()
step-retains (P.startProtocol t n) p ig s eq | just m | M.stopped = case eq of λ ()
step-retains (P.startProtocol t n) p ig s eq | just m | M.failed err = case eq of λ ()
step-retains (P.publishProtocols t) p ig s eq with P.started t (P.runs p)
... | false = case eq of λ ()
... | true = result-retains eq (from-anchors (anchors-refl ig))
step-retains (P.protocolResult n r) p ig s eq with P.finishRun n r (P.runs p)
... | nothing = case eq of λ ()
... | just rs = result-retains eq (from-anchors (anchors-refl ig))
step-retains P.markWarm p ig s eq = result-retains eq (from-anchors (anchors-refl ig))
step-retains P.forkMonitor p ig s eq with P.monitorStarted p
... | true = case eq of λ ()
... | false = result-retains eq (from-anchors (anchors-refl ig))
step-retains (P.markPromoted t) p ig s eq = result-retains eq (from-anchors (anchors-refl ig))
step-retains P.finishDeactivate p ig s eq with P.all T.hot (P.runs p)
... | nothing = case eq of λ ()
... | just (T.errored err) = result-retains eq (from-anchors (anchors-refl ig))
... | just T.clean with P.status p
...   | P.peerCold = result-retains eq (from-anchors (anchors-refl ig))
...   | P.peerCooling = result-retains eq (from-anchors (anchors-refl ig))
...   | P.peerWarm = result-retains eq (from-anchors (anchors-refl ig))
...   | P.peerHot = result-retains eq (from-anchors (anchors-refl ig))
step-retains P.timeoutDeactivate p ig s eq with lookup (P.muxRef p) (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m = result-retains eq (from-anchors (setMux-preserves (P.muxRef p) m _ ig found refl))
step-retains P.timeoutClose p ig s eq = step-retains P.timeoutDeactivate p ig s eq
step-retains P.monitorCooling p ig s eq with P.status p | P.demoted (P.key p) s
... | P.peerCooling | true = result-retains eq (from-anchors (anchors-refl ig))
... | P.peerCold | _ = result-retains eq (from-anchors (anchors-refl ig))
... | P.peerCooling | false = case eq of λ ()
... | P.peerWarm | _ = case eq of λ ()
... | P.peerHot | _ = case eq of λ ()
step-retains P.monitorError p ig s eq = result-retains eq (from-anchors (anchors-refl ig))

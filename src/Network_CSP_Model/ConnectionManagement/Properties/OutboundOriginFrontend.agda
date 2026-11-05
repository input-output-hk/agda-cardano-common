{-# OPTIONS --guardedness #-}

-- Closed frontend observation: selector permission, peer stutters and physical
-- source effects are proved internally, preserving every actual event label.
module ConnectionManagement.Properties.OutboundOriginFrontend where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.IGTypes using (number)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Properties.OutboundOriginPeers as PeerEffects
import ConnectionManagement.Properties.OutboundOriginUpper as Upper
import ConnectionManagement.Properties.OutboundOriginEffect as Effects
import ConnectionManagement.Properties.InboundOriginPlanSafety as Safety
import ConnectionManagement.Properties.OutboundOriginHistory as HistoryModel
import ConnectionManagement.Properties.ServerIGExit as ExitFacts

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 private
  module K = Combined b io using (State; source; server; serverStep; coreStep; peerStep; peerOpen; peerAllowed; rawPeerAllowed; serverAllowed; coreAllowed; coreAction; peers; step; context)
  module T = Combined.Protocols b io capability using (Runtime; Event; Plan; Runs; stop; more; initialize; base; advance; choose; enact; inherit; complete; caller; local; reading; traceFault; deliverTraceFault; birth; front; cacheResult; latest; calls; owner; descriptor; peerRef; handleRef; mux)
  module E = Exit b using (source; step; initial)
  module Server = Upper.IGExit b using (effect)
  module Peers = PeerEffects io using (module PS; module GP; Allowed; effect)
  module PS = Peers.PS
  module GP = Peers.GP
  module Safe = Safety.Frontend b io capability using (SafePlan; choose-safe)
  module C = Context io using (SubContext; subsystem)
 source : T.Runtime → O.Configuration
 source state = K.source (T.base state)
 core : T.Runtime → M.Configuration
 core state = O.core (source state)
 shared : T.Runtime → S.State
 shared state = M.world (core state)

 -- A permitted peer action cannot use the raw core route.
 peer-permission : ∀ action s → K.peerAllowed action s ≡ true → Peers.Allowed action
 peer-permission (PS.run (GP.run (Sub.core action))) s ()
 peer-permission (PS.run (GP.run Sub.publishPublicState)) s actual = tt
 peer-permission (PS.run (GP.run (Sub.sampleTime _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.applyAt _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.setTargets _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.selectMonitor _))) s actual = tt
 peer-permission (PS.run (GP.run Sub.selectCompletion)) s actual = tt
 peer-permission (PS.run (GP.run Sub.selectTargets)) s actual = tt
 peer-permission (PS.run (GP.run Sub.selectWakeup)) s actual = tt
 peer-permission (PS.run (GP.run Sub.registerWakeup)) s actual = tt
 peer-permission (PS.run (GP.run Sub.expireWakeup)) s actual = tt
 peer-permission (PS.run (GP.run Sub.cancelWakeup)) s actual = tt
 peer-permission (PS.run (GP.run Sub.publishCounters)) s actual = tt
 peer-permission (PS.run (GP.run Sub.traceSelection)) s actual = tt
 peer-permission (PS.run (GP.run (Sub.selectPolicy _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.forkJob _ _ _))) s actual = tt
 peer-permission (PS.run (GP.run Sub.registerJob)) s actual = tt
 peer-permission (PS.run (GP.run Sub.finishLaunch)) s actual = tt
 peer-permission (PS.run (GP.run (Sub.jobStep _ _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.enqueueCompletion _ _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.deregisterJob _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.protocolResult _ _ _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.publishInitiatorResult _ _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.pollPeer _ _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.monitorStep _ _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.monitorFinished _))) s actual = tt
 peer-permission (PS.run (GP.run (Sub.observeInitiatorFailure _))) s actual = tt
 peer-permission (PS.run (GP.handoff _)) s actual = tt
 peer-permission (PS.run (GP.beginClose _)) s actual = tt
 peer-permission (PS.run GP.requestCancel) s actual = tt
 peer-permission (PS.run GP.join) s actual = tt
 peer-permission (PS.run GP.finishClose) s actual = tt
 peer-permission (PS.run (GP.deliverCancellation _)) s actual = tt
 peer-permission (PS.run (GP.deliverOpenCancellation _)) s actual = tt
 peer-permission (PS.run (GP.cleanup _ _)) s actual = tt
 peer-permission (PS.run (GP.bodyUnwound _)) s actual = tt
 peer-permission (PS.run (GP.recoverCloseFailure _)) s actual = tt
 peer-permission (PS.run (GP.deregisterCancelled _)) s actual = tt
 peer-permission (PS.run (GP.publishAsyncResult _)) s actual = tt
 peer-permission (PS.forkMonitor _ _) s actual = tt
 peer-permission (PS.registerMonitor _) s actual = tt
 peer-permission (PS.returnEstablishment _) s actual = tt
 peer-permission (PS.finishEstablishment _) s actual = tt
 peer-permission (PS.monitorException _ _) s actual = tt
 peer-permission (PS.commitMonitorError _) s actual = tt
 peer-permission (PS.finishMonitorError _) s actual = tt
 peer-permission (PS.finishMonitor _) s actual = tt
 peer-permission (PS.scope _) s actual = tt
 peer-permission (PS.beginMonitorClose _) s actual = tt
 peer-permission PS.requestMonitorCancel s actual = tt
 peer-permission PS.joinMonitor s actual = tt
 peer-permission PS.finishMonitorClose s actual = tt
 peer-permission (PS.deliverMonitorCancellation _) s actual = tt
 peer-permission (PS.deliverBlockedMonitorCancellation _) s actual = tt
 peer-permission (PS.monitorBodyUnwound _) s actual = tt
 peer-permission (PS.deregisterMonitor _) s actual = tt
 peer-permission (PS.publishMonitorResult _) s actual = tt

 -- The shared dispatcher supplies either a real lower effect or a permitted
 -- peer stutter; each branch retains its exact current source endpoints.
 shared-effect : ∀ action before {after} → K.step action before ≡ just after →
   Effects.Effect (K.source before) (K.source after)
 shared-effect (K.serverStep action) before actual with K.serverAllowed action before
 ... | false = case actual of λ ()
 ... | true with E.step action (K.server before) in lower
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → Server.effect action (K.server before) lower }
 shared-effect (K.coreStep action) before actual with K.coreAllowed action before
 ... | false = case actual of λ ()
 ... | true with E.step (K.coreAction action) (K.server before) in lower
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → Server.effect (K.coreAction action) (K.server before) lower }
 shared-effect (K.peerStep action) before actual with K.peerOpen before | K.peerAllowed action before in allowed
 ... | false | _ = case actual of λ ()
 ... | true | false = case actual of λ ()
 ... | true | true with PS.step action (K.peers before) in lower
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → Peers.effect action (K.peers before) (peer-permission action before allowed) lower }

 -- Cache publication changes peer metadata while retaining the exact CM core.
 cache-source : ∀ rid capturedCall result front before → K.source (T.cacheResult rid capturedCall result front before) ≡ K.source before
 cache-source rid capturedCall result front before with T.latest (T.owner capturedCall) (number (T.descriptor capturedCall)) (T.calls front)
 ... | nothing = refl
 ... | just (current , _) with current ≟ rid
 ...   | no _ = refl
 ...   | yes _ with lookup (T.peerRef capturedCall) (C.SubContext.peers (C.subsystem (K.context before)))
 ...     | nothing = refl
 ...     | just peer with Peer.handleRef peer ≟ T.handleRef capturedCall | Peer.muxRef peer ≟ T.mux capturedCall
 ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor capturedCall)) result (Peer.runs peer)
 ...         | nothing = refl
 ...         | just runs = refl
 cache-source rid capturedCall result front before | just (current , _) | yes _ | just peer | no _ | _ = refl
 cache-source rid capturedCall result front before | just (current , _) | yes _ | just peer | yes _ | no _ = refl

 -- Permission for caller plans follows from the actual selector, rather than
 -- from an assumption that arbitrary manually built Plan values are safe.
 enact-effect : ∀ plan before {after} → Safe.SafePlan plan → T.enact plan before ≡ just after →
   Effects.Effect (source before) (source after)
 enact-effect (T.inherit action front) before safe actual with K.step action (T.base before) in lower
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → shared-effect action (T.base before) lower }
 enact-effect (T.caller action front) before (job , refl) actual with PS.step (PS.run (GP.run (Sub.jobStep job J.runNext))) (K.peers (T.base before)) in lower
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → Peers.effect (PS.run (GP.run (Sub.jobStep job J.runNext))) (K.peers (T.base before)) tt lower }
 enact-effect (T.local front) before safe actual = case just-injective actual of λ { refl → Effects.same refl }
 enact-effect (T.reading reading) before safe actual = case just-injective actual of λ { refl → Effects.same refl }
 enact-effect (T.traceFault worker rid result faults) before safe actual = case just-injective actual of λ { refl → Effects.same refl }
 enact-effect (T.deliverTraceFault worker rid result faults coordinator) before safe actual = case just-injective actual of λ { refl → Effects.same refl }
 enact-effect (T.birth worker capturedFrame pool job rid capturedCall front) before safe actual = case just-injective actual of λ { refl → Effects.same refl }
 enact-effect (T.complete action rid capturedCall result) before safe actual with K.step action (T.base before) in lower
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → Effects.reframe refl
   (cache-source rid capturedCall result (T.front before) next) (shared-effect action (T.base before) lower) }

 -- Every enabled frontend event carries a proved atomic source classification.
 observe : ∀ action before {after} → T.advance action before ≡ just after → Effects.Effect (source before) (source after)
 observe action before actual with T.choose action before in chosen
 ... | nothing = case actual of λ ()
 ... | just plan = enact-effect plan before (Safe.choose-safe action before plan chosen) actual

 -- Successful initialization retains the exact explicitly empty acquisition
 -- runtime; preloaded acquiring frames are outside this justified profile.
 initialized-source : ∀ initialSource governor {start} → T.initialize initialSource governor ≡ just start → source start ≡ initialSource
 initialized-source initialSource governor actual with E.initial initialSource in lower
 ... | nothing = case actual of λ ()
 ... | just server = case just-injective actual of λ { refl → ExitFacts.initial-source b initialSource lower }
 initialized-empty : ∀ initialCore governor {start} → T.initialize (O.initial initialCore) governor ≡ just start → O.acquiring (source start) ≡ []
 initialized-empty initialCore governor actual = trans
   (cong O.acquiring (initialized-source (O.initial initialCore) governor actual)) refl

 -- No physical birth inversion is imported into this generic prefix observer.
 module History = HistoryModel.Engine T.Runtime T.Event T.advance source observe
 to-runs : ∀ {before events after} → T.Runs before events after → History.Runs before events after
 to-runs T.stop = History.done
 to-runs (T.more actual path) = History.next actual (to-runs path)
 from-runs : ∀ {before events after} → History.Runs before events after → T.Runs before events after
 from-runs History.done = T.stop
 from-runs (History.next actual path) = T.more actual (from-runs path)

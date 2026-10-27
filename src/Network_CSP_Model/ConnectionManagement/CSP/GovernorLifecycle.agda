{-# OPTIONS --guardedness #-}

-- Integrated ordinary-peer OG establishment, activation, demotion and close.
module ConnectionManagement.CSP.GovernorLifecycle where

open import Data.Bool using (false; true)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Store using (put)
import ConnectionManagement.CSP.OutboundAdmission as O
import ConnectionManagement.Rules.MuxRuntime as M
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.IGTypes
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
open import ConnectionManagement.Subsystem
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.CSP.IGRegistration as Fixture
import ConnectionManagement.CSP.Fixtures as F
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.CSP.Subsystem using (Process; trace-intro; Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

peerAddr : PeerAddr
peerAddr = remote key₀
caller child : WorkerId
caller = ident 10
child = ident 11
settings : G.State
settings = G.governorState (G.targets 1 1 1)
  ((peerAddr , G.known 0 0 nothing false false) ∷ []) [] [] [] [] [] [] []
c₀ : Configuration
c₀ = initial (CM.initial F.start) settings

-- Expected snapshots are explicit; no full-schedule replay occurs here.
cmAfter : CM.Action → CM.Configuration → CM.Configuration
cmAfter a c with CM.advance a c
... | nothing = c
... | just c′ = c′
a1 : Action
a1 = publishPublicState
c1 : Configuration
c1 = configuration (J.world (CM.initial F.start) []) (settings) (settings) (sampleInputs) 0 (G.targets 1 1 1)
  [] [] [] [] 0 0 5 60 nothing false

step1 : advance a1 c₀ ≡ just c1
step1 = refl

a2 : Action
a2 = sampleTime 0
c2 : Configuration
c2 = configuration (J.world (CM.initial F.start) []) (settings) (settings) (prepareWait) 0 (G.targets 1 1 1)
  [] [] [] [] 0 0 5 60 nothing false

step2 : advance a2 c1 ≡ just c2
step2 = refl

a3 : Action
a3 = registerWakeup
c3 : Configuration
c3 = configuration (J.world (CM.initial F.start) []) (settings) (settings) (selecting) 0 (G.targets 1 1 1)
  [] [] [] [] 0 0 5 60 nothing false

step3 : advance a3 c2 ≡ just c3
step3 = refl

a4 : Action
a4 = selectPolicy (peerAddr ∷ [])
c4 : Configuration
c4 = configuration (J.world (CM.initial F.start) []) (settings) (settings) (apply (policy (G.decision (G.mark G.establish (peerAddr ∷ []) (settings)) (G.job G.establish peerAddr nothing ∷ [])))) 0 (G.targets 1 1 1)
  [] [] [] [] 0 0 5 60 nothing false

step4 : advance a4 c3 ≡ just c4
step4 = refl

g1 : G.State
g1 = G.mark G.establish (peerAddr ∷ []) (settings)

a5 : Action
a5 = applyAt 0
c5 : Configuration
c5 = configuration (J.world (CM.initial F.start) []) (g1) (settings) (publishView (G.job G.establish peerAddr nothing ∷ [])) 0 (G.targets 1 1 1)
  [] [] [] [] 0 0 5 60 nothing false

step5 : advance a5 c4 ≡ just c5
step5 = refl

a6 : Action
a6 = publishCounters
c6 : Configuration
c6 = configuration (J.world (CM.initial F.start) []) (g1) (settings) (traceDecision (G.job G.establish peerAddr nothing ∷ [])) 0 (G.targets 1 1 1)
  [] [] [] [] 0 0 5 60 nothing false

step6 : advance a6 c5 ≡ just c6
step6 = refl

a7 : Action
a7 = traceSelection
c7 : Configuration
c7 = configuration (J.world (CM.initial F.start) []) (g1) (settings) (launch (G.job G.establish peerAddr nothing ∷ [])) 0 (G.targets 1 1 1)
  [] [] [] [] 0 0 5 60 nothing false

step7 : advance a7 c6 ≡ just c7
step7 = refl

a8 : Action
a8 = forkJob caller child (ident 10)
c8 : Configuration
c8 = configuration (J.world (CM.initial F.start) []) (g1) (settings) (register (ident 0) []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.begin)) false false) ∷ []) [] [] [] 1 1 5 60 nothing false

step8 : advance a8 c7 ≡ just c8
step8 = refl

a9 : Action
a9 = registerJob
c9 : Configuration
c9 = configuration (J.world (CM.initial F.start) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.begin)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step9 : advance a9 c8 ≡ just c9
step9 = refl

a10 : Action
a10 = jobStep (ident 0) J.enter
c10 : Configuration
c10 = configuration (J.world (O.begun) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step10 : advance a10 c9 ≡ just c10
step10 = refl

a11 : Action
a11 = core (CM.acquire caller (A.select nothing))
c11 : Configuration
c11 = configuration (J.world (O.at (A.count (A.allocatePromise (ident 0))) O.reserved) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step11 : advance a11 c10 ≡ just c11
step11 = refl

a12 : Action
a12 = core (CM.acquire caller (A.readCounters))
c12 : Configuration
c12 = configuration (J.world (O.at (A.allocatePromise (ident 0)) O.reserved) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step12 : advance a12 c11 ≡ just c12
step12 = refl

a13 : Action
a13 = core (CM.acquire caller (A.newPromise))
c13 : Configuration
c13 = configuration (J.world (O.at (A.openSocket (ident 0) (ident 0)) O.promised) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step13 : advance a13 c12 ≡ just c13
step13 = refl

a14 : Action
a14 = core (CM.acquire caller (A.openOK))
c14 : Configuration
c14 = configuration (J.world (O.at (A.configureSocket (ident 0) (ident 0)) O.opened) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step14 : advance a14 c13 ≡ just c14
step14 = refl

a15 : Action
a15 = core (CM.acquire caller (A.configureOK))
c15 : Configuration
c15 = configuration (J.world (O.at (A.connectSocket (ident 0) (ident 0)) O.opened) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step15 : advance a15 c14 ≡ just c15
step15 = refl

a16 : Action
a16 = core (CM.acquire caller (A.connectOK))
c16 : Configuration
c16 = configuration (J.world (O.at (A.localAddress (ident 0) (ident 0)) O.opened) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step16 : advance a16 c15 ≡ just c16
step16 = refl

a17 : Action
a17 = core (CM.acquire caller (A.gotLocal (local key₀)))
c17 : Configuration
c17 = configuration (J.world (O.at (A.updateAddress (ident 0) (ident 0) key₀) O.opened) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step17 : advance a17 c16 ≡ just c17
step17 = refl

a18 : Action
a18 = core (CM.acquire caller (A.updateLocalAddress))
c18 : Configuration
c18 = configuration (J.world (O.at (A.forkHandler (ident 0) (ident 0) key₀) O.addressed) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step18 : advance a18 c17 ≡ just c18
step18 = refl

a19 : Action
a19 = core (CM.acquire caller (A.forkOK))
c19 : Configuration
c19 = configuration (J.world (O.at (A.connectedCommit (ident 0) (ident 0) key₀) O.forked) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step19 : advance a19 c18 ≡ just c19
step19 = refl

a20 : Action
a20 = core (CM.acquire caller (A.commitConnected))
c20 : Configuration
c20 = configuration (J.world (O.at (A.count O.wait) O.connected) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step20 : advance a20 c19 ≡ just c20
step20 = refl

a21 : Action
a21 = core (CM.acquire caller (A.readCounters))
c21 : Configuration
c21 = configuration (J.world (O.at O.wait O.connected) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step21 : advance a21 c20 ≡ just c21
step21 = refl

a22 : Action
a22 = core (CM.inbound (Inbound.igStep (IG.installHandle (ident 0) Fixture.mid key₀ (Fixture.proto ∷ []) duplex)))
c22 : Configuration
c22 = configuration (J.world (O.withHandle (O.at O.wait O.connected)) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step22 : advance a22 c21 ≡ just c22
step22 = refl

a23 : Action
a23 = core (CM.inbound (Inbound.handlerPublication child (S.negotiated (ident 0) duplex) Inbound.resultWritten))
c23 : Configuration
c23 = configuration (J.world (O.withHandle (O.at O.wait O.published)) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step23 : advance a23 c22 ≡ just c23
step23 = refl

a24 : Action
a24 = core (CM.acquire caller A.readResult)
c24 : Configuration
c24 = configuration (J.world (O.withHandle (O.at (A.commitResult (ident 0) key₀ (S.negotiated (ident 0) duplex)) O.published)) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step24 : advance a24 c23 ≡ just c24
step24 = refl

a25 : Action
a25 = core (CM.acquire caller A.commitHandshake)
c25 : Configuration
c25 = configuration (J.world (O.withHandle (O.at (A.count (A.complete (C.connected key₀ duplex (ident 0)))) O.negotiated)) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step25 : advance a25 c24 ≡ just c25
step25 = refl

a26 : Action
a26 = core (CM.acquire caller A.readCounters)
c26 : Configuration
c26 = configuration (J.world (O.withHandle (O.at (A.complete (C.connected key₀ duplex (ident 0))) O.negotiated)) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step26 : advance a26 c25 ≡ just c26
step26 = refl

a27 : Action
a27 = core (CM.acquire caller A.returnResult)
c27 : Configuration
c27 = configuration (J.world (O.returned) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step27 : advance a27 c26 ≡ just c27
step27 = refl

ig2 : CM.Configuration
ig2 = cmAfter (CM.inbound (Inbound.igStep (IG.captureTime 0))) (O.returned)

a28 : Action
a28 = core (CM.inbound (Inbound.igStep (IG.captureTime 0)))
c28 : Configuration
c28 = configuration (J.world (ig2) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step28 : advance a28 c27 ≡ just c28
step28 = refl

ig3 : CM.Configuration
ig3 = cmAfter (CM.inbound (Inbound.igStep (IG.registerInactivity))) (ig2)

a29 : Action
a29 = core (CM.inbound (Inbound.igStep (IG.registerInactivity)))
c29 : Configuration
c29 = configuration (J.world (ig3) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step29 : advance a29 c28 ≡ just c29
step29 = refl

ig4 : CM.Configuration
ig4 = cmAfter (CM.inbound (Inbound.igStep (IG.selectBatch))) (ig3)

a30 : Action
a30 = core (CM.inbound (Inbound.igStep (IG.selectBatch)))
c30 : Configuration
c30 = configuration (J.world (ig4) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step30 : advance a30 c29 ≡ just c30
step30 = refl

ig5 : CM.Configuration
ig5 = cmAfter (CM.inbound (Inbound.igStep (IG.readEvent))) (ig4)

a31 : Action
a31 = core (CM.inbound (Inbound.igStep (IG.readEvent)))
c31 : Configuration
c31 = configuration (J.world (ig5) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step31 : advance a31 c30 ≡ just c31
step31 = refl

ig6 : CM.Configuration
ig6 = cmAfter (CM.inbound (Inbound.igStep (IG.registerIdleTimer))) (ig5)

a32 : Action
a32 = core (CM.inbound (Inbound.igStep (IG.registerIdleTimer)))
c32 : Configuration
c32 = configuration (J.world (ig6) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step32 : advance a32 c31 ≡ just c32
step32 = refl

ig7 : CM.Configuration
ig7 = cmAfter (CM.inbound (Inbound.igStep (IG.runResponders))) (ig6)

a33 : Action
a33 = core (CM.inbound (Inbound.igStep (IG.runResponders)))
c33 : Configuration
c33 = configuration (J.world (ig7) []) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.awaitAcquire)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step33 : advance a33 c32 ≡ just c33
step33 = refl

p8 : P.Peer
p8 = P.initialPeer key₀ (ident 0) (M.handleState Fixture.mid (Fixture.proto ∷ []) duplex)

a34 : Action
a34 = jobStep (ident 0) J.collectAcquire
c34 : Configuration
c34 = configuration (J.world (ig7) ((ident 0 , p8) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.startBundle ConnectionManagement.IGTypes.warm [])) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step34 : advance a34 c33 ≡ just c34
step34 = refl

a35 : Action
a35 = jobStep (ident 0) J.runNext
c35 : Configuration
c35 = configuration (J.world (ig7) ((ident 0 , p8) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.publishBundle ConnectionManagement.IGTypes.warm)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step35 : advance a35 c34 ≡ just c35
step35 = refl

a36 : Action
a36 = jobStep (ident 0) J.publishStarted
c36 : Configuration
c36 = configuration (J.world (ig7) ((ident 0 , p8) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.startBundle ConnectionManagement.IGTypes.established [])) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step36 : advance a36 c35 ≡ just c36
step36 = refl

a37 : Action
a37 = jobStep (ident 0) J.runNext
c37 : Configuration
c37 = configuration (J.world (ig7) ((ident 0 , p8) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.publishBundle ConnectionManagement.IGTypes.established)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step37 : advance a37 c36 ≡ just c37
step37 = refl

a38 : Action
a38 = jobStep (ident 0) J.publishStarted
c38 : Configuration
c38 = configuration (J.world (ig7) ((ident 0 , p8) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.markWarm)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step38 : advance a38 c37 ≡ just c38
step38 = refl

p9 : P.Peer
p9 = record p8 { status = P.peerWarm }

a39 : Action
a39 = jobStep (ident 0) J.markEstablished
c39 : Configuration
c39 = configuration (J.world (ig7) ((ident 0 , p9) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.forkMonitor)) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step39 : advance a39 c38 ≡ just c39
step39 = refl

p10 : P.Peer
p10 = record p9 { monitorStarted = true }

a40 : Action
a40 = jobStep (ident 0) J.launchMonitor
c40 : Configuration
c40 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) false false) ∷ []) (ident 0 ∷ []) [] [] 1 1 5 60 nothing false

step40 : advance a40 c39 ≡ just c40
step40 = refl

a41 : Action
a41 = enqueueCompletion (ident 0) 0
c41 : Configuration
c41 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true false) ∷ []) (ident 0 ∷ []) (G.completion (G.job G.establish peerAddr nothing) (G.establishedOK (ident 0)) 0 ∷ []) [] 1 1 5 60 nothing false

step41 : advance a41 c40 ≡ just c41
step41 = refl

a42 : Action
a42 = deregisterJob (ident 0)
c42 : Configuration
c42 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g1) (settings) (launch []) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] (G.completion (G.job G.establish peerAddr nothing) (G.establishedOK (ident 0)) 0 ∷ []) [] 1 1 5 60 nothing false

step42 : advance a42 c41 ≡ just c42
step42 = refl

a43 : Action
a43 = finishLaunch
c43 : Configuration
c43 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g1) (settings) (publishPublic) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] (G.completion (G.job G.establish peerAddr nothing) (G.establishedOK (ident 0)) 0 ∷ []) [] 1 1 5 60 nothing false

step43 : advance a43 c42 ≡ just c43
step43 = refl

a44 : Action
a44 = publishPublicState
c44 : Configuration
c44 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g1) (g1) (sampleInputs) 0 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] (G.completion (G.job G.establish peerAddr nothing) (G.establishedOK (ident 0)) 0 ∷ []) [] 1 1 5 60 nothing false

step44 : advance a44 c43 ≡ just c44
step44 = refl

a45 : Action
a45 = sampleTime 1
c45 : Configuration
c45 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g1) (g1) (prepareWait) 1 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] (G.completion (G.job G.establish peerAddr nothing) (G.establishedOK (ident 0)) 0 ∷ []) [] 1 1 5 60 nothing false

step45 : advance a45 c44 ≡ just c45
step45 = refl

a46 : Action
a46 = registerWakeup
c46 : Configuration
c46 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g1) (g1) (selecting) 1 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] (G.completion (G.job G.establish peerAddr nothing) (G.establishedOK (ident 0)) 0 ∷ []) [] 1 1 5 60 nothing false

step46 : advance a46 c45 ≡ just c46
step46 = refl

a47 : Action
a47 = selectCompletion
c47 : Configuration
c47 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g1) (g1) (apply (completion (G.completion (G.job G.establish peerAddr nothing) (G.establishedOK (ident 0)) 0))) 1 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step47 : advance a47 c46 ≡ just c47
step47 = refl

g11 : G.State
g11 = G.complete 5 60 1 (G.completion (G.job G.establish peerAddr nothing) (G.establishedOK (ident 0)) 0) (g1)

a48 : Action
a48 = applyAt 1
c48 : Configuration
c48 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g11) (g1) (publishView []) 1 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step48 : advance a48 c47 ≡ just c48
step48 = refl

a49 : Action
a49 = publishCounters
c49 : Configuration
c49 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g11) (g1) (traceDecision []) 1 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step49 : advance a49 c48 ≡ just c49
step49 = refl

a50 : Action
a50 = traceSelection
c50 : Configuration
c50 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g11) (g1) (launch []) 1 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step50 : advance a50 c49 ≡ just c50
step50 = refl

a51 : Action
a51 = finishLaunch
c51 : Configuration
c51 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g11) (g1) (publishPublic) 1 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step51 : advance a51 c50 ≡ just c51
step51 = refl

a52 : Action
a52 = publishPublicState
c52 : Configuration
c52 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g11) (g11) (sampleInputs) 1 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step52 : advance a52 c51 ≡ just c52
step52 = refl

a53 : Action
a53 = sampleTime 2
c53 : Configuration
c53 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g11) (g11) (prepareWait) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step53 : advance a53 c52 ≡ just c53
step53 = refl

a54 : Action
a54 = registerWakeup
c54 : Configuration
c54 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g11) (g11) (selecting) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step54 : advance a54 c53 ≡ just c54
step54 = refl

a55 : Action
a55 = selectPolicy (peerAddr ∷ [])
c55 : Configuration
c55 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g11) (g11) (apply (policy (G.decision (G.mark G.activate (peerAddr ∷ []) (g11)) (G.job G.activate peerAddr (just (ident 0)) ∷ [])))) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step55 : advance a55 c54 ≡ just c55
step55 = refl

g12 : G.State
g12 = G.mark G.activate (peerAddr ∷ []) (g11)

a56 : Action
a56 = applyAt 2
c56 : Configuration
c56 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g12) (g11) (publishView (G.job G.activate peerAddr (just (ident 0)) ∷ [])) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step56 : advance a56 c55 ≡ just c56
step56 = refl

a57 : Action
a57 = publishCounters
c57 : Configuration
c57 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g12) (g11) (traceDecision (G.job G.activate peerAddr (just (ident 0)) ∷ [])) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step57 : advance a57 c56 ≡ just c57
step57 = refl

a58 : Action
a58 = traceSelection
c58 : Configuration
c58 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g12) (g11) (launch (G.job G.activate peerAddr (just (ident 0)) ∷ [])) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ []) [] [] [] 1 1 5 60 nothing false

step58 : advance a58 c57 ≡ just c58
step58 = refl

a59 : Action
a59 = forkJob (ident 12) (ident 13) (ident 12)
c59 : Configuration
c59 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g12) (g11) (register (ident 1) []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.begin)) false false) ∷ []) [] [] [] 2 1 5 60 nothing false

step59 : advance a59 c58 ≡ just c59
step59 = refl

a60 : Action
a60 = registerJob
c60 : Configuration
c60 = configuration (J.world (ig7) ((ident 0 , p10) ∷ [])) (g12) (g11) (launch []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.begin)) false false) ∷ []) (ident 1 ∷ []) [] [] 2 1 5 60 nothing false

step60 : advance a60 c59 ≡ just c60
step60 = refl

p13 : P.Peer
p13 = record p10 { status = P.peerHot; hotControl = P.continue; warmControl = P.quiesce }

a61 : Action
a61 = jobStep (ident 1) J.enter
c61 : Configuration
c61 = configuration (J.world (ig7) ((ident 0 , p13) ∷ [])) (g12) (g11) (launch []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.startBundle ConnectionManagement.IGTypes.hot (1 ∷ []))) false false) ∷ []) (ident 1 ∷ []) [] [] 2 1 5 60 nothing false

step61 : advance a61 c60 ≡ just c61
step61 = refl

p14 : P.Peer
p14 = record p13 { runs = P.protocolRun Fixture.proto P.running P.notStarted ∷ [] }

a62 : Action
a62 = jobStep (ident 1) J.runNext
c62 : Configuration
c62 = configuration (J.world (ig7) ((ident 0 , p14) ∷ [])) (g12) (g11) (launch []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.startBundle ConnectionManagement.IGTypes.hot [])) false false) ∷ []) (ident 1 ∷ []) [] [] 2 1 5 60 nothing false

step62 : advance a62 c61 ≡ just c62
step62 = refl

a63 : Action
a63 = jobStep (ident 1) J.runNext
c63 : Configuration
c63 = configuration (J.world (ig7) ((ident 0 , p14) ∷ [])) (g12) (g11) (launch []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.publishBundle ConnectionManagement.IGTypes.hot)) false false) ∷ []) (ident 1 ∷ []) [] [] 2 1 5 60 nothing false

step63 : advance a63 c62 ≡ just c63
step63 = refl

p15 : P.Peer
p15 = record p14 { runs = P.protocolRun Fixture.proto P.running P.running ∷ [] }

a64 : Action
a64 = jobStep (ident 1) J.publishStarted
c64 : Configuration
c64 = configuration (J.world (ig7) ((ident 0 , p15) ∷ [])) (g12) (g11) (launch []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.finishActivation)) false false) ∷ []) (ident 1 ∷ []) [] [] 2 1 5 60 nothing false

step64 : advance a64 c63 ≡ just c64
step64 = refl

promotedPeer : P.Peer
promotedPeer = record p15 { promotedAt = just 2 }

a65 : Action
a65 = jobStep (ident 1) (J.finishHotAt 2)
c65 : Configuration
c65 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g12) (g11) (launch []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) false false) ∷ []) (ident 1 ∷ []) [] [] 2 1 5 60 nothing false

step65 : advance a65 c64 ≡ just c65
step65 = refl

a66 : Action
a66 = enqueueCompletion (ident 1) 0
c66 : Configuration
c66 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g12) (g11) (launch []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true false) ∷ []) (ident 1 ∷ []) (G.completion (G.job G.activate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 2 1 5 60 nothing false

step66 : advance a66 c65 ≡ just c66
step66 = refl

a67 : Action
a67 = deregisterJob (ident 1)
c67 : Configuration
c67 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g12) (g11) (launch []) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.activate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 2 1 5 60 nothing false

step67 : advance a67 c66 ≡ just c67
step67 = refl

a68 : Action
a68 = finishLaunch
c68 : Configuration
c68 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g12) (g11) (publishPublic) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.activate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 2 1 5 60 nothing false

step68 : advance a68 c67 ≡ just c68
step68 = refl

a69 : Action
a69 = publishPublicState
c69 : Configuration
c69 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g12) (g12) (sampleInputs) 2 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.activate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 2 1 5 60 nothing false

step69 : advance a69 c68 ≡ just c69
step69 = refl

a70 : Action
a70 = sampleTime 3
c70 : Configuration
c70 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g12) (g12) (prepareWait) 3 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.activate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 2 1 5 60 nothing false

step70 : advance a70 c69 ≡ just c70
step70 = refl

a71 : Action
a71 = registerWakeup
c71 : Configuration
c71 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g12) (g12) (selecting) 3 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.activate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 2 1 5 60 nothing false

step71 : advance a71 c70 ≡ just c71
step71 = refl

a72 : Action
a72 = selectCompletion
c72 : Configuration
c72 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g12) (g12) (apply (completion (G.completion (G.job G.activate peerAddr (just (ident 0))) (G.succeeded) 0))) 3 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step72 : advance a72 c71 ≡ just c72
step72 = refl

g16 : G.State
g16 = G.complete 5 60 3 (G.completion (G.job G.activate peerAddr (just (ident 0))) (G.succeeded) 0) (g12)

a73 : Action
a73 = applyAt 3
c73 : Configuration
c73 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g12) (publishView []) 3 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step73 : advance a73 c72 ≡ just c73
step73 = refl

a74 : Action
a74 = publishCounters
c74 : Configuration
c74 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g12) (traceDecision []) 3 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step74 : advance a74 c73 ≡ just c74
step74 = refl

a75 : Action
a75 = traceSelection
c75 : Configuration
c75 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g12) (launch []) 3 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step75 : advance a75 c74 ≡ just c75
step75 = refl

a76 : Action
a76 = finishLaunch
c76 : Configuration
c76 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g12) (publishPublic) 3 (G.targets 1 1 1)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step76 : advance a76 c75 ≡ just c76
step76 = refl

a77 : Action
a77 = setTargets (G.targets 1 1 0)
c77 : Configuration
c77 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g12) (publishPublic) 3 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step77 : advance a77 c76 ≡ just c77
step77 = refl

a78 : Action
a78 = publishPublicState
c78 : Configuration
c78 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g16) (sampleInputs) 3 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step78 : advance a78 c77 ≡ just c78
step78 = refl

a79 : Action
a79 = sampleTime 4
c79 : Configuration
c79 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g16) (prepareWait) 4 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step79 : advance a79 c78 ≡ just c79
step79 = refl

a80 : Action
a80 = registerWakeup
c80 : Configuration
c80 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g16) (selecting) 4 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step80 : advance a80 c79 ≡ just c80
step80 = refl

a81 : Action
a81 = selectTargets
c81 : Configuration
c81 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g16) (g16) (apply (targets (G.targets 1 1 0))) 4 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step81 : advance a81 c80 ≡ just c81
step81 = refl

g17 : G.State
g17 = record (g16) { target = G.targets 1 1 0 }

a82 : Action
a82 = applyAt 4
c82 : Configuration
c82 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g17) (g16) (publishView []) 4 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step82 : advance a82 c81 ≡ just c82
step82 = refl

a83 : Action
a83 = publishCounters
c83 : Configuration
c83 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g17) (g16) (traceDecision []) 4 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step83 : advance a83 c82 ≡ just c83
step83 = refl

a84 : Action
a84 = traceSelection
c84 : Configuration
c84 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g17) (g16) (launch []) 4 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step84 : advance a84 c83 ≡ just c84
step84 = refl

a85 : Action
a85 = finishLaunch
c85 : Configuration
c85 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g17) (g16) (publishPublic) 4 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step85 : advance a85 c84 ≡ just c85
step85 = refl

a86 : Action
a86 = publishPublicState
c86 : Configuration
c86 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g17) (g17) (sampleInputs) 4 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step86 : advance a86 c85 ≡ just c86
step86 = refl

a87 : Action
a87 = sampleTime 5
c87 : Configuration
c87 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g17) (g17) (prepareWait) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step87 : advance a87 c86 ≡ just c87
step87 = refl

a88 : Action
a88 = registerWakeup
c88 : Configuration
c88 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g17) (g17) (selecting) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step88 : advance a88 c87 ≡ just c88
step88 = refl

a89 : Action
a89 = selectPolicy (peerAddr ∷ [])
c89 : Configuration
c89 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g17) (g17) (apply (policy (G.decision (G.mark G.deactivate (peerAddr ∷ []) (g17)) (G.job G.deactivate peerAddr (just (ident 0)) ∷ [])))) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step89 : advance a89 c88 ≡ just c89
step89 = refl

g18 : G.State
g18 = G.mark G.deactivate (peerAddr ∷ []) (g17)

a90 : Action
a90 = applyAt 5
c90 : Configuration
c90 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g18) (g17) (publishView (G.job G.deactivate peerAddr (just (ident 0)) ∷ [])) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step90 : advance a90 c89 ≡ just c90
step90 = refl

a91 : Action
a91 = publishCounters
c91 : Configuration
c91 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g18) (g17) (traceDecision (G.job G.deactivate peerAddr (just (ident 0)) ∷ [])) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step91 : advance a91 c90 ≡ just c91
step91 = refl

a92 : Action
a92 = traceSelection
c92 : Configuration
c92 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g18) (g17) (launch (G.job G.deactivate peerAddr (just (ident 0)) ∷ [])) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 2 1 5 60 nothing false

step92 : advance a92 c91 ≡ just c92
step92 = refl

a93 : Action
a93 = forkJob (ident 14) (ident 15) (ident 14)
c93 : Configuration
c93 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g18) (g17) (register (ident 2) []) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.begin)) false false) ∷ []) [] [] [] 3 1 5 60 nothing false

step93 : advance a93 c92 ≡ just c93
step93 = refl

a94 : Action
a94 = registerJob
c94 : Configuration
c94 = configuration (J.world (ig7) ((ident 0 , promotedPeer) ∷ [])) (g18) (g17) (launch []) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.begin)) false false) ∷ []) (ident 2 ∷ []) [] [] 3 1 5 60 nothing false

step94 : advance a94 c93 ≡ just c94
step94 = refl

p19 : P.Peer
p19 = record promotedPeer { hotControl = P.terminate; warmControl = P.continue }

a95 : Action
a95 = jobStep (ident 2) J.enter
c95 : Configuration
c95 = configuration (J.world (ig7) ((ident 0 , p19) ∷ [])) (g18) (g17) (launch []) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.awaitHot)) false false) ∷ []) (ident 2 ∷ []) [] [] 3 1 5 60 nothing false

step95 : advance a95 c94 ≡ just c95
step95 = refl

p20 : P.Peer
p20 = record p19 { runs = P.protocolRun Fixture.proto (P.returned S.clean) P.running ∷ []; pendingResults = (1 , S.clean) ∷ [] }

a96 : Action
a96 = protocolResult (ident 0) 1 S.clean
c96 : Configuration
c96 = configuration (J.world (ig7) ((ident 0 , p20) ∷ [])) (g18) (g17) (launch []) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.awaitHot)) false false) ∷ []) (ident 2 ∷ []) [] [] 3 1 5 60 nothing false

step96 : advance a96 c95 ≡ just c96
step96 = refl

p21 : P.Peer
p21 = record p20 { promotedAt = nothing; status = P.peerWarm; runs = P.protocolRun Fixture.proto (P.notRunning S.clean) (P.notRunning S.clean) ∷ [] }

a97 : Action
a97 = jobStep (ident 2) J.observeHot
c97 : Configuration
c97 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g18) (g17) (launch []) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) false false) ∷ []) (ident 2 ∷ []) [] [] 3 1 5 60 nothing false

step97 : advance a97 c96 ≡ just c97
step97 = refl

a98 : Action
a98 = enqueueCompletion (ident 2) 0
c98 : Configuration
c98 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g18) (g17) (launch []) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true false) ∷ []) (ident 2 ∷ []) (G.completion (G.job G.deactivate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 3 1 5 60 nothing false

step98 : advance a98 c97 ≡ just c98
step98 = refl

a99 : Action
a99 = deregisterJob (ident 2)
c99 : Configuration
c99 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g18) (g17) (launch []) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.deactivate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 3 1 5 60 nothing false

step99 : advance a99 c98 ≡ just c99
step99 = refl

a100 : Action
a100 = finishLaunch
c100 : Configuration
c100 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g18) (g17) (publishPublic) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.deactivate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 3 1 5 60 nothing false

step100 : advance a100 c99 ≡ just c100
step100 = refl

a101 : Action
a101 = publishPublicState
c101 : Configuration
c101 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g18) (g18) (sampleInputs) 5 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.deactivate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 3 1 5 60 nothing false

step101 : advance a101 c100 ≡ just c101
step101 = refl

a102 : Action
a102 = sampleTime 6
c102 : Configuration
c102 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g18) (g18) (prepareWait) 6 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.deactivate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 3 1 5 60 nothing false

step102 : advance a102 c101 ≡ just c102
step102 = refl

a103 : Action
a103 = registerWakeup
c103 : Configuration
c103 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g18) (g18) (selecting) 6 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.deactivate peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 3 1 5 60 nothing false

step103 : advance a103 c102 ≡ just c103
step103 = refl

a104 : Action
a104 = selectCompletion
c104 : Configuration
c104 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g18) (g18) (apply (completion (G.completion (G.job G.deactivate peerAddr (just (ident 0))) (G.succeeded) 0))) 6 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step104 : advance a104 c103 ≡ just c104
step104 = refl

g22 : G.State
g22 = G.complete 5 60 6 (G.completion (G.job G.deactivate peerAddr (just (ident 0))) (G.succeeded) 0) (g18)

a105 : Action
a105 = applyAt 6
c105 : Configuration
c105 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g18) (publishView []) 6 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step105 : advance a105 c104 ≡ just c105
step105 = refl

a106 : Action
a106 = publishCounters
c106 : Configuration
c106 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g18) (traceDecision []) 6 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step106 : advance a106 c105 ≡ just c106
step106 = refl

a107 : Action
a107 = traceSelection
c107 : Configuration
c107 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g18) (launch []) 6 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step107 : advance a107 c106 ≡ just c107
step107 = refl

a108 : Action
a108 = finishLaunch
c108 : Configuration
c108 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g18) (publishPublic) 6 (G.targets 1 1 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step108 : advance a108 c107 ≡ just c108
step108 = refl

a109 : Action
a109 = setTargets (G.targets 1 0 0)
c109 : Configuration
c109 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g18) (publishPublic) 6 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step109 : advance a109 c108 ≡ just c109
step109 = refl

a110 : Action
a110 = publishPublicState
c110 : Configuration
c110 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g22) (sampleInputs) 6 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step110 : advance a110 c109 ≡ just c110
step110 = refl

a111 : Action
a111 = sampleTime 7
c111 : Configuration
c111 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g22) (prepareWait) 7 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step111 : advance a111 c110 ≡ just c111
step111 = refl

a112 : Action
a112 = registerWakeup
c112 : Configuration
c112 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g22) (selecting) 7 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step112 : advance a112 c111 ≡ just c112
step112 = refl

a113 : Action
a113 = selectTargets
c113 : Configuration
c113 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g22) (g22) (apply (targets (G.targets 1 0 0))) 7 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step113 : advance a113 c112 ≡ just c113
step113 = refl

g23 : G.State
g23 = record (g22) { target = G.targets 1 0 0 }

a114 : Action
a114 = applyAt 7
c114 : Configuration
c114 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g23) (g22) (publishView []) 7 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step114 : advance a114 c113 ≡ just c114
step114 = refl

a115 : Action
a115 = publishCounters
c115 : Configuration
c115 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g23) (g22) (traceDecision []) 7 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step115 : advance a115 c114 ≡ just c115
step115 = refl

a116 : Action
a116 = traceSelection
c116 : Configuration
c116 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g23) (g22) (launch []) 7 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step116 : advance a116 c115 ≡ just c116
step116 = refl

a117 : Action
a117 = finishLaunch
c117 : Configuration
c117 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g23) (g22) (publishPublic) 7 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step117 : advance a117 c116 ≡ just c117
step117 = refl

a118 : Action
a118 = publishPublicState
c118 : Configuration
c118 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g23) (g23) (sampleInputs) 7 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step118 : advance a118 c117 ≡ just c118
step118 = refl

a119 : Action
a119 = sampleTime 8
c119 : Configuration
c119 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g23) (g23) (prepareWait) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step119 : advance a119 c118 ≡ just c119
step119 = refl

a120 : Action
a120 = registerWakeup
c120 : Configuration
c120 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g23) (g23) (selecting) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step120 : advance a120 c119 ≡ just c120
step120 = refl

a121 : Action
a121 = selectPolicy (peerAddr ∷ [])
c121 : Configuration
c121 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g23) (g23) (apply (policy (G.decision (G.mark G.close (peerAddr ∷ []) (g23)) (G.job G.close peerAddr (just (ident 0)) ∷ [])))) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step121 : advance a121 c120 ≡ just c121
step121 = refl

g24 : G.State
g24 = G.mark G.close (peerAddr ∷ []) (g23)

a122 : Action
a122 = applyAt 8
c122 : Configuration
c122 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g24) (g23) (publishView (G.job G.close peerAddr (just (ident 0)) ∷ [])) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step122 : advance a122 c121 ≡ just c122
step122 = refl

a123 : Action
a123 = publishCounters
c123 : Configuration
c123 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g24) (g23) (traceDecision (G.job G.close peerAddr (just (ident 0)) ∷ [])) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step123 : advance a123 c122 ≡ just c123
step123 = refl

a124 : Action
a124 = traceSelection
c124 : Configuration
c124 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g24) (g23) (launch (G.job G.close peerAddr (just (ident 0)) ∷ [])) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 3 1 5 60 nothing false

step124 : advance a124 c123 ≡ just c124
step124 = refl

a125 : Action
a125 = forkJob (ident 16) (ident 17) (ident 16)
c125 : Configuration
c125 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g24) (g23) (register (ident 3) []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.begin)) false false) ∷ []) [] [] [] 4 1 5 60 nothing false

step125 : advance a125 c124 ≡ just c125
step125 = refl

a126 : Action
a126 = registerJob
c126 : Configuration
c126 = configuration (J.world (ig7) ((ident 0 , p21) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.begin)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step126 : advance a126 c125 ≡ just c126
step126 = refl

p25 : P.Peer
p25 = record p21 { status = P.peerCooling; hotControl = P.terminate; warmControl = P.terminate; establishedControl = P.terminate }

a127 : Action
a127 = jobStep (ident 3) J.enter
c127 : Configuration
c127 = configuration (J.world (ig7) ((ident 0 , p25) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.awaitAll)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step127 : advance a127 c126 ≡ just c127
step127 = refl

a128 : Action
a128 = jobStep (ident 3) J.observeAll
c128 : Configuration
c128 = configuration (J.world (ig7) ((ident 0 , p25) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.callRelease)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step128 : advance a128 c127 ≡ just c128
step128 = refl

cm26 : CM.Configuration
cm26 = record (ig7) { releasing = (ident 16 , R.frame key₀ R.transaction false) ∷ [] }

a129 : Action
a129 = jobStep (ident 3) J.requestRelease
c129 : Configuration
c129 = configuration (J.world (cm26) ((ident 0 , p25) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.awaitRelease)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step129 : advance a129 c128 ≡ just c129
step129 = refl

release27 : CM.Configuration
release27 = cmAfter (CM.release (ident 16) R.transactionStep) (cm26)

a130 : Action
a130 = core (CM.release (ident 16) R.transactionStep)
c130 : Configuration
c130 = configuration (J.world (release27) ((ident 0 , p25) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.awaitRelease)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step130 : advance a130 c129 ≡ just c130
step130 = refl

release28 : CM.Configuration
release28 = cmAfter (CM.release (ident 16) R.readCounters) (release27)

a131 : Action
a131 = core (CM.release (ident 16) R.readCounters)
c131 : Configuration
c131 = configuration (J.world (release28) ((ident 0 , p25) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.awaitRelease)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step131 : advance a131 c130 ≡ just c131
step131 = refl

release29 : CM.Configuration
release29 = cmAfter (CM.release (ident 16) R.returnResult) (release28)

a132 : Action
a132 = core (CM.release (ident 16) R.returnResult)
c132 : Configuration
c132 = configuration (J.world (release29) ((ident 0 , p25) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.awaitRelease)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step132 : advance a132 c131 ≡ just c132
step132 = refl

a133 : Action
a133 = jobStep (ident 3) J.collectRelease
c133 : Configuration
c133 = configuration (J.world (release29) ((ident 0 , p25) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.awaitCold G.succeeded)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step133 : advance a133 c132 ≡ just c133
step133 = refl

p30 : P.Peer
p30 = record p25 { status = P.peerCold; monitorStarted = false; promotedAt = nothing }

a134 : Action
a134 = pollPeer (ident 0) (ident 18)
c134 : Configuration
c134 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.awaitCold G.succeeded)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step134 : advance a134 c133 ≡ just c134
step134 = refl

a135 : Action
a135 = jobStep (ident 3) J.observeCold
c135 : Configuration
c135 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) false false) ∷ []) (ident 3 ∷ []) [] [] 4 1 5 60 nothing false

step135 : advance a135 c134 ≡ just c135
step135 = refl

a136 : Action
a136 = enqueueCompletion (ident 3) 0
c136 : Configuration
c136 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true false) ∷ []) (ident 3 ∷ []) (G.completion (G.job G.close peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 4 1 5 60 nothing false

step136 : advance a136 c135 ≡ just c136
step136 = refl

a137 : Action
a137 = deregisterJob (ident 3)
c137 : Configuration
c137 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g23) (launch []) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.close peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 4 1 5 60 nothing false

step137 : advance a137 c136 ≡ just c137
step137 = refl

a138 : Action
a138 = finishLaunch
c138 : Configuration
c138 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g23) (publishPublic) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.close peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 4 1 5 60 nothing false

step138 : advance a138 c137 ≡ just c138
step138 = refl

a139 : Action
a139 = publishPublicState
c139 : Configuration
c139 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g24) (sampleInputs) 8 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.close peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 4 1 5 60 nothing false

step139 : advance a139 c138 ≡ just c139
step139 = refl

a140 : Action
a140 = sampleTime 9
c140 : Configuration
c140 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g24) (prepareWait) 9 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.close peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 4 1 5 60 nothing false

step140 : advance a140 c139 ≡ just c140
step140 = refl

a141 : Action
a141 = registerWakeup
c141 : Configuration
c141 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g24) (selecting) 9 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] (G.completion (G.job G.close peerAddr (just (ident 0))) (G.succeeded) 0 ∷ []) [] 4 1 5 60 nothing false

step141 : advance a141 c140 ≡ just c141
step141 = refl

a142 : Action
a142 = selectCompletion
c142 : Configuration
c142 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g24) (g24) (apply (completion (G.completion (G.job G.close peerAddr (just (ident 0))) (G.succeeded) 0))) 9 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 4 1 5 60 nothing false

step142 : advance a142 c141 ≡ just c142
step142 = refl

g31 : G.State
g31 = G.complete 5 60 9 (G.completion (G.job G.close peerAddr (just (ident 0))) (G.succeeded) 0) (g24)

a143 : Action
a143 = applyAt 9
c143 : Configuration
c143 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g31) (g24) (publishView []) 9 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 4 1 5 60 nothing false

step143 : advance a143 c142 ≡ just c143
step143 = refl

a144 : Action
a144 = publishCounters
c144 : Configuration
c144 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g31) (g24) (traceDecision []) 9 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 4 1 5 60 nothing false

step144 : advance a144 c143 ≡ just c144
step144 = refl

a145 : Action
a145 = traceSelection
c145 : Configuration
c145 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g31) (g24) (launch []) 9 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 4 1 5 60 nothing false

step145 : advance a145 c144 ≡ just c145
step145 = refl

a146 : Action
a146 = finishLaunch
c146 : Configuration
c146 = configuration (J.world (release29) ((ident 0 , p30) ∷ [])) (g31) (g24) (publishPublic) 9 (G.targets 1 0 0)
  ((ident 0 , jobFrame (J.frame (G.job G.establish peerAddr nothing) (caller) (child) (ident 10) (ident 0) (J.complete (G.establishedOK (ident 0)))) true true) ∷ (ident 1 , jobFrame (J.frame (G.job G.activate peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 2 , jobFrame (J.frame (G.job G.deactivate peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.complete G.succeeded)) true true) ∷ (ident 3 , jobFrame (J.frame (G.job G.close peerAddr (just (ident 0))) (ident 16) (ident 17) (ident 16) (ident 0) (J.complete G.succeeded)) true true) ∷ []) [] [] [] 4 1 5 60 nothing false

step146 : advance a146 c145 ≡ just c146
step146 = refl
schedule : List Action
schedule = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ a20 ∷ a21 ∷ a22 ∷ a23 ∷ a24 ∷ a25 ∷ a26 ∷ a27 ∷ a28 ∷ a29 ∷ a30 ∷ a31 ∷ a32 ∷ a33 ∷ a34 ∷ a35 ∷ a36 ∷ a37 ∷ a38 ∷ a39 ∷ a40 ∷ a41 ∷ a42 ∷ a43 ∷ a44 ∷ a45 ∷ a46 ∷ a47 ∷ a48 ∷ a49 ∷ a50 ∷ a51 ∷ a52 ∷ a53 ∷ a54 ∷ a55 ∷ a56 ∷ a57 ∷ a58 ∷ a59 ∷ a60 ∷ a61 ∷ a62 ∷ a63 ∷ a64 ∷ a65 ∷ a66 ∷ a67 ∷ a68 ∷ a69 ∷ a70 ∷ a71 ∷ a72 ∷ a73 ∷ a74 ∷ a75 ∷ a76 ∷ a77 ∷ a78 ∷ a79 ∷ a80 ∷ a81 ∷ a82 ∷ a83 ∷ a84 ∷ a85 ∷ a86 ∷ a87 ∷ a88 ∷ a89 ∷ a90 ∷ a91 ∷ a92 ∷ a93 ∷ a94 ∷ a95 ∷ a96 ∷ a97 ∷ a98 ∷ a99 ∷ a100 ∷ a101 ∷ a102 ∷ a103 ∷ a104 ∷ a105 ∷ a106 ∷ a107 ∷ a108 ∷ a109 ∷ a110 ∷ a111 ∷ a112 ∷ a113 ∷ a114 ∷ a115 ∷ a116 ∷ a117 ∷ a118 ∷ a119 ∷ a120 ∷ a121 ∷ a122 ∷ a123 ∷ a124 ∷ a125 ∷ a126 ∷ a127 ∷ a128 ∷ a129 ∷ a130 ∷ a131 ∷ a132 ∷ a133 ∷ a134 ∷ a135 ∷ a136 ∷ a137 ∷ a138 ∷ a139 ∷ a140 ∷ a141 ∷ a142 ∷ a143 ∷ a144 ∷ a145 ∷ a146 ∷ []
path : Executes c₀ schedule c146
path = next step1 (next step2 (next step3 (next step4 (next step5 (next step6 (next step7 (next step8 (next step9 (next step10 (next step11 (next step12 (next step13 (next step14 (next step15 (next step16 (next step17 (next step18 (next step19 (next step20 (next step21 (next step22 (next step23 (next step24 (next step25 (next step26 (next step27 (next step28 (next step29 (next step30 (next step31 (next step32 (next step33 (next step34 (next step35 (next step36 (next step37 (next step38 (next step39 (next step40 (next step41 (next step42 (next step43 (next step44 (next step45 (next step46 (next step47 (next step48 (next step49 (next step50 (next step51 (next step52 (next step53 (next step54 (next step55 (next step56 (next step57 (next step58 (next step59 (next step60 (next step61 (next step62 (next step63 (next step64 (next step65 (next step66 (next step67 (next step68 (next step69 (next step70 (next step71 (next step72 (next step73 (next step74 (next step75 (next step76 (next step77 (next step78 (next step79 (next step80 (next step81 (next step82 (next step83 (next step84 (next step85 (next step86 (next step87 (next step88 (next step89 (next step90 (next step91 (next step92 (next step93 (next step94 (next step95 (next step96 (next step97 (next step98 (next step99 (next step100 (next step101 (next step102 (next step103 (next step104 (next step105 (next step106 (next step107 (next step108 (next step109 (next step110 (next step111 (next step112 (next step113 (next step114 (next step115 (next step116 (next step117 (next step118 (next step119 (next step120 (next step121 (next step122 (next step123 (next step124 (next step125 (next step126 (next step127 (next step128 (next step129 (next step130 (next step131 (next step132 (next step133 (next step134 (next step135 (next step136 (next step137 (next step138 (next step139 (next step140 (next step141 (next step142 (next step143 (next step144 (next step145 (next step146 done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
accepted : traces (Process c₀) (map label schedule)
accepted = trace-intro path
final : Configuration
final = c146

{-# OPTIONS --guardedness #-}

-- G2 step 4: a configured one-protocol initiator on a plain unidirectional
-- outbound bearer. Real peer jobs and physical handler/mux lifetimes share the
-- ServerPeers frontend. Transport/handshake/provider/timer returns are inputs.
module ConnectionManagement.Negative.OutboundCleanLifecycleSupport where

open import Agda.Builtin.Reflection using (Term; TC; normalise; unify; bindTC)
open import Agda.Builtin.Unit using (⊤)
open import Data.Bool using (Bool; true; false) public
open import Data.Nat using (ℕ) public
open import Data.List using (List; []; _∷_; _++_; length) public
open import Data.Product using (_,_ )
open import Data.Maybe using (just; nothing) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import ConnectionManagement.Domain hiding (worker; local; mux; job) public
open import ConnectionManagement.Store using (lookup) public
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (admit; consume; handler; mux) public

classify : ErrorId → Bool
classify _ = false
capability : HandleId → ℕ → Bool
capability (ident 0) 1 = true
capability _ _ = false
module K = Combined I.bearerClosed classify
module V = K.Protocols capability
module C = Context classify
module PS = Supervision classify
module E = Exit I.bearerClosed
module S = Server I.bearerClosed
module N = Publication I.bearerClosed
module W = N.W
module G = N.G
module M = N.M
module P = N.P
module U = N.U
module T = N.S
module Pool = P.Pool
module F = X.F
settings : Governor.State
settings = Governor.governorState (Governor.targets 1 1 0)
  ((remote A.key₀ , Governor.known 0 0 nothing false false) ∷ []) [] [] [] [] [] [] [] []
c₀ : Machine.Configuration
c₀ = Machine.initial Shared.responderMode F.empty
initial : V.Runtime
initial = V.runtime (K.combined X.start (C.capture (PS.initial (O.initial c₀) settings))) V.empty
initializer : V.initialize (O.initial c₀) settings ≡ just initial
initializer = refl

-- Splice the normalized successor of ONE actual runtime edge as a literal.
-- The default is never accepted: each use has an independent just/refl edge.
macro
  snapshot : Term → Term → TC ⊤
  snapshot t hole = bindTC (normalise t) (unify hole)
after : V.Event → V.Runtime → V.Runtime
after a s with V.advance a s
... | just t = t
... | nothing = s
server : E.Action → V.Event
server a = V.dispatch (K.serverStep a)
ig : IG.IGAction → V.Event
ig a = server (E.run (S.run (S.runMachine (Machine.igStep a))))
release : Release.Action → V.Event
release a = server (E.run (S.run (S.runMachine (Machine.releaseStep a))))
protocol : P.Action → V.Event
protocol a = V.dispatch (V.physicalAction a)
group : G.Action → V.Event
group a = server (E.run (S.run (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run (W.run a))))))))
exit : W.Action → V.Event
exit a = server (E.run (S.run (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run a)))))))
source : V.Runtime → O.Configuration
source s = K.source (V.base s)
shared : V.Runtime → Shared.State
shared s = Machine.world (O.core (source s))
governor : V.Runtime → IG.Runtime
governor s = Machine.inboundGovernor (O.core (source s))

-- Caller-supplied DeltaQ return after the real responder completion tracer.
delta : N.D.Action → V.Event
delta a = server (E.run (S.run (N.run (N.C.run a))))

import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Rules.OutboundRelease as OutRelease
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.HandshakeContinuation as HS
import ConnectionManagement.CSP.GovernorLifecycle as L
module GP = PS.GP
peer : PS.Action → V.Event
peer a = V.dispatch (K.peerStep a)
ps : Sub.Action → V.Event
ps a = peer (PS.run (GP.run a))
core : O.Action → V.Event
core a = V.dispatch (K.coreStep a)
acquire : Acquire.Action → V.Event
acquire a = core (O.acquire L.caller a)
outRelease : OutRelease.Action → V.Event
outRelease a = core (O.release (ident 16) a)
startup : T.Action → V.Event
startup a = server (E.run (mux (U.startupStep L.child a)))
handshake : HS.Event → V.Event
handshake a = server (E.run (mux (U.handshakeStep L.child a)))
handlerState : V.Runtime → W.State
handlerState s = N.R.base (N.raw (V.publication (V.base s)))
append : ∀ {s as t bs u} → V.Runs s as t → V.Runs t bs u → V.Runs s (as ++ bs) u
append V.stop tail = tail
append (V.more edge rest) tail = V.more edge (append rest tail)

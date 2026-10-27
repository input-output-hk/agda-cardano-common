{-# OPTIONS --guardedness #-}

-- A fresh outbound socket, handler, promise and duplex result from an empty CM.
module ConnectionManagement.CSP.OutboundAdmission where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
open import ConnectionManagement.Store using (put)
import ConnectionManagement.Machine as Inbound
open import ConnectionManagement.OutboundMachine
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.CSP.Outbound using (Process; trace-intro; Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

caller child : WorkerId
caller = ident 10
child = ident 11
sock : SocketId
sock = ident 10
req : A.Request
req = A.acquireRequest (remote key₀) child sock outbound nothing
s₀ : S.State
s₀ = Inbound.world F.start
reserved : S.State
reserved = record s₀ { cm = S.cmStore (S.full (S.insertLocal (remote key₀) unknownLocal (ident 0) []))
  ((ident 0 , S.reservedOutbound) ∷ []) 1 }
promised : S.State
promised = record reserved { promises = ident 0 ∷ S.promises reserved; nextPromise = 1 }
opened : S.State
opened = record promised { sockets = put sock (S.admitting caller) (S.sockets promised) }
addressed : S.State
addressed = record opened { cm = record (S.cm opened) { mapCell = S.full (S.insertConnection key₀ (ident 0) []) } }
forked : S.State
forked = record addressed
  { handlers = put child (S.handlerStart (ident 0) sock (ident 0) key₀) (S.handlers addressed)
  ; sockets = put sock (S.handling child) (S.sockets addressed) }
connected : S.State
connected = record forked { cm = record (S.cm forked)
  { entries = put (ident 0) (S.unnegotiated outbound key₀ child) (S.entries (S.cm forked)) } }
published : S.State
published = record connected { handshakeResults = put (ident 0) (S.negotiated (ident 0) duplex) (S.handshakeResults connected) }
negotiated : S.State
negotiated = record published
  { cm = record (S.cm published) { entries = put (ident 0) (S.outboundDup key₀ child (ident 0) ticking) (S.entries (S.cm published)) }
  ; inboundInfo = S.newConnection (S.newConnectionInfo outbound key₀ duplex (ident 0)) ∷ [] }

at : A.PC → S.State → Configuration
at pc worldState = record (initial (Inbound.replaceWorld F.start worldState))
  { acquiring = (caller , A.frame req pc) ∷ []; randomGeneration = 1 }
begun : Configuration
begun = record (at A.selecting s₀) { randomGeneration = 0 }
wait : A.PC
wait = A.awaitResult (ident 0) (ident 0) key₀
-- Install a concrete handle via the existing runtime action, before publication.
installedCore : Inbound.Configuration
installedCore = record (Inbound.replaceWorld F.start connected)
  { inboundGovernor = Inbound.inboundGovernor G.installed }

withHandle : Configuration → Configuration
withHandle c = record c { core = record (core c) { inboundGovernor = Inbound.inboundGovernor G.installed } }
returned : Configuration
returned = record (withHandle (at (A.complete (C.connected key₀ duplex (ident 0))) negotiated))
  { acquiring = []; acquired = (caller , C.connected key₀ duplex (ident 0)) ∷ [] }
schedule : List Action
schedule = beginAcquire caller req ∷ acquire caller (A.select nothing) ∷
  acquire caller A.readCounters ∷ acquire caller A.newPromise ∷ acquire caller A.openOK ∷
  acquire caller A.configureOK ∷ acquire caller A.connectOK ∷ acquire caller (A.gotLocal (local key₀)) ∷
  acquire caller A.updateLocalAddress ∷ acquire caller A.forkOK ∷ acquire caller A.commitConnected ∷
  acquire caller A.readCounters ∷ inbound (Inbound.igStep (IG.installOutboundHandle (ident 0) G.mid key₀ (G.proto ∷ []) duplex)) ∷
  inbound (Inbound.handlerPublication child (S.negotiated (ident 0) duplex) Inbound.resultWritten) ∷
  acquire caller A.readResult ∷ acquire caller A.commitHandshake ∷ acquire caller A.readCounters ∷ acquire caller A.returnResult ∷ []
path : Executes (initial F.start) schedule returned
path = next {c₁ = begun} refl (
  next {c₁ = at (A.count (A.allocatePromise (ident 0))) reserved} refl (
  next {c₁ = at (A.allocatePromise (ident 0)) reserved} refl (
  next {c₁ = at (A.openSocket (ident 0) (ident 0)) promised} refl (
  next {c₁ = at (A.configureSocket (ident 0) (ident 0)) opened} refl (
  next {c₁ = at (A.connectSocket (ident 0) (ident 0)) opened} refl (
  next {c₁ = at (A.localAddress (ident 0) (ident 0)) opened} refl (
  next {c₁ = at (A.updateAddress (ident 0) (ident 0) key₀) opened} refl (
  next {c₁ = at (A.forkHandler (ident 0) (ident 0) key₀) addressed} refl (
  next {c₁ = at (A.connectedCommit (ident 0) (ident 0) key₀) forked} refl (
  next {c₁ = at (A.count wait) connected} refl (
  next {c₁ = at wait connected} refl (
  next {c₁ = withHandle (at wait connected)} refl (
  next {c₁ = withHandle (at wait published)} refl (
  next {c₁ = withHandle (at (A.commitResult (ident 0) key₀ (S.negotiated (ident 0) duplex)) published)} refl (
  next {c₁ = withHandle (at (A.count (A.complete (C.connected key₀ duplex (ident 0)))) negotiated)} refl (
  next {c₁ = withHandle (at (A.complete (C.connected key₀ duplex (ident 0))) negotiated)} refl (next refl done)))))))))))))))))
accepted : traces (Process (initial F.start)) (map label schedule)
accepted = trace-intro path

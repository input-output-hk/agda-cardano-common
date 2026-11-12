{-# OPTIONS --guardedness #-}

-- An initialized one-event counterexample to the physical component of CM-I4c
-- under C3's unchanged premises. A supplied outbound PC can skip allocation;
-- the actual supervised fork records that PC's missing entry and promise.
module ConnectionManagement.Properties.LiveTrackerReferencesCounterexample where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using
  (WorkerId; SocketId; EntryId; PromiseId; HandleId; ErrorId; ConnectionKey;
   ident; connection; addr; ipv4; remote; Provenance; inbound; outbound)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as IGExit
import ConnectionManagement.PeerSupervision as Peer
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.CMShutdown as Close

-- The witness needs no exceptional classifiers or initiator capabilities.
classify : ErrorId → Bool
classify _ = false
capability : HandleId → ℕ → Bool
capability _ _ = false

private
 module K = Combined classify classify using (combined; coreStep)
 module SA = Server classify using (serverState; serving; igLive)
 module E = IGExit classify using (igExitState; emptyExit)
 module PS = Peer classify using (initial)
 module Ctx = Context classify using (Context; capture; regions)
 module N = Publication classify using (publicationState; module C; module D; module R; module W; module G; module M; module P; module U)

open Combined.Protocols classify classify capability using
  (Runtime; Event; Runs; runtime; empty; initialize; dispatch; advance; more; stop)
open import ConnectionManagement.Properties.LiveTrackerReferences using (module Frontend)
open Frontend classify classify capability using
  (physicalState; shared; PhysicalReferences; Universal)
import ConnectionManagement.Properties.FrontendPhaseCleanup as PhaseCleanup
open PhaseCleanup.Frontend classify classify capability using (from-initial)
  renaming (Valid to PhaseCleanupValid)

-- Distinct identities keep the example independent of finite fixture bounds.
caller child : WorkerId
caller = ident 10
child = ident 11
socket : SocketId
socket = ident 10
missingEntry : EntryId
missingEntry = ident 99
missingPromise : PromiseId
missingPromise = ident 88
key : ConnectionKey
key = connection (addr ipv4 0 3001) (addr ipv4 1 3001)
request : A.Request
request = A.acquireRequest (remote key) child socket outbound nothing
captured : S.HandlerStart
captured = S.handlerStart missingEntry socket missingPromise key

-- The original map is well referenced. Its entry0 is not the captured entry99.
-- Physical, admission, socket, promise and cleanup stores all start empty.
seed : S.State
seed = S.state
  (S.cmStore (S.full (S.insertConnection key (ident 0) []))
    ((ident 0 , S.unnegotiated inbound key child) ∷ []) 1)
  [] [] [] [] 0 [] [] []
core : M.Configuration
core = M.initial S.responderMode seed
configuration : O.Configuration
configuration = record (O.initial core)
  { acquiring = (caller , A.frame request (A.forkHandler missingEntry missingPromise key)) ∷ [] }
settings : Governor.State
settings = Governor.governorState (Governor.targets 0 0 0) [] [] [] [] [] [] [] [] []
context : Ctx.Context
context = Ctx.capture (PS.initial configuration settings)

-- Flat snapshots avoid normalizing a chain of projected attempted transitions.
-- Every wrapper starts in its real initialized state; the edge below checks
-- all physical and shared-dispatch permissions, rather than assuming a plan.
render : B.State → Store WorkerId Provenance → Store WorkerId Cancel.Context → Runtime
render physical origins regions = runtime
  (K.combined
    (E.igExitState
      (SA.serverState
        (N.publicationState
          (N.C.catchState
            (N.D.deltaQState
              (N.R.unwinding
                (N.W.handlerExitState
                  (N.G.shutdownState
                    (N.M.monitorState
                      (N.P.protocolState (N.U.supervised physical origins []) [] []) []) []) []) []) []) []) [])
        [] SA.serving true SA.igLive)
      E.emptyExit)
    (record context { regions = regions })) empty

start : Runtime
start = render (B.supervised configuration [] Close.initialState) [] []
initialized : initialize configuration settings ≡ just start
initialized = refl

-- The required physical component holds initially, so failure is reached by
-- an enabled transition rather than inserted as an invalid physical snapshot.
initial-references : PhysicalReferences start
initial-references w thread ()

fork : Event
fork = dispatch (K.coreStep (O.acquire caller A.forkOK))
afterWorld : S.State
afterWorld = record seed
  { handlers = (child , captured) ∷ []
  ; sockets = (socket , S.handling child) ∷ [] }
afterConfiguration : O.Configuration
afterConfiguration = record configuration
  { core = M.replaceWorld core afterWorld
  ; acquiring = (caller , A.frame request (A.connectedCommit missingEntry missingPromise key)) ∷ [] }
after : Runtime
after = render
  (B.supervised afterConfiguration
    ((child , H.handlerThread captured H.maskedSetup) ∷ []) Close.initialState)
  ((child , outbound) ∷ []) ((caller , Cancel.forkedBeforeHandoff) ∷ [])
actual-fork : advance fork start ≡ just after
actual-fork = refl
initialized-run : Runs start (fork ∷ []) after
initialized-run = more {a = fork} actual-fork stop

-- Registration, physical capture and socket agree; precisely the referenced
-- entry and promise were never allocated. Terminal-state restrictions play no
-- role: the bad reference belongs to a live maskedSetup thread.
physical-found : lookup child (B.threads (physicalState after)) ≡
  just (H.handlerThread captured H.maskedSetup)
physical-found = refl
handler-found : lookup child (S.handlers (shared after)) ≡ just captured
handler-found = refl
socket-found : lookup socket (S.sockets (shared after)) ≡ just (S.handling child)
socket-found = refl
entry-missing : lookup missingEntry (S.entries (S.cm (shared after))) ≡ nothing
entry-missing = refl
promise-missing : missingPromise ∈ S.promises (shared after) → ⊥
promise-missing ()
not-references : PhysicalReferences after → ⊥
not-references valid with valid child (H.handlerThread captured H.maskedSetup) physical-found
... | (_ , (_ , ()) , _) , allocated

-- Refutes even a necessary part of full live-tracker reference validity, with
-- exactly C3's initialization/execution premises and no changed transition.
not-universal : Universal → ⊥
not-universal invariant = not-references (invariant configuration settings initialized initialized-run)

-- The same initialized run satisfies the existing C3 theorem. Reference
-- failure does not refute its separate phase/cleanup agreement.
phase-cleanup-valid : PhaseCleanupValid after
phase-cleanup-valid = from-initial configuration settings initialized initialized-run

-- The preloaded continuation is essential to this witness. O.initial erases
-- it, so the same immediate fork is refused under that narrower profile.
ordinary : Runtime
ordinary = render (B.supervised (O.initial core) [] Close.initialState) [] []
ordinary-initialized : initialize (O.initial core) settings ≡ just ordinary
ordinary-initialized = refl
ordinary-fork-refused : advance fork ordinary ≡ nothing
ordinary-fork-refused = refl

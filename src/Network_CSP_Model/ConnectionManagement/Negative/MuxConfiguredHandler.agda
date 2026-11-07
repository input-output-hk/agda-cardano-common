{-# OPTIONS --guardedness #-}

-- Initialized configured-mux handler path: the allocated handle receives an
-- actual scheduled egress profile before publication, then the configured
-- startup forks/registers exactly the Direct and Scheduled lane muxers and the
-- demuxer. Kernel-level acceptance only; no counter registry or M4 grants.
module ConnectionManagement.Negative.MuxConfiguredHandler where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.MuxHandlerSupervision as Coupled
module U = Coupled ⊤
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Machine as M
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxStartup as StartupRules
module S = StartupRules ⊤
import ConnectionManagement.CSP.OutboundAdmission as Fixture
import ConnectionManagement.Negative.MuxHandlerSupervision as Base

-- Guarded execution; each certificate below also proves the execution returned just.
exec : List U.Action → U.State → Maybe U.State
exec [] s = just s
exec (a ∷ as) s with U.step a s
... | nothing = nothing
... | just t = exec as t
exec-runs : ∀ as s {t} → exec as s ≡ just t → U.Executes s as t
exec-runs [] s refl = U.done
exec-runs (a ∷ as) s eq with U.step a s in advanced
... | just next = U.next advanced (exec-runs as next eq)
after : List U.Action → U.State
after as with exec as Base.q14
... | just t = t
... | nothing = Base.q14

-- Duplex protocol 1: initiator demand on the Scheduled lane, responder on Direct.
keys : List (Mux.ProtocolKey × E.Lane)
keys = ((1 , Mux.initiatorJob) , E.scheduledLane) ∷ ((1 , Mux.responderJob) , E.directLane) ∷ []
plan : E.Layout
plan = E.scheduledLayout false
st : S.Action → U.Action
st = U.startupStep Fixture.child
configured : U.Action
configured = U.configureMux Fixture.child plan 16 1000 keys
toEgress : List U.Action
toEgress = st S.allocateBuffer ∷ st S.createBearer ∷ st S.enterRun ∷ st S.traceStarting ∷ st S.allocateEgress ∷ []
startupActions : List U.Action
startupActions = toEgress ++ (st (S.configureStartup plan) ∷ st S.openPool ∷
  st (S.forkConfigured (ident 10)) ∷ st S.registerConfigured ∷
  st (S.forkConfigured (ident 11)) ∷ st S.registerConfigured ∷
  st (S.forkConfigured (ident 12)) ∷ st S.registerConfigured ∷
  st S.traceConfiguredMature ∷ st S.enterConfiguredMonitor ∷ [])
configuredActions : List U.Action
configuredActions = configured ∷ U.publishSuccess Fixture.child ∷ startupActions

abstract
  initialized-configured-handler : U.Executes Base.q₀ (Base.birthActions ++
    (U.negotiate Fixture.child Base.ps duplex ∷ U.allocateHandle Fixture.child (ident 0) (ident 0) ∷ [])
    ++ configuredActions) (after configuredActions)
  initialized-configured-handler = append (append Base.initialized-birth
    (U.next Base.actual-negotiate (U.next Base.actual-handle-allocation U.done)))
    (exec-runs configuredActions Base.q14 refl)
    where
    append : ∀ {p as q bs r} → U.Executes p as q → U.Executes q bs r → U.Executes p (as ++ bs) r
    append U.done tail = tail
    append (U.next eq path) tail = U.next eq (append path tail)

-- The actual source mux now has the configured layout and exact key lanes.
installed-plain-before : U.layoutIs E.plainLayout (Base.publishedFrame S.initial) Base.q14 ≡ true
installed-plain-before = refl
configured-layout : U.layoutIs plan (Base.publishedFrame S.initial) (after (configured ∷ [])) ≡ true
configured-layout = refl
monitoring-after-plan : S.monitoringPC (S.phase (U.startupAt Fixture.child (after configuredActions))) ≡ true
monitoring-after-plan = refl
exact-roles : S.infraBindings (S.phase (U.startupAt Fixture.child (after configuredActions))) ≡
  (Types.laneMuxer E.directLane , ident 10) ∷ (Types.laneMuxer E.scheduledLane , ident 11) ∷ (Types.demuxer , ident 12) ∷ []
exact-roles = refl

-- Refusals at the handler boundary.
afterEgress : U.State
afterEgress = after (configured ∷ U.publishSuccess Fixture.child ∷ toEgress)
legacy-pool-refused-on-scheduled-mux : U.step (st S.openPool) afterEgress ≡ nothing
legacy-pool-refused-on-scheduled-mux = refl
mismatched-plan-refused : U.step (st (S.configureStartup (E.scheduledLayout true))) afterEgress ≡ nothing
mismatched-plan-refused = refl
plain-configured-plan-refused : U.step (st (S.configureStartup E.plainLayout)) afterEgress ≡ nothing
plain-configured-plan-refused = refl
second-configuration-refused : U.step configured (after (configured ∷ [])) ≡ nothing
second-configuration-refused = refl
configuration-after-publication-refused : U.step configured (after (configured ∷ U.publishSuccess Fixture.child ∷ [])) ≡ nothing
configuration-after-publication-refused = refl
raw-ig-configuration-refused : U.step (U.run (B.handler (H.run (M.igStep (IG.configureEgress (ident 0) plan 16 1000 keys))))) Base.q14 ≡ nothing
raw-ig-configuration-refused = refl

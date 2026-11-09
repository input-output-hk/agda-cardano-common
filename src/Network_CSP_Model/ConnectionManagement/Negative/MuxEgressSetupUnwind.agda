{-# OPTIONS --guardedness #-}

-- M3 controls: failures inside a scheduled mux's pre-publication egress setup
-- (network 2f1c154, ConnectionHandler newMux: egressRuleOf, the rank-source/
-- charge-sink STM transaction, TraceEgressRank). Each site is reachable only
-- once the preceding setup operation has returned. A failure is captured
-- outside the handshake catch with no promise write; the failed owner cannot
-- continue setup or publish. A plain mux has no setup failure site.
module ConnectionManagement.Negative.MuxEgressSetupUnwind where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Negative.MuxPublicationFixtures as Old
import ConnectionManagement.Negative.MuxPublicationUnwind as Base
import ConnectionManagement.Negative.MuxConfiguredTraffic as T
module N = Old.N
module R = Old.R
module P = Old.P
module U = Old.U

owner : WorkerId
owner = Old.owner
err : ErrorId
err = errorId 93
isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false
after : N.Action → N.State → N.State
after a s with N.step a s
... | just t = t
... | nothing = s

-- Handler setup states: the allocated handle, then the configured scheduled
-- mux at each setup stage (rule obtained, rank installed, rank traced).
at : U.Setup → N.State
at k = Base.wrap (T.cfgAt k Old.b14)
configure : N.Action
configure = Base.runP (P.run (U.configureMux owner T.plan 16 1000 T.keys))
setup : N.Action
setup = Base.runP (P.run (U.egressSetup owner))
publish : N.Action
publish = Base.runP (P.run (U.publishSuccess owner))

e1 : N.step configure (Base.wrap Old.b14) ≡ just (at U.setupPending)
e1 = refl
e2 : N.step setup (at U.setupPending) ≡ just (at U.ruleObtained)
e2 = refl
e3 : N.step setup (at U.ruleObtained) ≡ just (at U.rankInstalled)
e3 = refl
e4 : N.step setup (at U.rankInstalled) ≡ just (at U.rankTraced)
e4 = refl

-- Each site follows exactly the last returned setup step.
rule-failure : isJust (N.step (N.observeFailure owner N.egressRule (R.sync err)) (at U.setupPending)) ≡ true
rule-failure = refl
rule-async : isJust (N.step (N.observeFailure owner N.egressRule (R.async err)) (at U.setupPending)) ≡ true
rule-async = refl
install-failure : isJust (N.step (N.observeFailure owner N.rankInstall (R.sync err)) (at U.ruleObtained)) ≡ true
install-failure = refl
-- The rule's STM may retry, so the transaction is interruptible.
install-async : isJust (N.step (N.observeFailure owner N.rankInstall (R.async err)) (at U.ruleObtained)) ≡ true
install-async = refl
trace-failure : isJust (N.step (N.observeFailure owner N.rankTrace (R.sync err)) (at U.rankInstalled)) ≡ true
trace-failure = refl
trace-async : isJust (N.step (N.observeFailure owner N.rankTrace (R.async err)) (at U.rankInstalled)) ≡ true
trace-async = refl

-- Out-of-order sites are refused.
install-before-rule-refused : N.step (N.observeFailure owner N.rankInstall (R.sync err)) (at U.setupPending) ≡ nothing
install-before-rule-refused = refl
trace-before-install-refused : N.step (N.observeFailure owner N.rankTrace (R.sync err)) (at U.ruleObtained) ≡ nothing
trace-before-install-refused = refl
rule-after-rule-refused : N.step (N.observeFailure owner N.egressRule (R.sync err)) (at U.ruleObtained) ≡ nothing
rule-after-rule-refused = refl
no-setup-site-after-trace : N.step (N.observeFailure owner N.rankTrace (R.sync err)) (at U.rankTraced) ≡ nothing
no-setup-site-after-trace = refl
-- A plain mux runs no egress rule.
plain-rule-refused : N.step (N.observeFailure owner N.egressRule (R.sync err)) (Base.wrap Old.b14) ≡ nothing
plain-rule-refused = refl
plain-trace-refused : N.step (N.observeFailure owner N.rankTrace (R.sync err)) (Base.wrap Old.b14) ≡ nothing
plain-trace-refused = refl

-- After a failed install, the owner neither retries setup nor publishes, and
-- no handshake result is written for its promise.
failed : N.State
failed = after (N.observeFailure owner N.rankInstall (R.sync err)) (at U.ruleObtained)
failed-setup-refused : N.step setup failed ≡ nothing
failed-setup-refused = refl
failed-publication-refused : N.step publish failed ≡ nothing
failed-publication-refused = refl
no-promise-written : lookup (Shared.handlerPromise Old.Prior.captured)
  (Shared.handshakeResults (Machine.world (O.core (N.source failed)))) ≡ nothing
no-promise-written = refl

-- Initialized: the actual birth/handshake prefix, allocation, configuration,
-- the rule and install steps, then a TraceEgressRank failure.
setupActions : List N.Action
setupActions = Base.runP (P.run (U.allocateHandle owner (ident 0) Old.mid)) ∷ configure ∷ setup ∷ setup ∷
  N.observeFailure owner N.rankTrace (R.sync err) ∷ []
traceFailed : N.State
traceFailed = after (N.observeFailure owner N.rankTrace (R.sync err)) (at U.rankInstalled)
abstract
  initialized-trace-failure : N.Executes Base.initial (Base.beforeActions ++ setupActions) traceFailed
  initialized-trace-failure = append Base.beforePrefix
    (N.next Base.prefix14 (N.next e1 (N.next e2 (N.next e3 (N.next refl N.done)))))
    where
    append : ∀ {p as q bs r} → N.Executes p as q → N.Executes q bs r → N.Executes p (as ++ bs) r
    append N.done tail = tail
    append (N.next eq path) tail = N.next eq (append path tail)

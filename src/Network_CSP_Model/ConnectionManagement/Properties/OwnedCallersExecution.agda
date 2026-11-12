{-# OPTIONS --guardedness #-}

-- Shared-state invariant: unchanged source Reach, plus no foreign frame worker.
-- The proof reuses Reach preservation and exact source effects; no original
-- ownership statement or shared source rule is changed.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallersExecution
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.ServerIGExit as ExitFacts
import ConnectionManagement.Properties.SourceKeysShared as KeyFacts
import ConnectionManagement.Properties.OwnedFramesExecution as ReachFacts
import ConnectionManagement.Properties.OwnedCallersBase as Base
import ConnectionManagement.Properties.OwnedCallersPeers as PeerFacts
import ConnectionManagement.Variants.OwnedCallers as Variant
open import ConnectionManagement.Properties.OutboundKeys using (keyRoot; Effect)
open Base isBearerClosed isIOManagerError using
  (module K; module PS; module GP; module C; NF; NoForeign; primitive-empty; not-present; no-present; same-source)
private
  module E = Exit isBearerClosed
  module Keys = KeyFacts isBearerClosed isIOManagerError
  module Reach = ReachFacts isBearerClosed isIOManagerError
  module Peer = PeerFacts isBearerClosed isIOManagerError
  module V = Variant isBearerClosed isIOManagerError

-- The original strengthened invariant is retained as an independent clause.
Inv : K.State → Set
Inv s = Reach.Reach s × NF s

-- The shared peer guard already forbids every raw subsystem core alias.
peer-policy : ∀ a s → K.peerAllowed a s ≡ true → Peer.allowed a ≡ true
peer-policy (PS.run (GP.run (Sub.core a))) s ()
peer-policy (PS.run (GP.run (Sub.publishPublicState))) s ok = refl
peer-policy (PS.run (GP.run (Sub.sampleTime t))) s ok = refl
peer-policy (PS.run (GP.run (Sub.applyAt t))) s ok = refl
peer-policy (PS.run (GP.run (Sub.setTargets desired))) s ok = refl
peer-policy (PS.run (GP.run (Sub.selectMonitor delays))) s ok = refl
peer-policy (PS.run (GP.run (Sub.selectCompletion))) s ok = refl
peer-policy (PS.run (GP.run (Sub.selectTargets))) s ok = refl
peer-policy (PS.run (GP.run (Sub.selectWakeup))) s ok = refl
peer-policy (PS.run (GP.run (Sub.registerWakeup))) s ok = refl
peer-policy (PS.run (GP.run (Sub.expireWakeup))) s ok = refl
peer-policy (PS.run (GP.run (Sub.cancelWakeup))) s ok = refl
peer-policy (PS.run (GP.run (Sub.publishCounters))) s ok = refl
peer-policy (PS.run (GP.run (Sub.traceSelection))) s ok = refl
peer-policy (PS.run (GP.run (Sub.selectPolicy picked))) s ok = refl
peer-policy (PS.run (GP.run (Sub.forkJob w child sock))) s ok = refl
peer-policy (PS.run (GP.run (Sub.registerJob))) s ok = refl
peer-policy (PS.run (GP.run (Sub.finishLaunch))) s ok = refl
peer-policy (PS.run (GP.run (Sub.jobStep j a))) s ok = refl
peer-policy (PS.run (GP.run (Sub.enqueueCompletion j delay))) s ok = refl
peer-policy (PS.run (GP.run (Sub.deregisterJob j))) s ok = refl
peer-policy (PS.run (GP.run (Sub.protocolResult ref n result))) s ok = refl
peer-policy (PS.run (GP.run (Sub.publishInitiatorResult ref n))) s ok = refl
peer-policy (PS.run (GP.run (Sub.pollPeer ref w))) s ok = refl
peer-policy (PS.run (GP.run (Sub.monitorStep ref a))) s ok = refl
peer-policy (PS.run (GP.run (Sub.monitorFinished ref))) s ok = refl
peer-policy (PS.run (GP.run (Sub.observeInitiatorFailure ref))) s ok = refl
peer-policy (PS.run (GP.handoff w)) s ok = refl
peer-policy (PS.run (GP.beginClose js)) s ok = refl
peer-policy (PS.run (GP.requestCancel)) s ok = refl
peer-policy (PS.run (GP.join)) s ok = refl
peer-policy (PS.run (GP.finishClose)) s ok = refl
peer-policy (PS.run (GP.deliverCancellation err)) s ok = refl
peer-policy (PS.run (GP.deliverOpenCancellation err)) s ok = refl
peer-policy (PS.run (GP.cleanup j a)) s ok = refl
peer-policy (PS.run (GP.bodyUnwound j)) s ok = refl
peer-policy (PS.run (GP.recoverCloseFailure j)) s ok = refl
peer-policy (PS.run (GP.deregisterCancelled j)) s ok = refl
peer-policy (PS.run (GP.publishAsyncResult j)) s ok = refl
peer-policy (PS.forkMonitor j w) s ok = refl
peer-policy (PS.registerMonitor j) s ok = refl
peer-policy (PS.returnEstablishment j) s ok = refl
peer-policy (PS.finishEstablishment j) s ok = refl
peer-policy (PS.monitorException j err) s ok = refl
peer-policy (PS.commitMonitorError j) s ok = refl
peer-policy (PS.finishMonitorError j) s ok = refl
peer-policy (PS.finishMonitor j) s ok = refl
peer-policy (PS.scope a) s ok = refl
peer-policy (PS.beginMonitorClose js) s ok = refl
peer-policy (PS.requestMonitorCancel) s ok = refl
peer-policy (PS.joinMonitor) s ok = refl
peer-policy (PS.finishMonitorClose) s ok = refl
peer-policy (PS.deliverMonitorCancellation err) s ok = refl
peer-policy (PS.deliverBlockedMonitorCancellation err) s ok = refl
peer-policy (PS.monitorBodyUnwound j) s ok = refl
peer-policy (PS.deregisterMonitor j) s ok = refl
peer-policy (PS.publishMonitorResult j) s ok = refl

-- Allowed primitive actions cannot create a call at any foreign worker.
primitive-nf : ∀ a c k {d} → V.ownedOnly (K.coreStep a) ≡ true → O.advance a c ≡ just d → NoForeign c k → NoForeign d k
primitive-nf a c k {d} ok eq held w present foreign = no-present d w (proj₁ after) (proj₂ after) present
  where
  before = not-present c w (λ p → held w p foreign)
  after = primitive-empty a c w
    (λ { _ _ refl → case ok of λ () }) (λ { _ _ refl → case ok of λ () }) eq (proj₁ before) (proj₂ before)

-- Server steps preserve caller keys and the exact CM-free peer context.
server-nf : ∀ a s {t} → K.step (K.serverStep a) s ≡ just t → NF s → NF t
server-nf a s {t} eq held with Keys.server-keys a s eq
... | keys , same = subst (NoForeign (K.source t)) (sym same) (same-source {k = K.context s} keys held)

-- The only source root of a core step is that step itself; notes keep owners.
core-nf : ∀ a s {t} → V.ownedOnly (K.coreStep a) ≡ true → K.step (K.coreStep a) s ≡ just t → NF s → NF t
core-nf a s {t} ok eq held with Keys.core-keys a s eq | keyRoot a in rooted
... | effect , same | nothing = subst (NoForeign (K.source t)) (sym same)
  (same-source {k = K.context s} (subst (λ root → Effect root (K.source s) (K.source t)) rooted effect) held)
... | effect , same | just x with Keys.key-just a rooted
...   | refl , changing with subst (λ root → Effect root (K.source s) (K.source t)) rooted effect
...     | d , raw , keys = subst (NoForeign (K.source t)) (sym same)
  (same-source {k = K.context s} keys (primitive-nf a (K.source s) (K.context s) ok raw held))

-- Actual peer execution keeps its guards and delegates to component proofs.
peer-nf : ∀ a s {t} → K.step (K.peerStep a) s ≡ just t → Reach.Reach s → NF s → NF t
peer-nf a s eq reach held with K.peerOpen s in opened | K.peerAllowed a s in permitted
... | false | _ = case eq of λ ()
... | true | false = case eq of λ ()
... | true | true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → Peer.peer-safe a (K.peers s) (peer-policy a s permitted) advanced
  (proj₁ reach) (proj₂ (proj₂ reach)) held }

-- The guarded shared step preserves both clauses without new reachability input.
step-inv : ∀ a s {t} → V.step′ a s ≡ just t → Inv s → Inv t
step-inv a s {t} eq (reach , held) with V.step-view a s eq
... | ok , original = Reach.step-reach a s original reach , extra a ok original
  where
  -- Select the additional preservation proof by shared action family.
  extra : ∀ a → V.ownedOnly a ≡ true → K.step a s ≡ just t → NF t
  extra (K.serverStep a) ok original = server-nf a s original held
  extra (K.coreStep a) ok original = core-nf a s ok original held
  extra (K.peerStep a) ok original = peer-nf a s original reach held

-- The source initializer's lens gives exactly the empty outbound caller tables.
initial-nf : ∀ c g {s} → K.initial (O.initial c) g ≡ just s → NF s
initial-nf c g initialized with E.initial (O.initial c) in server
... | nothing = case initialized of λ ()
... | just e = case just-injective initialized of λ { refl → subst
  (λ source → NoForeign source (C.capture (PS.initial (O.initial c) g)))
  (sym (ExitFacts.initial-source isBearerClosed (O.initial c) server))
  (Base.empty isBearerClosed isIOManagerError c (C.capture (PS.initial (O.initial c) g))) }

-- Both clauses hold at accepted empty-CM initialization.
initial-inv : ∀ c g {s} → K.initial (O.initial c) g ≡ just s → Inv s
initial-inv c g eq = Reach.initial-reach c g eq , initial-nf c g eq

-- Induction along guarded shared executions is independent of eventual shutdown.
exec-inv : ∀ {s as t} → V.Executes′ s as t → Inv s → Inv t
exec-inv V.done′ held = held
exec-inv (V.next′ {s = s} {a = a} eq rest) held = exec-inv rest (step-inv a s eq held)

-- The initialized variant's frames always have a historical job or monitor owner.
reachable-inv : ∀ c g {s as t} → K.initial (O.initial c) g ≡ just s → V.Executes′ s as t → Inv t
reachable-inv c g initialized path = exec-inv path (initial-inv c g initialized)

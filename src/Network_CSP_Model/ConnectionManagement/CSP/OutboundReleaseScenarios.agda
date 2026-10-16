{-# OPTIONS --guardedness #-}

-- Conditional release fixtures: timer cancellation and over-limit self-pruning.
module ConnectionManagement.CSP.OutboundReleaseScenarios where

open import Data.Bool using (false; true)
import ConnectionManagement.Rules.Pruning as Prune
open import Data.List using (List; []; _∷_; map)
open import Data.Integer using (+_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.Machine as Inbound
open import ConnectionManagement.OutboundMachine
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.CSP.OutboundAdmission as O
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.CSP.Outbound using (Process; trace-intro; Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

caller : WorkerId
caller = ident 20
initialUni : Configuration
initialUni = record O.returned { core = Inbound.replaceWorld (core O.returned)
  (record O.negotiated { cm = record (S.cm O.negotiated)
    { entries = put (ident 0) (S.outboundUni key₀ O.child (ident 0)) (S.entries (S.cm O.negotiated)) } }) }
-- Explicit frames avoid normalizing a nested replay through the dispatcher.
withEntry : S.ConnectionState → Configuration → Configuration
withEntry st c = record c { core = Inbound.replaceWorld (core c)
  (record (Inbound.world (core c)) { cm = record (S.cm (Inbound.world (core c)))
    { entries = put (ident 0) st (S.entries (S.cm (Inbound.world (core c)))) } }) }
at : R.PC → Data.Bool.Bool → Configuration → Configuration
at pc readyFlag c = record c { releasing = (caller , R.frame key₀ pc readyFlag) ∷ [] }
idleWorld termWorld : Configuration
idleWorld = withEntry (S.outboundIdle key₀ O.child (ident 0) unidirectional) initialUni
termWorld = withEntry (S.terminating key₀ O.child nothing) idleWorld
result : R.Result
result = R.success (just (S.terminating key₀ O.child nothing))

pruneInitial : Configuration
pruneInitial = record O.returned { core = record (core O.returned) { promotionHardLimit = 0 } }

t1 : Configuration
t1 = at R.transaction false initialUni

t2 : Configuration
t2 = at (R.count (R.armTimer (ident 0) O.child)) false idleWorld

t3 : Configuration
t3 = at (R.armTimer (ident 0) O.child) false idleWorld

t4 : Configuration
t4 = at (R.waitIdle (ident 0) O.child) false idleWorld

t5 : Configuration
t5 = at (R.waitIdle (ident 0) O.child) true idleWorld

t6 : Configuration
t6 = at (R.timeoutWrite (ident 0) O.child) true idleWorld

t7 : Configuration
t7 = at (R.count (R.cancel O.child (R.complete result))) true termWorld

t8 : Configuration
t8 = at (R.cancel O.child (R.complete result)) true termWorld

t9 : Configuration
t9 = at (R.delivering O.child (R.complete result)) true termWorld

t10 : Configuration
t10 = at (R.complete result) true termWorld

t11 : Configuration
t11 = record termWorld { released = (caller , result) ∷ [] }

tActions : List Action
tActions = (beginRelease caller key₀) ∷ (release caller R.transactionStep) ∷ (release caller R.readCounters) ∷ (release caller R.registerTimer) ∷ (release caller R.expireTimer) ∷ (release caller R.selectWakeup) ∷ (release caller R.commitTimeout) ∷ (release caller R.readCounters) ∷ (release caller R.requestCancellation) ∷ (release caller (R.cancellationDelivered O.child)) ∷ (release caller R.returnResult) ∷ []
tPath : Executes initialUni tActions t11
tPath = next {c₁ = t1} refl (next {c₁ = t2} refl (next {c₁ = t3} refl (next {c₁ = t4} refl (next {c₁ = t5} refl (next {c₁ = t6} refl (next {c₁ = t7} refl (next {c₁ = t8} refl (next {c₁ = t9} refl (next {c₁ = t10} refl (next refl done))))))))))
tTrace : traces (Process initialUni) (map label tActions)
tTrace = trace-intro tPath

pruneResult : R.Result
pruneResult = R.success (just (S.outboundDup key₀ O.child (ident 0) ticking))
pruneWorld : Configuration
pruneWorld = record (withEntry (S.terminated nothing) pruneInitial) { randomGeneration = 2 }
victim : Prune.Candidate
victim = Prune.candidate key₀ (ident 0) O.child 2 false

p1 : Configuration
p1 = at R.transaction false pruneInitial

p2 : Configuration
p2 = at (R.prune (victim ∷ []) pruneResult) false pruneWorld

p3 : Configuration
p3 = at (R.delivering O.child (R.prune [] pruneResult)) false pruneWorld

p4 : Configuration
p4 = at (R.prune [] pruneResult) false pruneWorld

p5 : Configuration
p5 = at (R.count (R.complete pruneResult)) false pruneWorld

p6 : Configuration
p6 = at (R.complete pruneResult) false pruneWorld

p7 : Configuration
p7 = record pruneWorld { released = (caller , pruneResult) ∷ [] }

pActions : List Action
pActions = (beginRelease caller key₀) ∷ (release caller (R.transactionPruning (+ 0 ∷ []))) ∷ (release caller R.requestCancellation) ∷ (release caller (R.cancellationDelivered O.child)) ∷ (release caller R.requestCancellation) ∷ (release caller R.readCounters) ∷ (release caller R.returnResult) ∷ []
pPath : Executes pruneInitial pActions p7
pPath = next {c₁ = p1} refl (next {c₁ = p2} refl (next {c₁ = p3} refl (next {c₁ = p4} refl (next {c₁ = p5} refl (next {c₁ = p6} refl (next refl done))))))
pTrace : traces (Process pruneInitial) (map label pActions)
pTrace = trace-intro pPath

-- Return acknowledges delivery; it does not join the handler or close its socket.
timeout-result : lookup caller (released t11) ≡ just (R.success (just (S.terminating key₀ O.child nothing)))
timeout-result = refl
socket-not-closed-by-release : lookup O.sock (S.sockets (Inbound.world (core t11))) ≡ just (S.handling O.child)
socket-not-closed-by-release = refl
pruned-entry : lookup (ident 0) (S.entries (S.cm (Inbound.world (core p7)))) ≡ just (S.terminated nothing)
pruned-entry = refl
prune-generation : randomGeneration p7 ≡ 2
prune-generation = refl

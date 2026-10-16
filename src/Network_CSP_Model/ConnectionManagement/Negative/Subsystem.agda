{-# OPTIONS --guardedness #-}

-- Integrated endpoint checks and source job-pool parent/child interleaving.
module ConnectionManagement.Negative.Subsystem where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.OutboundGovernor as G
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Subsystem
open import ConnectionManagement.CSP.Subsystem using (Process; trace-intro; refused-extension; Channel; label)
import ConnectionManagement.CSP.GovernorLifecycle as L
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

final-no-established : G.establishedPeers (privateState L.final) ≡ []
final-no-established = refl
final-no-active : G.activePeers (privateState L.final) ≡ []
final-no-active = refl
-- Outbound closure can leave the duplex bearer serving the inbound side.
final-inbound-retained : lookup (ident 0) (S.entries (S.cm (Inbound.world (CM.core (J.cm (world L.final)))))) ≡
  just (S.inboundIdle key₀ L.child (ident 0) duplex)
final-inbound-retained = refl
final-socket-retained : lookup (ident 10) (S.sockets (Inbound.world (CM.core (J.cm (world L.final))))) ≡ just (S.handling L.child)
final-socket-retained = refl
duplicate-completion-refused : advance (enqueueCompletion (ident 3) 0) L.final ≡ nothing
duplicate-completion-refused = refl
no-duplicate-completion : ¬ traces (Process L.c₀)
  (map label (L.schedule ++ (enqueueCompletion (ident 3) 0 ∷ [])))
no-duplicate-completion = refused-extension L.path duplicate-completion-refused

-- Delay the parent's registration while the first child executes and enqueues.
held : Configuration → Configuration
held c = record c { pc = register (ident 0) []; pool = [] }

raceActions : List Action
raceActions = L.a1 ∷ L.a2 ∷ L.a3 ∷ L.a4 ∷ L.a5 ∷ L.a6 ∷ L.a7 ∷ L.a8 ∷ L.a10 ∷ L.a11 ∷ L.a12 ∷ L.a13 ∷ L.a14 ∷ L.a15 ∷ L.a16 ∷ L.a17 ∷ L.a18 ∷ L.a19 ∷ L.a20 ∷ L.a21 ∷ L.a22 ∷ L.a23 ∷ L.a24 ∷ L.a25 ∷ L.a26 ∷ L.a27 ∷ L.a28 ∷ L.a29 ∷ L.a30 ∷ L.a31 ∷ L.a32 ∷ L.a33 ∷ L.a34 ∷ L.a35 ∷ L.a36 ∷ L.a37 ∷ L.a38 ∷ L.a39 ∷ L.a40 ∷ L.a41 ∷ []
racePath : Executes L.c₀ raceActions (held L.c41)
racePath = next {c₁ = L.c1} refl (next {c₁ = L.c2} refl (next {c₁ = L.c3} refl (next {c₁ = L.c4} refl (next {c₁ = L.c5} refl (next {c₁ = L.c6} refl (next {c₁ = L.c7} refl (next {c₁ = L.c8} refl (next {c₁ = held L.c10} refl (next {c₁ = held L.c11} refl (next {c₁ = held L.c12} refl (next {c₁ = held L.c13} refl (next {c₁ = held L.c14} refl (next {c₁ = held L.c15} refl (next {c₁ = held L.c16} refl (next {c₁ = held L.c17} refl (next {c₁ = held L.c18} refl (next {c₁ = held L.c19} refl (next {c₁ = held L.c20} refl (next {c₁ = held L.c21} refl (next {c₁ = held L.c22} refl (next {c₁ = held L.c23} refl (next {c₁ = held L.c24} refl (next {c₁ = held L.c25} refl (next {c₁ = held L.c26} refl (next {c₁ = held L.c27} refl (next {c₁ = held L.c28} refl (next {c₁ = held L.c29} refl (next {c₁ = held L.c30} refl (next {c₁ = held L.c31} refl (next {c₁ = held L.c32} refl (next {c₁ = held L.c33} refl (next {c₁ = held L.c34} refl (next {c₁ = held L.c35} refl (next {c₁ = held L.c36} refl (next {c₁ = held L.c37} refl (next {c₁ = held L.c38} refl (next {c₁ = held L.c39} refl (next {c₁ = held L.c40} refl (next refl done)))))))))))))))))))))))))))))))))))))))

raceTrace : traces (Process L.c₀) (map label raceActions)
raceTrace = trace-intro racePath
registration-required : advance (deregisterJob (ident 0)) (held L.c41) ≡ nothing
registration-required = refl
no-early-deregister : ¬ traces (Process L.c₀)
  (map label (raceActions ++ (deregisterJob (ident 0) ∷ [])))
no-early-deregister = refused-extension racePath registration-required
parent-then-child : Executes (held L.c41)
  (registerJob ∷ deregisterJob (ident 0) ∷ []) L.c42
parent-then-child = next {c₁ = L.c41} refl (next refl done)

-- A queued completion wins over a simultaneous target update. These are local
-- scheduling fixtures, separate from the reachable lifecycle above.
demotion : G.Completion
demotion = G.completion (G.job G.deactivate (remote key₀) (just (ident 0))) G.succeeded 0
pending : Configuration
pending = record L.c₀ { pc = selecting; completions = demotion ∷ []; targetInput = G.targets 0 0 0 }
completion-before-targets : advance selectTargets pending ≡ nothing
completion-before-targets = refl
completion-selected : advance selectCompletion pending ≡
  just (record pending { pc = apply (completion demotion); completions = [] })
completion-selected = refl

-- Retain the source assertion instead of silently accepting a malformed state.
applying : Configuration
applying = record L.c₀ { pc = apply (completion demotion) }
missing-established-asserts : advance (applyAt 0) applying ≡
  just (record applying { pc = completionAssertionFailed demotion })
missing-established-asserts = refl
assertion-cannot-publish : advance publishCounters
  (record applying { pc = completionAssertionFailed demotion }) ≡ nothing
assertion-cannot-publish = refl

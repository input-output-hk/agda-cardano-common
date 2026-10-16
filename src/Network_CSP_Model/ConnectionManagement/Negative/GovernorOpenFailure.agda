{-# OPTIONS --guardedness #-}

-- End-state and refused-extension checks for the reachable OG retry witness.
module ConnectionManagement.Negative.GovernorOpenFailure where

open import Data.Bool using (false)
open import Data.List using ([]; _∷_; _++_; map; take)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.CSP.GovernorOpenFailure as R
import ConnectionManagement.CSP.GovernorLifecycle as L
open import ConnectionManagement.Subsystem
open import ConnectionManagement.CSP.Subsystem using (Process; Channel; label; refused-extension)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- First failure schedules time 5; failure at that retry schedules time 15.
first-failure-state : lookup L.peerAddr (G.knownPeers (privateState R.c25)) ≡
  just (G.known 1 5 nothing false false)
first-failure-state = refl
second-failure-state : lookup L.peerAddr (G.knownPeers (privateState R.c64)) ≡
  just (G.known 2 15 nothing false false)
second-failure-state = refl
no-established-peer : G.establishedPeers (privateState R.c64) ≡ []
no-established-peer = refl
no-promotion-in-progress : G.promotingCold (privateState R.c64) ≡ []
no-promotion-in-progress = refl
reservation-persists : S.mapCell (S.cm (Inbound.world (CM.core (J.cm (world R.c64))))) ≡
  S.full (S.insertLocal L.peerAddr unknownLocal (ident 0) [])
reservation-persists = refl
entry-persists : lookup (ident 0) (S.entries (S.cm (Inbound.world (CM.core (J.cm (world R.c64)))))) ≡
  just S.reservedOutbound
entry-persists = refl
no-first-socket : lookup (ident 10) (S.sockets (Inbound.world (CM.core (J.cm (world R.c64))))) ≡ nothing
no-first-socket = refl
no-retry-socket : lookup (ident 20) (S.sockets (Inbound.world (CM.core (J.cm (world R.c64))))) ≡ nothing
no-retry-socket = refl
retry-outcome : lookup (ident 20) (CM.acquired (J.cm (world R.c64))) ≡ just (C.raised C.connectionExists)
retry-outcome = refl
jobs-deregistered : pool R.c64 ≡ []
jobs-deregistered = refl
completions-consumed : completions R.c64 ≡ []
completions-consumed = refl

backoff-refuses-promotion : advance (selectPolicy (L.peerAddr ∷ [])) R.c31 ≡ nothing
backoff-refuses-promotion = refl
wakeup-cannot-apply-early : advance (applyAt 4) R.c34 ≡ nothing
wakeup-cannot-apply-early = refl
prefix31 : Executes L.c₀ (take 31 R.schedule) R.c31
prefix31 = next {c₁ = L.c1} refl (next {c₁ = L.c2} refl (next {c₁ = L.c3} refl (next {c₁ = L.c4} refl (next {c₁ = L.c5} refl (next {c₁ = L.c6} refl (next {c₁ = L.c7} refl (next {c₁ = L.c8} refl (next {c₁ = L.c9} refl (next {c₁ = L.c10} refl (next {c₁ = L.c11} refl (next {c₁ = L.c12} refl (next {c₁ = L.c13} refl (next {c₁ = R.c14} refl (next {c₁ = R.c15} refl (next {c₁ = R.c16} refl (next {c₁ = R.c17} refl (next {c₁ = R.c18} refl (next {c₁ = R.c19} refl (next {c₁ = R.c20} refl (next {c₁ = R.c21} refl (next {c₁ = R.c22} refl (next {c₁ = R.c23} refl (next {c₁ = R.c24} refl (next {c₁ = R.c25} refl (next {c₁ = R.c26} refl (next {c₁ = R.c27} refl (next {c₁ = R.c28} refl (next {c₁ = R.c29} refl (next {c₁ = R.c30} refl (next refl done))))))))))))))))))))))))))))))
no-early-promotion-trace : ¬ traces (Process L.c₀)
  (map label (take 31 R.schedule ++ (selectPolicy (L.peerAddr ∷ []) ∷ [])))
no-early-promotion-trace = refused-extension prefix31 backoff-refuses-promotion

duplicate-completion-refused : advance (enqueueCompletion (ident 1) 2) R.c64 ≡ nothing
duplicate-completion-refused = refl
no-duplicate-completion-trace : ¬ traces (Process L.c₀)
  (map label (R.schedule ++ (enqueueCompletion (ident 1) 2 ∷ [])))
no-duplicate-completion-trace = refused-extension R.path duplicate-completion-refused

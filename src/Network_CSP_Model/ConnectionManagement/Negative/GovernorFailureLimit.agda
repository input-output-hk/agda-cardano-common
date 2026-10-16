{-# OPTIONS --guardedness #-}

-- Failure-limit boundary and retained CM state after a reachable OG execution.
module ConnectionManagement.Negative.GovernorFailureLimit where

open import Data.Bool using (false)
open import Data.List using ([]; _∷_; _++_; map)
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
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.CSP.GovernorFailureLimit as F
open import ConnectionManagement.Subsystem
open import ConnectionManagement.CSP.Subsystem using (Process; Channel; label; refused-extension)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- The pre-increment count is tested: fifth retained, sixth forgotten.
fifth-retained : lookup L.peerAddr (G.knownPeers (privateState F.c172)) ≡
  just (G.known 5 155 nothing false false)
fifth-retained = refl
sixth-forgotten : G.knownPeers (privateState F.c208) ≡ []
sixth-forgotten = refl
public-also-forgets : G.knownPeers (publicState F.c211) ≡ []
public-also-forgets = refl
no-established : G.establishedPeers (privateState F.c211) ≡ []
no-established = refl
no-progress : G.promotingCold (privateState F.c211) ≡ []
no-progress = refl

-- Forgetting is OG bookkeeping; it does not release the captured CM entry.
reservation-remains : S.mapCell (S.cm (Inbound.world (CM.core (J.cm (world F.c211))))) ≡
  S.full (S.insertLocal L.peerAddr unknownLocal (ident 0) [])
reservation-remains = refl
entry-remains : lookup (ident 0) (S.entries (S.cm (Inbound.world (CM.core (J.cm (world F.c211)))))) ≡
  just S.reservedOutbound
entry-remains = refl
last-job-rejected : lookup (ident 60) (CM.acquired (J.cm (world F.c211))) ≡
  just (C.raised C.connectionExists)
last-job-rejected = refl
no-final-socket : lookup (ident 60) (S.sockets (Inbound.world (CM.core (J.cm (world F.c211))))) ≡ nothing
no-final-socket = refl
no-pool-members : pool F.c211 ≡ []
no-pool-members = refl
no-completions : completions F.c211 ≡ []
no-completions = refl
no-retry-timer : wakeupAt F.c211 ≡ nothing
no-retry-timer = refl

-- The fixed-known-peer profile has no discovery action to replenish this set.
-- These refused events do not classify the whole open process as deadlocked.
no-next-promotion : advance (selectPolicy (L.peerAddr ∷ [])) F.c211 ≡ nothing
no-next-promotion = refl
no-next-promotion-trace : ¬ traces (Process L.c₀)
  (map label (F.schedule ++ (selectPolicy (L.peerAddr ∷ []) ∷ [])))
no-next-promotion-trace = refused-extension F.path no-next-promotion
no-timer-expiry : advance expireWakeup F.c211 ≡ nothing
no-timer-expiry = refl
no-spurious-timer-trace : ¬ traces (Process L.c₀)
  (map label (F.schedule ++ (expireWakeup ∷ [])))
no-spurious-timer-trace = refused-extension F.path no-timer-expiry

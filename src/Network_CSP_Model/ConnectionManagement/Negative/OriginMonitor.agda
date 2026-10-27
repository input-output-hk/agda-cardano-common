{-# OPTIONS --guardedness #-}

-- Contract rejection is distinct from open-machine refusal and source deadlock.
module ConnectionManagement.Negative.OriginMonitor where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (negotiated)
open import ConnectionManagement.Machine using (Action; igStep; handlerPublication; handlerStep; resultWritten)
open import ConnectionManagement.Rules.OriginMonitor
open import ConnectionManagement.CSP.OriginMonitor
open import ConnectionManagement.CSP.OriginMonitorWitness
open import ConnectionManagement.CSP.Process using (Channel; label)
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.Negative.HandlerOrigin as WrongFlow
import ConnectionManagement.Negative.HandlerEstablishment as WrongKey
open import ConnectionManagement.CSP.HandlerLifecycle using (cancelError)
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀; key₁)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

wrong-key : Action
wrong-key = igStep (IG.installHandle (ident 0) G.mid key₁ (G.proto ∷ []) duplex)
wrong-key-refused : step selected wrong-key initial ≡ nothing
wrong-key-refused = refl
no-wrong-key : ¬ traces (Process selected initial) (map label (wrong-key ∷ []))
no-wrong-key = refused-extension {as = []} done wrong-key-refused

uniInstall publishDuplex : Action
uniInstall = igStep (IG.installHandle (ident 0) G.mid key₀ (G.proto ∷ []) unidirectional)
publishDuplex = handlerPublication child₀ (negotiated (ident 0) duplex) resultWritten
uniInstalled : State
uniInstalled = observed WrongFlow.wrongInstalled (awaitingPublication (ticket G.mid (G.proto ∷ []) unidirectional))
uni-path : Executes selected initial (uniInstall ∷ []) uniInstalled
uni-path = next refl done
wrong-flow-refused : step selected publishDuplex uniInstalled ≡ nothing
wrong-flow-refused = refl
no-wrong-flow : ¬ traces (Process selected initial) (map label (uniInstall ∷ publishDuplex ∷ []))
no-wrong-flow = refused-extension uni-path wrong-flow-refused

-- A different handle cannot be substituted at the observed worker's publication.
wrong-handle : Action
wrong-handle = handlerPublication child₀ (negotiated (ident 1) duplex) resultWritten
wrong-handle-refused : step selected wrong-handle installed ≡ nothing
wrong-handle-refused = refl
no-wrong-handle : ¬ traces (Process selected installed) (map label (wrong-handle ∷ []))
no-wrong-handle = refused-extension {as = []} done wrong-handle-refused
publication-before-allocation : step selected publishDuplex initial ≡ nothing
publication-before-allocation = refl
-- Even a preexisting published open state cannot bypass the monitor phase.
attachment-before-observation : step selected (handlerStep child₀ (L.attach cancelError)) (start E.published) ≡ nothing
attachment-before-observation = refl
-- A permissive contract check cannot bypass the underlying freshness guard.
occupied-installation : step selected allocate (start E.installed) ≡ nothing
occupied-installation = refl
repeated-allocation : step selected allocate installed ≡ nothing
repeated-allocation = refl

-- Even unrelated outbound handle allocation is explicitly outside the inbound
-- monitor profile; classification must not fall through to `other`.
outbound-selected-refused : step selected
  (igStep (IG.installOutboundHandle (ident 0) G.mid key₀ (G.proto ∷ []) duplex)) initial ≡ nothing
outbound-selected-refused = refl
outbound-unrelated-refused : step selected
  (igStep (IG.installOutboundHandle (ident 99) (ident 99) key₁ (G.proto ∷ []) unidirectional)) initial ≡ nothing
outbound-unrelated-refused = refl

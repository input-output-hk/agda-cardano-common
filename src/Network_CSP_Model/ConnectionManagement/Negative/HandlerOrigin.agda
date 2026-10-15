{-# OPTIONS --guardedness #-}

-- The open machine accepts inconsistent flow inputs; reference coherence alone
-- does not establish a common negotiated version-data origin.
module ConnectionManagement.Negative.HandlerOrigin where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerOrigin
open import ConnectionManagement.Properties.HandlerEstablishment using (publication-creates; attach-established)
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro)
open import ConnectionManagement.CSP.HandlerOrigin using (origin-reachable)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; cancelError)
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
open import ConnectionManagement.Scenarios.Handshake using (success)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

wrongInstalled wrongPublished wrongAttached : Configuration
wrongInstalled = record E.installed { inboundGovernor = record (inboundGovernor E.installed)
  { execution = record (IG.execution (inboundGovernor E.installed))
    { handles = (ident 0 , M.handleState G.mid (G.proto ∷ []) unidirectional) ∷ [] } } }
wrongPublished = record E.published { inboundGovernor = inboundGovernor wrongInstalled }
wrongAttached = tracked L.monitoring wrongPublished
wrongActions : List Action
wrongActions = igStep (IG.installHandle (ident 0) G.mid key₀ (G.proto ∷ []) unidirectional) ∷
  handlerPublication child₀ success resultWritten ∷ handlerStep child₀ (L.attach cancelError) ∷ []
wrong-path : Executes E.forked wrongActions wrongAttached
wrong-path = next {c₁ = wrongInstalled} refl (next {c₁ = wrongPublished} refl (next refl done))
wrong-csp : Process E.forked ⟹⟨ map label wrongActions ⟩ Process wrongAttached
wrong-csp = exec-intro wrong-path
installed-origin : Origin child₀ (ident 0) G.mid (G.proto ∷ []) unidirectional wrongInstalled
installed-origin = install-origin (ident 0) G.mid (G.proto ∷ []) unidirectional E.forked E.forked-resources refl
-- The old reference-chain property still holds: the key and mux agree.
wrong-reference-chain : TrackedChain child₀ wrongAttached
wrong-reference-chain = attach-established child₀ cancelError wrongPublished
  (publication-creates child₀ (ident 0) G.mid duplex wrongInstalled (prepared installed-origin) refl) refl
-- The published duplex value cannot describe the installed handle's origin.
no-duplex-origin : ¬ Origin child₀ (ident 0) G.mid (G.proto ∷ []) duplex wrongAttached
no-duplex-origin o with descriptor o
... | ()

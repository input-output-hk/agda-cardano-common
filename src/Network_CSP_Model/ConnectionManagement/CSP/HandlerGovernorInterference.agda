{-# OPTIONS --guardedness #-}

-- Release, remote promotion and pruning preserve pre-attachment evidence.
module ConnectionManagement.CSP.HandlerGovernorInterference where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerEstablishment
open import ConnectionManagement.Properties.HandlerGovernorInterference
open import ConnectionManagement.Properties.HandlerConsumerEffects using (ParentAction)
import ConnectionManagement.Properties.HandlerConsumerEffects as Effects
open import ConnectionManagement.Properties.HandlerReferences using (Chain; TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement using (all-exec-preserves)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; cancelError)
import ConnectionManagement.CSP.HandlerEstablishment as Establish
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; key₀)
open import ConnectionManagement.Scenarios.Handshake using (success; info)
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-resources : ∀ {c as P w} → Interference as → Resources w (world c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Resources w (world c′))
raw-resources covered r reach with exec-inv reach
... | c′ , same , path = c′ , same , resources-exec covered path r

raw-prepared : ∀ {c as P w hid mid} → Interference as → Prepared w hid mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Prepared w hid mid (world c′) (inboundGovernor c′))
raw-prepared covered p reach with exec-inv reach
... | c′ , same , path = c′ , same , prepared-exec covered path p

-- Interference lists are restricted; the suffix after attachment is arbitrary.
raw-delayed-attachment : ∀ {w hid mid c P} flow err before after suffix →
  Interference before → Interference after → Prepared w hid mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label (before ++
    (handlerPublication w (negotiated hid flow) resultWritten ∷
      (after ++ (handlerStep w (L.attach err) ∷ suffix)))) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-delayed-attachment {w} {hid} {mid} flow err before after suffix beforeCovered afterCovered prepared reach
  with exec-inv reach
... | c′ , same , path with exec-split before path
...   | c₁ , beforePath , next {c₁ = c₂} published rest with exec-split after rest
...     | c₃ , afterPath , next attached suffixPath = c′ , same ,
  all-exec-preserves suffixPath w (attach-established w err c₃
    (chain-exec afterCovered afterPath
      (publication-creates w hid mid flow c₁ (prepared-exec beforeCovered beforePath prepared) published)) attached)

import ConnectionManagement.Properties.HandlerAllIGInterference as Earlier
import ConnectionManagement.CSP.HandlerIGInterference as Start
import ConnectionManagement.CSP.IGRuntime as Runtime
import ConnectionManagement.CSP.InboundRelease as Release
import ConnectionManagement.CSP.RemoteState as Remote
import ConnectionManagement.CSP.Pruning as Prune
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.RemoteState as RS
open import Data.Integer using (+_)

-- The release fixture has a published promise but no attached lifecycle frame.
release-batch-covered : Interference Release.batchActions
release-batch-covered = more (runtime Earlier.ig) (more (runtime Earlier.ig)
  (more (runtime Earlier.ig) (more (runtime Earlier.ig) (more (runtime Earlier.ig)
  (more (runtime Earlier.ig) (more release empty))))))
release-covered : Interference Release.releaseActions
release-covered = more release (more release (more release (more release
  (more release (more release (more (runtime Earlier.ig) empty))))))
released-prepared : Prepared child₀ (ident 0) G.mid (world Release.published) (inboundGovernor Release.published)
released-prepared = prepared-exec release-covered Release.release-path
  (prepared-exec release-batch-covered Release.batch-path Start.registered-prepared)
release-csp : Process G.registered ⟹⟨ map label (Release.batchActions ++ Release.releaseActions) ⟩ Process Release.published
release-csp = exec-intro (exec-append Release.batch-path Release.release-path)
released-unattached : handlerLifecycles Release.published ≡ []
released-unattached = refl

-- Promotion follows the existing responder-start path; no local input mutation.
promotion-batch-covered : Interference Remote.batchActions
promotion-batch-covered = more (runtime Earlier.ig) (more (runtime Earlier.ig)
  (more (runtime Earlier.ig) (more (runtime Earlier.ig) (more (runtime Earlier.ig)
  (more remoteOp empty)))))
promotion-covered : Interference Remote.promotionActions
promotion-covered = more remoteOp (more remoteOp (more remoteOp (more remoteOp
  (more (runtime Earlier.ig) (more (runtime Earlier.ig) (more (runtime Earlier.ig) empty))))))
promoted-prepared : Prepared child₀ (ident 0) G.mid (world Remote.hotPublished) (inboundGovernor Remote.hotPublished)
promoted-prepared = prepared-exec promotion-covered Remote.promotion-path
  (prepared-exec promotion-batch-covered Remote.batch-path Start.running-prepared)
promotion-csp : Process Runtime.jobRunning ⟹⟨ map label (Remote.batchActions ++ Remote.promotionActions) ⟩ Process Remote.hotPublished
promotion-csp = exec-intro (exec-append Remote.batch-path Remote.promotion-path)

-- Local scored-pruning fixtures. Outbound acquisition reachability is absent.
self-input-prepared : Prepared child₀ (ident 0) G.mid (world Remote.p₀) (inboundGovernor Remote.p₀)
self-input-prepared = record
  { resources = record { original = _; found = refl; entryExists = _ , refl; socketExists = _ , refl }
  ; hd = _; mx = _; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl }
self-pruned-prepared : Prepared child₀ (ident 0) G.mid (world Remote.p₁) (inboundGovernor Remote.p₁)
self-pruned-prepared = prepared-exec (more remoteOp empty) Remote.pruning-path self-input-prepared
self-pruning-csp : Process Remote.p₀ ⟹⟨ map label (remoteStep (RS.transactPruning 0 (+ 0 ∷ [])) ∷ []) ⟩ Process Remote.p₁
self-pruning-csp = exec-intro Remote.pruning-path
multi-input-prepared : Prepared child₀ (ident 0) G.mid (world Prune.multi) (inboundGovernor Prune.multi)
multi-input-prepared = record
  { resources = record { original = _; found = refl; entryExists = _ , refl; socketExists = _ , refl }
  ; hd = _; mx = _; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl }
pruning-covered : Interference Prune.actions
pruning-covered = more remoteOp (more remoteOp (more remoteOp (more remoteOp
  (more remoteOp (more remoteOp (more remoteOp (more remoteOp (more remoteOp
  (more (runtime Earlier.ig) empty)))))))))
pruned-prepared : Prepared child₀ (ident 0) G.mid (world Prune.published) (inboundGovernor Prune.published)
pruned-prepared = prepared-exec pruning-covered Prune.prune-path multi-input-prepared
pruning-csp : Process Prune.multi ⟹⟨ map label Prune.actions ⟩ Process Prune.published
pruning-csp = exec-intro Prune.prune-path
pruned-unattached : handlerLifecycles Prune.published ≡ []
pruned-unattached = refl

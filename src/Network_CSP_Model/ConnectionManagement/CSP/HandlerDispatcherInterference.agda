{-# OPTIONS --guardedness #-}

-- Unrestricted dispatcher traces preserve existing reference evidence.
module ConnectionManagement.CSP.HandlerDispatcherInterference where

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
open import ConnectionManagement.Properties.HandlerDispatcherInterference
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

-- The public endpoints require no action-subset certificate.
raw-all-resources : ∀ {c as P w} → Resources w (world c) → Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Resources w (world c′))
raw-all-resources {as = as} = raw-resources (all-actions as)
raw-all-prepared : ∀ {c as P w hid mid} → Prepared w hid mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Prepared w hid mid (world c′) (inboundGovernor c′))
raw-all-prepared {as = as} = raw-prepared (all-actions as)
raw-all-chain : ∀ {c as P w mid} → Chain w mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Chain w mid (world c′) (inboundGovernor c′))
raw-all-chain ch reach with exec-inv reach
... | c′ , same , path = c′ , same , all-chain path ch

raw-all-delayed-attachment : ∀ {w hid mid c P} flow err before after suffix →
  Prepared w hid mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label (before ++
    (handlerPublication w (negotiated hid flow) resultWritten ∷
      (after ++ (handlerStep w (L.attach err) ∷ suffix)))) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-all-delayed-attachment flow err before after suffix =
  raw-delayed-attachment flow err before after suffix (all-actions before) (all-actions after)

import ConnectionManagement.CSP.HandlerAll as Existing
import ConnectionManagement.CSP.HandlerIGInterference as Start
open import ConnectionManagement.Store using (lookup)

-- Reuse explicit snapshots, removing their optional lifecycle tracking.
-- Every transition is checked again below; no erasure theorem is assumed.
untracked : Configuration → Configuration
untracked c = record c { handlerLifecycles = [] }
secondStart secondEnd : Configuration
secondStart = untracked Existing.consumerEnd
secondEnd = untracked Existing.secondEnd
start-prepared : Prepared child₀ (ident 0) G.mid (world secondStart) (inboundGovernor secondStart)
start-prepared = Start.installed-prepared
second-path : Executes secondStart Existing.secondActions secondEnd
second-path = next {c₁ = untracked Existing.second1} refl (next {c₁ = untracked Existing.second2} refl (next {c₁ = untracked Existing.second3} refl (next {c₁ = untracked Existing.second4} refl (next {c₁ = untracked Existing.second5} refl (next {c₁ = untracked Existing.second6} refl (next {c₁ = untracked Existing.second7} refl (next {c₁ = untracked Existing.second8} refl (next {c₁ = untracked Existing.second9} refl (next {c₁ = untracked Existing.second10} refl (next {c₁ = untracked Existing.second11} refl (next refl done)))))))))))
old-prepared : Prepared child₀ (ident 0) G.mid (world secondEnd) (inboundGovernor secondEnd)
old-prepared = all-prepared second-path start-prepared
second-csp : Process secondStart ⟹⟨ map label Existing.secondActions ⟩ Process secondEnd
second-csp = exec-intro second-path
second-reachable : Σ Configuration (λ c′ → Process secondEnd ≡ Process c′ ×
  Prepared child₀ (ident 0) G.mid (world c′) (inboundGovernor c′))
second-reachable = raw-all-prepared start-prepared second-csp
no-lifecycle-frames : handlerLifecycles secondEnd ≡ []
no-lifecycle-frames = refl
old-result-retained : lookup (ident 0) (handshakeResults (world secondEnd)) ≡ just success
old-result-retained = refl
new-result-present : lookup (ident 1) (handshakeResults (world secondEnd)) ≡ just query
new-result-present = refl

-- The duplicate-write outcome records a blocked writer without replacing data.
faulted : Configuration
faulted = record secondEnd { publicationFaults = child₀ ∷ [] }
duplicate-path : Executes secondEnd (handlerPublication child₀ query duplicateWrite ∷ []) faulted
duplicate-path = next refl done
faulted-prepared : Prepared child₀ (ident 0) G.mid (world faulted) (inboundGovernor faulted)
faulted-prepared = all-prepared duplicate-path old-prepared
duplicate-csp : Process secondEnd ⟹⟨ map label (handlerPublication child₀ query duplicateWrite ∷ []) ⟩ Process faulted
duplicate-csp = exec-intro duplicate-path

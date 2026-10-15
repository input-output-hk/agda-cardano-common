{-# OPTIONS --guardedness #-}

-- Parent/consumer interleavings before publication and before attachment.
module ConnectionManagement.CSP.HandlerInterference where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerEstablishment
open import ConnectionManagement.Properties.HandlerInterference
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

-- The parent publishes its map between fork and handle installation.
mapPublished installed waiting published consumed attached : Configuration
mapPublished = F.snapshot F.unneg (full F.binding) (countPublished (ident 0) (ident 0))
  (handling child₀) [] [] []
installed = record mapPublished { inboundGovernor = inboundGovernor G.installed }
waiting = record F.waiting { inboundGovernor = inboundGovernor G.installed }
published = record F.published { inboundGovernor = inboundGovernor G.installed }
consumed = G.installed
attached = tracked L.monitoring consumed

map-path : Executes Establish.forked (admissionStep w₀ S.putMapBack ∷ []) mapPublished
map-path = next refl done
map-resources : Resources child₀ (world mapPublished)
map-resources = resources-exec (more (parent Effects.publish) empty) map-path Establish.forked-resources
installed-prepared : Prepared child₀ (ident 0) G.mid (world installed) (inboundGovernor installed)
installed-prepared = install-prepares (ident 0) G.mid (G.proto ∷ []) duplex mapPublished map-resources refl

-- Counters interleave after installation, before the negotiated result exists.
before : List Action
before = admissionStep w₀ S.readCounters ∷ []
before-covered : Interference before
before-covered = more (parent Effects.counters) empty
before-path : Executes installed before waiting
before-path = next refl done
waiting-prepared : Prepared child₀ (ident 0) G.mid (world waiting) (inboundGovernor waiting)
waiting-prepared = prepared-exec before-covered before-path installed-prepared

-- All five consumer phases run before the handler attaches its mux.
after : List Action
after = handshakeStep w₀ H.readResult ∷ handshakeStep w₀ H.commitResult ∷
  handshakeStep w₀ H.readResultCounters ∷ handshakeStep w₀ H.enqueueInbound ∷
  handshakeStep w₀ H.returnResult ∷ []
after-covered : Interference after
after-covered = more consumer (more consumer (more consumer (more consumer (more consumer empty))))
after-path : Executes published after consumed
after-path = next {c₁ = read} refl (next {c₁ = committed} refl (next {c₁ = counted} refl
  (next {c₁ = enqueued} refl (next refl done))))
  where
  read = record (F.snapshot F.unneg (full F.binding) (commitHandshake (ident 0) success)
    (handling child₀) F.resultStore [] []) { inboundGovernor = inboundGovernor G.installed }
  committed = record F.committed { inboundGovernor = inboundGovernor G.installed }
  counted = record (F.snapshot F.idle (full F.binding) (notifyInbound info)
    (handling child₀) F.resultStore [] []) { inboundGovernor = inboundGovernor G.installed }
  enqueued = record (F.snapshot F.idle (full F.binding) (returnHandshake (connected info))
    (handling child₀) F.resultStore (info ∷ []) []) { inboundGovernor = inboundGovernor G.installed }

schedule : List Action
schedule = before ++ (handlerPublication child₀ success resultWritten ∷
  (after ++ (handlerStep child₀ (L.attach cancelError) ∷ [])))
schedule-path : Executes installed schedule attached
schedule-path = exec-append before-path (next {c₁ = published} refl (exec-append after-path (next refl done)))
schedule-csp : Process installed ⟹⟨ map label schedule ⟩ Process attached
schedule-csp = exec-intro schedule-path
schedule-reachable : Σ Configuration (λ c′ → Process attached ≡ Process c′ × TrackedChain child₀ c′)
schedule-reachable = raw-delayed-attachment duplex cancelError before after []
  before-covered after-covered installed-prepared schedule-csp

attached-chain : TrackedChain child₀ attached
attached-chain = attach-established child₀ cancelError consumed
  (chain-exec after-covered after-path
    (publication-creates child₀ (ident 0) G.mid duplex waiting waiting-prepared refl)) refl

whole : List Action
whole = Establish.prefix ++ (admissionStep w₀ S.putMapBack ∷
  igStep (IG.installHandle (ident 0) G.mid key₀ (G.proto ∷ []) duplex) ∷ schedule)
whole-csp : Process F.start ⟹⟨ map label whole ⟩ Process attached
whole-csp = exec-intro (exec-append Establish.prefix-path
  (next {c₁ = mapPublished} refl (next {c₁ = installed} refl schedule-path)))

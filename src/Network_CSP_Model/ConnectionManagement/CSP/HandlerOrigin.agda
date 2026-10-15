{-# OPTIONS --guardedness #-}

-- Matched successful source boundaries, with arbitrary dispatcher interleavings.
-- The shared flow parameter is an input contract, not a rule of the open machine.
module ConnectionManagement.CSP.HandlerOrigin where

open import Data.List using ([]; _∷_; _++_; map)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerOrigin
open import ConnectionManagement.Properties.HandlerEstablishment using (publication-creates; attach-established)
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement using (all-exec-preserves)
open import ConnectionManagement.Properties.HandlerDispatcherInterference using (all-chain)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.CSP.HandlerLifecycle using (cancelError)
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-origin : ∀ {w c P} hid mid ps flow err before after suffix (r : Resources w (world c)) →
  Process c ⟹⟨ map label
    (igStep (IG.installHandle hid mid (handlerKey (original r)) ps flow) ∷
      (before ++ (handlerPublication w (negotiated hid flow) resultWritten ∷
        (after ++ (handlerStep w (L.attach err) ∷ suffix))))) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′ × Origin w hid mid ps flow c′)
raw-origin {w} {c} hid mid ps flow err before after suffix r reach with exec-inv reach
... | c′ , same , next {c₁ = installed} allocated remaining with exec-split before remaining
... | c₁ , beforePath , next {c₁ = published} written rest with exec-split after rest
... | c₂ , afterPath , next attached tail = c′ , same ,
  all-exec-preserves tail w
    (attach-established w err c₂
      (all-chain afterPath (publication-creates w hid mid flow c₁
        (prepared (origin-exec beforePath (install-origin hid mid ps flow c r allocated))) written)) attached) ,
  origin-exec remaining (install-origin hid mid ps flow c r allocated)

-- Derive the certificate from actual allocation, then transport it along the
-- established accepted-socket witness. No endpoint descriptor is postulated.
installed-origin : Origin child₀ (ident 0) G.mid (G.proto ∷ []) duplex E.installed
installed-origin = install-origin (ident 0) G.mid (G.proto ∷ []) duplex E.forked E.forked-resources refl
completed-origin : Origin child₀ (ident 0) G.mid (G.proto ∷ []) duplex E.completedState
completed-origin = origin-exec
  (next {c₁ = E.published} {a = handlerPublication child₀ (negotiated (ident 0) duplex) resultWritten} refl
    (next {c₁ = E.attached} {a = handlerStep child₀ (L.attach cancelError)} refl E.suffix-path)) installed-origin
origin-reachable : Σ Configuration (λ c′ → Process E.completedState ≡ Process c′ ×
  TrackedChain child₀ c′ × Origin child₀ (ident 0) G.mid (G.proto ∷ []) duplex c′)
origin-reachable = raw-origin (ident 0) G.mid (G.proto ∷ []) duplex cancelError [] [] E.suffix
  E.forked-resources E.establish-csp

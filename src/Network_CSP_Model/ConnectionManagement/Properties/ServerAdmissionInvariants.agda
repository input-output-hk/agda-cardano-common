{-# OPTIONS --guardedness #-}

-- Existing capture/supply/resource predicates through all Server actions and
-- finite executions. Resources concern stored records, not live ownership.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerAdmissionInvariants
  (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationFacts
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.Properties.ServerAdmissionInvariant as Invariant
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Properties.OutboundRuntimeResources as Resources
import ConnectionManagement.Properties.HandlerResourceFacts as Facts
open import ConnectionManagement.Properties.HandlerResources using (Resources; original)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
private
  module S = Server isBearerClosed
  module Lift = Invariant isBearerClosed
  module N = Publication isBearerClosed

-- Obtain already-proved source executions without normalizing the adapters.
lower-path : ∀ a n {n′} → N.step a n ≡ just n′ →
  Σ (List O.Action) (λ as → O.Executes (N.source n) as (N.source n′))
lower-path a n eq = ExitFacts.machine (PublicationFacts.step-projects isBearerClosed a n eq)
lower-captures : ∀ a n {n′} → N.step a n ≡ just n′ → Capture.Captures (N.source n) → Capture.Captures (N.source n′)
lower-captures a n eq valid = Capture.exec-preserves valid (proj₂ (lower-path a n eq))
lower-supply : ∀ a n {n′} → N.step a n ≡ just n′ → Supply.Valid (N.source n) → Supply.Valid (N.source n′)
lower-supply a n eq valid = Supply.exec-preserves valid (proj₂ (lower-path a n eq))

-- Initializer evidence supplies the actual initial source, without new bounds.
initial-source : ∀ c {s} → S.initial c ≡ just s → S.source s ≡ c
initial-source c eq with Shared.admissions (Machine.world (O.core c)) |
  Shared.sockets (Machine.world (O.core c)) | N.initial c in initialized
... | [] | [] | just n = case just-injective eq of λ { refl → PublicationFacts.initial-source isBearerClosed c initialized }
... | _ ∷ _ | _ | _ = case eq of λ ()
... | [] | _ ∷ _ | _ = case eq of λ ()
... | [] | [] | nothing = case eq of λ ()

-- Admission/socket writes leave acquisition frames and entry/promise bounds
-- unchanged. These facts do not assume absence of pending outbound callers.
admit-captures : ∀ w req c → Capture.Captures c → Capture.Captures (Lift.admitSource w req c)
admit-captures w req c valid = valid
socket-captures : ∀ sock owner c → Capture.Captures c → Capture.Captures (Lift.socketSource sock owner c)
socket-captures sock owner c valid = valid
admit-supply : ∀ w req c → Supply.Valid c → Supply.Valid (Lift.admitSource w req c)
admit-supply w req c valid = valid
socket-supply : ∀ sock owner c → Supply.Valid c → Supply.Valid (Lift.socketSource sock owner c)
socket-supply sock owner c valid = valid
private
  module Captures = Lift.Lift Capture.Captures lower-captures admit-captures socket-captures
  module Bounds = Lift.Lift Supply.Valid lower-supply admit-supply socket-supply

-- The public statements retain the old predicates and their initial premises.
captures-step : ∀ a s {t} → S.step a s ≡ just t → Capture.Captures (S.source s) → Capture.Captures (S.source t)
captures-step = Captures.step-preserves
captures-exec : ∀ {s as t} → S.Executes s as t → Capture.Captures (S.source s) → Capture.Captures (S.source t)
captures-exec = Captures.exec-preserves
from-initial-captures : ∀ {c start as t} → S.initial (O.initial c) ≡ just start → S.Executes start as t →
  Capture.Captures (S.source t)
from-initial-captures {c} init path = Captures.from-source (initial-source (O.initial c) init) path (Capture.initial-valid c)
supply-step : ∀ a s {t} → S.step a s ≡ just t → Supply.Valid (S.source s) → Supply.Valid (S.source t)
supply-step = Bounds.step-preserves
supply-exec : ∀ {s as t} → S.Executes s as t → Supply.Valid (S.source s) → Supply.Valid (S.source t)
supply-exec = Bounds.exec-preserves
from-initial-supply : ∀ {c start as t} → S.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) →
  S.Executes start as t → Supply.Valid (S.source t)
from-initial-supply {c} init bounded path = Bounds.from-source (initial-source (O.initial c) init) path (Capture.initial-valid c , bounded)

-- Fix the exact original descriptor throughout the induction. Socket writes
-- retain its stored identity even when the owner/close outcome changes.
module For (q : WorkerId) (captured : Shared.HandlerStart) where
  Valid : O.Configuration → Set
  Valid c = Facts.Facts q captured (Machine.world (O.core c))
  admit-resources : ∀ w req c → Valid c → Valid (Lift.admitSource w req c)
  admit-resources w req c valid = Facts.socket-write (Shared.socketRef req) (Shared.admitting w)
    (Machine.world (O.core c)) valid
  socket-resources : ∀ sock owner c → Valid c → Valid (Lift.socketSource sock owner c)
  socket-resources sock owner c valid = Facts.socket-write sock owner (Machine.world (O.core c)) valid
  lower-resources : ∀ a n {n′} → N.step a n ≡ just n′ → Valid (N.source n) → Valid (N.source n′)
  lower-resources a n eq valid = Resources.For.exec-preserves q captured valid (proj₂ (lower-path a n eq))
  open Lift.Lift Valid lower-resources admit-resources socket-resources
    public using (step-preserves; exec-preserves)

-- No supply, uniqueness, ownership or scheduling premise is added to Resources.
resources-step : ∀ a s {t q} → S.step a s ≡ just t → Resources q (S.shared s) → Resources q (S.shared t)
resources-step a s {q = q} eq resources = Facts.to-resources
  (For.step-preserves q (original resources) a s eq (Facts.from-resources resources))
resources-exec : ∀ {s as t q} → S.Executes s as t → Resources q (S.shared s) → Resources q (S.shared t)
resources-exec {q = q} path resources = Facts.to-resources
  (For.exec-preserves q (original resources) path (Facts.from-resources resources))

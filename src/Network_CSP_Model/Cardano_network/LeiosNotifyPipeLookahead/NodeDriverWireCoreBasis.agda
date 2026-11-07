{-# OPTIONS --safe #-}

-- Restrict only newly supplied eligible offers; existing queued/pending values
-- and all original node guards remain untouched, including for arbitrary states.
open import Data.List using (List)
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBasis
  (Notification : Set) (basis : List Notification) where

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc; acc)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreScheduling Notification as Scheduling

-- A genuine source offer must name a basis value; no other source rule is restricted.
Allowed : ∀ {s t} → Core.Tau s t → Set
Allowed (Core.offered {msg = value} _ _) = value ∈ basis
Allowed (Core.operational _) = ⊤
Allowed (Core.handled _) = ⊤
Allowed (Core.rejected _) = ⊤

-- The original transition evidence is retained rather than copying or weakening its guards.
Tau : Core.State → Core.State → Set
Tau s t = Σ[ proof ∈ Core.Tau s t ] Allowed proof

-- Visible packets and actor identities keep exactly the original core source rules.
Visible : Core.State → D.Event → Core.State → Set
Visible = Core.Visible

-- Membership evidence never changes the source or target of a hidden transition.
sound-tau : ∀ {s t} → Tau s t → Core.Tau s t
sound-tau = proj₁

-- Finite restricted executions retain every wire occurrence and original endpoint.
data Run : Core.State → List D.Event → Core.State → Set where
  stop : ∀ {s} → Run s [] s
  internal : ∀ {s t u rows} → Tau s t → Run t rows u → Run s rows u
  visible : ∀ {s t u row rows} → Visible s row t → Run t rows u → Run s (row ∷ rows) u

-- Every restricted execution is an actual unrestricted node-core run at the same states.
sound : ∀ {s rows t} → Run s rows t → Core.Run s rows t
sound stop = Core.stop
sound (internal proof rest) = Core.internal (sound-tau proof) (sound rest)
sound (visible proof rest) = Core.visible proof (sound rest)

-- Hidden accessibility is preserved by the subrelation, without a finite state graph.
from-core : ∀ s → Acc (λ t s → Core.Tau s t) s → Acc (λ t s → Tau s t) s
from-core s (acc smaller) = acc λ {t} proof → from-core t (smaller (sound-tau proof))

-- Every restricted state inherits the already checked combined scheduling/credit/failure measure.
tau-accessible : ∀ s → Acc (λ t s → Tau s t) s
tau-accessible s = from-core s (Scheduling.tau-accessible s)

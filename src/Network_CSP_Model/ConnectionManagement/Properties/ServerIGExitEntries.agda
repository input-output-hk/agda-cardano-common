{-# OPTIONS --guardedness #-}

-- Any stored entry stays present across the selected Server/IG adapter. This
-- also retains detached governor cleanup captures during Server interference.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerIGExitEntries
  (isBearerClosed : ErrorId → Bool) where

open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (EntryId)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.OutboundWorldInvariant as World
import ConnectionManagement.Properties.StateRetention as Retention
import ConnectionManagement.Properties.IGTableRetention as Tables
import ConnectionManagement.Properties.ServerAdmissionInvariant as ServerLift
import ConnectionManagement.Properties.ServerAdmissionInvariants as ServerFacts
import ConnectionManagement.Properties.ServerIGExit as ExitLift
open import ConnectionManagement.Properties.Entries using (Present)
private
  module E = Exit isBearerClosed
  module N = Publication isBearerClosed

module Entry (e : EntryId) where
  Predicate : S.State → IG.Runtime → Set
  Predicate world ig = Present e (S.entries (S.cm world))
  stable : ∀ {s t ig next} → Retention.Retains s t → Tables.Retains ig next →
    Predicate s ig → Predicate t next
  stable keeps tables = Retention.entriesRetained keeps e
  private
    module Raw = World.Lift Predicate stable
  Valid : O.Configuration → Set
  Valid c = Present e (S.entries (S.cm (I.world (O.core c))))
  lower : ∀ a n {t} → N.step a n ≡ just t → Valid (N.source n) → Valid (N.source t)
  lower a n eq valid = Raw.exec-preserves valid
    (proj₂ (ServerFacts.lower-path isBearerClosed a n eq))
  private
    module Server = ServerLift.Lift isBearerClosed Valid lower
      (λ w req c valid → valid) (λ sock owner c valid → valid)
    module Lift = ExitLift.Lift isBearerClosed Valid Server.step-preserves (λ c valid → valid)
  step-preserves : ∀ a s {t} → E.step a s ≡ just t → Valid (E.source s) → Valid (E.source t)
  step-preserves = Lift.step-preserves

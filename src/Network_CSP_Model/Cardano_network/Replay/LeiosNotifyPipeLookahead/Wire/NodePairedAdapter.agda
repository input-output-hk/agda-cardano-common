{-# OPTIONS --guardedness #-}

-- Full node-policy replay reuses the lossless endpoint validator without a generic-policy fallback.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodePairedAdapter where

open import Data.Empty using (⊥)
open import Data.List using (List; [])
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (Notification; notificationEq; votes)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverDecide Notification notificationEq (votes []) as Source
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as Existing
open Existing public using (Input; present; Valid; Adapted; Side; clientInput; serverInput;
  Failure; at; side; position; reason; translate; no-row-loss; client-roundtrip; server-roundtrip)

-- Each accepted summary position has its exact typed row and an unrestricted full node-policy run.
Accepted : Log.Role → Input → Log.Role → Input → Set
Accepted cr ci sr si = Σ[ client ∈ List Rows.ClientRow ] Σ[ server ∈ List Rows.ServerRow ]
  (Valid cr ci sr si client server × Source.SourceTrace client server)

-- Unique existing encodings transport the full-policy source refutation across every valid adaptation.
exclude : ∀ {cr ci sr si client server} → Valid cr ci sr si client server →
  (Source.SourceTrace client server → ⊥) → Accepted cr ci sr si → ⊥
exclude valid absent (otherClient , otherServer , otherValid , source) with Existing.unique valid otherValid
... | refl , refl = absent source

-- Validation failure, exhaustive source rejection and acceptance retain separate evidence.
data Verdict (cr : Log.Role) (ci : Input) (sr : Log.Role) (si : Input) : Set where
  invalidInput : Failure → (Adapted cr ci sr si → ⊥) → Verdict cr ci sr si
  protocolRejected : (client : List Rows.ClientRow) (server : List Rows.ServerRow) →
    Valid cr ci sr si client server → (Source.SourceTrace client server → ⊥) →
    (Accepted cr ci sr si → ⊥) → Verdict cr ci sr si
  accepted : Accepted cr ci sr si → Verdict cr ci sr si

-- Normalization is shared; the chosen source decision always uses the full node queue and client policy.
check : (cr : Log.Role) (ci : Input) (sr : Log.Role) (si : Input) → Verdict cr ci sr si
check cr ci sr si with translate cr ci sr si
... | inj₁ (failure , absent) = invalidInput failure absent
... | inj₂ (client , server , valid) with Source.decide client server
...   | yes source = accepted (client , server , valid , source)
...   | no absent = protocolRejected client server valid absent (exclude valid absent)

-- A negative result refutes all exact normalized full-policy witnesses, never a resource budget.
decide : (cr : Log.Role) (ci : Input) (sr : Log.Role) (si : Input) → Dec (Accepted cr ci sr si)
decide cr ci sr si with check cr ci sr si
... | accepted witness = yes witness
... | invalidInput failure absent = no λ { (client , server , valid , source) → absent (client , server , valid) }
... | protocolRejected client server valid absent impossible = no impossible

-- Fully parsed summaries keep their explicit endpoint roles and one event per supplied position.
check-normalized : (cr : Log.Role) (client : List Log.E) (sr : Log.Role) (server : List Log.E) →
  Verdict cr (present client) sr (present server)
check-normalized cr client sr server = check cr (present client) sr (present server)

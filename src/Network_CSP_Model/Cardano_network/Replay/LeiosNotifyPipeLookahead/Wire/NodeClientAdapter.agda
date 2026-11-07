{-# OPTIONS --guardedness #-}

-- Lossless existing client rows checked against the explicitly named node-control policy.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodeClientAdapter where

open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (notificationEq)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Payloads.Notification as W
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Schema
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodeClientPolicy Payloads.Notification notificationEq as Policy
open Schema public using
  (Input; present; Rows; empty; linked; Valid; Adapted; Failure; position; reason;
   Reason; wrongRole; wrongAgency; unparsedOrUnsupported; at;
   encode; decode; decode-encode; encode-decoded; no-row-loss; roundtrip;
   normalized-roundtrip; rows-unique; translate)

-- Acceptance retains every validated input row and an independent existing node-control run.
Accepted : Log.Role → Input → Set
Accepted role input = Σ[ rows ∈ List W.Wire ]
  (Valid role input rows × Policy.SourceTrace rows)

-- Exact mapping uniqueness transports policy rejection without dropping failed or repeated rows.
exclude : ∀ {role input} rows → Valid role input rows →
  (Policy.SourceTrace rows → ⊥) → Accepted role input → ⊥
exclude rows (_ , valid) absent (other , (_ , otherValid) , source) =
  absent (subst Policy.SourceTrace (sym (rows-unique valid otherValid)) source)

-- Input failures and exhaustive source-language rejection carry distinct refutations.
data Verdict (role : Log.Role) (input : Input) : Set where
  invalidInput : Failure → (Adapted role input → ⊥) → Verdict role input
  protocolRejected : (rows : List W.Wire) → Valid role input rows →
    (Policy.SourceTrace rows → ⊥) → (Accepted role input → ⊥) → Verdict role input
  accepted : Accepted role input → Verdict role input

-- Existing role/agency/schema validation precedes the exact node-control decision.
check : (role : Log.Role) (input : Input) → Verdict role input
check role input with translate role input
... | inj₁ (failure , absent) = invalidInput failure absent
... | inj₂ (rows , valid) with Policy.decide-source rows
...   | yes source = accepted (rows , valid , source)
...   | no absent = protocolRejected rows valid absent (exclude rows valid absent)

-- A negative result excludes every exact normalized-row and node-control witness.
decide : (role : Log.Role) (input : Input) → Dec (Accepted role input)
decide role input with check role input
... | accepted witness = yes witness
... | invalidInput _ absent = no λ { (rows , valid , _) → absent (rows , valid) }
... | protocolRejected _ _ _ absent = no absent

-- Typed normalized rows use the same lossless parser-outcome wrapper as the generic client.
check-normalized : (role : Log.Role) (events : List Log.E) → Verdict role (present events)
check-normalized role events = check role (present events)

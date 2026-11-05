{-# OPTIONS --guardedness #-}

-- Lossless normalized client rows reuse the server payload schema with opposite agency.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Payloads.Notification as W
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as SW
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Schema
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientQuotient Payloads.Notification ⊤ as Quotient

-- Agency reversal retains the exact message value and every summary field.
flip : Log.E → Log.E
flip (Log.Send , message) = Log.Recv , message
flip (Log.Recv , message) = Log.Send , message

-- Reversing direction twice recovers the exact original normalized row.
flip-involutive : ∀ event → flip (flip event) ≡ event
flip-involutive (Log.Send , _) = refl
flip-involutive (Log.Recv , _) = refl

-- The two wire alphabets share message shapes without sharing their transition languages.
toServer : W.Wire → SW.Wire
toServer W.request = SW.request
toServer W.quit = SW.quit
toServer W.done = SW.done
toServer (W.reply value) = SW.reply value

-- Structural conversion never reconstructs or abstracts a notification payload.
fromServer : SW.Wire → W.Wire
fromServer SW.request = W.request
fromServer SW.quit = W.quit
fromServer SW.done = W.done
fromServer (SW.reply value) = W.reply value

-- This cast preserves every selected client wire value exactly.
client-cast : ∀ row → fromServer (toServer row) ≡ row
client-cast W.request = refl
client-cast W.quit = refl
client-cast W.done = refl
client-cast (W.reply _) = refl

-- The reverse cast is equally exact on all server-shaped values.
server-cast : ∀ row → toServer (fromServer row) ≡ row
server-cast SW.request = refl
server-cast SW.quit = refl
server-cast SW.done = refl
server-cast (SW.reply _) = refl

-- Reuse all notification field mappings; only role agency changes.
encode : W.Wire → Log.E
encode row = flip (Schema.encode (toServer row))

-- Wrong client agency remains a failed decode instead of becoming an erased callback.
decode : Log.E → Maybe W.Wire
decode event = Maybe.map fromServer (Schema.decode (flip event))

-- The shared exact schema and reversible casts provide the complete value retraction.
decode-encode : ∀ row → decode (encode row) ≡ just row
decode-encode row rewrite flip-involutive (Schema.encode (toServer row)) |
  Schema.decode-encode (toServer row) | client-cast row = refl

-- Successful decoding reconstructs the exact original input direction and payload fields.
encode-decoded : ∀ {event row} → decode event ≡ just row → encode row ≡ event
encode-decoded {event} {row} same with Schema.decode (flip event) in found | same
... | nothing | ()
... | just source | refl rewrite server-cast source =
  trans (cong flip (Schema.encode-decoded found)) (flip-involutive event)

-- A missing decode cannot have any hidden exact encoding witness.
decode-missing : ∀ {event row} → decode event ≡ nothing → encode row ≡ event → ⊥
decode-missing {row = row} absent same
  with trans (sym (decode-encode row)) (trans (cong decode same) absent)
... | ()

-- Exact typed wire values cannot collapse under normalized client encoding.
encode-injective : ∀ {a b} → encode a ≡ encode b → a ≡ b
encode-injective {a} {b} same = just-injective
  (trans (sym (decode-encode a)) (trans (cong decode same) (decode-encode b)))

-- Parsing outcomes stay present; Nothing means unparsed/unsupported input, not an absent wire event.
Input : Set
Input = List (Maybe Log.E)

-- No textual parsing is performed here; upstream lexical/schema failures must remain Nothing.
present : List Log.E → Input
present = map just

-- Each retained input row has exactly one target row with an independent exact encoding equation.
data Rows : Input → List W.Wire → Set where
  empty : Rows [] []
  linked : ∀ {event input row rows} → encode row ≡ event → Rows input rows →
    Rows (just event ∷ input) (row ∷ rows)

-- Every successfully adapted row remains in its original ordered position.
no-row-loss : ∀ {input rows} → Rows input rows → length rows ≡ length input
no-row-loss empty = refl
no-row-loss (linked _ rest) = cong suc (no-row-loss rest)

-- This full re-encoding equation also retains optional values, vote order and duplicates.
roundtrip : ∀ {input rows} → Rows input rows → map (λ row → just (encode row)) rows ≡ input
roundtrip empty = refl
roundtrip (linked same rest) = cong₂ _∷_ (cong just same) (roundtrip rest)

-- Ordinary normalized rows enjoy the same exact retraction without a Maybe wrapper.
normalized-roundtrip : ∀ {events rows} → Rows (present events) rows → map encode rows ≡ events
normalized-roundtrip {[]} empty = refl
normalized-roundtrip {_ ∷ _} (linked same rest) = cong₂ _∷_ same (normalized-roundtrip rest)

-- A single input list cannot adapt to different values or a different order of wire rows.
rows-unique : ∀ {input a b} → Rows input a → Rows input b → a ≡ b
rows-unique empty empty = refl
rows-unique (linked first rest) (linked second later) =
  cong₂ _∷_ (encode-injective (trans first (sym second))) (rows-unique rest later)

-- Client role is part of validation even for empty input.
Valid : Log.Role → Input → List W.Wire → Set
Valid role input rows = role ≡ Log.client × Rows input rows

-- Adaptation witnesses no protocol success; they certify only role, agency and lossless summary mapping.
Adapted : Log.Role → Input → Set
Adapted role input = Σ[ rows ∈ List W.Wire ] Valid role input rows

-- Error classes retain the offending normalized row when direction/agency is wrong.
data Reason : Set where
  wrongRole : Log.Role → Reason
  wrongAgency : Log.E → Reason
  unparsedOrUnsupported : Reason

-- Positions are zero-based input indices, not fabricated source-file/thread coordinates.
record Failure : Set where
  constructor at
  field
    position : ℕ
    reason : Reason
open Failure public

-- Internal normalization returns either a located refutation or a complete row-by-row witness.
Walk : Input → Set
Walk input = (Failure × (∀ {rows} → Rows input rows → ⊥)) ⊎ (Σ[ rows ∈ List W.Wire ] Rows input rows)

-- Validate left to right, preserving the first parse or agency failure instead of dropping it.
walk : (input : Input) → Walk input
walk [] = inj₂ ([] , empty)
walk (nothing ∷ input) = inj₁ (at 0 unparsedOrUnsupported , λ ())
walk (just event ∷ input) with decode event in found
... | nothing = inj₁ (at 0 (wrongAgency event) ,
  λ { (linked {row = row} same rest) → decode-missing {row = row} found same })
... | just row with walk input
...   | inj₁ (at index reason , absent) = inj₁ (at (suc index) reason , λ { (linked _ rest) → absent rest })
...   | inj₂ (rows , rest) = inj₂ (row ∷ rows , linked (encode-decoded found) rest)

-- Wrong role and unparsed/unsupported input stay distinguishable from a later protocol rejection.
translate : (role : Log.Role) (input : Input) →
  (Failure × (Adapted role input → ⊥)) ⊎ Adapted role input
translate Log.server input = inj₁ (at 0 (wrongRole Log.server) , λ { (_ , () , _) })
translate Log.client input with walk input
... | inj₁ (failure , absent) = inj₁ (failure , λ { (_ , _ , rows) → absent rows })
... | inj₂ (rows , valid) = inj₂ (rows , refl , valid)

-- Acceptance retains every input row and a concrete detailed-source trace under generic successful unit-return callbacks.
Accepted : Log.Role → Input → Set
Accepted role input = Σ[ rows ∈ List W.Wire ]
  (Valid role input rows × Quotient.SourceTrace rows)

-- Exact mapping uniqueness transports exhaustive source rejection back to all normalized witnesses.
exclude : ∀ {role input} rows → Valid role input rows →
  (Quotient.SourceTrace rows → ⊥) → Accepted role input → ⊥
exclude rows (_ , valid) absent (other , (_ , otherValid) , source) =
  absent (subst (Quotient.SourceTrace) (sym (rows-unique valid otherValid)) source)

-- Verdicts separate invalid input from a source-language refutation; acceptance includes its witness.
data Verdict (role : Log.Role) (input : Input) : Set where
  invalidInput : Failure → (Adapted role input → ⊥) → Verdict role input
  protocolRejected : (rows : List W.Wire) → Valid role input rows →
    (Quotient.SourceTrace rows → ⊥) → (Accepted role input → ⊥) → Verdict role input
  accepted : Accepted role input → Verdict role input

-- The backend is the proved total client quotient; no fuel cutoff or unobserved row is introduced.
check : (role : Log.Role) (input : Input) → Verdict role input
check role input with translate role input
... | inj₁ (failure , absent) = invalidInput failure absent
... | inj₂ (rows , valid) with Quotient.decide-source tt rows
...   | yes source = accepted (rows , valid , source)
...   | no absent = protocolRejected rows valid absent (exclude rows valid absent)

-- The public decision refutes all matching input/source witnesses when rejection occurs.
decide : (role : Log.Role) (input : Input) → Dec (Accepted role input)
decide role input with check role input
... | accepted witness = yes witness
... | invalidInput failure absent = no λ { (rows , valid , source) → absent (rows , valid) }
... | protocolRejected rows valid absent impossible = no impossible

-- Typed normalized events can be checked directly without exposing the parser-outcome wrapper.
check-normalized : (role : Log.Role) (events : List Log.E) →
  Verdict role (present events)
check-normalized role events = check role (present events)

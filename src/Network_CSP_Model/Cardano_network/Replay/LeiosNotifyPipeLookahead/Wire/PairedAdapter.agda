{-# OPTIONS --guardedness #-}

-- Lossless validation precedes exhaustive compatibility of two fresh normalized endpoint prefixes.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Properties using (length-map; map-∘)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (notificationEq)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Payloads.Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Payloads.Notification ⊤ as R
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Payloads.Notification as CW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as SW
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as C
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Srv
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Payloads.Notification notificationEq (Payloads.votes []) as Source

-- Both endpoint validators consume exactly the same parser-outcome schema.
Input : Set
Input = C.Input

-- Typed normalized input remains present at every supplied position.
present : List Log.E → Input
present = C.present

-- Agency-preserving structural injection reuses exact selected packet values.
clientRow : CW.Wire → R.ClientRow
clientRow CW.request = R.sendCommand D.request
clientRow CW.quit = R.sendCommand D.quit
clientRow CW.done = R.receiveResponse D.done
clientRow (CW.reply value) = R.receiveResponse (D.reply value)

-- Typed endpoint rows recover precisely their original local wire shape.
clientWire : R.ClientRow → CW.Wire
clientWire (R.sendCommand D.request) = CW.request
clientWire (R.sendCommand D.quit) = CW.quit
clientWire (R.receiveResponse D.done) = CW.done
clientWire (R.receiveResponse (D.reply value)) = CW.reply value

-- No wire value is lost by passing through the paired typed alphabet.
client-wire-roundtrip : ∀ row → clientWire (clientRow row) ≡ row
client-wire-roundtrip CW.request = refl
client-wire-roundtrip CW.quit = refl
client-wire-roundtrip CW.done = refl
client-wire-roundtrip (CW.reply value) = refl

-- The reverse direction is exact for every typed paired row.
client-row-roundtrip : ∀ row → clientRow (clientWire row) ≡ row
client-row-roundtrip (R.sendCommand D.request) = refl
client-row-roundtrip (R.sendCommand D.quit) = refl
client-row-roundtrip (R.receiveResponse D.done) = refl
client-row-roundtrip (R.receiveResponse (D.reply value)) = refl

-- Structural list retraction preserves order and duplicate occurrences.
client-wires : ∀ rows → map clientWire (map clientRow rows) ≡ rows
client-wires [] = refl
client-wires (row ∷ rows) = cong₂ _∷_ (client-wire-roundtrip row) (client-wires rows)

-- Structural list retraction preserves order and duplicate occurrences.
client-rows : ∀ rows → map clientRow (map clientWire rows) ≡ rows
client-rows [] = refl
client-rows (row ∷ rows) = cong₂ _∷_ (client-row-roundtrip row) (client-rows rows)

-- Agency-preserving structural injection reuses exact selected packet values.
serverRow : SW.Wire → R.ServerRow
serverRow SW.request = R.receiveCommand D.request
serverRow SW.quit = R.receiveCommand D.quit
serverRow SW.done = R.sendResponse D.done
serverRow (SW.reply value) = R.sendResponse (D.reply value)

-- Typed endpoint rows recover precisely their original local wire shape.
serverWire : R.ServerRow → SW.Wire
serverWire (R.receiveCommand D.request) = SW.request
serverWire (R.receiveCommand D.quit) = SW.quit
serverWire (R.sendResponse D.done) = SW.done
serverWire (R.sendResponse (D.reply value)) = SW.reply value

-- No wire value is lost by passing through the paired typed alphabet.
server-wire-roundtrip : ∀ row → serverWire (serverRow row) ≡ row
server-wire-roundtrip SW.request = refl
server-wire-roundtrip SW.quit = refl
server-wire-roundtrip SW.done = refl
server-wire-roundtrip (SW.reply value) = refl

-- The reverse direction is exact for every typed paired row.
server-row-roundtrip : ∀ row → serverRow (serverWire row) ≡ row
server-row-roundtrip (R.receiveCommand D.request) = refl
server-row-roundtrip (R.receiveCommand D.quit) = refl
server-row-roundtrip (R.sendResponse D.done) = refl
server-row-roundtrip (R.sendResponse (D.reply value)) = refl

-- Structural list retraction preserves order and duplicate occurrences.
server-wires : ∀ rows → map serverWire (map serverRow rows) ≡ rows
server-wires [] = refl
server-wires (row ∷ rows) = cong₂ _∷_ (server-wire-roundtrip row) (server-wires rows)

-- Structural list retraction preserves order and duplicate occurrences.
server-rows : ∀ rows → map serverRow (map serverWire rows) ≡ rows
server-rows [] = refl
server-rows (row ∷ rows) = cong₂ _∷_ (server-row-roundtrip row) (server-rows rows)

-- Both declared roles and every ordered input position carry their exact mapping witness.
Valid : Log.Role → Input → Log.Role → Input → List R.ClientRow → List R.ServerRow → Set
Valid cr ci sr si client server = C.Valid cr ci (map clientWire client) × Srv.Valid sr si (map serverWire server)

-- Adaptation by itself asserts no protocol behavior.
Adapted : Log.Role → Input → Log.Role → Input → Set
Adapted cr ci sr si = Σ[ client ∈ List R.ClientRow ] Σ[ server ∈ List R.ServerRow ] Valid cr ci sr si client server

-- Client validation transfers across the exact structural injection without re-parsing fields.
client-valid : ∀ {role input rows} → C.Valid role input rows → C.Valid role input (map clientWire (map clientRow rows))
client-valid {role} {input} {rows} valid = subst (C.Valid role input) (sym (client-wires rows)) valid

-- Server validation uses the corresponding exact structural retraction.
server-valid : ∀ {role input rows} → Srv.Valid role input rows → Srv.Valid role input (map serverWire (map serverRow rows))
server-valid {role} {input} {rows} valid = subst (Srv.Valid role input) (sym (server-wires rows)) valid

-- Each endpoint retains one row per supplied parser outcome, even for repeated messages.
no-row-loss : ∀ {cr ci sr si client server} → Valid cr ci sr si client server →
  length client ≡ length ci × length server ≡ length si
no-row-loss {client = client} {server} ((_ , cv) , (_ , sv)) =
  trans (sym (length-map clientWire client)) (C.no-row-loss cv) ,
  trans (sym (length-map serverWire server)) (Srv.no-row-loss sv)

-- Every client input field is recovered, including optional announcements and vote duplicates.
client-roundtrip : ∀ {cr ci sr si client server} → Valid cr ci sr si client server →
  map (λ row → just (C.encode (clientWire row))) client ≡ ci
client-roundtrip {client = client} ((_ , valid) , _) = trans (map-∘ client) (C.roundtrip valid)

-- The server input enjoys the same exact complete-summary re-encoding equation.
server-roundtrip : ∀ {cr ci sr si client server} → Valid cr ci sr si client server →
  map (λ row → just (Srv.encode (serverWire row))) server ≡ si
server-roundtrip {server = server} (_ , (_ , valid)) = trans (map-∘ server) (Srv.roundtrip valid)

-- Unique local encodings make each full pair of typed inputs unique as well.
unique : ∀ {cr ci sr si client server otherClient otherServer} →
  Valid cr ci sr si client server → Valid cr ci sr si otherClient otherServer →
  client ≡ otherClient × server ≡ otherServer
unique {client = client} {server} {otherClient} {otherServer}
  ((_ , cv) , (_ , sv)) ((_ , cv′) , (_ , sv′)) =
  trans (sym (client-rows client)) (trans (cong (map clientRow) (C.rows-unique cv cv′)) (client-rows otherClient)) ,
  trans (sym (server-rows server)) (trans (cong (map serverRow) (Srv.rows-unique sv sv′)) (server-rows otherServer))

-- A paired failure identifies the original endpoint list in addition to its zero-based index.
data Side : Set where
  clientInput serverInput : Side

-- These are normalized-input positions, not unproved raw file/thread coordinates.
record Failure : Set where
  constructor at
  field
    side : Side
    position : ℕ
    reason : Srv.Reason
open Failure public

-- Preserve the exact offending row and distinguish agency, role and parser-outcome failures.
client-failure : C.Failure → Failure
client-failure (C.at position (C.wrongRole role)) = at clientInput position (Srv.wrongRole role)
client-failure (C.at position (C.wrongAgency event)) = at clientInput position (Srv.wrongAgency event)
client-failure (C.at position C.unparsedOrUnsupported) = at clientInput position Srv.unparsedOrUnsupported

-- Server diagnostics already use the shared normalized failure-reason type.
server-failure : Srv.Failure → Failure
server-failure (Srv.at position reason) = at serverInput position reason

-- Total validation never drops a failed row or silently fixes endpoint role/agency.
translate : (cr : Log.Role) (ci : Input) (sr : Log.Role) (si : Input) →
  (Failure × (Adapted cr ci sr si → ⊥)) ⊎ Adapted cr ci sr si
translate cr ci sr si with C.translate cr ci
... | inj₁ (failure , absent) = inj₁ (client-failure failure , λ { (client , server , cv , sv) → absent (_ , cv) })
... | inj₂ (client , cv) with Srv.translate sr si
...   | inj₁ (failure , absent) = inj₁ (server-failure failure , λ { (client , server , cv , sv) → absent (_ , sv) })
...   | inj₂ (server , sv) = inj₂ (map clientRow client , map serverRow server , client-valid cv , server-valid sv)

-- Acceptance combines lossless normalized mappings with an unrestricted fresh source merge/run.
Accepted : S.Contract → Log.Role → Input → Log.Role → Input → Set
Accepted contract cr ci sr si = Σ[ client ∈ List R.ClientRow ] Σ[ server ∈ List R.ServerRow ]
  (Valid cr ci sr si client server × Source.SourceTrace contract client server)

-- Exact mapping uniqueness transports a source refutation to all valid normalized witnesses.
exclude : ∀ {contract cr ci sr si client server} → Valid cr ci sr si client server →
  (Source.SourceTrace contract client server → ⊥) → Accepted contract cr ci sr si → ⊥
exclude valid absent (otherClient , otherServer , otherValid , source) with unique valid otherValid
... | refl , refl = absent source

-- Invalid normalized input is distinct from exhaustive failure of the protocol language.
data Verdict (contract : S.Contract) (cr : Log.Role) (ci : Input) (sr : Log.Role) (si : Input) : Set where
  invalidInput : Failure → (Adapted cr ci sr si → ⊥) → Verdict contract cr ci sr si
  protocolRejected : (client : List R.ClientRow) (server : List R.ServerRow) →
    Valid cr ci sr si client server → (Source.SourceTrace contract client server → ⊥) →
    (Accepted contract cr ci sr si → ⊥) → Verdict contract cr ci sr si
  accepted : Accepted contract cr ci sr si → Verdict contract cr ci sr si

-- The callback contract remains explicit while all permitted endpoint-order merges are searched.
check : (contract : S.Contract) (cr : Log.Role) (ci : Input) (sr : Log.Role) (si : Input) → Verdict contract cr ci sr si
check contract cr ci sr si with translate cr ci sr si
... | inj₁ (failure , absent) = invalidInput failure absent
... | inj₂ (client , server , valid) with Source.decide contract client server
...   | yes source = accepted (client , server , valid , source)
...   | no absent = protocolRejected client server valid absent (exclude valid absent)

-- Rejection refutes every matching exact-schema initial source trace, rather than a planner limit.
decide : (contract : S.Contract) (cr : Log.Role) (ci : Input) (sr : Log.Role) (si : Input) →
  Dec (Accepted contract cr ci sr si)
decide contract cr ci sr si with check contract cr ci sr si
... | accepted witness = yes witness
... | invalidInput failure absent = no λ { (client , server , valid , source) → absent (client , server , valid) }
... | protocolRejected client server valid absent impossible = no impossible

-- Fully typed summaries can enter directly while preserving explicit endpoint role declarations.
check-normalized : (contract : S.Contract) (cr : Log.Role) (client : List Log.E) (sr : Log.Role) (server : List Log.E) →
  Verdict contract cr (present client) sr (present server)
check-normalized contract cr client sr server = check contract cr (present client) sr (present server)

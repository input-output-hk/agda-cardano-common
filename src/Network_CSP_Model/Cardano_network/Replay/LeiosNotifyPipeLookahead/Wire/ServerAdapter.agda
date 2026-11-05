{-# OPTIONS --guardedness #-}

-- Total normalized server-row validation with exact logger-summary carriers, never row deletion.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as W
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerQuotient Payloads.Notification as Quotient

-- Encode the server's fixed agency while preserving every value present in the summary schema.
encode : W.Wire → Log.E
encode W.request = Log.Recv , Log.RequestNext
encode W.quit = Log.Recv , Log.Quit
encode W.done = Log.Send , Log.Done
encode (W.reply S.canceled) = Log.Send , Log.Canceled
encode (W.reply (S.normal (Payloads.announcement (header value)))) = Log.Send , Log.BlockAnnouncement value
encode (W.reply (S.normal (Payloads.offer (hash , slot) bytes))) = Log.Send , Log.BlockOffer hash slot bytes
encode (W.reply (S.normal (Payloads.txsOffer (hash , slot)))) = Log.Send , Log.BlockTxsOffer hash slot
encode (W.reply (S.normal (Payloads.votes votes))) = Log.Send , Log.Votes votes

-- Decode all normalized forms; inappropriate directions fail instead of becoming hidden events.
decode : Log.E → Maybe W.Wire
decode (Log.Recv , Log.RequestNext) = just W.request
decode (Log.Recv , Log.Quit) = just W.quit
decode (Log.Send , Log.Done) = just W.done
decode (Log.Send , Log.Canceled) = just (W.reply S.canceled)
decode (Log.Send , Log.BlockAnnouncement value) = just (W.reply (S.normal (Payloads.announcement (header value))))
decode (Log.Send , Log.BlockOffer hash slot bytes) = just (W.reply (S.normal (Payloads.offer (hash , slot) bytes)))
decode (Log.Send , Log.BlockTxsOffer hash slot) = just (W.reply (S.normal (Payloads.txsOffer (hash , slot))))
decode (Log.Send , Log.Votes votes) = just (W.reply (S.normal (Payloads.votes votes)))
decode _ = nothing

-- Exact canonical summary values roundtrip without sorting votes or inventing announcement metadata.
decode-encode : ∀ row → decode (encode row) ≡ just row
decode-encode W.request = refl
decode-encode W.quit = refl
decode-encode W.done = refl
decode-encode (W.reply S.canceled) = refl
decode-encode (W.reply (S.normal (Payloads.announcement (header _)))) = refl
decode-encode (W.reply (S.normal (Payloads.offer (_ , _) _))) = refl
decode-encode (W.reply (S.normal (Payloads.txsOffer (_ , _)))) = refl
decode-encode (W.reply (S.normal (Payloads.votes _))) = refl

-- Successful decoding recovers the original direction, constructor and all typed retained fields.
encode-decoded : ∀ {event row} → decode event ≡ just row → encode row ≡ event
encode-decoded {Log.Recv , Log.RequestNext} refl = refl
encode-decoded {Log.Recv , Log.Quit} refl = refl
encode-decoded {Log.Send , Log.Done} refl = refl
encode-decoded {Log.Send , Log.Canceled} refl = refl
encode-decoded {Log.Send , Log.BlockAnnouncement _} refl = refl
encode-decoded {Log.Send , Log.BlockOffer _ _ _} refl = refl
encode-decoded {Log.Send , Log.BlockTxsOffer _ _} refl = refl
encode-decoded {Log.Send , Log.Votes _} refl = refl
encode-decoded {Log.Send , Log.RequestNext} ()
encode-decoded {Log.Send , Log.Quit} ()
encode-decoded {Log.Recv , Log.Done} ()
encode-decoded {Log.Recv , Log.Canceled} ()
encode-decoded {Log.Recv , Log.BlockAnnouncement _} ()
encode-decoded {Log.Recv , Log.BlockOffer _ _ _} ()
encode-decoded {Log.Recv , Log.BlockTxsOffer _ _} ()
encode-decoded {Log.Recv , Log.Votes _} ()

-- A failed decode cannot possess a hidden exact-field encoding witness.
decode-missing : ∀ {event row} → decode event ≡ nothing → encode row ≡ event → ⊥
decode-missing {row = row} absent same
  with trans (sym (decode-encode row)) (trans (cong decode same) absent)
... | ()

-- Encoding is injective at exactly the fields represented by the normalized schema.
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

-- Server role is part of validation even for empty input.
Valid : Log.Role → Input → List W.Wire → Set
Valid role input rows = role ≡ Log.server × Rows input rows

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
translate Log.client input = inj₁ (at 0 (wrongRole Log.client) , λ { (_ , () , _) })
translate Log.server input with walk input
... | inj₁ (failure , absent) = inj₁ (failure , λ { (_ , _ , rows) → absent rows })
... | inj₂ (rows , valid) = inj₂ (rows , refl , valid)

-- Acceptance retains every input row and a concrete detailed-source trace under the declared callback contract.
Accepted : S.Contract → Log.Role → Input → Set
Accepted contract role input = Σ[ rows ∈ List W.Wire ]
  (Valid role input rows × Quotient.SourceTrace contract rows)

-- Exact mapping uniqueness transports exhaustive source rejection back to all normalized witnesses.
exclude : ∀ {contract role input} rows → Valid role input rows →
  (Quotient.SourceTrace contract rows → ⊥) → Accepted contract role input → ⊥
exclude {contract} rows (_ , valid) absent (other , (_ , otherValid) , source) =
  absent (subst (Quotient.SourceTrace contract) (sym (rows-unique valid otherValid)) source)

-- Verdicts separate invalid input from a source-language refutation; acceptance includes its witness.
data Verdict (contract : S.Contract) (role : Log.Role) (input : Input) : Set where
  invalidInput : Failure → (Adapted role input → ⊥) → Verdict contract role input
  protocolRejected : (rows : List W.Wire) → Valid role input rows →
    (Quotient.SourceTrace contract rows → ⊥) → (Accepted contract role input → ⊥) → Verdict contract role input
  accepted : Accepted contract role input → Verdict contract role input

-- The backend is the proved total server quotient; no fuel cutoff or unobserved row is introduced.
check : (contract : S.Contract) (role : Log.Role) (input : Input) → Verdict contract role input
check contract role input with translate role input
... | inj₁ (failure , absent) = invalidInput failure absent
... | inj₂ (rows , valid) with Quotient.decide-source contract rows
...   | yes source = accepted (rows , valid , source)
...   | no absent = protocolRejected rows valid absent (exclude rows valid absent)

-- The public decision refutes all matching input/source witnesses when rejection occurs.
decide : (contract : S.Contract) (role : Log.Role) (input : Input) → Dec (Accepted contract role input)
decide contract role input with check contract role input
... | accepted witness = yes witness
... | invalidInput failure absent = no λ { (rows , valid , source) → absent (rows , valid) }
... | protocolRejected rows valid absent impossible = no impossible

-- Typed normalized events can be checked directly without exposing the parser-outcome wrapper.
check-normalized : (contract : S.Contract) (role : Log.Role) (events : List Log.E) →
  Verdict contract role (present events)
check-normalized contract role events = check contract role (present events)

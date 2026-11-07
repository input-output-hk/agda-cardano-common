{-# OPTIONS --guardedness #-}

-- Concrete silenced local verdicts, and native transport of one decided silenced server witness.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.SilencedAdapterTests where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
open import Cardano_network.Net exactParams using (Link)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as SW
open import Cardano_network.Replay.LeiosNotifyPipeLookahead.Silenced exactParams using (isVotes)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.ServerSilenced Payloads.Notification isVotes as SS
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.SilencedAdapter as A
import Cardano_network.Replay.LeiosNotifyPipeLookahead.WireSilencedNative exactParams as Native

-- Verdict category only; the evidence itself is checked by the adapter's types.
data Kind : Set where
  invalid rejected accepted undetermined : Kind

-- Read off the verdict constructor of a concrete adapter run.
kind : ∀ {W : Set} {V P : List W → Set} → A.Outcome W V P → Kind
kind (A.invalid _ _) = invalid
kind (A.rejected _ _ _) = rejected
kind (A.accepted _ _ _) = accepted

-- The rows of an accepted verdict, for tying fixtures to actual adapter output.
acceptedRows : ∀ {W : Set} {V P : List W → Set} → A.Outcome W V P → Maybe (List W)
acceptedRows (A.accepted rows _ _) = just rows
acceptedRows _ = nothing

-- Normalized rows of the graceful node-next server fixture.
gracefulInput : List Log.E
gracefulInput = (Log.Send , Log.BlockAnnouncement nothing) ∷ (Log.Recv , Log.Quit) ∷
  (Log.Send , Log.Canceled) ∷ (Log.Send , Log.Done) ∷ []

-- Wire rows of the graceful server fixture.
gracefulRows : List SW.Wire
gracefulRows = SW.reply (S.normal (Payloads.announcement (header nothing))) ∷ SW.quit ∷
  SW.reply S.canceled ∷ SW.done ∷ []

-- Graceful node-next server shutdown with every RequestNext silenced.
server-graceful-accepted : kind (A.server S.nodeNext (map just gracefulInput)) ≡ accepted
server-graceful-accepted = refl

-- The accepted rows are exactly the wire rows used in the native test below.
server-graceful-rows : acceptedRows (A.server S.nodeNext (map just gracefulInput)) ≡ just gracefulRows
server-graceful-rows = refl

-- A present RequestNext row under the silenced profile is invalid input, never erased.
silenced-row-invalid : A.server S.nodeNext (just (Log.Recv , Log.RequestNext) ∷ []) ≡
  A.invalid 0 "silenced kind present: RequestNext/Votes"
silenced-row-invalid = refl

-- A present Votes row is equally invalid, here at a later position.
silenced-votes-invalid : A.server S.genericNext (map just
  ((Log.Send , Log.Canceled) ∷ (Log.Send , Log.Votes []) ∷ [])) ≡
  A.invalid 1 "silenced kind present: RequestNext/Votes"
silenced-votes-invalid = refl

-- An earlier parse failure keeps its existing reason ahead of a later silenced row.
unparsed-before-silenced : A.server S.nodeNext (nothing ∷ just (Log.Recv , Log.RequestNext) ∷ []) ≡
  A.invalid 0 "unparsed or unsupported event"
unparsed-before-silenced = refl

-- Wrong direction keeps the existing agency reason.
wrong-agency-kept : A.server S.nodeNext (just (Log.Recv , Log.Canceled) ∷ []) ≡
  A.invalid 0 "wrong agency: Recv Canceled"
wrong-agency-kept = refl

-- Graceful client shutdown with every RequestNext silenced.
client-graceful-accepted : kind (A.client (map just
  ((Log.Recv , Log.BlockAnnouncement nothing) ∷ (Log.Send , Log.Quit) ∷
   (Log.Recv , Log.Canceled) ∷ (Log.Recv , Log.Done) ∷ []))) ≡ accepted
client-graceful-accepted = refl

-- Done before Quit is outside the client silenced language.
client-done-first-rejected : kind (A.client (just (Log.Recv , Log.Done) ∷ [])) ≡ rejected
client-done-first-rejected = refl

-- A received Votes row is invalid for the client too.
client-votes-invalid : A.client (just (Log.Recv , Log.Votes []) ∷ []) ≡
  A.invalid 0 "silenced kind present: RequestNext/Votes"
client-votes-invalid = refl

-- Client rows mirroring the graceful server fixture.
gracefulClient : List Log.E
gracefulClient = (Log.Recv , Log.BlockAnnouncement nothing) ∷ (Log.Send , Log.Quit) ∷
  (Log.Recv , Log.Canceled) ∷ (Log.Recv , Log.Done) ∷ []

-- Read off an input-level paired verdict: invalid endpoint input, or the paired outcome constructor.
pairedKind : ∀ {contract ci si} → A.PairedOutcome contract ci si → Kind
pairedKind (A.invalidClient _ _) = invalid
pairedKind (A.invalidServer _ _) = invalid
pairedKind (A.checked _ _ _ _ (A.PS.accepted _)) = accepted
pairedKind (A.checked _ _ _ _ (A.PS.rejected _)) = rejected
pairedKind (A.checked _ _ _ _ (A.PS.undetermined _ _ _)) = undetermined

-- The graceful pair is accepted on the translations of both inputs.
paired-graceful-accepted : pairedKind (A.paired S.nodeNext (map just gracefulClient) (map just gracefulInput)) ≡ accepted
paired-graceful-accepted = refl

-- A local client rejection is a paired rejection (input-level through A.exclude).
paired-client-rejected : pairedKind (A.paired S.nodeNext (just (Log.Recv , Log.Done) ∷ []) (map just gracefulInput)) ≡ rejected
paired-client-rejected = refl

-- A present server Votes row is invalid server input at its own position.
paired-server-votes-invalid : A.paired S.nodeNext (map just gracefulClient)
  (just (Log.Send , Log.Canceled) ∷ just (Log.Send , Log.Votes []) ∷ []) ≡
  A.invalidServer 1 "silenced kind present: RequestNext/Votes"
paired-server-votes-invalid = refl

-- Native transport at an arbitrary chosen endpoint.
module For (l : Link) (d : Dir) where
  -- Silenced server native transport under node-next at this endpoint.
  module Node = Native.Server S.nodeNext l d

  -- The decided silenced proof for the adapter's accepted rows (server-graceful-rows) transports to a native trace whose erasure is the observed rows.
  native-graceful : Node.SilencedNative gracefulRows
  native-graceful = proj₁ (Node.equivalence gracefulRows)
    (toWitness {a? = SS.decide-silenced S.nodeNext gracefulRows} tt)

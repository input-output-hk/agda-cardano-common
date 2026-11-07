{-# OPTIONS --guardedness #-}

-- Silenced wire languages transported to the native lookahead trees: a silenced row list is the
-- erasure of some actual native wire trace, exactly when the local silenced machine accepts it.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.WireSilencedNative (p : Params) where

open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
import Cardano_network.LeiosNotifyPipe p as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as SW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Payloads.Notification as CW
open import Cardano_network.Replay.LeiosNotifyPipeLookahead.Silenced p using (isVotes)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.ServerSilenced Payloads.Notification isVotes as SS
import Cardano_network.LeiosNotifyPipeLookahead.Wire.ClientSilenced Payloads.Notification isVotes as CS
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerQuotient Payloads.Notification as SQ
import Cardano_network.Replay.LeiosNotifyPipeLookahead.WireServerNative p as ServerNative
import Cardano_network.Replay.LeiosNotifyPipeLookahead.WireClientNative p ⊤ as ClientNative

-- Server endpoint under an explicit callback contract.
module Server (contract : S.Contract) (l : Link) (d : Dir) where
  -- The exact server wire/native trace equivalence at this endpoint and contract.
  module Native = ServerNative.For contract l d

  -- Some full native wire trace whose silenced erasure is exactly the observed rows.
  SilencedNative : List SW.Wire → Set₁
  SilencedNative rows = Σ[ ws ∈ List SW.Wire ] (Native.NativeTrace ws × SS.erase ws ≡ rows)

  -- The same hidden full rows witness both sides, via the quotient and native equivalences.
  equivalence : ∀ rows →
    (SS.Silenced contract rows → SilencedNative rows) × (SilencedNative rows → SS.Silenced contract rows)
  equivalence rows =
    (λ { (ws , trace , same) →
      ws , proj₁ (Native.equivalence ws) (proj₂ (SQ.equivalence contract ws) trace) , same }) ,
    (λ { (ws , native , same) →
      ws , proj₁ (SQ.equivalence contract ws) (proj₂ (Native.equivalence ws) native) , same })

  -- The local silenced decision is exhaustive for every native realization.
  decide-native : ∀ rows → Dec (SilencedNative rows)
  decide-native rows with SS.decide-silenced contract rows
  ... | yes witness = yes (proj₁ (equivalence rows) witness)
  ... | no absent = no λ native → absent (proj₂ (equivalence rows) native)

-- Client endpoint with the unit successful-return profile.
module Client (l : Link) (d : Dir) where
  -- The exact client wire/native trace equivalence at this endpoint (unit return).
  module Native = ClientNative.At l d

  -- Some full native wire trace whose silenced erasure is exactly the observed rows.
  SilencedNative : List CW.Wire → Set₁
  SilencedNative rows = Σ[ ws ∈ List CW.Wire ] (Native.NativeTrace ws × CS.erase ws ≡ rows)

  -- The same hidden full rows witness both sides, via the client quotient (return tt) and native bridge.
  equivalence : ∀ rows → (CS.Silenced rows → SilencedNative rows) × (SilencedNative rows → CS.Silenced rows)
  equivalence rows =
    (λ { (ws , trace , same) → ws , Native.quotient→native tt trace , same }) ,
    (λ { (ws , native , same) → ws , Native.native→quotient native , same })

  -- The local silenced decision is exhaustive for every native realization.
  decide-native : ∀ rows → Dec (SilencedNative rows)
  decide-native rows with CS.decide-silenced rows
  ... | yes witness = yes (proj₁ (equivalence rows) witness)
  ... | no absent = no λ native → absent (proj₂ (equivalence rows) native)

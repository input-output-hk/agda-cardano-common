{-# OPTIONS --guardedness #-}

-- Exact decoded-bitmap observation drops decoder-failing receives before logging.
-- Hashes, slots and transaction counts are retained. Request offsets and validity are retained; receive-side sizes use WireOK.
-- Checked with --safe on the command line (B7a).
module Cardano_network.Replay.LeiosFetchObs where

open import Data.Nat using (ℕ; _≤_; _≤ᵇ_)
import Data.Nat.Properties as N
open import Data.List using (List; map; length; _∷_; [])
open import Data.Bool using (Bool; T; true; false)
open import Cardano_network.Replay.LeiosFetchWords using (decodable; canonical)
open import Cardano_network.Replay.LeiosFetchWords public using (Decodes)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs; Bitmap; validᵇ; offsets)
import Data.Unit
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (ExtI)
open import Cardano_network.Base using (N2N_LeiosFetch)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Net_Api; input; output)
open import Cardano_network.Data replayParams
  using ( Payload; Messages; leiosFetchP; MessageLeiosFetchP
        ; MsgLFPBlockRequest; MsgLFPBlock; MsgLFPBlockTxsRequest; MsgLFPBlockTxs; MsgLFPDone )
import Cardano_network.LeiosFetchP replayParams as LFP
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as LTSS
import Semantics.LTS {E = LFP.LFPEv} {I = ExtI LFP.LFPEv} as LTSC
import Semantics.Replay.Bridge {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as BrS
import Semantics.Replay.Bridge {E = LFP.LFPEv} {I = ExtI LFP.LFPEv} as BrC
open import Cardano_network.Replay.LeiosFetchSession
  using (Direction; Send; Recv; Msg; E
        ; MsgLeiosBlockRequest; MsgLeiosBlock; MsgLeiosBlockTxsRequest; MsgLeiosBlockTxs
        ; MsgLeiosDone)

-- a LeiosFetch message as far as the replay can compare it
data Msg♭ : Set where
  -- BlockRequest (ebHash, ebSlot)
  blockReq♭ : (h s : ℕ) → Msg♭
  -- Block ebHash
  block♭    : (h : ℕ) → Msg♭
  -- BlockTxsRequest (hash, slot, count, decoded offsets, decoder validity)
  txsReq♭   : (h s n : ℕ) → List ℕ → Bool → Msg♭
  -- BlockTxs positional reply count
  txs♭      : (n : ℕ) → Msg♭
  -- Done
  done♭     : Msg♭

-- an observed event: direction and abstract message
E♭ : Set
E♭ = Direction × Msg♭

-- the observable part of a spec (log-level) event
forget : E → E♭
forget (d , MsgLeiosBlockRequest h s)        = d , blockReq♭ h s
forget (d , MsgLeiosBlock h _)               = d , block♭ h
forget (d , MsgLeiosBlockTxsRequest h s n b) = d , txsReq♭ h s n (offsets b) (validᵇ b)
forget (d , MsgLeiosBlockTxs n _)            = d , txs♭ n
forget (d , MsgLeiosDone)                    = d , done♭

-- the observable part of a model wire message (`ebHash = id` at `replayParams`)
msg♭ : MessageLeiosFetchP → Msg♭
msg♭ (MsgLFPBlockRequest (h , s))      = blockReq♭ h s
msg♭ (MsgLFPBlock eb)                  = block♭ eb
msg♭ (MsgLFPBlockTxsRequest (h , s) bm) = txsReq♭ h s (length bm) bm true
msg♭ (MsgLFPBlockTxs txs)              = txs♭ (length txs)
msg♭ MsgLFPDone                        = done♭

-- the observable part of a LeiosFetch payload, if it is one
pay♭ : Direction → Payload → Maybe E♭
pay♭ d (_ , _ , _ , leiosFetchP m) = just (d , msg♭ m)
pay♭ d _                           = nothing

-- Decoder failures occur before the upstream receive tracer is called.
decodes : MessageLeiosFetchP → Bool
decodes (MsgLFPBlockTxsRequest _ bm) = decodable bm
decodes (MsgLFPBlockTxs txs) = length txs ≤ᵇ maxTxs
decodes _ = true

-- Sending is observed; a receive is observed only after successful decoding.
recv♭ : Payload → Maybe E♭
recv♭ (_ , _ , _ , leiosFetchP m) with decodes m
... | true = just (Recv , msg♭ m)
... | false = nothing
recv♭ _ = nothing

-- Successful Boolean evidence exposes the classifier's decoder branch.
T-true : ∀ {b} → T b → b ≡ true
T-true {true} p = refl
T-true {false} ()

-- A decoded server request is logged with its actual offset count.
recv-request : ∀ tm md ln q bm → T (decodable bm) →
  recv♭ (tm , md , ln , leiosFetchP (MsgLFPBlockTxsRequest q bm)) ≡
  just (Recv , txsReq♭ (Data.Product.proj₁ q) (Data.Product.proj₂ q) (length bm) bm true)
recv-request tm md ln q bm ok rewrite T-true ok = refl

-- A decoder-failing request is absent from the upstream receive trace.
recv-request-fails : ∀ tm md ln q bm → decodable bm ≡ false →
  recv♭ (tm , md , ln , leiosFetchP (MsgLFPBlockTxsRequest q bm)) ≡ nothing
recv-request-fails tm md ln q bm bad rewrite bad = refl

-- A bounded client reply is logged with its actual transaction count.
recv-reply : ∀ tm md ln ts → length ts ≤ maxTxs →
  recv♭ (tm , md , ln , leiosFetchP (MsgLFPBlockTxs ts)) ≡ just (Recv , txs♭ (length ts))
recv-reply tm md ln ts cap rewrite T-true (N.≤⇒≤ᵇ cap) = refl

-- classify a renamed-server event: LeiosFetch wire I/O is logged, all else is silent
clsS : LTSS.Event → Maybe E♭
clsS (LTSS.evLabel _ (input  _ _ N2N_LeiosFetch) a) = pay♭ Send a
clsS (LTSS.evLabel _ (output _ _ N2N_LeiosFetch) a) = recv♭ a
clsS _                                              = nothing

-- classify a client (`LFPEv`) event: wire I/O is logged, api/done are silent
clsC : LTSC.Event → Maybe E♭
clsC (LTSC.evLabel _ (LFP.sendLFP    _ _) a) = pay♭ Send a
clsC (LTSC.evLabel _ (LFP.receiveLFP _ _) a) = recv♭ a
clsC _                                       = nothing

-- B3's `Obs` on the server side: the log sees exactly `es` (up to `forget`)
ObsS : List LTSS.Event → List E → Set
ObsS = BrS.Obs clsS forget

-- B3's `Obs` on the client side
ObsC : List LTSC.Event → List E → Set
ObsC = BrC.Obs clsC forget

-- Two replay traces agree on retained fields, including decoded request offsets.
infix 4 _≈♭_
_≈♭_ : List E → List E → Set
es ≈♭ es′ = map forget es ≡ map forget es′

-- Exact request equality exposes decoder validity, count and decoded offsets.
request-match : ∀ {h s n b h′ s′ bm} →
  txsReq♭ h s n (offsets b) (validᵇ b) ≡ txsReq♭ h′ s′ (length bm) bm true →
  (h ≡ h′) × (s ≡ s′) × (n ≡ length bm) × Decodes b bm
request-match {b = b} eq with validᵇ b
... | false with eq
... | ()
request-match {b = b} refl | true = refl , refl , refl , Data.Unit.tt , refl

-- Decoder evidence constructs an exact request observation.
request-equal : ∀ h s n b bm → n ≡ length bm → Decodes b bm →
  txsReq♭ h s n (offsets b) (validᵇ b) ≡ txsReq♭ h s (length bm) bm true
request-equal h s .(length bm) b bm refl (valid , same)
  rewrite T-true valid | same = refl

-- Equal flattened requests retain validity, counts and offsets independently.
request-fields : ∀ {h s n os v h′ s′ n′ os′ v′} →
  txsReq♭ h s n os v ≡ txsReq♭ h′ s′ n′ os′ v′ →
  (h ≡ h′) × (s ≡ s′) × (n ≡ n′) × (os ≡ os′) × (v ≡ v′)
request-fields refl = refl , refl , refl , refl , refl

-- Honest outgoing requests use offsets inside the client's transaction table.
Honest : E → Set
Honest (Send , MsgLeiosBlockTxsRequest _ _ _ b) = T (canonical (offsets b))
Honest _ = Data.Unit.⊤

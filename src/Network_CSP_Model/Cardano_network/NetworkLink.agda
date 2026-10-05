{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the LINK-INDEXED `NetworkLink` process.
--
-- A second rendering of the CSPm `Network` (see `Network.agda`) in which
-- the whole multiplexer is replicated PER TCP LINK:
--
--   NetOneLink(l) = (TxSideₗ(l) [|{|tx,ack|}|] RxSideₗ(l)) \ {|tx,ack|}
--   NetworkLink   = ||| l : Link @ NetOneLink(l)
--
-- Each `NetOneLink l` is a faithful copy of the monolithic `Network`
-- restricted to link `l`: the per-instance `Input`/`Output` leaves are
-- shared with `Network.agda`, while the four shared one-place buffers
-- (`Transmitter`/`RcvAck`/`Receiver`/`SndAck`) become link-local
-- variants (`Transmitterₗ l`, …) whose menus additionally filter the
-- event's link component against `l`.  The synchronisation / hiding
-- sets stay the whole-channel `csSR`/`csRS`/`csTA` of `Network.agda`:
-- `NetOneLink l`'s operands only ever OFFER link-`l` events, so
-- synchronising on other links' events is vacuous.
--
-- Equivalence with `CopySpec` (which is per-link already) is proved in
-- `NetworkVerification/NetworkLinkEquiv.agda`.
------------------------------------------------------------------------

open import Data.List using (map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ContinueType; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.NetworkLink
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open Params p using (numLinks; linkConfig)

import CSP.Operators {E = Net Data} (Net-≟ {Data}) as Op
open Op using (Par⊤; _∥⇘_⇙_; _⦀_; ⦀⋆; ⦀Fin; _∖_; pchoice; Prefix₀; Skip; loop0; chanSet)

open import CSP.Examples.Cardano_network.Network p Data
  using ( NetProc; Menu; Input; Output
        ; csSR; csSR-dec; csRS; csRS-dec; csTA; csTA-dec )

------------------------------------------------------------------------
-- Link-local buffer leaves (the per-link variants of `Network.agda`'s
-- shared `Transmitter`/`RcvAck`/`Receiver`/`SndAck`): same menus, but
-- each first filters the event's link component against `l`.
------------------------------------------------------------------------

-- Transmitterₗ l's offer menu (hoisted to top level for confinement proofs):
-- accept sndmsg on link l (any d, id), emit tx.
transmitterMenuₗ : Link → Menu
transmitterMenuₗ l (_ , sndmsg l′ d id) x with l′ ≟ l
... | yes refl = just (Op.Output (tx l d id) x Skip)
... | no  _    = nothing
transmitterMenuₗ l _ _ = nothing

-- Transmitterₗ l: accept sndmsg on link l (any d, id), emit tx, repeat.
Transmitterₗ : Link → NetProc
Transmitterₗ l = loop0 (pchoice (transmitterMenuₗ l))

-- RcvAckₗ l's offer menu (hoisted to top level for confinement proofs):
-- accept ack on link l (any d, id), emit rcvack.
rcvackMenuₗ : Link → Menu
rcvackMenuₗ l (_ , ack l′ d id) _ with l′ ≟ l
... | yes refl = just (rcvack l d id ⟶₀ Skip)
... | no  _    = nothing
rcvackMenuₗ l _ _ = nothing

-- RcvAckₗ l: accept ack on link l (any d, id), emit rcvack, repeat.
RcvAckₗ : Link → NetProc
RcvAckₗ l = loop0 (pchoice (rcvackMenuₗ l))

-- Receiverₗ l's offer menu (hoisted to top level for confinement proofs):
-- accept tx on link l (any d, id), emit rcvmsg.
receiverMenuₗ : Link → Menu
receiverMenuₗ l (_ , tx l′ d id) x with l′ ≟ l
... | yes refl = just (Op.Output (rcvmsg l d id) x Skip)
... | no  _    = nothing
receiverMenuₗ l _ _ = nothing

-- Receiverₗ l: accept tx on link l (any d, id), emit rcvmsg, repeat.
Receiverₗ : Link → NetProc
Receiverₗ l = loop0 (pchoice (receiverMenuₗ l))

-- SndAckₗ l's offer menu (hoisted to top level for confinement proofs):
-- accept sndack on link l (any d, id), emit ack.
sndackMenuₗ : Link → Menu
sndackMenuₗ l (_ , sndack l′ d id) _ with l′ ≟ l
... | yes refl = just (ack l d id ⟶₀ Skip)
... | no  _    = nothing
sndackMenuₗ l _ _ = nothing

-- SndAckₗ l: accept sndack on link l (any d, id), emit ack, repeat.
SndAckₗ : Link → NetProc
SndAckₗ l = loop0 (pchoice (sndackMenuₗ l))

------------------------------------------------------------------------
-- One link's configured instance bundles and the per-link sides —
-- exactly `Network.agda`'s `Inputs`/`Outputs`/`TxSide`/`RxSide` with the
-- `⦀Fin numLinks` layer stripped off and the buffers link-localised.
------------------------------------------------------------------------

-- link l's configured Input cells, interleaved (empty config ⇒ Skip)
Inputsₗ : Link → NetProc
Inputsₗ l = ⦀⋆ (map (λ { (d , id) → Input l d id }) (linkConfig l))

-- link l's configured Output cells, interleaved (empty config ⇒ Skip)
Outputsₗ : Link → NetProc
Outputsₗ l = ⦀⋆ (map (λ { (d , id) → Output l d id }) (linkConfig l))

-- link l's Tx side: inputs against the link-local transmitter/ack pair
TxSideₗ : Link → NetProc
TxSideₗ l = (Inputsₗ l ∥⇘ chanSet csSR csSR-dec ⇙ (Transmitterₗ l ⦀ RcvAckₗ l))
              ∖ chanSet csSR csSR-dec

-- link l's Rx side: outputs against the link-local receiver/ack pair
RxSideₗ : Link → NetProc
RxSideₗ l = (Outputsₗ l ∥⇘ chanSet csRS csRS-dec ⇙ (Receiverₗ l ⦀ SndAckₗ l))
              ∖ chanSet csRS csRS-dec

-- the complete small network for one link
NetOneLink : Link → NetProc
NetOneLink l = (TxSideₗ l ∥⇘ chanSet csTA csTA-dec ⇙ RxSideₗ l)
                 ∖ chanSet csTA csTA-dec

-- the link-indexed network: one small network per link, interleaved
NetworkLink : NetProc
NetworkLink = ⦀Fin numLinks NetOneLink

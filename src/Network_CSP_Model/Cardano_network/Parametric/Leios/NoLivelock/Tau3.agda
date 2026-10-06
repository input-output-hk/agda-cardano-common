{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage L: PREMISE (b) CLOSED for the shipped
-- three-node line.  `TauAssembly` at `pL 2 3` over `leiosLLine`, with the
-- twelve peer leaves (dispatched on the protocol id), the node-logic leaf
-- `TauLogic.logic-R`, and the BREAKABLE medium's τ-accessibility
-- `NetworkLinkBreakableA-τ-AccReach`.  No module parameters.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NoLivelock.Tau3 where

open import Relation.Nullary using (¬_)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL)
open import Cardano_network.Parametric.Leios.LeiosInstanceL using (leiosLLine)
open import Cardano_network.Parametric.Leios.LeiosInstance3 using (rawL)
open import Cardano_network.Net (pL 2 3) using (Net_Api; Net_Api-≟)
open import Cardano_network.Data (pL 2 3) using (Payload)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (∅ES)
open import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (τ-AccReach; Diverges)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.ModAcc (Net_Api-≟ {Payload}) using (MAccR; τ-AccReach→MAccR∅; τ-AccReach→noDiv)
open import Cardano_network.Parametric.Leios.PeersP (pL 2 3) using (clientPeerP; serverPeerP)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerKA (pL 2 3) using (kaClientA-τ; kaServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerCS (pL 2 3) using (csClientA-τ; csServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerBF (pL 2 3) using (bfClientA-τ; bfServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerTS (pL 2 3) using (tsClientA-τ; tsServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLNP (pL 2 3) using (lnpClientA-τ; lnpServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP (pL 2 3) using (lfpClientA-τ; lfpServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.TauLogic 2 3 leiosLLine (λ n → n) using (logic-R)
open import Cardano_network.Parametric.Leios.NoLivelock.TauAssembly 2 3 leiosLLine (λ n → n) using (sys-τ)
open import Cardano_network.NetworkVerification.MediumTauAcc (pL 2 3) using (NetworkLinkBreakableA-τ-AccReach)

-- the client peer leaves, by protocol id
peerC : ∀ l d id → MAccR ∅ES (clientPeerP l d id)
peerC l d N2N_KeepAlive    = τ-AccReach→MAccR∅ (kaClientA-τ l d)
peerC l d N2N_ChainSync    = τ-AccReach→MAccR∅ (csClientA-τ l d)
peerC l d N2N_BlockFetch   = τ-AccReach→MAccR∅ (bfClientA-τ l d)
peerC l d N2N_TxSubmission = τ-AccReach→MAccR∅ (tsClientA-τ l d)
peerC l d N2N_LeiosNotify  = τ-AccReach→MAccR∅ (lnpClientA-τ l d)
peerC l d N2N_LeiosFetch   = τ-AccReach→MAccR∅ (lfpClientA-τ l d)

-- the server peer leaves, by protocol id (TxSubmission: the reply-reporting requester)
peerS : ∀ l d id → MAccR ∅ES (serverPeerP l d id)
peerS l d N2N_KeepAlive    = τ-AccReach→MAccR∅ (kaServerA-τ l d)
peerS l d N2N_ChainSync    = τ-AccReach→MAccR∅ (csServerA-τ l d)
peerS l d N2N_BlockFetch   = τ-AccReach→MAccR∅ (bfServerA-τ l d)
peerS l d N2N_TxSubmission = τ-AccReach→MAccR∅ (tsServerA-τ l d)
peerS l d N2N_LeiosNotify  = τ-AccReach→MAccR∅ (lnpServerA-τ l d)
peerS l d N2N_LeiosFetch   = τ-AccReach→MAccR∅ (lfpServerA-τ l d)

-- PREMISE (b), assembled: τ-accessibility at every √-free reachable state of `rawL`
rawL-τ-AccReach : τ-AccReach rawL
rawL-τ-AccReach = sys-τ peerC peerS logic-R NetworkLinkBreakableA-τ-AccReach

-- PREMISE (b) of `noLivelockT`: no reachable state of `rawL` diverges
noDivL : ∀ {s Q} → rawL ⟹⟨ s ⟩ Q → ¬ Diverges Q
noDivL = τ-AccReach→noDiv rawL-τ-AccReach

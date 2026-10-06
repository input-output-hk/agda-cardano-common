{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: PREMISE (b) CLOSED for the two-node line.
-- `TauAssembly` instantiated with the twelve peer leaves (dispatched on
-- the protocol id) and the node-logic leaf `TauLogic.logic-R`.  No module
-- parameters: every leaf hypothesis is discharged here.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.NoLivelock.Tau2 where

open import Relation.Nullary using (¬_)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch)
open import Cardano_network.Parametric.Leios.LeiosInstance2 using (p2; rawSys2; line2)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (U6; allV6)
open import Cardano_network.Net p2 using (Net_Api; Net_Api-≟)
open import Cardano_network.Data p2 using (Payload)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (∅ES)
open import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (τ-AccReach; Diverges)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.ModAcc (Net_Api-≟ {Payload}) using (MAccR; τ-AccReach→MAccR∅; τ-AccReach→noDiv)
open import Cardano_network.Parametric.Leios.PeersP p2 using (clientPeerP; serverPeerP)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerKA p2 using (kaClientA-τ; kaServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerCS p2 using (csClientA-τ; csServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerBF p2 using (bfClientA-τ; bfServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerTS p2 using (tsClientA-τ; tsServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLNP p2 using (lnpClientA-τ; lnpServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP p2 using (lfpClientA-τ; lfpServerA-τ)
open import Cardano_network.Parametric.Leios.NoLivelock.TauLogic 1 2 line2 (λ n → n) using (logic-R)

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

open import Cardano_network.Parametric.Leios.NoLivelock.TauAssembly 1 2 line2 (λ n → n) using (sys-τ)
open import Cardano_network.NetworkVerification.MediumTauAcc p2 using (NetworkLinkA-τ-AccReach)

-- PREMISE (b), assembled: τ-accessibility at every √-free reachable state of `rawSys2`
rawSys2-τ-AccReach : τ-AccReach rawSys2
rawSys2-τ-AccReach = sys-τ peerC peerS logic-R NetworkLinkA-τ-AccReach

-- PREMISE (b) of `noLivelockT`: no reachable state of `rawSys2` diverges
noDiv2 : ∀ {s Q} → rawSys2 ⟹⟨ s ⟩ Q → ¬ Diverges Q
noDiv2 = τ-AccReach→noDiv rawSys2-τ-AccReach

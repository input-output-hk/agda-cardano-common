{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: the prototype LeiosFetch PEERS (LFP).
--   * VIEWS: each menu state of each side inverted ONCE at `LFPEv`; every
--     fact of a side is read off one view-to-obligations function
--   * premise (b): `lfpClientA-τ`, `lfpServerA-τ`
--   * counting on the peer's own renamed trace: P1, and the relays —
--     client: block / tx-closure requests sent ≤ commanded, requested
--     bitmap entries ≤ commanded, tx-closure entries reported ≤ received
--     (list lengths), sends no BlockTxs; server: request reports ≤
--     requests received (and bitmap lengths), sends no request, BlockTxs
--     entries sent ≤ commanded (list lengths)
--   * provenance: chain-free by renaming alone (`lfpA-PA`)
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.PeerLFP (p : Params) where

open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _≤_; _+_; z≤n)
open import Data.Nat.Properties using (≤-refl; m≤m+n)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosFetchP p
open import Cardano_network.Parametric.Leios.PeersP p using (ιLFP; ιLFP⁻¹; ιLFP-linv; LFPclientA; LFPserverA)
open Params p using (time₀; length₀; Time; Length; decEB)
import CSP.Rename {E₁ = LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RenLFP
open import CSP.Operators LFPEv-≟ using (∅ES; Ret; Output; Prefix; Prefix₀)
open import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} using (_─[_]─►_; ev; evl; sVis)
import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} as F
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as L
import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as DF
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.ModAcc LFPEv-≟ using (MAccR; MAccR→τ-AccReach)
open import CSP.Laws.DivFree.Reach LFPEv-≟ using (MAccR-Ret)
open import CSP.Laws.DivFree.Loop LFPEv-≟
  using (NoRetBy; Looping; NoRetBy-mono; NoRetBy-Ret; Guarded-react; MAccR-react; MAccR-Output; MAccR-⟶₀; MAccR-iter)
open import CSP.Laws.DivFree.ReachRename {E₁ = LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv using (τ-AccReach-renameMap)
import CSP.Laws.DivFree.Count LFPEv-≟ as S
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (slack0; none0)
open import CSP.Laws.DivFree.CountMore LFPEv-≟ using (RoundPot; StepPot; rp-pch; rp-done; sp-Ret; sp-Out; sp-Out≤; sp-⟶; potIter)
open import CSP.Laws.DivFree.Prov LFPEv-≟ using (pa)
open import CSP.Laws.DivFree.ProvMore LFPEv-≟ using (Prov-free)
import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) as PL
open import Cardano_network.Parametric.Leios.NoLivelock.Weights p
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF p using (ChS; InP)

------------------------------------------------------------------------
-- the renaming pulls back exactly its images (`CountRename`'s `ι-rinv`)
------------------------------------------------------------------------

-- ιLFP⁻¹ pulls back only ιLFP-images
ιLFP-rinv : ∀ {A} {e₂ : Net_Api Payload A} {e : LFPEv A} → ιLFP⁻¹ e₂ ≡ just e → e₂ ≡ ιLFP e
ιLFP-rinv {e₂ = input  _ _ N2N_LeiosFetch} refl = refl
ιLFP-rinv {e₂ = output _ _ N2N_LeiosFetch} refl = refl
ιLFP-rinv {e₂ = apiLP  _ _ _} refl = refl
ιLFP-rinv {e₂ = done   _ _ N2N_LeiosFetch} refl = refl
ιLFP-rinv {e₂ = input  _ _ N2N_ChainSync} ()
ιLFP-rinv {e₂ = input  _ _ N2N_BlockFetch} ()
ιLFP-rinv {e₂ = input  _ _ N2N_TxSubmission} ()
ιLFP-rinv {e₂ = input  _ _ N2N_KeepAlive} ()
ιLFP-rinv {e₂ = input  _ _ N2N_LeiosNotify} ()
ιLFP-rinv {e₂ = output _ _ N2N_ChainSync} ()
ιLFP-rinv {e₂ = output _ _ N2N_BlockFetch} ()
ιLFP-rinv {e₂ = output _ _ N2N_TxSubmission} ()
ιLFP-rinv {e₂ = output _ _ N2N_KeepAlive} ()
ιLFP-rinv {e₂ = output _ _ N2N_LeiosNotify} ()
ιLFP-rinv {e₂ = done   _ _ N2N_ChainSync} ()
ιLFP-rinv {e₂ = done   _ _ N2N_BlockFetch} ()
ιLFP-rinv {e₂ = done   _ _ N2N_TxSubmission} ()
ιLFP-rinv {e₂ = done   _ _ N2N_KeepAlive} ()
ιLFP-rinv {e₂ = done   _ _ N2N_LeiosNotify} ()
ιLFP-rinv {e₂ = sndmsg _ _ _} ()
ιLFP-rinv {e₂ = rcvmsg _ _ _} ()
ιLFP-rinv {e₂ = tx _ _ _} ()
ιLFP-rinv {e₂ = sndack _ _ _} ()
ιLFP-rinv {e₂ = rcvack _ _ _} ()
ιLFP-rinv {e₂ = ack _ _ _} ()
ιLFP-rinv {e₂ = apiBF _ _ _} ()
ιLFP-rinv {e₂ = apiTS _ _ _} ()
ιLFP-rinv {e₂ = apiKA _ _ _} ()
ιLFP-rinv {e₂ = apiLN _ _ _} ()
ιLFP-rinv {e₂ = apiLF _ _ _} ()
ιLFP-rinv {e₂ = apiCS _ _ _} ()
ιLFP-rinv {e₂ = store _ _ _} ()
ιLFP-rinv {e₂ = env _ _ _} ()
ιLFP-rinv {e₂ = break _} ()

open import CSP.Laws.DivFree.CountRename ιLFP ιLFP⁻¹ ιLFP-linv ιLFP-rinv LFPEv-≟ (Net_Api-≟ {Payload})
  using (renE; Σc≤-ren; PA-ren)

-- a `Net_Api` weight pulled back to `LFPEv`
_ʳ : (L.Event → ℕ) → F.Event → ℕ
(c ʳ) e = c (renE e)

------------------------------------------------------------------------
-- views
------------------------------------------------------------------------

-- a LeiosFetch round tree
Rd : Set₁
Rd = PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)

-- a received LFP message on the peer's own cell
rcv : Link → Dir → Time → Mode → Length → MessageLeiosFetchP → F.Event
rcv l d tm md ln msg = F.evLabel _ (receiveLFP l d) (tm , md , ln , leiosFetchP msg)

-- the peer sends `msg` (as `md`), then goes on to `st`
snd : Link → Dir → Mode → MessageLeiosFetchP → LFPState → Rd
snd l d md msg st = sendLFP l d ! (time₀ , md , length₀ , leiosFetchP msg) ⟶ Ret (inj₁ st)

-- client Idle: the api menu (block request / tx-closure request / Done), each a single send
data CIdleV (l : Link) (d : Dir) : F.Event → Rd → Set₁ where
  ciBlk  : ∀ q    → CIdleV l d (F.evLabel _ (apiLPev l d lfpSendBlockRequest) q) (snd l d FromInitiator (MsgLFPBlockRequest q) stBlock)
  ciTxs  : ∀ q bm → CIdleV l d (F.evLabel _ (apiLPev l d lfpSendBlockTxsRequest) (q , bm))
                      (snd l d FromInitiator (MsgLFPBlockTxsRequest q bm) stBlockTxs)
  ciDone : ∀ u    → CIdleV l d (F.evLabel _ (apiLPev l d lfpSendDone) u) (snd l d FromInitiator MsgLFPDone stDone)

-- the client Idle inversion
cIdleV : ∀ {l d x t′} → clientStepP l d stIdle ─[ ev (evl x) ]─► t′ → CIdleV l d x t′
cIdleV {l} {d} (sVis {at = _ , apiLPev l′ d′ lfpSendBlockRequest} {a = q} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciBlk q)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV {l} {d} (sVis {at = _ , apiLPev l′ d′ lfpSendBlockTxsRequest} {a = q , bm} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciTxs q bm)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV {l} {d} (sVis {at = _ , apiLPev l′ d′ lfpSendDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciDone _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendRequestNext} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendDone} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendBlockAnnouncement} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendBlockOffer} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendBlockTxsOffer} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendVotes} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpRecvBlockAnnouncement} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpRecvBlockOffer} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpRecvBlockTxsOffer} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpRecvVotes} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpSendBlock} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxs} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpRecvBlock} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpRecvBlockTxs} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpReqBlockRequest} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpReqBlockTxsRequest} refl ())
cIdleV (sVis {at = _ , sendLFP _ _} refl ())
cIdleV (sVis {at = _ , receiveLFP _ _} refl ())
cIdleV (sVis {at = _ , doneLFP _ _} refl ())

-- client stBlock: the receive menu (the block, reported)
data CBlkV (l : Link) (d : Dir) : F.Event → Rd → Set₁ where
  cbBlk : ∀ {tm md ln} eb → CBlkV l d (rcv l d tm md ln (MsgLFPBlock eb)) (Output ⦃ decEB ⦄ (apiLPev l d lfpRecvBlock) eb (Ret (inj₁ stIdle)))

-- the client stBlock inversion
cBlkV : ∀ {l d x t′} → clientStepP l d stBlock ─[ ev (evl x) ]─► t′ → CBlkV l d x t′
cBlkV {l} {d} (sVis {at = _ , receiveLFP l′ d′} {a = _ , _ , _ , leiosFetchP (MsgLFPBlock eb)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CBlkV l d _) (just-injective br) (cbBlk eb)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest _)} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest _ _)} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs _ _)} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP MsgLFPDone} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
cBlkV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
cBlkV (sVis {at = _ , sendLFP _ _} refl ())
cBlkV (sVis {at = _ , doneLFP _ _} refl ())
cBlkV (sVis {at = _ , apiLPev _ _ _} refl ())

-- client stBlockTxs: the receive menu (the tx closure, reported)
data CTxsV (l : Link) (d : Dir) : F.Event → Rd → Set₁ where
  ctTxs : ∀ {tm md ln} q es → CTxsV l d (rcv l d tm md ln (MsgLFPBlockTxs q es))
                                (Output ⦃ DecEq-TxsReply ⦄ (apiLPev l d lfpRecvBlockTxs) (q , es) (Ret (inj₁ stIdle)))

-- the client stBlockTxs inversion
cTxsV : ∀ {l d x t′} → clientStepP l d stBlockTxs ─[ ev (evl x) ]─► t′ → CTxsV l d x t′
cTxsV {l} {d} (sVis {at = _ , receiveLFP l′ d′} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs q es)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CTxsV l d _) (just-injective br) (ctTxs q es)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest _)} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlock _)} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest _ _)} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP MsgLFPDone} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
cTxsV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
cTxsV (sVis {at = _ , sendLFP _ _} refl ())
cTxsV (sVis {at = _ , doneLFP _ _} refl ())
cTxsV (sVis {at = _ , apiLPev _ _ _} refl ())

-- server Idle: the receive menu (both requests reported / Done)
data SIdleV (l : Link) (d : Dir) : F.Event → Rd → Set₁ where
  siBlk  : ∀ {tm md ln} q    → SIdleV l d (rcv l d tm md ln (MsgLFPBlockRequest q))
                                 (Output ⦃ DecEq-EBPoint ⦄ (apiLPev l d lfpReqBlockRequest) q (Ret (inj₁ stBlock)))
  siTxs  : ∀ {tm md ln} q bm → SIdleV l d (rcv l d tm md ln (MsgLFPBlockTxsRequest q bm))
                                 (Output ⦃ DecEq-TxsRequest ⦄ (apiLPev l d lfpReqBlockTxsRequest) (q , bm) (Ret (inj₁ stBlockTxs)))
  siDone : ∀ {tm md ln}      → SIdleV l d (rcv l d tm md ln MsgLFPDone) (doneLFP l d ⟶₀ Ret (inj₁ stDone))

-- the server Idle inversion
sIdleV : ∀ {l d x t′} → serverStepP l d stIdle ─[ ev (evl x) ]─► t′ → SIdleV l d x t′
sIdleV {l} {d} (sVis {at = _ , receiveLFP l′ d′} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest q)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) (siBlk q)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV {l} {d} (sVis {at = _ , receiveLFP l′ d′} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest q bm)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) (siTxs q bm)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV {l} {d} (sVis {at = _ , receiveLFP l′ d′} {a = _ , _ , _ , leiosFetchP MsgLFPDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) siDone
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlock _)} refl ())
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs _ _)} refl ())
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
sIdleV (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
sIdleV (sVis {at = _ , sendLFP _ _} refl ())
sIdleV (sVis {at = _ , doneLFP _ _} refl ())
sIdleV (sVis {at = _ , apiLPev _ _ _} refl ())

-- server stBlock: the api menu (send the block)
data SBlkV (l : Link) (d : Dir) : F.Event → Rd → Set₁ where
  sbBlk : ∀ eb → SBlkV l d (F.evLabel _ (apiLPev l d lfpSendBlock) eb) (snd l d FromResponder (MsgLFPBlock eb) stIdle)

-- the server stBlock inversion
sBlkV : ∀ {l d x t′} → serverStepP l d stBlock ─[ ev (evl x) ]─► t′ → SBlkV l d x t′
sBlkV {l} {d} (sVis {at = _ , apiLPev l′ d′ lfpSendBlock} {a = eb} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBlkV l d _) (just-injective br) (sbBlk eb)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBlkV (sVis {at = _ , apiLPev _ _ lnpSendRequestNext} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpSendDone} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpSendBlockAnnouncement} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpSendBlockOffer} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpSendBlockTxsOffer} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpSendVotes} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpRecvBlockAnnouncement} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpRecvBlockOffer} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpRecvBlockTxsOffer} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lnpRecvVotes} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lfpSendBlockRequest} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxsRequest} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lfpSendDone} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxs} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lfpRecvBlock} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lfpRecvBlockTxs} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lfpReqBlockRequest} refl ())
sBlkV (sVis {at = _ , apiLPev _ _ lfpReqBlockTxsRequest} refl ())
sBlkV (sVis {at = _ , sendLFP _ _} refl ())
sBlkV (sVis {at = _ , receiveLFP _ _} refl ())
sBlkV (sVis {at = _ , doneLFP _ _} refl ())

-- server stBlockTxs: the api menu (send the tx closure)
data STxsV (l : Link) (d : Dir) : F.Event → Rd → Set₁ where
  stxTxs : ∀ q es → STxsV l d (F.evLabel _ (apiLPev l d lfpSendBlockTxs) (q , es))
                      (snd l d FromResponder (MsgLFPBlockTxs q es) stIdle)

-- the server stBlockTxs inversion
sTxsV : ∀ {l d x t′} → serverStepP l d stBlockTxs ─[ ev (evl x) ]─► t′ → STxsV l d x t′
sTxsV {l} {d} (sVis {at = _ , apiLPev l′ d′ lfpSendBlockTxs} {a = q , es} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (STxsV l d _) (just-injective br) (stxTxs q es)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sTxsV (sVis {at = _ , apiLPev _ _ lnpSendRequestNext} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpSendDone} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpSendBlockAnnouncement} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpSendBlockOffer} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpSendBlockTxsOffer} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpSendVotes} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpRecvBlockAnnouncement} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpRecvBlockOffer} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpRecvBlockTxsOffer} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lnpRecvVotes} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lfpSendBlockRequest} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxsRequest} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lfpSendDone} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lfpSendBlock} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lfpRecvBlock} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lfpRecvBlockTxs} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lfpReqBlockRequest} refl ())
sTxsV (sVis {at = _ , apiLPev _ _ lfpReqBlockTxsRequest} refl ())
sTxsV (sVis {at = _ , sendLFP _ _} refl ())
sTxsV (sVis {at = _ , receiveLFP _ _} refl ())
sTxsV (sVis {at = _ , doneLFP _ _} refl ())

------------------------------------------------------------------------
-- every fact of a step, read off the views ONCE
------------------------------------------------------------------------

-- the zero potential
Φ0 : LFPState → ℕ
Φ0 _ = 0

-- a single output then a return is accessible
aOut : ∀ {B : Set} ⦃ _ : DecEq B ⦄ {e : LFPEv B} {v : B} {r : LFPState ⊎ Rr} → MAccR ∅ES (e ! v ⟶ Ret r)
aOut = MAccR-Output _ _ (MAccR-Ret _)

-- a client step's facts: accessibility, P1 and the five relays
record OkC (a : LFPState) (x : F.Event) (t′ : Rd) : Set₁ where
  constructor okC
  field
    acc : MAccR ∅ES t′
    p1  : StepPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} a x t′
    bq  : StepPot {Rx = Rr} {Φ = Φ0} {wIn BlockReq ʳ} {cCmd lfpSendBlockRequest ʳ} {0} a x t′
    tq  : StepPot {Rx = Rr} {Φ = Φ0} {wIn TxsReq ʳ} {cCmd lfpSendBlockTxsRequest ʳ} {0} a x t′
    bm  : StepPot {Rx = Rr} {Φ = Φ0} {ℓIn TxsReq ʳ} {ℓCmd lfpSendBlockTxsRequest ʳ} {0} a x t′
    es  : StepPot {Rx = Rr} {Φ = Φ0} {ℓRep lfpRecvBlockTxs ʳ} {ℓOut BlockTxs ʳ} {0} a x t′
    nBT : StepPot {Rx = Rr} {Φ = Φ0} {wIn BlockTxs ʳ} {λ _ → 0} {0} a x t′

-- (client Idle; the bitmap relay pays list lengths)
ok-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → OkC stIdle x t′
ok-cIdle (ciBlk _)   = okC aOut sp-Out sp-Out sp-Out sp-Out sp-Out sp-Out
ok-cIdle (ciTxs _ _) = okC aOut sp-Out sp-Out sp-Out (sp-Out≤ z≤n (m≤m+n _ _) ≤-refl) sp-Out sp-Out
ok-cIdle (ciDone _)  = okC aOut sp-Out sp-Out sp-Out sp-Out sp-Out sp-Out

-- (client stBlock)
ok-cBlk : ∀ {l d x t′} → CBlkV l d x t′ → OkC stBlock x t′
ok-cBlk (cbBlk _) = okC (aOut ⦃ decEB ⦄) (sp-Out ⦃ decEB ⦄) (sp-Out ⦃ decEB ⦄) (sp-Out ⦃ decEB ⦄) (sp-Out ⦃ decEB ⦄)
                        (sp-Out ⦃ decEB ⦄) (sp-Out ⦃ decEB ⦄)

-- (client stBlockTxs; the entries relay pays list lengths)
ok-cTxs : ∀ {l d x t′} → CTxsV l d x t′ → OkC stBlockTxs x t′
ok-cTxs (ctTxs _ _) = okC (aOut ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄)
                          (sp-Out≤ ⦃ i ⦄ z≤n (m≤m+n _ _) ≤-refl) (sp-Out ⦃ i ⦄)
  where
    -- the tx-closure carrier's decidable equality
    i = DecEq-TxsReply

-- a server step's facts: accessibility, P1 and the six relays
record OkS (a : LFPState) (x : F.Event) (t′ : Rd) : Set₁ where
  constructor okS
  field
    acc : MAccR ∅ES t′
    p1  : StepPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} a x t′
    bq  : StepPot {Rx = Rr} {Φ = Φ0} {cRep lfpReqBlockRequest ʳ} {wOut BlockReq ʳ} {0} a x t′
    tq  : StepPot {Rx = Rr} {Φ = Φ0} {cRep lfpReqBlockTxsRequest ʳ} {wOut TxsReq ʳ} {0} a x t′
    bm  : StepPot {Rx = Rr} {Φ = Φ0} {ℓRep lfpReqBlockTxsRequest ʳ} {ℓOut TxsReq ʳ} {0} a x t′
    nBQ : StepPot {Rx = Rr} {Φ = Φ0} {wIn BlockReq ʳ} {λ _ → 0} {0} a x t′
    nTQ : StepPot {Rx = Rr} {Φ = Φ0} {wIn TxsReq ʳ} {λ _ → 0} {0} a x t′
    es  : StepPot {Rx = Rr} {Φ = Φ0} {ℓIn BlockTxs ʳ} {ℓCmd lfpSendBlockTxs ʳ} {0} a x t′

-- (server Idle; the bitmap relay pays list lengths)
ok-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → OkS stIdle x t′
ok-sIdle (siBlk _)   = okS (aOut ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄)
                           (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄)
  where
    -- the point carrier's decidable equality
    i = DecEq-EBPoint
ok-sIdle (siTxs _ _) = okS (aOut ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out≤ ⦃ i ⦄ z≤n (m≤m+n _ _) ≤-refl)
                           (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄) (sp-Out ⦃ i ⦄)
  where
    -- the tx-closure-request carrier's decidable equality
    i = DecEq-TxsRequest
ok-sIdle siDone      = okS (MAccR-⟶₀ _ (MAccR-Ret _)) sp-⟶ sp-⟶ sp-⟶ sp-⟶ sp-⟶ sp-⟶ sp-⟶

-- (server stBlock)
ok-sBlk : ∀ {l d x t′} → SBlkV l d x t′ → OkS stBlock x t′
ok-sBlk (sbBlk _) = okS aOut sp-Out sp-Out sp-Out sp-Out sp-Out sp-Out sp-Out

-- (server stBlockTxs; the entries relay pays list lengths)
ok-sTxs : ∀ {l d x t′} → STxsV l d x t′ → OkS stBlockTxs x t′
ok-sTxs (stxTxs _ _) = okS aOut sp-Out sp-Out sp-Out sp-Out sp-Out sp-Out (sp-Out≤ z≤n (m≤m+n _ _) ≤-refl)

-- the client's rounds, for any fact its steps provide
rd-c : ∀ {Φ : LFPState → ℕ} {cost credit : F.Event → ℕ} {K}
     → (∀ {a x t′} → OkC a x t′ → StepPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} a x t′)
     → ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} st (clientStepP l d st)
rd-c π stIdle     = rp-pch λ st → π (ok-cIdle (cIdleV st))
rd-c π stBlock    = rp-pch λ st → π (ok-cBlk (cBlkV st))
rd-c π stBlockTxs = rp-pch λ st → π (ok-cTxs (cTxsV st))
rd-c π stDone     = rp-done

-- the server's rounds, for any fact its steps provide
rd-s : ∀ {Φ : LFPState → ℕ} {cost credit : F.Event → ℕ} {K}
     → (∀ {a x t′} → OkS a x t′ → StepPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} a x t′)
     → ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} st (serverStepP l d st)
rd-s π stIdle     = rp-pch λ st → π (ok-sIdle (sIdleV st))
rd-s π stBlock    = rp-pch λ st → π (ok-sBlk (sBlkV st))
rd-s π stBlockTxs = rp-pch λ st → π (ok-sTxs (sTxsV st))
rd-s π stDone     = rp-done

------------------------------------------------------------------------
-- premise (b)
------------------------------------------------------------------------

-- every client body state is accessible at every reachable state
cbodyR : ∀ {l d} st → MAccR ∅ES (clientStepP l d st)
cbodyR {l} {d} stIdle     = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cIdle (cIdleV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR {l} {d} stBlock    = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cBlk (cBlkV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR {l} {d} stBlockTxs = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cTxs (cTxsV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR stDone             = MAccR-Ret _

-- every client round starts with a visible event
cbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (clientStepP l d st)
cbodyG stIdle     = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stBlock    = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stBlockTxs = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stDone     = NoRetBy-Ret λ ()

-- every server body state is accessible at every reachable state
sbodyR : ∀ {l d} st → MAccR ∅ES (serverStepP l d st)
sbodyR {l} {d} stIdle     = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sIdle (sIdleV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR {l} {d} stBlock    = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sBlk (sBlkV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR {l} {d} stBlockTxs = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sTxs (sTxsV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR stDone             = MAccR-Ret _

-- every server round starts with a visible event
sbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (serverStepP l d st)
sbodyG stIdle     = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stBlock    = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stBlockTxs = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stDone     = NoRetBy-Ret λ ()

-- THE CLIENT LEAF
lfpClientA-τ : ∀ l d → DF.τ-AccReach (LFPclientA l d)
lfpClientA-τ l d = τ-AccReach-renameMap (MAccR→τ-AccReach (MAccR-iter {k = clientStepP l d} cbodyG cbodyR stIdle))

-- THE SERVER LEAF
lfpServerA-τ : ∀ l d → DF.τ-AccReach (LFPserverA l d)
lfpServerA-τ l d = τ-AccReach-renameMap (MAccR→τ-AccReach (MAccR-iter {k = serverStepP l d} sbodyG sbodyR stIdle))

------------------------------------------------------------------------
-- counting: `potIter` at `LFPEv`, carried onto `Net_Api` by `Σc≤-ren`
------------------------------------------------------------------------

-- P1 (LFP client): every wire input but one was commanded through the api
lfpClientA-P1 : ∀ l d {s W} → LFPclientA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
lfpClientA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 _ _ 1 (rd-c OkC.p1 {l} {d}) stIdle)

-- P1 (LFP server)
lfpServerA-P1 : ∀ l d {s W} → LFPserverA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
lfpServerA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 _ _ 1 (rd-s OkS.p1 {l} {d}) stIdle)

-- RELAY (client): every block request it sends was commanded
lfpClientA-bq : ∀ l d {s W} → LFPclientA l d ⟹⟨ s ⟩ W
              → Σc (wIn BlockReq) (labels s) ≤ Σc (cCmd lfpSendBlockRequest) (labels s)
lfpClientA-bq l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (wIn BlockReq) (cCmd lfpSendBlockRequest) 0 (potIter Φ0 _ _ 0 (rd-c OkC.bq {l} {d}) stIdle) tr)

-- RELAY (client): every tx-closure request it sends was commanded
lfpClientA-tq : ∀ l d {s W} → LFPclientA l d ⟹⟨ s ⟩ W
              → Σc (wIn TxsReq) (labels s) ≤ Σc (cCmd lfpSendBlockTxsRequest) (labels s)
lfpClientA-tq l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (wIn TxsReq) (cCmd lfpSendBlockTxsRequest) 0 (potIter Φ0 _ _ 0 (rd-c OkC.tq {l} {d}) stIdle) tr)

-- RELAY (client): the bitmap entries it requests were commanded (list lengths)
lfpClientA-bm : ∀ l d {s W} → LFPclientA l d ⟹⟨ s ⟩ W
              → Σc (ℓIn TxsReq) (labels s) ≤ Σc (ℓCmd lfpSendBlockTxsRequest) (labels s)
lfpClientA-bm l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (ℓIn TxsReq) (ℓCmd lfpSendBlockTxsRequest) 0 (potIter Φ0 _ _ 0 (rd-c OkC.bm {l} {d}) stIdle) tr)

-- RELAY (client): the tx-closure entries it reports, it received (list lengths)
lfpClientA-es : ∀ l d {s W} → LFPclientA l d ⟹⟨ s ⟩ W
              → Σc (ℓRep lfpRecvBlockTxs) (labels s) ≤ Σc (ℓOut BlockTxs) (labels s)
lfpClientA-es l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (ℓRep lfpRecvBlockTxs) (ℓOut BlockTxs) 0 (potIter Φ0 _ _ 0 (rd-c OkC.es {l} {d}) stIdle) tr)

-- RELAY (client): it puts no tx closure on the wire
lfpClientA-noBT : ∀ l d {s W} → LFPclientA l d ⟹⟨ s ⟩ W → Σc (wIn BlockTxs) (labels s) ≡ 0
lfpClientA-noBT l d {s} tr = none0 {ls = labels s}
  (Σc≤-ren (wIn BlockTxs) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd-c OkC.nBT {l} {d}) stIdle) tr)

-- RELAY (server): every block request it reports, it received
lfpServerA-bq : ∀ l d {s W} → LFPserverA l d ⟹⟨ s ⟩ W
              → Σc (cRep lfpReqBlockRequest) (labels s) ≤ Σc (wOut BlockReq) (labels s)
lfpServerA-bq l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (cRep lfpReqBlockRequest) (wOut BlockReq) 0 (potIter Φ0 _ _ 0 (rd-s OkS.bq {l} {d}) stIdle) tr)

-- RELAY (server): every tx-closure request it reports, it received
lfpServerA-tq : ∀ l d {s W} → LFPserverA l d ⟹⟨ s ⟩ W
              → Σc (cRep lfpReqBlockTxsRequest) (labels s) ≤ Σc (wOut TxsReq) (labels s)
lfpServerA-tq l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (cRep lfpReqBlockTxsRequest) (wOut TxsReq) 0 (potIter Φ0 _ _ 0 (rd-s OkS.tq {l} {d}) stIdle) tr)

-- RELAY (server): the bitmap entries it reports, it received (list lengths)
lfpServerA-bm : ∀ l d {s W} → LFPserverA l d ⟹⟨ s ⟩ W
              → Σc (ℓRep lfpReqBlockTxsRequest) (labels s) ≤ Σc (ℓOut TxsReq) (labels s)
lfpServerA-bm l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (ℓRep lfpReqBlockTxsRequest) (ℓOut TxsReq) 0 (potIter Φ0 _ _ 0 (rd-s OkS.bm {l} {d}) stIdle) tr)

-- RELAY (server): it puts no block request on the wire
lfpServerA-noBQ : ∀ l d {s W} → LFPserverA l d ⟹⟨ s ⟩ W → Σc (wIn BlockReq) (labels s) ≡ 0
lfpServerA-noBQ l d {s} tr = none0 {ls = labels s}
  (Σc≤-ren (wIn BlockReq) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd-s OkS.nBQ {l} {d}) stIdle) tr)

-- RELAY (server): it puts no tx-closure request on the wire
lfpServerA-noTQ : ∀ l d {s W} → LFPserverA l d ⟹⟨ s ⟩ W → Σc (wIn TxsReq) (labels s) ≡ 0
lfpServerA-noTQ l d {s} tr = none0 {ls = labels s}
  (Σc≤-ren (wIn TxsReq) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd-s OkS.nTQ {l} {d}) stIdle) tr)

-- RELAY (server): the tx-closure entries it sends were commanded (list lengths)
lfpServerA-es : ∀ l d {s W} → LFPserverA l d ⟹⟨ s ⟩ W
              → Σc (ℓIn BlockTxs) (labels s) ≤ Σc (ℓCmd lfpSendBlockTxs) (labels s)
lfpServerA-es l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (ℓIn BlockTxs) (ℓCmd lfpSendBlockTxs) 0 (potIter Φ0 _ _ 0 (rd-s OkS.es {l} {d}) stIdle) tr)

------------------------------------------------------------------------
-- provenance (D1-b): LeiosFetch never touches the block chain — by its
-- renaming alone (`ChS` has no clause for a LeiosFetch cell, `apiLP`, `done`)
------------------------------------------------------------------------

-- no LFP label is a chain label
noChain : ∀ {e : F.Event} {y} → ChS (renE e) y → ⊥
noChain {F.evLabel _ (sendLFP _ _) _}    ()
noChain {F.evLabel _ (receiveLFP _ _) _} ()
noChain {F.evLabel _ (apiLPev _ _ _) _}  ()
noChain {F.evLabel _ (doneLFP _ _) _}    ()

-- every renamed LFP process is chain-free
lfpA-PA : ∀ {ℓr} {R : Set ℓr} {P : PTree LFPEv (ExtI LFPEv) R} → PL.PA ChS ChS InP (RenLFP.renameMap P)
lfpA-PA = PA-ren (pa λ {_} {s} _ → Prov-free noChain (S.labels s))

-- (the client)
lfpClientA-PA : ∀ l d → PL.PA ChS ChS InP (LFPclientA l d)
lfpClientA-PA l d = lfpA-PA

-- (the server)
lfpServerA-PA : ∀ l d → PL.PA ChS ChS InP (LFPserverA l d)
lfpServerA-PA l d = lfpA-PA

------------------------------------------------------------------------
-- Task 9a (F3a): the report alphabet — each LFP side makes only its own
-- reports (none of the LNP client's, none of the other LFP side's)
------------------------------------------------------------------------

-- a client step makes no foreign report
NRc : LFPState → F.Event → Rd → Set₁
NRc = StepPot {Rx = Rr} {Φ = Φ0} {(λ e → repLNP e + repLFs e) ʳ} {λ _ → 0} {0}

-- (client Idle)
nr-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → NRc stIdle x t′
nr-cIdle (ciBlk _)   = sp-Out
nr-cIdle (ciTxs _ _) = sp-Out
nr-cIdle (ciDone _)  = sp-Out

-- (client stBlock, stBlockTxs)
nr-cBlk : ∀ {l d x t′} → CBlkV l d x t′ → NRc stBlock x t′
nr-cBlk (cbBlk _) = sp-Out ⦃ decEB ⦄

-- (client stBlockTxs)
nr-cTxs : ∀ {l d x t′} → CTxsV l d x t′ → NRc stBlockTxs x t′
nr-cTxs (ctTxs _ _) = sp-Out ⦃ DecEq-TxsReply ⦄

-- the client's rounds
nr-c : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {(λ e → repLNP e + repLFs e) ʳ} {λ _ → 0} {0} st (clientStepP l d st)
nr-c stIdle     = rp-pch λ st → nr-cIdle (cIdleV st)
nr-c stBlock    = rp-pch λ st → nr-cBlk (cBlkV st)
nr-c stBlockTxs = rp-pch λ st → nr-cTxs (cTxsV st)
nr-c stDone     = rp-done

-- a server step makes no foreign report
NRs : LFPState → F.Event → Rd → Set₁
NRs = StepPot {Rx = Rr} {Φ = Φ0} {(λ e → repLNP e + repLFc e) ʳ} {λ _ → 0} {0}

-- (server Idle)
nr-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → NRs stIdle x t′
nr-sIdle (siBlk _)   = sp-Out ⦃ DecEq-EBPoint ⦄
nr-sIdle (siTxs _ _) = sp-Out ⦃ DecEq-TxsRequest ⦄
nr-sIdle siDone      = sp-⟶

-- (server stBlock)
nr-sBlk : ∀ {l d x t′} → SBlkV l d x t′ → NRs stBlock x t′
nr-sBlk (sbBlk _) = sp-Out

-- (server stBlockTxs)
nr-sTxs : ∀ {l d x t′} → STxsV l d x t′ → NRs stBlockTxs x t′
nr-sTxs (stxTxs _ _) = sp-Out

-- the server's rounds
nr-s : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {(λ e → repLNP e + repLFc e) ʳ} {λ _ → 0} {0} st (serverStepP l d st)
nr-s stIdle     = rp-pch λ st → nr-sIdle (sIdleV st)
nr-s stBlock    = rp-pch λ st → nr-sBlk (sBlkV st)
nr-s stBlockTxs = rp-pch λ st → nr-sTxs (sTxsV st)
nr-s stDone     = rp-done

-- ALPHABET (client): it makes no LNP-client report and no LFP-server report
lfpClientA-noRep : ∀ l d {s W} → LFPclientA l d ⟹⟨ s ⟩ W → Σc (λ e → repLNP e + repLFs e) (labels s) ≡ 0
lfpClientA-noRep l d {s} tr =
  none0 {ls = labels s} (Σc≤-ren (λ e → repLNP e + repLFs e) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (nr-c {l} {d}) stIdle) tr)

-- ALPHABET (server): it makes no LNP-client report and no LFP-client report
lfpServerA-noRep : ∀ l d {s W} → LFPserverA l d ⟹⟨ s ⟩ W → Σc (λ e → repLNP e + repLFc e) (labels s) ≡ 0
lfpServerA-noRep l d {s} tr =
  none0 {ls = labels s} (Σc≤-ren (λ e → repLNP e + repLFc e) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (nr-s {l} {d}) stIdle) tr)

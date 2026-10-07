{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: the prototype LeiosNotify PEERS (LNP).
--   * VIEWS: each menu state of each side inverted ONCE at `LNPEv`; every
--     fact of a side is read off one view-to-obligations function
--     (`ok-c…`/`ok-s…`: accessibility and every counting step at once)
--   * premise (b): `lnpClientA-τ`, `lnpServerA-τ`.  The server's
--     RequestNext round is the receive ALONE (`Ret (inj₁ stBusy)`, no event
--     after it) — still guarded: its first event is the receive
--   * counting on the peer's own renamed trace: P1, and the relays —
--     client: notification reports ≤ notifications received, vote reports
--     ≤ votes received (list lengths), sends no notification; server:
--     notifications sent ≤ commanded, votes sent ≤ commanded.  "The
--     notification command / report" is the SUM over the three LNP
--     notification tags (`cCmdN`, `cRepN`)
--   * provenance: chain-free by renaming alone (`lnpA-PA`)
--   * graceful shutdown (PR 2344, the blueprint table literally, no
--     pipelining): the client's quit round is api + one send, its `stQuit`
--     round the single MsgDone receive, its MsgCanceled round a single
--     receive; the server's cancel round is api (`lnpSendCanceled`) + one
--     send, its `stQuit` round `done` + one send — every wire send is paid by
--     its own api / done event, so both P1s run on the zero potential `Φ0`
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.PeerLNP (p : Params) where

open import Data.Empty using (⊥)
open import Data.List using (List)
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
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open import Cardano_network.Parametric.Leios.PeersP p using (ιLNP; ιLNP⁻¹; ιLNP-linv; LNPclientA; LNPserverA)
open Params p using (time₀; length₀; Time; Length; VoteBlob)
import CSP.Rename {E₁ = LNPEv} {E₂ = Net_Api Payload} ιLNP ιLNP⁻¹ ιLNP-linv as RenLNP
open import CSP.Operators LNPEv-≟ using (∅ES; Ret; Output; Prefix; Prefix₀)
open import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} using (_─[_]─►_; ev; evl; sVis)
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as N
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as L
import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as DF
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.ModAcc LNPEv-≟ using (MAccR; MAccR→τ-AccReach)
open import CSP.Laws.DivFree.Reach LNPEv-≟ using (MAccR-Ret)
open import CSP.Laws.DivFree.Loop LNPEv-≟
  using (NoRetBy; Looping; NoRetBy-mono; Guarded-react; MAccR-react; MAccR-Output; MAccR-iter)
open import CSP.Laws.DivFree.ReachRename {E₁ = LNPEv} {E₂ = Net_Api Payload} ιLNP ιLNP⁻¹ ιLNP-linv using (τ-AccReach-renameMap)
import CSP.Laws.DivFree.Count LNPEv-≟ as S
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (slack0; none0)
open import CSP.Laws.DivFree.CountMore LNPEv-≟ using (RoundPot; StepPot; rp-pch; sp-Ret; sp-Out; sp-Out≤; potIter)
open import CSP.Laws.DivFree.Prov LNPEv-≟ using (pa)
open import CSP.Laws.DivFree.ProvMore LNPEv-≟ using (Prov-free)
import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) as PL
open import Cardano_network.Parametric.Leios.NoLivelock.Weights p
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF p using (ChS; InP)

------------------------------------------------------------------------
-- the renaming pulls back exactly its images (`CountRename`'s `ι-rinv`)
------------------------------------------------------------------------

-- ιLNP⁻¹ pulls back only ιLNP-images
ιLNP-rinv : ∀ {A} {e₂ : Net_Api Payload A} {e : LNPEv A} → ιLNP⁻¹ e₂ ≡ just e → e₂ ≡ ιLNP e
ιLNP-rinv {e₂ = input  _ _ N2N_LeiosNotify} refl = refl
ιLNP-rinv {e₂ = output _ _ N2N_LeiosNotify} refl = refl
ιLNP-rinv {e₂ = apiLP  _ _ _} refl = refl
ιLNP-rinv {e₂ = done   _ _ N2N_LeiosNotify} refl = refl
ιLNP-rinv {e₂ = input  _ _ N2N_ChainSync} ()
ιLNP-rinv {e₂ = input  _ _ N2N_BlockFetch} ()
ιLNP-rinv {e₂ = input  _ _ N2N_TxSubmission} ()
ιLNP-rinv {e₂ = input  _ _ N2N_KeepAlive} ()
ιLNP-rinv {e₂ = input  _ _ N2N_LeiosFetch} ()
ιLNP-rinv {e₂ = output _ _ N2N_ChainSync} ()
ιLNP-rinv {e₂ = output _ _ N2N_BlockFetch} ()
ιLNP-rinv {e₂ = output _ _ N2N_TxSubmission} ()
ιLNP-rinv {e₂ = output _ _ N2N_KeepAlive} ()
ιLNP-rinv {e₂ = output _ _ N2N_LeiosFetch} ()
ιLNP-rinv {e₂ = done   _ _ N2N_ChainSync} ()
ιLNP-rinv {e₂ = done   _ _ N2N_BlockFetch} ()
ιLNP-rinv {e₂ = done   _ _ N2N_TxSubmission} ()
ιLNP-rinv {e₂ = done   _ _ N2N_KeepAlive} ()
ιLNP-rinv {e₂ = done   _ _ N2N_LeiosFetch} ()
ιLNP-rinv {e₂ = sndmsg _ _ _} ()
ιLNP-rinv {e₂ = rcvmsg _ _ _} ()
ιLNP-rinv {e₂ = tx _ _ _} ()
ιLNP-rinv {e₂ = sndack _ _ _} ()
ιLNP-rinv {e₂ = rcvack _ _ _} ()
ιLNP-rinv {e₂ = ack _ _ _} ()
ιLNP-rinv {e₂ = apiBF _ _ _} ()
ιLNP-rinv {e₂ = apiTS _ _ _} ()
ιLNP-rinv {e₂ = apiKA _ _ _} ()
ιLNP-rinv {e₂ = apiLN _ _ _} ()
ιLNP-rinv {e₂ = apiLF _ _ _} ()
ιLNP-rinv {e₂ = apiCS _ _ _} ()
ιLNP-rinv {e₂ = store _ _ _} ()
ιLNP-rinv {e₂ = env _ _ _} ()
ιLNP-rinv {e₂ = break _} ()

open import CSP.Laws.DivFree.CountRename ιLNP ιLNP⁻¹ ιLNP-linv ιLNP-rinv LNPEv-≟ (Net_Api-≟ {Payload})
  using (renE; Σc≤-ren; PA-ren)

-- a `Net_Api` weight pulled back to `LNPEv`
_ʳ : (L.Event → ℕ) → N.Event → ℕ
(c ʳ) e = c (renE e)

-- the notification COMMANDS: the sum over the three LNP notification tags
cCmdN : L.Event → ℕ
cCmdN e = cCmd lnpSendBlockAnnouncement e + cCmd lnpSendBlockOffer e + cCmd lnpSendBlockTxsOffer e

-- the notification REPORTS: the sum over the three LNP notification tags
cRepN : L.Event → ℕ
cRepN e = cRep lnpRecvBlockAnnouncement e + cRep lnpRecvBlockOffer e + cRep lnpRecvBlockTxsOffer e

------------------------------------------------------------------------
-- views
------------------------------------------------------------------------

-- a LeiosNotify round tree
Rd : Set₁
Rd = PTree LNPEv (ExtI LNPEv) (LNPState ⊎ Rr)

-- a received LNP message on the peer's own cell
rcv : Link → Dir → Time → Mode → Length → MessageLeiosNotifyP → N.Event
rcv l d tm md ln msg = N.evLabel _ (receiveLNP l d) (tm , md , ln , leiosNotifyP msg)

-- the peer sends `msg` (as `md`), then goes on to `st`
snd : Link → Dir → Mode → MessageLeiosNotifyP → LNPState → Rd
snd l d md msg st = sendLNP l d ! (time₀ , md , length₀ , leiosNotifyP msg) ⟶ Ret (inj₁ st)

-- the vote-list carrier's decidable equality (the one the peers use)
iV : DecEq (List VoteBlob)
iV = DecEqI.DecEq-List

-- client Idle: the api menu (RequestNext / Quit), each a single send
data CIdleV (l : Link) (d : Dir) : N.Event → Rd → Set₁ where
  ciNext : ∀ u → CIdleV l d (N.evLabel _ (apiLPev l d lnpSendRequestNext) u) (snd l d FromInitiator MsgLNPRequestNext stBusy)
  ciQuit : ∀ u → CIdleV l d (N.evLabel _ (apiLPev l d lnpSendDone) u) (snd l d FromInitiator MsgLNPQuit stQuit)

-- the client Idle inversion
cIdleV : ∀ {l d x t′} → clientStepP l d stIdle ─[ ev (evl x) ]─► t′ → CIdleV l d x t′
cIdleV {l} {d} (sVis {at = _ , apiLPev l′ d′ lnpSendRequestNext} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciNext _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV {l} {d} (sVis {at = _ , apiLPev l′ d′ lnpSendDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciQuit _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendBlockAnnouncement} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendBlockOffer} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendBlockTxsOffer} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendVotes} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpSendCanceled} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpRecvBlockAnnouncement} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpRecvBlockOffer} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpRecvBlockTxsOffer} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lnpRecvVotes} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpSendBlockRequest} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxsRequest} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpSendDone} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpSendBlock} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxs} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpRecvBlock} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpRecvBlockTxs} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpReqBlockRequest} refl ())
cIdleV (sVis {at = _ , apiLPev _ _ lfpReqBlockTxsRequest} refl ())
cIdleV (sVis {at = _ , sendLNP _ _} refl ())
cIdleV (sVis {at = _ , receiveLNP _ _} refl ())
cIdleV (sVis {at = _ , doneLNP _ _} refl ())

-- client Busy: the receive menu, each notification reported; MsgCanceled accepted silently
data CBusyV (l : Link) (d : Dir) : N.Event → Rd → Set₁ where
  cbCan  : ∀ {tm md ln}      → CBusyV l d (rcv l d tm md ln MsgLNPCanceled) (Ret (inj₁ stIdle))
  cbAnn  : ∀ {tm md ln} h    → CBusyV l d (rcv l d tm md ln (MsgLNPBlockAnnouncement h))
                                 (apiLPev l d lnpRecvBlockAnnouncement ! h ⟶ Ret (inj₁ stIdle))
  cbOff  : ∀ {tm md ln} q sz → CBusyV l d (rcv l d tm md ln (MsgLNPBlockOffer q sz))
                                 (Output ⦃ DecEq-Offer ⦄ (apiLPev l d lnpRecvBlockOffer) (q , sz) (Ret (inj₁ stIdle)))
  cbTxs  : ∀ {tm md ln} q    → CBusyV l d (rcv l d tm md ln (MsgLNPBlockTxsOffer q))
                                 (Output ⦃ DecEq-EBPoint ⦄ (apiLPev l d lnpRecvBlockTxsOffer) q (Ret (inj₁ stIdle)))
  cbVote : ∀ {tm md ln} vs   → CBusyV l d (rcv l d tm md ln (MsgLNPVotes vs))
                                 (Output ⦃ iV ⦄ (apiLPev l d lnpRecvVotes) vs (Ret (inj₁ stIdle)))

-- the client Busy inversion
cBusyV : ∀ {l d x t′} → clientStepP l d stBusy ─[ ev (evl x) ]─► t′ → CBusyV l d x t′
cBusyV {l} {d} (sVis {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockAnnouncement h)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CBusyV l d _) (just-injective br) (cbAnn h)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cBusyV {l} {d} (sVis {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockOffer q sz)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CBusyV l d _) (just-injective br) (cbOff q sz)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cBusyV {l} {d} (sVis {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockTxsOffer q)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CBusyV l d _) (just-injective br) (cbTxs q)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cBusyV {l} {d} (sVis {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , leiosNotifyP (MsgLNPVotes vs)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CBusyV l d _) (just-injective br) (cbVote vs)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cBusyV {l} {d} (sVis {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , leiosNotifyP MsgLNPCanceled} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CBusyV l d _) (just-injective br) cbCan
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPRequestNext} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPDone} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPQuit} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , keepAlive _} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , blockFetch _} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , chainSync _} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , txSubmission _} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
cBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
cBusyV (sVis {at = _ , sendLNP _ _} refl ())
cBusyV (sVis {at = _ , doneLNP _ _} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpSendRequestNext} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpSendDone} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpSendCanceled} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpSendBlockAnnouncement} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpSendBlockOffer} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpSendBlockTxsOffer} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpSendVotes} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpRecvBlockAnnouncement} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpRecvBlockOffer} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpRecvBlockTxsOffer} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lnpRecvVotes} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpSendBlockRequest} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxsRequest} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpSendDone} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpSendBlock} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxs} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpRecvBlock} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpRecvBlockTxs} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpReqBlockRequest} refl ())
cBusyV (sVis {at = _ , apiLPev _ _ lfpReqBlockTxsRequest} refl ())

-- client Quit: MsgDone ends it (√)
data CQuitV (l : Link) (d : Dir) : N.Event → Rd → Set₁ where
  cqDone  : ∀ {tm md ln} → CQuitV l d (rcv l d tm md ln MsgLNPDone) (Ret (inj₂ tt))

-- the client Quit inversion
cQuitV : ∀ {l d x t′} → clientStepP l d stQuit ─[ ev (evl x) ]─► t′ → CQuitV l d x t′
cQuitV {l} {d} (sVis {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , leiosNotifyP MsgLNPDone} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CQuitV l d _) (just-injective br) cqDone
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockAnnouncement _)} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockOffer _ _)} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockTxsOffer _)} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPVotes _)} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPCanceled} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPRequestNext} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPQuit} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , keepAlive _} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , blockFetch _} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , chainSync _} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , txSubmission _} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
cQuitV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
cQuitV (sVis {at = _ , sendLNP _ _} refl ())
cQuitV (sVis {at = _ , doneLNP _ _} refl ())
cQuitV (sVis {at = _ , apiLPev _ _ _} refl ())

-- server Idle: the receive menu (RequestNext alone / Quit alone)
data SIdleV (l : Link) (d : Dir) : N.Event → Rd → Set₁ where
  siNext : ∀ {tm md ln} → SIdleV l d (rcv l d tm md ln MsgLNPRequestNext) (Ret (inj₁ stBusy))
  siQuit : ∀ {tm md ln} → SIdleV l d (rcv l d tm md ln MsgLNPQuit) (Ret (inj₁ stQuit))

-- the server Idle inversion
sIdleV : ∀ {l d x t′} → serverStepP l d stIdle ─[ ev (evl x) ]─► t′ → SIdleV l d x t′
sIdleV {l} {d} (sVis {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , leiosNotifyP MsgLNPRequestNext} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) siNext
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV {l} {d} (sVis {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , leiosNotifyP MsgLNPQuit} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) siQuit
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockAnnouncement _)} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockOffer _ _)} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockTxsOffer _)} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPVotes _)} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPDone} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPCanceled} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , keepAlive _} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , blockFetch _} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , chainSync _} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , txSubmission _} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
sIdleV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
sIdleV (sVis {at = _ , sendLNP _ _} refl ())
sIdleV (sVis {at = _ , doneLNP _ _} refl ())
sIdleV (sVis {at = _ , apiLPev _ _ _} refl ())

-- server Busy: the api menu (one notification, the votes, or the cancel), each a single send
data SBusyV (l : Link) (d : Dir) : N.Event → Rd → Set₁ where
  sbCan  : ∀ u    → SBusyV l d (N.evLabel _ (apiLPev l d lnpSendCanceled) u)
                      (snd l d FromResponder MsgLNPCanceled stIdle)
  sbAnn  : ∀ h    → SBusyV l d (N.evLabel _ (apiLPev l d lnpSendBlockAnnouncement) h)
                      (snd l d FromResponder (MsgLNPBlockAnnouncement h) stIdle)
  sbOff  : ∀ q sz → SBusyV l d (N.evLabel _ (apiLPev l d lnpSendBlockOffer) (q , sz))
                      (snd l d FromResponder (MsgLNPBlockOffer q sz) stIdle)
  sbTxs  : ∀ q    → SBusyV l d (N.evLabel _ (apiLPev l d lnpSendBlockTxsOffer) q)
                      (snd l d FromResponder (MsgLNPBlockTxsOffer q) stIdle)
  sbVote : ∀ vs   → SBusyV l d (N.evLabel _ (apiLPev l d lnpSendVotes) vs)
                      (snd l d FromResponder (MsgLNPVotes vs) stIdle)

-- the server Busy inversion
sBusyV : ∀ {l d x t′} → serverStepP l d stBusy ─[ ev (evl x) ]─► t′ → SBusyV l d x t′
sBusyV {l} {d} (sVis {at = _ , apiLPev l′ d′ lnpSendBlockAnnouncement} {a = h} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBusyV l d _) (just-injective br) (sbAnn h)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBusyV {l} {d} (sVis {at = _ , apiLPev l′ d′ lnpSendBlockOffer} {a = q , sz} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBusyV l d _) (just-injective br) (sbOff q sz)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBusyV {l} {d} (sVis {at = _ , apiLPev l′ d′ lnpSendBlockTxsOffer} {a = q} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBusyV l d _) (just-injective br) (sbTxs q)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBusyV {l} {d} (sVis {at = _ , apiLPev l′ d′ lnpSendVotes} {a = vs} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBusyV l d _) (just-injective br) (sbVote vs)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBusyV {l} {d} (sVis {at = _ , apiLPev l′ d′ lnpSendCanceled} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBusyV l d _) (just-injective br) (sbCan _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBusyV (sVis {at = _ , apiLPev _ _ lnpSendRequestNext} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lnpSendDone} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lnpRecvBlockAnnouncement} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lnpRecvBlockOffer} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lnpRecvBlockTxsOffer} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lnpRecvVotes} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpSendBlockRequest} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxsRequest} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpSendDone} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpSendBlock} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxs} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpRecvBlock} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpRecvBlockTxs} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpReqBlockRequest} refl ())
sBusyV (sVis {at = _ , apiLPev _ _ lfpReqBlockTxsRequest} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPQuit} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPRequestNext} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockAnnouncement _)} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockOffer _ _)} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPBlockTxsOffer _)} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP (MsgLNPVotes _)} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPDone} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotifyP MsgLNPCanceled} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , keepAlive _} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , blockFetch _} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , chainSync _} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , txSubmission _} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
sBusyV (sVis {at = _ , receiveLNP _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
sBusyV (sVis {at = _ , sendLNP _ _} refl ())
sBusyV (sVis {at = _ , doneLNP _ _} refl ())

-- server Quit: the peer-local Done, then MsgDone, then √
data SQuitV (l : Link) (d : Dir) : N.Event → Rd → Set₁ where
  sqDone : ∀ u → SQuitV l d (N.evLabel _ (doneLNP l d) u)
                   (sendLNP l d ! (time₀ , FromResponder , length₀ , leiosNotifyP MsgLNPDone) ⟶ Ret (inj₂ tt))

-- the server Quit inversion
sQuitV : ∀ {l d x t′} → serverStepP l d stQuit ─[ ev (evl x) ]─► t′ → SQuitV l d x t′
sQuitV {l} {d} (sVis {at = _ , doneLNP l′ d′} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SQuitV l d _) (just-injective br) (sqDone _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sQuitV (sVis {at = _ , sendLNP _ _} refl ())
sQuitV (sVis {at = _ , receiveLNP _ _} refl ())
sQuitV (sVis {at = _ , apiLPev _ _ _} refl ())

------------------------------------------------------------------------
-- every fact of a step, read off the views ONCE
------------------------------------------------------------------------

-- the zero potential
Φ0 : LNPState → ℕ
Φ0 _ = 0

-- a single output then a return is accessible
aOut : ∀ {B : Set} ⦃ _ : DecEq B ⦄ {e : LNPEv B} {v : B} {r : LNPState ⊎ Rr} → MAccR ∅ES (e ! v ⟶ Ret r)
aOut = MAccR-Output _ _ (MAccR-Ret _)

-- a client step's facts: accessibility, P1 and the three relays
record OkC (a : LNPState) (x : N.Event) (t′ : Rd) : Set₁ where
  constructor okC
  field
    acc : MAccR ∅ES t′
    p1  : StepPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} a x t′
    rep : StepPot {Rx = Rr} {Φ = Φ0} {cRepN ʳ} {wOut notif ʳ} {0} a x t′
    vot : StepPot {Rx = Rr} {Φ = Φ0} {ℓRep lnpRecvVotes ʳ} {ℓOut votes ʳ} {0} a x t′
    noN : StepPot {Rx = Rr} {Φ = Φ0} {wIn notif ʳ} {λ _ → 0} {0} a x t′

-- (client Idle)
ok-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → OkC stIdle x t′
ok-cIdle (ciNext _) = okC aOut sp-Out sp-Out sp-Out sp-Out
ok-cIdle (ciQuit _) = okC aOut sp-Out sp-Out sp-Out sp-Out

-- (client Busy; the votes relay pays list lengths)
ok-cBusy : ∀ {l d x t′} → CBusyV l d x t′ → OkC stBusy x t′
ok-cBusy cbCan       = okC (MAccR-Ret _) sp-Ret sp-Ret sp-Ret sp-Ret
ok-cBusy (cbAnn _)   = okC aOut sp-Out sp-Out sp-Out sp-Out
ok-cBusy (cbOff _ _) = okC (aOut ⦃ DecEq-Offer ⦄) (sp-Out ⦃ DecEq-Offer ⦄) (sp-Out ⦃ DecEq-Offer ⦄) (sp-Out ⦃ DecEq-Offer ⦄) (sp-Out ⦃ DecEq-Offer ⦄)
ok-cBusy (cbTxs _)   = okC (aOut ⦃ DecEq-EBPoint ⦄) (sp-Out ⦃ DecEq-EBPoint ⦄) (sp-Out ⦃ DecEq-EBPoint ⦄) (sp-Out ⦃ DecEq-EBPoint ⦄) (sp-Out ⦃ DecEq-EBPoint ⦄)
ok-cBusy (cbVote _)  = okC (aOut ⦃ iV ⦄) (sp-Out ⦃ iV ⦄) (sp-Out ⦃ iV ⦄) (sp-Out≤ ⦃ iV ⦄ z≤n (m≤m+n _ _) ≤-refl) (sp-Out ⦃ iV ⦄)

-- (client Quit: a single receive, nothing reported)
ok-cQuit : ∀ {l d x t′} → CQuitV l d x t′ → OkC stQuit x t′
ok-cQuit cqDone = okC (MAccR-Ret _) sp-Ret sp-Ret sp-Ret sp-Ret

-- a server step's facts: accessibility, P1 and the two relays
record OkS (a : LNPState) (x : N.Event) (t′ : Rd) : Set₁ where
  constructor okS
  field
    acc : MAccR ∅ES t′
    p1  : StepPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} a x t′
    nt  : StepPot {Rx = Rr} {Φ = Φ0} {wIn notif ʳ} {cCmdN ʳ} {0} a x t′
    vot : StepPot {Rx = Rr} {Φ = Φ0} {ℓIn votes ʳ} {ℓCmd lnpSendVotes ʳ} {0} a x t′

-- (server Idle)
ok-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → OkS stIdle x t′
ok-sIdle siNext = okS (MAccR-Ret _) sp-Ret sp-Ret sp-Ret
ok-sIdle siQuit = okS (MAccR-Ret _) sp-Ret sp-Ret sp-Ret

-- (server Busy; the votes relay pays list lengths)
ok-sBusy : ∀ {l d x t′} → SBusyV l d x t′ → OkS stBusy x t′
ok-sBusy (sbCan _)   = okS aOut sp-Out sp-Out sp-Out
ok-sBusy (sbAnn _)   = okS aOut sp-Out sp-Out sp-Out
ok-sBusy (sbOff _ _) = okS aOut sp-Out sp-Out sp-Out
ok-sBusy (sbTxs _)   = okS aOut sp-Out sp-Out sp-Out
ok-sBusy (sbVote _)  = okS aOut sp-Out sp-Out (sp-Out≤ z≤n (m≤m+n _ _) ≤-refl)

-- (server Quit)
ok-sQuit : ∀ {l d x t′} → SQuitV l d x t′ → OkS stQuit x t′
ok-sQuit (sqDone _) = okS aOut sp-Out sp-Out sp-Out

-- the client's rounds, for any fact its steps provide
rd-c : ∀ {Φ : LNPState → ℕ} {cost credit : N.Event → ℕ} {K}
     → (∀ {a x t′} → OkC a x t′ → StepPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} a x t′)
     → ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} st (clientStepP l d st)
rd-c π stIdle = rp-pch λ st → π (ok-cIdle (cIdleV st))
rd-c π stBusy = rp-pch λ st → π (ok-cBusy (cBusyV st))
rd-c π stQuit = rp-pch λ st → π (ok-cQuit (cQuitV st))

-- the server's rounds, for any fact its steps provide
rd-s : ∀ {Φ : LNPState → ℕ} {cost credit : N.Event → ℕ} {K}
     → (∀ {a x t′} → OkS a x t′ → StepPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} a x t′)
     → ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} st (serverStepP l d st)
rd-s π stIdle = rp-pch λ st → π (ok-sIdle (sIdleV st))
rd-s π stBusy = rp-pch λ st → π (ok-sBusy (sBusyV st))
rd-s π stQuit = rp-pch λ st → π (ok-sQuit (sQuitV st))

------------------------------------------------------------------------
-- premise (b)
------------------------------------------------------------------------

-- every client body state is accessible at every reachable state
cbodyR : ∀ {l d} st → MAccR ∅ES (clientStepP l d st)
cbodyR {l} {d} stIdle = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cIdle (cIdleV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR {l} {d} stBusy = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cBusy (cBusyV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR {l} {d} stQuit = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cQuit (cQuitV {l} {d} (sVis {at = at} {a = a} refl eq)))

-- every client round starts with a visible event
cbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (clientStepP l d st)
cbodyG stIdle = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stBusy = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stQuit = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())

-- every server body state is accessible at every reachable state
sbodyR : ∀ {l d} st → MAccR ∅ES (serverStepP l d st)
sbodyR {l} {d} stIdle = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sIdle (sIdleV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR {l} {d} stBusy = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sBusy (sBusyV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR {l} {d} stQuit = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sQuit (sQuitV {l} {d} (sVis {at = at} {a = a} refl eq)))

-- every server round starts with a visible event (RequestNext's round is that receive alone)
sbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (serverStepP l d st)
sbodyG stIdle = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stBusy = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stQuit = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())

-- THE CLIENT LEAF
lnpClientA-τ : ∀ l d → DF.τ-AccReach (LNPclientA l d)
lnpClientA-τ l d = τ-AccReach-renameMap (MAccR→τ-AccReach (MAccR-iter {k = clientStepP l d} cbodyG cbodyR stIdle))

-- THE SERVER LEAF
lnpServerA-τ : ∀ l d → DF.τ-AccReach (LNPserverA l d)
lnpServerA-τ l d = τ-AccReach-renameMap (MAccR→τ-AccReach (MAccR-iter {k = serverStepP l d} sbodyG sbodyR stIdle))

------------------------------------------------------------------------
-- counting: `potIter` at `LNPEv`, carried onto `Net_Api` by `Σc≤-ren`
------------------------------------------------------------------------

-- P1 (LNP client): every wire input but one was commanded through the api
lnpClientA-P1 : ∀ l d {s W} → LNPclientA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
lnpClientA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 _ _ 1 (rd-c OkC.p1 {l} {d}) stIdle)

-- P1 (LNP server): every wire input but one was commanded through the api (or `done`)
lnpServerA-P1 : ∀ l d {s W} → LNPserverA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
lnpServerA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 _ _ 1 (rd-s OkS.p1 {l} {d}) stIdle)

-- RELAY (client): every notification it reports, it received
lnpClientA-rep : ∀ l d {s W} → LNPclientA l d ⟹⟨ s ⟩ W → Σc cRepN (labels s) ≤ Σc (wOut notif) (labels s)
lnpClientA-rep l d {s} tr = slack0 {ls = labels s} (Σc≤-ren cRepN (wOut notif) 0 (potIter Φ0 _ _ 0 (rd-c OkC.rep {l} {d}) stIdle) tr)

-- RELAY (client): the votes it reports, it received (list lengths)
lnpClientA-votes : ∀ l d {s W} → LNPclientA l d ⟹⟨ s ⟩ W
                 → Σc (ℓRep lnpRecvVotes) (labels s) ≤ Σc (ℓOut votes) (labels s)
lnpClientA-votes l d {s} tr =
  slack0 {ls = labels s} (Σc≤-ren (ℓRep lnpRecvVotes) (ℓOut votes) 0 (potIter Φ0 _ _ 0 (rd-c OkC.vot {l} {d}) stIdle) tr)

-- RELAY (client): it puts no notification on the wire
lnpClientA-noN : ∀ l d {s W} → LNPclientA l d ⟹⟨ s ⟩ W → Σc (wIn notif) (labels s) ≡ 0
lnpClientA-noN l d {s} tr = none0 {ls = labels s} (Σc≤-ren (wIn notif) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd-c OkC.noN {l} {d}) stIdle) tr)

-- RELAY (server): every notification it sends was commanded
lnpServerA-notif : ∀ l d {s W} → LNPserverA l d ⟹⟨ s ⟩ W → Σc (wIn notif) (labels s) ≤ Σc cCmdN (labels s)
lnpServerA-notif l d {s} tr = slack0 {ls = labels s} (Σc≤-ren (wIn notif) cCmdN 0 (potIter Φ0 _ _ 0 (rd-s OkS.nt {l} {d}) stIdle) tr)

-- RELAY (server): the votes it sends were commanded (list lengths)
lnpServerA-votes : ∀ l d {s W} → LNPserverA l d ⟹⟨ s ⟩ W
                 → Σc (ℓIn votes) (labels s) ≤ Σc (ℓCmd lnpSendVotes) (labels s)
lnpServerA-votes l d {s} tr =
  slack0 {ls = labels s} (Σc≤-ren (ℓIn votes) (ℓCmd lnpSendVotes) 0 (potIter Φ0 _ _ 0 (rd-s OkS.vot {l} {d}) stIdle) tr)

------------------------------------------------------------------------
-- provenance (D1-b): LeiosNotify never touches the block chain — by its
-- renaming alone (`ChS` has no clause for a LeiosNotify cell, `apiLP`, `done`)
------------------------------------------------------------------------

-- no LNP label is a chain label
noChain : ∀ {e : N.Event} {y} → ChS (renE e) y → ⊥
noChain {N.evLabel _ (sendLNP _ _) _}    ()
noChain {N.evLabel _ (receiveLNP _ _) _} ()
noChain {N.evLabel _ (apiLPev _ _ _) _}  ()
noChain {N.evLabel _ (doneLNP _ _) _}    ()

-- every renamed LNP process is chain-free
lnpA-PA : ∀ {ℓr} {R : Set ℓr} {P : PTree LNPEv (ExtI LNPEv) R} → PL.PA ChS ChS InP (RenLNP.renameMap P)
lnpA-PA = PA-ren (pa λ {_} {s} _ → Prov-free noChain (S.labels s))

-- (the client)
lnpClientA-PA : ∀ l d → PL.PA ChS ChS InP (LNPclientA l d)
lnpClientA-PA l d = lnpA-PA

-- (the server)
lnpServerA-PA : ∀ l d → PL.PA ChS ChS InP (LNPserverA l d)
lnpServerA-PA l d = lnpA-PA

------------------------------------------------------------------------
-- Task 9a: the votes-COUNT relays (F2) and the report alphabet (F3a).
-- Read off the same views, through a second record of step facts.
------------------------------------------------------------------------

-- a client step's further facts: vote reports ≤ votes received, no votes sent, no LFP report
record OkC₂ (a : LNPState) (x : N.Event) (t′ : Rd) : Set₁ where
  constructor okC₂
  field
    vtN : StepPot {Rx = Rr} {Φ = Φ0} {cRep lnpRecvVotes ʳ} {wOut votes ʳ} {0} a x t′
    noV : StepPot {Rx = Rr} {Φ = Φ0} {wIn votes ʳ} {λ _ → 0} {0} a x t′
    noR : StepPot {Rx = Rr} {Φ = Φ0} {(λ e → repLFc e + repLFs e) ʳ} {λ _ → 0} {0} a x t′

-- (client Idle)
ok₂-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → OkC₂ stIdle x t′
ok₂-cIdle (ciNext _) = okC₂ sp-Out sp-Out sp-Out
ok₂-cIdle (ciQuit _) = okC₂ sp-Out sp-Out sp-Out

-- (client Busy)
ok₂-cBusy : ∀ {l d x t′} → CBusyV l d x t′ → OkC₂ stBusy x t′
ok₂-cBusy cbCan       = okC₂ sp-Ret sp-Ret sp-Ret
ok₂-cBusy (cbAnn _)   = okC₂ sp-Out sp-Out sp-Out
ok₂-cBusy (cbOff _ _) = okC₂ (sp-Out ⦃ DecEq-Offer ⦄) (sp-Out ⦃ DecEq-Offer ⦄) (sp-Out ⦃ DecEq-Offer ⦄)
ok₂-cBusy (cbTxs _)   = okC₂ (sp-Out ⦃ DecEq-EBPoint ⦄) (sp-Out ⦃ DecEq-EBPoint ⦄) (sp-Out ⦃ DecEq-EBPoint ⦄)
ok₂-cBusy (cbVote _)  = okC₂ (sp-Out ⦃ iV ⦄) (sp-Out ⦃ iV ⦄) (sp-Out ⦃ iV ⦄)

-- (client Quit)
ok₂-cQuit : ∀ {l d x t′} → CQuitV l d x t′ → OkC₂ stQuit x t′
ok₂-cQuit cqDone = okC₂ sp-Ret sp-Ret sp-Ret

-- a server step's further facts: votes sent ≤ commanded, no client-side report
record OkS₂ (a : LNPState) (x : N.Event) (t′ : Rd) : Set₁ where
  constructor okS₂
  field
    vtN : StepPot {Rx = Rr} {Φ = Φ0} {wIn votes ʳ} {cCmd lnpSendVotes ʳ} {0} a x t′
    noR : StepPot {Rx = Rr} {Φ = Φ0} {(λ e → repLNP e + (repLFc e + repLFs e)) ʳ} {λ _ → 0} {0} a x t′

-- (server Idle)
ok₂-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → OkS₂ stIdle x t′
ok₂-sIdle siNext = okS₂ sp-Ret sp-Ret
ok₂-sIdle siQuit = okS₂ sp-Ret sp-Ret

-- (server Busy)
ok₂-sBusy : ∀ {l d x t′} → SBusyV l d x t′ → OkS₂ stBusy x t′
ok₂-sBusy (sbCan _)   = okS₂ sp-Out sp-Out
ok₂-sBusy (sbAnn _)   = okS₂ sp-Out sp-Out
ok₂-sBusy (sbOff _ _) = okS₂ sp-Out sp-Out
ok₂-sBusy (sbTxs _)   = okS₂ sp-Out sp-Out
ok₂-sBusy (sbVote _)  = okS₂ sp-Out sp-Out

-- (server Quit)
ok₂-sQuit : ∀ {l d x t′} → SQuitV l d x t′ → OkS₂ stQuit x t′
ok₂-sQuit (sqDone _) = okS₂ sp-Out sp-Out

-- the client's rounds, for any further fact
rd₂-c : ∀ {cost credit : N.Event → ℕ} {K}
      → (∀ {a x t′} → OkC₂ a x t′ → StepPot {Rx = Rr} {Φ = Φ0} {cost} {credit} {K} a x t′)
      → ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {cost} {credit} {K} st (clientStepP l d st)
rd₂-c π stIdle = rp-pch λ st → π (ok₂-cIdle (cIdleV st))
rd₂-c π stBusy = rp-pch λ st → π (ok₂-cBusy (cBusyV st))
rd₂-c π stQuit = rp-pch λ st → π (ok₂-cQuit (cQuitV st))

-- the server's rounds, for any further fact
rd₂-s : ∀ {cost credit : N.Event → ℕ} {K}
      → (∀ {a x t′} → OkS₂ a x t′ → StepPot {Rx = Rr} {Φ = Φ0} {cost} {credit} {K} a x t′)
      → ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {cost} {credit} {K} st (serverStepP l d st)
rd₂-s π stIdle = rp-pch λ st → π (ok₂-sIdle (sIdleV st))
rd₂-s π stBusy = rp-pch λ st → π (ok₂-sBusy (sBusyV st))
rd₂-s π stQuit = rp-pch λ st → π (ok₂-sQuit (sQuitV st))

-- RELAY (client): every votes report it makes, it received a votes message for
lnpClientA-votesN : ∀ l d {s W} → LNPclientA l d ⟹⟨ s ⟩ W → Σc (cRep lnpRecvVotes) (labels s) ≤ Σc (wOut votes) (labels s)
lnpClientA-votesN l d {s} tr =
  slack0 {ls = labels s} (Σc≤-ren (cRep lnpRecvVotes) (wOut votes) 0 (potIter Φ0 _ _ 0 (rd₂-c OkC₂.vtN {l} {d}) stIdle) tr)

-- RELAY (client): it puts no votes message on the wire
lnpClientA-noV : ∀ l d {s W} → LNPclientA l d ⟹⟨ s ⟩ W → Σc (wIn votes) (labels s) ≡ 0
lnpClientA-noV l d {s} tr =
  none0 {ls = labels s} (Σc≤-ren (wIn votes) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd₂-c OkC₂.noV {l} {d}) stIdle) tr)

-- ALPHABET (client): it makes no LeiosFetch report
lnpClientA-noRep : ∀ l d {s W} → LNPclientA l d ⟹⟨ s ⟩ W → Σc (λ e → repLFc e + repLFs e) (labels s) ≡ 0
lnpClientA-noRep l d {s} tr =
  none0 {ls = labels s} (Σc≤-ren (λ e → repLFc e + repLFs e) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd₂-c OkC₂.noR {l} {d}) stIdle) tr)

-- RELAY (server): every votes message it sends was commanded
lnpServerA-votesN : ∀ l d {s W} → LNPserverA l d ⟹⟨ s ⟩ W → Σc (wIn votes) (labels s) ≤ Σc (cCmd lnpSendVotes) (labels s)
lnpServerA-votesN l d {s} tr =
  slack0 {ls = labels s} (Σc≤-ren (wIn votes) (cCmd lnpSendVotes) 0 (potIter Φ0 _ _ 0 (rd₂-s OkS₂.vtN {l} {d}) stIdle) tr)

-- ALPHABET (server): it makes no report at all (of the LNP client's or the LFP peers')
lnpServerA-noRep : ∀ l d {s W} → LNPserverA l d ⟹⟨ s ⟩ W
                 → Σc (λ e → repLNP e + (repLFc e + repLFs e)) (labels s) ≡ 0
lnpServerA-noRep l d {s} tr =
  none0 {ls = labels s} (Σc≤-ren (λ e → repLNP e + (repLFc e + repLFs e)) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd₂-s OkS₂.noR {l} {d}) stIdle) tr)

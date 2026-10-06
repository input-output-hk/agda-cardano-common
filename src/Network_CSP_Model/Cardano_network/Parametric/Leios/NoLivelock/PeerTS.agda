{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: the TxSubmission PEERS — the submitter
-- `TSclientA` and the REPLY-REPORTING requester `PeersR.TSserverRA`.
--   * VIEWS: each menu state of each side inverted ONCE at `TSEv`; every
--     fact of a side is read off one view-to-obligations function
--   * premise (b): `tsClientA-τ`, `tsServerA-τ` (the requester's Init round
--     is the receive alone — still guarded)
--   * counting on the peer's own renamed trace: P1 (the submitter's
--     unprompted `MsgInit` is its `+ 1`: potential 1 in `stInit`), and the
--     relays — submitter: txid replies sent ≤ commanded, txs sent ≤
--     commanded (list lengths); requester: txid reports ≤ txid replies
--     received, tx reports ≤ txs received (list lengths), sends no reply
--   * provenance: chain-free by renaming alone (`tsA-PA`)
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.PeerTS (p : Params) where

open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _≤_; _+_; z≤n)
open import Data.Nat.Properties using (≤-refl; m≤m+n)
open import Data.Product using (_,_; _×_)
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
open import Cardano_network.TxSubmission p
open import Cardano_network.NetworkPar p using (ιTS; ιTS⁻¹; ιTS-linv; TSclientA)
open import Cardano_network.Parametric.Leios.PeersR p using (TSserverRA)
open Params p using (time₀; length₀; Time; Length; Tx; TxHash)
import CSP.Rename {E₁ = TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RenTS
open import CSP.Operators TSEv-≟ using (∅ES; Ret; Output; Prefix; Prefix₀)
open import Semantics.LTS {E = TSEv} {I = ExtI TSEv} using (_─[_]─►_; ev; evl; sVis)
import Semantics.LTS {E = TSEv} {I = ExtI TSEv} as T
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as L
import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as DF
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.ModAcc TSEv-≟ using (MAccR; MAccR→τ-AccReach)
open import CSP.Laws.DivFree.Reach TSEv-≟ using (MAccR-Ret)
open import CSP.Laws.DivFree.Loop TSEv-≟
  using (NoRetBy; Looping; NoRetBy-mono; NoRetBy-Ret; Guarded-react; MAccR-react; MAccR-Output; MAccR-⟶₀; MAccR-iter)
open import CSP.Laws.DivFree.ReachRename {E₁ = TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv using (τ-AccReach-renameMap)
import CSP.Laws.DivFree.Count TSEv-≟ as S
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (slack0; none0)
open import CSP.Laws.DivFree.CountMore TSEv-≟ using (RoundPot; StepPot; rp-pch; rp-done; rp-Out; sp-Ret; sp-Out; sp-Out≤; sp-⟶; potIter)
open import CSP.Laws.DivFree.Prov TSEv-≟ using (pa)
open import CSP.Laws.DivFree.ProvMore TSEv-≟ using (Prov-free)
import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) as PL
open import Cardano_network.Parametric.Leios.NoLivelock.Weights p
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF p using (ChS; InP)

------------------------------------------------------------------------
-- the renaming pulls back exactly its images (`CountRename`'s `ι-rinv`)
------------------------------------------------------------------------

-- ιTS⁻¹ pulls back only ιTS-images
ιTS-rinv : ∀ {A} {e₂ : Net_Api Payload A} {e : TSEv A} → ιTS⁻¹ e₂ ≡ just e → e₂ ≡ ιTS e
ιTS-rinv {e₂ = input  _ _ N2N_TxSubmission} refl = refl
ιTS-rinv {e₂ = output _ _ N2N_TxSubmission} refl = refl
ιTS-rinv {e₂ = apiTS  _ _ _} refl = refl
ιTS-rinv {e₂ = done   _ _ N2N_TxSubmission} refl = refl
ιTS-rinv {e₂ = input  _ _ N2N_ChainSync} ()
ιTS-rinv {e₂ = input  _ _ N2N_BlockFetch} ()
ιTS-rinv {e₂ = input  _ _ N2N_KeepAlive} ()
ιTS-rinv {e₂ = input  _ _ N2N_LeiosNotify} ()
ιTS-rinv {e₂ = input  _ _ N2N_LeiosFetch} ()
ιTS-rinv {e₂ = output _ _ N2N_ChainSync} ()
ιTS-rinv {e₂ = output _ _ N2N_BlockFetch} ()
ιTS-rinv {e₂ = output _ _ N2N_KeepAlive} ()
ιTS-rinv {e₂ = output _ _ N2N_LeiosNotify} ()
ιTS-rinv {e₂ = output _ _ N2N_LeiosFetch} ()
ιTS-rinv {e₂ = done   _ _ N2N_ChainSync} ()
ιTS-rinv {e₂ = done   _ _ N2N_BlockFetch} ()
ιTS-rinv {e₂ = done   _ _ N2N_KeepAlive} ()
ιTS-rinv {e₂ = done   _ _ N2N_LeiosNotify} ()
ιTS-rinv {e₂ = done   _ _ N2N_LeiosFetch} ()
ιTS-rinv {e₂ = sndmsg _ _ _} ()
ιTS-rinv {e₂ = rcvmsg _ _ _} ()
ιTS-rinv {e₂ = tx _ _ _} ()
ιTS-rinv {e₂ = sndack _ _ _} ()
ιTS-rinv {e₂ = rcvack _ _ _} ()
ιTS-rinv {e₂ = ack _ _ _} ()
ιTS-rinv {e₂ = apiBF _ _ _} ()
ιTS-rinv {e₂ = apiKA _ _ _} ()
ιTS-rinv {e₂ = apiLN _ _ _} ()
ιTS-rinv {e₂ = apiLF _ _ _} ()
ιTS-rinv {e₂ = apiLP _ _ _} ()
ιTS-rinv {e₂ = apiCS _ _ _} ()
ιTS-rinv {e₂ = store _ _ _} ()
ιTS-rinv {e₂ = env _ _ _} ()
ιTS-rinv {e₂ = break _} ()

open import CSP.Laws.DivFree.CountRename ιTS ιTS⁻¹ ιTS-linv ιTS-rinv TSEv-≟ (Net_Api-≟ {Payload})
  using (renE; Σc≤-ren; PA-ren)

-- a `Net_Api` weight pulled back to `TSEv`
_ʳ : (L.Event → ℕ) → T.Event → ℕ
(c ʳ) e = c (renE e)

------------------------------------------------------------------------
-- views
------------------------------------------------------------------------

-- a TxSubmission round tree
Rd : Set₁
Rd = PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)

-- a received TS message on the peer's own cell
rcv : Link → Dir → Time → Mode → Length → MessageTxSubmission2 → T.Event
rcv l d tm md ln msg = T.evLabel _ (receiveTS l d) (tm , md , ln , txSubmission msg)

-- the peer sends `msg` (as `md`), then goes on to `st`
snd : Link → Dir → Mode → MessageTxSubmission2 → TSState → Rd
snd l d md msg st = sendTS l d ! (time₀ , md , length₀ , txSubmission msg) ⟶ Ret (inj₁ st)

-- the txid-list carrier's decidable equality (the one the requester uses)
iH : DecEq (List TxHash)
iH = DecEqI.DecEq-List

-- the tx-list carrier's decidable equality (the one the requester uses)
iT : DecEq (List Tx)
iT = DecEqI.DecEq-List

-- submitter Idle: the receive menu (a txid request of either style, a tx request), each reported
data CIdleV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  ciBlk : ∀ {tm md ln} a r → CIdleV l d (rcv l d tm md ln (MsgTSRequestTxIds Blocking a r))
            (Output ⦃ DecEq-BS×ℕ×ℕ ⦄ (apiTSev l d recvTSRequestTxIds) (Blocking , a , r) (Ret (inj₁ stTxIdsBlocking)))
  ciNB  : ∀ {tm md ln} a r → CIdleV l d (rcv l d tm md ln (MsgTSRequestTxIds NonBlocking a r))
            (Output ⦃ DecEq-BS×ℕ×ℕ ⦄ (apiTSev l d recvTSRequestTxIds) (NonBlocking , a , r) (Ret (inj₁ stTxIdsNonBlocking)))
  ciTxs : ∀ {tm md ln} hs → CIdleV l d (rcv l d tm md ln (MsgTSRequestTxs hs))
            (Output ⦃ DecEq-ListTxHash ⦄ (apiTSev l d recvTSRequestTxs) hs (Ret (inj₁ stTxs)))

-- the submitter Idle inversion
cIdleV : ∀ {l d x t′} → clientStep l d stIdle ─[ ev (evl x) ]─► t′ → CIdleV l d x t′
cIdleV {l} {d} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking a r)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciBlk a r)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV {l} {d} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking a r)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciNB a r)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV {l} {d} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs hs)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciTxs hs)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission MsgTSInit} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission MsgTSDone} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , keepAlive _} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , blockFetch _} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , chainSync _} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotify _} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetch _} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
cIdleV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
cIdleV (sVis {at = _ , sendTS _ _} refl ())
cIdleV (sVis {at = _ , doneTS _ _} refl ())
cIdleV (sVis {at = _ , apiTSev _ _ _} refl ())

-- submitter stTxIdsBlocking: the api menu (reply txids / Done), each a single send
data CBlkV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  cbIds  : ∀ ids → CBlkV l d (T.evLabel _ (apiTSev l d sendTSReplyTxIds) ids) (snd l d FromInitiator (MsgTSReplyTxIds ids) stIdle)
  cbDone : ∀ u   → CBlkV l d (T.evLabel _ (apiTSev l d sendTSDone) u) (snd l d FromInitiator MsgTSDone stDone)

-- the submitter stTxIdsBlocking inversion
cBlkV : ∀ {l d x t′} → clientStep l d stTxIdsBlocking ─[ ev (evl x) ]─► t′ → CBlkV l d x t′
cBlkV {l} {d} (sVis {at = _ , apiTSev l′ d′ sendTSReplyTxIds} {a = ids} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CBlkV l d _) (just-injective br) (cbIds ids)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cBlkV {l} {d} (sVis {at = _ , apiTSev l′ d′ sendTSDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CBlkV l d _) (just-injective br) (cbDone _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cBlkV (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
cBlkV (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
cBlkV (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
cBlkV (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
cBlkV (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
cBlkV (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
cBlkV (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
cBlkV (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
cBlkV (sVis {at = _ , sendTS _ _} refl ())
cBlkV (sVis {at = _ , receiveTS _ _} refl ())
cBlkV (sVis {at = _ , doneTS _ _} refl ())

-- submitter stTxIdsNonBlocking: the api menu (reply txids)
data CNbV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  cnIds : ∀ ids → CNbV l d (T.evLabel _ (apiTSev l d sendTSReplyTxIds) ids) (snd l d FromInitiator (MsgTSReplyTxIds ids) stIdle)

-- the submitter stTxIdsNonBlocking inversion
cNbV : ∀ {l d x t′} → clientStep l d stTxIdsNonBlocking ─[ ev (evl x) ]─► t′ → CNbV l d x t′
cNbV {l} {d} (sVis {at = _ , apiTSev l′ d′ sendTSReplyTxIds} {a = ids} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CNbV l d _) (just-injective br) (cnIds ids)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cNbV (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
cNbV (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
cNbV (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
cNbV (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
cNbV (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
cNbV (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
cNbV (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
cNbV (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
cNbV (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
cNbV (sVis {at = _ , sendTS _ _} refl ())
cNbV (sVis {at = _ , receiveTS _ _} refl ())
cNbV (sVis {at = _ , doneTS _ _} refl ())

-- submitter stTxs: the api menu (reply txs)
data CTxsV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  ctTxs : ∀ txs → CTxsV l d (T.evLabel _ (apiTSev l d sendTSReplyTxs) txs) (snd l d FromInitiator (MsgTSReplyTxs txs) stIdle)

-- the submitter stTxs inversion
cTxsV : ∀ {l d x t′} → clientStep l d stTxs ─[ ev (evl x) ]─► t′ → CTxsV l d x t′
cTxsV {l} {d} (sVis {at = _ , apiTSev l′ d′ sendTSReplyTxs} {a = txs} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CTxsV l d _) (just-injective br) (ctTxs txs)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cTxsV (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
cTxsV (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
cTxsV (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
cTxsV (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
cTxsV (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
cTxsV (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
cTxsV (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
cTxsV (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
cTxsV (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
cTxsV (sVis {at = _ , sendTS _ _} refl ())
cTxsV (sVis {at = _ , receiveTS _ _} refl ())
cTxsV (sVis {at = _ , doneTS _ _} refl ())

-- requester stInit: the receive menu (Init alone, no event after it)
data SInitV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  siInit : ∀ {tm md ln} → SInitV l d (rcv l d tm md ln MsgTSInit) (Ret (inj₁ stIdle))

-- the requester stInit inversion
sInitV : ∀ {l d x t′} → serverStepR l d stInit ─[ ev (evl x) ]─► t′ → SInitV l d x t′
sInitV {l} {d} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission MsgTSInit} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SInitV l d _) (just-injective br) siInit
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission MsgTSDone} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , keepAlive _} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , blockFetch _} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , chainSync _} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotify _} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetch _} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
sInitV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
sInitV (sVis {at = _ , sendTS _ _} refl ())
sInitV (sVis {at = _ , doneTS _ _} refl ())
sInitV (sVis {at = _ , apiTSev _ _ _} refl ())

-- requester Idle: the api menu (a txid request of either style, a tx request), each a single send
data SIdleV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  siBlk : ∀ a r → SIdleV l d (T.evLabel _ (apiTSev l d sendTSRequestTxIdsBlocking) (a , r))
                    (snd l d FromResponder (MsgTSRequestTxIds Blocking a r) stTxIdsBlocking)
  siPip : ∀ a r → SIdleV l d (T.evLabel _ (apiTSev l d sendTSRequestTxIdsPipelined) (a , r))
                    (snd l d FromResponder (MsgTSRequestTxIds NonBlocking a r) stTxIdsNonBlocking)
  siTxs : ∀ hs  → SIdleV l d (T.evLabel _ (apiTSev l d sendTSRequestTxsPipelined) hs)
                    (snd l d FromResponder (MsgTSRequestTxs hs) stTxs)

-- the requester Idle inversion
sIdleV : ∀ {l d x t′} → serverStepR l d stIdle ─[ ev (evl x) ]─► t′ → SIdleV l d x t′
sIdleV {l} {d} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxIdsBlocking} {a = a , r} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) (siBlk a r)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV {l} {d} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxIdsPipelined} {a = a , r} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) (siPip a r)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV {l} {d} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxsPipelined} {a = hs} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) (siTxs hs)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
sIdleV (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
sIdleV (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
sIdleV (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
sIdleV (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
sIdleV (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
sIdleV (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
sIdleV (sVis {at = _ , sendTS _ _} refl ())
sIdleV (sVis {at = _ , receiveTS _ _} refl ())
sIdleV (sVis {at = _ , doneTS _ _} refl ())

-- requester stTxIdsBlocking: the receive menu (txids reported / Done)
data SBlkV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  sbIds  : ∀ {tm md ln} ids → SBlkV l d (rcv l d tm md ln (MsgTSReplyTxIds ids))
                                (Output ⦃ iH ⦄ (apiTSev l d recvTSReplyTxIds) ids (Ret (inj₁ stIdle)))
  sbDone : ∀ {tm md ln}     → SBlkV l d (rcv l d tm md ln MsgTSDone) (doneTS l d ⟶₀ Ret (inj₁ stDone))

-- the requester stTxIdsBlocking inversion
sBlkV : ∀ {l d x t′} → serverStepR l d stTxIdsBlocking ─[ ev (evl x) ]─► t′ → SBlkV l d x t′
sBlkV {l} {d} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds ids)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBlkV l d _) (just-injective br) (sbIds ids)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBlkV {l} {d} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission MsgTSDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SBlkV l d _) (just-injective br) sbDone
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission MsgTSInit} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , keepAlive _} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , blockFetch _} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , chainSync _} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotify _} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetch _} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
sBlkV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
sBlkV (sVis {at = _ , sendTS _ _} refl ())
sBlkV (sVis {at = _ , doneTS _ _} refl ())
sBlkV (sVis {at = _ , apiTSev _ _ _} refl ())

-- requester stTxIdsNonBlocking: the receive menu (txids reported)
data SNbV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  snIds : ∀ {tm md ln} ids → SNbV l d (rcv l d tm md ln (MsgTSReplyTxIds ids))
                               (Output ⦃ iH ⦄ (apiTSev l d recvTSReplyTxIds) ids (Ret (inj₁ stIdle)))

-- the requester stTxIdsNonBlocking inversion
sNbV : ∀ {l d x t′} → serverStepR l d stTxIdsNonBlocking ─[ ev (evl x) ]─► t′ → SNbV l d x t′
sNbV {l} {d} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds ids)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SNbV l d _) (just-injective br) (snIds ids)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission MsgTSInit} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission MsgTSDone} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , keepAlive _} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , blockFetch _} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , chainSync _} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotify _} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetch _} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
sNbV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
sNbV (sVis {at = _ , sendTS _ _} refl ())
sNbV (sVis {at = _ , doneTS _ _} refl ())
sNbV (sVis {at = _ , apiTSev _ _ _} refl ())

-- requester stTxs: the receive menu (txs reported)
data STxsV (l : Link) (d : Dir) : T.Event → Rd → Set₁ where
  stxTxs : ∀ {tm md ln} txs → STxsV l d (rcv l d tm md ln (MsgTSReplyTxs txs))
                                (Output ⦃ iT ⦄ (apiTSev l d recvTSReplyTxs) txs (Ret (inj₁ stIdle)))

-- the requester stTxs inversion
sTxsV : ∀ {l d x t′} → serverStepR l d stTxs ─[ ev (evl x) ]─► t′ → STxsV l d x t′
sTxsV {l} {d} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs txs)} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (STxsV l d _) (just-injective br) (stxTxs txs)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission MsgTSInit} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission MsgTSDone} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , keepAlive _} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , blockFetch _} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , chainSync _} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotify _} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetch _} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
sTxsV (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
sTxsV (sVis {at = _ , sendTS _ _} refl ())
sTxsV (sVis {at = _ , doneTS _ _} refl ())
sTxsV (sVis {at = _ , apiTSev _ _ _} refl ())

------------------------------------------------------------------------
-- every fact of a step, read off the views ONCE
------------------------------------------------------------------------

-- the zero potential
Φ0 : TSState → ℕ
Φ0 _ = 0

-- the submitter's P1 potential: its `MsgInit` is still to be sent
Φi : TSState → ℕ
Φi stInit = 1
Φi _      = 0

-- a single output then a return is accessible
aOut : ∀ {B : Set} ⦃ _ : DecEq B ⦄ {e : TSEv B} {v : B} {r : TSState ⊎ Rr} → MAccR ∅ES (e ! v ⟶ Ret r)
aOut = MAccR-Output _ _ (MAccR-Ret _)

-- a submitter step's facts: accessibility, P1 and the two relays
record OkC (a : TSState) (x : T.Event) (t′ : Rd) : Set₁ where
  constructor okC
  field
    acc : MAccR ∅ES t′
    p1  : StepPot {Rx = Rr} {Φ = Φi} {cIn ʳ} {cApi ʳ} {0} a x t′
    ids : StepPot {Rx = Rr} {Φ = Φ0} {wIn ReplyTxIds ʳ} {cCmd sendTSReplyTxIds ʳ} {0} a x t′
    txs : StepPot {Rx = Rr} {Φ = Φ0} {ℓIn ReplyTxs ʳ} {ℓCmd sendTSReplyTxs ʳ} {0} a x t′

-- (submitter Idle)
ok-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → OkC stIdle x t′
ok-cIdle (ciBlk _ _) = okC (aOut ⦃ DecEq-BS×ℕ×ℕ ⦄) (sp-Out ⦃ DecEq-BS×ℕ×ℕ ⦄) (sp-Out ⦃ DecEq-BS×ℕ×ℕ ⦄) (sp-Out ⦃ DecEq-BS×ℕ×ℕ ⦄)
ok-cIdle (ciNB _ _)  = okC (aOut ⦃ DecEq-BS×ℕ×ℕ ⦄) (sp-Out ⦃ DecEq-BS×ℕ×ℕ ⦄) (sp-Out ⦃ DecEq-BS×ℕ×ℕ ⦄) (sp-Out ⦃ DecEq-BS×ℕ×ℕ ⦄)
ok-cIdle (ciTxs _)   = okC (aOut ⦃ DecEq-ListTxHash ⦄) (sp-Out ⦃ DecEq-ListTxHash ⦄) (sp-Out ⦃ DecEq-ListTxHash ⦄) (sp-Out ⦃ DecEq-ListTxHash ⦄)

-- (submitter stTxIdsBlocking)
ok-cBlk : ∀ {l d x t′} → CBlkV l d x t′ → OkC stTxIdsBlocking x t′
ok-cBlk (cbIds _)  = okC aOut sp-Out sp-Out sp-Out
ok-cBlk (cbDone _) = okC aOut sp-Out sp-Out sp-Out

-- (submitter stTxIdsNonBlocking)
ok-cNb : ∀ {l d x t′} → CNbV l d x t′ → OkC stTxIdsNonBlocking x t′
ok-cNb (cnIds _) = okC aOut sp-Out sp-Out sp-Out

-- (submitter stTxs; the txs relay pays list lengths)
ok-cTxs : ∀ {l d x t′} → CTxsV l d x t′ → OkC stTxs x t′
ok-cTxs (ctTxs _) = okC aOut sp-Out sp-Out (sp-Out≤ z≤n (m≤m+n _ _) ≤-refl)

-- a requester step's facts: accessibility, P1 and the four relays
record OkS (a : TSState) (x : T.Event) (t′ : Rd) : Set₁ where
  constructor okS
  field
    acc : MAccR ∅ES t′
    p1  : StepPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} a x t′
    ids : StepPot {Rx = Rr} {Φ = Φ0} {cRep recvTSReplyTxIds ʳ} {wOut ReplyTxIds ʳ} {0} a x t′
    txs : StepPot {Rx = Rr} {Φ = Φ0} {ℓRep recvTSReplyTxs ʳ} {ℓOut ReplyTxs ʳ} {0} a x t′
    nId : StepPot {Rx = Rr} {Φ = Φ0} {wIn ReplyTxIds ʳ} {λ _ → 0} {0} a x t′
    nTx : StepPot {Rx = Rr} {Φ = Φ0} {wIn ReplyTxs ʳ} {λ _ → 0} {0} a x t′

-- (requester stInit)
ok-sInit : ∀ {l d x t′} → SInitV l d x t′ → OkS stInit x t′
ok-sInit siInit = okS (MAccR-Ret _) sp-Ret sp-Ret sp-Ret sp-Ret sp-Ret

-- (requester Idle)
ok-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → OkS stIdle x t′
ok-sIdle (siBlk _ _) = okS aOut sp-Out sp-Out sp-Out sp-Out sp-Out
ok-sIdle (siPip _ _) = okS aOut sp-Out sp-Out sp-Out sp-Out sp-Out
ok-sIdle (siTxs _)   = okS aOut sp-Out sp-Out sp-Out sp-Out sp-Out

-- (requester stTxIdsBlocking)
ok-sBlk : ∀ {l d x t′} → SBlkV l d x t′ → OkS stTxIdsBlocking x t′
ok-sBlk (sbIds _) = okS (aOut ⦃ iH ⦄) (sp-Out ⦃ iH ⦄) (sp-Out ⦃ iH ⦄) (sp-Out ⦃ iH ⦄) (sp-Out ⦃ iH ⦄) (sp-Out ⦃ iH ⦄)
ok-sBlk sbDone    = okS (MAccR-⟶₀ _ (MAccR-Ret _)) sp-⟶ sp-⟶ sp-⟶ sp-⟶ sp-⟶

-- (requester stTxIdsNonBlocking)
ok-sNb : ∀ {l d x t′} → SNbV l d x t′ → OkS stTxIdsNonBlocking x t′
ok-sNb (snIds _) = okS (aOut ⦃ iH ⦄) (sp-Out ⦃ iH ⦄) (sp-Out ⦃ iH ⦄) (sp-Out ⦃ iH ⦄) (sp-Out ⦃ iH ⦄) (sp-Out ⦃ iH ⦄)

-- (requester stTxs; the txs relay pays list lengths)
ok-sTxs : ∀ {l d x t′} → STxsV l d x t′ → OkS stTxs x t′
ok-sTxs (stxTxs _) = okS (aOut ⦃ iT ⦄) (sp-Out ⦃ iT ⦄) (sp-Out ⦃ iT ⦄) (sp-Out≤ ⦃ iT ⦄ z≤n (m≤m+n _ _) ≤-refl) (sp-Out ⦃ iT ⦄) (sp-Out ⦃ iT ⦄)

-- the submitter's rounds, for any fact its steps provide (`stInit` is the one `MsgInit` send)
rd-c : ∀ {Φ : TSState → ℕ} {cost credit : T.Event → ℕ} {K}
     → (∀ {l d} → RoundPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} stInit (clientStep l d stInit))
     → (∀ {a x t′} → OkC a x t′ → StepPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} a x t′)
     → ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} st (clientStep l d st)
rd-c i π stInit             = i
rd-c i π stIdle             = rp-pch λ st → π (ok-cIdle (cIdleV st))
rd-c i π stTxIdsBlocking    = rp-pch λ st → π (ok-cBlk (cBlkV st))
rd-c i π stTxIdsNonBlocking = rp-pch λ st → π (ok-cNb (cNbV st))
rd-c i π stTxs              = rp-pch λ st → π (ok-cTxs (cTxsV st))
rd-c i π stDone             = rp-done

-- the requester's rounds, for any fact its steps provide
rd-s : ∀ {Φ : TSState → ℕ} {cost credit : T.Event → ℕ} {K}
     → (∀ {a x t′} → OkS a x t′ → StepPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} a x t′)
     → ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ} {cost} {credit} {K} st (serverStepR l d st)
rd-s π stInit             = rp-pch λ st → π (ok-sInit (sInitV st))
rd-s π stIdle             = rp-pch λ st → π (ok-sIdle (sIdleV st))
rd-s π stTxIdsBlocking    = rp-pch λ st → π (ok-sBlk (sBlkV st))
rd-s π stTxIdsNonBlocking = rp-pch λ st → π (ok-sNb (sNbV st))
rd-s π stTxs              = rp-pch λ st → π (ok-sTxs (sTxsV st))
rd-s π stDone             = rp-done

------------------------------------------------------------------------
-- premise (b)
------------------------------------------------------------------------

-- every submitter body state is accessible at every reachable state
cbodyR : ∀ {l d} st → MAccR ∅ES (clientStep l d st)
cbodyR stInit                     = aOut
cbodyR {l} {d} stIdle             = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cIdle (cIdleV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR {l} {d} stTxIdsBlocking    = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cBlk (cBlkV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR {l} {d} stTxIdsNonBlocking = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cNb (cNbV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR {l} {d} stTxs              = MAccR-react refl λ {at} {a} eq → OkC.acc (ok-cTxs (cTxsV {l} {d} (sVis {at = at} {a = a} refl eq)))
cbodyR stDone                     = MAccR-Ret _

-- every submitter round starts with a visible event
cbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (clientStep l d st)
cbodyG stInit             = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stIdle             = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stTxIdsBlocking    = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stTxIdsNonBlocking = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stTxs              = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stDone             = NoRetBy-Ret λ ()

-- every requester body state is accessible at every reachable state
sbodyR : ∀ {l d} st → MAccR ∅ES (serverStepR l d st)
sbodyR {l} {d} stInit             = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sInit (sInitV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR {l} {d} stIdle             = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sIdle (sIdleV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR {l} {d} stTxIdsBlocking    = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sBlk (sBlkV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR {l} {d} stTxIdsNonBlocking = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sNb (sNbV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR {l} {d} stTxs              = MAccR-react refl λ {at} {a} eq → OkS.acc (ok-sTxs (sTxsV {l} {d} (sVis {at = at} {a = a} refl eq)))
sbodyR stDone                     = MAccR-Ret _

-- every requester round starts with a visible event (Init's round is that receive alone)
sbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (serverStepR l d st)
sbodyG stInit             = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stIdle             = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stTxIdsBlocking    = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stTxIdsNonBlocking = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stTxs              = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
sbodyG stDone             = NoRetBy-Ret λ ()

-- THE SUBMITTER LEAF
tsClientA-τ : ∀ l d → DF.τ-AccReach (TSclientA l d)
tsClientA-τ l d = τ-AccReach-renameMap (MAccR→τ-AccReach (MAccR-iter {k = clientStep l d} cbodyG cbodyR stInit))

-- THE REQUESTER LEAF
tsServerA-τ : ∀ l d → DF.τ-AccReach (TSserverRA l d)
tsServerA-τ l d = τ-AccReach-renameMap (MAccR→τ-AccReach (MAccR-iter {k = serverStepR l d} sbodyG sbodyR stInit))

------------------------------------------------------------------------
-- counting: `potIter` at `TSEv`, carried onto `Net_Api` by `Σc≤-ren`
------------------------------------------------------------------------

-- P1 (TS submitter): every wire input but one (its `MsgInit`) was commanded through the api
tsClientA-P1 : ∀ l d {s W} → TSclientA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
tsClientA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φi _ _ 0 (rd-c rp-Out OkC.p1 {l} {d}) stInit)

-- P1 (TS requester)
tsServerA-P1 : ∀ l d {s W} → TSserverRA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
tsServerA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 _ _ 1 (rd-s OkS.p1 {l} {d}) stInit)

-- RELAY (submitter): every txid reply it sends was commanded
tsClientA-ids : ∀ l d {s W} → TSclientA l d ⟹⟨ s ⟩ W
              → Σc (wIn ReplyTxIds) (labels s) ≤ Σc (cCmd sendTSReplyTxIds) (labels s)
tsClientA-ids l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (wIn ReplyTxIds) (cCmd sendTSReplyTxIds) 0 (potIter Φ0 _ _ 0 (rd-c rp-Out OkC.ids {l} {d}) stInit) tr)

-- RELAY (submitter): the txs it sends were commanded (list lengths)
tsClientA-txs : ∀ l d {s W} → TSclientA l d ⟹⟨ s ⟩ W
              → Σc (ℓIn ReplyTxs) (labels s) ≤ Σc (ℓCmd sendTSReplyTxs) (labels s)
tsClientA-txs l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (ℓIn ReplyTxs) (ℓCmd sendTSReplyTxs) 0 (potIter Φ0 _ _ 0 (rd-c rp-Out OkC.txs {l} {d}) stInit) tr)

-- RELAY (requester): every txid reply it reports, it received
tsServerA-ids : ∀ l d {s W} → TSserverRA l d ⟹⟨ s ⟩ W
              → Σc (cRep recvTSReplyTxIds) (labels s) ≤ Σc (wOut ReplyTxIds) (labels s)
tsServerA-ids l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (cRep recvTSReplyTxIds) (wOut ReplyTxIds) 0 (potIter Φ0 _ _ 0 (rd-s OkS.ids {l} {d}) stInit) tr)

-- RELAY (requester): the txs it reports, it received (list lengths)
tsServerA-txs : ∀ l d {s W} → TSserverRA l d ⟹⟨ s ⟩ W
              → Σc (ℓRep recvTSReplyTxs) (labels s) ≤ Σc (ℓOut ReplyTxs) (labels s)
tsServerA-txs l d {s} tr = slack0 {ls = labels s}
  (Σc≤-ren (ℓRep recvTSReplyTxs) (ℓOut ReplyTxs) 0 (potIter Φ0 _ _ 0 (rd-s OkS.txs {l} {d}) stInit) tr)

-- RELAY (requester): it puts no txid reply on the wire
tsServerA-noIds : ∀ l d {s W} → TSserverRA l d ⟹⟨ s ⟩ W → Σc (wIn ReplyTxIds) (labels s) ≡ 0
tsServerA-noIds l d {s} tr = none0 {ls = labels s}
  (Σc≤-ren (wIn ReplyTxIds) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd-s OkS.nId {l} {d}) stInit) tr)

-- RELAY (requester): it puts no tx reply on the wire
tsServerA-noTxs : ∀ l d {s W} → TSserverRA l d ⟹⟨ s ⟩ W → Σc (wIn ReplyTxs) (labels s) ≡ 0
tsServerA-noTxs l d {s} tr = none0 {ls = labels s}
  (Σc≤-ren (wIn ReplyTxs) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (rd-s OkS.nTx {l} {d}) stInit) tr)

------------------------------------------------------------------------
-- provenance (D1-b): TxSubmission never touches the block chain — by its
-- renaming alone (`ChS` has no clause for a TxSubmission cell, `apiTS`, `done`)
------------------------------------------------------------------------

-- no TS label is a chain label
noChain : ∀ {e : T.Event} {y} → ChS (renE e) y → ⊥
noChain {T.evLabel _ (sendTS _ _) _}    ()
noChain {T.evLabel _ (receiveTS _ _) _} ()
noChain {T.evLabel _ (apiTSev _ _ _) _} ()
noChain {T.evLabel _ (doneTS _ _) _}    ()

-- every renamed TS process is chain-free
tsA-PA : ∀ {ℓr} {R : Set ℓr} {P : PTree TSEv (ExtI TSEv) R} → PL.PA ChS ChS InP (RenTS.renameMap P)
tsA-PA = PA-ren (pa λ {_} {s} _ → Prov-free noChain (S.labels s))

-- (the submitter)
tsClientA-PA : ∀ l d → PL.PA ChS ChS InP (TSclientA l d)
tsClientA-PA l d = tsA-PA

-- (the requester)
tsServerA-PA : ∀ l d → PL.PA ChS ChS InP (TSserverRA l d)
tsServerA-PA l d = tsA-PA

------------------------------------------------------------------------
-- Task 9a (F3a): the report alphabet — the submitter makes none of the
-- requester's reports
------------------------------------------------------------------------

-- a submitter step makes no requester report
NRc : TSState → T.Event → Rd → Set₁
NRc = StepPot {Rx = Rr} {Φ = Φ0} {repTS ʳ} {λ _ → 0} {0}

-- (submitter Idle)
nr-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → NRc stIdle x t′
nr-cIdle (ciBlk _ _) = sp-Out ⦃ DecEq-BS×ℕ×ℕ ⦄
nr-cIdle (ciNB _ _)  = sp-Out ⦃ DecEq-BS×ℕ×ℕ ⦄
nr-cIdle (ciTxs _)   = sp-Out ⦃ DecEq-ListTxHash ⦄

-- (submitter stTxIdsBlocking)
nr-cBlk : ∀ {l d x t′} → CBlkV l d x t′ → NRc stTxIdsBlocking x t′
nr-cBlk (cbIds _)  = sp-Out
nr-cBlk (cbDone _) = sp-Out

-- (submitter stTxIdsNonBlocking)
nr-cNb : ∀ {l d x t′} → CNbV l d x t′ → NRc stTxIdsNonBlocking x t′
nr-cNb (cnIds _) = sp-Out

-- (submitter stTxs)
nr-cTxs : ∀ {l d x t′} → CTxsV l d x t′ → NRc stTxs x t′
nr-cTxs (ctTxs _) = sp-Out

-- the submitter's rounds (`stInit`: the one `MsgInit` send)
nr-c : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {repTS ʳ} {λ _ → 0} {0} st (clientStep l d st)
nr-c stInit             = rp-Out
nr-c stIdle             = rp-pch λ st → nr-cIdle (cIdleV st)
nr-c stTxIdsBlocking    = rp-pch λ st → nr-cBlk (cBlkV st)
nr-c stTxIdsNonBlocking = rp-pch λ st → nr-cNb (cNbV st)
nr-c stTxs              = rp-pch λ st → nr-cTxs (cTxsV st)
nr-c stDone             = rp-done

-- ALPHABET (submitter): it makes no txid-reply or tx-reply report
tsClientA-noRep : ∀ l d {s W} → TSclientA l d ⟹⟨ s ⟩ W → Σc repTS (labels s) ≡ 0
tsClientA-noRep l d {s} tr =
  none0 {ls = labels s} (Σc≤-ren repTS (λ _ → 0) 0 (potIter Φ0 _ _ 0 (nr-c {l} {d}) stInit) tr)

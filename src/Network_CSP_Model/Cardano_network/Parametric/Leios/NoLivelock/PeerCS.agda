{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: the ChainSync PEERS.
--   * VIEWS: each menu state of each peer inverted ONCE at the source
--     alphabet `CSEv` into a view (`S…V` server, `C…V` client); the
--     τ-leaves, the counting summaries and the provenance read them off
--   * premise (b): `csServerA-τ`, `csClientA-τ` — accessibility through
--     `MAccR-iter`, carried through `renameMap` (`τ-AccReach-renameMap`)
--   * counting, on the peer's own renamed trace: P1 for both sides, the
--     RollForward relays (client reports ≤ received, sends none; server
--     sends ≤ commanded) — `potIter` at `CSEv`, then `Σc≤-ren`
--   * provenance: chain-free by renaming alone (`csA-PA`)
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.PeerCS (p : Params) where

open import Data.Empty using (⊥)
open import Data.List using (List; [])
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _≤_; _+_)
open import Data.Nat.Properties using (+-identityʳ; n≤0⇒n≡0)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong)
open import Class.DecEq using (_≟_)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.ChainSync p
open import Cardano_network.NetworkPar p using (ιCS; ιCS⁻¹; ιCS-linv; CSserverA; CSclientA)
open import CSP.Operators CSEv-≟ using (∅ES; Ret; Output; Prefix; Prefix₀)
open import Semantics.LTS {E = CSEv} {I = ExtI CSEv} using (_─[_]─►_; ev; evl; sVis)
import Semantics.LTS {E = CSEv} {I = ExtI CSEv} as C
open import Semantics.DivergenceFree {E = CSEv} {I = ExtI CSEv} using (τ-AccReach)
open import Cardano_network.Data p
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as L
open Params p using (time₀; length₀; Time; Length)
import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as DF
open import CSP.Laws.DivFree.ModAcc CSEv-≟ using (MAccR; MAccR→τ-AccReach)
open import CSP.Laws.DivFree.Reach CSEv-≟ using (MAccR-Ret)
open import CSP.Laws.DivFree.Loop CSEv-≟
  using (NoRetBy; Looping; NoRetBy-mono; NoRetBy-Ret; Guarded-react;
         MAccR-react; MAccR-Output; MAccR-⟶₀; MAccR-iter)
import CSP.Rename {E₁ = CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RenCS
open import CSP.Laws.DivFree.ReachRename {E₁ = CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv using (τ-AccReach-renameMap)
import Semantics.Failures {E = CSEv} {I = ExtI CSEv} as SF
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
import CSP.Laws.DivFree.Count CSEv-≟ as S
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload}) using (Σc; labels)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (Σc-0)
open import CSP.Laws.DivFree.CountMore CSEv-≟ using (RoundPot; StepPot; rp-pch; rp-done; sp-Ret; sp-Out; sp-⟶; potIter)
open import CSP.Laws.DivFree.Prov CSEv-≟ using (PA; pa)
open import CSP.Laws.DivFree.ProvMore CSEv-≟ using (Prov-free)
import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload}) as PL
open import Cardano_network.Parametric.Leios.NoLivelock.Weights p
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF p using (ChS; InP)

------------------------------------------------------------------------
-- the renaming pulls back exactly its images (`CountRename`'s `ι-rinv`)
------------------------------------------------------------------------

-- ιCS⁻¹ pulls back only ιCS-images
ιCS-rinv : ∀ {A} {e₂ : Net_Api Payload A} {e : CSEv A} → ιCS⁻¹ e₂ ≡ just e → e₂ ≡ ιCS e
ιCS-rinv {e₂ = input  _ _ N2N_ChainSync} refl = refl
ιCS-rinv {e₂ = output _ _ N2N_ChainSync} refl = refl
ιCS-rinv {e₂ = apiCS  _ _ _}             refl = refl
ιCS-rinv {e₂ = done   _ _ N2N_ChainSync} refl = refl
ιCS-rinv {e₂ = input  _ _ N2N_BlockFetch} ()
ιCS-rinv {e₂ = input  _ _ N2N_TxSubmission} ()
ιCS-rinv {e₂ = input  _ _ N2N_KeepAlive} ()
ιCS-rinv {e₂ = input  _ _ N2N_LeiosNotify} ()
ιCS-rinv {e₂ = input  _ _ N2N_LeiosFetch} ()
ιCS-rinv {e₂ = output _ _ N2N_BlockFetch} ()
ιCS-rinv {e₂ = output _ _ N2N_TxSubmission} ()
ιCS-rinv {e₂ = output _ _ N2N_KeepAlive} ()
ιCS-rinv {e₂ = output _ _ N2N_LeiosNotify} ()
ιCS-rinv {e₂ = output _ _ N2N_LeiosFetch} ()
ιCS-rinv {e₂ = done   _ _ N2N_BlockFetch} ()
ιCS-rinv {e₂ = done   _ _ N2N_TxSubmission} ()
ιCS-rinv {e₂ = done   _ _ N2N_KeepAlive} ()
ιCS-rinv {e₂ = done   _ _ N2N_LeiosNotify} ()
ιCS-rinv {e₂ = done   _ _ N2N_LeiosFetch} ()
ιCS-rinv {e₂ = sndmsg _ _ _} ()
ιCS-rinv {e₂ = rcvmsg _ _ _} ()
ιCS-rinv {e₂ = tx     _ _ _} ()
ιCS-rinv {e₂ = sndack _ _ _} ()
ιCS-rinv {e₂ = rcvack _ _ _} ()
ιCS-rinv {e₂ = ack    _ _ _} ()
ιCS-rinv {e₂ = apiBF  _ _ _} ()
ιCS-rinv {e₂ = apiTS  _ _ _} ()
ιCS-rinv {e₂ = apiKA  _ _ _} ()
ιCS-rinv {e₂ = apiLN  _ _ _} ()
ιCS-rinv {e₂ = apiLF  _ _ _} ()
ιCS-rinv {e₂ = apiLP  _ _ _} ()
ιCS-rinv {e₂ = store  _ _ _} ()
ιCS-rinv {e₂ = env    _ _ _} ()
ιCS-rinv {e₂ = break  _} ()

open import CSP.Laws.DivFree.CountRename ιCS ιCS⁻¹ ιCS-linv ιCS-rinv CSEv-≟ (Net_Api-≟ {Payload})
  using (renE; Σc≤-ren; PA-ren)

-- a `Net_Api` weight pulled back to `CSEv`
_ʳ : (L.Event → ℕ) → C.Event → ℕ
(c ʳ) e = c (renE e)

-- a ChainSync round tree
Rd : Set₁
Rd = PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)

------------------------------------------------------------------------
-- server views (the GREEN inversions, re-targeted to return a view)
------------------------------------------------------------------------

-- Idle: the receive menu (RequestNext / FindIntersect / Done)
data SIdleV (l : Link) (d : Dir) : C.Event → Rd → Set₁ where
  siNext : ∀ {tm md ln} → SIdleV l d (C.evLabel _ (receiveCS l d) (tm , md , ln , chainSync MsgCSRequestNext))
                                     (apiCSev l d reqCSRequestNext ⟶₀ Ret (inj₁ stCanAwait))
  siFind : ∀ {tm md ln} ps → SIdleV l d (C.evLabel _ (receiveCS l d) (tm , md , ln , chainSync (MsgCSFindIntersect ps)))
                                        (Output ⦃ DecEq-ListPoint ⦄ (apiCSev l d reqCSFindIntersect) ps (Ret (inj₁ stIntersect)))
  siDone : ∀ {tm md ln} → SIdleV l d (C.evLabel _ (receiveCS l d) (tm , md , ln , chainSync MsgCSDone))
                                     (doneCS l d ⟶₀ Ret (inj₁ stDone))

-- the Idle inversion
sIdleV : ∀ {l d x t′} → serverStep l d stIdle ─[ ev (evl x) ]─► t′ → SIdleV l d x t′
sIdleV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync MsgCSRequestNext} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) siNext
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) (siFind ps)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync MsgCSDone} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIdleV l d _) (just-injective br) siDone
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSAwaitReply} refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , keepAlive _}    refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , blockFetch _}   refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , txSubmission _} refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotify _}  refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetch _}   refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
sIdleV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetchP _}  refl ())
sIdleV (sVis {at = _ , sendCS _ _}    refl ())
sIdleV (sVis {at = _ , apiCSev _ _ _} refl ())
sIdleV (sVis {at = _ , doneCS _ _}    refl ())

-- the server's roll answer to `msg`, then back to Idle-or-`st`
sSend : Link → Dir → MessageChainSync → CSState → Rd
sSend l d msg st = sendCS l d ! (time₀ , FromResponder , length₀ , chainSync msg) ⟶ Ret (inj₁ st)

-- stCanAwait: the api menu (RollForward / RollBackward / AwaitReply), each a single send
data SAwaitV (l : Link) (d : Dir) : C.Event → Rd → Set₁ where
  saRF : ∀ h tp  → SAwaitV l d (C.evLabel _ (apiCSev l d sendCSRollForward) (h , tp)) (sSend l d (MsgCSRollForward h tp) stIdle)
  saRB : ∀ pt tp → SAwaitV l d (C.evLabel _ (apiCSev l d sendCSRollBackward) (pt , tp)) (sSend l d (MsgCSRollBackward pt tp) stIdle)
  saAw : ∀ u     → SAwaitV l d (C.evLabel _ (apiCSev l d sendCSAwaitReply) u) (sSend l d MsgCSAwaitReply stMustReply)

-- the stCanAwait inversion
sAwaitV : ∀ {l d x t′} → serverStep l d stCanAwait ─[ ev (evl x) ]─► t′ → SAwaitV l d x t′
sAwaitV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSRollForward} {a = h , tp} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SAwaitV l d _) (just-injective br) (saRF h tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sAwaitV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSRollBackward} {a = pt , tp} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SAwaitV l d _) (just-injective br) (saRB pt tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sAwaitV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSAwaitReply} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SAwaitV l d _) (just-injective br) (saAw _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sAwaitV (sVis {at = _ , apiCSev _ _ sendCSRequestNext} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ sendCSIntersectFound} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ sendCSIntersectNotFound} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
sAwaitV (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
sAwaitV (sVis {at = _ , sendCS _ _}    refl ())
sAwaitV (sVis {at = _ , receiveCS _ _} refl ())
sAwaitV (sVis {at = _ , doneCS _ _}    refl ())

-- stMustReply: the api menu (RollForward / RollBackward), each a single send
data SMustV (l : Link) (d : Dir) : C.Event → Rd → Set₁ where
  smRF : ∀ h tp  → SMustV l d (C.evLabel _ (apiCSev l d sendCSRollForward) (h , tp)) (sSend l d (MsgCSRollForward h tp) stIdle)
  smRB : ∀ pt tp → SMustV l d (C.evLabel _ (apiCSev l d sendCSRollBackward) (pt , tp)) (sSend l d (MsgCSRollBackward pt tp) stIdle)

-- the stMustReply inversion
sMustV : ∀ {l d x t′} → serverStep l d stMustReply ─[ ev (evl x) ]─► t′ → SMustV l d x t′
sMustV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSRollForward} {a = h , tp} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SMustV l d _) (just-injective br) (smRF h tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sMustV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSRollBackward} {a = pt , tp} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SMustV l d _) (just-injective br) (smRB pt tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sMustV (sVis {at = _ , apiCSev _ _ sendCSRequestNext} refl ())
sMustV (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
sMustV (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
sMustV (sVis {at = _ , apiCSev _ _ sendCSAwaitReply} refl ())
sMustV (sVis {at = _ , apiCSev _ _ sendCSIntersectFound} refl ())
sMustV (sVis {at = _ , apiCSev _ _ sendCSIntersectNotFound} refl ())
sMustV (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
sMustV (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
sMustV (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
sMustV (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
sMustV (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
sMustV (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
sMustV (sVis {at = _ , sendCS _ _}    refl ())
sMustV (sVis {at = _ , receiveCS _ _} refl ())
sMustV (sVis {at = _ , doneCS _ _}    refl ())

-- stIntersect: the api menu (IntersectFound / IntersectNotFound), each a single send
data SIsectV (l : Link) (d : Dir) : C.Event → Rd → Set₁ where
  sxFound : ∀ pt tp → SIsectV l d (C.evLabel _ (apiCSev l d sendCSIntersectFound) (pt , tp)) (sSend l d (MsgCSIntersectFound pt tp) stIdle)
  sxNot   : ∀ tp    → SIsectV l d (C.evLabel _ (apiCSev l d sendCSIntersectNotFound) tp) (sSend l d (MsgCSIntersectNotFound tp) stIdle)

-- the stIntersect inversion
sIsectV : ∀ {l d x t′} → serverStep l d stIntersect ─[ ev (evl x) ]─► t′ → SIsectV l d x t′
sIsectV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSIntersectFound} {a = pt , tp} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIsectV l d _) (just-injective br) (sxFound pt tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIsectV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSIntersectNotFound} {a = tp} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (SIsectV l d _) (just-injective br) (sxNot tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
sIsectV (sVis {at = _ , apiCSev _ _ sendCSRequestNext} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ sendCSAwaitReply} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ sendCSRollForward} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ sendCSRollBackward} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
sIsectV (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
sIsectV (sVis {at = _ , sendCS _ _}    refl ())
sIsectV (sVis {at = _ , receiveCS _ _} refl ())
sIsectV (sVis {at = _ , doneCS _ _}    refl ())

------------------------------------------------------------------------
-- client views
------------------------------------------------------------------------

-- the client's request `msg`, then on to `st`
cSend : Link → Dir → MessageChainSync → CSState → Rd
cSend l d msg st = sendCS l d ! (time₀ , FromInitiator , length₀ , chainSync msg) ⟶ Ret (inj₁ st)

-- Idle: the api menu (RequestNext / FindIntersect / Done), each a single send
data CIdleV (l : Link) (d : Dir) : C.Event → Rd → Set₁ where
  ciNext : ∀ u  → CIdleV l d (C.evLabel _ (apiCSev l d sendCSRequestNext) u) (cSend l d MsgCSRequestNext stCanAwait)
  ciFind : ∀ ps → CIdleV l d (C.evLabel _ (apiCSev l d sendCSFindIntersect) ps) (cSend l d (MsgCSFindIntersect ps) stIntersect)
  ciDone : ∀ u  → CIdleV l d (C.evLabel _ (apiCSev l d sendCSDone) u) (cSend l d MsgCSDone stDone)

-- the client Idle inversion
cIdleV : ∀ {l d x t′} → clientStep l d stIdle ─[ ev (evl x) ]─► t′ → CIdleV l d x t′
cIdleV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSRequestNext} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciNext _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSFindIntersect} {a = ps} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciFind ps)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV {l} {d} (sVis {at = _ , apiCSev l′ d′ sendCSDone} refl br) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIdleV l d _) (just-injective br) (ciDone _)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIdleV (sVis {at = _ , apiCSev _ _ sendCSAwaitReply} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ sendCSRollForward} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ sendCSRollBackward} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ sendCSIntersectFound} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ sendCSIntersectNotFound} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
cIdleV (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
cIdleV (sVis {at = _ , sendCS _ _}    refl ())
cIdleV (sVis {at = _ , receiveCS _ _} refl ())
cIdleV (sVis {at = _ , doneCS _ _}    refl ())

-- a received ChainSync message on the client's own cell
rcvC : Link → Dir → Time → Mode → Length → MessageChainSync → C.Event
rcvC l d tm md ln msg = C.evLabel _ (receiveCS l d) (tm , md , ln , chainSync msg)

-- stCanAwait: the receive menu (RollForward / RollBackward reported; AwaitReply silent)
data CAwaitV (l : Link) (d : Dir) : C.Event → Rd → Set₁ where
  caRF : ∀ {tm md ln} h tp  → CAwaitV l d (rcvC l d tm md ln (MsgCSRollForward h tp))
                                         (apiCSev l d recvCSRollforward ! (h , tp) ⟶ Ret (inj₁ stIdle))
  caRB : ∀ {tm md ln} pt tp → CAwaitV l d (rcvC l d tm md ln (MsgCSRollBackward pt tp))
                                         (apiCSev l d recvCSRollback ! (pt , tp) ⟶ Ret (inj₁ stIdle))
  caAw : ∀ {tm md ln}       → CAwaitV l d (rcvC l d tm md ln MsgCSAwaitReply) (Ret (inj₁ stMustReply))

-- the client stCanAwait inversion
cAwaitV : ∀ {l d x t′} → clientStep l d stCanAwait ─[ ev (evl x) ]─► t′ → CAwaitV l d x t′
cAwaitV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync (MsgCSRollForward h tp)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CAwaitV l d _) (just-injective br) (caRF h tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cAwaitV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync (MsgCSRollBackward pt tp)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CAwaitV l d _) (just-injective br) (caRB pt tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cAwaitV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync MsgCSAwaitReply} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CAwaitV l d _) (just-injective br) caAw
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSRequestNext} refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSDone} refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , keepAlive _}    refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , blockFetch _}   refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , txSubmission _} refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotify _}  refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetch _}   refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
cAwaitV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetchP _}  refl ())
cAwaitV (sVis {at = _ , sendCS _ _}    refl ())
cAwaitV (sVis {at = _ , apiCSev _ _ _} refl ())
cAwaitV (sVis {at = _ , doneCS _ _}    refl ())

-- stMustReply: the receive menu (RollForward / RollBackward), each reported
data CMustV (l : Link) (d : Dir) : C.Event → Rd → Set₁ where
  cmRF : ∀ {tm md ln} h tp  → CMustV l d (rcvC l d tm md ln (MsgCSRollForward h tp))
                                        (apiCSev l d recvCSRollforward ! (h , tp) ⟶ Ret (inj₁ stIdle))
  cmRB : ∀ {tm md ln} pt tp → CMustV l d (rcvC l d tm md ln (MsgCSRollBackward pt tp))
                                        (apiCSev l d recvCSRollback ! (pt , tp) ⟶ Ret (inj₁ stIdle))

-- the client stMustReply inversion
cMustV : ∀ {l d x t′} → clientStep l d stMustReply ─[ ev (evl x) ]─► t′ → CMustV l d x t′
cMustV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync (MsgCSRollForward h tp)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CMustV l d _) (just-injective br) (cmRF h tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cMustV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync (MsgCSRollBackward pt tp)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CMustV l d _) (just-injective br) (cmRB pt tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSRequestNext} refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSAwaitReply} refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSDone} refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , keepAlive _}    refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , blockFetch _}   refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , txSubmission _} refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotify _}  refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetch _}   refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
cMustV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetchP _}  refl ())
cMustV (sVis {at = _ , sendCS _ _}    refl ())
cMustV (sVis {at = _ , apiCSev _ _ _} refl ())
cMustV (sVis {at = _ , doneCS _ _}    refl ())

-- stIntersect: the receive menu (IntersectFound / IntersectNotFound), each reported
data CIsectV (l : Link) (d : Dir) : C.Event → Rd → Set₁ where
  cxFound : ∀ {tm md ln} pt tp → CIsectV l d (rcvC l d tm md ln (MsgCSIntersectFound pt tp))
                                            (apiCSev l d recvCSIntersectFound ! (pt , tp) ⟶ Ret (inj₁ stIdle))
  cxNot   : ∀ {tm md ln} tp    → CIsectV l d (rcvC l d tm md ln (MsgCSIntersectNotFound tp))
                                            (apiCSev l d recvCSIntersectNotFound ! tp ⟶ Ret (inj₁ stIdle))

-- the client stIntersect inversion
cIsectV : ∀ {l d x t′} → clientStep l d stIntersect ─[ ev (evl x) ]─► t′ → CIsectV l d x t′
cIsectV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync (MsgCSIntersectFound pt tp)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIsectV l d _) (just-injective br) (cxFound pt tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIsectV {l} {d} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound tp)} refl br)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = subst (CIsectV l d _) (just-injective br) (cxNot tp)
... | no _     | _        with () ← br
... | yes refl | no _     with () ← br
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSRequestNext} refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSAwaitReply} refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync MsgCSDone} refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , keepAlive _}    refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , blockFetch _}   refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , txSubmission _} refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotify _}  refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetch _}   refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
cIsectV (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetchP _}  refl ())
cIsectV (sVis {at = _ , sendCS _ _}    refl ())
cIsectV (sVis {at = _ , apiCSev _ _ _} refl ())
cIsectV (sVis {at = _ , doneCS _ _}    refl ())

------------------------------------------------------------------------
-- premise (b): τ-accessibility, read off the views
------------------------------------------------------------------------

-- what each server view leaves behind is accessible
sIdleR : ∀ {l d x t′} → SIdleV l d x t′ → MAccR ∅ES t′
sIdleR siNext     = MAccR-⟶₀ _ (MAccR-Ret _)
sIdleR (siFind _) = MAccR-Output ⦃ DecEq-ListPoint ⦄ _ _ (MAccR-Ret _)
sIdleR siDone     = MAccR-⟶₀ _ (MAccR-Ret _)

-- a server send round is accessible
sSendR : ∀ {l d msg st} → MAccR ∅ES (sSend l d msg st)
sSendR = MAccR-Output _ _ (MAccR-Ret _)

-- every server body state is accessible at every reachable state
bodyR : ∀ {l d} st → MAccR ∅ES (serverStep l d st)
bodyR {l} {d} stIdle      = MAccR-react refl λ {at} {a} eq → sIdleR (sIdleV {l} {d} (sVis {at = at} {a = a} refl eq))
bodyR {l} {d} stCanAwait  = MAccR-react refl λ {at} {a} eq → case sAwaitV {l} {d} (sVis {at = at} {a = a} refl eq) of λ
  { (saRF _ _) → sSendR ; (saRB _ _) → sSendR ; (saAw _) → sSendR }
bodyR {l} {d} stMustReply = MAccR-react refl λ {at} {a} eq → case sMustV {l} {d} (sVis {at = at} {a = a} refl eq) of λ
  { (smRF _ _) → sSendR ; (smRB _ _) → sSendR }
bodyR {l} {d} stIntersect = MAccR-react refl λ {at} {a} eq → case sIsectV {l} {d} (sVis {at = at} {a = a} refl eq) of λ
  { (sxFound _ _) → sSendR ; (sxNot _) → sSendR }
bodyR stDone              = MAccR-Ret _

-- every round starts with a visible event (`stDone` returns `inj₂`, not a loop-back)
bodyG : ∀ {l d} st → NoRetBy Looping ∅ES (serverStep l d st)
bodyG stIdle      = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
bodyG stCanAwait  = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
bodyG stMustReply = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
bodyG stIntersect = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
bodyG stDone      = NoRetBy-Ret λ ()

-- THE PEER LEAF, at the source alphabet …
csServer-τ : ∀ l d → τ-AccReach (CSserverStClient l d)
csServer-τ l d = MAccR→τ-AccReach (MAccR-iter {k = serverStep l d} bodyG bodyR stIdle)

-- … and renamed onto `Net_Api`
csServerA-τ : ∀ l d → DF.τ-AccReach (CSserverA l d)
csServerA-τ l d = τ-AccReach-renameMap (csServer-τ l d)

-- a client send round is accessible
cSendR : ∀ {l d msg st} → MAccR ∅ES (cSend l d msg st)
cSendR = MAccR-Output _ _ (MAccR-Ret _)

-- what each client view leaves behind is accessible
cAwaitR : ∀ {l d x t′} → CAwaitV l d x t′ → MAccR ∅ES t′
cAwaitR (caRF _ _) = MAccR-Output _ _ (MAccR-Ret _)
cAwaitR (caRB _ _) = MAccR-Output _ _ (MAccR-Ret _)
cAwaitR caAw       = MAccR-Ret _

-- (stMustReply)
cMustR : ∀ {l d x t′} → CMustV l d x t′ → MAccR ∅ES t′
cMustR (cmRF _ _) = MAccR-Output _ _ (MAccR-Ret _)
cMustR (cmRB _ _) = MAccR-Output _ _ (MAccR-Ret _)

-- (stIntersect)
cIsectR : ∀ {l d x t′} → CIsectV l d x t′ → MAccR ∅ES t′
cIsectR (cxFound _ _) = MAccR-Output _ _ (MAccR-Ret _)
cIsectR (cxNot _)     = MAccR-Output _ _ (MAccR-Ret _)

-- every client body state is accessible at every reachable state
cbodyR : ∀ {l d} st → MAccR ∅ES (clientStep l d st)
cbodyR {l} {d} stIdle      = MAccR-react refl λ {at} {a} eq → case cIdleV {l} {d} (sVis {at = at} {a = a} refl eq) of λ
  { (ciNext _) → cSendR ; (ciFind _) → cSendR ; (ciDone _) → cSendR }
cbodyR {l} {d} stCanAwait  = MAccR-react refl λ {at} {a} eq → cAwaitR (cAwaitV {l} {d} (sVis {at = at} {a = a} refl eq))
cbodyR {l} {d} stMustReply = MAccR-react refl λ {at} {a} eq → cMustR (cMustV {l} {d} (sVis {at = at} {a = a} refl eq))
cbodyR {l} {d} stIntersect = MAccR-react refl λ {at} {a} eq → cIsectR (cIsectV {l} {d} (sVis {at = at} {a = a} refl eq))
cbodyR stDone              = MAccR-Ret _

-- every client round starts with a visible event
cbodyG : ∀ {l d} st → NoRetBy Looping ∅ES (clientStep l d st)
cbodyG stIdle      = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stCanAwait  = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stMustReply = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stIntersect = NoRetBy-mono (λ _ _ → tt) (Guarded-react refl λ ())
cbodyG stDone      = NoRetBy-Ret λ ()

-- THE CLIENT LEAF, at the source alphabet …
csClient-τ : ∀ l d → τ-AccReach (CSclientStClient l d)
csClient-τ l d = MAccR→τ-AccReach (MAccR-iter {k = clientStep l d} cbodyG cbodyR stIdle)

-- … and renamed onto `Net_Api`
csClientA-τ : ∀ l d → DF.τ-AccReach (CSclientA l d)
csClientA-τ l d = τ-AccReach-renameMap (csClient-τ l d)

------------------------------------------------------------------------
-- counting: `potIter` at `CSEv` (one obligation per view constructor,
-- discharged by reduction), carried onto `Net_Api` by `Σc≤-ren`
------------------------------------------------------------------------

-- the zero potential
Φ0 : CSState → ℕ
Φ0 _ = 0

-- P1 obligations (wire inputs ≤ api labels + 1)
P1 : CSState → C.Event → Rd → Set₁
P1 = StepPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1}

-- the server's P1, per view
p1-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → P1 stIdle x t′
p1-sIdle siNext     = sp-⟶
p1-sIdle (siFind _) = sp-Out ⦃ DecEq-ListPoint ⦄
p1-sIdle siDone     = sp-⟶

-- (stCanAwait)
p1-sAwait : ∀ {l d x t′} → SAwaitV l d x t′ → P1 stCanAwait x t′
p1-sAwait (saRF _ _) = sp-Out
p1-sAwait (saRB _ _) = sp-Out
p1-sAwait (saAw _)   = sp-Out

-- (stMustReply)
p1-sMust : ∀ {l d x t′} → SMustV l d x t′ → P1 stMustReply x t′
p1-sMust (smRF _ _) = sp-Out
p1-sMust (smRB _ _) = sp-Out

-- (stIntersect)
p1-sIsect : ∀ {l d x t′} → SIsectV l d x t′ → P1 stIntersect x t′
p1-sIsect (sxFound _ _) = sp-Out
p1-sIsect (sxNot _)     = sp-Out

-- the server's P1 rounds
p1-s : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} st (serverStep l d st)
p1-s stIdle      = rp-pch λ st → p1-sIdle (sIdleV st)
p1-s stCanAwait  = rp-pch λ st → p1-sAwait (sAwaitV st)
p1-s stMustReply = rp-pch λ st → p1-sMust (sMustV st)
p1-s stIntersect = rp-pch λ st → p1-sIsect (sIsectV st)
p1-s stDone      = rp-done

-- the client's P1, per view
p1-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → P1 stIdle x t′
p1-cIdle (ciNext _) = sp-Out
p1-cIdle (ciFind _) = sp-Out
p1-cIdle (ciDone _) = sp-Out

-- (stCanAwait)
p1-cAwait : ∀ {l d x t′} → CAwaitV l d x t′ → P1 stCanAwait x t′
p1-cAwait (caRF _ _) = sp-Out
p1-cAwait (caRB _ _) = sp-Out
p1-cAwait caAw       = sp-Ret

-- (stMustReply)
p1-cMust : ∀ {l d x t′} → CMustV l d x t′ → P1 stMustReply x t′
p1-cMust (cmRF _ _) = sp-Out
p1-cMust (cmRB _ _) = sp-Out

-- (stIntersect)
p1-cIsect : ∀ {l d x t′} → CIsectV l d x t′ → P1 stIntersect x t′
p1-cIsect (cxFound _ _) = sp-Out
p1-cIsect (cxNot _)     = sp-Out

-- the client's P1 rounds
p1-c : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {cIn ʳ} {cApi ʳ} {1} st (clientStep l d st)
p1-c stIdle      = rp-pch λ st → p1-cIdle (cIdleV st)
p1-c stCanAwait  = rp-pch λ st → p1-cAwait (cAwaitV st)
p1-c stMustReply = rp-pch λ st → p1-cMust (cMustV st)
p1-c stIntersect = rp-pch λ st → p1-cIsect (cIsectV st)
p1-c stDone      = rp-done

-- P1 (ChainSync server): every wire input but one was commanded through the api
csServerA-P1 : ∀ l d {s W} → CSserverA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
csServerA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 (cIn ʳ) (cApi ʳ) 1 (p1-s {l} {d}) stIdle)

-- P1 (ChainSync client)
csClientA-P1 : ∀ l d {s W} → CSclientA l d ⟹⟨ s ⟩ W → Σc cIn (labels s) ≤ Σc cApi (labels s) + 1
csClientA-P1 l d = Σc≤-ren cIn cApi 1 (potIter Φ0 (cIn ʳ) (cApi ʳ) 1 (p1-c {l} {d}) stIdle)

-- relay obligations: RollForward reports ≤ RollForwards received
RepC : CSState → C.Event → Rd → Set₁
RepC = StepPot {Rx = Rr} {Φ = Φ0} {cRep recvCSRollforward ʳ} {wOut RF ʳ} {0}

-- (stIdle)
rep-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → RepC stIdle x t′
rep-cIdle (ciNext _) = sp-Out
rep-cIdle (ciFind _) = sp-Out
rep-cIdle (ciDone _) = sp-Out

-- (stCanAwait)
rep-cAwait : ∀ {l d x t′} → CAwaitV l d x t′ → RepC stCanAwait x t′
rep-cAwait (caRF _ _) = sp-Out
rep-cAwait (caRB _ _) = sp-Out
rep-cAwait caAw       = sp-Ret

-- (stMustReply)
rep-cMust : ∀ {l d x t′} → CMustV l d x t′ → RepC stMustReply x t′
rep-cMust (cmRF _ _) = sp-Out
rep-cMust (cmRB _ _) = sp-Out

-- (stIntersect)
rep-cIsect : ∀ {l d x t′} → CIsectV l d x t′ → RepC stIntersect x t′
rep-cIsect (cxFound _ _) = sp-Out
rep-cIsect (cxNot _)     = sp-Out

-- the client's report rounds
rep-c : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {cRep recvCSRollforward ʳ} {wOut RF ʳ} {0} st (clientStep l d st)
rep-c stIdle      = rp-pch λ st → rep-cIdle (cIdleV st)
rep-c stCanAwait  = rp-pch λ st → rep-cAwait (cAwaitV st)
rep-c stMustReply = rp-pch λ st → rep-cMust (cMustV st)
rep-c stIntersect = rp-pch λ st → rep-cIsect (cIsectV st)
rep-c stDone      = rp-done

-- RELAY (client): every RollForward it reports, it received
csClientA-rep : ∀ l d {s W} → CSclientA l d ⟹⟨ s ⟩ W
              → Σc (cRep recvCSRollforward) (labels s) ≤ Σc (wOut RF) (labels s)
csClientA-rep l d {s} tr =
  subst (Σc (cRep recvCSRollforward) (labels s) ≤_) (+-identityʳ _)
    (Σc≤-ren (cRep recvCSRollforward) (wOut RF) 0 (potIter Φ0 _ _ 0 (rep-c {l} {d}) stIdle) tr)

-- relay obligations: the client sends no RollForward
NoRF : CSState → C.Event → Rd → Set₁
NoRF = StepPot {Rx = Rr} {Φ = Φ0} {wIn RF ʳ} {λ _ → 0} {0}

-- (stIdle)
noRF-cIdle : ∀ {l d x t′} → CIdleV l d x t′ → NoRF stIdle x t′
noRF-cIdle (ciNext _) = sp-Out
noRF-cIdle (ciFind _) = sp-Out
noRF-cIdle (ciDone _) = sp-Out

-- (stCanAwait)
noRF-cAwait : ∀ {l d x t′} → CAwaitV l d x t′ → NoRF stCanAwait x t′
noRF-cAwait (caRF _ _) = sp-Out
noRF-cAwait (caRB _ _) = sp-Out
noRF-cAwait caAw       = sp-Ret

-- (stMustReply)
noRF-cMust : ∀ {l d x t′} → CMustV l d x t′ → NoRF stMustReply x t′
noRF-cMust (cmRF _ _) = sp-Out
noRF-cMust (cmRB _ _) = sp-Out

-- (stIntersect)
noRF-cIsect : ∀ {l d x t′} → CIsectV l d x t′ → NoRF stIntersect x t′
noRF-cIsect (cxFound _ _) = sp-Out
noRF-cIsect (cxNot _)     = sp-Out

-- the client's no-RollForward rounds
noRF-c : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {wIn RF ʳ} {λ _ → 0} {0} st (clientStep l d st)
noRF-c stIdle      = rp-pch λ st → noRF-cIdle (cIdleV st)
noRF-c stCanAwait  = rp-pch λ st → noRF-cAwait (cAwaitV st)
noRF-c stMustReply = rp-pch λ st → noRF-cMust (cMustV st)
noRF-c stIntersect = rp-pch λ st → noRF-cIsect (cIsectV st)
noRF-c stDone      = rp-done

-- RELAY (client): it puts no RollForward on the wire
csClientA-noRF : ∀ l d {s W} → CSclientA l d ⟹⟨ s ⟩ W → Σc (wIn RF) (labels s) ≡ 0
csClientA-noRF l d {s} tr =
  n≤0⇒n≡0 (subst (Σc (wIn RF) (labels s) ≤_) (cong (_+ 0) (Σc-0 (labels s)))
            (Σc≤-ren (wIn RF) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (noRF-c {l} {d}) stIdle) tr))

-- relay obligations: RollForwards sent ≤ RollForwards commanded
RFS : CSState → C.Event → Rd → Set₁
RFS = StepPot {Rx = Rr} {Φ = Φ0} {wIn RF ʳ} {cCmd sendCSRollForward ʳ} {0}

-- (stIdle)
rf-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → RFS stIdle x t′
rf-sIdle siNext     = sp-⟶
rf-sIdle (siFind _) = sp-Out ⦃ DecEq-ListPoint ⦄
rf-sIdle siDone     = sp-⟶

-- (stCanAwait)
rf-sAwait : ∀ {l d x t′} → SAwaitV l d x t′ → RFS stCanAwait x t′
rf-sAwait (saRF _ _) = sp-Out
rf-sAwait (saRB _ _) = sp-Out
rf-sAwait (saAw _)   = sp-Out

-- (stMustReply)
rf-sMust : ∀ {l d x t′} → SMustV l d x t′ → RFS stMustReply x t′
rf-sMust (smRF _ _) = sp-Out
rf-sMust (smRB _ _) = sp-Out

-- (stIntersect)
rf-sIsect : ∀ {l d x t′} → SIsectV l d x t′ → RFS stIntersect x t′
rf-sIsect (sxFound _ _) = sp-Out
rf-sIsect (sxNot _)     = sp-Out

-- the server's RollForward rounds
rf-s : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {wIn RF ʳ} {cCmd sendCSRollForward ʳ} {0} st (serverStep l d st)
rf-s stIdle      = rp-pch λ st → rf-sIdle (sIdleV st)
rf-s stCanAwait  = rp-pch λ st → rf-sAwait (sAwaitV st)
rf-s stMustReply = rp-pch λ st → rf-sMust (sMustV st)
rf-s stIntersect = rp-pch λ st → rf-sIsect (sIsectV st)
rf-s stDone      = rp-done

-- RELAY (server): every RollForward it sends was commanded
csServerA-RF : ∀ l d {s W} → CSserverA l d ⟹⟨ s ⟩ W
             → Σc (wIn RF) (labels s) ≤ Σc (cCmd sendCSRollForward) (labels s)
csServerA-RF l d {s} tr =
  subst (Σc (wIn RF) (labels s) ≤_) (+-identityʳ _)
    (Σc≤-ren (wIn RF) (cCmd sendCSRollForward) 0 (potIter Φ0 _ _ 0 (rf-s {l} {d}) stIdle) tr)

------------------------------------------------------------------------
-- provenance (D1-b): ChainSync never touches the block chain — by its
-- renaming alone (`ChS` has no clause for a ChainSync cell, `apiCS`, `done`)
------------------------------------------------------------------------

-- no ChainSync label is a chain label
noChain : ∀ {e : C.Event} {y} → ChS (renE e) y → ⊥
noChain {C.evLabel _ (sendCS _ _) _}    ()
noChain {C.evLabel _ (receiveCS _ _) _} ()
noChain {C.evLabel _ (apiCSev _ _ _) _} ()
noChain {C.evLabel _ (doneCS _ _) _}    ()

-- every renamed ChainSync process is chain-free
csA-PA : ∀ {ℓr} {R : Set ℓr} {P : PTree CSEv (ExtI CSEv) R} → PL.PA ChS ChS InP (RenCS.renameMap P)
csA-PA = PA-ren (pa λ {_} {s} _ → Prov-free noChain (S.labels s))

-- (the client)
csClientA-PA : ∀ l d → PL.PA ChS ChS InP (CSclientA l d)
csClientA-PA l d = csA-PA

-- (the server)
csServerA-PA : ∀ l d → PL.PA ChS ChS InP (CSserverA l d)
csServerA-PA l d = csA-PA

------------------------------------------------------------------------
-- Task 9a (F3a): the report alphabet — the server makes no RollForward
-- report (that report is the client's)
------------------------------------------------------------------------

-- a server step makes no RollForward report
NRS : CSState → C.Event → Rd → Set₁
NRS = StepPot {Rx = Rr} {Φ = Φ0} {cRep recvCSRollforward ʳ} {λ _ → 0} {0}

-- (stIdle)
nr-sIdle : ∀ {l d x t′} → SIdleV l d x t′ → NRS stIdle x t′
nr-sIdle siNext     = sp-⟶
nr-sIdle (siFind _) = sp-Out ⦃ DecEq-ListPoint ⦄
nr-sIdle siDone     = sp-⟶

-- (stCanAwait)
nr-sAwait : ∀ {l d x t′} → SAwaitV l d x t′ → NRS stCanAwait x t′
nr-sAwait (saRF _ _) = sp-Out
nr-sAwait (saRB _ _) = sp-Out
nr-sAwait (saAw _)   = sp-Out

-- (stMustReply)
nr-sMust : ∀ {l d x t′} → SMustV l d x t′ → NRS stMustReply x t′
nr-sMust (smRF _ _) = sp-Out
nr-sMust (smRB _ _) = sp-Out

-- (stIntersect)
nr-sIsect : ∀ {l d x t′} → SIsectV l d x t′ → NRS stIntersect x t′
nr-sIsect (sxFound _ _) = sp-Out
nr-sIsect (sxNot _)     = sp-Out

-- the server's rounds
nr-s : ∀ {l d} st → RoundPot {Rx = Rr} {Φ = Φ0} {cRep recvCSRollforward ʳ} {λ _ → 0} {0} st (serverStep l d st)
nr-s stIdle      = rp-pch λ st → nr-sIdle (sIdleV st)
nr-s stCanAwait  = rp-pch λ st → nr-sAwait (sAwaitV st)
nr-s stMustReply = rp-pch λ st → nr-sMust (sMustV st)
nr-s stIntersect = rp-pch λ st → nr-sIsect (sIsectV st)
nr-s stDone      = rp-done

-- ALPHABET (server): it makes no RollForward report
csServerA-noRep : ∀ l d {s W} → CSserverA l d ⟹⟨ s ⟩ W → Σc (cRep recvCSRollforward) (labels s) ≡ 0
csServerA-noRep l d {s} tr =
  n≤0⇒n≡0 (subst (Σc (cRep recvCSRollforward) (labels s) ≤_) (cong (_+ 0) (Σc-0 (labels s)))
            (Σc≤-ren (cRep recvCSRollforward) (λ _ → 0) 0 (potIter Φ0 _ _ 0 (nr-s {l} {d}) stIdle) tr))

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- PipePairPeers2 — the ChainSync + TxSubmission slice of the FourNode
-- node-side pipeline milestone (M1, Part 10).
--
-- SPLIT RATIONALE (controller-sanctioned): the flat `PipePair.agda` keeps
-- the contract surface (`pipe`/`pipeSpec`/goal types) + the already-landed
-- KA/BF content.  ChainSync and TxSubmission must be imported QUALIFIED
-- (their `CSState`/`TSState`/`clientStep`/`serverStep`/`Rr` clash with the
-- opened KeepAlive names, AND their `DecEq (List Point)`/`DecEq (List Txid)`
-- instances shadow the generic `DecEqI.DecEq-List` used by `PipePair`'s spec
-- tables).  Isolating them here keeps `PipePair` unambiguous.  This module
-- houses the CS/TS impl-side `OffersOnly` (item 2(b) catch-up) and the CS/TS
-- per-peer bisims (item 3); `PipePairAssembly` consumes both.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.Nat using (ℕ)
import Data.Fin as F
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI
open import Function.Base using (case_of_)

open import Process_Trees
open PTree

-- the concrete FourNode instantiation (same as PipePair)
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; consume; apiES; linkBD; linkCD )

open import CSP.Examples.Cardano_network.Params using (Params)
open Params p

open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net p

-- the ChainSync / TxSubmission impl peers + their event injections
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( CSclientA; CSserverA; ιCS; ιCS⁻¹; ιCS-linv
        ; TSclientA; TSserverA; ιTS; ιTS⁻¹; ιTS-linv )

-- ChainSync source FSM (qualified — see the split rationale)
import CSP.Examples.Cardano_network.ChainSync p as CS
import CSP.Operators {E = CS.CSEv} CS.CSEv-≟ as SrcOpC
import CSP.Rename {E₁ = CS.CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RenCS
-- TxSubmission source FSM (qualified — see the split rationale)
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Operators {E = TS.TSEv} TS.TSEv-≟ as SrcOpT
import CSP.Rename {E₁ = TS.TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RenTS

-- the ambient CSP operators + DR/weak bisim + coinduction principle
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _>>_; Skip )

open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _≈DR_; deadlock-no-τ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev )
open import Semantics.BisimFromRel {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( module DRFromRel )
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; sRet; sSil; sVis; sTau; ev; evl; evLabel; Event√; √; Label; τ
        ; Diverges )

import CSP.Laws.Bisim.DRCongruenceRep
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; Disj; OffersOnly; MenuConf
        ; OffersOnly-deadlock; OffersOnly-Ret; OffersOnly-Skip; OffersOnly-mono
        ; OffersOnly-pchoice; OffersOnly-Prefix; OffersOnly-Prefix₀; OffersOnly-Output
        ; OffersOnly->>= )

-- the contract surface + the generic `RenOO` transport + `peerAlpha` slots
-- + the τ-free spec tables (`csServerSpec`/`csClientSpec`/`tsServerSpec`/
-- `tsClientSpec`) all come from `PipePair`.
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePair

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairPeers2 where

------------------------------------------------------------------------
-- Item 2(b), ChainSync server + client impl-side OffersOnly at their
-- goalBD combos (server (linkBD, lo), client (linkBD, hi)).  New per-
-- protocol infra RenCS-OO / SrcCS / slotCS / srcAlphaCS / cs-img⊆
-- (mirrors the BF block); the source-OO menu enumerations are script-
-- generated (`.superpowers/sdd/gen-src-oo.py`).
------------------------------------------------------------------------

-- the generic ren-OffersOnly specialised to the CS alphabet injection
module RenCS-OO = RenOO CS.CSEv-≟ ιCS ιCS⁻¹ ιCS-linv

-- source-side OffersOnly builders for the CS alphabet
module SrcCS = CSP.Laws.Bisim.DRCongruenceRep CS.CSEv-≟

-- the (direction) slot of a CS source event (the protocol is implicit = CS)
slotCS : AnyTypes CS.CSEv → Maybe Dir
slotCS (_ , CS.sendCS    _ d)   = just d
slotCS (_ , CS.receiveCS _ d)   = just d
slotCS (_ , CS.apiCSev   _ d _) = just d
slotCS (_ , CS.doneCS    _ d)   = just d

-- the CS source alphabet on direction `d`: every event on that direction
srcAlphaCS : Dir → SrcCS.Alpha
srcAlphaCS d at a = slotCS at ≡ just d

-- the ι-image of `srcAlphaCS d` lands in the CS peer slot on `d`
cs-img⊆ : (d : Dir) → ∀ at a → RenCS-OO.ιImg (srcAlphaCS d) at a → peerAlpha N2N_ChainSync d at a
cs-img⊆ d (_ , input  l′ d′ N2N_ChainSync)    a (_ , refl , refl) = refl
cs-img⊆ d (_ , output l′ d′ N2N_ChainSync)    a (_ , refl , refl) = refl
cs-img⊆ d (_ , done   l′ d′ N2N_ChainSync)    a (_ , refl , refl) = refl
cs-img⊆ d (_ , apiCS  l′ d′ m)                a (_ , refl , refl) = refl
cs-img⊆ d (_ , input  l′ d′ N2N_BlockFetch) a (_ , () , _)
cs-img⊆ d (_ , input  l′ d′ N2N_TxSubmission) a (_ , () , _)
cs-img⊆ d (_ , input  l′ d′ N2N_KeepAlive) a (_ , () , _)
cs-img⊆ d (_ , input  l′ d′ N2N_LeiosNotify) a (_ , () , _)
cs-img⊆ d (_ , input  l′ d′ N2N_LeiosFetch) a (_ , () , _)
cs-img⊆ d (_ , output l′ d′ N2N_BlockFetch) a (_ , () , _)
cs-img⊆ d (_ , output l′ d′ N2N_TxSubmission) a (_ , () , _)
cs-img⊆ d (_ , output l′ d′ N2N_KeepAlive) a (_ , () , _)
cs-img⊆ d (_ , output l′ d′ N2N_LeiosNotify) a (_ , () , _)
cs-img⊆ d (_ , output l′ d′ N2N_LeiosFetch) a (_ , () , _)
cs-img⊆ d (_ , done   l′ d′ N2N_BlockFetch) a (_ , () , _)
cs-img⊆ d (_ , done   l′ d′ N2N_TxSubmission) a (_ , () , _)
cs-img⊆ d (_ , done   l′ d′ N2N_KeepAlive) a (_ , () , _)
cs-img⊆ d (_ , done   l′ d′ N2N_LeiosNotify) a (_ , () , _)
cs-img⊆ d (_ , done   l′ d′ N2N_LeiosFetch) a (_ , () , _)
cs-img⊆ d (_ , sndmsg l′ d′ i)                a (_ , () , _)
cs-img⊆ d (_ , rcvmsg l′ d′ i)                a (_ , () , _)
cs-img⊆ d (_ , tx     l′ d′ i)                a (_ , () , _)
cs-img⊆ d (_ , sndack l′ d′ i)                a (_ , () , _)
cs-img⊆ d (_ , rcvack l′ d′ i)                a (_ , () , _)
cs-img⊆ d (_ , ack    l′ d′ i)                a (_ , () , _)
cs-img⊆ d (_ , apiKA l′ d′ m)                a (_ , () , _)
cs-img⊆ d (_ , apiBF l′ d′ m)                a (_ , () , _)
cs-img⊆ d (_ , apiTS l′ d′ m)                a (_ , () , _)
cs-img⊆ d (_ , apiLN l′ d′ m)                a (_ , () , _)
cs-img⊆ d (_ , apiLF l′ d′ m)                a (_ , () , _)
cs-img⊆ d (_ , break  l′)                     a (_ , () , _)

-- CS SERVER source peer confines its offers to `srcAlphaCS lo`.
csServerSrc-OO : (l : Link) → SrcCS.OffersOnly (srcAlphaCS lo) (CS.CSserverStClient l lo)
csServerSrc-OO F.zero = SrcCS.OffersOnly-iter {k = CS.serverStep F.zero lo} {a = CS.stIdle} step
  where
  step : ∀ q → SrcCS.OffersOnly (srcAlphaCS lo) (CS.serverStep F.zero lo q)
  step CS.stIdle = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    -- recv MsgCSRequestNext: fires only on (F.zero , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) refl =
      refl , SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq = case eq of λ ()
    -- recv MsgCSFindIntersect: fires only on (F.zero , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) refl =
      refl , SrcCS.OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    -- recv MsgCSDone: fires only on (F.zero , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSDone)) refl =
      refl , SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stCanAwait = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    -- api sendCSAwaitReply: fires only on (F.zero , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSAwaitReply) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev F.zero hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSAwaitReply) a ()
    -- api sendCSRollForward: fires only on (F.zero , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollForward) (h , t) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev F.zero hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollForward) (h , t) ()
    -- api sendCSRollBackward: fires only on (F.zero , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollBackward) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev F.zero hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stMustReply = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    -- api sendCSRollForward: fires only on (F.zero , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollForward) (h , t) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev F.zero hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollForward) (h , t) ()
    -- api sendCSRollBackward: fires only on (F.zero , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollBackward) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev F.zero hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stIntersect = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollForward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollBackward) a eq = case eq of λ ()
    -- api sendCSIntersectFound: fires only on (F.zero , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSIntersectFound) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev F.zero hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSIntersectFound) (pt , tp) ()
    -- api sendCSIntersectNotFound: fires only on (F.zero , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSIntersectNotFound) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev F.zero hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stDone = SrcCS.OffersOnly-Ret
csServerSrc-OO (F.suc F.zero) = SrcCS.OffersOnly-iter {k = CS.serverStep (F.suc F.zero) lo} {a = CS.stIdle} step
  where
  step : ∀ q → SrcCS.OffersOnly (srcAlphaCS lo) (CS.serverStep (F.suc F.zero) lo q)
  step CS.stIdle = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    -- recv MsgCSRequestNext: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) refl =
      refl , SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq = case eq of λ ()
    -- recv MsgCSFindIntersect: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) refl =
      refl , SrcCS.OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    -- recv MsgCSDone: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSDone)) refl =
      refl , SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stCanAwait = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    -- api sendCSAwaitReply: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSAwaitReply) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSAwaitReply) a ()
    -- api sendCSRollForward: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollForward) (h , t) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollForward) (h , t) ()
    -- api sendCSRollBackward: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollBackward) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stMustReply = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    -- api sendCSRollForward: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollForward) (h , t) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollForward) (h , t) ()
    -- api sendCSRollBackward: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollBackward) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stIntersect = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollForward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollBackward) a eq = case eq of λ ()
    -- api sendCSIntersectFound: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSIntersectFound) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSIntersectFound) (pt , tp) ()
    -- api sendCSIntersectNotFound: fires only on ((F.suc F.zero) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSIntersectNotFound) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stDone = SrcCS.OffersOnly-Ret
csServerSrc-OO (F.suc (F.suc F.zero)) = SrcCS.OffersOnly-iter {k = CS.serverStep (F.suc (F.suc F.zero)) lo} {a = CS.stIdle} step
  where
  step : ∀ q → SrcCS.OffersOnly (srcAlphaCS lo) (CS.serverStep (F.suc (F.suc F.zero)) lo q)
  step CS.stIdle = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    -- recv MsgCSRequestNext: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) refl =
      refl , SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq = case eq of λ ()
    -- recv MsgCSFindIntersect: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) refl =
      refl , SrcCS.OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    -- recv MsgCSDone: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSDone)) refl =
      refl , SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stCanAwait = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    -- api sendCSAwaitReply: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSAwaitReply) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSAwaitReply) a ()
    -- api sendCSRollForward: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollForward) (h , t) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollForward) (h , t) ()
    -- api sendCSRollBackward: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollBackward) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stMustReply = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    -- api sendCSRollForward: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollForward) (h , t) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollForward) (h , t) ()
    -- api sendCSRollBackward: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollBackward) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stIntersect = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollForward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollBackward) a eq = case eq of λ ()
    -- api sendCSIntersectFound: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSIntersectFound) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSIntersectFound) (pt , tp) ()
    -- api sendCSIntersectNotFound: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSIntersectNotFound) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stDone = SrcCS.OffersOnly-Ret
csServerSrc-OO (F.suc (F.suc (F.suc F.zero))) = SrcCS.OffersOnly-iter {k = CS.serverStep (F.suc (F.suc (F.suc F.zero))) lo} {a = CS.stIdle} step
  where
  step : ∀ q → SrcCS.OffersOnly (srcAlphaCS lo) (CS.serverStep (F.suc (F.suc (F.suc F.zero))) lo q)
  step CS.stIdle = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    -- recv MsgCSRequestNext: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRequestNext)) refl =
      refl , SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRequestNext)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq = case eq of λ ()
    -- recv MsgCSFindIntersect: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) refl =
      refl , SrcCS.OffersOnly-Output ⦃ DecEqI.DecEq-List ⦄ refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    -- recv MsgCSDone: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSDone)) refl =
      refl , SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSDone)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stCanAwait = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    -- api sendCSAwaitReply: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSAwaitReply) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSAwaitReply) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSAwaitReply) a ()
    -- api sendCSRollForward: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollForward) (h , t) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollForward) (h , t) ()
    -- api sendCSRollBackward: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollBackward) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stMustReply = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    -- api sendCSRollForward: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollForward) (h , t) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollForward) (h , t) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollForward) (h , t) ()
    -- api sendCSRollBackward: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRollBackward) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRollBackward) (pt , tp) ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stIntersect = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS lo) _
    mc (_ , CS.apiCSev _ _ sendCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSDone) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollForward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollBackward) a eq = case eq of λ ()
    -- api sendCSIntersectFound: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev F.zero hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSIntersectFound) (pt , tp) ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSIntersectFound) (pt , tp) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSIntersectFound) (pt , tp) ()
    -- api sendCSIntersectNotFound: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , CS.apiCSev F.zero lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSIntersectNotFound) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSIntersectNotFound) a ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stDone = SrcCS.OffersOnly-Ret

-- CS SERVER impl peer confines to its (ChainSync, lo) slot (transport + mono)
csServer-OO : (l : Link) → OffersOnly (peerAlpha N2N_ChainSync lo) (CSserverA l lo)
csServer-OO l = OffersOnly-mono (cs-img⊆ lo) (RenCS-OO.ren-OffersOnly (csServerSrc-OO l))

-- CS CLIENT source peer confines its offers to `srcAlphaCS hi`.
csClientSrc-OO : (l : Link) → SrcCS.OffersOnly (srcAlphaCS hi) (CS.CSclientStClient l hi)
csClientSrc-OO F.zero = SrcCS.OffersOnly-iter {k = CS.clientStep F.zero hi} {a = CS.stIdle} step
  where
  step : ∀ q → SrcCS.OffersOnly (srcAlphaCS hi) (CS.clientStep F.zero hi q)
  step CS.stIdle = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    -- api sendCSRequestNext: fires only on (F.zero , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSRequestNext) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRequestNext) a ()
    -- api sendCSFindIntersect: fires only on (F.zero , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSFindIntersect) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSFindIntersect) a ()
    -- api sendCSDone: fires only on (F.zero , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSDone) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSDone) a refl =
      refl , SrcCS.OffersOnly-Output refl (SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret)
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSDone) a ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollForward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollBackward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stCanAwait = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    -- recv MsgCSAwaitReply: fires only on (F.zero , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) refl =
      refl , SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    -- recv MsgCSRollForward: fires only on (F.zero , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    -- recv MsgCSRollBackward: fires only on (F.zero , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stMustReply = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    -- recv MsgCSRollForward: fires only on (F.zero , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    -- recv MsgCSRollBackward: fires only on (F.zero , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stIntersect = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    -- recv MsgCSIntersectFound: fires only on (F.zero , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    -- recv MsgCSIntersectNotFound: fires only on (F.zero , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stDone = SrcCS.OffersOnly-Ret
csClientSrc-OO (F.suc F.zero) = SrcCS.OffersOnly-iter {k = CS.clientStep (F.suc F.zero) hi} {a = CS.stIdle} step
  where
  step : ∀ q → SrcCS.OffersOnly (srcAlphaCS hi) (CS.clientStep (F.suc F.zero) hi q)
  step CS.stIdle = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    -- api sendCSRequestNext: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRequestNext) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRequestNext) a ()
    -- api sendCSFindIntersect: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSFindIntersect) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSFindIntersect) a ()
    -- api sendCSDone: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSDone) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSDone) a refl =
      refl , SrcCS.OffersOnly-Output refl (SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret)
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSDone) a ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollForward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollBackward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stCanAwait = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    -- recv MsgCSAwaitReply: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) refl =
      refl , SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    -- recv MsgCSRollForward: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    -- recv MsgCSRollBackward: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stMustReply = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    -- recv MsgCSRollForward: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    -- recv MsgCSRollBackward: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stIntersect = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    -- recv MsgCSIntersectFound: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    -- recv MsgCSIntersectNotFound: fires only on ((F.suc F.zero) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stDone = SrcCS.OffersOnly-Ret
csClientSrc-OO (F.suc (F.suc F.zero)) = SrcCS.OffersOnly-iter {k = CS.clientStep (F.suc (F.suc F.zero)) hi} {a = CS.stIdle} step
  where
  step : ∀ q → SrcCS.OffersOnly (srcAlphaCS hi) (CS.clientStep (F.suc (F.suc F.zero)) hi q)
  step CS.stIdle = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    -- api sendCSRequestNext: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRequestNext) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRequestNext) a ()
    -- api sendCSFindIntersect: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSFindIntersect) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSFindIntersect) a ()
    -- api sendCSDone: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSDone) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSDone) a refl =
      refl , SrcCS.OffersOnly-Output refl (SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret)
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSDone) a ()
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollForward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollBackward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stCanAwait = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    -- recv MsgCSAwaitReply: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) refl =
      refl , SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    -- recv MsgCSRollForward: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    -- recv MsgCSRollBackward: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stMustReply = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    -- recv MsgCSRollForward: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    -- recv MsgCSRollBackward: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stIntersect = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    -- recv MsgCSIntersectFound: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    -- recv MsgCSIntersectNotFound: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stDone = SrcCS.OffersOnly-Ret
csClientSrc-OO (F.suc (F.suc (F.suc F.zero))) = SrcCS.OffersOnly-iter {k = CS.clientStep (F.suc (F.suc (F.suc F.zero))) hi} {a = CS.stIdle} step
  where
  step : ∀ q → SrcCS.OffersOnly (srcAlphaCS hi) (CS.clientStep (F.suc (F.suc (F.suc F.zero))) hi q)
  step CS.stIdle = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    -- api sendCSRequestNext: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSRequestNext) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSRequestNext) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    -- api sendCSFindIntersect: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSFindIntersect) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSFindIntersect) a refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    -- api sendCSDone: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.apiCSev F.zero lo sendCSDone) a ()
    mc (_ , CS.apiCSev F.zero hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc F.zero) hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc F.zero)) hi sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) lo sendCSDone) a ()
    mc (_ , CS.apiCSev (F.suc (F.suc (F.suc F.zero))) hi sendCSDone) a refl =
      refl , SrcCS.OffersOnly-Output refl (SrcCS.OffersOnly-Prefix₀ (λ _ → refl) SrcCS.OffersOnly-Ret)
    mc (_ , CS.apiCSev _ _ sendCSAwaitReply) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollForward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSRollBackward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ sendCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollforward) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSRollback) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ recvCSIntersectNotFound) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSRequestNext) a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ reqCSFindIntersect) a eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.receiveCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stCanAwait = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    -- recv MsgCSAwaitReply: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSAwaitReply)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSAwaitReply)) refl =
      refl , SrcCS.OffersOnly-Ret
    -- recv MsgCSRollForward: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    -- recv MsgCSRollBackward: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stMustReply = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    -- recv MsgCSRollForward: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    -- recv MsgCSRollBackward: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stIntersect = SrcCS.OffersOnly-pchoice mc
    where
    mc : SrcCS.MenuConf (srcAlphaCS hi) _
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRequestNext)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSAwaitReply)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq = case eq of λ ()
    -- recv MsgCSIntersectFound: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    -- recv MsgCSIntersectNotFound: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , CS.receiveCS F.zero lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS F.zero hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc F.zero) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
    mc (_ , CS.receiveCS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) refl =
      refl , SrcCS.OffersOnly-Output refl SrcCS.OffersOnly-Ret
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , chainSync (MsgCSDone)) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , txSubmission _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , CS.receiveCS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , CS.sendCS _ _)    a eq = case eq of λ ()
    mc (_ , CS.apiCSev _ _ _)   a eq = case eq of λ ()
    mc (_ , CS.doneCS _ _)    a eq = case eq of λ ()
  step CS.stDone = SrcCS.OffersOnly-Ret

-- CS CLIENT impl peer confines to its (ChainSync, hi) slot (transport + mono)
csClient-OO : (l : Link) → OffersOnly (peerAlpha N2N_ChainSync hi) (CSclientA l hi)
csClient-OO l = OffersOnly-mono (cs-img⊆ hi) (RenCS-OO.ren-OffersOnly (csClientSrc-OO l))


------------------------------------------------------------------------
-- Item 2(b), TxSubmission server + client impl-side OffersOnly at their
-- goalBD combos (server (linkBD, lo), client (linkBD, hi)).  Per-protocol
-- infra RenTS-OO / SrcTS / slotTS / srcAlphaTS / ts-img⊆ (mirrors CS).
-- The TS client `stInit` is a direct auto-send Output (not a menu); the
-- `MsgTSRequestTxIds` notification splits on BlockingStyle; the two
-- tuple/list api-emit outputs pin their (defeq) DecEq instance.
------------------------------------------------------------------------

-- the generic ren-OffersOnly specialised to the TS alphabet injection
module RenTS-OO = RenOO TS.TSEv-≟ ιTS ιTS⁻¹ ιTS-linv

-- source-side OffersOnly builders for the TS alphabet
module SrcTS = CSP.Laws.Bisim.DRCongruenceRep TS.TSEv-≟

-- the (direction) slot of a TS source event (the protocol is implicit = TS)
slotTS : AnyTypes TS.TSEv → Maybe Dir
slotTS (_ , TS.sendTS    _ d)   = just d
slotTS (_ , TS.receiveTS _ d)   = just d
slotTS (_ , TS.apiTSev   _ d _) = just d
slotTS (_ , TS.doneTS    _ d)   = just d

-- the TS source alphabet on direction `d`: every event on that direction
srcAlphaTS : Dir → SrcTS.Alpha
srcAlphaTS d at a = slotTS at ≡ just d

-- the ι-image of `srcAlphaTS d` lands in the TS peer slot on `d`
ts-img⊆ : (d : Dir) → ∀ at a → RenTS-OO.ιImg (srcAlphaTS d) at a → peerAlpha N2N_TxSubmission d at a
ts-img⊆ d (_ , input  l′ d′ N2N_TxSubmission)    a (_ , refl , refl) = refl
ts-img⊆ d (_ , output l′ d′ N2N_TxSubmission)    a (_ , refl , refl) = refl
ts-img⊆ d (_ , done   l′ d′ N2N_TxSubmission)    a (_ , refl , refl) = refl
ts-img⊆ d (_ , apiTS  l′ d′ m)                a (_ , refl , refl) = refl
ts-img⊆ d (_ , input  l′ d′ N2N_ChainSync) a (_ , () , _)
ts-img⊆ d (_ , input  l′ d′ N2N_BlockFetch) a (_ , () , _)
ts-img⊆ d (_ , input  l′ d′ N2N_KeepAlive) a (_ , () , _)
ts-img⊆ d (_ , input  l′ d′ N2N_LeiosNotify) a (_ , () , _)
ts-img⊆ d (_ , input  l′ d′ N2N_LeiosFetch) a (_ , () , _)
ts-img⊆ d (_ , output l′ d′ N2N_ChainSync) a (_ , () , _)
ts-img⊆ d (_ , output l′ d′ N2N_BlockFetch) a (_ , () , _)
ts-img⊆ d (_ , output l′ d′ N2N_KeepAlive) a (_ , () , _)
ts-img⊆ d (_ , output l′ d′ N2N_LeiosNotify) a (_ , () , _)
ts-img⊆ d (_ , output l′ d′ N2N_LeiosFetch) a (_ , () , _)
ts-img⊆ d (_ , done   l′ d′ N2N_ChainSync) a (_ , () , _)
ts-img⊆ d (_ , done   l′ d′ N2N_BlockFetch) a (_ , () , _)
ts-img⊆ d (_ , done   l′ d′ N2N_KeepAlive) a (_ , () , _)
ts-img⊆ d (_ , done   l′ d′ N2N_LeiosNotify) a (_ , () , _)
ts-img⊆ d (_ , done   l′ d′ N2N_LeiosFetch) a (_ , () , _)
ts-img⊆ d (_ , sndmsg l′ d′ i)                a (_ , () , _)
ts-img⊆ d (_ , rcvmsg l′ d′ i)                a (_ , () , _)
ts-img⊆ d (_ , tx     l′ d′ i)                a (_ , () , _)
ts-img⊆ d (_ , sndack l′ d′ i)                a (_ , () , _)
ts-img⊆ d (_ , rcvack l′ d′ i)                a (_ , () , _)
ts-img⊆ d (_ , ack    l′ d′ i)                a (_ , () , _)
ts-img⊆ d (_ , apiCS l′ d′ m)                a (_ , () , _)
ts-img⊆ d (_ , apiKA l′ d′ m)                a (_ , () , _)
ts-img⊆ d (_ , apiBF l′ d′ m)                a (_ , () , _)
ts-img⊆ d (_ , apiLN l′ d′ m)                a (_ , () , _)
ts-img⊆ d (_ , apiLF l′ d′ m)                a (_ , () , _)
ts-img⊆ d (_ , break  l′)                     a (_ , () , _)

-- TS SERVER source peer confines its offers to `srcAlphaTS lo`.
tsServerSrc-OO : (l : Link) → SrcTS.OffersOnly (srcAlphaTS lo) (TS.TSserverStClient l lo)
tsServerSrc-OO F.zero = SrcTS.OffersOnly-iter {k = TS.serverStep F.zero lo} {a = TS.stInit} step
  where
  step : ∀ q → SrcTS.OffersOnly (srcAlphaTS lo) (TS.serverStep F.zero lo q)
  step TS.stInit = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    -- recv MsgTSInit: fires only on (F.zero , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSInit)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stIdle = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.apiTSev _ _ sendTSReplyTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    -- api sendTSRequestTxIdsBlocking: fires only on (F.zero , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxIdsBlocking) (a , r) refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxIdsBlocking) (a , r) ()
    -- api sendTSRequestTxIdsPipelined: fires only on (F.zero , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxIdsPipelined) (a , r) refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxIdsPipelined) (a , r) ()
    -- api sendTSRequestTxsPipelined: fires only on (F.zero , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxsPipelined) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxIds: fires only on (F.zero , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    -- recv MsgTSDone: fires only on (F.zero , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSDone)) refl =
      refl , SrcTS.OffersOnly-Prefix₀ (λ _ → refl) SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsNonBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxIds: fires only on (F.zero , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxs = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxs: fires only on (F.zero , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stDone = SrcTS.OffersOnly-Ret
tsServerSrc-OO (F.suc F.zero) = SrcTS.OffersOnly-iter {k = TS.serverStep (F.suc F.zero) lo} {a = TS.stInit} step
  where
  step : ∀ q → SrcTS.OffersOnly (srcAlphaTS lo) (TS.serverStep (F.suc F.zero) lo q)
  step TS.stInit = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    -- recv MsgTSInit: fires only on ((F.suc F.zero) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSInit)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stIdle = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.apiTSev _ _ sendTSReplyTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    -- api sendTSRequestTxIdsBlocking: fires only on ((F.suc F.zero) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxIdsBlocking) (a , r) refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxIdsBlocking) (a , r) ()
    -- api sendTSRequestTxIdsPipelined: fires only on ((F.suc F.zero) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxIdsPipelined) (a , r) refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxIdsPipelined) (a , r) ()
    -- api sendTSRequestTxsPipelined: fires only on ((F.suc F.zero) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxsPipelined) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxIds: fires only on ((F.suc F.zero) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    -- recv MsgTSDone: fires only on ((F.suc F.zero) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSDone)) refl =
      refl , SrcTS.OffersOnly-Prefix₀ (λ _ → refl) SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsNonBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxIds: fires only on ((F.suc F.zero) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxs = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxs: fires only on ((F.suc F.zero) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stDone = SrcTS.OffersOnly-Ret
tsServerSrc-OO (F.suc (F.suc F.zero)) = SrcTS.OffersOnly-iter {k = TS.serverStep (F.suc (F.suc F.zero)) lo} {a = TS.stInit} step
  where
  step : ∀ q → SrcTS.OffersOnly (srcAlphaTS lo) (TS.serverStep (F.suc (F.suc F.zero)) lo q)
  step TS.stInit = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    -- recv MsgTSInit: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSInit)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stIdle = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.apiTSev _ _ sendTSReplyTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    -- api sendTSRequestTxIdsBlocking: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxIdsBlocking) (a , r) refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxIdsBlocking) (a , r) ()
    -- api sendTSRequestTxIdsPipelined: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxIdsPipelined) (a , r) refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxIdsPipelined) (a , r) ()
    -- api sendTSRequestTxsPipelined: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxsPipelined) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxIds: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    -- recv MsgTSDone: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSDone)) refl =
      refl , SrcTS.OffersOnly-Prefix₀ (λ _ → refl) SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsNonBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxIds: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxs = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxs: fires only on ((F.suc (F.suc F.zero)) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stDone = SrcTS.OffersOnly-Ret
tsServerSrc-OO (F.suc (F.suc (F.suc F.zero))) = SrcTS.OffersOnly-iter {k = TS.serverStep (F.suc (F.suc (F.suc F.zero))) lo} {a = TS.stInit} step
  where
  step : ∀ q → SrcTS.OffersOnly (srcAlphaTS lo) (TS.serverStep (F.suc (F.suc (F.suc F.zero))) lo q)
  step TS.stInit = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    -- recv MsgTSInit: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSInit)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSInit)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stIdle = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.apiTSev _ _ sendTSReplyTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    -- api sendTSRequestTxIdsBlocking: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxIdsBlocking) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxIdsBlocking) (a , r) refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxIdsBlocking) (a , r) ()
    -- api sendTSRequestTxIdsPipelined: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxIdsPipelined) (a , r) ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxIdsPipelined) (a , r) refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxIdsPipelined) (a , r) ()
    -- api sendTSRequestTxsPipelined: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , TS.apiTSev F.zero lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSRequestTxsPipelined) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSRequestTxsPipelined) a ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxIds: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    -- recv MsgTSDone: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSDone)) refl =
      refl , SrcTS.OffersOnly-Prefix₀ (λ _ → refl) SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSDone)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsNonBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxIds: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxs = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS lo) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq = case eq of λ ()
    -- recv MsgTSReplyTxs: fires only on ((F.suc (F.suc (F.suc F.zero))) , lo)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) refl =
      refl , SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stDone = SrcTS.OffersOnly-Ret

-- TS SERVER impl peer confines to its (TxSubmission, lo) slot (transport + mono)
tsServer-OO : (l : Link) → OffersOnly (peerAlpha N2N_TxSubmission lo) (TSserverA l lo)
tsServer-OO l = OffersOnly-mono (ts-img⊆ lo) (RenTS-OO.ren-OffersOnly (tsServerSrc-OO l))

-- TS CLIENT source peer confines its offers to `srcAlphaTS hi`.
tsClientSrc-OO : (l : Link) → SrcTS.OffersOnly (srcAlphaTS hi) (TS.TSclientStClient l hi)
tsClientSrc-OO F.zero = SrcTS.OffersOnly-iter {k = TS.clientStep F.zero hi} {a = TS.stInit} step
  where
  step : ∀ q → SrcTS.OffersOnly (srcAlphaTS hi) (TS.clientStep F.zero hi q)
  step TS.stInit = SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
  step TS.stIdle = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    -- recv MsgTSRequestTxIds_B: fires only on (F.zero , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    -- recv MsgTSRequestTxIds_N: fires only on (F.zero , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    -- recv MsgTSRequestTxs: fires only on (F.zero , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-ListTxid ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    -- api sendTSReplyTxIds: fires only on (F.zero , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxIds) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    -- api sendTSDone: fires only on (F.zero , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSDone) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSDone) a refl =
      refl , SrcTS.OffersOnly-Output refl (SrcTS.OffersOnly-Prefix₀ (λ _ → refl) SrcTS.OffersOnly-Ret)
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSDone) a ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsNonBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    -- api sendTSReplyTxIds: fires only on (F.zero , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxIds) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxs = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    mc (_ , TS.apiTSev _ _ sendTSReplyTxIds) a eq = case eq of λ ()
    -- api sendTSReplyTxs: fires only on (F.zero , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxs) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stDone = SrcTS.OffersOnly-Ret
tsClientSrc-OO (F.suc F.zero) = SrcTS.OffersOnly-iter {k = TS.clientStep (F.suc F.zero) hi} {a = TS.stInit} step
  where
  step : ∀ q → SrcTS.OffersOnly (srcAlphaTS hi) (TS.clientStep (F.suc F.zero) hi q)
  step TS.stInit = SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
  step TS.stIdle = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    -- recv MsgTSRequestTxIds_B: fires only on ((F.suc F.zero) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    -- recv MsgTSRequestTxIds_N: fires only on ((F.suc F.zero) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    -- recv MsgTSRequestTxs: fires only on ((F.suc F.zero) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-ListTxid ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    -- api sendTSReplyTxIds: fires only on ((F.suc F.zero) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxIds) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    -- api sendTSDone: fires only on ((F.suc F.zero) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSDone) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSDone) a refl =
      refl , SrcTS.OffersOnly-Output refl (SrcTS.OffersOnly-Prefix₀ (λ _ → refl) SrcTS.OffersOnly-Ret)
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSDone) a ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsNonBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    -- api sendTSReplyTxIds: fires only on ((F.suc F.zero) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxIds) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxs = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    mc (_ , TS.apiTSev _ _ sendTSReplyTxIds) a eq = case eq of λ ()
    -- api sendTSReplyTxs: fires only on ((F.suc F.zero) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxs) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stDone = SrcTS.OffersOnly-Ret
tsClientSrc-OO (F.suc (F.suc F.zero)) = SrcTS.OffersOnly-iter {k = TS.clientStep (F.suc (F.suc F.zero)) hi} {a = TS.stInit} step
  where
  step : ∀ q → SrcTS.OffersOnly (srcAlphaTS hi) (TS.clientStep (F.suc (F.suc F.zero)) hi q)
  step TS.stInit = SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
  step TS.stIdle = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    -- recv MsgTSRequestTxIds_B: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    -- recv MsgTSRequestTxIds_N: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    -- recv MsgTSRequestTxs: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-ListTxid ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    -- api sendTSReplyTxIds: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxIds) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    -- api sendTSDone: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSDone) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSDone) a refl =
      refl , SrcTS.OffersOnly-Output refl (SrcTS.OffersOnly-Prefix₀ (λ _ → refl) SrcTS.OffersOnly-Ret)
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSDone) a ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsNonBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    -- api sendTSReplyTxIds: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxIds) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxs = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    mc (_ , TS.apiTSev _ _ sendTSReplyTxIds) a eq = case eq of λ ()
    -- api sendTSReplyTxs: fires only on ((F.suc (F.suc F.zero)) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxs) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stDone = SrcTS.OffersOnly-Ret
tsClientSrc-OO (F.suc (F.suc (F.suc F.zero))) = SrcTS.OffersOnly-iter {k = TS.clientStep (F.suc (F.suc (F.suc F.zero))) hi} {a = TS.stInit} step
  where
  step : ∀ q → SrcTS.OffersOnly (srcAlphaTS hi) (TS.clientStep (F.suc (F.suc (F.suc F.zero))) hi q)
  step TS.stInit = SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
  step TS.stIdle = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSInit)) eq = case eq of λ ()
    -- recv MsgTSRequestTxIds_B: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking _ _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ refl SrcTS.OffersOnly-Ret
    -- recv MsgTSRequestTxIds_N: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking _ _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq = case eq of λ ()
    -- recv MsgTSRequestTxs: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , TS.receiveTS F.zero lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS F.zero hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc F.zero) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc F.zero)) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) lo) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
    mc (_ , TS.receiveTS (F.suc (F.suc (F.suc F.zero))) hi) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) refl =
      refl , SrcTS.OffersOnly-Output ⦃ TS.DecEq-ListTxid ⦄ refl SrcTS.OffersOnly-Ret
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , txSubmission (MsgTSDone)) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , keepAlive _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , blockFetch _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , chainSync _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosNotify _) eq = case eq of λ ()
    mc (_ , TS.receiveTS l′ d′) (_ , _ , _ , leiosFetch _) eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ _)   a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    -- api sendTSReplyTxIds: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxIds) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    -- api sendTSDone: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSDone) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSDone) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSDone) a refl =
      refl , SrcTS.OffersOnly-Output refl (SrcTS.OffersOnly-Prefix₀ (λ _ → refl) SrcTS.OffersOnly-Ret)
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxIdsNonBlocking = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    -- api sendTSReplyTxIds: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxIds) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxIds) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev _ _ sendTSReplyTxs) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stTxs = SrcTS.OffersOnly-pchoice mc
    where
    mc : SrcTS.MenuConf (srcAlphaTS hi) _
    mc (_ , TS.apiTSev _ _ sendTSReplyTxIds) a eq = case eq of λ ()
    -- api sendTSReplyTxs: fires only on ((F.suc (F.suc (F.suc F.zero))) , hi)
    mc (_ , TS.apiTSev F.zero lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev F.zero hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc F.zero) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc F.zero)) hi sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) lo sendTSReplyTxs) a ()
    mc (_ , TS.apiTSev (F.suc (F.suc (F.suc F.zero))) hi sendTSReplyTxs) a refl =
      refl , SrcTS.OffersOnly-Output refl SrcTS.OffersOnly-Ret
    mc (_ , TS.apiTSev _ _ sendTSDone) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsBlocking) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxIdsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ sendTSRequestTxsPipelined) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxIds) a eq = case eq of λ ()
    mc (_ , TS.apiTSev _ _ recvTSRequestTxs) a eq = case eq of λ ()
    mc (_ , TS.sendTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.receiveTS _ _)    a eq = case eq of λ ()
    mc (_ , TS.doneTS _ _)    a eq = case eq of λ ()
  step TS.stDone = SrcTS.OffersOnly-Ret

-- TS CLIENT impl peer confines to its (TxSubmission, hi) slot (transport + mono)
tsClient-OO : (l : Link) → OffersOnly (peerAlpha N2N_TxSubmission hi) (TSclientA l hi)
tsClient-OO l = OffersOnly-mono (ts-img⊆ hi) (RenTS-OO.ren-OffersOnly (tsClientSrc-OO l))


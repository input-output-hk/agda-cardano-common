{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE REGRESSION PINS FOR THE TWO LIVENESS FIXES
-- of `NodeLogicL` (spec 2026-10-02-leios-rb-dedup-and-closure-gate-design):
--
--   * RB DEDUP.  `storeStepL`'s `putEv` arm keeps `held` when the block is
--     already there (`dedup-held`) and still PREPENDS a fresh one
--     (`fresh-prepends`), so read-pointer indices over `reverse held` never shift.
--   * TX-CLOSURE OFFER GATE.  After the body offer, `bodyOfferBody` waits at the
--     mempool for the closure (`getTxEv … true`) instead of sending
--     `lnpSendBlockTxsOffer` at once (`gate-waits`, `empty-mempool-withholds`).
--
-- STORE-LOCAL / THREAD-LOCAL `viewV` facts at the shipped `leiosLParams`, where
-- `Block = Maybe Bool`, `EB = EBHash = Tx = TxHash = Bool` and
-- `ebTxs true = (true , tt) ∷ []`.  They are NOT facts about the composite.
-- It proves no property of the protocol.  Nothing imports it.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.DedupGateSanity where

import Data.Unit as U
open import Data.Bool using (true)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; ExtI; ret)
open import Cardano_network.Base using (hi)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; apiLP; lnpSendBlockOffer; lnpSendBlockTxsOffer)
open import Cardano_network.Data leiosLParams using (Payload)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.NodeLogicL as NLL

open Params leiosLParams using (Block)
open NL.Generic leiosLParams leiosLLine apiES using (StoreProc; putEv)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (storeStepL; bodyOfferBody; memStep; getAtEv; getBodyEv; getTxEv)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (viewV)

-- the node under test: node 0 of the line, home endpoint `(link 0 , lo)`
nA : Fin 3
nA = fzero

-- a block announcing the EB `true`, whose closure `ebTxs true` is non-empty
blk : Block
blk = just true

-- a second, distinct block (it announces nothing)
blk′ : Block
blk′ = nothing

-- one round of a pointer-carrying thread: a tree returning the next pointer
Round : Set₁
Round = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) ℕ

------------------------------------------------------------------------
-- FACT 1 — RB dedup (store side, prepend)
------------------------------------------------------------------------

-- DEPOSITING A HELD BLOCK IS A NO-OP: the `putEv` continuation returns `held` unchanged
dedup-held :
  Σ[ P ∈ StoreProc ]
    (viewV (PTree.force (storeStepL nA (blk ∷ []))) (Block , putEv nA) blk ≡ just P
     × PTree.force P ≡ ret (blk ∷ []))
dedup-held = _ , refl , refl

-- … AND A FRESH BLOCK IS STILL PREPENDED (not appended, as `insertU` would), so every
-- index over `reverse held` is stable
fresh-prepends :
  Σ[ P ∈ StoreProc ]
    (viewV (PTree.force (storeStepL nA (blk ∷ []))) (Block , putEv nA) blk′ ≡ just P
     × PTree.force P ≡ ret (blk′ ∷ blk ∷ []))
fresh-prepends = _ , refl , refl

------------------------------------------------------------------------
-- FACT 2 — the tx-closure offer gate
------------------------------------------------------------------------

-- AFTER THE BODY OFFER THE THREAD WAITS AT THE MEMPOOL, AND ONLY THERE: read `blk` at
-- pointer 0, read the body `true`, send the body offer; the next node does NOT offer
-- `lnpSendBlockTxsOffer` and DOES offer the closure read `getTxEv nA true`.  Once that read
-- is taken the closure offer goes out and the round returns the advanced pointer 1, so the
-- gate is passable and not a dead end.
gate-waits :
  Σ[ P₁ ∈ Round ] Σ[ P₂ ∈ Round ] Σ[ P₃ ∈ Round ] Σ[ P₄ ∈ Round ] Σ[ P₅ ∈ Round ]
    ( viewV (PTree.force (bodyOfferBody nA fzero hi 0)) (_ , getAtEv nA 0) blk ≡ just P₁
    × viewV (PTree.force P₁) (_ , getBodyEv nA true) true ≡ just P₂
    × viewV (PTree.force P₂) (_ , apiLP fzero hi lnpSendBlockOffer) ((true , U.tt) , U.tt)
        ≡ just P₃
    × viewV (PTree.force P₃) (_ , apiLP fzero hi lnpSendBlockTxsOffer) (true , U.tt)
        ≡ nothing
    × viewV (PTree.force P₃) (_ , getTxEv nA true) true ≡ just P₄
    × viewV (PTree.force P₄) (_ , apiLP fzero hi lnpSendBlockTxsOffer) (true , U.tt)
        ≡ just P₅
    × PTree.force P₅ ≡ ret 1 )
gate-waits = _ , _ , _ , _ , _ , refl , refl , refl , refl , refl , refl , refl

-- … AND AN EMPTY MEMPOOL WITHHOLDS THAT READ: the mempool offers `getTxEv nA true` only
-- for a transaction it holds, so from `[]` the gate stays shut
empty-mempool-withholds :
  viewV (PTree.force (memStep nA [])) (_ , getTxEv nA true) true ≡ nothing
empty-mempool-withholds = refl

{-# OPTIONS --guardedness #-}

-- A local successful tx-serving run against populated stores, without a network
-- or LeiosFetchP peer. Two offsets read two different held transactions; the
-- complete reply is followed by the next round's request. No full-network
-- reachability or delivery-liveness claim is made.
module Cardano_network.Parametric.Leios.ServeOkSanity where

import Data.Unit as U
open import Data.Unit.Polymorphic using (tt; ⊤)
open import Level using (0ℓ)
open import Data.Bool using (true; false)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (lo; hi)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine)
open import Cardano_network.Net leiosLParams
  using (Net_Api; Net_Api-≟; apiLP; lfpReqBlockTxsRequest; lfpSendBlockTxs)
open import Cardano_network.Data leiosLParams using (Payload)
open import Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import Cardano_network.Parametric.Node leiosLParams leiosLLine apiES using (Proc)
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.LeiosParams as LP
open NL.Generic leiosLParams leiosLLine apiES using (storeES)

-- Enlarge the shipped body's table to exercise every offset of two transactions.
lpHeld : LP.LeiosParams leiosLParams
lpHeld = record leiosLP { ebTxs = λ _ → (true , U.tt) ∷ (false , U.tt) ∷ [] }

-- Use the actual serving thread and stores with that two-entry table.
open NLL.Generic leiosLParams lpHeld leiosLLine apiES (λ n → n)
  using (ebTxsServeLoop; bodyStore; mempool; getBodyEv; getTxEv)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (_∥⇘_⇙_; _⦀_)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-ev; ⟹-τ)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-soloL; Par-soloR; Par-sync; Par-τ-L; Par-τ-R)

-- Node zero's home endpoint is link zero, lo.
nA : Fin 3
nA = fzero

-- Request every offset, rather than a hand-picked subset of the table.
all-offsets : LP.allOffsets leiosLParams lpHeld true ≡ 0 ∷ 1 ∷ []
all-offsets = refl

-- The request carries the held EB's hash and the complete bitmap.
request : Event√ (⊤ {0ℓ})
request = evl (evLabel _ (apiLP fzero hi lfpReqBlockTxsRequest)
  ((true , U.tt) , LP.allOffsets leiosLParams lpHeld true))

-- The expected reply contains both transactions in offset order.
reply : Event√ (⊤ {0ℓ})
reply = evl (evLabel _ (apiLP fzero hi lfpSendBlockTxs)
  ((true , U.tt) , (0 , true) ∷ (1 , false) ∷ []))

-- Start the actual loop with the body and both transactions already held.
initial : Proc
initial = ebTxsServeLoop nA (fzero , lo) ∥⇘ storeES ⇙
  (bodyStore nA (true ∷ []) ⦀ mempool nA (true ∷ false ∷ []))

-- The request is a solo API step of the serving loop.
requested : Σ[ P ∈ Proc ] (initial ─[ ev request ]─► P)
requested = _ , Par-soloL storeES _ _ _ (λ ()) (sVis refl refl) refl

-- The held body is read by rendezvous with the body store.
body-read : Σ[ P ∈ Proc ] (proj₁ requested ─[
  ev (evl (evLabel _ (getBodyEv nA true) true)) ]─► P)
body-read = _ , Par-sync storeES _ _ _ tt (sVis refl refl)
  (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)

-- Offset zero obtains the first transaction from the populated mempool.
tx-zero : Σ[ P ∈ Proc ] (proj₁ body-read ─[
  ev (evl (evLabel _ (getTxEv nA true) true)) ]─► P)
tx-zero = _ , Par-sync storeES _ _ _ tt (sVis refl refl)
  (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)

-- The mempool loops back after its read, preserving both held transactions.
mem-reset : Σ[ P ∈ Proc ] (proj₁ tx-zero ─[ τ ]─► P)
mem-reset = _ , Par-τ-R storeES _ _ _ (Par-τ-R _ _ _ _ (sSil refl))

-- Offset one obtains the other transaction; no negative read or Stop is taken.
tx-one : Σ[ P ∈ Proc ] (proj₁ mem-reset ─[
  ev (evl (evLabel _ (getTxEv nA false) false)) ]─► P)
tx-one = _ , Par-sync storeES _ _ _ tt (sVis refl refl)
  (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)

-- Only after both reads does the thread output the complete two-entry reply.
replied : Σ[ P ∈ Proc ] (proj₁ tx-one ─[ ev reply ]─► P)
replied = _ , Par-soloL storeES _ _ _ (λ ()) (sVis refl refl) refl

-- The successful round returns through the guarded loop-back, rather than Stop.
round-reset : Σ[ P ∈ Proc ] (proj₁ replied ─[ τ ]─► P)
round-reset = _ , Par-τ-L storeES _ _ _ (sSil refl)

-- The next round really accepts another request in the same composition.
next-request : Σ[ P ∈ Proc ] (proj₁ round-reset ─[ ev request ]─► P)
next-request = _ , Par-soloL storeES _ _ _ (λ ()) (sVis refl refl) refl

-- Assemble the finite composed trace, including its successful loop continuation.
serve-ok : initial ⟹⟨ request
  ∷ evl (evLabel _ (getBodyEv nA true) true)
  ∷ evl (evLabel _ (getTxEv nA true) true)
  ∷ evl (evLabel _ (getTxEv nA false) false)
  ∷ reply ∷ request ∷ [] ⟩ proj₁ next-request
serve-ok = ⟹-ev (Data.Product.proj₂ requested)
  (⟹-ev (Data.Product.proj₂ body-read)
  (⟹-ev (Data.Product.proj₂ tx-zero)
  (⟹-τ (Data.Product.proj₂ mem-reset)
  (⟹-ev (Data.Product.proj₂ tx-one)
  (⟹-ev (Data.Product.proj₂ replied)
  (⟹-τ (Data.Product.proj₂ round-reset)
  (⟹-ev (Data.Product.proj₂ next-request) ⟹-refl)))))))

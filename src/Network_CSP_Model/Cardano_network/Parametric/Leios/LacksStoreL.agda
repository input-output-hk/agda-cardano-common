{-# OPTIONS --guardedness #-}

-- Shared inversions and trace facts for the state-preserving negative store menus.
module Cardano_network.Parametric.Leios.LacksStoreL where

open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (map)
open import Data.Maybe using (nothing; just)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Maybe.Properties using (just-injective)
import Data.Unit as U
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology)
import Cardano_network.Parametric.Leios.LeiosParams as LP
import Cardano_network.Parametric.Leios.NodeLogicL as NL
import Cardano_network.Net as N
import Cardano_network.Data as D
import CSP.Operators as O

-- The facts use the same node, store, and alphabet parameters as the logic.
module Generic (p : Params) (lp : LP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (vo : Topology.Node t → Params.VoterId p) where
  open Params p using (EBHash; TxHash; ebHash; txHash; decEBHash; decTxHash)
  open N p using (Net_Api; Net_Api-≟)
  open D p using (Payload)
  open NL.Generic p lp t apiES vo
  open O (Net_Api-≟ {Payload}) using (Ret)
  open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
  open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (AllT-pchoice; Post-pchoice)

  -- A negative body step identifies its channel and returns the unchanged body list.
  body-inv : ∀ n bs {x M} → lacksBodies n bs ─[ ev (evl x) ]─► M
           → Σ[ h ∈ EBHash ] (x ≡ evLabel U.⊤ (lacksBodyEv n h) U.tt × M ≡ Ret bs)
  body-inv n bs (sVis {at = at} refl br) with lacksBodyKey n at
  ... | nothing = case br of λ ()
  ... | just (h , refl) with memberOf h (map ebHash bs)
  ...   | true = case br of λ ()
  ...   | false with just-injective br
  ...     | refl = h , refl , refl

  -- A negative transaction step identifies its channel and returns the unchanged mempool.
  tx-inv : ∀ n ts {x M} → lacksTxs n ts ─[ ev (evl x) ]─► M
         → Σ[ h ∈ TxHash ] (x ≡ evLabel U.⊤ (lacksTxEv n h) U.tt × M ≡ Ret ts)
  tx-inv n ts (sVis {at = at} refl br) with lacksTxKey n at
  ... | nothing = case br of λ ()
  ... | just (h , refl) with memberOf h (map txHash ts)
  ...   | true = case br of λ ()
  ...   | false with just-injective br
  ...     | refl = h , refl , refl

  -- Admitting every negative body label admits every trace of its menu.
  body-All : ∀ {P : Event → Set} n bs
           → (∀ h → P (evLabel U.⊤ (lacksBodyEv n h) U.tt)) → AllT P (lacksBodies n bs)
  body-All {P} n bs p = AllT-pchoice (λ st → go st (body-inv n bs st))
    where
    -- The inversion reduces the successor obligation to a return.
    go : ∀ {x M} → lacksBodies n bs ─[ ev (evl x) ]─► M
       → Σ[ h ∈ EBHash ] (x ≡ evLabel U.⊤ (lacksBodyEv n h) U.tt × M ≡ Ret bs)
       → P x × AllT P M
    go _ (h , refl , refl) = p h , AllT-Ret

  -- Admitting every negative transaction label admits every trace of its menu.
  tx-All : ∀ {P : Event → Set} n ts
         → (∀ h → P (evLabel U.⊤ (lacksTxEv n h) U.tt)) → AllT P (lacksTxs n ts)
  tx-All {P} n ts p = AllT-pchoice (λ st → go st (tx-inv n ts st))
    where
    -- The inversion reduces the successor obligation to a return.
    go : ∀ {x M} → lacksTxs n ts ─[ ev (evl x) ]─► M
       → Σ[ h ∈ TxHash ] (x ≡ evLabel U.⊤ (lacksTxEv n h) U.tt × M ≡ Ret ts)
       → P x × AllT P M
    go _ (h , refl , refl) = p h , AllT-Ret

  -- Every completed negative transaction read preserves any invariant of the state.
  tx-Post : ∀ {Q : Mem → Set} n ts → Q ts → Post (λ _ ts′ → Q ts′) (lacksTxs n ts)
  tx-Post {Q} n ts q = Post-pchoice (λ st → go st (tx-inv n ts st))
    where
    -- The returned state is propositionally the initial state.
    go : ∀ {x M} → lacksTxs n ts ─[ ev (evl x) ]─► M
       → Σ[ h ∈ TxHash ] (x ≡ evLabel U.⊤ (lacksTxEv n h) U.tt × M ≡ Ret ts)
       → Post (λ _ ts′ → Q ts′) M
    go _ (_ , refl , refl) = Post-Ret q

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Sanity checks (reduction / refl-style) for the `Network` process.
--
-- We instantiate the abstract parameters at the smallest non-trivial
-- scenario: every protocol has exactly one connection (`numConns ≡ 1`),
-- the opaque data domains are `⊤`, and the forwarded payload is `Data = ⊤`.
-- Then we observe `force Network` directly and read its visible-offer map:
--
--   * the external `input` channel IS offered initially, and
--   * the internal channels (`sndmsg`, `tx`, …) are hidden ⇒ offer nothing.
--
-- Each check is proved by `refl`, so they double as a proof that the whole
-- `Par⊤ … ∖ chanSet …` stack actually reduces (is productive at the head).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Nat using (ℕ)
open import Data.Fin using (zero)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Bool using (true)
open import Data.Product using (_,_; proj₁)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; NodeKind; react; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
  using (IDs; N2N_KeepAlive)

module CSP.Examples.Cardano_network.NetworkSanity where
open PTree

------------------------------------------------------------------------
-- A concrete parameter bundle: one connection per protocol, ⊤ domains.
------------------------------------------------------------------------

instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

p : Params
p = record
  { Cookie = ⊤ ; Block = ⊤ ; Txid = ⊤ ; LSlot = ⊤
  ; VoterId = ⊤ ; LFBitmap = ⊤ ; VoteBlob = ⊤
  ; numConns = λ _ → 1
  ; decCookie  = decEq⊤ ; decBlock    = decEq⊤ ; decTxid    = decEq⊤
  ; decLSlot   = decEq⊤ ; decVoterId  = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤ }

open import CSP.Examples.Cardano_network.Net p
  using (Net; Conn; input; sndmsg; tx)
open import CSP.Examples.Cardano_network.Network p ⊤

------------------------------------------------------------------------
-- Read the visible-offer continuation out of a node.
------------------------------------------------------------------------

NetR : Set
NetR = Poly.⊤ {0ℓ}

visCont : NodeKind (Net ⊤) (ExtI (Net ⊤)) NetR
        → (at : AnyTypes (Net ⊤)) → proj₁ at → Maybe (PTree (Net ⊤) (ExtI (Net ⊤)) NetR)
visCont (react v _) = v
visCont _           = λ _ _ → nothing

-- the single connection of the keep-alive protocol in this scenario
c0 : Conn N2N_KeepAlive
c0 = zero

------------------------------------------------------------------------
-- Checks.
------------------------------------------------------------------------

-- `input` is the external interface ⇒ offered in the initial state.
offers-input : is-just (visCont (force Network) (⊤ , input N2N_KeepAlive c0) tt) ≡ true
offers-input = refl

-- `sndmsg` is hidden by the TxSide hide ⇒ no top-level offer.
hidden-sndmsg : visCont (force Network) (⊤ , sndmsg N2N_KeepAlive c0) tt ≡ nothing
hidden-sndmsg = refl

-- `tx` is hidden by the outermost Network hide ⇒ no top-level offer.
hidden-tx : visCont (force Network) (⊤ , tx N2N_KeepAlive c0) tt ≡ nothing
hidden-tx = refl

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Sanity checks (reduction / refl-style) for the `Network` process.
--
-- We instantiate the abstract parameters at the smallest non-trivial
-- scenario: a single TCP link (`numLinks ≡ 1`) carrying exactly one
-- configured mini-protocol instance (`lo , N2N_KeepAlive`), the opaque
-- data domains are `⊤`, and the forwarded payload is `Data = ⊤`.
-- Then we observe `force Network` directly and read its visible-offer map:
--
--   * the external `input` channel IS offered initially, and
--   * the internal channels (`sndmsg`, `tx`, …) are hidden ⇒ offer nothing.
--
-- Each check is proved by `refl`, so they double as a proof that the whole
-- `Par⊤ … ∖ chanSet …` stack actually reduces (is productive at the head).
-- Note: the config-driven medium interleaves over `⦀Fin numLinks` and
-- `⦀⋆ (linkConfig l)`; at this single-instance `p1` that unfolds to one
-- live cell nested inside two `⦀ Skip` units (the `|||` unit for the
-- unused remaining links / instances) rather than the bare per-id cell
-- of the old `numConns`-indexed medium. The checks below are stated at
-- the level of the visible-offer *map*, so they hold by `refl` unchanged
-- in shape — only the underlying reduction is deeper.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fz)
open import Data.List using (_∷_; [])
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Bool using (true)
open import Data.Product using (_,_; proj₁)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; NodeKind; react; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
  using (IDs; Dir; lo; N2N_KeepAlive)

module CSP.Examples.Cardano_network.NetworkVerification.NetworkSanity where
open PTree

------------------------------------------------------------------------
-- A concrete parameter bundle: one connection per protocol, ⊤ domains.
------------------------------------------------------------------------

instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

import Data.Maybe as PMaybe

p : Params
p = record
  { Cookie = ⊤ ; Block = ⊤ ; Txid = ⊤ ; LSlot = ⊤
  ; VoterId = ⊤ ; LFBitmap = ⊤ ; VoteBlob = ⊤
  ; numLinks = 1
  ; linkConfig = λ _ → (lo , N2N_KeepAlive) ∷ []
  ; decCookie  = decEq⊤ ; decBlock    = decEq⊤ ; decTxid    = decEq⊤
  ; decLSlot   = decEq⊤ ; decVoterId  = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤
  ; Time = ⊤ ; Length = ⊤ ; time₀ = tt ; length₀ = tt
  ; decTime = decEq⊤ ; decLength = decEq⊤
  -- Leios EB domains, inert here: both ⊤, no RB ever announces an EB
  ; EB = ⊤ ; EBHash = ⊤ ; decEB = decEq⊤ ; decEBHash = decEq⊤
  ; ebHash = λ _ → tt ; announcedEB = λ _ → PMaybe.nothing }

open import CSP.Examples.Cardano_network.Net p
  using (Net; Link; input; sndmsg; tx)
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

-- the single link/direction of the keep-alive protocol in this scenario
l0 : Link
l0 = fz

d0 : Dir
d0 = lo

------------------------------------------------------------------------
-- Checks.
------------------------------------------------------------------------

-- `input` is the external interface ⇒ offered in the initial state.
offers-input : is-just (visCont (force Network) (⊤ , input l0 d0 N2N_KeepAlive) tt) ≡ true
offers-input = refl

-- `sndmsg` is hidden by the TxSide hide ⇒ no top-level offer.
hidden-sndmsg : visCont (force Network) (⊤ , sndmsg l0 d0 N2N_KeepAlive) tt ≡ nothing
hidden-sndmsg = refl

-- `tx` is hidden by the outermost Network hide ⇒ no top-level offer.
hidden-tx : visCont (force Network) (⊤ , tx l0 d0 N2N_KeepAlive) tt ≡ nothing
hidden-tx = refl

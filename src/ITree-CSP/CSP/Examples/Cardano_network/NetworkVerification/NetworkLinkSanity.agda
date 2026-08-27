{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Sanity: instantiate the POSTULATE-FREE all-singleton headline
-- NetworkLink ≈FD CopySpec at a two-link scenario (KeepAlive on link 0,
-- BlockFetch on link 1), Data = ⊤ — every link carries a single instance,
-- so `netLink≈FD-single` applies. The general `perLink` is now a PROVED
-- theorem (Milestone 2b), and the whole cone here carries zero axiom
-- declarations, modulo the certified König class in the FD layer, as
-- elsewhere.
------------------------------------------------------------------------

open import Data.Unit using (⊤; tt)
open import Data.List using (_∷_; [])
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
  using (Dir; IDs; lo; hi; N2N_KeepAlive; N2N_BlockFetch)

module CSP.Examples.Cardano_network.NetworkVerification.NetworkLinkSanity where

-- decidable equality on ⊤ (trivial, the only inhabitant)
instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

-- two links: KeepAlive initiated lo on link 0, BlockFetch hi on link 1
import Data.Maybe as PMaybe

p2 : Params
p2 = record
  { Cookie = ⊤ ; Block = ⊤ ; Txid = ⊤ ; LSlot = ⊤
  ; VoterId = ⊤ ; LFBitmap = ⊤ ; VoteBlob = ⊤
  ; Time = ⊤ ; Length = ⊤ ; time₀ = tt ; length₀ = tt
  ; numLinks = 2
  ; linkConfig = λ { fzero        → (lo , N2N_KeepAlive)  ∷ []
                   ; (fsuc fzero) → (hi , N2N_BlockFetch) ∷ [] }
  ; decCookie = decEq⊤ ; decBlock = decEq⊤ ; decTxid = decEq⊤
  ; decLSlot = decEq⊤ ; decVoterId = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤ ; decTime = decEq⊤ ; decLength = decEq⊤
  -- Leios EB domains, inert here: both ⊤, no RB ever announces an EB
  ; EB = ⊤ ; EBHash = ⊤ ; decEB = decEq⊤ ; decEBHash = decEq⊤
  ; ebHash = λ _ → tt ; announcedEB = λ _ → PMaybe.nothing }

open import CSP.Examples.Cardano_network.NetworkLink p2 ⊤ using (NetworkLink)
open import CSP.Examples.Cardano_network.Network p2 ⊤ using (CopySpec)
open import CSP.Examples.Cardano_network.NetworkVerification.NetworkLinkEquiv p2 ⊤
  using (netLink≈FD-single)
open import CSP.Examples.Cardano_network.Net p2 using (Net; Net-≟; Link)
open Params p2 using (linkConfig)
open import Process_Trees using (ExtI)
open import Semantics.FailuresDivergences {E = Net ⊤} {I = ExtI (Net ⊤)} using (_≈FD_)

-- both links are singleton-configured: exhibit the witness by a `Fin 2` split
wit : ∀ l → Σ[ c ∈ Dir × IDs ] linkConfig l ≡ c ∷ []
wit fzero        = (lo , N2N_KeepAlive)  , refl
wit (fsuc fzero) = (hi , N2N_BlockFetch) , refl

-- the POSTULATE-FREE all-singleton theorem at the concrete two-link instance
sanity : NetworkLink ≈FD CopySpec
sanity = netLink≈FD-single wit

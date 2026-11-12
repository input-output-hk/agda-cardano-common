{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the LEIOS PARAMETERS of the Linear-Leios node
-- logic: the vote-blob algebra (a vote names the RANKING BLOCK it endorses),
-- the certification oracle, the two endorser-block projections the node logic
-- needs, and the certificate attribute of a ranking block.
--
-- A SEPARATE RECORD, parametrised by `Params`, exactly as `ApiAlphabet` is:
-- no existing `Params` instance changes and no `Net` closure rebuild starts
-- from `Params`.  Certification from votes is NOT modelled — `certifies`
-- stands in for it and the logic only routes its verdict.
--
-- NO VALIDATION ORACLE: the prototype's votes carry no verdict (spec §1.2
-- decision 4), so `valid`/`blobValid` are gone and nothing validates.
-- `slotOf` MOVED OUT to `Params` (it is a Praos header attribute that
-- `Data`/`Net` need).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosParams (p : Params) where

import Cardano_network.Replay.LeiosFetchWire as Wire
open import Data.Bool using (Bool; true)
open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_; concat)
open import Data.List.Base using (length; upTo; take; drop)
open import Data.List.Properties using (length-drop; take++drop≡id)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; m∸n≤m)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Class.DecEq using (DecEq)
import Class.DecEq.Instances as DecEqI

open Params p using (Block; TxHash; Size; VoterId; VoteBlob; EB; EBHash; RbHash; LSlot)
open import Cardano_network.Data p using (TxBitmap)

-- the Leios EB body, an alias for the opaque Params `EB`
LeiosEb : Set
LeiosEb = EB

-- a Leios point: the hash of an EB with the slot of the RB that announced it
LeiosPoint : Set
LeiosPoint = EBHash × LSlot

instance
  -- the EB-store entry carrier and state
  DecEq-LeiosPoint : DecEq LeiosPoint
  DecEq-LeiosPoint = DecEqI.DecEq-×

-- the Leios-specific parameters over a given `Params`: the vote-blob algebra, the
-- certification oracle, the two EB projections only node logic uses, and the
-- certificate attribute of a ranking block
record LeiosParams : Set where
  field
    -- build a vote blob: a voter and the announcing RANKING BLOCK it names.  No slot, no
    -- EB hash and NO VERDICT — exactly the prototype's `LeiosVote`.
    mkVoteBlob   : VoterId → RbHash → VoteBlob
    -- the voter that cast a vote blob
    blobVoter    : VoteBlob → VoterId
    -- the ranking block a vote blob endorses
    blobRb       : VoteBlob → RbHash
    -- the projection laws: `mkVoteBlob` really does carry both components
    blobVoter-mk : ∀ v r → blobVoter (mkVoteBlob v r) ≡ v
    blobRb-mk    : ∀ v r → blobRb    (mkVoteBlob v r) ≡ r
    -- THE CERTIFICATION ORACLE: do these vote blobs certify this RANKING BLOCK?  No
    -- quorum, no committee and no weights are modelled; a weight sum over distinct
    -- voters is one admissible instantiation.
    certifies    : List VoteBlob → RbHash → Bool
    -- THE EB BODY TABLE, keyed by the EB's IDENTITY: `(ebHash , offset) ↦ (txHash , size)`,
    -- offset = list index.  A node looks up `ebTxs (ebHash eb)` for a body it holds and
    -- `ebTxs (proj₁ point)` for a point it was offered, which is why the key is the hash
    -- and not the `EB` value.
    -- see ADR 2026-09-21 (leios-tx-closure-and-object-identities)
    ebTxs        : EBHash → List (TxHash × Size)
  -- The decoder and node logic share the fixed upstream wire ceiling.
  maxTxs : ℕ
  maxTxs = Wire.maxTxs

  field
    -- the positive number of offsets requested in each transaction chunk
    chunk        : ℕ
    -- every chunk consumes at least one offset
    chunk-pos    : 1 ≤ chunk
    -- requests never exceed the accepted EB transaction count
    chunk≤maxTxs : chunk ≤ maxTxs
    -- the EB's byte size, the value `MsgLeiosBlockOffer` carries.  A FIELD, not a sum over
    -- `ebTxs`, because `Size` is opaque.  Only `bodyOfferLoop` computes it, which is why
    -- it lives here and not in `Params`.
    ebSize       : LeiosEb → Size
    -- the ranking block whose announced EB this block's BODY carries a certificate for,
    -- if any.  A cert-carrying RB travels by BlockFetch like any other RB.
    rbCert       : Block → Maybe RbHash

-- THE S3 PREMISE: the oracle never WITHDRAWS a certificate.  A hypothesis about the
-- oracle, not about the logic.  A COUNTING quorum is NOT admissible: `[a,a] ⊆ [a]` under
-- propositional `⊆`, so counting is not `⊆`-monotone (campaign ledger, Task 9).
CertifiesMono : LeiosParams → Set
CertifiesMono lp = ∀ {vs ws} → vs ⊆ ws → ∀ r →
  LeiosParams.certifies lp vs r ≡ true → LeiosParams.certifies lp ws r ≡ true

-- THE "ALL TRANSACTIONS" REQUEST: every offset of an EB body.  Derivable from `ebTxs`,
-- hence a definition and not a field (it replaced the old `allTxs` parameter).
allOffsets : LeiosParams → EBHash → TxBitmap
allOffsets lp h = upTo (length (LeiosParams.ebTxs lp h))

private
  -- Fuel bounds the number of chunks; c is one less than their positive size.
  chunksOfFuel : ∀ {ℓ : Level} {A : Set ℓ} → ℕ → ℕ → List A → List (List A)
  chunksOfFuel fuel c [] = []
  chunksOfFuel zero c (_ ∷ _) = []
  chunksOfFuel (suc fuel) c (x ∷ xs) =
    (x ∷ take c xs) ∷ chunksOfFuel fuel c (drop c xs)

  -- Enough fuel preserves the input by rejoining each take/drop partition.
  chunksOfFuel-concat : ∀ {ℓ : Level} {A : Set ℓ} (fuel c : ℕ) (xs : List A) →
    length xs ≤ fuel → concat (chunksOfFuel fuel c xs) ≡ xs
  chunksOfFuel-concat fuel c [] bound = refl
  chunksOfFuel-concat zero c (_ ∷ _) ()
  chunksOfFuel-concat (suc fuel) c (x ∷ xs) (s≤s bound) =
    cong (x ∷_) (trans
      (cong (take c xs ++_) (chunksOfFuel-concat fuel c (drop c xs)
        (≤-trans (≤-trans (≤-reflexive (length-drop c xs))
          (m∸n≤m (length xs) c)) bound)))
      (take++drop≡id c xs))

-- Split into positive-sized chunks with length xs fuel; zero size returns no chunks.
-- LeiosParams.chunk-pos excludes that total-function fallback for transaction requests.
chunksOf : ∀ {ℓ : Level} {A : Set ℓ} → ℕ → List A → List (List A)
chunksOf c [] = []
chunksOf zero (_ ∷ _) = []
chunksOf (suc c) (x ∷ xs) = chunksOfFuel (length (x ∷ xs)) c (x ∷ xs)

-- Concatenating chunks at any positive size recovers the original list in order.
chunksOf-concat : ∀ {ℓ : Level} {A : Set ℓ} {c : ℕ} {xs : List A} →
  1 ≤ c → concat (chunksOf c xs) ≡ xs
chunksOf-concat {xs = []} positive = refl
chunksOf-concat {c = suc c} {xs = x ∷ xs} (s≤s _) =
  chunksOfFuel-concat (length (x ∷ xs)) c (x ∷ xs) ≤-refl

-- Request every transaction offset in bounded chunks, with no request for an empty EB.
txChunks : LeiosParams → EBHash → List TxBitmap
txChunks lp h = chunksOf (LeiosParams.chunk lp) (allOffsets lp h)

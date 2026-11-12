{-# OPTIONS --safe #-}

-- Wire bitmap and constants pinned to ouroboros-consensus leios-prototype
-- e651152750388ccf20700eb28149751981a396f4 (e6511527).
-- Sources: Ouroboros/Consensus/Leios/Types.hs: maxTxsPerEb, cborIntBytesSize,
-- encodeLeiosEbItemSize and encodeLeiosEbMaxFramingSize give
-- maxTxs = (600000 - 5) div 35 = 17142. LeiosDemoOnlyTestFetch.hs:
-- maxBitmapEntries = (maxTxs + 63) div 64 = 268, and the BlockTxs/Block
-- limits are withMargin 500000 / withMargin 600000. The margin comes from
-- ouroboros-network Cardano/Network/NodeToNode.hs:328, addSafetyMargin x =
-- x + x div 10. Diffusion Network/NodeToNode.hs:2165 sets Fetch depth 150.
-- LeiosDemoLogic.hs:701 gives the most-significant-bit-first offset order.
module Cardano_network.Replay.LeiosFetchWire where

open import Data.Bool using (Bool; T; true; false; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; _++_; length; map; filter; tabulate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as Pairsₚ
open import Data.List.Relation.Unary.Linked using (Linked; linked?)
open import Data.List.Relation.Unary.Linked.Properties
  using (Linked⇒AllPairs; AllPairs⇒Linked)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _∸_; _/_; _%_; _≡ᵇ_;
  _<_; _≤_; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using
  (_<?_; m^n≢0; <-trans; <-≤-trans; ≤-trans;
   +-monoʳ-<; +-comm; *-monoʳ-≤; *-suc; m≤m+n)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable using (Dec; does; T?; yes; no)

-- Upstream maximum number of transactions in an EB.
maxTxs : ℕ
maxTxs = 17142

-- Ceiling of maxTxs / 64, as used by the bitmap decoder.
maxBitmapEntries : ℕ
maxBitmapEntries = 268

-- BlockTxs byte limit including the upstream ten percent margin.
txsCap : ℕ
txsCap = 550000

-- Block byte limit including the upstream ten percent margin.
ebCap : ℕ
ebCap = 660000

-- Default upstream number of pipelined Fetch requests.
fetchDepth : ℕ
fetchDepth = 150

-- Keep the wire shape so malformed bitmaps can also be represented.
Bitmap : Set
Bitmap = List (ℕ × ℕ)

private
  -- Check each index and nonzero Word64 independently of list order.
  entryᵇ : ℕ × ℕ → Bool
  entryᵇ (i , w) = (i <ᵇ maxBitmapEntries) ∧ (0 <ᵇ w) ∧
                    (w <ᵇ 18446744073709551616)

  -- Decide strict ordering of consecutive wire indices.
  indices? : (b : Bitmap) → Dec (Linked (λ x y → proj₁ x < proj₁ y) b)
  indices? = linked? (λ x y → proj₁ x <? proj₁ y)

-- Decoder conditions: bounded entry count, legal words/indices, strict order.
validᵇ : Bitmap → Bool
validᵇ b = ((length b ≤ᵇ maxBitmapEntries) ∧ all entryᵇ b) ∧ does (indices? b)

private
  -- Test bit 63-r of a word; the power of two is always a nonzero divisor.
  bitᵇ : ℕ → Fin 64 → Bool
  bitᵇ w r = ((_/_ w (2 ^ (63 ∸ toℕ r))
    {{m^n≢0 2 (63 ∸ toℕ r)}} % 2) ≡ᵇ 1)

  -- Reflect the bit test for the standard library's proof-preserving filter.
  bit? : (w : ℕ) (r : Fin 64) → Dec (T (bitᵇ w r))
  bit? w r = T? (bitᵇ w r)

  -- Translate an in-word position to its absolute transaction offset.
  position : ℕ → Fin 64 → ℕ
  position i r = 64 * i + toℕ r

  -- Enumerate positions 0..63, retaining precisely the set bits of this word.
  wordOffsets : ℕ → ℕ → List ℕ
  wordOffsets i w = map (position i) (filter (bit? w) (tabulate (λ r → r)))

-- Concatenate the per-word offsets in wire list order, including on invalid input.
offsets : Bitmap → List ℕ
offsets [] = []
offsets ((i , w) ∷ b) = wordOffsets i w ++ offsets b

-- The request count is exactly the number of enumerated offsets.
popcount : Bitmap → ℕ
popcount b = length (offsets b)

private
  -- Lift any property of all 64 positions to the selected offsets.
  word-all : ∀ {P : ℕ → Set} i w →
    (∀ r → P (position i r)) → All P (wordOffsets i w)
  word-all i w p = Allₚ.map⁺
    (Allₚ.filter⁺ (bit? w) (Allₚ.tabulate⁺ p))

  -- Every selected offset is below the start of the next word.
  word-upper : ∀ i w → All (_< 64 * suc i) (wordOffsets i w)
  word-upper i w = word-all i w (λ r →
    subst (position i r <_) (trans (+-comm (64 * i) 64) (sym (*-suc 64 i)))
      (+-monoʳ-< (64 * i) (toℕ<n r)))

  -- Filtering preserves the strict order of the in-word positions.
  word-sorted : ∀ i w → AllPairs _<_ (wordOffsets i w)
  word-sorted i w = Pairsₚ.map⁺ (Pairsₚ.filter⁺ (bit? w)
    (Pairsₚ.tabulate⁺-< (λ p → +-monoʳ-< (64 * i) p)))

  -- Offsets in strictly later words are greater than any offset in this word.
  later-above : ∀ {i x} b → All (λ e → i < proj₁ e) b →
    x < 64 * suc i → All (x <_) (offsets b)
  later-above [] [] x<end = []
  later-above ((j , w) ∷ b) (i<j ∷ later) x<end = Allₚ.++⁺
    (word-all j w (λ r → <-≤-trans x<end
      (≤-trans (*-monoʳ-≤ 64 i<j)
        (m≤m+n (64 * j) (toℕ r)))))
    (later-above b later x<end)

  -- Expand ordered word indices to ordered transaction offsets.
  expand-sorted : ∀ b → AllPairs (λ x y → proj₁ x < proj₁ y) b →
    AllPairs _<_ (offsets b)
  expand-sorted [] [] = []
  expand-sorted ((i , w) ∷ b) (later ∷ rest) = Pairsₚ.++⁺
    (word-sorted i w) (expand-sorted b rest)
    (Data.List.Relation.Unary.All.map (later-above b later) (word-upper i w))

  -- A true conjunction supplies evidence for its right-hand condition.
  ∧-right : ∀ {a b} → T (a ∧ b) → T b
  ∧-right {true} p = p
  ∧-right {false} ()

  -- Recover the ordering evidence reflected by the index decision.
  indices-sorted : ∀ b → T (does (indices? b)) →
    Linked (λ x y → proj₁ x < proj₁ y) b
  indices-sorted b p with indices? b
  ... | yes ordered = ordered
  ... | no _ = ⊥-elim p

-- A valid wire bitmap enumerates strictly ascending offsets.
offsets-sorted : ∀ b → T (validᵇ b) → Linked _<_ (offsets b)
offsets-sorted b valid = AllPairs⇒Linked (expand-sorted b
  (Linked⇒AllPairs <-trans (indices-sorted b (∧-right valid))))

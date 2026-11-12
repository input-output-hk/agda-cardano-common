{-# OPTIONS --safe #-}

module Cardano_network.Replay.LeiosFetchWords where

open import Cardano_network.Replay.LeiosFetchWire
  using (Bitmap; maxTxs; maxBitmapEntries; validᵇ; offsets; popcount; offsets-sorted)
open import Data.Bool.ListAction using (all)
open import Data.Bool using (Bool; T; true; false; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<)
open import Data.List using (List; []; _∷_; _++_; length; map; filter; tabulate; applyUpTo; upTo)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Properties as L
import Data.List.Membership.Propositional.Properties as M
import Data.List.Relation.Unary.All.Properties as A
import Data.List.Relation.Unary.AllPairs.Properties as P
open import Data.List.Relation.Unary.Linked using (linked?)
open import Data.List.Relation.Unary.Linked.Properties using (AllPairs⇒Linked; Linked⇒AllPairs)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _/_; _%_;
  _<_; _≤_; _<ᵇ_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Data.Nat.DivMod
open import Data.Nat.Divisibility using (divides-refl; ∣-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary.Decidable using (Dec; does; T?; yes; no)

-- Locate the wire word containing an offset.
index : ℕ → ℕ
index o = o / 64

-- Locate its MSB-first power of two within that word.
exponent : ℕ → ℕ
exponent o = 63 ∸ o % 64

-- Extend the first run when its index agrees, otherwise start a new run.
prepend : ℕ → Bitmap → Bitmap
prepend o [] = (index o , 2 ^ exponent o) ∷ []
prepend o ((i , w) ∷ b) with index o N.≟ i
... | yes _ = (i , 2 ^ exponent o + w) ∷ b
... | no _ = (index o , 2 ^ exponent o) ∷ (i , w) ∷ b

-- Traverse only the supplied offsets; each consecutive quotient run is one word.
toWords : List ℕ → Bitmap
toWords [] = []
toWords (o ∷ os) = prepend o (toWords os)

-- Bound every offset and require each next offset to be strictly greater.
canonicalFrom : ℕ → List ℕ → Bool
canonicalFrom lo [] = true
canonicalFrom lo (o ∷ os) = (lo ≤ᵇ o) ∧ (o <ᵇ maxTxs) ∧ canonicalFrom (suc o) os

-- Canonical model bitmaps are strictly ascending offsets below the wire cap.
canonical : List ℕ → Bool
canonical = canonicalFrom 0

-- The decoder permits every bit in each bounded Word64 entry.
decoderOffsets : ℕ
decoderOffsets = 64 * maxBitmapEntries

-- Decode strictly ascending offsets, including the final word's padding bits.
decodableFrom : ℕ → List ℕ → Bool
decodableFrom lo [] = true
decodableFrom lo (o ∷ os) = (lo ≤ᵇ o) ∧ (o <ᵇ decoderOffsets) ∧ decodableFrom (suc o) os

-- Server receive bitmaps use the decoder domain rather than the honest send cap.
decodable : List ℕ → Bool
decodable = decodableFrom 0

-- Reflect a successful decision using its computational Boolean projection.
dec-true : ∀ {P : Set} → (d : Dec P) → P → T (does d)
dec-true (yes _) p = tt
dec-true (no reject) p = ⊥-elim (reject p)

-- A conjunction supplies its left component.
∧-left : ∀ {a b} → T (a ∧ b) → T a
∧-left {true} p = tt
∧-left {false} ()

-- A conjunction supplies its right component.
∧-right : ∀ {a b} → T (a ∧ b) → T b
∧-right {true} p = p
∧-right {false} ()

-- Combine evidence for Boolean conjunction.
∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
∧-intro {true} p q = q
∧-intro {false} ()

-- Reflect the current canonical offset's lower bound.
canonical-lower : ∀ lo o os → T (canonicalFrom lo (o ∷ os)) → lo ≤ o
canonical-lower lo o os p = N.≤ᵇ⇒≤ lo o
  (∧-left {a = lo ≤ᵇ o} {b = (o <ᵇ maxTxs) ∧ canonicalFrom (suc o) os} p)

-- Reflect the current canonical offset's exclusive transaction bound.
canonical-bound : ∀ lo o os → T (canonicalFrom lo (o ∷ os)) → o < maxTxs
canonical-bound lo o os p = N.<ᵇ⇒< o maxTxs
  (∧-left {a = o <ᵇ maxTxs} {b = canonicalFrom (suc o) os}
    (∧-right {a = lo ≤ᵇ o} {b = (o <ᵇ maxTxs) ∧ canonicalFrom (suc o) os} p))

-- Remove the head of a canonical list, increasing the suffix's lower bound.
canonical-tail : ∀ lo o os → T (canonicalFrom lo (o ∷ os)) →
  T (canonicalFrom (suc o) os)
canonical-tail lo o os p =
  ∧-right {a = o <ᵇ maxTxs} {b = canonicalFrom (suc o) os}
    (∧-right {a = lo ≤ᵇ o} {b = (o <ᵇ maxTxs) ∧ canonicalFrom (suc o) os} p)

-- Reflect the current decodable offset's lower bound.
decodable-lower : ∀ lo o os → T (decodableFrom lo (o ∷ os)) → lo ≤ o
decodable-lower lo o os p = N.≤ᵇ⇒≤ lo o
  (∧-left {a = lo ≤ᵇ o} {b = (o <ᵇ decoderOffsets) ∧ decodableFrom (suc o) os} p)

-- Reflect the current decodable offset's exclusive transaction bound.
decodable-bound : ∀ lo o os → T (decodableFrom lo (o ∷ os)) → o < decoderOffsets
decodable-bound lo o os p = N.<ᵇ⇒< o decoderOffsets
  (∧-left {a = o <ᵇ decoderOffsets} {b = decodableFrom (suc o) os}
    (∧-right {a = lo ≤ᵇ o} {b = (o <ᵇ decoderOffsets) ∧ decodableFrom (suc o) os} p))

-- Remove the head of a decodable list, increasing the suffix's lower bound.
decodable-tail : ∀ lo o os → T (decodableFrom lo (o ∷ os)) →
  T (decodableFrom (suc o) os)
decodable-tail lo o os p =
  ∧-right {a = o <ᵇ decoderOffsets} {b = decodableFrom (suc o) os}
    (∧-right {a = lo ≤ᵇ o} {b = (o <ᵇ decoderOffsets) ∧ decodableFrom (suc o) os} p)

-- Raising the exclusive bound preserves every honest canonical suffix.
canonicalFrom-decodable : ∀ lo os → T (canonicalFrom lo os) → T (decodableFrom lo os)
canonicalFrom-decodable lo [] p = tt
canonicalFrom-decodable lo (o ∷ os) p =
  ∧-intro {a = lo ≤ᵇ o} {b = (o <ᵇ decoderOffsets) ∧ decodableFrom (suc o) os}
    (N.≤⇒≤ᵇ (canonical-lower lo o os p))
    (∧-intro {a = o <ᵇ decoderOffsets} {b = decodableFrom (suc o) os}
      (N.<⇒<ᵇ (N.<-≤-trans (canonical-bound lo o os p)
        (N.≤ᵇ⇒≤ maxTxs decoderOffsets tt)))
      (canonicalFrom-decodable (suc o) os (canonical-tail lo o os p)))

-- Honest client requests always pass server decoding.
canonical-decodable : ∀ {os} → T (canonical os) → T (decodable os)
canonical-decodable {os} = canonicalFrom-decodable 0 os

-- Read the wire's MSB-first bit predicate, definitionally equal to its test.
bitᵇ : ℕ → Fin 64 → Bool
bitᵇ w r = ((_/_ w (2 ^ (63 ∸ toℕ r)) {{N.m^n≢0 2 (63 ∸ toℕ r)}} % 2) ≡ᵇ 1)

-- Reflect the wire bit predicate for its proof-preserving list filter.
bit? : (w : ℕ) (r : Fin 64) → Dec (T (bitᵇ w r))
bit? w r = T? (bitᵇ w r)

-- One word's expanded offsets, with exactly the wire module's computation.
wordOffsets : ℕ → ℕ → List ℕ
wordOffsets i w = map (λ r → 64 * i + toℕ r)
  (filter (bit? w) (tabulate (λ r → r)))

-- A selected bit occurs in the expanded offsets of its word.
word-member⁺ : ∀ i w r → T (bitᵇ w r) → (64 * i + toℕ r) ∈ wordOffsets i w
word-member⁺ i w r p = M.∈-map⁺ (λ s → 64 * i + toℕ s)
  (M.∈-filter⁺ (bit? w) {xs = tabulate (λ r → r)}
    (M.∈-tabulate⁺ {f = λ r → r} r) p)

-- Recover a selected in-word position and its bit evidence.
word-member⁻ : ∀ i w {x} → x ∈ wordOffsets i w →
  ∃ λ r → x ≡ 64 * i + toℕ r × T (bitᵇ w r)
word-member⁻ i w p with M.∈-map⁻ (λ r → 64 * i + toℕ r)
  {xs = filter (bit? w) (tabulate (λ r → r))} p
... | r , member , eq = r , eq , proj₂ (M.∈-filter⁻ (bit? w) {xs = tabulate (λ r → r)} member)

-- The head of a strictly ascending list is a lower bound for its members.
head-minimum : ∀ {x xs y} → All (x <_) xs → y ∈ (x ∷ xs) → x ≤ y
head-minimum p (here refl) = N.≤-refl
head-minimum p (there q) = N.<⇒≤ (Data.List.Relation.Unary.All.lookup p q)

-- Remove a shared head from an inclusion between strictly ascending lists.
tails-subset : ∀ {x xs ys} → All (x <_) xs →
  (∀ {y} → y ∈ (x ∷ xs) → y ∈ (x ∷ ys)) →
  ∀ {y} → y ∈ xs → y ∈ ys
tails-subset ordered included member with included (there member)
... | here refl = ⊥-elim (N.<-irrefl refl
  (Data.List.Relation.Unary.All.lookup ordered member))
... | there tail = tail

-- Strictly ascending lists with the same members are propositionally equal.
sorted-ext : ∀ {xs ys} → AllPairs _<_ xs → AllPairs _<_ ys →
  (∀ {x} → x ∈ xs → x ∈ ys) → (∀ {x} → x ∈ ys → x ∈ xs) → xs ≡ ys
sorted-ext {[]} {[]} [] [] forward backward = refl
sorted-ext {[]} {y ∷ ys} [] ordered forward backward with backward (here refl)
... | ()
sorted-ext {x ∷ xs} {[]} ordered [] forward backward with forward (here refl)
... | ()
sorted-ext {x ∷ xs} {y ∷ ys} (xs> ∷ xs-sort) (ys> ∷ ys-sort) forward backward
  with N.≤-antisym (head-minimum xs> (backward (here refl)))
    (head-minimum ys> (forward (here refl)))
... | refl = cong (x ∷_) (sorted-ext xs-sort ys-sort
  (tails-subset xs> forward) (tails-subset ys> backward))

-- Read a bit by its exponent, keeping all arithmetic generic in the width.
readBit : ℕ → ℕ → ℕ
readBit w k = (_/_ w (2 ^ k) {{N.m^n≢0 2 k}}) % 2

abstract
  -- Powers of two are positive without evaluating their numeral representation.
  power-positive : ∀ k → 0 < 2 ^ k
  power-positive k = N.m^n>0 2 k

  -- Adding a top bit to a smaller tail fits within the next binary width.
  high-bound : ∀ k w → w < 2 ^ k → 2 ^ k + w < 2 ^ suc k
  high-bound k w p = subst (2 ^ k + w <_)
    (cong (2 ^ k +_) (sym (N.+-identityʳ (2 ^ k))))
    (N.+-monoʳ-< (2 ^ k) p)

  -- A higher power is an even multiple of every lower bit's divisor.
  power-even : ∀ e k → k < e → ∃ λ t → 2 ^ e ≡ (t * 2) * 2 ^ k
  power-even (suc e) zero p = 2 ^ e ,
    trans (N.*-comm 2 (2 ^ e)) (sym (N.*-identityʳ (2 ^ e * 2)))
  power-even (suc e) (suc k) (s≤s p) with power-even e k p
  ... | t , eq = t , trans (cong (2 *_) eq)
    (trans (sym (N.*-assoc 2 (t * 2) (2 ^ k)))
      (trans (cong (_* 2 ^ k) (N.*-comm 2 (t * 2)))
        (N.*-assoc (t * 2) 2 (2 ^ k))))

  -- Adding a higher bit preserves all lower bit tests, with no word expansion.
  read-low : ∀ e k w → k < e → readBit (2 ^ e + w) k ≡ readBit w k
  read-low e k w p with power-even e k p
  ... | t , eq rewrite eq
    | +-distrib-/-∣ˡ w {{N.m^n≢0 2 k}} (divides-refl (t * 2))
    | m*n/n≡m (t * 2) (2 ^ k) {{N.m^n≢0 2 k}}
    | N.+-comm (t * 2) (_/_ w (2 ^ k) {{N.m^n≢0 2 k}})
    | [m+kn]%n≡m%n (_/_ w (2 ^ k) {{N.m^n≢0 2 k}}) t 2 {{_}} = refl

  -- A tail smaller than the bit's divisor cannot set that bit.
  read-zero : ∀ k w → w < 2 ^ k → readBit w k ≡ 0
  read-zero k w p rewrite m<n⇒m/n≡0 {{N.m^n≢0 2 k}} p = refl

  -- The newly added top bit is set exactly once.
  read-high : ∀ k w → w < 2 ^ k → readBit (2 ^ k + w) k ≡ 1
  read-high k w p rewrite +-distrib-/-∣ˡ w {{N.m^n≢0 2 k}} ∣-refl
    | n/n≡1 (2 ^ k) {{N.m^n≢0 2 k}}
    | m<n⇒m/n≡0 {{N.m^n≢0 2 k}} p = refl

abstract
  -- A set bit of a bounded word must lie below its binary width.
  read-below : ∀ e k w → w < 2 ^ e → readBit w k ≡ 1 → k < e
  read-below e k w bound bit with k N.<? e
  ... | yes p = p
  ... | no p = ⊥-elim (N.0≢1+n (trans (sym (read-zero k w
    (N.<-≤-trans bound (N.^-monoʳ-≤ 2 (N.≮⇒≥ p))))) bit))

  -- Every set bit after insertion is either the new bit or an old lower bit.
  read-added : ∀ e k w → w < 2 ^ e → readBit (2 ^ e + w) k ≡ 1 →
    k ≡ e ⊎ readBit w k ≡ 1
  read-added e k w bound bit with N.<-cmp k e
  ... | tri< p _ _ = inj₂ (trans (sym (read-low e k w p)) bit)
  ... | tri≈ _ eq _ = inj₁ eq
  ... | tri> _ _ p = ⊥-elim (N.0≢1+n (trans (sym (read-zero k (2 ^ e + w)
    (N.<-≤-trans (high-bound e w bound) (N.^-monoʳ-≤ 2 p)))) bit))

  -- Inserting a higher bit retains each previously selected bit.
  read-retained : ∀ e k w → w < 2 ^ e → readBit w k ≡ 1 →
    readBit (2 ^ e + w) k ≡ 1
  read-retained e k w bound bit = trans
    (read-low e k w (read-below e k w bound bit)) bit

-- Every word's selected offsets are strictly ascending.
word-sorted : ∀ i w → AllPairs _<_ (wordOffsets i w)
word-sorted i w = P.map⁺ (P.filter⁺ (bit? w)
  (P.tabulate⁺-< (λ p → N.+-monoʳ-< (64 * i) p)))

-- Reverse a finite MSB-first position without expanding a word numeral.
reverse-position : ∀ r → r < 64 → 63 ∸ (63 ∸ r) ≡ r
reverse-position r p = N.m∸[m∸n]≡n (N.≤-pred p)

-- Equal exponents in the finite word identify equal bit positions.
reverse-injective : ∀ r s → r < 64 → s < 64 → 63 ∸ r ≡ 63 ∸ s → r ≡ s
reverse-injective r s r< s< eq = trans (sym (reverse-position r r<))
  (trans (cong (63 ∸_) eq) (reverse-position s s<))

-- A bounded tail contains only offsets strictly after the new MSB-first position.
word-lower : ∀ i r w → r < 64 → w < 2 ^ (63 ∸ r) →
  All ((64 * i + r) <_) (wordOffsets i w)
word-lower i r w r< bound = A.map⁺
  (Data.List.Relation.Unary.All.map
    (λ {s} bit → N.+-monoʳ-< (64 * i)
      (N.∸-cancelʳ-< (read-below (63 ∸ r) (63 ∸ toℕ s) w bound
        (N.≡ᵇ⇒≡ _ 1 bit))))
    (A.all-filter (bit? w) (tabulate (λ r → r))))

-- Adding a distinct higher bit prepends precisely one decoded offset.
word-prepend : ∀ i r w → r < 64 → w < 2 ^ (63 ∸ r) →
  wordOffsets i (2 ^ (63 ∸ r) + w) ≡ (64 * i + r) ∷ wordOffsets i w
word-prepend i r w r< bound = sorted-ext (word-sorted i (2 ^ (63 ∸ r) + w))
  (word-lower i r w r< bound ∷ word-sorted i w) forward backward
  where
  -- Any newly selected position is the added position or belongs to the tail.
  forward : ∀ {x} → x ∈ wordOffsets i (2 ^ (63 ∸ r) + w) →
    x ∈ ((64 * i + r) ∷ wordOffsets i w)
  forward member with word-member⁻ i (2 ^ (63 ∸ r) + w) member
  ... | s , eq , bit with read-added (63 ∸ r) (63 ∸ toℕ s) w bound
    (N.≡ᵇ⇒≡ _ 1 bit)
  ... | inj₁ same = here (trans eq (cong (64 * i +_)
    (reverse-injective (toℕ s) r (toℕ<n s) r< same)))
  ... | inj₂ old = there (subst (_∈ wordOffsets i w) (sym eq)
    (word-member⁺ i w s (N.≡⇒≡ᵇ _ 1 old)))

  -- The added position and every old selected position are selected afterwards.
  backward : ∀ {x} → x ∈ ((64 * i + r) ∷ wordOffsets i w) →
    x ∈ wordOffsets i (2 ^ (63 ∸ r) + w)
  backward (here refl) = subst (λ s → (64 * i + s) ∈ wordOffsets i (2 ^ (63 ∸ r) + w))
    (toℕ-fromℕ< r<)
    (word-member⁺ i (2 ^ (63 ∸ r) + w) (fromℕ< r<)
      (N.≡⇒≡ᵇ _ 1 (subst (λ s → readBit (2 ^ (63 ∸ r) + w) (63 ∸ s) ≡ 1)
        (sym (toℕ-fromℕ< r<)) (read-high (63 ∸ r) w bound))))
  backward (there member) with word-member⁻ i w member
  ... | s , eq , bit = subst (_∈ wordOffsets i (2 ^ (63 ∸ r) + w)) (sym eq)
    (word-member⁺ i (2 ^ (63 ∸ r) + w) s (N.≡⇒≡ᵇ _ 1
      (read-retained (63 ∸ r) (63 ∸ toℕ s) w bound (N.≡ᵇ⇒≡ _ 1 bit))))

abstract
  -- Zero contributes no decoded offsets.
  word-zero : ∀ i → wordOffsets i 0 ≡ []
  word-zero i = cong (map (λ r → 64 * i + toℕ r))
    (L.filter-none (bit? 0) {xs = tabulate (λ r → r)} (A.tabulate⁺ {f = λ r → r} (λ r bit → N.0≢1+n
      (trans (sym (read-zero (63 ∸ toℕ r) 0 (power-positive (63 ∸ toℕ r))))
        (N.≡ᵇ⇒≡ _ 1 bit)))))

  -- Quotient and remainder reconstruct the absolute offset.
  offset-position : ∀ o → o ≡ 64 * index o + o % 64
  offset-position o = trans (m≡m%n+[m/n]*n o 64 {{_}})
    (trans (N.+-comm (o % 64) (index o * 64))
      (cong (_+ o % 64) (N.*-comm (index o) 64)))

  -- A single set bit decodes to the offset that selected it.
  word-single : ∀ o → wordOffsets (index o) (2 ^ exponent o) ≡ o ∷ []
  word-single o = trans (cong (wordOffsets (index o)) (sym (N.+-identityʳ (2 ^ exponent o))))
    (trans (word-prepend (index o) (o % 64) 0 (m%n<n o 64 {{_}})
      (power-positive (exponent o)))
      (cong₂ _∷_ (sym (offset-position o)) (word-zero (index o))))

  -- Legal offsets have bounded wire word indices.
  index-bound : ∀ o → o < decoderOffsets → index o < maxBitmapEntries
  index-bound o p = m<n*o⇒m/o<n {{_}}
    (subst (o <_) (N.*-comm 64 maxBitmapEntries) p)

  -- Every MSB-first exponent lies within the 64-bit word width.
  exponent-bound : ∀ o → exponent o < 64
  exponent-bound o = s≤s (N.m∸n≤m 63 (o % 64))

  -- A single bit fits strictly below the following power of two.
  single-bound : ∀ e → 2 ^ e < 2 ^ suc e
  single-bound e = N.^-monoʳ-< 2 (s≤s (s≤s z≤n)) (N.n<1+n e)

  -- A bound at the leading bit's width implies the Word64 bound.
  word-wide : ∀ o w → w < 2 ^ suc (exponent o) → w < 2 ^ 64
  word-wide o w p = N.<-≤-trans p (N.^-monoʳ-≤ 2 (exponent-bound o))

  -- Within one quotient run, ascending offsets have ascending remainders.
  same-remainders : ∀ o n → o < n → index o ≡ index n → o % 64 < n % 64
  same-remainders o n p eq = N.+-cancelˡ-< (64 * index o) (o % 64) (n % 64)
    (subst (λ j → 64 * index o + o % 64 < 64 * j + n % 64) (sym eq)
      (subst (λ x → x < 64 * index n + n % 64) (offset-position o)
        (subst (o <_) (offset-position n) p)))

  -- A later offset in the same word leaves room for the earlier bit.
  tail-width : ∀ o n w → o < n → index o ≡ index n →
    w < 2 ^ suc (exponent n) → w < 2 ^ exponent o
  tail-width o n w p eq bound = N.<-≤-trans bound (N.^-monoʳ-≤ 2
    (N.∸-monoʳ-< (same-remainders o n p eq) (N.≤-pred (m%n<n n 64 {{_}}))))

-- The decoder's mathematical per-entry conditions, with a symbolic word bound.
Entry : ℕ × ℕ → Set
Entry (i , w) = i < maxBitmapEntries × 0 < w × w < 2 ^ 64

-- Package the induction invariant for a nonempty sorted offset list.
record Built (o : ℕ) (os : List ℕ) : Set where
  field
    -- The first run accumulates all bits with the head's quotient.
    firstWord : ℕ
    -- Subsequent runs retain their strictly later wire indices.
    restWords : Bitmap
    -- The recursion produces exactly these runs.
    shape : toWords (o ∷ os) ≡ (index o , firstWord) ∷ restWords
    -- No bit above the head's bit is set in its run.
    small : firstWord < 2 ^ suc (exponent o)
    -- All generated entries satisfy the word and index bounds.
    entries : All Entry ((index o , firstWord) ∷ restWords)
    -- Run indices are pairwise strictly ascending.
    ordered : AllPairs (λ e f → proj₁ e < proj₁ f)
      ((index o , firstWord) ∷ restWords)
    -- Decoding the runs recovers exactly the supplied offsets.
    decoded : offsets ((index o , firstWord) ∷ restWords) ≡ o ∷ os
open Built

-- A matching quotient merges into the first word, preserving its index.
prepend-same : ∀ o i w b → index o ≡ i →
  prepend o ((i , w) ∷ b) ≡ (index o , 2 ^ exponent o + w) ∷ b
prepend-same o i w b eq with index o N.≟ i
... | yes _ = cong (λ j → (j , 2 ^ exponent o + w) ∷ b) (sym eq)
... | no reject = ⊥-elim (reject eq)

-- A different quotient starts a fresh word before the existing runs.
prepend-different : ∀ o i w b → index o ≢ i →
  prepend o ((i , w) ∷ b) ≡ (index o , 2 ^ exponent o) ∷ (i , w) ∷ b
prepend-different o i w b neq with index o N.≟ i
... | yes eq = ⊥-elim (neq eq)
... | no _ = refl

-- Build all invariants by structural induction over the decodable offset list.
build : ∀ lo o os → T (decodableFrom lo (o ∷ os)) → Built o os
build lo o [] p = record
  { firstWord = 2 ^ exponent o
  ; restWords = []
  ; shape = refl
  ; small = single-bound (exponent o)
  ; entries = (index-bound o (decodable-bound lo o [] p) ,
      power-positive (exponent o) , word-wide o _ (single-bound (exponent o))) ∷ []
  ; ordered = [] ∷ []
  ; decoded = trans (L.++-identityʳ _) (word-single o)
  }
build lo o (n ∷ ns) p with build (suc o) n ns (decodable-tail lo o (n ∷ ns) p)
... | tail with index o N.≟ index n
... | yes eq = record
  { firstWord = 2 ^ exponent o + firstWord tail
  ; restWords = restWords tail
  ; shape = trans (cong (prepend o) (shape tail))
      (prepend-same o (index n) (firstWord tail) (restWords tail) eq)
  ; small = high-bound (exponent o) (firstWord tail) room
  ; entries = (head-index , N.≤-trans (power-positive (exponent o))
      (N.m≤m+n (2 ^ exponent o) (firstWord tail)) ,
      word-wide o _ (high-bound (exponent o) (firstWord tail) room)) ∷
      Data.List.Relation.Unary.All.tail (entries tail)
  ; ordered = subst (λ i → All (λ e → i < proj₁ e) (restWords tail)) (sym eq)
      (Data.List.Relation.Unary.AllPairs.head (ordered tail)) ∷
      Data.List.Relation.Unary.AllPairs.tail (ordered tail)
  ; decoded = trans
      (cong (_++ offsets (restWords tail))
        (word-prepend (index o) (o % 64) (firstWord tail) (m%n<n o 64 {{_}}) room))
      (cong₂ _∷_ (sym (offset-position o))
        (trans (cong (λ i → offsets ((i , firstWord tail) ∷ restWords tail)) eq)
          (decoded tail)))
  }
  where
  -- The canonical successor is strictly greater than the current offset.
  ascending : o < n
  ascending = decodable-lower (suc o) n ns (decodable-tail lo o (n ∷ ns) p)

  -- The leading run is bounded by the wire's configured number of words.
  head-index : index o < maxBitmapEntries
  head-index = index-bound o (decodable-bound lo o (n ∷ ns) p)

  -- Earlier distinct bits cannot carry into each other when their powers are added.
  room : firstWord tail < 2 ^ exponent o
  room = tail-width o n (firstWord tail) ascending eq (small tail)
... | no neq = record
  { firstWord = 2 ^ exponent o
  ; restWords = (index n , firstWord tail) ∷ restWords tail
  ; shape = trans (cong (prepend o) (shape tail))
      (prepend-different o (index n) (firstWord tail) (restWords tail) neq)
  ; small = single-bound (exponent o)
  ; entries = (index-bound o (decodable-bound lo o (n ∷ ns) p) ,
      power-positive (exponent o) , word-wide o _ (single-bound (exponent o))) ∷
      entries tail
  ; ordered = (earlier ∷ Data.List.Relation.Unary.All.map (N.<-trans earlier)
      (Data.List.Relation.Unary.AllPairs.head (ordered tail))) ∷ ordered tail
  ; decoded = trans
      (cong (_++ offsets ((index n , firstWord tail) ∷ restWords tail)) (word-single o))
      (cong (o ∷_) (decoded tail))
  }
  where
  -- Distinct quotients preserve the decodable offset ordering.
  earlier : index o < index n
  earlier = N.≤∧≢⇒< (/-monoˡ-≤ 64 {{_}} (N.<⇒≤
    (decodable-lower (suc o) n ns (decodable-tail lo o (n ∷ ns) p)))) neq

abstract
  -- An increasing bounded index list has at most as many entries as indices.
  count-from : ∀ lo upper (b : Bitmap) → lo ≤ upper → All (λ e → lo ≤ proj₁ e) b →
    All (λ e → proj₁ e < upper) b →
    AllPairs (λ e f → proj₁ e < proj₁ f) b → lo + length b ≤ upper
  count-from lo upper [] bound [] [] [] =
    subst (_≤ upper) (sym (N.+-identityʳ lo)) bound
  count-from lo upper ((i , w) ∷ b) bound (lower ∷ lowers) (limit ∷ limits)
    (later ∷ ordered) = N.≤-trans
      (subst (_≤ suc i + length b) (sym (N.+-suc lo (length b)))
        (s≤s (N.+-monoˡ-≤ (length b) lower)))
      (count-from (suc i) upper b limit later limits ordered)

  -- Use precisely the decoder's entry predicate at the proof boundary.
  entryᵇ : ℕ × ℕ → Bool
  entryᵇ (i , w) = (i <ᵇ maxBitmapEntries) ∧ (0 <ᵇ w) ∧
    (w <ᵇ 2 ^ 64)

  -- Reflect symbolic index, positivity and Word64 bounds into the wire decoder.
  entry-valid : ∀ e → Entry e → T (entryᵇ e)
  entry-valid (i , w) (i< , w> , w<) =
    ∧-intro {a = i <ᵇ maxBitmapEntries}
      {b = (0 <ᵇ w) ∧ (w <ᵇ 2 ^ 64)} (N.<⇒<ᵇ i<)
      (∧-intro {a = 0 <ᵇ w} {b = w <ᵇ 2 ^ 64}
        (N.<⇒<ᵇ w>) (N.<⇒<ᵇ w<))

  -- Bounded positive words and increasing indices satisfy every decoder condition.
  bitmap-valid : ∀ b → All Entry b →
    AllPairs (λ e f → proj₁ e < proj₁ f) b → T (validᵇ b)
  bitmap-valid b entries ordered =
    ∧-intro {a = (length b ≤ᵇ maxBitmapEntries) ∧ Data.Bool.ListAction.all entryᵇ b}
      {b = does (linked? (λ e f → proj₁ e N.<? proj₁ f) b)}
      (∧-intro {a = length b ≤ᵇ maxBitmapEntries}
        {b = Data.Bool.ListAction.all entryᵇ b}
        (N.≤⇒≤ᵇ (count-from 0 maxBitmapEntries b z≤n
          (Data.List.Relation.Unary.All.map (λ _ → z≤n) entries)
          (Data.List.Relation.Unary.All.map proj₁ entries) ordered))
        (A.all⁻ entryᵇ (Data.List.Relation.Unary.All.map (λ {e} → entry-valid e) entries)))
      (dec-true (linked? (λ e f → proj₁ e N.<? proj₁ f) b) (AllPairs⇒Linked ordered))

  -- Encoding every decodable list yields a valid list of nonempty wire words.
  toWords-valid : ∀ {os} → T (decodable os) → T (validᵇ (toWords os))
  toWords-valid {[]} p = tt
  toWords-valid {o ∷ os} p = subst (λ b → T (validᵇ b)) (sym (shape built-proof))
    (bitmap-valid _ (entries built-proof) (ordered built-proof))
    where
    -- The list induction supplies bounds and strict ordering of all runs.
    built-proof : Built o os
    built-proof = build 0 o os p

  -- Decoding the generated words recovers the decodable offset list exactly.
  offsets-toWords : ∀ {os} → T (decodable os) → offsets (toWords os) ≡ os
  offsets-toWords {[]} p = refl
  offsets-toWords {o ∷ os} p = trans (cong offsets (shape built-proof)) (decoded built-proof)
    where
    -- The same induction proves exact coverage as well as decoder validity.
    built-proof : Built o os
    built-proof = build 0 o os p

  -- The wire popcount is decoded length, so each distinct source offset counts once.
  toWords-popcount : ∀ {os} → T (decodable os) → popcount (toWords os) ≡ length os
  toWords-popcount {os} p = cong length (offsets-toWords {os} p)

abstract
  -- A canonical suffix cannot have more offsets than its remaining range.
  canonical-count-from : ∀ lo os → lo ≤ maxTxs → T (canonicalFrom lo os) → lo + length os ≤ maxTxs
  canonical-count-from lo [] low p = subst (_≤ maxTxs) (sym (N.+-identityʳ lo)) low
  canonical-count-from lo (o ∷ os) low p = N.≤-trans
    (subst (_≤ suc o + length os) (sym (N.+-suc lo (length os)))
      (s≤s (N.+-monoˡ-≤ (length os) (canonical-lower lo o os p))))
    (canonical-count-from (suc o) os (canonical-bound lo o os p) (canonical-tail lo o os p))

  -- Honest requests fit the transaction count cap as well as the offset cap.
  canonical-count : ∀ {os} → T (canonical os) → length os ≤ maxTxs
  canonical-count {os} = canonical-count-from 0 os z≤n

  -- Decoding supplies the table bounds for every requested offset.
  decodable-all-from : ∀ lo os → T (decodableFrom lo os) → All (_< decoderOffsets) os
  decodable-all-from lo [] p = []
  decodable-all-from lo (o ∷ os) p = decodable-bound lo o os p ∷
    decodable-all-from (suc o) os (decodable-tail lo o os p)

  -- The server can look up each decoded offset in a decoder-sized table.
  decodable-all : ∀ {os} → T (decodable os) → All (_< decoderOffsets) os
  decodable-all {os} = decodable-all-from 0 os

  -- Bounded increasing tabulations satisfy the honest send predicate.
  canonical-tabulation : ∀ n (f : ℕ → ℕ) lo → lo ≤ f 0 →
    (∀ i → i < n → f i < maxTxs) → (∀ i → suc (f i) ≤ f (suc i)) →
    T (canonicalFrom lo (applyUpTo f n))
  canonical-tabulation zero f lo low bounded increasing = tt
  canonical-tabulation (suc n) f lo low bounded increasing =
    ∧-intro {a = lo ≤ᵇ f 0} {b = (f 0 <ᵇ maxTxs) ∧ canonicalFrom (suc (f 0)) (applyUpTo (λ i → f (suc i)) n)}
      (N.≤⇒≤ᵇ low)
      (∧-intro {a = f 0 <ᵇ maxTxs} {b = canonicalFrom (suc (f 0)) (applyUpTo (λ i → f (suc i)) n)}
        (N.<⇒<ᵇ (bounded 0 (s≤s z≤n)))
        (canonical-tabulation n (λ i → f (suc i)) (suc (f 0)) (increasing 0)
          (λ i lt → bounded (suc i) (s≤s lt)) (λ i → increasing (suc i))))

  -- Completeness chooses the first n offsets for an honest count n.
  canonical-upTo : ∀ n → n ≤ maxTxs → T (canonical (upTo n))
  canonical-upTo n cap = canonical-tabulation n (λ i → i) 0 N.≤-refl
    (λ i lt → N.≤-trans lt cap) (λ i → N.≤-refl)

-- Spell the wire's entry test locally for extracting its index bound.
wireEntryᵇ : ℕ × ℕ → Bool
wireEntryᵇ (i , w) = (i <ᵇ maxBitmapEntries) ∧ (0 <ᵇ w) ∧ (w <ᵇ 18446744073709551616)

abstract
  -- Every selected bit in a bounded-index word is below the decoder ceiling.
  word-decoder-bound : ∀ i w → i < maxBitmapEntries → All (_< decoderOffsets) (wordOffsets i w)
  word-decoder-bound i w cap = A.map⁺ (A.filter⁺ (bit? w)
    (A.tabulate⁺ (λ r → N.<-≤-trans
      (subst (64 * i + toℕ r <_) (trans (N.+-comm (64 * i) 64) (sym (N.*-suc 64 i)))
        (N.+-monoʳ-< (64 * i) (toℕ<n r)))
      (N.*-monoʳ-≤ 64 cap))))

  -- Legal wire entries bound every expanded offset, without evaluating word numerals.
  expanded-bounds : ∀ b → All (λ e → T (wireEntryᵇ e)) b → All (_< decoderOffsets) (offsets b)
  expanded-bounds [] [] = []
  expanded-bounds ((i , w) ∷ b) (ok ∷ oks) = A.++⁺
    (word-decoder-bound i w (N.<ᵇ⇒< i maxBitmapEntries
      (∧-left {a = i <ᵇ maxBitmapEntries} {b = (0 <ᵇ w) ∧ (w <ᵇ 18446744073709551616)} ok)))
    (expanded-bounds b oks)

  -- Strict ordering with lower and exclusive upper bounds satisfies decoding.
  sorted-decodable : ∀ lo os → All (lo ≤_) os → All (_< decoderOffsets) os →
    AllPairs _<_ os → T (decodableFrom lo os)
  sorted-decodable lo [] [] [] [] = tt
  sorted-decodable lo (o ∷ os) (low ∷ lows) (cap ∷ caps) (later ∷ sorted) =
    ∧-intro {a = lo ≤ᵇ o} {b = (o <ᵇ decoderOffsets) ∧ decodableFrom (suc o) os}
      (N.≤⇒≤ᵇ low)
      (∧-intro {a = o <ᵇ decoderOffsets} {b = decodableFrom (suc o) os}
        (N.<⇒<ᵇ cap) (sorted-decodable (suc o) os later caps sorted))

  -- Every bitmap accepted by the wire decoder has a decodable model representative.
  offsets-decodable : ∀ b → T (validᵇ b) → T (decodable (offsets b))
  offsets-decodable b ok = sorted-decodable 0 (offsets b)
    (Data.List.Relation.Unary.All.universal (λ _ → z≤n) (offsets b))
    (expanded-bounds b (A.all⁺ wireEntryᵇ b
      (∧-right {a = length b ≤ᵇ maxBitmapEntries} {b = all wireEntryᵇ b}
        (∧-left {a = (length b ≤ᵇ maxBitmapEntries) ∧ all wireEntryᵇ b}
          {b = does (linked? (λ e f → proj₁ e N.<? proj₁ f) b)} ok))))
    (Data.List.Relation.Unary.Linked.Properties.Linked⇒AllPairs N.<-trans
      (Cardano_network.Replay.LeiosFetchWire.offsets-sorted b ok))

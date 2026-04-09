
open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapMaybe)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)

open import Relation.Binary                       using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; [_])

module Prelude where
≡-equiv : ∀ {ℓ} {A : Set ℓ} → IsEquivalence {A = A} _≡_
≡-equiv = record { refl = refl ; sym = sym ; trans = trans }

-- Extract the witnessed value from Is-just
to-witness : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} → Is-just m → A
to-witness {m = just x} _ = x

-- Proof that Is-just m implies m ≡ just (to-witness m)
just-to-witness : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} (p : Is-just m)
                → m ≡ just (to-witness p)
just-to-witness {m = just _} _ = refl

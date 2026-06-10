{-
  This module 
-}

{-# OPTIONS --guardedness #-}

open import Data.Nat.Properties
open import Data.Nat using (ℕ; _≟_; _+_; suc; zero)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool)
-- open import Data.Empty.Polymorphic using (⊥)
-- open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to 0ℓ; suc to lsuc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (map′)
open import Class.DecEq using (DecEq-⊥; _==_)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes

module CSP.Examples.IO.IO where
data IO : Set → Set where
  input  : IO ℕ
  output : ℕ → IO ⊥
  inout  : ℕ → ℕ → IO (ℕ)

-- A subset of events for input
OnlyInput : AnyTypes IO → Set
OnlyInput (.ℕ , input)      = ⊤
OnlyInput (.⊥ , output _)   = ⊥
OnlyInput (.ℕ , inout _ _)  = ⊥

------------------------------------------------------------------
-- Dec for equality

IO-AnyTypes-≟ : (x y : AnyTypes IO) → Dec (x ≡ y)

IO-AnyTypes-≟ (_ , input) (_ , input) = yes refl

IO-AnyTypes-≟ (_ , output n) (_ , output m) with n ≟ m
... | yes p = yes (cong (λ k → (_ , output k)) p)
... | no ¬p = no (λ { refl → ¬p refl })

IO-AnyTypes-≟ (_ , inout a b) (_ , inout c d)
  with a ≟ c | b ≟ d
... | yes p | yes q =
      yes (cong₂ (λ x y → (_ , inout x y)) p q)
... | no ¬p | _ = no (λ { refl → ¬p refl })
... | _ | no ¬q = no (λ { refl → ¬q refl })

IO-AnyTypes-≟ (_ , input) (_ , output _) = no λ ()
IO-AnyTypes-≟ (_ , input) (_ , inout _ _) = no λ ()
IO-AnyTypes-≟ (_ , output _) (_ , input) = no λ ()
IO-AnyTypes-≟ (_ , output _) (_ , inout _ _) = no λ ()
IO-AnyTypes-≟ (_ , inout _ _) (_ , input) = no λ ()
IO-AnyTypes-≟ (_ , inout _ _) (_ , output _) = no λ ()

-- decEs : (es : AnyTypes IO → Set) → (at : AnyTypes IO) → Dec (es at)

import CSP.Definitions.Operators {E = IO} as CSPOps
open CSPOps IO-AnyTypes-≟
import CSP.Definitions.Iterate {E = IO} as CSPIte
open CSPIte IO-AnyTypes-≟
import CSP.Definitions.Parallel {E = IO} as CSPPar
open CSPPar IO-AnyTypes-≟

-- Decidable membership for the OnlyInput synchronisation set
OnlyInput-dec : (at : AnyTypes IO) → Dec (OnlyInput at)
OnlyInput-dec (_ , input)     = yes tt
OnlyInput-dec (_ , output _)  = no λ ()
OnlyInput-dec (_ , inout _ _) = no λ ()

-- A process that takes an input, outputs it, and then terminates.
copy⊤ : ITree IO (ExtI IO) (⊤)
--    copy⊤ = Prefix input (λ x → Prefix (output x) (λ _ → Ret tt))
copy⊤ = input ⟶ (λ x → (output x) ⟶ (λ _ → Ret tt))

copy⊥ : ITree IO (ExtI IO) (⊥)
copy⊥ = input ⟶ (λ x → (output x) ⟶ (λ ()))

echo : ITree IO (ExtI IO) ⊥
echo = loop0 (
  input ⟶ (λ x →
    (output x) ⟶ (λ _ → Skip))
  )

-- Output the initial value 0, then like a copy machine with x from input
-- outputted and then pass x to the next iteration
echo' : ITree IO (ExtI IO) ⊥
echo' = loop (λ a → 
  (output a ⟶₀ input ⟶ (λ x →
    (output x) ⟶ (λ _ → Ret x)))
  ) 0

P : ITree IO (ExtI IO) ⊥
P = copy⊥ □ (Run)
  -- where all : AnyTypes IO → Set
  --      all (A , _) = A

Q : ITree IO (ExtI IO) ℕ
Q = input ⟶₀ Ret 1

R : ℕ → ITree IO (ExtI IO) (⊥)
R x = inout x (x + 1) ⟶ (λ y → (output y ⟶  λ ()))

QR : ITree IO (ExtI IO) (⊥)
QR = do
  x ← Q
  inout x (x + 1) ⟶ (λ y → (output y ⟶  λ ()))

guardP : ITree IO (ExtI IO) (⊥)
guardP = do
  x ← Ret 1
  (x == suc zero) ＆ Stop

PorQ : ITree IO (ExtI IO) ⊥
PorQ = P ⊓ R 0

P1 : ITree IO (ExtI IO) ⊥
P1 = ((P ⊓ P) ⊓ (P □ P)) □ R 0

-- Parallel composition of P and Q synchronising on `input` events.
-- P offers `input` (via copy⊥) and `Run`; Q offers `input`.
-- On the shared `input` event they must agree; other events interleave.
P∥Q : ITree IO (ExtI IO) (⊥ × ℕ)
P∥Q = P ∥⇘ OnlyInput ¿ OnlyInput-dec ⇙ Q

-- Pure interleaving variant (empty synchronisation set).
NoSync : AnyTypes IO → Set
NoSync _ = ⊥

NoSync-dec : (at : AnyTypes IO) → Dec (NoSync at)
NoSync-dec _ = no λ ()

P∥∅Q : ITree IO (ExtI IO) (⊥ × ℕ)
P∥∅Q = P ∥⇘ NoSync ¿ NoSync-dec ⇙ Q

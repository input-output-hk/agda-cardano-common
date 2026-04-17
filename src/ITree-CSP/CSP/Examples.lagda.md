```
{-# OPTIONS --guardedness #-}

open import Data.Nat.Properties
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to 0ℓ; suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
-- open import Data.Empty.Polymorphic using (⊥)
-- open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Data.Nat using (ℕ; _≟_; _+_; suc; zero)
-- open import Data.Nat.Properties 
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (map′)
open import Class.DecEq using (DecEq-⊥; _==_)
open import Data.Bool using (Bool)

open import Interaction_Trees
open import CSP.Basic_Processes
```

```
module CSP.Examples where
  open ITree
```

# Up and Down

This is a simple CSP example with only up and down events
```
  module CSP_UpDown where
    data UpDown : Set → Set where
      up   : UpDown (⊥)
      down : UpDown (⊥)

```

```
    UpDown-AnyTypes-≟ : (x y : AnyTypes UpDown) → Dec (x ≡ y)
    
    UpDown-AnyTypes-≟ (_ , up) (_ , up) = yes refl
    UpDown-AnyTypes-≟ (_ , down) (_ , down) = yes refl    
    UpDown-AnyTypes-≟ (_ , up)   (_ , down) = no λ ()
    UpDown-AnyTypes-≟ (_ , down) (_ , up)   = no λ ()    

    import CSP.Operators {E = UpDown} as CSPOps
    import CSP.Iterate {E = UpDown} as CSPIte
    open CSPOps UpDown-AnyTypes-≟
    open CSPIte UpDown-AnyTypes-≟    
```

```
    P : ITree UpDown (ExtI UpDown) (⊥)
    P = up ⟶₀ down ⟶₀ Stop

    P' : ITree UpDown (ExtI UpDown) (⊥)
    P' = down ⟶₀ Stop

    P□P' : ITree UpDown (ExtI UpDown) (⊥)
    P□P' = P □ P'

    P⊓P' : ITree UpDown (ExtI UpDown) (⊥)
    P⊓P' = P ⊓ P'

    -- Loop version
    Q : ITree UpDown (ExtI UpDown) (⊥)
    Q = loop0 (up ⟶₀ down ⟶₀ Skip)

    R : ITree UpDown (UpDown) (⊤)
    R = Run

    R_up_only : ITree UpDown (ExtI UpDown) (⊤)
    R_up_only = Run′ es dec
      where
        es : AnyTypes UpDown → Set
        es (⊥ , up)   = ⊤
        es (⊥ , down) = ⊥

        dec : (at : AnyTypes UpDown) → Dec (es at)
        dec (_ , up)   = yes tt
        dec (_ , down) = no λ()
```

```
  module CSP_IO where

    data IO : Set → Set where
      input  : IO ℕ
      output : ℕ → IO ⊥
      inout  : ℕ → ℕ → IO (ℕ)

    OnlyInput : AnyTypes IO → Set
    OnlyInput (.ℕ , input)      = ⊤
    OnlyInput (.⊥ , output _)   = ⊥
    OnlyInput (.ℕ , inout _ _)  = ⊥
        
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

    import CSP.Operators {E = IO} as CSPOps
    open CSPOps IO-AnyTypes-≟
    import CSP.Iterate {E = IO} as CSPIte
    open CSPIte IO-AnyTypes-≟    
      
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
  ```

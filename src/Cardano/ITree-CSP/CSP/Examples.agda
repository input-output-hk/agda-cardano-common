{-# OPTIONS --guardedness #-}

open import Data.Nat.Properties
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Data.Nat using (ℕ; _≟_; _+_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (map′)

open import Interaction_Trees
open import CSP.Basic_Processes

module CSP.Examples where
  open ITree

  module CSP_UpDown where
    data UpDown : Set → Set where
      up   : UpDown ⊥
      down : UpDown ⊥

    UpDown-AnyTypes-≟ : (x y : AnyTypes UpDown) → Dec (x ≡ y)
    
    UpDown-AnyTypes-≟ (_ , up) (_ , up) = yes refl
    UpDown-AnyTypes-≟ (_ , down) (_ , down) = yes refl    
    UpDown-AnyTypes-≟ (_ , up)   (_ , down) = no λ ()
    UpDown-AnyTypes-≟ (_ , down) (_ , up)   = no λ ()    

    import CSP.Operators {E = UpDown} as CSPOps
    import CSP.Iterate {E = UpDown} as CSPIte
    open CSPOps UpDown-AnyTypes-≟
    open CSPIte UpDown-AnyTypes-≟    

    P : ITree UpDown ⊥
    P = up ⟶₀ down ⟶₀ Stop'

    -- Loop version
    Q : ITree UpDown ⊥
    Q = loop0 (up ⟶₀ down ⟶₀ Skip)

    R : ITree UpDown ⊤
    R = Run

    R_up_only : ITree UpDown ⊤
    R_up_only = Run' es dec
      where
        es : AnyTypes UpDown → Set
        es (⊥ , up)   = ⊤
        es (⊥ , down) = ⊥

        dec : (at : AnyTypes UpDown) → Dec (es at)
        dec (_ , up)   = yes tt
        dec (_ , down) = no λ()
            
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
      
    -- A process that takes an input, outputs it, and then terminates.
    copy⊤ : ITree IO ⊤
    copy⊤ = Prefix input (λ x → Prefix (output x) (λ _ → Ret tt))
      
    copy⊥ : ITree IO ⊥
    copy⊥ = Prefix input (λ x → Prefix (output x) (λ ()))

    {-
    P : ITree IO ⊥
    P = copy⊥ □ (Run all)
      where all : AnyTypes IO → Set
            all (A , _) = A
    -}
    Q : ITree IO ℕ
    Q = input ⟶₀ Ret 1

    R : ℕ → ITree IO ⊥
    R x = inout x (x + 1) ⟶ (λ y → (output y ⟶  λ ()))

    QR : ITree IO ⊥
    QR = do
      x ← Q
      inout x (x + 1) ⟶ (λ y → (output y ⟶  λ ()))
  

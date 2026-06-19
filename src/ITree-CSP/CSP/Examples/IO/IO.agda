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
open import Data.Maybe using (Maybe; just; nothing)

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to 0ℓ; suc to lsuc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable using (map′)
open import Class.DecEq using (DecEq-⊥; _==_)
open import Class.DecEq.Instances using (DecEq-ℕ)
import Data.Unit.Polymorphic as ⊤ₚ

open import Process_Trees

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

import CSP.Operators {E = IO} as CSPOps
open CSPOps IO-AnyTypes-≟

-- Decidable membership for the OnlyInput synchronisation set
OnlyInput-dec : (at : AnyTypes IO) → Dec (OnlyInput at)
OnlyInput-dec (_ , input)     = yes tt
OnlyInput-dec (_ , output _)  = no λ ()
OnlyInput-dec (_ , inout _ _) = no λ ()

-- A process that takes an input, outputs it, and then terminates.
copy⊤ : PTree IO (ExtI IO) (⊤)
--    copy⊤ = Prefix input (λ x → Prefix (output x) (λ _ → Ret tt))
copy⊤ = input ⟶ (λ x → (output x) ⟶ (λ _ → Ret tt))

copy⊥ : PTree IO (ExtI IO) (⊥)
copy⊥ = input ⟶ (λ x → (output x) ⟶ (λ ()))

echo : PTree IO (ExtI IO) ⊥
echo = loop0 (
  input ⟶ (λ x →
    (output x) ⟶ (λ _ → Skip))
  )

-- Output the initial value 0, then like a copy machine with x from input
-- outputted and then pass x to the next iteration
echo' : PTree IO (ExtI IO) ⊥
echo' = loop (λ a → 
  (output a ⟶₀ (input ⟶ (λ x →
    (output x) ⟶ (λ _ → Ret x))))
  ) 0

P : PTree IO (ExtI IO) ⊥
P = copy⊥ □ (Run)
  -- where all : AnyTypes IO → Set
  --      all (A , _) = A

Q : PTree IO (ExtI IO) ℕ
Q = input ⟶₀ Ret 1

R : ℕ → PTree IO (ExtI IO) (⊥)
R x = inout x (x + 1) ⟶ (λ y → (output y ⟶  λ ()))

QR : PTree IO (ExtI IO) (⊥)
QR = do
  x ← Q
  inout x (x + 1) ⟶ (λ y → (output y ⟶  λ ()))

guardP : PTree IO (ExtI IO) (⊥)
guardP = do
  x ← Ret 1
  (x == suc zero) ＆ Stop

PorQ : PTree IO (ExtI IO) ⊥
PorQ = P ⊓ R 0

P1 : PTree IO (ExtI IO) ⊥
P1 = ((P ⊓ P) ⊓ (P □ P)) □ R 0

-- Parallel composition of P and Q synchronising on `input` events.
-- P offers `input` (via copy⊥) and `Run`; Q offers `input`.
-- On the shared `input` event they must agree; other events interleave.
P∥Q : PTree IO (ExtI IO) (⊥ × ℕ)
P∥Q = Par (chanSet OnlyInput OnlyInput-dec) _,_ P Q

-- Pure interleaving variant (empty synchronisation set).
NoSync : AnyTypes IO → Set
NoSync _ = ⊥

NoSync-dec : (at : AnyTypes IO) → Dec (NoSync at)
NoSync-dec _ = no λ ()

P∥∅Q : PTree IO (ExtI IO) (⊥ × ℕ)
P∥∅Q = Par (chanSet NoSync NoSync-dec) _,_ P Q

------------------------------------------------------------------
-- Same-index reader/writer synchronisation: `c?x` and `c!v` are the SAME
-- event index `(ℕ , c)`; they differ ONLY in the visible-offer map over the
-- carried ℕ.  Prefix (`c ⟶ P`) offers every value; Output (`c ! v ⟶ P`) offers
-- only `v`.  Both fire at index `(ℕ , c)`, so a parallel synchronising on `c`
-- agrees iff the writer's value is in the reader's menu.
------------------------------------------------------------------

-- A subset of events for the inout channel family
OnlyInout : AnyTypes IO → Set
OnlyInout (_ , inout _ _) = ⊤
OnlyInout _              = ⊥

OnlyInout-dec : (at : AnyTypes IO) → Dec (OnlyInout at)
OnlyInout-dec (_ , input)     = no λ ()
OnlyInout-dec (_ , output _)  = no λ ()
OnlyInout-dec (_ , inout _ _) = yes tt

-- (b) input-channel sync: reader offers every value (input?x), writer offers
-- only value 1 (input.1); both fire at the SAME index (ℕ , input).
inReader : PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
inReader = input ⟶ (λ x → Skip)        -- input?x → Skip

inWriter : PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
inWriter = input ! 1 ⟶ Skip            -- input.1  → Skip

inSync : PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
inSync = inReader ∥⇘ chanSet OnlyInput OnlyInput-dec ⇙ inWriter

-- (c) inout-channel sync: parameterised channel `inout 1 2`, reader inout.1.2?x,
-- writer inout.1.2!1, same index (ℕ , inout 1 2).
inoutReader : PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
inoutReader = inout 1 2 ⟶ (λ x → Skip)     -- inout.1.2?x → Skip

inoutWriter : PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
inoutWriter = inout 1 2 ! 1 ⟶ Skip          -- inout.1.2.1 → Skip

inoutSync : PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
inoutSync = inoutReader ∥⇘ chanSet OnlyInout OnlyInout-dec ⇙ inoutWriter

------------------------------------------------------------------------
-- (d) VALUE-SELECTIVE synchronisation — the payload the value-level `Par`
-- migration delivers.  `inOne` = {| input.1 |}: it synchronises the `input`
-- channel ONLY on the carried value `1`, and is empty on every other value
-- of `input` (and on all other channels).  So in `inReader ∥⇘ inOne ⇙ inWriter1`
-- the writer's `input!1` MUST rendez-vous with the reader, whereas a value `2`
-- (offered by the reader's `input?x` menu but NOT in `inOne`) interleaves.
-- A channel-level set could not express this: it would either sync ALL input
-- values or none.
------------------------------------------------------------------------

-- {| input.1 |}: the input channel, selected only at value 1.
inOne : EventSet
inOne .EventSet.mem (.ℕ , input)     a = a ≡ 1
inOne .EventSet.mem (.⊥ , output _)  a = ⊥
inOne .EventSet.mem (.ℕ , inout _ _) a = ⊥
inOne .EventSet.dec (.ℕ , input)     a = a ≟ 1
inOne .EventSet.dec (.⊥ , output _)  a = no (λ ())
inOne .EventSet.dec (.ℕ , inout _ _) a = no (λ ())

inWriter1 : PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
inWriter1 = input ! 1 ⟶ Skip            -- input.1 → Skip

inSelSync : PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
inSelSync = inReader ∥⇘ inOne ⇙ inWriter1

------------------------------------------------------------------------
-- Regression: value 1 SYNCS, value 2 INTERLEAVES.
-- Read the visible-offer continuation of a node at index (ℕ , input).
------------------------------------------------------------------------

visContIO : NodeKind IO (ExtI IO) (⊤ₚ.⊤ {0ℓ})
          → (at : AnyTypes IO) → proj₁ at → Maybe (PTree IO (ExtI IO) (⊤ₚ.⊤ {0ℓ}))
visContIO (react v _) = v
visContIO _           = λ _ _ → nothing

-- value 1 ∈ inOne ⇒ rendez-vous: both sides advance to Skip, the composite
-- steps to  Skip ∥⇘ inOne ⇙ Skip  (a SINGLE just on the synced index).
sync-on-1 : visContIO (PTree.force inSelSync) (ℕ , input) 1
          ≡ just (Skip ∥⇘ inOne ⇙ Skip)
sync-on-1 = refl

-- value 2 ∉ inOne ⇒ the reader's `input?2` proceeds ALONE (writer unchanged):
-- the composite interleaves to  Skip ∥⇘ inOne ⇙ inWriter1 .  This continuation
-- DIFFERS from the value-1 (sync) one: the writer is NOT consumed.
interleave-on-2 : visContIO (PTree.force inSelSync) (ℕ , input) 2
                ≡ just (Skip ∥⇘ inOne ⇙ inWriter1)
interleave-on-2 = refl

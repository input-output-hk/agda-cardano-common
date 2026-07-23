{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Smoke test for the CHANNEL-level priority operator `Priᶜ` over an
-- INFINITE carrier — the case the value-level `Pri` cannot express.
--
-- Alphabet: `tick : Ch ⊤` and an `ℕ`-carried input `inp : Ch ℕ`, with the
-- INFINITE-carrier channel dominating: `tick <ᶜ inp`.  Then `aboveᶜ tick =
-- [inp]` is a ONE-element finite list — whereas the value-level `above (tick∙tt)`
-- would have to list `inp∙0, inp∙1, …`, an INFINITE list that `Pri` cannot form.
--
-- On `P = tick→Stop □ inp?n→Stop` (both offered): `Priᶜ` PRUNES `tick` (its
-- dominating channel `inp` is offered) and KEEPS `inp` (maximal).  This shows
-- `Priᶜ` prioritises value-free, so infinite carriers work end to end.
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_; proj₁; Σ-syntax)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; DecEq-⊥)

open import Process_Trees

module CSP.Examples.priority.PriorityCInfinite where

-- event alphabet: a ⊤-channel `tick` and an ℕ-carried (INFINITE) input `inp`
data Ch : Set → Set where
  tick : Ch ⊤
  inp  : Ch ℕ

-- decidable equality on the (channel) events
Ch-≟ : (x y : AnyTypes Ch) → Dec (x ≡ y)
Ch-≟ (_ , tick) (_ , tick) = yes refl
Ch-≟ (_ , inp)  (_ , inp)  = yes refl
Ch-≟ (_ , tick) (_ , inp)  = no λ ()
Ch-≟ (_ , inp)  (_ , tick) = no λ ()

open import Semantics.PriOrderC {0ℓ} {0ℓ} {Ch}
open import Semantics.LTS       {E = Ch} {I = ExtI Ch}
open import Semantics.Refusals  {E = Ch} {I = ExtI Ch} using (Offers)
open import CSP.Priority.Base        {0ℓ} {0ℓ} {Ch} using (FinBr)
open import CSP.Priority.Closure Ch-≟
open import CSP.Priority.Channel Ch-≟
open import CSP.Operators Ch-≟

------------------------------------------------------------------------
-- The channel order  tick <ᶜ inp  (the INFINITE-carrier channel dominates).
------------------------------------------------------------------------

-- strict channel order: only `tick ◃ᶜ inp`
_◃ᶜ_ : AnyTypes Ch → AnyTypes Ch → Set
(_ , tick) ◃ᶜ (_ , inp) = ⊤
_          ◃ᶜ _         = ⊥

◃ᶜ-irrefl : ∀ {c} → ¬ (c ◃ᶜ c)
◃ᶜ-irrefl {_ , tick} ()
◃ᶜ-irrefl {_ , inp}  ()

◃ᶜ-trans : ∀ {x y z} → x ◃ᶜ y → y ◃ᶜ z → x ◃ᶜ z
◃ᶜ-trans {_ , inp}                ()
◃ᶜ-trans {_ , tick} {_ , tick}    ()
◃ᶜ-trans {_ , tick} {_ , inp}  _  ()

-- dominating CHANNELS: `aboveᶜ tick = [inp]` (FINITE — value-level `above` is not)
aboveᶜ′ : AnyTypes Ch → List (AnyTypes Ch)
aboveᶜ′ (_ , tick) = (ℕ , inp) ∷ []
aboveᶜ′ _          = []

aboveᶜ′-sound : ∀ {c c′} → c′ ∈ aboveᶜ′ c → c ◃ᶜ c′
aboveᶜ′-sound {_ , tick} (here refl) = tt
aboveᶜ′-sound {_ , inp}  ()

aboveᶜ′-complete : ∀ {c c′} → c ◃ᶜ c′ → c′ ∈ aboveᶜ′ c
aboveᶜ′-complete {_ , tick} {_ , inp} _ = here refl

-- the dominating channel `inp` is inhabited (carries ℕ); others vacuous
aboveᶜ′-inhabited : ∀ {c c′} → c′ ∈ aboveᶜ′ c → proj₁ c′
aboveᶜ′-inhabited {_ , tick} (here refl) = zero
aboveᶜ′-inhabited {_ , inp}  ()

-- the channel-level priority order
O : PriOrderC 0ℓ
O = record
  { prop = record { _<ᶜ_ = _◃ᶜ_ ; <ᶜ-irrefl = ◃ᶜ-irrefl ; <ᶜ-trans = ◃ᶜ-trans }
  ; aboveᶜ = aboveᶜ′
  ; aboveᶜ-sound = aboveᶜ′-sound
  ; aboveᶜ-complete = aboveᶜ′-complete
  ; above-inhabited = aboveᶜ′-inhabited
  }

------------------------------------------------------------------------
-- The process and its finite-branching certificate.
------------------------------------------------------------------------

-- offers BOTH `tick` and the infinite input `inp?n`
P : PTree Ch (ExtI Ch) ⊥
P = _□_ ⦃ DecEq-⊥ ⦄ (tick ⟶₀ Stop) (inp ⟶ (λ _ → Stop))

fbP : FinBr P
fbP = finBr-□ ⦃ DecEq-⊥ ⦄ (finBr-prefix₀ finBr-Stop) (finBr-prefix (λ _ → finBr-Stop))

------------------------------------------------------------------------
-- The two visible labels we observe.
------------------------------------------------------------------------

-- the label `tick`
ℓtick : Event√ ⊥
ℓtick = evl (evLabel ⊤ tick tt)

-- the label `inp 0` (any ℕ value works; `0` is representative)
ℓinp0 : Event√ ⊥
ℓinp0 = evl (evLabel ℕ inp zero)

------------------------------------------------------------------------
-- (a) `Priᶜ O deadlock` — the generic operator smoke lives in `CSP.Priority.Channel`
--     (`pri-c-deadlock-smoke`); here we exercise the INFINITE-carrier case.
--
-- (b) `Priᶜ` PRUNES `tick` (dominated by the offered infinite-carrier `inp`)
--     and KEEPS `inp` — decided purely at the CHANNEL level, never touching ℕ.
------------------------------------------------------------------------

-- `tick` is pruned: its dominating channel `inp` is in `chan-supp`
pri-prunes-tick : ¬ Offers (Priᶜ O P fbP) ℓtick
pri-prunes-tick (_ , sVis {v = v} eqf br) with react-injective eqf
... | veq , _ = case subst (λ w → w (⊤ , tick) tt ≡ just _) (sym veq) br of λ ()

-- the infinite-carrier input `inp` survives (it is ≤-maximal)
pri-keeps-inp : Offers (Priᶜ O P fbP) ℓinp0
pri-keeps-inp = _ , sVis refl refl

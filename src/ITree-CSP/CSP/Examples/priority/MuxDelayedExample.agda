{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Concrete mux "delayed-not-lost" demo for the channel-level `Priᶜ`.
--
-- Two ⊤-channels: `hi` (BlockFetch-analogue) dominates `lo` (LeiosFetch).
-- On the interleaving `P ⦀ Q` of a high-priority peer `P = hi→Stop` and a
-- low-priority peer `Q = lo→Stop`:
--   * `Priᶜ` KEEPS `hi` (maximal) and PRUNES `lo` (its dominator `hi` is
--     concurrently offered — both peers compete);
--   * after `hi` fires the (solo) step `P ⦀ Q ─[hi]─► Stop ⦀ Q`, interleaving
--     leaves the `lo` peer `Q` UNTOUCHED, so `Stop ⦀ Q` still offers `lo`; now
--     `hi` is gone from the offer support, so `Priᶜ` RE-OFFERS `lo`.
-- (2)+(4) together are delayed-not-lost: `lo` was suppressed by contention while
-- `hi` competed, and re-offered once the `hi` step cleared it.  (3)+(4) mirror
-- the generic `priᶜ-mux-reappears` (CSP/PriorityCMuxDelayed.agda): interleaving
-- keeps `Q`, so `lo` persists across the `hi` step.
--
-- On these CONCRETE finite processes `dominatedᶜ?` COMPUTES, so every fact is by
-- direct reduction — no `ExactSupp` needed for (1)-(4).
--
-- STARVATION CAVEAT: this is single-step reappearance, not eventual delivery.
-- If `P` kept re-offering `hi` at every reachable state, `lo` would stay pruned
-- forever; "eventually offered" needs a fairness/drain hypothesis (out of scope).
--
-- `--safe`, 0 postulates, no `dne`.
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; Σ-syntax)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Function using (case_of_)

open import Process_Trees

module CSP.Examples.priority.MuxDelayedExample where

-- event alphabet: high-priority `hi`, low-priority `lo` (both ⊤-carried)
data Ch : Set → Set where
  hi : Ch ⊤
  lo : Ch ⊤

-- decidable equality on the (channel) events
Ch-≟ : (x y : AnyTypes Ch) → Dec (x ≡ y)
Ch-≟ (_ , hi) (_ , hi) = yes refl
Ch-≟ (_ , lo) (_ , lo) = yes refl
Ch-≟ (_ , hi) (_ , lo) = no λ ()
Ch-≟ (_ , lo) (_ , hi) = no λ ()

open import Semantics.PriOrderC {0ℓ} {0ℓ} {Ch}
open import Semantics.LTS       {E = Ch} {I = ExtI Ch}
open import Semantics.Refusals  {E = Ch} {I = ExtI Ch} using (Offers)
open import CSP.Priority.Base        {0ℓ} {0ℓ} {Ch} using (FinBr)
open import CSP.Priority.Closure Ch-≟
open import CSP.Priority.Channel Ch-≟
open import CSP.Operators Ch-≟

------------------------------------------------------------------------
-- The priority order  lo <ᶜ hi  (hi dominates lo).
------------------------------------------------------------------------

-- strict channel order: only `lo ◃ᶜ hi`
_◃ᶜ_ : AnyTypes Ch → AnyTypes Ch → Set
(_ , lo) ◃ᶜ (_ , hi) = ⊤
_        ◃ᶜ _        = ⊥

◃ᶜ-irrefl : ∀ {c} → ¬ (c ◃ᶜ c)
◃ᶜ-irrefl {_ , hi} ()
◃ᶜ-irrefl {_ , lo} ()

◃ᶜ-trans : ∀ {x y z} → x ◃ᶜ y → y ◃ᶜ z → x ◃ᶜ z
◃ᶜ-trans {_ , hi}              ()
◃ᶜ-trans {_ , lo} {_ , lo}     ()
◃ᶜ-trans {_ , lo} {_ , hi}  _  ()

-- dominating CHANNELS: `aboveᶜ lo = [hi]`, `hi` maximal
aboveᶜ′ : AnyTypes Ch → List (AnyTypes Ch)
aboveᶜ′ (_ , lo) = (⊤ , hi) ∷ []
aboveᶜ′ _        = []

aboveᶜ′-sound : ∀ {c c′} → c′ ∈ aboveᶜ′ c → c ◃ᶜ c′
aboveᶜ′-sound {_ , lo} (here refl) = tt
aboveᶜ′-sound {_ , hi} ()

aboveᶜ′-complete : ∀ {c c′} → c ◃ᶜ c′ → c′ ∈ aboveᶜ′ c
aboveᶜ′-complete {_ , lo} {_ , hi} _ = here refl

-- the dominating channel `hi` is inhabited (carries ⊤); others vacuous
aboveᶜ′-inhabited : ∀ {c c′} → c′ ∈ aboveᶜ′ c → proj₁ c′
aboveᶜ′-inhabited {_ , lo} (here refl) = tt
aboveᶜ′-inhabited {_ , hi} ()

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
-- The two interleaved peers and their certificates.
------------------------------------------------------------------------

-- high-priority peer P offers `hi`, low-priority peer Q offers `lo`
P Q : PTree Ch (ExtI Ch) (⊤ {0ℓ})
P = hi ⟶₀ Stop
Q = lo ⟶₀ Stop

fbP : FinBr P
fbP = finBr-prefix₀ finBr-Stop
fbQ : FinBr Q
fbQ = finBr-prefix₀ finBr-Stop

-- certificate for the running mux `P ⦀ Q` and for the post-`hi` state `Stop ⦀ Q`
fb : FinBr (P ⦀ Q)
fb = finBr-⦀ fbP fbQ
fb′ : FinBr (Stop ⦀ Q)
fb′ = finBr-⦀ finBr-Stop fbQ

------------------------------------------------------------------------
-- The two visible labels.
------------------------------------------------------------------------

-- the high-priority label `hi`
ℓhi : Event√ (⊤ {0ℓ})
ℓhi = evl (evLabel ⊤ hi tt)

-- the low-priority label `lo`
ℓlo : Event√ (⊤ {0ℓ})
ℓlo = evl (evLabel ⊤ lo tt)

------------------------------------------------------------------------
-- The delayed-not-lost story (all by direct reduction).
------------------------------------------------------------------------

-- (1) `hi` (maximal) survives prioritisation
mux-keeps-hi : Offers (Priᶜ O (P ⦀ Q) fb) ℓhi
mux-keeps-hi = _ , sVis refl refl

-- (2) `lo` is pruned: its dominator `hi` is concurrently offered (both peers compete)
mux-prunes-lo : ¬ Offers (Priᶜ O (P ⦀ Q) fb) ℓlo
mux-prunes-lo (_ , sVis {v = v} eqf br) with react-injective eqf
... | veq , _ = case subst (λ w → w (⊤ , lo) tt ≡ just _) (sym veq) br of λ ()

-- (3) the high-priority (solo) step fires: P advances to Stop, Q stays intact
hi-fires : (P ⦀ Q) ─[ ev ℓhi ]─► (Stop ⦀ Q)
hi-fires = sVis refl refl

-- (4) at `Stop ⦀ Q` the offer support is just `[lo]` (hi gone), so `Priᶜ` re-offers `lo`
mux-lo-reappears : Offers (Priᶜ O (Stop ⦀ Q) fb′) ℓlo
mux-lo-reappears = _ , sVis refl refl

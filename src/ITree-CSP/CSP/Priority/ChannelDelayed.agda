{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- "DELAYED-NOT-LOST" for the channel-level priority operator `Priᶜ`
-- (operator-level; the mux is an instance).
--
-- Priᶜ's visible offers are EXACTLY the underlying tree's UNCONTENDED genuine
-- offers: nothing is invented, and an offer is dropped ONLY while a strict
-- dominator is concurrently offered.  Writing
--   `dom t e := Σ[ b ] (e <ᵖ b) × Offers t b`   -- a live strict dominator of e
-- we prove, at a STABLE node:
--   (1) no-invent      : Priᶜ offers e ⇒ t offers e                (soundness)
--   (2) keep-uncontended : t offers e ∧ ¬ dom t e ⇒ Priᶜ offers e   (needs ExactSupp)
--   (3) prune⇒contended  : t offers e ∧ Priᶜ refuses e ⇒ dom t e    (needs ExactSupp)
--   char : Priᶜ offers e  ⟺  (t offers e ∧ ¬ dom t e)
--   (4) reappears        : after a (dominating) step fires, if e is STILL offered
--       at t′ and now uncontended there, Priᶜ offers it again.
--
-- SO: a lower-priority offer (e.g. LeiosFetch) is refused ONLY while a strict
-- dominator (e.g. BlockFetch) is concurrently offered, and it REAPPEARS once the
-- dominator's step clears the contention.  (The persistence hypothesis
-- `Offers t′ e` in (4) is what interleaving `⦀` supplies for the mux; we do NOT
-- prove ⦀-persistence here.)
--
-- STARVATION CAVEAT (honest boundary): EVENTUAL delivery is NOT proved and is
-- genuinely gated.  If a dominator is offered at EVERY reachable state
-- (saturating high-priority traffic) the offer is suppressed forever — starvation.
-- "Eventually offered" needs a fairness/drain hypothesis (that some reachable
-- state has `¬ dom`); that is out of scope and is NOT proved unconditionally.
--
-- `--safe`, 0 postulates, no `dne`/`Classical`.  Reuses the `CSP.Priority.ChannelAdequacy`
-- bridges (`liftC`, `ExactSupp`, `domᶜ-false→premise`, `domᶜ-true→dominator`,
-- `premise→domᶜ-false`, the `fPriᶜ`/`priVisAtᶜ` inversions) — nothing re-derived.
------------------------------------------------------------------------

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Priority.ChannelDelayed {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import Semantics.PriOrder  {ℓ} {ℓe} {E} using (Ev; _∙_; PriOrderProp)
open import Semantics.PriOrderC {ℓ} {ℓe} {E}
open import Semantics.LTS       {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Refusals  {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E} using (Offers)
open import CSP.Priority.Base        {ℓ} {ℓe} {E} using (FinBr; stab?)
open import CSP.Priority.Channel E-≟
open import CSP.Priority.ChannelAdequacy E-≟
open import CSP.Priority.Adequacy {ℓ} {ℓe} {E} using (offers→just; just→offers)
import Semantics.PriLTS

module _ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo) where
  private
    module Spec = Semantics.PriLTS
                    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {ℓo} {E} {ExtI E} (liftC O)
  open PriOrderProp (liftC O) using (_<ᵖ_)

  ----------------------------------------------------------------------
  -- Contention predicate.
  ----------------------------------------------------------------------

  -- `dom t e`: some strict dominator of `e` is concurrently offered by `t`
  dom : PTree E (ExtI E) R → Event → Set (lsuc ℓ ⊔ ℓe ⊔ ℓo ⊔ ℓr)
  dom t e = Σ[ b ∈ Ev ] ((Spec.evToEv e) <ᵖ b) × Offers t (evl (Spec.evOfEv b))

  ----------------------------------------------------------------------
  -- (1) NO-INVENT (soundness): every `Priᶜ` offer is a genuine `t` offer.
  ----------------------------------------------------------------------

  -- invert the `Priᶜ` visible step through the node-view to the underlying offer
  priᶜ-no-invent : {t : PTree E (ExtI E) R} {fb : FinBr t}
                   {B : Set ℓ} {eb : E B} {ab : B}
                 → Offers (Priᶜ O t fb) (evl (evLabel B eb ab))
                 → Offers t (evl (evLabel B eb ab))
  priᶜ-no-invent {t = t} {fb = fb} {B} {eb} {ab} offer with PTree.force t in eqft
  ... | ret r with offer
  ...   | (u′ , sVis eqP br) = case trans (sym eqP) (fPriᶜ-ret O eqft) of λ ()
  priᶜ-no-invent {t = t} {fb = fb} {B} {eb} {ab} offer | sil c with offer
  ...   | (u′ , sVis eqP br) = case trans (sym eqP) (proj₂ (fPriᶜ-sil O {fb = fb} eqft)) of λ ()
  priᶜ-no-invent {t = t} {fb = fb} {B} {eb} {ab} offer | react v τc
    with fPriᶜ-react O {fb = fb} eqft | offer
  ...   | inj₁ (st , eqf , peq) | (u′ , sVis eqP br) =
          let (_ , _ , eva , _) = priVisAtᶜ-just O eqf {fb = fb}
                                    (dominatedᶜ? O fb (B , eb)) refl (v (B , eb) ab) refl
                                    (subst (λ w → w (B , eb) ab ≡ just u′)
                                           (proj₁ (react-injective (trans (sym eqP) peq))) br)
          in just→offers eqf eva
  ...   | inj₂ (¬st , eqf , peq) | (u′ , sVis eqP br) =
          let (_ , _ , eva , _) = priMaxAtᶜ-just O eqf {fb = fb}
                                    (isMaxᶜ? O (B , eb)) refl (v (B , eb) ab) refl
                                    (subst (λ w → w (B , eb) ab ≡ just u′)
                                           (proj₁ (react-injective (trans (sym eqP) peq))) br)
          in just→offers eqf eva

  ----------------------------------------------------------------------
  -- `Priᶜ` offers ⇒ uncontended (COMPLETENESS via `domᶜ-false→premise`; no ExactSupp).
  ----------------------------------------------------------------------

  -- a surviving offer is uncontended: no strict dominator is concurrently offered
  priᶜ-offer→¬dom : {t : PTree E (ExtI E) R} {fb : FinBr t}
                    {B : Set ℓ} {eb : E B} {ab : B}
                  → isStable t
                  → Offers (Priᶜ O t fb) (evl (evLabel B eb ab))
                  → ¬ dom t (evLabel B eb ab)
  -- (`eqft` is recovered from `priᶜ-no-invent` — avoids a `with force t` that
  -- would reduce the `isStable t` hypothesis into a stuck neutral)
  priᶜ-offer→¬dom {t = t} {fb = fb} {B} {eb} {ab} st offer
    with priᶜ-no-invent offer
  ... | (_ , sVis {v = v} eqft _) with fPriᶜ-react O {fb = fb} eqft | offer
  ...   | inj₂ (¬st , _ , _) | _ = ⊥-elim (¬st st)
  ...   | inj₁ (_ , eqf , peq) | (u′ , sVis eqP br) =
          let (_ , dmfalse , _ , _) = priVisAtᶜ-just O eqf {fb = fb}
                                        (dominatedᶜ? O fb (B , eb)) refl (v (B , eb) ab) refl
                                        (subst (λ w → w (B , eb) ab ≡ just u′)
                                               (proj₁ (react-injective (trans (sym eqP) peq))) br)
          in λ { (b , lt , off) →
                   domᶜ-false→premise O {fb = fb} {at = (B , eb)} {a = ab} eqf dmfalse b lt off }

  ----------------------------------------------------------------------
  -- (2) KEEP-UNCONTENDED: an uncontended genuine offer survives (needs ExactSupp).
  ----------------------------------------------------------------------

  -- at a stable node, `t offers e` + no live dominator ⇒ `Priᶜ` keeps `e`
  priᶜ-keep-uncontended : {t : PTree E (ExtI E) R} {fb : FinBr t}
                          {B : Set ℓ} {eb : E B} {ab : B}
                        → isStable t → ExactSupp fb
                        → Offers t (evl (evLabel B eb ab)) → ¬ dom t (evLabel B eb ab)
                        → Offers (Priᶜ O t fb) (evl (evLabel B eb ab))
  priᶜ-keep-uncontended {t = t} {fb = fb} {B} {eb} {ab} st es (t′ , sVis {v = v} eqft br) ¬d
    with fPriᶜ-react O {fb = fb} eqft
  ... | inj₂ (¬st , _ , _) = ⊥-elim (¬st st)
  ... | inj₁ (_ , eqf , peq) =
        let prem : ∀ b → ((B , eb) ∙ ab) <ᵖ b → ¬ Offers t (evl (Spec.evOfEv b))
            prem b lt off = ¬d (b , lt , off)
            dmfalse = premise→domᶜ-false O {fb = fb} {at = (B , eb)} {a = ab} es eqf prem
            (eva , vfire) = priVisAtᶜ-fires O eqf {fb = fb}
                              (dominatedᶜ? O fb (B , eb)) refl (v (B , eb) ab) refl dmfalse br
        in just→offers peq vfire

  ----------------------------------------------------------------------
  -- (3) PRUNE⇒CONTENDED: a pruned genuine offer ALWAYS has a live dominator.
  ----------------------------------------------------------------------

  -- at a stable node, `t offers e` but `Priᶜ` refuses it ⇒ `e` is contended
  priᶜ-prune⇒contended : {t : PTree E (ExtI E) R} {fb : FinBr t}
                         {B : Set ℓ} {eb : E B} {ab : B}
                       → isStable t → ExactSupp fb
                       → Offers t (evl (evLabel B eb ab))
                       → ¬ Offers (Priᶜ O t fb) (evl (evLabel B eb ab))
                       → dom t (evLabel B eb ab)
  priᶜ-prune⇒contended {t = t} {fb = fb} {B} {eb} {ab} st es (t′ , sVis {v = v} eqft br) ¬off
    with fPriᶜ-react O {fb = fb} eqft
  ... | inj₂ (¬st , _ , _) = ⊥-elim (¬st st)
  ... | inj₁ (_ , eqf , peq) with dominatedᶜ? O fb (B , eb) in domeq
  ...   | true  = domᶜ-true→dominator O {a = ab} es eqf domeq
  ...   | false = let (eva , vfire) = priVisAtᶜ-fires O eqf {fb = fb}
                                        (dominatedᶜ? O fb (B , eb)) refl (v (B , eb) ab) refl domeq br
                  in ⊥-elim (¬off (just→offers peq vfire))

  ----------------------------------------------------------------------
  -- CHARACTERIZATION: `Priᶜ` offers = uncontended genuine offers (stable node).
  ----------------------------------------------------------------------

  -- `Priᶜ offers e  ⟺  (t offers e ∧ ¬ dom t e)`
  priᶜ-offer-char : {t : PTree E (ExtI E) R} {fb : FinBr t}
                    {B : Set ℓ} {eb : E B} {ab : B}
                  → isStable t → ExactSupp fb
                  → (Offers (Priᶜ O t fb) (evl (evLabel B eb ab))
                       → Offers t (evl (evLabel B eb ab)) × ¬ dom t (evLabel B eb ab))
                  × ((Offers t (evl (evLabel B eb ab)) × ¬ dom t (evLabel B eb ab))
                       → Offers (Priᶜ O t fb) (evl (evLabel B eb ab)))
  priᶜ-offer-char st es =
      (λ o → priᶜ-no-invent o , priᶜ-offer→¬dom st o)
    , (λ { (o , ¬d) → priᶜ-keep-uncontended st es o ¬d })

  ----------------------------------------------------------------------
  -- (4) REAPPEARS (dynamic "delayed"): after a step clears the contention, the
  -- pruned offer returns (direct corollary of (2) at `t′`; the step is context).
  ----------------------------------------------------------------------

  -- once the dominating step fires and `e` is still offered & uncontended at `t′`,
  -- `Priᶜ` offers `e` again — nothing was lost, only delayed
  priᶜ-reappears : {t t′ : PTree E (ExtI E) R} {fb′ : FinBr t′}
                   {B : Set ℓ} {eb : E B} {ab : B} {lb : Event}
                 → t ─[ ev (evl lb) ]─► t′
                 → isStable t′ → ExactSupp fb′
                 → Offers t′ (evl (evLabel B eb ab)) → ¬ dom t′ (evLabel B eb ab)
                 → Offers (Priᶜ O t′ fb′) (evl (evLabel B eb ab))
  priᶜ-reappears _ st es o ¬d = priᶜ-keep-uncontended st es o ¬d

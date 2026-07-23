{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- END-TO-END mux "delayed-not-lost": interleaving offer-persistence
-- (`⦀-offer-R`) chained into `Priᶜ`'s reappearance (`priᶜ-reappears`).
--
-- Concrete payoff for the mux (`Priᶜ` over an interleaving `P ⦀ Q` of a
-- high-priority peer `P` = BlockFetch and a low-priority peer `Q` = LeiosFetch):
-- while BlockFetch's event `hi` competed, `Priᶜ` pruned LeiosFetch's `lo`.  After
-- BlockFetch takes its (solo) step `P ⦀ Q ─[hi]─► P′ ⦀ Q`, the LeiosFetch peer
-- `Q` is UNTOUCHED by interleaving, so it STILL offers `lo` (`⦀-offer-R`); if the
-- new state is now uncontended for `lo`, `Priᶜ` RE-OFFERS it.  Nothing was lost —
-- only delayed by contention.
--
-- STARVATION CAVEAT (unchanged): this is single-step reappearance, NOT eventual
-- delivery.  If BlockFetch is offered at every reachable state (saturating
-- high-priority traffic) `lo` stays suppressed forever; "eventually offered"
-- needs a fairness/drain hypothesis (a reachable state with `¬ dom`), which is
-- out of scope and NOT proved here.
--
-- `--safe`, 0 postulates, no `dne`/`Classical`.
------------------------------------------------------------------------

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Priority.MuxDelayed {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import Semantics.PriOrderC {ℓ} {ℓe} {E}
open import Semantics.LTS       {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Refusals  {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E} using (Offers)
open import CSP.Priority.Base        {ℓ} {ℓe} {E} using (FinBr)
open import CSP.Priority.Channel E-≟ using (Priᶜ)
open import CSP.Priority.ChannelAdequacy E-≟ using (ExactSupp)
open import CSP.Priority.ChannelDelayed E-≟ using (dom; priᶜ-reappears)
open import CSP.Operators E-≟ using (_⦀_)
open import CSP.Laws.Traces.ParInterleaveOffers E-≟ using (⦀-offer-R)

-- mux reappearance: after the high-priority peer steps solo, the untouched
-- low-priority peer `Q` still offers `lo`, so `Priᶜ` re-offers it once uncontended
priᶜ-mux-reappears : ∀ {ℓo ℓr} (O : PriOrderC ℓo)
    {P P′ Q : PTree E (ExtI E) (⊤ {ℓr})} {fb′ : FinBr (P′ ⦀ Q)}
    {Xhi : Set ℓ} {hi : E Xhi} {ahi : Xhi}
    {Xlo : Set ℓ} {lo : E Xlo} {alo : Xlo}
  → (P ⦀ Q) ─[ ev (evl (evLabel Xhi hi ahi)) ]─► (P′ ⦀ Q)     -- BlockFetch steps solo
  → Offers Q (evl (evLabel Xlo lo alo))                        -- LeiosFetch peer still offers lo
  → isStable (P′ ⦀ Q) → ExactSupp fb′
  → ¬ dom O (P′ ⦀ Q) (evLabel Xlo lo alo)                      -- now uncontended for lo
  → Offers (Priᶜ O (P′ ⦀ Q) fb′) (evl (evLabel Xlo lo alo))
priᶜ-mux-reappears O step offQ st es ¬d =
  priᶜ-reappears O step st es (⦀-offer-R offQ) ¬d

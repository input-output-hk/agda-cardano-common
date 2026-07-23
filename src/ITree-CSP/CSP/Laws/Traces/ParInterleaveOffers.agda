{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Interleaving OFFER-PERSISTENCE for `_⦀_` (= `Par ∅ES`).
--
-- Since the synchronisation set is empty, each operand's visible offers survive
-- into `P ⦀ Q` regardless of the other operand: one side moves solo (and, when
-- BOTH sides happen to offer the same event, the interleaving `⊓`-overlap still
-- offers it).  So:
--   `⦀-offer-R : Offers Q e → Offers (P ⦀ Q) e`   (Q's offers persist)
--   `⦀-offer-L : Offers P e → Offers (P ⦀ Q) e`   (P's offers persist)
-- These are the reusable core behind the mux "delayed-not-lost" reappearance:
-- an untouched interleaved peer keeps offering its event across the other peer's
-- steps.
--
-- Built from the existing `Par-soloL`/`Par-soloR` intro lemmas (idle side does
-- not offer the event) plus a tiny both-offer reduction of `par-pVis`.
--
-- `--safe`, 0 postulates, no `dne`/`Classical`.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Data.Product using (Σ; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.Traces.ParInterleaveOffers {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟ using (Par; _⦀_; ∅ES; par-pVis; viewV)
open import Semantics.LTS      {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Refusals {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E} using (Offers)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-soloL; Par-soloR; fPar-nn)

------------------------------------------------------------------------
-- both-offer reduction: when BOTH sides offer the event, `par-pVis` (at ∅ES)
-- fires to the interleaving overlap node — so there IS a successor.
------------------------------------------------------------------------

-- `par-pVis` at the empty sync set with both sides offering ⇒ a `just` successor
par-pVis-both : ∀ {ℓr} {P Q : PTree E (ExtI E) (⊤ {ℓr})}
                {vP τcP vQ τcQ} {X : Set ℓ} {ex : E X} {a : X} {P′ Q′}
              → vP (X , ex) a ≡ just P′ → vQ (X , ex) a ≡ just Q′
              → Σ[ t′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
                  par-pVis ∅ES (λ _ _ → tt) (react vP τcP) (react vQ τcQ) P Q (X , ex) a ≡ just t′
par-pVis-both brP brQ rewrite brP | brQ = _ , refl

------------------------------------------------------------------------
-- Offer-persistence.
------------------------------------------------------------------------

-- Q's visible offers survive into `P ⦀ Q` (Q moves solo, or both-offer overlap)
⦀-offer-R : ∀ {ℓr} {P Q : PTree E (ExtI E) (⊤ {ℓr})}
            {X : Set ℓ} {ex : E X} {a : X}
          → Offers Q (evl (evLabel X ex a)) → Offers (P ⦀ Q) (evl (evLabel X ex a))
⦀-offer-R {P = P} {Q} {X} {ex} {a} (Q′ , sVis {v = vQ} {τc = τcQ} eqQ brQ)
  with PTree.force P in eqP
  -- P terminated / silent / not offering ⇒ Q solo
... | ret r  = Par ∅ES (λ _ _ → tt) P Q′
             , Par-soloR ∅ES (λ _ _ → tt) P Q (λ ()) (sVis eqQ brQ)
                 (subst (λ n → viewV n (X , ex) a ≡ nothing) (sym eqP) refl)
... | sil P″ = Par ∅ES (λ _ _ → tt) P Q′
             , Par-soloR ∅ES (λ _ _ → tt) P Q (λ ()) (sVis eqQ brQ)
                 (subst (λ n → viewV n (X , ex) a ≡ nothing) (sym eqP) refl)
... | react vP τcP with vP (X , ex) a in vpeq
  -- P offers nothing at this event ⇒ Q solo
...   | nothing = Par ∅ES (λ _ _ → tt) P Q′
               , Par-soloR ∅ES (λ _ _ → tt) P Q (λ ()) (sVis eqQ brQ)
                   (subst (λ n → viewV n (X , ex) a ≡ nothing) (sym eqP) vpeq)
  -- both sides offer ⇒ interleaving overlap still offers it
...   | just P′ = let (t′ , eqbr) = par-pVis-both {vP = vP} {τcP} {vQ} {τcQ} vpeq brQ
                  in t′ , sVis (fPar-nn ∅ES (λ _ _ → tt) eqP eqQ U.tt U.tt) eqbr

-- P's visible offers survive into `P ⦀ Q` (symmetric)
⦀-offer-L : ∀ {ℓr} {P Q : PTree E (ExtI E) (⊤ {ℓr})}
            {X : Set ℓ} {ex : E X} {a : X}
          → Offers P (evl (evLabel X ex a)) → Offers (P ⦀ Q) (evl (evLabel X ex a))
⦀-offer-L {P = P} {Q} {X} {ex} {a} (P′ , sVis {v = vP} {τc = τcP} eqP brP)
  with PTree.force Q in eqQ
... | ret r  = Par ∅ES (λ _ _ → tt) P′ Q
             , Par-soloL ∅ES (λ _ _ → tt) P Q (λ ()) (sVis eqP brP)
                 (subst (λ n → viewV n (X , ex) a ≡ nothing) (sym eqQ) refl)
... | sil Q″ = Par ∅ES (λ _ _ → tt) P′ Q
             , Par-soloL ∅ES (λ _ _ → tt) P Q (λ ()) (sVis eqP brP)
                 (subst (λ n → viewV n (X , ex) a ≡ nothing) (sym eqQ) refl)
... | react vQ τcQ with vQ (X , ex) a in vqeq
...   | nothing = Par ∅ES (λ _ _ → tt) P′ Q
               , Par-soloL ∅ES (λ _ _ → tt) P Q (λ ()) (sVis eqP brP)
                   (subst (λ n → viewV n (X , ex) a ≡ nothing) (sym eqQ) vqeq)
...   | just Q′ = let (t′ , eqbr) = par-pVis-both {vP = vP} {τcP} {vQ} {τcQ} brP vqeq
                  in t′ , sVis (fPar-nn ∅ES (λ _ _ → tt) eqP eqQ U.tt U.tt) eqbr

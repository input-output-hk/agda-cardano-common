{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Priority Laws: the Layer-2 executable priority operator `Pri`
-- (`CSP.Priority.Base`) applied to a slide / timeout node `P ▷ Q`
-- (`CSP.Operators`), up to STRONG bisimulation (`Semantics.Bisim._∼_`).
--
-- A slide `P ▷ Q` is a `react` node that offers ALL of P's visible events
-- (`viewV`) TOGETHER WITH an always-enabled timeout τ (→ Q) plus P's own
-- τ's sliding on (→ P′ ▷ Q); it is therefore NEVER stable.  Three laws:
--
--   (1) STEP LAW  `pri-▷-step`: when P reacts, `Pri` on the (unstable) slide
--       reduces to `priMax`-pruned root offers (only ≤-maximal survive) plus
--       `priTau` over the slide's τ-map (P's τ's + timeout).
--   (2) URGENT-TIMEOUT `pri-▷-urgent`: if P is stable and EVERY root offer is
--       non-maximal, `priMax` prunes them all, so the sole surviving τ is the
--       timeout — hence `Pri O (P ▷ Q) … ∼ τ→ (Pri O Q …)`.
--   (3) PERSISTENCE  `pri-▷-persist`: a ≤-maximal root offer of P survives `Pri`
--       unchanged (`Pri O (P ▷ Q) …` still Offers it).
--
-- `--safe`, 0 postulates, nothing from `Classical`/`dne`, no `NON_TERMINATING`.
-- All `Pri` node-view / firing / inversion lemmas are reused from
-- `CSP.Priority.Adequacy`; the slide force-equation from `CSP.Laws.Traces`;
-- FinBr-irrelevance (differing certificates ⇒ `∼`) from `pri-cong`
-- (`CSP.Priority.Laws.Cong`).  No corecursion of our own — every residual is
-- closed by a finished lemma (`pri-cong`), so guardedness is trivial.
------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Function using (case_of_)

open import Process_Trees
open PTree

module CSP.Priority.Laws.Slide {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import Semantics.PriOrder {ℓ} {ℓe} {E}
open import Semantics.LTS      {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Bisim    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Refusals {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E} using (Offers)
open import CSP.Priority.Base          {ℓ} {ℓe} {E}
open import CSP.Priority.Adequacy  {ℓ} {ℓe} {E}
open import CSP.Priority.Tau       {ℓ} {ℓe} {E} using (τ→_)
open import CSP.Priority.Laws.Cong {ℓ} {ℓe} {E} using (pri-cong; nothing≢just; stable-react-τc)
open import CSP.Operators        E-≟
open import CSP.Priority.Closure  E-≟ using (finBr-▷)
open import CSP.Laws.Traces.TraceLaws              E-≟ using (force-▷-react)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (▷-slide-elim)

------------------------------------------------------------------------
-- The slide's always-enabled timeout τ (cf. `finBr-▷`'s instability witness):
-- at the index `(pair fin fin)` with value `(lift fzero , lift fzero)` the
-- `▷-slide` map fires unconditionally to `Q`.
------------------------------------------------------------------------

-- the timeout τ-index of a slide node
timeout-i : AnyTypes (ExtI E)
timeout-i = (Lift ℓ (Fin 1) × Lift ℓ (Fin 1)) , pair fin fin

-- its (unique) value
timeout-a : proj₁ timeout-i
timeout-a = lift fzero , lift fzero

-- the timeout branch of a react-headed slide fires to `Q`
slide-timeout-eq : ∀ {ℓr} {R : Set ℓr}
    {vP  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
    {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
    {Q : PTree E (ExtI E) R}
  → ▷-slide (react vP τcP) Q timeout-i timeout-a ≡ just Q
slide-timeout-eq = refl

------------------------------------------------------------------------
-- (1) STEP LAW.
--
-- `force P ≡ react vP τcP` ⇒ `force (P ▷ Q) ≡ react vP (▷-slide (react vP τcP) Q)`
-- (via `force-▷-react`), and since `P ▷ Q` is UNSTABLE, `Pri` reduces through the
-- `priMax` (offers) / `priTau` (τ's) clauses.  We obtain both equations from
-- `fPri-react`; its stable (`inj₁`) alternative is refuted by the timeout τ.
--
-- NOTE (regression): this COMPOSES with the existing slide-step machinery in
-- `CSP.Laws.Traces` (`force-▷-react`, `▷-slide-elim`, `▷-τ-elim`, `▷-ev-elim`);
-- it re-uses those inversions rather than re-proving any slide-step lemma.
------------------------------------------------------------------------

-- `Pri` on a react-headed slide = pruned-to-maximal offers + prioritised τ-map
pri-▷-step : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
               {P Q : PTree E (ExtI E) R} (fp : FinBr P) (fq : FinBr Q)
               {vP  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             → PTree.force P ≡ react vP τcP
             → Σ[ eqf ∈ PTree.force (P ▷ Q) ≡ react vP (▷-slide (react vP τcP) Q) ]
                 PTree.force (Pri O (P ▷ Q) (finBr-▷ fp fq))
                   ≡ react (priMax O vP eqf (finBr-▷ fp fq))
                           (priTau O (▷-slide (react vP τcP) Q) eqf (finBr-▷ fp fq))
pri-▷-step O {P = P} {Q = Q} fp fq {vP = vP} {τcP = τcP} eqP
  with fPri-react O {t = P ▷ Q} {fb = finBr-▷ fp fq} (force-▷-react {P = P} {Q = Q} eqP)
... | inj₂ (¬st , eqf , peq) = eqf , peq
-- stable is impossible: the timeout τ is always enabled at a react-headed slide
... | inj₁ (st , eqf , _) =
      ⊥-elim (nothing≢just
                (trans (sym (isStable-react O {t = P ▷ Q} eqf st timeout-i timeout-a))
                       (slide-timeout-eq {vP = vP} {τcP = τcP} {Q = Q})))

------------------------------------------------------------------------
-- (2) URGENT TIMEOUT.
--
-- P stable + every root offer non-maximal ⇒ `priMax` empties the visible menu,
-- P's own τ's are absent (stability), so the ONLY τ's are timeouts (→ Q); the
-- prioritised slide is thus `∼` a single τ to `Pri O Q fq`.  The proof is a
-- single-step bisimulation (no corecursion): visible steps are refuted, and the
-- timeout residuals `Pri O Q (FinBr.next …)` match `Pri O Q fq` via `pri-cong`
-- (FinBr-irrelevance: differing stability certificates give `∼` processes).
------------------------------------------------------------------------

-- prioritised urgent slide collapses to a τ before `Pri O Q fq`
pri-▷-urgent : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
                 {P Q : PTree E (ExtI E) R} (fp : FinBr P) (fq : FinBr Q)
                 {vP  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                 {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
               → PTree.force P ≡ react vP τcP
               → isStable P
               → (∀ at a t′ → vP at a ≡ just t′ → isMax? O (at ∙ a) ≡ false)
               → Pri O (P ▷ Q) (finBr-▷ fp fq) ∼ (τ→ (Pri O Q fq))
pri-▷-urgent {R = R} O {P} {Q} fp fq {vP} {τcP} eqP stableP nonmax
  with pri-▷-step O fp fq eqP
... | eqf , peq = bis
  where
  fb : FinBr (P ▷ Q)
  fb = finBr-▷ fp fq

  -- LHS is simulated by the single-τ RHS
  fwd : SSimF (Sbisim R) (Pri O (P ▷ Q) fb) (τ→ (Pri O Q fq))
  -- no √-step: `Pri` on the slide reacts (peq), it does not `ret`
  fwd .SSimF.on-ev (sRet eqL) = case trans (sym peq) eqL of λ ()
  -- no visible step: every survivor of `priMax` would be ≤-maximal, but all are non-maximal
  fwd .SSimF.on-ev (sVis {at = at} {a = a} eqL br)
    with priMaxAt-just O {t = P ▷ Q} eqf {fb = fb} (isMax? O (at ∙ a)) refl (vP at a) refl
           (subst (λ w → w at a ≡ just _)
                  (sym (proj₁ (react-injective (trans (sym peq) eqL)))) br)
  ... | tP′ , mxtrue , eva , _ = case trans (sym mxtrue) (nonmax at a tP′ eva) of λ ()
  -- no leading τ from `Pri`'s head being `sil` (the slide reacts)
  fwd .SSimF.on-tau (sSil eqL) = case trans (sym peq) eqL of λ ()
  -- every τ is a timeout (P's own τ's are absent by stability) ⇒ lands on `Pri O Q …`
  fwd .SSimF.on-tau (sTau {i = i} {a = a} eqL br)
    with priTauAt-just O {t = P ▷ Q} eqf {fb = fb} {i = i} {a = a} (▷-slide (react vP τcP) Q i a) refl
           (subst (λ w → w i a ≡ just _)
                  (sym (proj₂ (react-injective (trans (sym peq) eqL)))) br)
  ... | tP′ , eia , resid with ▷-slide-elim (react vP τcP) Q {i = i} {a = a} eia
  ...   | inj₁ refl =
            Pri O Q fq , sSil refl
              , subst (_∼ Pri O Q fq) resid
                  (pri-cong {O = O} (sbisim-refl Q) (FinBr.next fb (sTau eqf eia)) fq)
  ...   | inj₂ (j , a′ , P′ , veq , _) =
            case trans (sym (stable-react-τc {t = P} stableP eqP j a′)) veq of λ ()

  -- the single-τ RHS is simulated by LHS (via the timeout τ)
  bwd : SSimF (Sbisim R) (τ→ (Pri O Q fq)) (Pri O (P ▷ Q) fb)
  -- RHS (`sil`) has no visible steps
  bwd .SSimF.on-ev (sRet eqR)   = case eqR of λ ()
  bwd .SSimF.on-ev (sVis eqR _) = case eqR of λ ()
  -- RHS's leading τ is matched by LHS's timeout τ (→ Pri O Q (next …)), related by pri-cong
  bwd .SSimF.on-tau (sSil eqR) with sil-injective eqR
  ... | refl =
        Pri O Q (FinBr.next fb (sTau eqf eia₀)) , sTau {i = timeout-i} {a = timeout-a} peq tfire
          , pri-cong {O = O} (sbisim-refl Q) fq (FinBr.next fb (sTau eqf eia₀))
    where
    ft = priTauAt-fires O {t = P ▷ Q} eqf {fb = fb} {i = timeout-i} {a = timeout-a} {t′ = Q}
           (▷-slide (react vP τcP) Q timeout-i timeout-a) refl
           (slide-timeout-eq {vP = vP} {τcP = τcP} {Q = Q})
    eia₀ = proj₁ ft
    tfire = proj₂ ft

  bis : Pri O (P ▷ Q) fb ∼ (τ→ (Pri O Q fq))
  bis .Sbisim.fwd = fwd
  bis .Sbisim.bwd = bwd

------------------------------------------------------------------------
-- (3) MAXIMAL-OFFER PERSISTENCE.
--
-- A ≤-maximal root offer of P survives `Pri` on the (unstable) slide: `priMax`
-- keeps it (`priMaxAt-fires`), so `Pri O (P ▷ Q) …` still Offers that event.
------------------------------------------------------------------------

-- a maximal root offer of P is offered by `Pri O (P ▷ Q) …`
pri-▷-persist : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
                  {P Q : PTree E (ExtI E) R} (fp : FinBr P) (fq : FinBr Q)
                  {vP  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  {at : AnyTypes E} {a : proj₁ at} {p′ : PTree E (ExtI E) R}
                → PTree.force P ≡ react vP τcP
                → vP at a ≡ just p′
                → isMax? O (at ∙ a) ≡ true
                → Offers (Pri O (P ▷ Q) (finBr-▷ fp fq))
                         (evl (evLabel (proj₁ at) (proj₂ at) a))
pri-▷-persist O {P = P} {Q = Q} fp fq {vP = vP} {at = at} {a = a} {p′ = p′} eqP vjust mx
  with pri-▷-step O fp fq eqP
... | eqf , peq
    with priMaxAt-fires O {t = P ▷ Q} eqf {fb = finBr-▷ fp fq}
           (isMax? O (at ∙ a)) refl (vP at a) refl mx vjust
...   | eva , mfire =
        Pri O p′ (FinBr.next (finBr-▷ fp fq) (sVis eqf eva)) , sVis peq mfire

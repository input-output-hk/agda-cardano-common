{-# OPTIONS --guardedness #-}

-- Hide FAILURES-DIVERGENCES monotonicity.
--
-- We deliver TWO results:
--   • `Hide-mono-fail`     : the UNCONDITIONAL stable-failure transfer
--                            `P ⊑F⊥ Q → failures (Q ∖ A) s X → failures⊥ (P ∖ A) s X`.
--   • `Hide-mono-⊑FD-df`   : the headline law `(P ∖ A) ⊑FD (Q ∖ A)`, under the SIDE
--                            CONDITION that `Q ∖ A` is divergence-free.
--
-- ⚠ WHY THE UNCONDITIONAL LAW `P ⊑FD Q → (P ∖ A) ⊑FD (Q ∖ A)` IS FALSE.
-- Operationally, `divergences` is an *actual* infinite τ-path, whereas `⊑FD` only
-- constrains stable failures + divergences.  Take any `E` with an event of infinite
-- payload (e.g. `c : E ℕ`; the law quantifies over ALL `E`, so this single family
-- kills it).  Let `h` be a hidable event, and put:
--     Q = μX. h → X                       (so `Q ∖ {h}` DIVERGES: an infinite tag-1 τ-path)
--     P = ⊓ₙ (hⁿ ; STOP)                  (an infinitely-branching internal choice — a single
--                                           `react` node whose τ-branch map is `just` on an
--                                           ℕ-indexed family; expressible as a raw `PTree`).
-- Then `failures⊥ P ⊇ failures⊥ Q` (every `(hⁿ, X ∌ h)` failure of `Q` is matched by a
-- branch `m > n`; `P` only ADDS failures) and `divergences P = divergences Q = ∅`, hence
-- `P ⊑FD Q`.  But `P ∖ {h}` has NO infinite τ-path (each branch `hⁿ ; STOP` is finite;
-- infinite branching defeats König), so `(P ∖ {h}) ⊑D (Q ∖ {h})` FAILS — and via
-- divergence-chaos at `[]` even `(P′ ∖ {h}) ⊑F⊥ (Q ∖ {h})` fails for a `b`-offering variant
-- `P′`.  This is exactly the known unsoundness of the denotational N-model's hiding under
-- unbounded nondeterminism (Roscoe).  `modA-transfer` (DRCongruence) cannot rescue it — it
-- needs `≈DR`, not `⊑FD` — and NO dne-certified postulate can save a FALSE ∀-`E` statement.
-- Hence the divergence-freedom side condition below.  For trace-only needs the unconditional
-- `Hide-mono-⊑ᵀ` (CSP.Laws.Traces.TraceLawsHide) remains available.
--
-- CROSS-REFERENCE: this very pair is now formally shown NOT to be a failure simulation —
-- `CSP.Laws.FSim.HideCounterexample.¬fsim-Pinf-Qh` — which is why the OPERATIONAL hiding
-- congruence `CSP.Laws.FSim.HideCong.Hide-fsim` can afford to be unconditional.
--
-- ⚠ AND: `FinBr` (`Semantics.FinBr`) is NOT a repair.  Replacing the divergence-freedom
-- side condition by a finite-branching certificate `FinBr P` on the refining side does
-- NOT recover the law: `CSP.Laws.FD.HideMonoFinBrFail.finBr-Pinf` CONSTRUCTS `FinBr Pinf`
-- for the very `P = ⊓ₙ (hⁿ ; STOP)` above.  `FinBr` bounds only the VISIBLE channel
-- support (`chan-supp`), while the pathology here is τ-fan-out, which `FinBr` records
-- merely as a `Dec (isStable ·)`.
--
-- ZERO postulates in this module.  The only corecursion reused is `hide-Diverges-lift`
-- (from HideFD); everything here is structural.

open import Level using (Level; Lift; lift; lower)
open import Data.Maybe using (just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.FD.HideMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS      {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Offers; Refuses)
open import Semantics.Failures {E = E} {I = ExtI E} using (failures)
open import Semantics.DRImpliesFD {E = E} {I = ExtI E}
  using (stable-not-ret; stable-no-τ; nothing≢just)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊑F⊥_; _⊑D_; _⊑FD_; failures⊥; divergences; IsDivergence; div-extension-closed)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (HideTr; hnil; hkeep; hdrop; h√; heV; he√; Hide-ev-elim
        ; Hide-keep; Hide-hidden; hide-hTau-tag0-eq; fHide-ret; fHide-sil; fHide-react)
open import CSP.Laws.FD.HideFD E-≟
  using (Hide-failures-elim; Hide-failures-intro; Hide-div-intro; hide-Diverges-lift)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- ban-set retagging: extend `X` with ALL hidden (`A`-member) events; the `dec`-case
-- keeps the level at `ℓr` (yes ↦ polymorphic ⊤, no/√ ↦ the original ban).
-------------------------------------------------------------------------------------

-- `hideBan A X` bans, in addition to `X`, every visible event of `A`.
hideBan : (A : EventSet) → (Event√ R → Set ℓr) → (Event√ R → Set ℓr)
hideBan A X (evl (evLabel B e a)) with A .dec (B , e) a
... | yes _ = ⊤
... | no  _ = X (evl (evLabel B e a))
hideBan A X (√ r) = X (√ r)

-- build `hideBan A X (evl …)` for an `A`-member event (its yes-branch is `⊤`).
hideBan-yes : (A : EventSet) {X : Event√ R → Set ℓr}
              {B : Set ℓ} {e : E B} {a : B}
            → A .mem (B , e) a → hideBan A X (evl (evLabel B e a))
hideBan-yes A {B = B} {e = e} {a = a} c with A .dec (B , e) a
... | yes _ = tt
... | no ¬c = ⊥-elim (¬c c)

-- build `hideBan A X (evl …)` for a non-`A` event (its no-branch is `X`).
hideBan-no : (A : EventSet) {X : Event√ R → Set ℓr}
             {B : Set ℓ} {e : E B} {a : B}
           → ¬ A .mem (B , e) a → X (evl (evLabel B e a)) → hideBan A X (evl (evLabel B e a))
hideBan-no A {B = B} {e = e} {a = a} ¬c Xe with A .dec (B , e) a
... | yes c = ⊥-elim (¬c c)
... | no  _ = Xe

-------------------------------------------------------------------------------------
-- stability transfer between `P` and `P ∖ A`
-------------------------------------------------------------------------------------

-- if `P ∖ A` is stable then so is `P` (a τ / ret / sil of `P` would survive the hide).
-- After the `with`, the goal `isStable P` reduces to the `react` case's τ-map equation.
hide-stable-elim : (A : EventSet) (P : PTree E (ExtI E) R) → isStable (P ∖ A) → isStable P
hide-stable-elim A P st with PTree.force P in eqP
... | ret r      = ⊥-elim (lower st)
... | sil c      = ⊥-elim (lower st)
... | react v τc = τc-noth
      where
      -- `P ∖ A`'s τ-map (`hide-hTau A (react v τc)`) is everywhere nothing …
      st′ : ∀ (i : AnyTypes (ExtI E)) (a : proj₁ i) → hide-hTau A (react v τc) i a ≡ nothing
      st′ = st  -- in this branch `isStable (P ∖ A)` already reduces to this τ-map equation
      -- … which forces `P`'s own τ-map (read off tag0) to be everywhere nothing.
      τc-noth : ∀ (i : AnyTypes (ExtI E)) (a : proj₁ i) → τc i a ≡ nothing
      τc-noth (B , i′) a with τc (B , i′) a in teq
      ... | nothing  = refl
      ... | just P'' = ⊥-elim (nothing≢just
              (trans (sym (st′ ((Lift ℓ (Fin 2) × B) , pair fin i′) (lift fzero , a)))
                     (hide-hTau-tag0-eq A (react v τc) {iₚ = (B , i′)} {aₚ = a} teq)))

-- if `P′` is stable AND offers no `A`-member event, then `P′ ∖ A` is stable
-- (tag0 nothing by `P′`'s stability; tag1 nothing because no `A`-offer exists).
hide-stable-intro : (A : EventSet) (P′ : PTree E (ExtI E) R) → isStable P′
                  → (∀ {B : Set ℓ} {e : E B} {a : B}
                       → A .mem (B , e) a → ¬ Offers P′ (evl (evLabel B e a)))
                  → isStable (P′ ∖ A)
hide-stable-intro A P′ st noOff with PTree.force P′ in eqP
... | ret r      = ⊥-elim (lower st)
... | sil c      = ⊥-elim (lower st)
... | react v τc = hTau-noth
      where
      -- the tag1 emitter is nothing: an `A`-offer of `P′` would contradict `noOff`.
      hide-emit-noth : ∀ {B : Set ℓ} (i′ : ExtI E B) (a : B)
                     → hide-emit A (react v τc) i′ a ≡ nothing
      hide-emit-noth (base e) a with A .dec (_ , e) a
      ... | no _ = refl
      ... | yes csat with viewV (react v τc) (_ , e) a in veq
      ...   | nothing  = refl
      ...   | just P'' = ⊥-elim (noOff csat (P'' , sVis eqP veq))
      hide-emit-noth (pair _ _) a = refl
      hide-emit-noth fin        a = refl
      -- the whole hidden τ-map is everywhere nothing.
      hTau-noth : ∀ (i : AnyTypes (ExtI E)) (a : proj₁ i) → hide-hTau A (react v τc) i a ≡ nothing
      hTau-noth (_ , base _)            a = refl
      hTau-noth (_ , fin)               a = refl
      hTau-noth (_ , pair (base _)   _) a = refl
      hTau-noth (_ , pair (pair _ _) _) a = refl
      hTau-noth (_ , pair fin i′) (lift fzero           , a)
        with viewT (react v τc) (_ , i′) a in teq
      ... | nothing  = refl
      ... | just P'' = ⊥-elim (nothing≢just (trans (sym (st (_ , i′) a)) teq))
      hTau-noth (_ , pair fin i′) (lift (fsuc fzero)    , a) = hide-emit-noth i′ a
      hTau-noth (_ , pair fin i′) (lift (fsuc (fsuc _)) , a) = refl

-------------------------------------------------------------------------------------
-- refusal transfer between `P′ ∖ A` (over `X`) and `P′` (over `hideBan A X`)
-------------------------------------------------------------------------------------

-- a stable refusal of `P′ ∖ A` de-hides to a refusal of `P′` over the extended ban set.
hide-refuses-elim : (A : EventSet) (P′ : PTree E (ExtI E) R) {X : Event√ R → Set ℓr}
                  → Refuses (P′ ∖ A) X → Refuses P′ (hideBan A X)
hide-refuses-elim A P′ {X} ref = hide-stable-elim A P′ (proj₁ ref) , offNo
  where
  offNo : ∀ e → hideBan A X e → ¬ Offers P′ e
  -- a √-offer means `force P′ ≡ ret r`, but `P′ ∖ A` is stable — absurd.
  offNo (√ r) hb (P'' , sRet fpP) = stable-not-ret {t = P′ ∖ A} (proj₁ ref) (fHide-ret A P′ fpP)
  offNo (evl (evLabel B e a)) hb (P'' , step) with A .dec (B , e) a | hb
  -- an `A`-offer of `P′` is a τ of `P′ ∖ A` (`Hide-hidden`) — but it is stable.
  ... | yes csat | _  = stable-no-τ (proj₁ ref) (Hide-hidden A P′ csat step)
  -- a non-`A` offer survives (`Hide-keep`) and is banned by `X` (= `hb` here).
  ... | no ¬csat | Xe = proj₂ ref (evl (evLabel B e a)) Xe (P'' ∖ A , Hide-keep A P′ ¬csat step)

-- dually: a `hideBan`-refusal of `P′` re-hides to a refusal of `P′ ∖ A` over `X`.
hide-refuses-intro : (A : EventSet) (P′ : PTree E (ExtI E) R) {X : Event√ R → Set ℓr}
                   → Refuses P′ (hideBan A X) → Refuses (P′ ∖ A) X
hide-refuses-intro A P′ {X} ref = hide-stable-intro A P′ (proj₁ ref) noOffA , offNo
  where
  -- `P′` offers no `A`-member event (its `hideBan` yes-branch is `⊤`, refused by `ref`).
  noOffA : ∀ {B : Set ℓ} {e : E B} {a : B} → A .mem (B , e) a → ¬ Offers P′ (evl (evLabel B e a))
  noOffA csat = proj₂ ref (evl (evLabel _ _ _)) (hideBan-yes A csat)
  offNo : ∀ e → X e → ¬ Offers (P′ ∖ A) e
  offNo e Xe (M , step) with Hide-ev-elim A P′ step
  -- a surviving visible offer of `P′ ∖ A` came from a non-`A` offer of `P′`.
  ... | heV {B} {e = e'} {a} P'' ¬csat Pev =
          proj₂ ref (evl (evLabel B e' a)) (hideBan-no A ¬csat Xe) (P'' , Pev)
  -- a √-offer means `force P′ ≡ ret r`, contradicting `isStable P′`.
  ... | he√ fpP = ⊥-elim (stable-not-ret {t = P′} (proj₁ ref) fpP)

-------------------------------------------------------------------------------------
-- de-hiding witnesses split along a prefix of the `P`-side trace
-------------------------------------------------------------------------------------

-- `HideTr A (p′ ++ suf′) s` splits `s` at the image of `p′`.
HideTr-split : (A : EventSet) (p′ : List (Event√ R)) {suf′ s : List (Event√ R)}
             → HideTr A (p′ ++ suf′) s
             → Σ[ s₀ ∈ List (Event√ R) ] Σ[ s₁ ∈ List (Event√ R) ]
                 ((s ≡ s₀ ++ s₁) × HideTr A p′ s₀)
HideTr-split A [] {s = s} h = [] , s , refl , hnil
HideTr-split A (evl (evLabel B e a) ∷ p″) (hkeep ¬c h′) with HideTr-split A p″ h′
... | s₀ , s₁ , refl , h₀ = (evl (evLabel B e a) ∷ s₀) , s₁ , refl , hkeep ¬c h₀
HideTr-split A (evl (evLabel B e a) ∷ p″) (hdrop c h′) with HideTr-split A p″ h′
... | s₀ , s₁ , refl , h₀ = s₀ , s₁ , refl , hdrop c h₀
HideTr-split A (√ r ∷ []) h√ = (√ r ∷ []) , [] , refl , h√

-------------------------------------------------------------------------------------
-- (i) UNCONDITIONAL stable-failure transfer (no divergence hypothesis)
-------------------------------------------------------------------------------------

-- `Hide-mono-fail`: a stable failure of `Q ∖ A` transfers (as a failure⊥) to `P ∖ A`.
-- A `Q ∖ A` failure de-hides to a `Q`-reach + refusal over `hideBan A X`; `P ⊑F⊥ Q`
-- matches it either with a `P`-failure (re-hidden) or a `P`-divergence (extension-closed
-- through the split point of the de-hiding witness).
Hide-mono-fail : (A : EventSet) {P Q : PTree E (ExtI E) R} → P ⊑F⊥ Q
               → ∀ {s} {X : Event√ R → Set ℓr}
               → failures (Q ∖ A) s X → failures⊥ (P ∖ A) s X
Hide-mono-fail A {P} {Q} f {s} {X} fl with Hide-failures-elim A Q fl
... | s′ , Q′ , run , h , ref
      with f {s′} {hideBan A X} (inj₁ (Q′ , run , hide-refuses-elim A Q′ ref))
...   | inj₁ (P′ , runP , refP) =
          inj₁ (Hide-failures-intro A P runP h (hide-refuses-intro A P′ refP))
...   | inj₂ dP
        with HideTr-split A (dP .IsDivergence.prefix)
               (subst (λ z → HideTr A z s) (dP .IsDivergence.split) h)
...     | s₀ , s₁ , seq , h₀ =
          inj₂ (subst (divergences (P ∖ A)) (sym seq)
                  (div-extension-closed
                    (Hide-div-intro A P (dP .IsDivergence.reach) h₀
                      (hide-Diverges-lift A (dP .IsDivergence.divwit)))))

-------------------------------------------------------------------------------------
-- (ii) the headline law, under divergence-freedom of the refined side's hide
-------------------------------------------------------------------------------------

-- `Hide-mono-⊑FD-df`: `(P ∖ A) ⊑FD (Q ∖ A)` when `Q ∖ A` is divergence-free.  The
-- failures half reduces to `Hide-mono-fail`; both divergence obligations are vacuous
-- (their `Q ∖ A`-divergence hypothesis is refuted by `hdf`).
Hide-mono-⊑FD-df : (A : EventSet) {P Q : PTree E (ExtI E) R} → P ⊑FD Q
                 → (∀ {s} → ¬ divergences (Q ∖ A) s)
                 → (P ∖ A) ⊑FD (Q ∖ A)
Hide-mono-⊑FD-df A {P} {Q} (fF , _) hdf = fF⊥ , fD
  where
  fF⊥ : (P ∖ A) ⊑F⊥ (Q ∖ A)
  fF⊥ (inj₁ fl) = Hide-mono-fail A fF fl
  fF⊥ (inj₂ dv) = ⊥-elim (hdf dv)
  fD : (P ∖ A) ⊑D (Q ∖ A)
  fD dv = ⊥-elim (hdf dv)

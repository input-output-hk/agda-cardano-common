{-# OPTIONS --guardedness #-}

-- Prefix firing/inversion, loop step-inversion, nested-□ stability, and the
-- small silent-step helpers, hoisted from CSP.Examples.TPC.*.  Parametrised
-- by the event decider, mirroring CSP.Laws.Traces.TraceLaws.  The loop lemmas
-- fix the loop return type at `Poly.⊤ {lzero}` (loops never return) and are
-- channel-generic over `(ce : E B) ⦃ DecEq B ⦄`.

open import Level using (_⊔_; lift) renaming (zero to lzero; suc to lsuc)
import Data.Unit.Polymorphic as Poly
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.Traces.PrefixInversion
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟
open import Semantics.LTS       {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures  {E = E} {I = ExtI E}
  using (traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.DRBisim   {E = E} {I = ExtI E} using (Diverges)

-------------------------------------------------------------------------------------
-- silent-step helpers (model-generic; housed here so every example imports
-- them from one place without a Semantics→CSP layering breach)
-------------------------------------------------------------------------------------

sil-inj : ∀ {ℓr} {R : Set ℓr} {x y : PTree E (ExtI E) R}
        → sil {E = E} {I = ExtI E} x ≡ sil y → x ≡ y
sil-inj refl = refl

sil-no-ev : ∀ {ℓr} {R : Set ℓr} {S u t′ : PTree E (ExtI E) R} {l : Event√ R}
          → PTree.force S ≡ sil u → S ─[ ev l ]─► t′ → ⊥
sil-no-ev eq (sRet eq′)   = case trans (sym eq) eq′ of λ ()
sil-no-ev eq (sVis eq′ _) = case trans (sym eq) eq′ of λ ()

sil-τ-uniq : ∀ {ℓr} {R : Set ℓr} {S u t′ : PTree E (ExtI E) R}
           → PTree.force S ≡ sil u → S ─[ τ ]─► t′ → t′ ≡ u
sil-τ-uniq eq (sSil eq′)   = sil-inj (trans (sym eq′) eq)
sil-τ-uniq eq (sTau eq′ _) = case trans (sym eq) eq′ of λ ()

divergesSil : ∀ {ℓr} {R : Set ℓr} {S u : PTree E (ExtI E) R}
            → PTree.force S ≡ sil u → Diverges S → Diverges u
divergesSil eq d = subst Diverges (sil-τ-uniq eq (Diverges.step d)) (Diverges.rest d)

-------------------------------------------------------------------------------------
-- prefix firing / inversion (`ce ⟶₀ Q`)
--
-- The example copies pinned the payload at `Data.Unit.⊤`, which lives at Set₀ and
-- so cannot appear under `E : Set ℓ → Set ℓe` generically.  These are therefore
-- generalised over an arbitrary payload `{B : Set ℓ}` (exactly as the loop lemmas
-- below already are); at ℓ = lzero the examples instantiate `B := ⊤` and, since ⊤
-- has η, the Σ-witness in ⟶₀-ev-inv is definitionally `tt`.
-------------------------------------------------------------------------------------

Prefix-cont-fires : ∀ {ℓr} {R : Set ℓr} {A B : Set ℓ} {e : E A} {a : A}
                      {ce : E B} {P : B → PTree E (ExtI E) R}
                      {t′ : PTree E (ExtI E) R}
                  → Prefix-cont ce P (A , e) a ≡ just t′
                  → ((B , ce) ≡ (A , e)) × Σ[ x ∈ B ] (t′ ≡ P x)
Prefix-cont-fires {A = A} {B = B} {e = e} {a = a} {ce = ce} br with E-≟ (B , ce) (A , e)
... | yes refl = refl , a , sym (just-injective br)
... | no ¬eq   = ⊥-elim (case br of λ ())

⟶₀-no-τ : ∀ {ℓr} {R : Set ℓr} {B : Set ℓ} {ce : E B} {Q : PTree E (ExtI E) R} {t′}
        → (ce ⟶₀ Q) ─[ τ ]─► t′ → ⊥
⟶₀-no-τ (sSil eq)      = case eq of λ ()
⟶₀-no-τ (sTau refl br) = case br of λ ()

⟶₀-ev-inv : ∀ {ℓr} {R : Set ℓr} {B : Set ℓ} {ce : E B} {Q : PTree E (ExtI E) R}
              {l : Event√ R} {t′}
          → (ce ⟶₀ Q) ─[ ev l ]─► t′
          → Σ[ x ∈ B ] ((l ≡ evl (evLabel B ce x)) × (t′ ≡ Q))
⟶₀-ev-inv (sRet eq) = case eq of λ ()
⟶₀-ev-inv (sVis {at = at} {a = a} refl br) with Prefix-cont-fires br
... | refl , _ , t′≡ = a , refl , t′≡

-------------------------------------------------------------------------------------
-- loop step-inversion (channel-generic, loop return type `Poly.⊤ {lzero}`)
-------------------------------------------------------------------------------------

loop-pfx-ev-inv : ∀ {A B : Set ℓ} (ce : E B) (P : B → PTree E (ExtI E) A)
                    (K : A → PTree E (ExtI E) (A ⊎ Poly.⊤ {lzero}))
                    {l : Event√ (Poly.⊤ {lzero})} {t′}
                → iter-bind ((ce ⟶ P) >>= (λ a′ → Ret (inj₁ a′))) K ─[ ev l ]─► t′
                → Σ[ x ∈ B ] ((l ≡ evl (evLabel B ce x))
                    × (t′ ≡ iter-bind (P x >>= (λ a′ → Ret (inj₁ a′))) K))
loop-pfx-ev-inv ce P K (sRet eq) = case eq of λ ()
loop-pfx-ev-inv ce P K (sVis {at = at} {a = a} refl br) with E-≟ (_ , ce) at
... | yes refl = a , refl , sym (just-injective br)
... | no _     = ⊥-elim (case br of λ ())

loop-pfx-no-τ : ∀ {A B : Set ℓ} (ce : E B) (P : B → PTree E (ExtI E) A)
                  (K : A → PTree E (ExtI E) (A ⊎ Poly.⊤ {lzero})) {t′}
              → iter-bind ((ce ⟶ P) >>= (λ a′ → Ret (inj₁ a′))) K ─[ τ ]─► t′ → ⊥
loop-pfx-no-τ ce P K (sSil eq)      = case eq of λ ()
loop-pfx-no-τ ce P K (sTau refl br) = case br of λ ()

loop-out-ev-inv : ∀ {A B : Set ℓ} ⦃ _ : DecEq B ⦄
                    (ce : E B) (u : B) (X : PTree E (ExtI E) A)
                    (K : A → PTree E (ExtI E) (A ⊎ Poly.⊤ {lzero}))
                    {l : Event√ (Poly.⊤ {lzero})} {t′}
                → iter-bind ((ce ! u ⟶ X) >>= (λ a′ → Ret (inj₁ a′))) K ─[ ev l ]─► t′
                → (l ≡ evl (evLabel B ce u))
                  × (t′ ≡ iter-bind (X >>= (λ a′ → Ret (inj₁ a′))) K)
loop-out-ev-inv ce u X K (sRet eq) = case eq of λ ()
loop-out-ev-inv {B = B} ce u X K (sVis {at = at} {a = a} refl br) with E-≟ (B , ce) at
... | no _ = ⊥-elim (case br of λ ())
... | yes refl with a ≟ u
...   | yes refl = refl , sym (just-injective br)
...   | no _     = ⊥-elim (case br of λ ())

loop-out-no-τ : ∀ {A B : Set ℓ} ⦃ _ : DecEq B ⦄
                  (ce : E B) (u : B) (X : PTree E (ExtI E) A)
                  (K : A → PTree E (ExtI E) (A ⊎ Poly.⊤ {lzero})) {t′}
              → iter-bind ((ce ! u ⟶ X) >>= (λ a′ → Ret (inj₁ a′))) K ─[ τ ]─► t′ → ⊥
loop-out-no-τ ce u X K (sSil eq)      = case eq of λ ()
loop-out-no-τ ce u X K (sTau refl br) = case br of λ ()

-------------------------------------------------------------------------------------
-- loop trace-elimination
-------------------------------------------------------------------------------------

loop-pfx-trace-elim : ∀ {A B : Set ℓ} (ce : E B) (P : B → PTree E (ExtI E) A)
                        (K : A → PTree E (ExtI E) (A ⊎ Poly.⊤ {lzero})) {s}
                    → traces (iter-bind ((ce ⟶ P) >>= (λ a′ → Ret (inj₁ a′))) K) s
                    → (s ≡ []) ⊎ (Σ[ x ∈ B ] Σ[ t ∈ List (Event√ (Poly.⊤ {lzero})) ]
                        ((s ≡ evl (evLabel B ce x) ∷ t)
                         × traces (iter-bind (P x >>= (λ a′ → Ret (inj₁ a′))) K) t))
loop-pfx-trace-elim ce P K (_ , ⟹-refl)   = inj₁ refl
loop-pfx-trace-elim ce P K (_ , ⟹-τ st _) = ⊥-elim (loop-pfx-no-τ ce P K st)
loop-pfx-trace-elim ce P K (end , ⟹-ev st rest) with loop-pfx-ev-inv ce P K st
... | x , refl , refl = inj₂ (x , _ , refl , end , rest)

loop-out-trace-elim : ∀ {A B : Set ℓ} ⦃ _ : DecEq B ⦄
                        (ce : E B) (u : B) (X : PTree E (ExtI E) A)
                        (K : A → PTree E (ExtI E) (A ⊎ Poly.⊤ {lzero})) {s}
                    → traces (iter-bind ((ce ! u ⟶ X) >>= (λ a′ → Ret (inj₁ a′))) K) s
                    → (s ≡ []) ⊎ (Σ[ t ∈ List (Event√ (Poly.⊤ {lzero})) ]
                        ((s ≡ evl (evLabel B ce u) ∷ t)
                         × traces (iter-bind (X >>= (λ a′ → Ret (inj₁ a′))) K) t))
loop-out-trace-elim ce u X K (_ , ⟹-refl)   = inj₁ refl
loop-out-trace-elim ce u X K (_ , ⟹-τ st _) = ⊥-elim (loop-out-no-τ ce u X K st)
loop-out-trace-elim ce u X K (end , ⟹-ev st rest) with loop-out-ev-inv ce u X K st
... | refl , refl = inj₂ (_ , refl , end , rest)

-------------------------------------------------------------------------------------
-- output-firing (channel-generic; subsumes the per-channel *-fire lemmas)
-------------------------------------------------------------------------------------

-- NOTE: the loop-state type `A` must live at `Set ℓ` (iterV's telescope), so it
-- is quantified rather than pinned to `Poly.⊤ {lzero}`; the examples (ℓ = lzero)
-- instantiate `A := Poly.⊤ {lzero}` and recover the per-channel *-fire lemmas.
out-fire : ∀ {A B : Set ℓ} ⦃ _ : DecEq B ⦄ (ce : E B) (u : B)
             (P : PTree E (ExtI E) A)
             (K : A → PTree E (ExtI E) (A ⊎ Poly.⊤ {lzero}))
         → iterV K (react (bindV (λ a′ → Ret (inj₁ a′)) (react (Output-cont ce u P) ∅t))
                          (bindT (λ a′ → Ret (inj₁ a′)) (react (Output-cont ce u P) ∅t)))
                (B , ce) u
           ≡ just (iter-bind (P >>= (λ a′ → Ret (inj₁ a′))) K)
-- (In the examples the channel decider reduced definitionally on concrete
-- constructors; generically `E-≟ (B , ce) (B , ce)` is opaque, so it needs its
-- own with-match before the payload decision `u ≟ u` unblocks.)
out-fire {B = B} ce u P K with E-≟ (B , ce) (B , ce)
... | no ¬eq = ⊥-elim (¬eq refl)
... | yes refl with u ≟ u
...   | yes _  = refl
...   | no ¬eq = ⊥-elim (¬eq refl)

-------------------------------------------------------------------------------------
-- nested-□ stability: □ of two stable (τ-empty) react nodes is stable
-------------------------------------------------------------------------------------

-- pointwise-empty τ-part of a node
TEmpty : ∀ {ℓr} {R : Set ℓr}
       → ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
       → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
TEmpty τc = ∀ i (a : proj₁ i) → τc i a ≡ nothing

∅t-empty : ∀ {ℓr} {R : Set ℓr} → TEmpty (∅t {R = R})
∅t-empty i a = refl

□-mt-empty : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
             {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τcP τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             {P Q : PTree E (ExtI E) R}
           → TEmpty τcP → TEmpty τcQ
           → TEmpty (□-mt (react vP τcP) (react vQ τcQ) P Q)
□-mt-empty eP eQ (_ , base _)            _ = refl
□-mt-empty eP eQ (_ , fin)               _ = refl
□-mt-empty eP eQ (_ , pair (base _) _)   _ = refl
□-mt-empty eP eQ (_ , pair (pair _ _) _) _ = refl
□-mt-empty {τcP = τcP} eP eQ (_ , pair fin i) (lift fzero , a)
  with τcP (_ , i) a | eP (_ , i) a
... | just _  | ()
... | nothing | refl = refl
□-mt-empty {τcQ = τcQ} eP eQ (_ , pair fin i) (lift (fsuc fzero) , a)
  with τcQ (_ , i) a | eQ (_ , i) a
... | just _  | ()
... | nothing | refl = refl
□-mt-empty eP eQ (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.BindFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree
open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (failures⊥; divergences; IsDivergence)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses; Offers)

-- FORCE lemmas: `force (P >>= k)` reduces by case-analysis on `force P`.

bind-force-ret : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S) {r : R}
   → force P ≡ ret r → force (P >>= k) ≡ force (k r)
bind-force-ret P k eq with force P | eq
... | ret r | refl = refl

bind-force-sil : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S) {c : PTree E (ExtI E) R}
   → force P ≡ sil c → force (P >>= k) ≡ sil (c >>= k)
bind-force-sil P k eq with force P | eq
... | sil c | refl = refl

bind-force-react : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
   → force P ≡ react v τc
   → force (P >>= k) ≡ react (bindV k (react v τc)) (bindT k (react v τc))
bind-force-react P k eq with force P | eq
... | react v τc | refl = refl

-- CONTINUATION just-lemmas: `bindV`/`bindT` follow the underlying `viewV`/`viewT`.

bind-cont-vis-just : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
   {at : AnyTypes E} {a : proj₁ at} {t : PTree E (ExtI E) R}
   → viewV nP at a ≡ just t → bindV k nP at a ≡ just (t >>= k)
bind-cont-vis-just k nP {at} {a} eq with viewV nP at a | eq
... | just t | refl = refl

bind-cont-tau-just : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (k : R → PTree E (ExtI E) S) (nP : NodeKind E (ExtI E) R)
   {i : AnyTypes (ExtI E)} {a : proj₁ i} {t : PTree E (ExtI E) R}
   → viewT nP i a ≡ just t → bindT k nP i a ≡ just (t >>= k)
bind-cont-tau-just k nP {i} {a} eq with viewT nP i a | eq
... | just t | refl = refl

-- LIFT a visible big-step run of `P` into `P >>= k`.
-- The trace `map evl vs` (vs : List Event) captures "visible run, no √".
-- Recursion is structural on the finite `⟹` derivation.
lift-bind-bigstep : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P P′ : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   (vs : List Event)
   → P ⟹⟨ map evl vs ⟩ P′ → (P >>= k) ⟹⟨ map evl vs ⟩ (P′ >>= k)
-- empty trace: only ⟹-refl or τ-steps can apply
lift-bind-bigstep P P′ k []         ⟹-refl              = ⟹-refl
lift-bind-bigstep P P′ k []         (⟹-τ step rest) with τ-inv step
... | inj₁ eqf                       =
        ⟹-τ (sSil (bind-force-sil P k eqf)) (lift-bind-bigstep _ P′ k [] rest)
... | inj₂ (v , τc , i , a , eqf , eqj) =
        ⟹-τ (sTau (bind-force-react P k eqf)
                  (bind-cont-tau-just k (react v τc) eqj))
            (lift-bind-bigstep _ P′ k [] rest)
-- non-empty trace head `evl ev`: ⟹-τ (no consume) or ⟹-ev (consume head)
lift-bind-bigstep P P′ k (x ∷ vs′) (⟹-τ step rest) with τ-inv step
... | inj₁ eqf                       =
        ⟹-τ (sSil (bind-force-sil P k eqf)) (lift-bind-bigstep _ P′ k (x ∷ vs′) rest)
... | inj₂ (v , τc , i , a , eqf , eqj) =
        ⟹-τ (sTau (bind-force-react P k eqf)
                  (bind-cont-tau-just k (react v τc) eqj))
            (lift-bind-bigstep _ P′ k (x ∷ vs′) rest)
lift-bind-bigstep P P′ k (evLabel A e a ∷ vs′) (⟹-ev step rest) with ev-inv step
... | (v , τc , eqf , eqj) =
        ⟹-ev (sVis (bind-force-react P k eqf)
                   (bind-cont-vis-just k (react v τc) eqj))
             (lift-bind-bigstep _ P′ k vs′ rest)

-- ============================================================================
-- Task 3: BindSplit + bind-bigstep-inv
-- ============================================================================

-- Transport a single step across an equal `force`: a step depends on its
-- source only through `force`, so an equal-force root admits the same step.
─►-force-cong : ∀ {ℓr} {R : Set ℓr} {p q t : PTree E (ExtI E) R} {l : Label R}
   → PTree.force p ≡ PTree.force q
   → p ─[ l ]─► t → q ─[ l ]─► t
─►-force-cong eq (sRet ef)    = sRet  (trans (sym eq) ef)
─►-force-cong eq (sSil ef)    = sSil  (trans (sym eq) ef)
─►-force-cong eq (sVis ef ej) = sVis  (trans (sym eq) ef) ej
─►-force-cong eq (sTau ef ej) = sTau  (trans (sym eq) ef) ej


data BindSplit {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   (T : PTree E (ExtI E) S) : List (Event√ S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr ⊔ ℓs) where
  in-P : ∀ {P′} {vs : List Event}
       → P ⟹⟨ map evl vs ⟩ P′ → T ≡ (P′ >>= k)
       → BindSplit P k T (map evl vs)
  in-k : ∀ {r : R} {s₁ : List Event} {s₂ : List (Event√ S)} {Pᵣ}
       → P ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret r
       → k r ⟹⟨ s₂ ⟩ T
       → BindSplit P k T (map evl s₁ ++ s₂)

-- Re-wrap a recursive BindSplit by *prepending one τ-step* (from P to its
-- silent/τ-successor `c`) onto P's run.  The trace index is unchanged.
prepend-τ : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   {P c : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
   {T : PTree E (ExtI E) S} {s : List (Event√ S)}
   → (P ─[ τ ]─► c)
   → BindSplit c k T s → BindSplit P k T s
prepend-τ pstep (in-P cstep eq)    = in-P (⟹-τ pstep cstep) eq
prepend-τ pstep (in-k cstep fe kr) = in-k (⟹-τ pstep cstep) fe kr

-- Re-wrap a recursive BindSplit by *prepending one visible step* (from P
-- to its visible successor `t`, on event `evLabel A e a`).  The trace index
-- grows by `evl (evLabel A e a)` at the front (matching `⟹-ev`).
prepend-ev : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   {P t : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
   {T : PTree E (ExtI E) S} {s : List (Event√ S)}
   {A : Set ℓ} {e : E A} {a : A}
   → (P ─[ ev (evl (evLabel A e a)) ]─► t)
   → BindSplit t k T s → BindSplit P k T (evl (evLabel A e a) ∷ s)
prepend-ev {A = A} {e} {a} pstep (in-P {vs = vs} cstep eq) =
  in-P {vs = evLabel A e a ∷ vs} (⟹-ev pstep cstep) eq
prepend-ev {A = A} {e} {a} pstep (in-k {s₁ = s₁} cstep fe kr) =
  in-k {s₁ = evLabel A e a ∷ s₁} (⟹-ev pstep cstep) fe kr

-- injectivity of the `sil` head constructor (used to read off the τ-target)
sil-inj : ∀ {ℓi ℓa} {I : Set ℓ → Set ℓi} {A : Set ℓa} {x y : PTree E I A}
        → _≡_ {A = NodeKind E I A} (sil x) (sil y) → x ≡ y
sil-inj refl = refl

-- injectivity of the `react` head constructor in its two offer maps
react-inj-v : ∀ {ℓi ℓa} {I : Set ℓ → Set ℓi} {A : Set ℓa}
   {v₁ v₂ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I A))}
   {τc₁ τc₂ : (i : AnyTypes I) → ContinueType i (Maybe (PTree E I A))}
   → _≡_ {A = NodeKind E I A} (react v₁ τc₁) (react v₂ τc₂) → v₁ ≡ v₂
react-inj-v refl = refl

react-inj-τ : ∀ {ℓi ℓa} {I : Set ℓ → Set ℓi} {A : Set ℓa}
   {v₁ v₂ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I A))}
   {τc₁ τc₂ : (i : AnyTypes I) → ContinueType i (Maybe (PTree E I A))}
   → _≡_ {A = NodeKind E I A} (react v₁ τc₁) (react v₂ τc₂) → τc₁ ≡ τc₂
react-inj-τ refl = refl

-- Read a bound τ/visible branch back to its underlying `viewT`/`viewV ≡ just`
-- together with the witnessing bind-shape `(t′ >>= k) ≡ q` of the target.
bindT-inv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (k : R → PTree E (ExtI E) S)
   (v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) R)))
   (τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) R)))
   {i a} {q : PTree E (ExtI E) S}
   → bindT k (react v τc) i a ≡ just q
   → Σ[ t′ ∈ PTree E (ExtI E) R ]
       (τc i a ≡ just t′ × (t′ >>= k) ≡ q)
bindT-inv k v τc {i} {a} ej with τc i a in vtq
... | just t′ = t′ , refl , just-inj ej
  where just-inj : ∀ {q} → just (t′ >>= k) ≡ just q → (t′ >>= k) ≡ q
        just-inj refl = refl

bindV-inv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (k : R → PTree E (ExtI E) S)
   (v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) R)))
   (τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) R)))
   {at a} {q : PTree E (ExtI E) S}
   → bindV k (react v τc) at a ≡ just q
   → Σ[ t′ ∈ PTree E (ExtI E) R ]
       (v at a ≡ just t′ × (t′ >>= k) ≡ q)
bindV-inv k v τc {at} {a} ej with v at a in vvq
... | just t′ = t′ , refl , just-inj ej
  where just-inj : ∀ {q} → just (t′ >>= k) ≡ just q → (t′ >>= k) ≡ q
        just-inj refl = refl

bind-bigstep-inv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   {T : PTree E (ExtI E) S} {s : List (Event√ S)}
   → (P >>= k) ⟹⟨ s ⟩ T → BindSplit P k T s
-- refl: independent of `force P` — P stays put, T ≡ P >>= k.
bind-bigstep-inv P k ⟹-refl = in-P {vs = []} ⟹-refl refl
-- ── τ via sSil ──────────────────────────────────────────────────────────────
bind-bigstep-inv P k (⟹-τ (sSil eqf) rest) with PTree.force P in eqP | eqf
... | ret r     | eqf′ =
      -- hand-off: force(P>>=k) ≡ force(k r); the τ-step belongs to k r.
      in-k {s₁ = []} ⟹-refl eqP (⟹-τ (sSil eqf′) rest)
... | sil c     | eqf′
      -- force(P>>=k) ≡ sil (c >>= k), so target ≡ (c >>= k); recurse on c.
      rewrite sym (sil-inj eqf′) =
        prepend-τ (sSil eqP) (bind-bigstep-inv c k rest)
... | react v τc | ()   -- force(P>>=k) ≡ react ≠ sil
-- ── τ via sTau ──────────────────────────────────────────────────────────────
bind-bigstep-inv P k (⟹-τ (sTau eqf eqj) rest) with PTree.force P in eqP | eqf
... | ret r     | eqf′ =
      -- hand-off: force(P>>=k) ≡ force(k r); the τ-step belongs to k r.
      in-k {s₁ = []} ⟹-refl eqP (⟹-τ (sTau eqf′ eqj) rest)
... | sil c     | ()    -- force(P>>=k) ≡ sil ≠ react
... | react v τc | eqf′
      -- the step's τc unifies (via react-injectivity) with `bindT k (react v τc)`
      rewrite sym (react-inj-τ eqf′) with bindT-inv k v τc eqj
...   | (t′ , vtq , refl) =
        prepend-τ (sTau eqP vtq) (bind-bigstep-inv t′ k rest)
-- ── visible step via sVis ────────────────────────────────────────────────────
bind-bigstep-inv P k (⟹-ev (sVis eqf eqj) rest) with PTree.force P in eqP | eqf
... | ret r     | eqf′ =
      -- hand-off: force(P>>=k) ≡ force(k r); the visible step belongs to k r.
      in-k {s₁ = []} ⟹-refl eqP (⟹-ev (sVis eqf′ eqj) rest)
... | sil c     | ()    -- force(P>>=k) ≡ sil ≠ react
... | react v τc | eqf′
      rewrite sym (react-inj-v eqf′) with bindV-inv k v τc eqj
...   | (t′ , vvq , refl) =
        prepend-ev (sVis eqP vvq) (bind-bigstep-inv t′ k rest)
-- ── √ hand-off via sRet ──────────────────────────────────────────────────────
-- A `√ x` visible step from `P >>= k` can only happen once P has returned and
-- the continuation `k r` reaches `ret x`; so it belongs entirely to `k r`.
bind-bigstep-inv P k (⟹-ev (sRet eqf) rest) with PTree.force P in eqP | eqf
... | ret r     | eqf′ =
      in-k {s₁ = []} ⟹-refl eqP (⟹-ev (sRet eqf′) rest)
... | sil c     | ()    -- force(P>>=k) ≡ sil ≠ ret
... | react v τc | ()   -- force(P>>=k) ≡ react ≠ ret

-- ============================================================================
-- Task 4: bind DIVERGENCE characterisation
-- ============================================================================

open IsDivergence
open Diverges

-- ── helpers ──────────────────────────────────────────────────────────────

-- Compose two visible big-step runs (transitivity of ⟹).
⟹-trans : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E (ExtI E) R}
   {s₁ s₂ : List (Event√ R)}
   → p ⟹⟨ s₁ ⟩ q → q ⟹⟨ s₂ ⟩ r → p ⟹⟨ s₁ ++ s₂ ⟩ r
⟹-trans ⟹-refl          q⟹ = q⟹
⟹-trans (⟹-τ step rest)  q⟹ = ⟹-τ  step (⟹-trans rest q⟹)
⟹-trans (⟹-ev step rest) q⟹ = ⟹-ev step (⟹-trans rest q⟹)

-- Transport a single τ-step across `>>= k`: a τ-step of `Q` lifts to a τ-step
-- of `Q >>= k` (mirrors `lift-bind-step-ev`, but for the silent label).
lift-bind-step-τ : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (Q : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   {n : PTree E (ExtI E) R}
   → Q ─[ τ ]─► n → (Q >>= k) ─[ τ ]─► (n >>= k)
lift-bind-step-τ Q k step with τ-inv step
... | inj₁ eqf                       = sSil (bind-force-sil Q k eqf)
... | inj₂ (v , τc , i , a , eqf , eqj) =
        sTau (bind-force-react Q k eqf) (bind-cont-tau-just k (react v τc) eqj)

-- A diverging `Q` makes `Q >>= k` diverge: every τ-step on the spine lifts
-- through `>>= k` (coinductively, guarded under the `Diverges` constructor).
Diverges->>= : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   {Q : PTree E (ExtI E) R} (k : R → PTree E (ExtI E) S)
   → Diverges Q → Diverges (Q >>= k)
Diverges->>= {Q = Q} k dQ .next = dQ .next >>= k
Diverges->>= {Q = Q} k dQ .step = lift-bind-step-τ Q k (dQ .step)
Diverges->>= {Q = Q} k dQ .rest = Diverges->>= k (dQ .rest)

-- Transport a `Diverges` across an equal `force`: only the first step depends
-- on the source, and it does so through `force` only (mirrors the old
-- `Divergent-force-eq`).
Diverges-force-eq : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
   → force P ≡ force Q → Diverges Q → Diverges P
Diverges-force-eq eq dQ .next = dQ .next
Diverges-force-eq eq dQ .step = ─►-force-cong (sym eq) (dQ .step)
Diverges-force-eq eq dQ .rest = dQ .rest

-- Splitting `map evl vs ≡ xs ++ ys` recovers the visible-list witnesses of the
-- two halves (every element of `map evl vs` is an `evl`, so are its splits).
∷-inj : ∀ {ℓa} {A : Set ℓa} {h₁ h₂ : A} {t₁ t₂ : List A}
      → (h₁ ∷ t₁) ≡ (h₂ ∷ t₂) → h₁ ≡ h₂ × t₁ ≡ t₂
∷-inj refl = refl , refl

evl-split : ∀ {ℓr} {R : Set ℓr} (xs : List (Event√ R)) (vs : List Event) (ys : List (Event√ R))
   → map evl vs ≡ xs ++ ys
   → Σ[ vs₁ ∈ List Event ] Σ[ vs₂ ∈ List Event ]
       (xs ≡ map evl vs₁ × ys ≡ map evl vs₂ × vs ≡ vs₁ ++ vs₂)
evl-split []         vs        ys eq = [] , vs , refl , sym eq , refl
evl-split (x ∷ xs′) (v ∷ vs′) ys eq with ∷-inj eq
... | hd , tl with evl-split xs′ vs′ ys tl
...   | vs₁ , vs₂ , exs , eys , evs =
        v ∷ vs₁ , vs₂ , trans (cong (_∷ xs′) (sym hd)) (cong (evl v ∷_) exs)
                      , eys , cong (v ∷_) evs

-- ── bind-div-intro-P ───────────────────────────────────────────────────────
-- If `P` diverges on a visible trace `map evl vs`, so does `P >>= k`.
bind-div-intro-P : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S) {vs : List Event}
   → divergences P (map evl vs) → divergences (P >>= k) (map evl vs)
bind-div-intro-P P k {vs} d
   with evl-split (d .prefix) vs (d .suffix) (d .split)
... | vs₁ , vs₂ , refl , refl , evs = record
  { prefix  = map evl vs₁
  ; suffix  = map evl vs₂
  ; split   = trans (cong (map evl) evs) (map-++ evl vs₁ vs₂)
  ; witness = d .witness >>= k
  ; reach   = lift-bind-bigstep P (d .witness) k vs₁ (d .reach)
  ; divwit  = Diverges->>= k (d .divwit)
  }

-- Cross the force-equal boundary `force p ≡ force q` for a divergence-bearing
-- run out of `q`.  A non-trivial run transports its first step to `p`, keeping
-- the same endpoint/witness; a 0-step run (`q` itself is the witness, but `p`
-- is what we hold) is reflected by re-rooting the `Diverges` witness at `p`.
cross-div-force-eq : ∀ {ℓr} {R : Set ℓr} {p q w : PTree E (ExtI E) R} {s}
   → force p ≡ force q → q ⟹⟨ s ⟩ w → Diverges w
   → Σ[ w′ ∈ PTree E (ExtI E) R ] (p ⟹⟨ s ⟩ w′ × Diverges w′)
cross-div-force-eq {p = p} eq ⟹-refl          dw = p , ⟹-refl , Diverges-force-eq eq dw
cross-div-force-eq         eq (⟹-τ step rest)  dw =
  _ , ⟹-τ  (─►-force-cong (sym eq) step) rest , dw
cross-div-force-eq         eq (⟹-ev step rest) dw =
  _ , ⟹-ev (─►-force-cong (sym eq) step) rest , dw

-- ── bind-div-intro-k ─────────────────────────────────────────────────────────
-- If `P` visibly reaches a `ret r` state and `k r` diverges on `s₂`, then
-- `P >>= k` diverges on `map evl s₁ ++ s₂`.
bind-div-intro-k : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   {r : R} {s₁ : List Event} {s₂ : List (Event√ S)} {Pᵣ}
   → P ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret r → divergences (k r) s₂
   → divergences (P >>= k) (map evl s₁ ++ s₂)
bind-div-intro-k P k {r} {s₁} {s₂} {Pᵣ} reach eqr d
   with cross-div-force-eq (bind-force-ret Pᵣ k eqr)
          (IsDivergence.reach d) (IsDivergence.divwit d)
... | w′ , run , dw′ = record
  { prefix  = map evl s₁ ++ IsDivergence.prefix d
  ; suffix  = IsDivergence.suffix d
  ; split   = trans (cong (map evl s₁ ++_) (IsDivergence.split d))
                    (sym (++-assoc (map evl s₁) (IsDivergence.prefix d) (IsDivergence.suffix d)))
  ; witness = w′
  ; reach   = ⟹-trans (lift-bind-bigstep P Pᵣ k s₁ reach) run
  ; divwit  = dw′
  }

-- ── bind-div-elim ────────────────────────────────────────────────────────────
-- A divergence of `P >>= k` decomposes via `bind-bigstep-inv` on its reach:
--   • in-P : P visibly reaches some P′ and the residual `P′ >>= k` diverges.
--   • in-k : P visibly reaches a `ret r` state and `k r` diverges thereafter.
--
-- SIGNATURE ADJUSTMENT (documented).  The naïve `divergences P s` in-P branch is
-- NOT constructively derivable: `Diverges (P′ >>= k)` does not entail
-- `Diverges P′` (P′ may *terminate* and hand divergence off to k — deciding which
-- is a König/LEM obstruction).  We therefore keep the divergent witness *inside*
-- `P′ >>= k` (mirroring the old proof's `bds-tau-after` constructor): the in-P
-- branch returns the visible reach into P′ together with `Diverges (P′ >>= k)`.
bind-div-elim : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S) {s : List (Event√ S)}
   → divergences (P >>= k) s
   → (Σ[ vs ∈ List Event ] Σ[ P′ ∈ PTree E (ExtI E) R ] Σ[ sx ∈ List (Event√ S) ]
        (P ⟹⟨ map evl vs ⟩ P′ × Diverges (P′ >>= k) × (s ≡ map evl vs ++ sx)))
   ⊎ (Σ[ r ∈ R ] Σ[ s₁ ∈ List Event ] Σ[ s₂ ∈ List (Event√ S) ]
        (traces P (map evl s₁) × divergences (k r) s₂ × (s ≡ map evl s₁ ++ s₂)))
bind-div-elim P k {s} d
   with bind-bigstep-inv P k (IsDivergence.reach d)
... | in-P {P′ = P′} {vs = vs} reachP weq =
      inj₁ (vs , P′ , IsDivergence.suffix d , reachP
           , subst Diverges weq (IsDivergence.divwit d)
           , trans (IsDivergence.split d)
                   (cong (_++ IsDivergence.suffix d) refl))
... | in-k {r = r} {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} reachP eqr reachk =
      inj₂ (r , s₁ , s₂ ++ IsDivergence.suffix d
           , (Pᵣ , reachP)
           , record
               { prefix  = s₂
               ; suffix  = IsDivergence.suffix d
               ; split   = refl
               ; witness = IsDivergence.witness d
               ; reach   = reachk
               ; divwit  = IsDivergence.divwit d
               }
           , trans (IsDivergence.split d)
                   (++-assoc (map evl s₁) s₂ (IsDivergence.suffix d)))

-- ============================================================================
-- Task 5: bind FAILURES⊥ characterisation
-- ============================================================================
--
-- `failures⊥ X s B = failures X s B ⊎ divergences X s`, with
-- `failures X s B = Σ[ X′ ] (X ⟹⟨ s ⟩ X′ × Refuses X′ B)` and
-- `Refuses t B = isStable t × (∀ e → B e → ¬ Offers t e)`.
--
-- The DIVERGENCE half of every lemma reuses Task 4 (bind-div-*) verbatim; the
-- FAILURES half does the refusal-transfer bookkeeping over the visible run.
--
-- SIGNATURE ADJUSTMENTS (documented).  The plan's draft elim phrased the in-P
-- branch as `Refuses (P′ >>= k) B × s ≡ map evl vs` and the in-k branch as
-- `failures⊥ (k r) s₂ B × s ≡ map evl s₁ ++ s₂`.  The in-k shape is kept.  The
-- in-P shape is GENERALISED to `failures⊥ (P′ >>= k) sx B × s ≡ map evl vs ++ sx`
-- (a `failures⊥`, not a bare `Refuses`, plus a residual suffix `sx`).  Reason:
-- the divergence input to elim routes through `bind-div-elim`, whose in-P arm
-- returns `Diverges (P′ >>= k)` on a NON-empty suffix `sx` (the divergent witness
-- is kept inside `P′ >>= k`, exactly as Task 4's principled adjustment).  That
-- cannot be reflected to a `Refuses (P′ >>= k) B` at the bare reach.  The
-- generalised branch subsumes both: a genuine failure takes `sx = []` and
-- `inj₁ (failure)`; the divergence takes `inj₂ (divergence on sx)`.  The intro
-- lemmas keep the clean draft shapes (suffix-free), so downstream callers that
-- only build failures are unaffected.

-- `isStable` inspects only `force`, so an equal force transports stability.
stable-force-eq : ∀ {ℓs} {S : Set ℓs} {p q : PTree E (ExtI E) S}
   → force p ≡ force q → isStable q → isStable p
stable-force-eq {p = p} {q} eq st with force p | force q | eq
... | react _ _ | react _ _ | refl = st

-- `Refuses` depends on its tree only through `force` (both `isStable` and
-- `Offers` — the latter via the LTS steps, which read the source's `force`).
reflect-Refuses : ∀ {ℓs} {S : Set ℓs} {p q : PTree E (ExtI E) S}
   {B : Event√ S → Set ℓs}
   → force p ≡ force q → Refuses q B → Refuses p B
reflect-Refuses {p = p} {q} eq (st , no-off) =
  stable-force-eq {p = p} {q} eq st
  , λ e Be (t′ , step) → no-off e Be (t′ , ─►-force-cong eq step)

-- Cross a force-equal boundary `force p ≡ force q` for a FAILURE run out of `q`.
-- Mirrors `cross-div-force-eq`: a non-trivial run transports its first step to
-- `p`; a 0-step run reflects the endpoint's `Refuses` back through equal force.
cross-fail-force-eq : ∀ {ℓs} {S : Set ℓs} {p q : PTree E (ExtI E) S}
   {s : List (Event√ S)} {B : Event√ S → Set ℓs}
   → force p ≡ force q → failures q s B → failures p s B
cross-fail-force-eq {p = p} eq (_ , ⟹-refl , ref) =
  p , ⟹-refl , reflect-Refuses eq ref
cross-fail-force-eq eq (w , ⟹-τ step rest , ref) =
  w , ⟹-τ (─►-force-cong (sym eq) step) rest , ref
cross-fail-force-eq eq (w , ⟹-ev step rest , ref) =
  w , ⟹-ev (─►-force-cong (sym eq) step) rest , ref

-- ── bind-failures⊥-intro-P ───────────────────────────────────────────────────
-- A still-in-P failure: P visibly reaches P′ and `P′ >>= k` refuses B.  Lift the
-- run through `>>= k` (endpoint `P′ >>= k`) and reuse the given refusal directly.
bind-failures⊥-intro-P : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   {vs : List Event} {B : Event√ S → Set ℓs} {P′}
   → P ⟹⟨ map evl vs ⟩ P′ → Refuses (P′ >>= k) B
   → failures⊥ (P >>= k) (map evl vs) B
bind-failures⊥-intro-P P k {vs} {P′ = P′} reach ref =
  inj₁ (P′ >>= k , lift-bind-bigstep P P′ k vs reach , ref)

-- ── bind-failures⊥-intro-k ───────────────────────────────────────────────────
-- A hand-off failure: P visibly reaches a `ret r` state, then `k r` fails on s₂.
-- Lift P's run, cross the `ret r` force boundary, concat `k r`'s failing run.
bind-failures⊥-intro-k : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   {r : R} {s₁ : List Event} {s₂ : List (Event√ S)} {Pᵣ} {B : Event√ S → Set ℓs}
   → P ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret r → failures⊥ (k r) s₂ B
   → failures⊥ (P >>= k) (map evl s₁ ++ s₂) B
-- failure half: cross to `Pᵣ >>= k`, then prepend the lifted P-run.
bind-failures⊥-intro-k P k {r} {s₁} {s₂} {Pᵣ} reach eqr (inj₁ (w , run , ref))
   with cross-fail-force-eq (bind-force-ret Pᵣ k eqr) (w , run , ref)
... | w′ , run′ , ref′ =
      inj₁ (w′ , ⟹-trans (lift-bind-bigstep P Pᵣ k s₁ reach) run′ , ref′)
-- divergence half: reuse Task 4's bind-div-intro-k.
bind-failures⊥-intro-k P k {r} {s₁} {s₂} {Pᵣ} reach eqr (inj₂ d) =
  inj₂ (bind-div-intro-k P k reach eqr d)

-- ── bind-failures⊥-elim ──────────────────────────────────────────────────────
-- A failure⊥ of `P >>= k` splits into a still-in-P case (P reaches P′, then
-- `P′ >>= k` fails⊥ on a residual suffix sx) or a hand-off case (P reaches a
-- `ret r` state, then `k r` fails⊥ on s₂).  See the adjustment note above for
-- why the in-P branch carries a `failures⊥ … sx` rather than a bare `Refuses`.
bind-failures⊥-elim : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (P : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
   {s : List (Event√ S)} {B : Event√ S → Set ℓs}
   → failures⊥ (P >>= k) s B
   → (Σ[ vs ∈ List Event ] Σ[ P′ ∈ PTree E (ExtI E) R ] Σ[ sx ∈ List (Event√ S) ]
        (P ⟹⟨ map evl vs ⟩ P′ × failures⊥ (P′ >>= k) sx B × s ≡ map evl vs ++ sx))
   ⊎ (Σ[ r ∈ R ] Σ[ s₁ ∈ List Event ] Σ[ s₂ ∈ List (Event√ S) ] Σ[ Pᵣ ∈ PTree E (ExtI E) R ]
        (P ⟹⟨ map evl s₁ ⟩ Pᵣ × force Pᵣ ≡ ret r × failures⊥ (k r) s₂ B × s ≡ map evl s₁ ++ s₂))
-- FAILURE input: invert the run with bind-bigstep-inv.
bind-failures⊥-elim P k (inj₁ (T , run , ref)) with bind-bigstep-inv P k run
... | in-P {P′ = P′} {vs = vs} reachP refl =
      -- endpoint T ≡ P′ >>= k, which refuses B at the empty residual suffix.
      inj₁ (vs , P′ , [] , reachP
           , inj₁ (P′ >>= k , ⟹-refl , ref)
           , sym (++-identityʳ (map evl vs)))
... | in-k {r = r} {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} reachP eqr reachk =
      -- endpoint T reached inside k r; package as a failure of k r on s₂.
      inj₂ (r , s₁ , s₂ , Pᵣ , reachP , eqr
           , inj₁ (T , reachk , ref)
           , refl)
-- DIVERGENCE input: invert the divergence's reach directly (mirrors
-- bind-div-elim's body) so we keep the `force Pᵣ ≡ ret r` witness the in-k arm
-- of this elim demands — bind-div-elim discards it, so we re-derive here.
bind-failures⊥-elim P k (inj₂ d) with bind-bigstep-inv P k (IsDivergence.reach d)
... | in-P {P′ = P′} {vs = vs} reachP weq =
      -- divergent witness lives inside `P′ >>= k`; carry it as a residual
      -- `failures⊥ (P′ >>= k) (suffix d)` via inj₂ (a divergence at the reach).
      inj₁ (vs , P′ , IsDivergence.suffix d , reachP
           , inj₂ (record
              { prefix  = []
              ; suffix  = IsDivergence.suffix d
              ; split   = refl
              ; witness = P′ >>= k
              ; reach   = ⟹-refl
              ; divwit  = subst Diverges weq (IsDivergence.divwit d)
              })
           , IsDivergence.split d)
... | in-k {r = r} {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} reachP eqr reachk =
      inj₂ (r , s₁ , s₂ ++ IsDivergence.suffix d , Pᵣ , reachP , eqr
           , inj₂ (record
              { prefix  = s₂
              ; suffix  = IsDivergence.suffix d
              ; split   = refl
              ; witness = IsDivergence.witness d
              ; reach   = reachk
              ; divwit  = IsDivergence.divwit d
              })
           , trans (IsDivergence.split d)
                   (++-assoc (map evl s₁) s₂ (IsDivergence.suffix d)))

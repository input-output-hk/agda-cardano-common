{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.IterateFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree
open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (failures⊥; divergences; IsDivergence)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses; Offers)
open import CSP.Laws.FD.BindFD E-≟
  using (BindSplit; bind-bigstep-inv; lift-bind-bigstep; ⟹-trans
        ; bind-force-ret; Diverges->>=)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges)
open import Semantics.WeakBisim {E = E} {I = ExtI E} using (_─[τ*]─►_; τ*-refl; τ*-step)

-- FORCE lemmas: `force (iter-bind t k)` reduces by case-analysis on `force t`.

iter-bind-force-react : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
   {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) (A ⊎ R)))}
   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) (A ⊎ R)))}
   → force t ≡ react v τc
   → force (iter-bind t k) ≡ react (iterV k (react v τc)) (iterT k (react v τc))
iter-bind-force-react t k eq with force t | eq
... | react v τc | refl = refl

iter-bind-force-sil : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
   {c : PTree E (ExtI E) (A ⊎ R)}
   → force t ≡ sil c → force (iter-bind t k) ≡ sil (iter-bind c k)
iter-bind-force-sil t k eq with force t | eq
... | sil c | refl = refl

-- CONTINUATION just-lemmas: `iterV`/`iterT` follow the underlying `viewV`/`viewT`.

iter-bind-cont-vis-just : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
   {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) (A ⊎ R)}
   → viewV nP at a ≡ just t′ → iterV k nP at a ≡ just (iter-bind t′ k)
iter-bind-cont-vis-just k nP {at} {a} eq with viewV nP at a | eq
... | just t′ | refl = refl

iter-bind-cont-tau-just : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
   {i : AnyTypes (ExtI E)} {a : proj₁ i} {t′ : PTree E (ExtI E) (A ⊎ R)}
   → viewT nP i a ≡ just t′ → iterT k nP i a ≡ just (iter-bind t′ k)
iter-bind-cont-tau-just k nP {i} {a} eq with viewT nP i a | eq
... | just t′ | refl = refl

-- LIFT a visible big-step run of `P` into `iter-bind P k`.
-- Same shape as `lift-bind-bigstep` (CSP.Laws.FD.BindFD), with the
-- `bind-*` lemmas replaced by their `iter-bind-*` analogs.
lift-iter-bigstep : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (P P′ : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
   (vs : List Event)
   → P ⟹⟨ map evl vs ⟩ P′ → (iter-bind P k) ⟹⟨ map evl vs ⟩ (iter-bind P′ k)
lift-iter-bigstep P P′ k []         ⟹-refl              = ⟹-refl
lift-iter-bigstep P P′ k []         (⟹-τ step rest) with τ-inv step
... | inj₁ eqf                       =
        ⟹-τ (sSil (iter-bind-force-sil P k eqf)) (lift-iter-bigstep _ P′ k [] rest)
... | inj₂ (v , τc , i , a , eqf , eqj) =
        ⟹-τ (sTau (iter-bind-force-react P k eqf)
                  (iter-bind-cont-tau-just k (react v τc) eqj))
            (lift-iter-bigstep _ P′ k [] rest)
lift-iter-bigstep P P′ k (x ∷ vs′) (⟹-τ step rest) with τ-inv step
... | inj₁ eqf                       =
        ⟹-τ (sSil (iter-bind-force-sil P k eqf)) (lift-iter-bigstep _ P′ k (x ∷ vs′) rest)
... | inj₂ (v , τc , i , a , eqf , eqj) =
        ⟹-τ (sTau (iter-bind-force-react P k eqf)
                  (iter-bind-cont-tau-just k (react v τc) eqj))
            (lift-iter-bigstep _ P′ k (x ∷ vs′) rest)
lift-iter-bigstep P P′ k (evLabel A e a ∷ vs′) (⟹-ev step rest) with ev-inv step
... | (v , τc , eqf , eqj) =
        ⟹-ev (sVis (iter-bind-force-react P k eqf)
                   (iter-bind-cont-vis-just k (react v τc) eqj))
             (lift-iter-bigstep _ P′ k vs′ rest)

-- ============================================================================
-- Task 3: IterSplit + iter-bind-inv
-- ============================================================================

-- Transport a single step across an equal `force` (mirrors `BindFD.─►-force-cong`).
─►-force-cong : ∀ {ℓr} {R : Set ℓr} {p q t : PTree E (ExtI E) R} {l : Label R}
   → PTree.force p ≡ PTree.force q
   → p ─[ l ]─► t → q ─[ l ]─► t
─►-force-cong eq (sRet ef)    = sRet  (trans (sym eq) ef)
─►-force-cong eq (sSil ef)    = sSil  (trans (sym eq) ef)
─►-force-cong eq (sVis ef ej) = sVis  (trans (sym eq) ef) ej
─►-force-cong eq (sTau ef ej) = sTau  (trans (sym eq) ef) ej

-- A run out of `deadlock` is empty: deadlock's force is an all-`nothing` react,
-- so no step constructor fires; the run must be `⟹-refl`.
deadlock-run-inv : ∀ {ℓr} {R : Set ℓr} {T : PTree E (ExtI E) R} {s : List (Event√ R)}
   → deadlock ⟹⟨ s ⟩ T → s ≡ [] × T ≡ deadlock
deadlock-run-inv ⟹-refl                 = refl , refl
deadlock-run-inv (⟹-τ (sSil ()) _)
deadlock-run-inv (⟹-τ (sTau refl ()) _)
deadlock-run-inv (⟹-ev (sRet ()) _)
deadlock-run-inv (⟹-ev (sVis refl ()) _)

-- The IterSplit invariant: a run of `iter-bind P k` decomposes into
--   • in-body : P still executing (visible run into P′; T ≡ iter-bind P′ k);
--   • in-done : P returned `inj₂ r` (the loop terminates: a √-tick to deadlock);
--   • in-loop : P returned `inj₁ a′` (loop back: `iter k a′` runs on to T).
data IterSplit {ℓr} {A : Set ℓ} {R : Set ℓr}
   (P : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
   (T : PTree E (ExtI E) R) : List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  in-body : ∀ {P′} {vs : List Event}
          → P ⟹⟨ map evl vs ⟩ P′ → T ≡ iter-bind P′ k
          → IterSplit P k T (map evl vs)
  in-done : ∀ {r : R} {s₁ : List Event} {Pᵣ}
          → P ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₂ r) → T ≡ deadlock
          → IterSplit P k T (map evl s₁ ++ (√ r ∷ []))
  in-loop : ∀ {a′ : A} {s₁ : List Event} {s₂ : List (Event√ R)} {Pᵣ}
          → P ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ a′)
          → iter k a′ ⟹⟨ s₂ ⟩ T
          → IterSplit P k T (map evl s₁ ++ s₂)

-- Re-wrap a recursive IterSplit by prepending one τ-step (from P to its
-- silent/τ-successor `c`) onto P's run.  All three arms carry a `P ⟹ …`.
prepend-τ-Iter : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   {P c : PTree E (ExtI E) (A ⊎ R)} {k : A → PTree E (ExtI E) (A ⊎ R)}
   {T : PTree E (ExtI E) R} {s : List (Event√ R)}
   → (P ─[ τ ]─► c)
   → IterSplit c k T s → IterSplit P k T s
prepend-τ-Iter pstep (in-body cstep eq)        = in-body (⟹-τ pstep cstep) eq
prepend-τ-Iter pstep (in-done cstep fe te)      = in-done (⟹-τ pstep cstep) fe te
prepend-τ-Iter pstep (in-loop cstep fe kr)      = in-loop (⟹-τ pstep cstep) fe kr

-- Re-wrap a recursive IterSplit by prepending one visible step (from P to its
-- visible successor `t`, on event `evLabel A e a`).  The trace grows by
-- `evl (evLabel A e a)` at the front (matching `⟹-ev`).
prepend-ev-Iter : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   {P t : PTree E (ExtI E) (A ⊎ R)} {k : A → PTree E (ExtI E) (A ⊎ R)}
   {T : PTree E (ExtI E) R} {s : List (Event√ R)}
   {B : Set ℓ} {e : E B} {a : B}
   → (P ─[ ev (evl (evLabel B e a)) ]─► t)
   → IterSplit t k T s → IterSplit P k T (evl (evLabel B e a) ∷ s)
prepend-ev-Iter {B = B} {e} {a} pstep (in-body {vs = vs} cstep eq) =
  in-body {vs = evLabel B e a ∷ vs} (⟹-ev pstep cstep) eq
prepend-ev-Iter {B = B} {e} {a} pstep (in-done {s₁ = s₁} cstep fe te) =
  in-done {s₁ = evLabel B e a ∷ s₁} (⟹-ev pstep cstep) fe te
prepend-ev-Iter {B = B} {e} {a} pstep (in-loop {s₁ = s₁} cstep fe kr) =
  in-loop {s₁ = evLabel B e a ∷ s₁} (⟹-ev pstep cstep) fe kr

-- injectivity of the head constructors (mirror `BindFD.sil-inj`/`react-inj-*`).
sil-inj : ∀ {ℓi ℓa} {I : Set ℓ → Set ℓi} {A : Set ℓa} {x y : PTree E I A}
        → _≡_ {A = NodeKind E I A} (sil x) (sil y) → x ≡ y
sil-inj refl = refl

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
-- together with the witnessing iter-bind-shape `iter-bind t′ k ≡ q` of the target
-- (mirror `BindFD.bindT-inv`/`bindV-inv`; same shape as iterV/iterT match viewV/viewT).
iterT-inv : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (k : A → PTree E (ExtI E) (A ⊎ R))
   (v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) (A ⊎ R))))
   (τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) (A ⊎ R))))
   {i a} {q : PTree E (ExtI E) R}
   → iterT k (react v τc) i a ≡ just q
   → Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ]
       (τc i a ≡ just t′ × iter-bind t′ k ≡ q)
iterT-inv k v τc {i} {a} ej with τc i a in vtq
... | just t′ = t′ , refl , just-inj ej
  where just-inj : ∀ {q} → just (iter-bind t′ k) ≡ just q → iter-bind t′ k ≡ q
        just-inj refl = refl

iterV-inv : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (k : A → PTree E (ExtI E) (A ⊎ R))
   (v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) (A ⊎ R))))
   (τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) (A ⊎ R))))
   {at a} {q : PTree E (ExtI E) R}
   → iterV k (react v τc) at a ≡ just q
   → Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ]
       (v at a ≡ just t′ × iter-bind t′ k ≡ q)
iterV-inv k v τc {at} {a} ej with v at a in vvq
... | just t′ = t′ , refl , just-inj ej
  where just-inj : ∀ {q} → just (iter-bind t′ k) ≡ just q → iter-bind t′ k ≡ q
        just-inj refl = refl

iter-bind-inv : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (P : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
   {T : PTree E (ExtI E) R} {s : List (Event√ R)}
   → (iter-bind P k) ⟹⟨ s ⟩ T → IterSplit P k T s
-- refl: independent of `force P` — P stays put, T ≡ iter-bind P k.
iter-bind-inv P k ⟹-refl = in-body {vs = []} ⟹-refl refl
-- ── τ via sSil ──────────────────────────────────────────────────────────────
iter-bind-inv P k (⟹-τ (sSil eqf) rest) with PTree.force P in eqP | eqf
... | ret (inj₁ a′) | eqf′
      -- force(iter-bind P k) ≡ sil (iter k a′); HAND `rest` back directly (no recursion).
      rewrite sym (sil-inj eqf′) =
        in-loop {s₁ = []} ⟹-refl eqP rest
... | ret (inj₂ r)  | ()    -- force(iter-bind P k) ≡ ret ≠ sil
... | sil c         | eqf′
      -- force(iter-bind P k) ≡ sil (iter-bind c k); recurse on c.
      rewrite sym (sil-inj eqf′) =
        prepend-τ-Iter (sSil eqP) (iter-bind-inv c k rest)
... | react v τc    | ()    -- force(iter-bind P k) ≡ react ≠ sil
-- ── τ via sTau ──────────────────────────────────────────────────────────────
iter-bind-inv P k (⟹-τ (sTau eqf eqj) rest) with PTree.force P in eqP | eqf
... | ret (inj₁ a′) | ()    -- force(iter-bind P k) ≡ sil ≠ react
... | ret (inj₂ r)  | ()    -- force(iter-bind P k) ≡ ret ≠ react
... | sil c         | ()    -- force(iter-bind P k) ≡ sil ≠ react
... | react v τc    | eqf′
      rewrite sym (react-inj-τ eqf′) with iterT-inv k v τc eqj
...   | (t′ , vtq , refl) =
        prepend-τ-Iter (sTau eqP vtq) (iter-bind-inv t′ k rest)
-- ── visible step via sVis ────────────────────────────────────────────────────
iter-bind-inv P k (⟹-ev (sVis eqf eqj) rest) with PTree.force P in eqP | eqf
... | ret (inj₁ a′) | ()    -- force(iter-bind P k) ≡ sil ≠ react
... | ret (inj₂ r)  | ()    -- force(iter-bind P k) ≡ ret ≠ react
... | sil c         | ()    -- force(iter-bind P k) ≡ sil ≠ react
... | react v τc    | eqf′
      rewrite sym (react-inj-v eqf′) with iterV-inv k v τc eqj
...   | (t′ , vvq , refl) =
        prepend-ev-Iter (sVis eqP vvq) (iter-bind-inv t′ k rest)
-- ── √ tick via sRet ──────────────────────────────────────────────────────────
-- A `√ r` step can only fire once `force(iter-bind P k) ≡ ret r`, i.e. P returned
-- `inj₂ r`; the step goes to deadlock and the run can do nothing more.
iter-bind-inv P k (⟹-ev (sRet eqf) rest) with PTree.force P in eqP | eqf
... | ret (inj₁ a′) | ()    -- force(iter-bind P k) ≡ sil ≠ ret
... | ret (inj₂ r)  | refl with deadlock-run-inv rest
...   | refl , refl =
        in-done {s₁ = []} ⟹-refl eqP refl
iter-bind-inv P k (⟹-ev (sRet eqf) rest) | sil c      | ()  -- force ≡ sil ≠ ret
iter-bind-inv P k (⟹-ev (sRet eqf) rest) | react v τc | ()  -- force ≡ react ≠ ret

-- ============================================================================
-- Task 4: LoopSplit + loop0 trace inversion/intro
-- ============================================================================

-- `loop`'s private `where` step is  `λ a → (λ _ → body) a >>= λ a′ → Ret (inj₁ a′)`.
-- These top-level abbreviations are DEFINITIONALLY what `loop0 body` unfolds to:
--   loop0 body = loop (λ _ → body) tt = iter (loopStep body) tt
--              = iter-bind (loopStep body tt) (loopStep body)   (definitionally).
loop-k : ∀ {ℓr} {R : Set ℓr} → ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)
loop-k a′ = Ret (inj₁ a′)

loopStep : ∀ {ℓr} {R : Set ℓr}
         → PTree E (ExtI E) (⊤ {ℓ}) → ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)
loopStep body a = body >>= loop-k

-- sanity: loop0 body reduces to iter-bind (loopStep body tt) (loopStep body).
loop0-unfold : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
             → loop0 {R = R} body ≡ iter-bind (loopStep body tt) (loopStep body)
loop0-unfold body = refl

-- ── discharging the impossible in-done (inj₂) case for loopStep ──────────────
-- loopStep body a = body >>= loop-k, and loop-k a′ = Ret (inj₁ a′), so every
-- `ret` reachable through loopStep carries an inj₁ tag.  Hence a loopStep run
-- ending at a tree whose force is `ret (inj₂ r)` is impossible.

-- A `ret (inj₁ x)`-forced tree cannot run to a tree forced to ret (inj₂ r).
-- The only steps out of `ret (inj₁ x)` are the √-tick to deadlock (whose force
-- is a react, not a ret), so the run is either refl (force stays ret (inj₁ x))
-- or one √-step into deadlock (force a react).
ret-inj₁-run-no-inj₂ : ∀ {ℓr} {R : Set ℓr} {x : ⊤ {ℓ}} {r : R}
   {P T : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)} {s : List (Event√ (⊤ {ℓ} ⊎ R))}
   → force P ≡ ret (inj₁ x) → P ⟹⟨ s ⟩ T → force T ≡ ret (inj₂ r) → ⊥
ret-inj₁-run-no-inj₂ eqP ⟹-refl eqT
  with trans (sym eqP) eqT
... | ()
ret-inj₁-run-no-inj₂ eqP (⟹-τ (sSil eqf) _) _
  with trans (sym eqP) eqf
... | ()
ret-inj₁-run-no-inj₂ eqP (⟹-τ (sTau eqf _) _) _
  with trans (sym eqP) eqf
... | ()
ret-inj₁-run-no-inj₂ eqP (⟹-ev (sVis eqf _) _) _
  with trans (sym eqP) eqf
... | ()
ret-inj₁-run-no-inj₂ eqP (⟹-ev (sRet _) rest) eqT
  -- step goes to deadlock; deadlock's force is a react, never ret.
  with deadlock-run-inv rest
... | refl , refl with eqT
...   | ()

-- The `>>=`-into-`loop-k` shape: force (P′ >>= loop-k) is never ret (inj₂ r).
-- By the bind force equation it is `ret` only when force P′ ≡ ret y, where it
-- equals force (loop-k y) = ret (inj₁ y).
bind-loopk-force-no-inj₂ : ∀ {ℓr} {R : Set ℓr} {r : R}
   (P′ : PTree E (ExtI E) (⊤ {ℓ}))
   → force (P′ >>= loop-k {R = R}) ≡ ret (inj₂ r) → ⊥
bind-loopk-force-no-inj₂ P′ eq with force P′
... | ret y      with eq
...   | ()
bind-loopk-force-no-inj₂ P′ eq | sil c     with eq
...   | ()
bind-loopk-force-no-inj₂ P′ eq | react v τc with eq
...   | ()

-- loopStep never reaches a `ret (inj₂ r)` state.
loopStep-no-inj₂ : ∀ {ℓr} {R : Set ℓr} {r : R}
   (body : PTree E (ExtI E) (⊤ {ℓ}))
   {Pᵣ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)} {s : List (Event√ (⊤ {ℓ} ⊎ R))}
   → (loopStep body tt) ⟹⟨ s ⟩ Pᵣ → force Pᵣ ≡ ret (inj₂ r) → ⊥
loopStep-no-inj₂ body run eqPᵣ
  with bind-bigstep-inv body loop-k run
... | BindSplit.in-P {P′ = P′} _ refl =
      bind-loopk-force-no-inj₂ P′ eqPᵣ
... | BindSplit.in-k {r = r'} _ _ kr =
      -- loop-k r' = Ret (inj₁ r'), force = ret (inj₁ r'); cannot reach inj₂.
      ret-inj₁-run-no-inj₂ {x = r'} refl kr eqPᵣ

-- ── LoopSplit ────────────────────────────────────────────────────────────────
-- LoopSplit specialises IterSplit to `loop0 body`: the step never returns
-- inj₂, so the `in-done` arm is absent.
data LoopSplit {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
   (T : PTree E (ExtI E) R) : List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  in-body : ∀ {P′} {vs : List Event}
          → (loopStep {R = R} body tt) ⟹⟨ map evl vs ⟩ P′
          → T ≡ iter-bind P′ (loopStep body) → LoopSplit body T (map evl vs)
  in-loop : ∀ {s₁ : List Event} {s₂ : List (Event√ R)} {Pᵣ}
          → (loopStep {R = R} body tt) ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ tt)
          → loop0 {R = R} body ⟹⟨ s₂ ⟩ T → LoopSplit body T (map evl s₁ ++ s₂)

-- loop-trace : a run of `loop0 body` decomposes into a LoopSplit.  Obtained
-- by specialising `iter-bind-inv` (loop0 body = iter-bind (loopStep body tt)
-- (loopStep body) definitionally) and translating IterSplit → LoopSplit; the
-- in-done arm is discharged by `loopStep-no-inj₂`.  In the in-loop arm,
-- `a′ : ⊤` is forced to `tt`, and `iter (loopStep body) tt = loop0 body`.
loop-trace : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ})) {T s}
           → (loop0 body) ⟹⟨ s ⟩ T → LoopSplit body T s
loop-trace {R = R} body run
  with iter-bind-inv (loopStep {R = R} body tt) (loopStep body) run
... | IterSplit.in-body bs eq              = in-body bs eq
... | IterSplit.in-loop {a′ = tt} bs fe kr = in-loop bs fe kr
... | IterSplit.in-done bs fe _            = ⊥-elim (loopStep-no-inj₂ body bs fe)

-- The loop-back step: when `force Pᵣ ≡ ret (inj₁ tt)`, `iter-bind Pᵣ (loopStep
-- body)` does a single τ to `iter (loopStep body) tt = loop0 body`.
loop-back-sil : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
   (Pᵣ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R))
   → force Pᵣ ≡ ret (inj₁ tt)
   → force (iter-bind Pᵣ (loopStep body)) ≡ sil (loop0 body)
loop-back-sil body Pᵣ fe with force Pᵣ | fe
... | ret (inj₁ tt) | refl = refl

-- loop-trace-intro : reassemble a LoopSplit into a run of `loop0 body`.
loop-trace-intro : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
                   {T : PTree E (ExtI E) R} {s : List (Event√ R)}
                 → LoopSplit body T s → (loop0 {R = R} body) ⟹⟨ s ⟩ T
-- in-body: lift the loopStep run into iter-bind, then transport via T ≡ ….
--   loop0 body = iter-bind (loopStep body tt) (loopStep body)  (definitionally).
loop-trace-intro {R = R} body (in-body {P′ = P′} {vs = vs} bs refl) =
  lift-iter-bigstep (loopStep {R = R} body tt) P′ (loopStep body) vs bs
-- in-loop: lift the loopStep prefix, append the τ loop-back (force Pᵣ ≡
-- ret (inj₁ tt) ⇒ force (iter-bind Pᵣ …) ≡ sil (iter (loopStep body) tt) =
-- sil (loop0 body)), then ⟹-trans with the loop0 continuation.
loop-trace-intro {R = R} body (in-loop {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} bs fe cont) =
  ⟹-trans
    (lift-iter-bigstep (loopStep {R = R} body tt) Pᵣ (loopStep body) s₁ bs)
    (⟹-τ (sSil (loop-back-sil body Pᵣ fe)) cont)

-- ============================================================================
-- Task 5: loop0 FAILURES⊥ characterisation (LoopFailureSplit + elim/intro)
-- ============================================================================

-- A failure of `loop0 body` is a reached state `Q` (a `LoopSplit`) that refuses
-- the ban-set `B`.  `failures (loop0 body) s B = Σ[ Q ] (run × Refuses Q B)`;
-- `LoopFailureSplit` packages the same data with the run replaced by its
-- `LoopSplit` decomposition.  Unlike BindFD's `bind-failures⊥-elim`, the elim
-- here needs NO residual-suffix generalisation: `loop-trace`/`loop-trace-intro`
-- are total inverses on the whole run, so a bare `Refuses Q B` on the reached
-- state suffices and the divergence half passes straight through.
data LoopFailureSplit {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
   (B : Event√ R → Set ℓr) : List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  loop-fail : ∀ {Q s} → LoopSplit body Q s → Refuses Q B → LoopFailureSplit body B s

-- elim: a failure⊥ of `loop0 body` is a `LoopFailureSplit` (a reached refusing
-- state, via `loop-trace`) or a divergence of `loop0 body` (passed through).
loop0-failures⊥-elim : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
   {s : List (Event√ R)} {B : Event√ R → Set ℓr}
   → failures⊥ (loop0 body) s B
   → LoopFailureSplit body B s ⊎ divergences (loop0 body) s
loop0-failures⊥-elim body (inj₁ (Q , run , ref)) =
  inj₁ (loop-fail (loop-trace body run) ref)
loop0-failures⊥-elim body (inj₂ d) = inj₂ d

-- intro: a `LoopFailureSplit` (a genuine reached-refusal) is a failure⊥ of
-- `loop0 body` (reassemble the run via `loop-trace-intro`, keep the refusal).
loop0-failures⊥-intro-failures : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
   {s : List (Event√ R)} {B : Event√ R → Set ℓr}
   → LoopFailureSplit body B s → failures⊥ (loop0 body) s B
loop0-failures⊥-intro-failures body (loop-fail {Q = Q} sp ref) =
  inj₁ (Q , loop-trace-intro body sp , ref)

-- ============================================================================
-- Task 6: loop0 DIVERGENCE characterisation (LoopDivergenceSplit + elim/intro)
--          + the canonical silent-spin divergence.
-- ============================================================================

open IsDivergence
open Diverges

-- A divergence of `loop0 body` is: a `LoopSplit`-reached state `Q` at some
-- visible prefix that DIVERGES (`Diverges Q`), with the full divergence trace
-- `s` being that prefix extended by an arbitrary suffix `s ≡ prefix ++ suffix`.
--
-- INDEX/SUFFIX HANDLING.  Mirrors `IsDivergence` itself: the `LoopSplit` is taken
-- at the divergence *prefix*, and `loop-div` carries the `prefix ++ suffix`
-- split so the data type stays indexed by the full trace `s`.  This is the
-- minimal generalisation that makes `loop-trace`/`loop-trace-intro` (which invert
-- the WHOLE reach) line up with the suffix-bearing `IsDivergence` record.
data LoopDivergenceSplit {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
   : List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  loop-div : ∀ {Q prefix suffix s} → s ≡ prefix ++ suffix
           → LoopSplit body Q prefix → Diverges Q → LoopDivergenceSplit body s

-- elim: a divergence of `loop0 body` decomposes into a `LoopSplit` to a
-- diverging state.  Invert the divergence's `reach` with `loop-trace`, repackage
-- with the record's `divwit`, and carry the `split` (prefix/suffix) through.
loop0-div-elim : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ})) {s : List (Event√ R)}
   → divergences (loop0 body) s → LoopDivergenceSplit {R = R} body s
loop0-div-elim body d =
  loop-div (d .split) (loop-trace body (d .reach)) (d .divwit)

-- intro: a `LoopSplit`-to-diverging-state is a divergence of `loop0 body`.
-- Reassemble the reach via `loop-trace-intro`, keep the `Diverges` witness, and
-- restore the prefix/suffix split into the `IsDivergence` record.
loop0-div-intro : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ})) {s : List (Event√ R)}
   → LoopDivergenceSplit {R = R} body s → divergences (loop0 body) s
loop0-div-intro body (loop-div {Q = Q} {prefix = prefix} {suffix = suffix} eq sp dv) = record
  { prefix  = prefix
  ; suffix  = suffix
  ; split   = eq
  ; witness = Q
  ; reach   = loop-trace-intro body sp
  ; divwit  = dv
  }

-- THE canonical silent-spin divergence: if `body` terminates (force ≡ ret tt),
-- `loop0 body` τ-spins forever.  Then
--   force (loopStep body tt) = force (body >>= loop-k) = force (loop-k tt)
--                            = force (Ret (inj₁ tt)) = ret (inj₁ tt)
-- so by the iter-bind `ret (inj₁ tt) → sil (iter (loopStep body) tt)` clause
-- (packaged by `loop-back-sil`) we get the self-τ-step
--   force (loop0 body) ≡ sil (loop0 body),
-- and the coinductive `Diverges` is built guarded under `.rest`.
loop0-spins-diverges : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
   → force body ≡ ret tt
   → Diverges (loop0 {R = R} body)
loop0-spins-diverges {R = R} body eq .next = loop0 body
loop0-spins-diverges {R = R} body eq .step =
  sSil (loop-back-sil body (loopStep body tt) (bind-force-ret body loop-k eq))
loop0-spins-diverges {R = R} body eq .rest = loop0-spins-diverges body eq

-- ============================================================================
-- THE ITERATE / LOOP "KÖNIG STEP" — stated DIRECTLY (not via `dne`), the FD
-- layer's iterate-divergence classical postulate.
--
-- A divergence of `iter-bind Q (loopStep body)` (an infinite τ-chain of one
-- loop iteration whose source is `Q`, threaded through the loop-back) is either:
--   • a divergence of the CURRENT iteration's source `Q` (the loop never
--     completes this iteration — body-internal livelock), OR
--   • the iteration COMPLETES: `Q` silently reaches a loop-back state
--     (`force ≡ ret (inj₁ tt)`, i.e. `iter (loopStep body) tt = loop0 body`)
--     and the residual loop `loop0 body` itself diverges (the loop spins).
--
-- Deciding WHICH — does the infinite τ-chain stay inside this iteration's `Q`,
-- or does `Q` silently terminate and the loop carry the divergence forward — is
-- a König / infinite-pigeonhole step over an infinite τ-future, no more
-- constructive than `□-Diverges→` / `Par-Diverges→` / `>>-Diverges→`.  It is the
-- single classical postulate of the loop-level FD refinement-monotonicity
-- sub-project (see docs/notes/fd-classical-postulates.md, Postulate "iterate
-- König step").
--
-- CERTIFIED sound — derivable from the single `dne` axiom — in the standalone
-- module CSP.Laws.ClassicalFromLEM (Derivation 6), by the same DAcc / well-founded
-- τ-accessibility route as `>>-Diverges→`: a τ of `iter-bind Q (loopStep body)`
-- either advances `Q` (stays in iter-bind form) or is the loop-back `sSil` (`Q`
-- at `ret (inj₁ tt)`, handing to `loop0 body`); so an infinite τ-chain forces
-- either an infinite τ-chain inside `Q` or infinitely many loop-backs.  Nothing
-- imports ClassicalFromLEM, so no axiom leaks here.
-- ============================================================================
postulate
  loop-Diverges→ : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
                     (Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R))
                 → Diverges (iter-bind Q (loopStep body))
                 → Diverges Q
                 ⊎ (Σ[ Qᵣ ∈ PTree E (ExtI E) (⊤ {ℓ} ⊎ R) ]
                      (Q ─[τ*]─► Qᵣ) × (force Qᵣ ≡ ret (inj₁ tt))
                      × Diverges (loop0 {R = R} body))

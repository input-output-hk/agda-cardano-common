{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <-trans; m≤n⇒m≤1+n)
open import Data.Nat.Induction using (<-wellFounded; Acc; acc)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.IterateMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree
open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; failures; _⊑T_)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊑F⊥_; _⊑D_; _⊑FD_; failures⊥; divergences; IsDivergence; div-extension-closed; empty-div)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses; Offers; deadlock-refuses)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges; deadlock-converges)
-- generic stability facts, kept qualified: the historic local names below differ from
-- the canonical ones only in argument order.
import Semantics.Stability {E = E} {I = ExtI E} as S
open import CSP.Laws.FD.BindFD     E-≟
  using (BindSplit; bind-bigstep-inv; lift-bind-bigstep; bind-force-ret
        ; bind-force-react; bind-force-sil; bind-cont-vis-just; ⟹-trans
        ; bind-failures⊥-intro-P; bind-failures⊥-intro-k; bindV-inv; bindT-inv; react-inj-v
        ; Diverges->>=; bind-div-intro-P; evl-split)
open import CSP.Laws.FD.IterateFD  E-≟
  using (LoopSplit; loopStep; loop-k; loop-trace; loop-trace-intro
        ; LoopFailureSplit; loop-fail
        ; loop0-failures⊥-elim; loop0-failures⊥-intro-failures
        ; loop0-div-intro; loop0-div-elim; LoopDivergenceSplit; loop-div
        ; loop0-spins-diverges; loop-Diverges→
        ; iter-bind-cont-vis-just; iter-bind-cont-tau-just; iter-bind-force-react
        ; iterV-inv; lift-iter-bigstep
        ; loop-back-sil; deadlock-run-inv
        ; sil-inj; react-inj-τ; loopStep-no-inj₂; iterT-inv)
open import Semantics.WeakBisim {E = E} {I = ExtI E} using (_─[τ*]─►_; τ*-refl; τ*-step)
open import Data.List.Properties using (++-identityʳ; map-++; ++-assoc)
open Diverges
open IsDivergence

-- ============================================================================
-- Ban-set retagging across the loop's carrier changes.
--
-- `loop0 body : PTree E (ExtI E) R` is a NEVER-returning loop, so its result
-- type `R` is phantom.  We therefore work at the canonical level `ℓr ≡ ℓ`
-- (`R : Set ℓ`, `B : Event√ R → Set ℓ`); this lets a ban set cross the carrier
-- changes `R → ⊤ ⊎ R → ⊤` (all `Set ℓ`) that `iter-bind`/`>>= loop-k` introduce.
-- Only VISIBLE events are ever offered by a stable node, so the retag keeps the
-- event part and bans no `√`.
-- ============================================================================

banEvl : ∀ {ℓr} {X : Set ℓr} → (Event → Set ℓ) → Event√ X → Set ℓ
banEvl P (evl e) = P e
banEvl P (√ _)   = Lift ℓ ⊥

-- A `√`-event is never in a `banEvl` set.
banEvl-no-√ : ∀ {ℓr} {X : Set ℓr} {P : Event → Set ℓ} {x : X} → ¬ (banEvl {X = X} P (√ x))
banEvl-no-√ ()

-- ----------------------------------------------------------------------------
-- iter-bind layer: offers / stability correspond to those of the source `Q`.
-- ----------------------------------------------------------------------------

-- INTRO: a visible offer of `Q` lifts to one of `iter-bind Q k` (same event).
iter-offer-intro : ∀ {ℓr} {R : Set ℓr} (k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R))
   {Q t′ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)} {A : Set ℓ} {e : E A} {a : A}
   → Q ─[ ev (evl (evLabel A e a)) ]─► t′
   → iter-bind Q k ─[ ev (evl (evLabel A e a)) ]─► iter-bind t′ k
iter-offer-intro k {Q = Q} step with ev-inv step
... | (v , τc , eqf , ej) =
      sVis (iter-bind-force-react Q k eqf)
           (iter-bind-cont-vis-just k (react v τc) ej)

-- force equations for the ret-source `iter-bind` cases (loop-back / done).
iter-bind-force-ret₁ : ∀ {ℓr} {R : Set ℓr}
   (Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)) (k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)) {a′}
   → force Q ≡ ret (inj₁ a′) → force (iter-bind Q k) ≡ sil (iter k a′)
iter-bind-force-ret₁ Q k eq with force Q | eq
... | ret (inj₁ a′) | refl = refl

iter-bind-force-ret₂ : ∀ {ℓr} {R : Set ℓr}
   (Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)) (k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)) {r}
   → force Q ≡ ret (inj₂ r) → force (iter-bind Q k) ≡ ret r
iter-bind-force-ret₂ Q k eq with force Q | eq
... | ret (inj₂ r) | refl = refl

iter-bind-force-sil : ∀ {ℓr} {R : Set ℓr}
   (Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)) (k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)) {c}
   → force Q ≡ sil c → force (iter-bind Q k) ≡ sil (iter-bind c k)
iter-bind-force-sil Q k eq with force Q | eq
... | sil c | refl = refl

-- The five helpers below are GENERIC stability facts, proved once in
-- `Semantics.Stability`; they are kept here under their historic names (and historic
-- argument order) as aliases.

-- `isStable` is read off `force`: transport it across an equal force.
stable-force-eq : ∀ {ℓr} {R : Set ℓr} {p q : PTree E (ExtI E) R}
   → force p ≡ force q → isStable q → isStable p
stable-force-eq {p = p} {q} = S.stable-force-eq {p = p} {q = q}

-- `isStable` for a react-forced tree is exactly "the τ-map is everywhere nothing".
stable-react : ∀ {ℓr} {R : Set ℓr} {Q : PTree E (ExtI E) R}
   {v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) R))}
   {τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) R))}
   → force Q ≡ react v τc → (∀ i a → τc i a ≡ nothing) → isStable Q
stable-react {Q = Q} = S.mk-stable {t = Q}

-- inverse of `stable-react`: a stable react-forced tree has an everywhere-nothing τ-map.
stable-react-elim : ∀ {ℓr} {R : Set ℓr} {Q : PTree E (ExtI E) R}
   {v  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) R))}
   {τc : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) R))}
   → force Q ≡ react v τc → isStable Q → (∀ i a → τc i a ≡ nothing)
stable-react-elim {Q = Q} eqQ st = S.stable-react-τc {t = Q} st eqQ

-- a sil/ret-forced tree is never stable.
sil-not-stable : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R} {c}
   → force t ≡ sil c → isStable t → ⊥
sil-not-stable {t = t} eq st = S.stable-not-sil {t = t} st eq
ret-not-stable : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R} {r}
   → force t ≡ ret r → isStable t → ⊥
ret-not-stable {t = t} eq st = S.stable-not-ret {t = t} st eq

-- STABILITY reflection: a stable `iter-bind Q k` forces `Q` to be stable too.
-- ret/sil sources make `iter-bind Q k` force to sil/ret (un-stable), absurd.
iter-stable-elim : ∀ {ℓr} {R : Set ℓr} {k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   {Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → isStable (iter-bind Q k) → isStable Q
iter-stable-elim {k = k} {Q = Q} st with PTree.force Q in eqQ
-- In each non-react branch the `with`-abstraction on `force Q` already forces
-- `force (iter-bind Q k)` to a sil/ret, so `isStable (iter-bind Q k)` reduces to
-- the empty `Lift ⊥` and `st` is directly absurd.
... | ret (inj₁ a′) = ⊥-elim (lower st)
... | ret (inj₂ r)  = ⊥-elim (lower st)
... | sil c         = ⊥-elim (lower st)
... | react v τc    = iterT-nil   -- goal `isStable Q` reduces to `∀ i a → τc i a ≡ nothing`
      where
        -- `force Q` is abstracted to `react v τc` here, so `force (iter-bind Q k)`
        -- reduces to a `react` with τ-map `iterT k (react v τc)`; hence the
        -- stability hypothesis `st` already IS the everywhere-`nothing` proof.
        st-react : ∀ i a → iterT k (react v τc) i a ≡ nothing
        st-react = st
        iterT-nil : ∀ i a → τc i a ≡ nothing
        iterT-nil i a with τc i a in vt
        ... | nothing  = refl
        ... | just t″  = ⊥-elim (just≢nothing (trans (sym (iterT-just i a vt)) (st-react i a)))
          where iterT-just : ∀ i a → τc i a ≡ just t″
                            → iterT k (react v τc) i a ≡ just (iter-bind t″ k)
                iterT-just i a e with τc i a | e
                ... | just _ | refl = refl
                just≢nothing : ∀ {ℓx} {X : Set ℓx} {x : X} → just x ≡ nothing → ⊥
                just≢nothing ()

-- `map evl` is injective in its visible-list argument (across carriers): the
-- underlying `evl` constructor is injective, so equal `map evl` lists agree on
-- the source `List Event`.  Used to bridge the `⊤ ⊎ R` / `R` carrier mismatch.
-- `unEvl`: project a `List (Event√ X)` back to `List Event`, keeping only `evl`s.
unEvl : ∀ {ℓr} {R : Set ℓr} → List (Event√ R) → List Event
unEvl []          = []
unEvl (evl e ∷ s) = e ∷ unEvl s
unEvl (√ _   ∷ s) = unEvl s

unEvl-map : ∀ {ℓr} {R : Set ℓr} (vs : List Event) → unEvl (map (evl {R = R}) vs) ≡ vs
unEvl-map []        = refl
unEvl-map (v ∷ vs)  = cong (v ∷_) (unEvl-map vs)

map-evl-inj : ∀ {ℓr} {R : Set ℓr} {xs ys : List Event}
   → map (evl {R = R}) xs ≡ map (evl {R = R}) ys → xs ≡ ys
map-evl-inj {R = R} {xs = xs} {ys = ys} eq =
  trans (sym (unEvl-map {R = R} xs)) (trans (cong unEvl eq) (unEvl-map {R = R} ys))

-- A `ret`-forced tree is STUCK under a purely-visible (`map evl`) run: a `ret`
-- offers only its `√` (never an `evl`), so an all-`evl` trace forces the run to
-- be `⟹-refl`; hence the endpoint still forces to the same `ret`.
ret-stuck : ∀ {ℓr} {R : Set ℓr} {Q P′ : PTree E (ExtI E) R} {x : R} (vs : List Event)
   → force Q ≡ ret x → Q ⟹⟨ map evl vs ⟩ P′ → force P′ ≡ ret x
ret-stuck []        eq ⟹-refl = eq
ret-stuck []        eq (⟹-τ step rest) with τ-inv step
... | inj₁ eqf                       with () ← trans (sym eq) eqf
ret-stuck []        eq (⟹-τ step rest) | inj₂ (v , τc , i , a , eqf , eqj)
      with () ← trans (sym eq) eqf
ret-stuck (x₁ ∷ vs) eq (⟹-τ step rest) with τ-inv step
... | inj₁ eqf                       with () ← trans (sym eq) eqf
ret-stuck (x₁ ∷ vs) eq (⟹-τ step rest) | inj₂ (v , τc , i , a , eqf , eqj)
      with () ← trans (sym eq) eqf
ret-stuck (x₁ ∷ vs) eq (⟹-ev (sVis eqf _) rest) with () ← trans (sym eq) eqf

-- STABILITY reflection through `>>= loop-k`: a stable `Q >>= loop-k` forces `Q`
-- stable.  Unlike a generic `k`, `loop-k r = Ret (inj₁ r)` forces to a `ret`, so
-- a `ret`-source makes `Q >>= loop-k` force to a `ret` (un-stable) — hence the
-- `ret` case is absurd just as for the `sil` case.
bind-stable-elim : ∀ {ℓr} {R : Set ℓr} {Q : PTree E (ExtI E) (⊤ {ℓ})}
   → isStable (Q >>= loop-k {R = R}) → isStable Q
bind-stable-elim {Q = Q} st with PTree.force Q in eqQ
... | ret r      = ⊥-elim (lower st)
... | sil c      = ⊥-elim (lower st)
... | react v τc = bindT-nil
      where
        st-react : ∀ i a → bindT loop-k (react v τc) i a ≡ nothing
        st-react = st
        bindT-nil : ∀ i a → τc i a ≡ nothing
        bindT-nil i a with τc i a in vt
        ... | nothing  = refl
        ... | just t″  = ⊥-elim (just≢nothing (trans (sym (bindT-just i a vt)) (st-react i a)))
          where bindT-just : ∀ i a → τc i a ≡ just t″
                           → bindT loop-k (react v τc) i a ≡ just (t″ >>= loop-k)
                bindT-just i a e with τc i a | e
                ... | just _ | refl = refl
                just≢nothing : ∀ {ℓx} {X : Set ℓx} {x : X} → just x ≡ nothing → ⊥
                just≢nothing ()

-- ----------------------------------------------------------------------------
-- OFFER reflection: a visible offer of `iter-bind Q k` comes from one of `Q`.
-- The endpoint is irrelevant for `Refuses`, so we only return the SOURCE offer.
-- ----------------------------------------------------------------------------

-- helper: read `iterV k (react v τc) (A,e) a ≡ just q` back to `v (A,e) a ≡ just _`,
-- and rebuild a visible offer of `Q` (`force Q ≡ react v τc`).
iter-offer-elim : ∀ {ℓr} {R : Set ℓr} {k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   {Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)} {e : Event}
   → Offers (iter-bind Q k) (evl e) → Offers Q (evl e)
iter-offer-elim {k = k} {Q = Q} {e = evLabel A ε a} (t′ , step) with ev-inv step
... | (v′ , τc′ , eqf , eqj) with force Q in eqQ
...   | ret (inj₁ a′) with () ← eqf
iter-offer-elim {k = k} {Q = Q} {e = evLabel A ε a} (t′ , step)
    | (v′ , τc′ , eqf , eqj) | ret (inj₂ r) with () ← eqf
iter-offer-elim {k = k} {Q = Q} {e = evLabel A ε a} (t′ , step)
    | (v′ , τc′ , eqf , eqj) | sil c with () ← eqf
iter-offer-elim {k = k} {Q = Q} {e = evLabel A ε a} (t′ , step)
    | (v′ , τc′ , eqf , eqj) | react v τc with react-inj-v eqf
...     | refl with iterV-inv k v τc eqj
...       | (t″ , vj , _) = t″ , sVis eqQ vj

-- OFFER reflection through the bind layer: a visible offer of `Q >>= k` comes
-- from `Q` (the continuation `k` only contributes once `Q` has returned, by which
-- point `force(Q>>=k)` follows `force(k r)`, never a `react` rooted in `Q`).
bind-offer-elim : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   {k : R → PTree E (ExtI E) S} {Q : PTree E (ExtI E) R} {e : Event}
   → isStable Q → Offers (Q >>= k) (evl e) → Offers Q (evl e)
bind-offer-elim {k = k} {Q = Q} {e = evLabel A ε a} stQ (t′ , step) with ev-inv step
... | (v′ , τc′ , eqf , eqj) with force Q in eqQ
...   | ret r     = ⊥-elim (lower stQ)
...   | sil c     = ⊥-elim (lower stQ)
...   | react v τc with react-inj-v eqf
...     | refl with bindV-inv k v τc eqj
...       | (t″ , vj , _) = t″ , sVis eqQ vj

-- ----------------------------------------------------------------------------
-- STABILITY / OFFER INTRO: forward through `>>=` and `iter-bind` (re-wrapping).
-- ----------------------------------------------------------------------------

-- A stable `Q` (react, τ-map everywhere nothing) stays stable under `>>= k`:
-- `bindT k (react v τc) i a` is `nothing` exactly when `τc i a` is.
bind-stable-intro : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   {k : R → PTree E (ExtI E) S} {Q : PTree E (ExtI E) R}
   → isStable Q → isStable (Q >>= k)
bind-stable-intro {k = k} {Q = Q} stQ with force Q in eqQ
... | ret r     = ⊥-elim (lower stQ)
... | sil c     = ⊥-elim (lower stQ)
... | react v τc = bindT-nil
      where
        τc-nil : ∀ i a → τc i a ≡ nothing
        τc-nil = stQ
        bindT-nil : ∀ i a → bindT k (react v τc) i a ≡ nothing
        bindT-nil i a with τc i a in vt
        ... | nothing = refl
        ... | just t″ = ⊥-elim (just≢nothing (trans (sym vt) (τc-nil i a)))
          where just≢nothing : ∀ {ℓx} {X : Set ℓx} {x : X} → just x ≡ nothing → ⊥
                just≢nothing ()

-- Likewise a stable `Q` stays stable under `iter-bind … k`.
iter-stable-intro : ∀ {ℓr} {R : Set ℓr} {k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   {Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → isStable Q → isStable (iter-bind Q k)
iter-stable-intro {k = k} {Q = Q} stQ with force Q in eqQ
... | ret (inj₁ a′) = ⊥-elim (lower stQ)
... | ret (inj₂ r)  = ⊥-elim (lower stQ)
... | sil c         = ⊥-elim (lower stQ)
... | react v τc = iterT-nil
      where
        τc-nil : ∀ i a → τc i a ≡ nothing
        τc-nil = stQ
        iterT-nil : ∀ i a → iterT k (react v τc) i a ≡ nothing
        iterT-nil i a with τc i a in vt
        ... | nothing = refl
        ... | just t″ = ⊥-elim (just≢nothing (trans (sym vt) (τc-nil i a)))
          where just≢nothing : ∀ {ℓx} {X : Set ℓx} {x : X} → just x ≡ nothing → ⊥
                just≢nothing ()

-- A visible offer of `Q >>= k` from one of `Q` (forward; mirrors iter-offer-intro).
bind-offer-intro : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   (k : R → PTree E (ExtI E) S) {Q t′ : PTree E (ExtI E) R}
   {A : Set ℓ} {e : E A} {a : A}
   → Q ─[ ev (evl (evLabel A e a)) ]─► t′
   → (Q >>= k) ─[ ev (evl (evLabel A e a)) ]─► (t′ >>= k)
bind-offer-intro k {Q = Q} step with ev-inv step
... | (v , τc , eqf , ej) =
      sVis (bind-force-react Q k eqf)
           (bind-cont-vis-just k (react v τc) ej)

-- ----------------------------------------------------------------------------
-- A diverging `Q` makes `iter-bind Q k` diverge (mirror `Diverges->>=`).
-- ----------------------------------------------------------------------------

lift-iter-step-τ : ∀ {ℓr} {R : Set ℓr} (k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R))
   {Q n : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → Q ─[ τ ]─► n → iter-bind Q k ─[ τ ]─► iter-bind n k
lift-iter-step-τ k {Q = Q} step with τ-inv step
... | inj₁ eqf                       = sSil (iter-bind-force-sil Q k eqf)
... | inj₂ (v , τc , i , a , eqf , eqj) =
        sTau (iter-bind-force-react Q k eqf)
             (iter-bind-cont-tau-just k (react v τc) eqj)

Diverges-iter-bind : ∀ {ℓr} {R : Set ℓr} {Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   (k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R))
   → Diverges Q → Diverges (iter-bind Q k)
Diverges-iter-bind {Q = Q} k dQ .next = iter-bind (dQ .next) k
Diverges-iter-bind {Q = Q} k dQ .step = lift-iter-step-τ k (dQ .step)
Diverges-iter-bind {Q = Q} k dQ .rest = Diverges-iter-bind k (dQ .rest)

-- ----------------------------------------------------------------------------
-- REFUSAL transport across the `iter-bind`/`>>=` layers, retagging the ban set.
-- The ban set only ever mentions VISIBLE events (a stable node offers nothing
-- but visible events), so it crosses the carrier changes via `banEvl`.
-- ----------------------------------------------------------------------------

-- ELIM through `iter-bind`: a refusal of `iter-bind Q k` is one of `Q`.
refuses-iter-elim : ∀ {ℓr} {R : Set ℓr} {k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   {Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)} {B : Event√ R → Set ℓ}
   → Refuses (iter-bind Q k) B
   → Refuses Q (banEvl {X = ⊤ {ℓ} ⊎ R} (λ e → B (evl e)))
refuses-iter-elim {R = R} {k = k} {Q = Q} {B = B} (st , no-off) =
  iter-stable-elim {Q = Q} st
  , no-off′
  where no-off′ : ∀ e → banEvl {X = ⊤ {ℓ} ⊎ R} (λ e → B (evl e)) e → ¬ Offers Q e
        no-off′ (evl εv) Be off =
          no-off (evl εv) Be (_ , iter-offer-intro k (proj₂ off))
        no-off′ (√ x) Be (t′ , sRet eqf) =
          ⊥-elim (ret-not-stable {t = Q} eqf (iter-stable-elim {Q = Q} st))

-- ELIM through `>>=`: a refusal of `Q >>= k` is one of `Q` (Q stable).
refuses-bind-elim : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   {k : R → PTree E (ExtI E) S} {Q : PTree E (ExtI E) R} {B : Event√ S → Set ℓ}
   → isStable Q → Refuses (Q >>= k) B
   → Refuses Q (banEvl {X = R} (λ e → B (evl e)))
refuses-bind-elim {R = R} {k = k} {Q = Q} {B = B} stQ (st , no-off) =
  stQ
  , no-off′
  where no-off′ : ∀ e → banEvl {X = R} (λ e → B (evl e)) e → ¬ Offers Q e
        no-off′ (evl εv) Be off =
          no-off (evl εv) Be (_ , bind-offer-intro k (proj₂ off))
        no-off′ (√ x) Be (t′ , sRet eqf) =
          ⊥-elim (ret-not-stable {t = Q} eqf stQ)

-- INTRO through `>>=`: a refusal of `Q` lifts to one of `Q >>= k` (same retag back).
refuses-bind-intro : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
   {k : R → PTree E (ExtI E) S} {Q : PTree E (ExtI E) R} {B : Event√ S → Set ℓ}
   → Refuses Q (banEvl {X = R} (λ e → B (evl e)))
   → Refuses (Q >>= k) B
refuses-bind-intro {k = k} {Q = Q} {B = B} (stQ , no-off) =
  bind-stable-intro {k = k} {Q = Q} stQ
  , no-off′
  where no-off′ : ∀ e → B e → ¬ Offers (Q >>= k) e
        no-off′ (evl εv) Be off =
          no-off (evl εv) Be (bind-offer-elim {k = k} {Q = Q} stQ off)
        -- a `√`-offer needs `force(Q>>=k) ≡ ret`, but a stable `Q>>=k` is react.
        no-off′ (√ x) Be (t′ , sRet eqf) =
          ⊥-elim (ret-not-stable {t = Q >>= k} eqf (bind-stable-intro {k = k} {Q = Q} stQ))

-- INTRO through `iter-bind`: a refusal of `Q` lifts to one of `iter-bind Q k`.
refuses-iter-intro : ∀ {ℓr} {R : Set ℓr} {k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   {Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)} {B : Event√ R → Set ℓ}
   → Refuses Q (banEvl {X = ⊤ {ℓ} ⊎ R} (λ e → B (evl e)))
   → Refuses (iter-bind Q k) B
refuses-iter-intro {k = k} {Q = Q} {B = B} (stQ , no-off) =
  iter-stable-intro {k = k} {Q = Q} stQ
  , no-off′
  where no-off′ : ∀ e → B e → ¬ Offers (iter-bind Q k) e
        no-off′ (evl (evLabel A ε a)) Be off =
          no-off (evl (evLabel A ε a)) Be
                 (iter-offer-elim {k = k} {Q = Q} off)
        no-off′ (√ x) Be (t′ , sRet eqf) =
          ⊥-elim (ret-not-stable {t = iter-bind Q k} eqf
                                 (iter-stable-intro {k = k} {Q = Q} stQ))

-- A divergence of `Q` on a visible trace lifts to `iter-bind Q k` (mirror
-- `bind-div-intro-P`: split the prefix into `map evl`, lift the reach and the
-- `Diverges` witness through `iter-bind`).
iter-div-intro-P : ∀ {ℓr} {R : Set ℓr}
   (Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)) (k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R))
   {vs : List Event}
   → divergences Q (map evl vs) → divergences (iter-bind Q k) (map evl vs)
iter-div-intro-P Q k {vs} d
   with evl-split (d .prefix) vs (d .suffix) (d .split)
... | vs₁ , vs₂ , refl , refl , evs = record
  { prefix  = map evl vs₁
  ; suffix  = map evl vs₂
  ; split   = trans (cong (map evl) evs) (map-++ evl vs₁ vs₂)
  ; witness = iter-bind (d .witness) k
  ; reach   = lift-iter-bigstep Q (d .witness) k vs₁ (d .reach)
  ; divwit  = Diverges-iter-bind k (d .divwit)
  }

-- ============================================================================
-- in-body-map : the per-iteration failure-map (Task 1, Step 2).
-- A reached refusing state of `loopStep body′`-iteration is mapped, via
-- `body ⊑F⊥ body′`, to a failure⊥ of `loop0 body` at the SAME visible trace.
-- Works at the canonical level `ℓr ≡ ℓ` (the loop's carrier `R` is phantom).
-- ============================================================================

-- shared re-wrapping: a `failures⊥ body` (failure OR divergence) on a visible
-- trace is re-assembled into a `failures⊥ (loop0 body)` on the same trace.
loop0-wrap : ∀ {R : Set ℓ} (body : PTree E (ExtI E) (⊤ {ℓ}))
   {vs : List Event} {B : Event√ R → Set ℓ}
   → failures⊥ body (map evl vs) (banEvl {X = ⊤ {ℓ}} (λ e → B (evl e)))
   → failures⊥ (loop0 {R = R} body) (map evl vs) B
loop0-wrap {R = R} body {vs} {B} (inj₁ (P₀ , body-run , ref₀)) =
  loop0-failures⊥-intro-failures body
    (loop-fail
      (LoopSplit.in-body
        (lift-bind-bigstep body P₀ loop-k vs body-run)
        refl)
      (refuses-iter-intro {k = loopStep body} {Q = P₀ >>= loop-k} {B = B}
        (refuses-bind-intro {k = loop-k} {Q = P₀}
          {B = banEvl {X = ⊤ {ℓ} ⊎ R} (λ e → B (evl e))} ref₀)))
loop0-wrap {R = R} body {vs} {B} (inj₂ d) =
  inj₂ (iter-div-intro-P (loopStep body tt) (loopStep body)
                         (bind-div-intro-P body loop-k {vs} d))

in-body-map : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → body ⊑F⊥ body′
   → ∀ {P′ vs} {B : Event√ R → Set ℓ}
   → (loopStep body′ tt) ⟹⟨ map evl vs ⟩ P′
   → Refuses (iter-bind P′ (loopStep body′)) B
   → failures⊥ (loop0 body) (map evl vs) B
in-body-map {R = R} body body′ f {P′} {vs} {B} run ref =
  in-body-map′ (map evl vs) refl (refuses-iter-elim {Q = P′} ref)
               (bind-bigstep-inv body′ loop-k run)
  where
    -- Worker at a GENERIC trace `s` (with `s ≡ map evl vs` carried separately):
    -- this keeps the in-P/in-k index a free variable so it unifies cleanly.
    in-body-map′ : (s : List (Event√ (⊤ {ℓ} ⊎ R)))
                 → s ≡ map evl vs
                 → Refuses P′ (banEvl {X = ⊤ {ℓ} ⊎ R} (λ e → B (evl e)))
                 → BindSplit body′ loop-k P′ s
                 → failures⊥ (loop0 body) (map evl vs) B
    in-body-map′ .(map evl vs₀) seq ref₁ (BindSplit.in-P {P′ = P″} {vs = vs₀} run′ refl)
        with map-evl-inj {R = ⊤ {ℓ} ⊎ R} seq
    ... | refl =
        loop0-wrap body
          (f {map evl vs₀} {banEvl {X = ⊤ {ℓ}} (λ e → B (evl e))}
             (inj₁ (P″ , run′
                  , refuses-bind-elim {k = loop-k} {Q = P″}
                      {B = banEvl {X = ⊤ {ℓ} ⊎ R} (λ e → B (evl e))}
                      (bind-stable-elim {Q = P″} (proj₁ ref₁))
                      ref₁)))
    in-body-map′ .(map evl s₁ ++ s₂) seq ref₁
                 (BindSplit.in-k {r = r} {s₁ = s₁} {s₂ = s₂} reachP eqr kr)
        with evl-split (map evl s₁) vs s₂ (sym seq)
    ...   | vs₁ , vs₂ , _ , refl , _ =
            ⊥-elim (ret-not-stable {t = P′}
                      (ret-stuck {Q = loop-k r} {x = inj₁ r} vs₂ refl kr)
                      (proj₁ ref₁))

-- ============================================================================
-- Task 2: loop0-mono-⊑F⊥  — THE SPIKE / DECISION GATE
--
-- Strategy (failures branch).  Decompose a failure⊥ of `loop0 body′` via
-- `loop0-failures⊥-elim`.  The `in-body` arm is the per-iteration Task-1 helper
-- `in-body-map`.  The `in-loop` arm is ONE complete body′-iteration on `s₁`
-- (reaching a `ret (inj₁ tt)` loop-back) followed by a `loop0 body′` run on `s₂`;
-- we RECURSE on the `s₂` failure and PREPEND a reconstructed body-side iteration.
--
-- TERMINATION.  The recursive `s₂` run is shorter than the input run (the
-- loop-back consumes ≥1 τ-step), so we recurse by well-founded recursion on a
-- run-step count `runLen`.  A measured loop-trace (`loop-trace<`) carries the
-- `runLen kr < runLen run` evidence out of the `iter-bind-inv` traversal.
--
-- THE CRUX (reconstruction).  The body-side iteration is recovered POSTULATE-FREE:
-- `bs`/`fe` witness that `body′` TERMINATES (reaches `ret tt`) on the visible
-- trace `s₁`; a terminating run gives a √-failure `failures body′ (s₁ ++ √)`,
-- which `body ⊑F⊥ body′` (`f`) transfers to `body`; inverting the √-trace yields
-- an actual `body`-run to a `ret tt` state on `s₁`, which we re-wrap into a
-- body-side loop-back iteration.  No after-state choice / classical step is
-- needed because the witness for the √-trace is constructive (deadlock refuses
-- everything) and √-trace inversion is structural.
-- ============================================================================

-- run-step count: number of ⟹-τ / ⟹-ev nodes in a big-step run.
runLen : ∀ {ℓr} {R : Set ℓr} {p q : PTree E (ExtI E) R} {s}
       → p ⟹⟨ s ⟩ q → ℕ
runLen ⟹-refl         = zero
runLen (⟹-τ  _ rest)  = suc (runLen rest)
runLen (⟹-ev _ rest)  = suc (runLen rest)

-- ── measured IterSplit ──────────────────────────────────────────────────────
-- Like `IterSplit`, but bounded by a step count `n`; the `in-loop` arm carries
-- `runLen kr < n` so the loop-back recursion is well-founded.
data IterSplitN {ℓr} {A : Set ℓ} {R : Set ℓr}
   (P : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
   (T : PTree E (ExtI E) R) : List (Event√ R) → ℕ → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  in-bodyN : ∀ {P′} {vs : List Event} {n}
           → P ⟹⟨ map evl vs ⟩ P′ → T ≡ iter-bind P′ k
           → IterSplitN P k T (map evl vs) n
  in-doneN : ∀ {r : R} {s₁ : List Event} {Pᵣ} {n}
           → P ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₂ r) → T ≡ deadlock
           → IterSplitN P k T (map evl s₁ ++ (√ r ∷ [])) n
  in-loopN : ∀ {a′ : A} {s₁ : List Event} {s₂ : List (Event√ R)} {Pᵣ} {n}
           → P ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ a′)
           → (kr : iter k a′ ⟹⟨ s₂ ⟩ T) → runLen kr < n
           → IterSplitN P k T (map evl s₁ ++ s₂) n

-- prepend a τ-step: trace unchanged, but the step-count grows by one, so we relax
-- the in-loop bound `runLen kr < n` to `runLen kr < suc n` (≤-step).
prepend-τ-IterN : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   {P c : PTree E (ExtI E) (A ⊎ R)} {k : A → PTree E (ExtI E) (A ⊎ R)}
   {T : PTree E (ExtI E) R} {s : List (Event√ R)} {n}
   → (P ─[ τ ]─► c)
   → IterSplitN c k T s n → IterSplitN P k T s (suc n)
prepend-τ-IterN pstep (in-bodyN cstep eq)        = in-bodyN (⟹-τ pstep cstep) eq
prepend-τ-IterN pstep (in-doneN cstep fe te)      = in-doneN (⟹-τ pstep cstep) fe te
prepend-τ-IterN pstep (in-loopN cstep fe kr lt)   =
  in-loopN (⟹-τ pstep cstep) fe kr (m≤n⇒m≤1+n lt)

prepend-ev-IterN : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   {P t : PTree E (ExtI E) (A ⊎ R)} {k : A → PTree E (ExtI E) (A ⊎ R)}
   {T : PTree E (ExtI E) R} {s : List (Event√ R)} {n}
   {B : Set ℓ} {e : E B} {a : B}
   → (P ─[ ev (evl (evLabel B e a)) ]─► t)
   → IterSplitN t k T s n → IterSplitN P k T (evl (evLabel B e a) ∷ s) (suc n)
prepend-ev-IterN {B = B} {e} {a} pstep (in-bodyN {vs = vs} cstep eq) =
  in-bodyN {vs = evLabel B e a ∷ vs} (⟹-ev pstep cstep) eq
prepend-ev-IterN {B = B} {e} {a} pstep (in-doneN {s₁ = s₁} cstep fe te) =
  in-doneN {s₁ = evLabel B e a ∷ s₁} (⟹-ev pstep cstep) fe te
prepend-ev-IterN {B = B} {e} {a} pstep (in-loopN {s₁ = s₁} cstep fe kr lt) =
  in-loopN {s₁ = evLabel B e a ∷ s₁} (⟹-ev pstep cstep) fe kr (m≤n⇒m≤1+n lt)

-- measured iter-bind inversion: mirrors `iter-bind-inv`, but the result is
-- bounded by `runLen run`, and the loop-back arm carries `runLen kr < runLen run`.
iter-bind-invN : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
   (P : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
   {T : PTree E (ExtI E) R} {s : List (Event√ R)}
   → (run : (iter-bind P k) ⟹⟨ s ⟩ T) → IterSplitN P k T s (runLen run)
iter-bind-invN P k ⟹-refl = in-bodyN {vs = []} ⟹-refl refl
-- ── τ via sSil ──────────────────────────────────────────────────────────────
iter-bind-invN P k (⟹-τ (sSil eqf) rest) with PTree.force P in eqP | eqf
... | ret (inj₁ a′) | eqf′
      rewrite sym (sil-inj eqf′) =
        in-loopN {s₁ = []} ⟹-refl eqP rest ≤-refl
... | ret (inj₂ r)  | ()
... | sil c         | eqf′
      rewrite sym (sil-inj eqf′) =
        prepend-τ-IterN (sSil eqP) (iter-bind-invN c k rest)
... | react v τc    | ()
-- ── τ via sTau ──────────────────────────────────────────────────────────────
iter-bind-invN P k (⟹-τ (sTau eqf eqj) rest) with PTree.force P in eqP | eqf
... | ret (inj₁ a′) | ()
... | ret (inj₂ r)  | ()
... | sil c         | ()
... | react v τc    | eqf′
      rewrite sym (react-inj-τ eqf′) with iterT-inv k v τc eqj
...   | (t′ , vtq , refl) =
        prepend-τ-IterN (sTau eqP vtq) (iter-bind-invN t′ k rest)
-- ── visible step via sVis ────────────────────────────────────────────────────
iter-bind-invN P k (⟹-ev (sVis eqf eqj) rest) with PTree.force P in eqP | eqf
... | ret (inj₁ a′) | ()
... | ret (inj₂ r)  | ()
... | sil c         | ()
... | react v τc    | eqf′
      rewrite sym (react-inj-v eqf′) with iterV-inv k v τc eqj
...   | (t′ , vvq , refl) =
        prepend-ev-IterN (sVis eqP vvq) (iter-bind-invN t′ k rest)
-- ── √ tick via sRet ──────────────────────────────────────────────────────────
iter-bind-invN P k (⟹-ev (sRet eqf) rest) with PTree.force P in eqP | eqf
... | ret (inj₁ a′) | ()
... | ret (inj₂ r)  | refl with deadlock-run-inv rest
...   | refl , refl =
        in-doneN {s₁ = []} ⟹-refl eqP refl
iter-bind-invN P k (⟹-ev (sRet eqf) rest) | sil c      | ()
iter-bind-invN P k (⟹-ev (sRet eqf) rest) | react v τc | ()

-- ── measured loop-trace ──────────────────────────────────────────────────────
-- Specialise `iter-bind-invN` to `loop0 body` and translate to a LoopSplit-style
-- result bounded by `runLen run`; the `in-done` arm is impossible (loopStep
-- never returns inj₂).  The in-loop arm exposes `runLen kr < runLen run`.
data LoopSplit< {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ}))
   (T : PTree E (ExtI E) R) : List (Event√ R) → ℕ → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  in-body< : ∀ {P′} {vs : List Event} {n}
           → (loopStep {R = R} body tt) ⟹⟨ map evl vs ⟩ P′
           → T ≡ iter-bind P′ (loopStep body) → LoopSplit< body T (map evl vs) n
  in-loop< : ∀ {s₁ : List Event} {s₂ : List (Event√ R)} {Pᵣ} {n}
           → (loopStep {R = R} body tt) ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ tt)
           → (kr : loop0 {R = R} body ⟹⟨ s₂ ⟩ T) → runLen kr < n
           → LoopSplit< body T (map evl s₁ ++ s₂) n

loop-trace< : ∀ {ℓr} {R : Set ℓr} (body : PTree E (ExtI E) (⊤ {ℓ})) {T s}
            → (run : (loop0 body) ⟹⟨ s ⟩ T) → LoopSplit< body T s (runLen run)
loop-trace< {R = R} body run
  with iter-bind-invN (loopStep {R = R} body tt) (loopStep body) run
... | in-bodyN bs eq               = in-body< bs eq
... | in-loopN {a′ = tt} bs fe kr lt = in-loop< bs fe kr lt
... | in-doneN bs fe _             = ⊥-elim (loopStep-no-inj₂ body bs fe)

-- ── reconstruction: body′ TERMINATES on s₁ ───────────────────────────────────
-- `force (Q >>= loop-k) ≡ ret (inj₁ tt)` forces `force Q ≡ ret tt` (then the bind
-- hands off to `force (loop-k tt) = ret (inj₁ tt)`).
bind-loopk-ret-elim : ∀ {R : Set ℓ}
   (Q : PTree E (ExtI E) (⊤ {ℓ}))
   → force (Q >>= loop-k {R = R}) ≡ ret (inj₁ tt) → force Q ≡ ret tt
bind-loopk-ret-elim Q eq with force Q in eqQ
... | ret tt     = refl
... | sil c      with eq
...   | ()
bind-loopk-ret-elim Q eq | react v τc with eq
...   | ()

-- a purely-visible run out of a `ret`-state consumes NO events (it must be
-- `⟹-refl`): a `ret` offers only its `√`, never an `evl`.  (General payload `x`.)
ret-run-nil : ∀ {ℓr} {R : Set ℓr} {Q P′ : PTree E (ExtI E) R} {x : R} (vs : List Event)
   → force Q ≡ ret x → Q ⟹⟨ map evl vs ⟩ P′ → vs ≡ []
ret-run-nil []        eq ⟹-refl = refl
ret-run-nil []        eq (⟹-τ step rest) with τ-inv step
... | inj₁ eqf                       with () ← trans (sym eq) eqf
ret-run-nil []        eq (⟹-τ step rest) | inj₂ (v , τc , i , a , eqf , eqj)
      with () ← trans (sym eq) eqf
ret-run-nil (x ∷ vs) eq (⟹-τ step rest) with τ-inv step
... | inj₁ eqf                       with () ← trans (sym eq) eqf
ret-run-nil (x ∷ vs) eq (⟹-τ step rest) | inj₂ (v , τc , i , a , eqf , eqj)
      with () ← trans (sym eq) eqf
ret-run-nil (x ∷ vs) eq (⟹-ev (sVis eqf _) rest) with () ← trans (sym eq) eqf

-- From a complete body-iteration witness (`loopStep body tt` visibly reaches a
-- `ret (inj₁ tt)` loop-back state on `s₁`), recover that `body` itself reaches
-- a `ret tt` (terminating) state on the SAME visible trace `s₁`.
body-terminates : ∀ (body : PTree E (ExtI E) (⊤ {ℓ})) {R : Set ℓ}
   {s₁ : List Event} {Pᵣ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → (loopStep body tt) ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ tt)
   → Σ[ Bᵣ ∈ PTree E (ExtI E) (⊤ {ℓ}) ] (body ⟹⟨ map evl s₁ ⟩ Bᵣ × force Bᵣ ≡ ret tt)
body-terminates body {R = R} {s₁ = s₁} {Pᵣ} run fe =
  go (map evl s₁) refl (bind-bigstep-inv body loop-k run)
  where
    -- Worker at a GENERIC trace `s` (with `s ≡ map evl s₁` carried separately),
    -- so the in-P/in-k trace index is a free variable that unifies cleanly.
    go : (s : List (Event√ (⊤ {ℓ} ⊎ R))) → s ≡ map evl s₁
       → BindSplit body loop-k Pᵣ s
       → Σ[ Bᵣ ∈ PTree E (ExtI E) (⊤ {ℓ}) ] (body ⟹⟨ map evl s₁ ⟩ Bᵣ × force Bᵣ ≡ ret tt)
    -- in-P: body reaches `P″`, and `force(P″ >>= loop-k) ≡ ret (inj₁ tt)` forces
    -- `force P″ ≡ ret tt`.
    go .(map evl vs) seq (BindSplit.in-P {P′ = P″} {vs = vs} runB refl)
        with map-evl-inj {R = ⊤ {ℓ} ⊎ R} seq
    ... | refl = P″ , runB , bind-loopk-ret-elim P″ fe
    -- in-k: body reaches `ret tt` on `s₁′`, then `loop-k tt` (force `ret (inj₁ tt)`)
    -- runs on `s₂′` — a purely-visible run out of a ret-state, so `s₂′ ≡ []`.
    go .(map evl s₁′ ++ s₂′) seq
       (BindSplit.in-k {r = tt} {s₁ = s₁′} {s₂ = s₂′} {Pᵣ = Bᵣ} runB eqr kr)
        with evl-split (map evl s₁′) s₁ s₂′ (sym seq)
    ...   | vs₁ , vs₂ , e1 , refl , es1
            with map-evl-inj {R = ⊤ {ℓ} ⊎ R} (sym e1)
    ...     | refl with ret-run-nil {x = inj₁ tt} vs₂ refl kr
    ...       | refl rewrite ++-identityʳ vs₁ | es1 = Bᵣ , runB , eqr

-- ── the √-trace witnesses and their inversion ────────────────────────────────
-- A terminating run (`P` reaches a `ret x` state on `s₁`) gives a √-extended
-- FAILURE for ANY ban set `B`: append the `√ x` tick to `deadlock`, which refuses
-- everything.  Used to feed `body ⊑F⊥ body′` a witness of body′'s termination.
term→√failure : ∀ {ℓr} {R : Set ℓr} {P Pᵣ : PTree E (ExtI E) R} {x : R}
   {s₁ : List (Event√ R)} {B : Event√ R → Set ℓr}
   → P ⟹⟨ s₁ ⟩ Pᵣ → force Pᵣ ≡ ret x → failures P (s₁ ++ √ x ∷ []) B
term→√failure {x = x} ⟹-refl          fe =
  deadlock , ⟹-ev (sRet fe) ⟹-refl , deadlock-refuses
term→√failure {x = x} (⟹-τ step rest)  fe with term→√failure rest fe
... | (T , run , ref) = T , ⟹-τ step run , ref
term→√failure {x = x} (⟹-ev step rest) fe with term→√failure rest fe
... | (T , run , ref) = T , ⟹-ev step run , ref

-- INVERSION of a √-extended visible run: `P ⟹⟨ map evl s₁ ++ √ x ∷ [] ⟩ T` means
-- `P` visibly reaches a `ret x` state on `s₁` (the √ ticks to deadlock at the end).
-- Recursion peels the run; the √ can only fire from a `ret x`-forced state.
√-run-split : ∀ {ℓr} {R : Set ℓr} {P T : PTree E (ExtI E) R} {x : R}
   (s₁ : List Event)
   → P ⟹⟨ map evl s₁ ++ √ x ∷ [] ⟩ T
   → Σ[ Pᵣ ∈ PTree E (ExtI E) R ] (P ⟹⟨ map evl s₁ ⟩ Pᵣ × force Pᵣ ≡ ret x)
-- empty s₁: trace is `√ x ∷ []`; a τ-step keeps it, the `√` tick fires from `ret x`.
√-run-split {P = P} {x = x} []        (⟹-τ step rest) with √-run-split [] rest
... | (Pᵣ , run , fe) = Pᵣ , ⟹-τ step run , fe
√-run-split {P = P} {x = x} []        (⟹-ev (sRet fe) rest) = P , ⟹-refl , fe
-- non-empty s₁: trace is `evl v ∷ …`; a τ-step keeps it, an `evl` step peels it.
√-run-split {P = P} {x = x} (v ∷ vs) (⟹-τ step rest) with √-run-split (v ∷ vs) rest
... | (Pᵣ , run , fe) = Pᵣ , ⟹-τ step run , fe
√-run-split {P = P} {x = x} (v ∷ vs) (⟹-ev {q = q} step rest) with √-run-split vs rest
... | (Pᵣ , run , fe) = Pᵣ , ⟹-ev step run , fe

-- ── divergence half of the reconstruction ────────────────────────────────────
-- A `Diverges`-reaching run cannot pass a `√` tick: the √ steps to `deadlock`,
-- which is stable (no τ) and cannot diverge (`deadlock-converges`, imported —
-- this used to be a local duplicate called `deadlock-not-diverges`).  Hence a
-- divergence witness reached along a trace `s₁ ++ √ x ∷ rest` is impossible.
no-div-through-√ : ∀ {ℓr} {R : Set ℓr} {P W : PTree E (ExtI E) R} {x : R}
   (s′ rest : List (Event√ R))
   → P ⟹⟨ s′ ++ √ x ∷ rest ⟩ W → Diverges W → ⊥
-- empty s′: trace is `√ x ∷ rest`; a τ keeps it, the `√` ticks to deadlock.
no-div-through-√ []        rest (⟹-τ step run) dv = no-div-through-√ [] rest run dv
no-div-through-√ []        rest (⟹-ev (sRet _) run) dv with deadlock-run-inv run
... | refl , refl = deadlock-converges dv
-- non-empty s′: trace is `head ∷ …`; a τ keeps it, a visible step peels it.
no-div-through-√ (e ∷ es) rest (⟹-τ step run) dv = no-div-through-√ (e ∷ es) rest run dv
no-div-through-√ (e ∷ es) rest (⟹-ev step run) dv = no-div-through-√ es rest run dv

-- transport a run across an equal trace.
subst-run : ∀ {ℓr} {R : Set ℓr} {Q : PTree E (ExtI E) R} {p p′ W} → p ≡ p′
          → Q ⟹⟨ p ⟩ W → Q ⟹⟨ p′ ⟩ W
subst-run refl r = r

-- Split a divergence on `map evl s₁ ++ √ x ∷ []`: its prefix is purely visible
-- (the √ lives in the suffix, by `no-div-through-√`), so the divergent witness is
-- reached on `map evl vs′` with `vs′` a prefix of `s₁`.
div-√-prefix-visible : ∀ (body : PTree E (ExtI E) (⊤ {ℓ})) {x : ⊤ {ℓ}}
   {s₁ : List Event}
   → divergences body (map evl s₁ ++ √ x ∷ [])
   → Σ[ vs′ ∈ List Event ] Σ[ mid ∈ List Event ]
       (s₁ ≡ vs′ ++ mid × divergences body (map evl vs′))
div-√-prefix-visible body {x} {s₁} d
  with prefix-shape (d .prefix) (d .suffix) s₁ (sym (d .split))
  where
    ∷-inj-local : ∀ {ℓa} {A : Set ℓa} {h₁ h₂ : A} {t₁ t₂ : List A}
                → (h₁ ∷ t₁) ≡ (h₂ ∷ t₂) → h₁ ≡ h₂ × t₁ ≡ t₂
    ∷-inj-local refl = refl , refl

    -- PURE list split of `p ++ sfx ≡ map evl s ++ √ x ∷ []`: the only √ in the RHS
    -- is the trailing one, so either `p` is a visible prefix of `map evl s`, or `p`
    -- exhausts the whole RHS (and therefore contains the trailing √).
    prefix-shape : (p sfx : List (Event√ (⊤ {ℓ}))) (s : List Event)
                 → p ++ sfx ≡ map evl s ++ √ x ∷ []
                 → (Σ[ vs′ ∈ List Event ] Σ[ mid ∈ List Event ]
                       (s ≡ vs′ ++ mid × p ≡ map evl vs′))
                 ⊎ (Σ[ pre ∈ List Event ] Σ[ rest ∈ List (Event√ (⊤ {ℓ})) ]
                       (p ≡ map evl pre ++ √ x ∷ rest))
    prefix-shape []        sfx s        eq = inj₁ ([] , s , refl , refl)
    prefix-shape (q ∷ qs) sfx []       eq with ∷-inj-local eq
    ... | refl , _  = inj₂ ([] , qs , refl)
    prefix-shape (q ∷ qs) sfx (v ∷ vs) eq with ∷-inj-local eq
    ... | refl , tl with prefix-shape qs sfx vs tl
    ...   | inj₁ (vs′ , mid , es , eqp) =
            inj₁ (v ∷ vs′ , mid , cong (v ∷_) es , cong (evl v ∷_) eqp)
    ...   | inj₂ (pre , rest , eqp) = inj₂ (v ∷ pre , rest , cong (evl v ∷_) eqp)
... | inj₁ (vs′ , mid , es , eqp) =
      vs′ , mid , es ,
      record
        { prefix  = map evl vs′
        ; suffix  = []
        ; split   = sym (++-identityʳ (map evl vs′))
        ; witness = d .witness
        ; reach   = subst-run eqp (d .reach)
        ; divwit  = d .divwit
        }
-- the √-containing case is impossible: the divergence run would pass the √.
... | inj₂ (pre , rest , eqp) =
      ⊥-elim (no-div-through-√ {x = x} (map evl pre) rest (subst-run eqp (d .reach)) (d .divwit))

-- a body divergence on a visible trace pushes through `>>= loop-k` and the iter
-- layer to a `loop0 body` divergence on the same visible trace.
body-div→loop0-div : ∀ {R : Set ℓ} (body : PTree E (ExtI E) (⊤ {ℓ}))
   {vs : List Event}
   → divergences body (map evl vs) → divergences (loop0 {R = R} body) (map evl vs)
body-div→loop0-div {R = R} body {vs} d =
  iter-div-intro-P (loopStep body tt) (loopStep body)
                   (bind-div-intro-P body loop-k {vs} d)

-- PREPEND one complete body-iteration (trace `s₁`, looping back) before a
-- `failures⊥ (loop0 body)` on `s₂`, yielding a `failures⊥ (loop0 body)` on
-- `map evl s₁ ++ s₂`.  Failures re-wrap as a `LoopSplit.in-loop`; divergences
-- prepend the lifted iteration run + the loop-back τ to the divergence's reach.
loop0-prepend-iter : ∀ {R : Set ℓ} (body : PTree E (ExtI E) (⊤ {ℓ}))
   {s₁ : List Event} {s₂ : List (Event√ R)} {Pᵣ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   {B : Event√ R → Set ℓ}
   → (loopStep body tt) ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ tt)
   → failures⊥ (loop0 body) s₂ B
   → failures⊥ (loop0 {R = R} body) (map evl s₁ ++ s₂) B
-- FAILURE half: wrap the s₂ failure-run into a LoopSplit.in-loop, keep the refusal.
loop0-prepend-iter {R = R} body {s₁} {s₂} {Pᵣ} {B} bs fe (inj₁ (T , run , ref)) =
  loop0-failures⊥-intro-failures body
    (loop-fail (LoopSplit.in-loop {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} bs fe run) ref)
-- DIVERGENCE half: prepend the lifted iteration run and the loop-back τ to the
-- divergence's reach; the prefix grows by `map evl s₁` (the τ loop-back is silent).
loop0-prepend-iter {R = R} body {s₁} {s₂} {Pᵣ} {B} bs fe (inj₂ d) =
  inj₂ (record
    { prefix  = map evl s₁ ++ d .prefix
    ; suffix  = d .suffix
    ; split   = trans (cong (map evl s₁ ++_) (d .split))
                      (sym (++-assoc (map evl s₁) (d .prefix) (d .suffix)))
    ; witness = d .witness
    ; reach   = ⟹-trans
                  (lift-iter-bigstep (loopStep body tt) Pᵣ (loopStep body) s₁ bs)
                  (⟹-τ (sSil (loop-back-sil body Pᵣ fe)) (d .reach))
    ; divwit  = d .divwit
    })

-- ── divergence-branch reconstruction helpers ─────────────────────────────────

-- bind-into-loop-k τ-step inversion: a τ of `P″ >>= loop-k` is always a P″-phase
-- step (P″ ─τ→ P‴, residual `P‴ >>= loop-k`).  `loop-k r = Ret (inj₁ r)` is τ-less,
-- so the √-splice (force P″ ≡ ret) is impossible: it would force the node to a ret.
bind-loopk-τ-elim : ∀ {R : Set ℓ} (P″ : PTree E (ExtI E) (⊤ {ℓ}))
   {u : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → (P″ >>= loop-k {R = R}) ─[ τ ]─► u
   → Σ[ P‴ ∈ PTree E (ExtI E) (⊤ {ℓ}) ] (P″ ─[ τ ]─► P‴) × (u ≡ P‴ >>= loop-k)
bind-loopk-τ-elim {R = R} P″ step with PTree.force P″ in eqP
-- ret: the node is `ret (inj₁ r)` (τ-less), so the τ-step is impossible.
... | ret r      = ⊥-elim (ret-no-τ step)
  where ret-no-τ : ∀ {u} → (P″ >>= loop-k {R = R}) ─[ τ ]─► u → ⊥
        ret-no-τ st with τ-inv st
        ... | inj₁ ef                         with () ← trans (sym (bind-force-ret P″ loop-k eqP)) ef
        ... | inj₂ (_ , _ , _ , _ , ef , _) with () ← trans (sym (bind-force-ret P″ loop-k eqP)) ef
-- sil: a P″-phase silent step.
... | sil c      = c , sSil eqP , sym (sil-inj (trans (sym (bind-force-sil P″ loop-k eqP)) (sSil-eqf step)))
  where sSil-eqf : ∀ {u} → (P″ >>= loop-k {R = R}) ─[ τ ]─► u → force (P″ >>= loop-k) ≡ sil u
        sSil-eqf st with τ-inv st
        ... | inj₁ ef                         = ef
        ... | inj₂ (_ , _ , _ , _ , ef , _) with () ← trans (sym (bind-force-sil P″ loop-k eqP)) ef
-- react: a P″-phase τ via a just τ-branch.
... | react v τc with τ-inv step
...   | inj₁ ef                         with () ← trans (sym (bind-force-react P″ loop-k eqP)) ef
bind-loopk-τ-elim {R = R} P″ step | react v τc | inj₂ (v′ , τc′ , i , a , ef , bj)
  with react-inj-τ (trans (sym (bind-force-react P″ loop-k eqP)) ef)
... | refl with bindT-inv loop-k v τc bj
...   | (t′ , τcj , teq) = t′ , sTau eqP τcj , sym teq

-- CONSTRUCTIVE bind-into-loop-k divergence peel: a divergence of `P″ >>= loop-k`
-- is a divergence of `P″`.  No König step: every τ is a P″-phase τ (the k-phase
-- `Ret (inj₁ _)` is τ-less, so the chain never splices), projecting directly to an
-- infinite τ-chain of `P″`.
-- transport `Diverges` across an equal `force` (mirror BindFD.Diverges-force-eq):
-- only the first τ-step inspects `force`, so retarget it.
Diverges-force-eq′ : ∀ {ℓr} {R : Set ℓr} {a b : PTree E (ExtI E) R}
                   → PTree.force a ≡ PTree.force b → Diverges b → Diverges a
Diverges-force-eq′ {a = a} {b} eq db .next = db .next
Diverges-force-eq′ {a = a} {b} eq db .step with db .step
... | sSil ef   = sSil (trans eq ef)
... | sTau ef br = sTau (trans eq ef) br
Diverges-force-eq′ {a = a} {b} eq db .rest = db .rest

bind-loopk-Diverges→ : ∀ {R : Set ℓ} (P″ : PTree E (ExtI E) (⊤ {ℓ}))
   → Diverges (P″ >>= loop-k {R = R}) → Diverges P″
-- corecursion guarded under `.rest`; the per-step inversion is inlined so the
-- recursive call sits syntactically under the `Diverges` constructor.
bind-loopk-Diverges→ {R = R} P″ d .next =
  proj₁ (bind-loopk-τ-elim P″ (d .step))
bind-loopk-Diverges→ {R = R} P″ d .step =
  proj₁ (proj₂ (bind-loopk-τ-elim P″ (d .step)))
bind-loopk-Diverges→ {R = R} P″ d .rest =
  bind-loopk-Diverges→ (proj₁ (bind-loopk-τ-elim P″ (d .step)))
    (subst Diverges (proj₂ (proj₂ (bind-loopk-τ-elim P″ (d .step)))) (d .rest))

-- compose a visible big-step run with a trailing silent τ*-run (trace unchanged).
⟹-then-τ* : ∀ {ℓr} {R : Set ℓr} {P Q Q′ : PTree E (ExtI E) R} {s}
           → P ⟹⟨ s ⟩ Q → Q ─[τ*]─► Q′ → P ⟹⟨ s ⟩ Q′
⟹-then-τ* ⟹-refl            τ*-refl           = ⟹-refl
⟹-then-τ* ⟹-refl            (τ*-step st rest) = ⟹-τ st (⟹-then-τ* ⟹-refl rest)
⟹-then-τ* (⟹-τ step run)    tt*               = ⟹-τ step (⟹-then-τ* run tt*)
⟹-then-τ* (⟹-ev step run)   tt*               = ⟹-ev step (⟹-then-τ* run tt*)

-- DIVERGENCE prepend: ONE complete body-iteration (trace `s₁`, looping back) before
-- a `divergences (loop0 body)` on `s₂` yields a `divergences (loop0 body)` on
-- `map evl s₁ ++ s₂` (the divergence half of `loop0-prepend-iter`, divergence-typed:
-- prepend the lifted iteration run + the loop-back τ to the divergence's reach).
loop0-prepend-div : ∀ {R : Set ℓ} (body : PTree E (ExtI E) (⊤ {ℓ}))
   {s₁ : List Event} {s₂ : List (Event√ R)} {Pᵣ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → (loopStep body tt) ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ tt)
   → divergences (loop0 body) s₂
   → divergences (loop0 {R = R} body) (map evl s₁ ++ s₂)
loop0-prepend-div {R = R} body {s₁} {s₂} {Pᵣ} bs fe d = record
  { prefix  = map evl s₁ ++ d .prefix
  ; suffix  = d .suffix
  ; split   = trans (cong (map evl s₁ ++_) (d .split))
                    (sym (++-assoc (map evl s₁) (d .prefix) (d .suffix)))
  ; witness = d .witness
  ; reach   = ⟹-trans
                (lift-iter-bigstep (loopStep body tt) Pᵣ (loopStep body) s₁ bs)
                (⟹-τ (sSil (loop-back-sil body Pᵣ fe)) (d .reach))
  ; divwit  = d .divwit
  }

-- transport a divergence across an equal trace.
subst-div0 : ∀ {R : Set ℓ} {body : PTree E (ExtI E) (⊤ {ℓ})} {t t′ : List (Event√ R)}
           → t ≡ t′ → divergences (loop0 body) t → divergences (loop0 body) t′
subst-div0 refl x = x

-- a silent (empty-visible-trace) run reaching a divergent state IS a divergence of
-- the source: a `⟹⟨ [] ⟩` run is τ-only (no `⟹-ev`), so prepend its τ's to `Diverges`.
⟹[]→Diverges : ∀ {ℓr} {R : Set ℓr} {P W : PTree E (ExtI E) R}
             → P ⟹⟨ [] ⟩ W → Diverges W → Diverges P
⟹[]→Diverges ⟹-refl          dW = dW
⟹[]→Diverges (⟹-τ step rest) dW =
  record { step = step ; rest = ⟹[]→Diverges rest dW }

-- collapse a `divergences (loop0 body) []` (empty trace) into a bare `Diverges`:
-- `[] ≡ prefix ++ suffix` forces `prefix ≡ []`, so the reach is a `⟹⟨ [] ⟩` run.
div[]→Diverges : ∀ {R : Set ℓ} {body : PTree E (ExtI E) (⊤ {ℓ})}
               → divergences (loop0 {R = R} body) [] → Diverges (loop0 body)
div[]→Diverges d = go (d .prefix) (d .split) (d .reach) (d .divwit)
  where go : ∀ {body : PTree E (ExtI E) (⊤ {ℓ})} {W} (pre : List (Event√ _))
           → [] ≡ pre ++ _ → loop0 body ⟹⟨ pre ⟩ W → Diverges W → Diverges (loop0 body)
        go []      _  reach dW = ⟹[]→Diverges reach dW
        go (_ ∷ _) () _     _

-- RECONSTRUCT the body-side loop-back from body′'s termination on s₁ via `f`:
-- either `body` ALSO terminates-and-loops-back on s₁ (left), or `body` itself
-- diverges on a prefix of s₁ — already pushed to a `loop0 body` divergence on s₁
-- (right).  Mirrors the in-loop reconstruction of `mono-fail`.
recover-loopback : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → body ⊑F⊥ body′
   → ∀ {s₁ : List Event} {Pᵣ′ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → (loopStep body′ tt) ⟹⟨ map evl s₁ ⟩ Pᵣ′ → force Pᵣ′ ≡ ret (inj₁ tt)
   → (Σ[ Pᵣ ∈ PTree E (ExtI E) (⊤ {ℓ} ⊎ R) ]
        ((loopStep body tt) ⟹⟨ map evl s₁ ⟩ Pᵣ × force Pᵣ ≡ ret (inj₁ tt)))
   ⊎ divergences (loop0 {R = R} body) (map evl s₁)
recover-loopback {R = R} body body′ f {s₁} bs fe
  with body-terminates body′ bs fe
... | (Bᵣ′ , bodyrun′ , feB′)
      with f {map evl s₁ ++ √ tt ∷ []} {λ _ → Lift ℓ ⊥}
             (inj₁ (term→√failure {x = tt} bodyrun′ feB′))
...   | inj₁ (T , brun , bref) with √-run-split s₁ brun
...     | (Bᵣ , bodyrun , feB) =
          inj₁ (Bᵣ >>= loop-k
               , lift-bind-bigstep body Bᵣ loop-k s₁ bodyrun
               , bind-force-ret Bᵣ loop-k feB)
recover-loopback {R = R} body body′ f {s₁} bs fe
    | (Bᵣ′ , bodyrun′ , feB′)
      | inj₂ dbody with div-√-prefix-visible body dbody
...     | (vs′ , mid , es , dvis) =
          inj₂ (subst-div0 {body = body} (sym (push es))
                  (div-extension-closed {t = map evl mid}
                    (body-div→loop0-div body dvis)))
  where push : s₁ ≡ vs′ ++ mid → map evl s₁ ≡ map evl vs′ ++ map evl mid
        push refl = map-++ evl vs′ mid

-- ── THE SILENT-SPIN TRANSFER (coinductive) ───────────────────────────────────
-- A SILENT divergence of `loop0 body′` (a bare `Diverges` is τ-only) is transferred
-- to a silent divergence of `loop0 body`, using the FD-refinement.  At each peel
-- (`loop-Diverges→`) the chain is EITHER (a) a body′-internal divergence of this
-- iteration — CONSTRUCTIVELY peeled (`bind-loopk-Diverges→`), transferred via
-- `body ⊑D body′`, and pushed up by `body-div→loop0-div` (a FINITE divergence record,
-- collapsed back to a `Diverges` — TERMINATES), OR (b) a silent loop-back with the
-- residual `loop0 body′` still spinning — reconstruct `body`'s OWN silent loop-back
-- (`recover-loopback` at the empty visible trace, via `body ⊑F⊥ body′`), emit `loop0
-- body`'s loop-back τ-chain (≥1 τ), and CORECURSE on the residual (GUARDED).
loopD-transfer : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → body ⊑F⊥ body′ → body ⊑D body′
   → Diverges (loop0 {R = R} body′) → Diverges (loop0 body)

-- Thin guarding indirection (mutual with `loopD-transfer`): a clean top-level
-- function whose body is the corecursion.  Used as the `.rest` of every emitted
-- loop-back step so the corecursive cycle passes through a SEPARATE function, not
-- through `loopD-transfer`'s own `with`-auxiliaries — which is what lets Agda's
-- guardedness checker see the guarding `.step` of the caller.
corecurse-now : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → (f : body ⊑F⊥ body′) (d : body ⊑D body′)
   → Diverges (loop0 {R = R} body′) → Diverges (loop0 body)
corecurse-now body body′ f d dvLoop′ = loopD-transfer body body′ f d dvLoop′

-- View the lifted body-iteration prefix run `P ⟹⟨ [] ⟩ iter-bind Pᵣ (loopStep body)`
-- by its FIRST τ-step.  `inj₁`: the prefix is EMPTY, so the only remaining transition
-- is the loop-back `P ─[τ]─► loop0 body` (the transport `iter-bind Pᵣ ≡ … ≡ loop0 body`
-- is discharged HERE, where the run's endpoint `M` is a flexible Σ-bound variable, so
-- the `⟹-refl` split is not index-stuck).  `inj₂`: a head τ `P ─[τ]─► M` followed by a
-- tail run `M ⟹⟨ [] ⟩ iter-bind Pᵣ` still to walk via `loopback-tail`.
loopback-head : ∀ {R : Set ℓ} (body : PTree E (ExtI E) (⊤ {ℓ}))
   → ∀ {Pᵣ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → force Pᵣ ≡ ret (inj₁ tt)
   → {P : PTree E (ExtI E) R}
   → P ⟹⟨ [] ⟩ (iter-bind Pᵣ (loopStep body))
   → (P ─[ τ ]─► loop0 {R = R} body)            -- empty prefix: head is the loop-back
   ⊎ (Σ[ M ∈ PTree E (ExtI E) R ]
        ((P ─[ τ ]─► M) × (M ⟹⟨ [] ⟩ iter-bind Pᵣ (loopStep body))))
loopback-head body {Pᵣ = Pᵣ} bodyfe ⟹-refl =
  inj₁ (sSil (loop-back-sil body Pᵣ bodyfe))
loopback-head body bodyfe (⟹-τ step rest) =
  inj₂ (_ , step , rest)

-- GUARDED tail walk (mutual with `loopD-transfer`).  Walk the prefix-tail run
-- `P ⟹⟨ [] ⟩ iter-bind Pᵣ (loopStep body)`, emitting each τ as a `Diverges` `.step`;
-- at the run's END (`⟹-refl`, P ≡ iter-bind Pᵣ) emit the LOOP-BACK τ as the `.step`
-- and CORECURSE via `loopD-transfer` directly under `.rest`.  EVERY clause emits a
-- record `.step`, so the corecursion is never returned bare — guardedness holds.
loopback-tail : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → (f : body ⊑F⊥ body′) (d : body ⊑D body′)
   → ∀ {Pᵣ : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
   → force Pᵣ ≡ ret (inj₁ tt)
   → Diverges (loop0 {R = R} body′)
   → {P : PTree E (ExtI E) R}
   → P ⟹⟨ [] ⟩ (iter-bind Pᵣ (loopStep body))
   → Diverges P
loopback-tail body body′ f d {Pᵣ = Pᵣ} bodyfe dvLoop′ ⟹-refl = record
  { step = sSil (loop-back-sil body Pᵣ bodyfe)
  ; rest = loopD-transfer body body′ f d dvLoop′ }
loopback-tail body body′ f d bodyfe dvLoop′ (⟹-τ step rest) = record
  { step = step
  ; rest = loopback-tail body body′ f d bodyfe dvLoop′ rest }

-- COPATTERN-based (productivity-critical): each `Diverges` projection runs the same
-- `loop-Diverges→`/`recover-loopback`/`loopback-head` decision and reads off the
-- corresponding field.  Cases (a)/(b-right) project from a FINITE, pre-built
-- `Diverges` (`div[]→Diverges …`, terminating).  Case (b-left) emits the lifted
-- body-iteration run's FIRST τ as `.step` and CORECURSES under `.rest` — the
-- corecursive `loopback-tail`/self call sits SYNTACTICALLY in the `.rest` copattern
-- clause (the guard), never buried under a `with`-auxiliary's record, so Agda's
-- guardedness checker accepts it.  `.next`, `.step`, `.rest` are kept consistent by
-- running an identical `with`-chain in each.
loopD-transfer {R = R} body body′ f d dv′ .Diverges.next
  with loop-Diverges→ body′ (loopStep body′ tt) dv′
... | inj₁ dStep = div[]→Diverges {body = body}
      (body-div→loop0-div body (d (empty-div (bind-loopk-Diverges→ body′ dStep)))) .Diverges.next
... | inj₂ (Qᵣ , silr , feQ , dvLoop′)
      with recover-loopback body body′ f (⟹-then-τ* ⟹-refl silr) feQ
...     | inj₂ dbody = div[]→Diverges {body = body} dbody .Diverges.next
...     | inj₁ (Pᵣ , bodybs , bodyfe)
          with loopback-head body bodyfe
                 (lift-iter-bigstep (loopStep body tt) Pᵣ (loopStep body) [] bodybs)
...         | inj₁ _                = loop0 body
...         | inj₂ (M , _ , _)      = M

loopD-transfer {R = R} body body′ f d dv′ .Diverges.step
  with loop-Diverges→ body′ (loopStep body′ tt) dv′
... | inj₁ dStep = div[]→Diverges {body = body}
      (body-div→loop0-div body (d (empty-div (bind-loopk-Diverges→ body′ dStep)))) .Diverges.step
... | inj₂ (Qᵣ , silr , feQ , dvLoop′)
      with recover-loopback body body′ f (⟹-then-τ* ⟹-refl silr) feQ
...     | inj₂ dbody = div[]→Diverges {body = body} dbody .Diverges.step
...     | inj₁ (Pᵣ , bodybs , bodyfe)
          with loopback-head body bodyfe
                 (lift-iter-bigstep (loopStep body tt) Pᵣ (loopStep body) [] bodybs)
...         | inj₁ head             = head
...         | inj₂ (M , head , tail) = head

loopD-transfer {R = R} body body′ f d dv′ .Diverges.rest
  with loop-Diverges→ body′ (loopStep body′ tt) dv′
... | inj₁ dStep = div[]→Diverges {body = body}
      (body-div→loop0-div body (d (empty-div (bind-loopk-Diverges→ body′ dStep)))) .Diverges.rest
... | inj₂ (Qᵣ , silr , feQ , dvLoop′)
      with recover-loopback body body′ f (⟹-then-τ* ⟹-refl silr) feQ
...     | inj₂ dbody = div[]→Diverges {body = body} dbody .Diverges.rest
...     | inj₁ (Pᵣ , bodybs , bodyfe)
          with loopback-head body bodyfe
                 (lift-iter-bigstep (loopStep body tt) Pᵣ (loopStep body) [] bodybs)
...         | inj₁ _                = corecurse-now body body′ f d dvLoop′
...         | inj₂ (M , head , tail) = loopback-tail body body′ f d bodyfe dvLoop′ tail

-- ============================================================================
-- loop0-mono-⊑D : the divergence-refinement half (Task 3).
--
-- `divergences (loop0 body′) s` decomposes via `loop-trace<` to a `LoopSplit<`
-- reaching a diverging state `Q`; recursion is well-founded on the run-step count
-- `runLen` (the `in-loop` loop-back consumes ≥1 τ).  The `in-body` arm — the
-- diverging state is `iter-bind P′ (loopStep body′)` — is the ONLY classical step:
-- `loop-Diverges→` decides whether the divergence is body′-internal this iteration
-- (transfer via `body ⊑D body′`, the bind-into-loop-k peel being CONSTRUCTIVE) or
-- the loop spins (body′ terminates and loops back; reconstruct the body-side
-- loop-back via `body ⊑F⊥ body′` and `loop0-spins-diverges`, exactly as
-- `mono-fail`'s in-loop).  The `in-loop` arm recurses on the shorter `s₂` run and
-- prepends the reconstructed body-side iteration (`loop0-prepend-div`).
-- ============================================================================
loop0-mono-⊑D : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → body ⊑F⊥ body′ → body ⊑D body′ → (loop0 {R = R} body) ⊑D (loop0 body′)

-- WORKER: by well-founded recursion on the run-step count of the divergence reach.
mono-div : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → body ⊑F⊥ body′ → body ⊑D body′
   → ∀ {prefix} (Q : PTree E (ExtI E) R)
   → (run : loop0 body′ ⟹⟨ prefix ⟩ Q) → Acc _<_ (runLen run) → Diverges Q
   → divergences (loop0 body) prefix

loop0-mono-⊑D {R = R} body body′ f d {s} dv =
  subst-div0 {body = body} (sym (dv .split))
    (div-extension-closed {t = dv .suffix}
      (mono-div body body′ f d (dv .witness) (dv .reach)
                (<-wellFounded (runLen (dv .reach))) (dv .divwit)))

mono-div {R = R} body body′ f d {prefix} Q run (acc rs) dvQ
  with loop-trace< body′ run
-- ── in-body : ONE in-progress body′-iteration; THE classical (loop-Diverges→) step.
... | in-body< {P′ = P′} bs refl
      with loop-Diverges→ body′ P′ dvQ
-- (a) the divergence stays inside this iteration's source P′ (= body′ >>= loop-k):
--     peel CONSTRUCTIVELY to a body′-internal divergence, transfer via `d`, push up.
--     Worker at a GENERIC trace `s` (with `s ≡ map evl vs` carried separately) so the
--     in-P/in-k trace index unifies cleanly (mirrors `in-body-map′`/`body-terminates`).
...   | inj₁ dP′ = peel-body (map evl _) refl dP′ (bind-bigstep-inv body′ loop-k bs)
  where
    peel-body : ∀ {vs} {P′} (s : List (Event√ (⊤ {ℓ} ⊎ R))) → s ≡ map evl vs
              → Diverges P′ → BindSplit body′ loop-k P′ s
              → divergences (loop0 body) (map evl vs)
    peel-body {vs} .(map evl vs₀) seq dP (BindSplit.in-P {P′ = P″} {vs = vs₀} runB refl)
        with map-evl-inj {R = ⊤ {ℓ} ⊎ R} seq
    ... | refl =
          body-div→loop0-div body
            (d (record { prefix  = map evl vs₀ ; suffix = []
                       ; split   = sym (++-identityʳ (map evl vs₀))
                       ; witness = P″ ; reach = runB
                       ; divwit  = bind-loopk-Diverges→ P″ dP }))
    peel-body {vs} {P′} .(map evl s₁ ++ s₂) seq dP
              (BindSplit.in-k {r = tt} {s₁ = s₁} {s₂ = s₂} runB eqr kr)
        with evl-split (map evl s₁) vs s₂ (sym seq)
    ...   | vs₁ , vs₂ , _ , refl , _ =
            -- `loop-k tt` forces `ret (inj₁ tt)`; a purely-visible run is STUCK there,
            -- so the BindSplit target `P′` is forced `ret (inj₁ tt)`, hence `Diverges P′`
            -- is absurd.
            ⊥-elim (ret-diverges-absurd
                     (ret-stuck {R = ⊤ {ℓ} ⊎ R} {Q = loop-k tt} {P′ = P′} {x = inj₁ tt} vs₂ refl kr) dP)
      where ret-diverges-absurd : ∀ {x} → force P′ ≡ ret x → Diverges P′ → ⊥
            ret-diverges-absurd eqf dp with τ-inv (dp .step)
            ... | inj₁ ef                         with () ← trans (sym eqf) ef
            ... | inj₂ (_ , _ , _ , _ , ef , _)  with () ← trans (sym eqf) ef
-- (b) the iteration COMPLETES (loop-back) and the residual `loop0 body′` SPINS:
--     reconstruct body's vs-iteration loop-back (via `f`) and transfer the silent
--     spin to `loop0 body` (`loopD-transfer`, the coinductive transfer), then prepend.
mono-div {R = R} body body′ f d {prefix} Q run (acc rs) dvQ
    | in-body< {P′ = P′} {vs = vs} bs refl
      | inj₂ (Qᵣ , silr , feQ , dvLoop′)
        with recover-loopback body body′ f (⟹-then-τ* bs silr) feQ
...       | inj₁ (Pᵣ-b , bodybs , bodyfe) =
            subst-div0 {body = body} (++-identityʳ (map evl vs))
              (loop0-prepend-div body bodybs bodyfe
                 (empty-div (loopD-transfer body body′ f d dvLoop′)))
...       | inj₂ dbody = dbody
-- ── in-loop : ONE complete body′-iteration (s₁) + the rest (s₂).  Recurse on s₂.
mono-div {R = R} body body′ f d {prefix} Q run (acc rs) dvQ
    | in-loop< {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} bs fe kr lt
      with recover-loopback body body′ f bs fe
...   | inj₁ (Pᵣ-b , bodybs , bodyfe) =
        loop0-prepend-div body bodybs bodyfe
          (mono-div body body′ f d Q kr (rs lt) dvQ)
...   | inj₂ dbody =
        div-extension-closed {t = s₂} dbody

-- ============================================================================
-- loop0-mono-⊑F⊥ : THE SPIKE.  POSTULATE-FREE, HOLE-FREE (modulo the ⊑D hole).
-- ============================================================================

-- WORKER on the FAILURE half (explicit run), by well-founded recursion on the
-- run-step count `runLen run` (the loop-back consumes ≥1 τ each iteration).
mono-fail : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → body ⊑F⊥ body′ → body ⊑D body′
   → ∀ {s} {B : Event√ R → Set ℓ} (Q : PTree E (ExtI E) R)
   → (run : loop0 body′ ⟹⟨ s ⟩ Q) → Acc _<_ (runLen run) → Refuses Q B
   → failures⊥ (loop0 body) s B
mono-fail {R = R} body body′ f d {s} {B} Q run (acc rs) ref
  with loop-trace< body′ run
-- ── in-body : ONE in-progress body′-iteration; immediate via the Task-1 helper.
... | in-body< {P′ = P′} bs refl =
      in-body-map body body′ f bs ref
-- ── in-loop : ONE complete body′-iteration (s₁) + the rest (s₂).  Recurse on s₂
--    (strictly shorter run, `lt`), then prepend the reconstructed body-iteration.
... | in-loop< {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} bs fe kr lt
      with body-terminates body′ bs fe                  -- body′ TERMINATES on s₁
...   | (Bᵣ′ , bodyrun′ , feB′)
        -- feed body′'s √-termination failure through `body ⊑F⊥ body′` and case
        -- on whether `body` matches it by a failure (terminates) or a divergence.
        with f {map evl s₁ ++ √ tt ∷ []} {λ _ → Lift ℓ ⊥}
                 (inj₁ (term→√failure {x = tt} bodyrun′ feB′))
...     | inj₁ (T , brun , bref) with √-run-split s₁ brun
...       | (Bᵣ , bodyrun , feB) =
            -- body reaches `ret tt` on s₁ ⇒ build the body-side loop iteration
            -- `loopStep body tt ⟹⟨s₁⟩ (Bᵣ >>= loop-k)`, force `ret (inj₁ tt)`;
            -- recurse on s₂ then prepend.
            loop0-prepend-iter body
              (lift-bind-bigstep body Bᵣ loop-k s₁ bodyrun)
              (bind-force-ret Bᵣ loop-k feB)
              (mono-fail body body′ f d Q kr (rs lt) ref)
-- ── body matched body′'s termination by a DIVERGENCE: loop0 body diverges.
mono-fail {R = R} body body′ f d {s} {B} Q run (acc rs) ref
    | in-loop< {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} bs fe kr lt
      | (Bᵣ′ , bodyrun′ , feB′)
        | inj₂ dbody with div-√-prefix-visible body dbody
...       | (vs′ , mid , es , dvis) =
            inj₂ (subst-div (sym (push es))
                    (div-extension-closed {t = map evl mid ++ s₂}
                      (body-div→loop0-div body dvis)))
  where
    -- `loop0 body` diverges at `map evl vs′`; extend to `map evl s₁ ++ s₂`.
    push : s₁ ≡ vs′ ++ mid → map evl s₁ ++ s₂ ≡ map evl vs′ ++ (map evl mid ++ s₂)
    push refl = trans (cong (_++ s₂) (map-++ evl vs′ mid)) (++-assoc (map evl vs′) (map evl mid) s₂)
    subst-div : ∀ {t t′} → t ≡ t′ → divergences (loop0 body) t → divergences (loop0 body) t′
    subst-div refl x = x

loop0-mono-⊑F⊥ : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → body ⊑F⊥ body′ → body ⊑D body′ → (loop0 {R = R} body) ⊑F⊥ (loop0 body′)
loop0-mono-⊑F⊥ {R = R} body body′ f d {s} {B} (inj₁ (Q , run , ref)) =
  mono-fail body body′ f d Q run (<-wellFounded (runLen run)) ref
loop0-mono-⊑F⊥ {R = R} body body′ f d {s} {B} (inj₂ dv) =
  inj₂ (loop0-mono-⊑D body body′ f d dv)

-- ============================================================================
-- Task 4: loop0-mono-⊑FD — pair the two halves (`_⊑FD_ = (_⊑F⊥_) × (_⊑D_)`).
-- ============================================================================
loop0-mono-⊑FD : ∀ {R : Set ℓ} (body body′ : PTree E (ExtI E) (⊤ {ℓ}))
   → body ⊑FD body′ → (loop0 {R = R} body) ⊑FD (loop0 body′)
loop0-mono-⊑FD body body′ (f , d) =
  loop0-mono-⊑F⊥ body body′ f d , loop0-mono-⊑D body body′ f d

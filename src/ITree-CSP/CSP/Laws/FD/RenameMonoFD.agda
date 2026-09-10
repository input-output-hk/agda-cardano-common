{-# OPTIONS --guardedness #-}

-- FACT-SHAPED (`⊑FD → ⊑FD`) monotonicity for RENAMING — the same-alphabet functional
-- wrapper `renameInv` and its `renameMap` specialisation.  Renaming had NO monotonicity
-- law at any shape before this module; the precedents were `renameInv-mono-⊑ᵀ` at `⊑T`
-- (`CSP.Laws.Traces.TraceLawsRename`) and the unconditional `≈DR` congruences
-- `cong-renameInv`/`cong-renameMap` (`CSP.Laws.Bisim.DRCongruence`, section 4).
--
--   renameInv-mono-⊇D  : P ⊇D  Q → (P ⟦ inv ⟧ⁱ) ⊇D  (Q ⟦ inv ⟧ⁱ)    UNCONDITIONAL
--   renameInv-mono-⊇F⊥ : RenTight inv → P ⊇F⊥ Q → …  ⊇F⊥ …           see side condition
--   renameInv-mono-⊑FD : RenTight inv → P ⊑FD Q → …  ⊑FD …
--   renameMap-mono-⊇D / -⊇F⊥ / -⊑FD                                  UNCONDITIONAL
--
-- ── NOTE ON PARAMETERISATION (a correction worth recording) ────────────────────────
--
-- No `ι`/`ι⁻¹`/`ι-linv` module telescope is needed and no `E-≟` either.  `cong-renameInv`
-- sits inside a parameterised inner module because it is stated CROSS-ALPHABET
-- (`E₁ = E`, `E₂` arbitrary).  The trace-level precedent `renameInv-mono-⊑ᵀ` is stated at
-- the SAME alphabet — `CSP.Laws.Traces.TraceLawsRename` instantiates `CSP.Rename` at
-- `E₁ = E₂ = E`, `ι = id`, `ι⁻¹ = just`, and takes no parameters at all — and this module
-- follows it, reusing its `RenTr` / `ren-trace-elim` / single-step suite wholesale.  The
-- cross-alphabet generalisation would need the telescope; it is not attempted here
-- because `_⊇F⊥_` would then pin TWO different ban levels (see below).
--
-- ── THE `⊇D` HALF IS CONSTRUCTIVE.  VERIFIED, not assumed. ────────────────────────
--
-- `renameInv` is a step-for-step STRUCTURAL relabelling: `ret r ↦ ret r`,
-- `sil P′ ↦ sil (renamed P′)`, and a `react` node keeps its τ-branch map (merely
-- re-tagged).  So the τ-spaces correspond ONE-FOR-ONE (`ren-τ-fwd` / `ren-τ-inv` are
-- inverse to each other on steps) and `Diverges (P ⟦inv⟧ⁱ) ↔ Diverges P` is a plain
-- corecursive projection — NO König step, NO `Diverges-LEM`, NO decision about where an
-- infinite τ-chain lives, because there is only one place it can live.  This is exactly
-- why rename is the cheap congruence and hiding/parallel/interrupt are the expensive ones.
-- ZERO postulates, local or inherited, reach the `⊇D` half.
--
-- ── THE `⊇F⊥` HALF NEEDS `RenTight`, AND THE REASON IS A LEVEL ARTEFACT ────────────
--
-- Transferring a still-reachable REFUSAL needs the target ban set PULLED BACK along
-- `inv` to a source ban set.  The mathematically right pullback is
--
--     banFull B e  =  Σ[ b ∈ target event ] (inv b ≡ just e × B (evl b))
--
-- and with it the law is unconditional.  But `_⊇F⊥_ {R = Rr}` pins its ban sets to
-- `Event√ Rr → Set ℓr` — the CARRIER's level — while `banFull` lives at
-- `lsuc ℓ ⊔ ℓe ⊔ ℓr`, because it quantifies over `AnyTypes E`.  `Lift` only raises
-- levels, so `banFull` cannot be fed to the premise unless `ℓr ≥ lsuc ℓ ⊔ ℓe`, which no
-- real carrier in this repo satisfies (they are `⊤ {ℓ}` and friends).  This is a
-- LEVEL artefact of how `_⊇F⊥_` is stated, NOT a failure of FD-monotonicity: renaming is
-- an FD congruence in Roscoe, and the `≈DR` congruence here is unconditional.
--
-- The WEAKEST repair that keeps the law usable at every level is to make the pullback
-- POINTWISE, which needs each source event to have AT MOST ONE `inv`-preimage — i.e.
-- `inv` must be a partial BIJECTION on concrete events, not merely a partial function.
-- That is `RenTight` below: a forward section `fwd` with `inv (fwd ce) ≡ just ce`, plus
-- the converse `inv ce ≡ just ce′ → ce ≡ fwd ce′`.  With it, `banSrc B e = B (fwd e)` is
-- at level `ℓr` and everything goes through.
--
-- What `RenTight` rules out is visible FAN-OUT (`inv` sending two target events to one
-- source event, which the operator does allow and which merely duplicates offers).  It
-- does NOT rule out partiality: targets outside the image simply offer nothing, and
-- `RenTight` says nothing about them.  It is DISCHARGED for `renameMap` below, because at
-- the same alphabet `ι = id` / `ι⁻¹ = just` makes `ι-vis-inv` the identity inverse.

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.RenameMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe} where
open PTree

open import Semantics.LTS      {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals {E = E} {I = ExtI E}
  using (Refuses; Offers; deadlock-refuses)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊇F⊥_; _⊇D_; _⊑FD_; failures⊥; divergences; IsDivergence
        ; div-extension-closed)
open import Semantics.DRBisim  {E = E} {I = ExtI E} using (Diverges; deadlock-converges)
open import Semantics.Stability {E = E} {I = ExtI E}
  using (stable-not-ret; stable→react; react-no-τ→stable; stable-no-τ)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (ConcEvent₁; renameInv; renameMap; ι-vis-inv)
open import CSP.Laws.Traces.TraceLawsRename {E = E}
  using (_⟦_⟧ⁱ; RenTr; []ᵣ; evᵣ; √ᵣ; deadlock-⟹-[]
        ; ren-τ-fwd; ren-ev-fwd; ren-√-fwd; ren-τ-inv; ren-ev-inv
        ; force-ren-react; force-ren-react-inv)
open IsDivergence

private
  variable
    ℓr : Level
    Rr : Set ℓr

-- the per-target partial inverse that drives `renameInv` (same alphabet)
RenInv : Set (lsuc ℓ ⊔ ℓe)
RenInv = (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁

-- uncurried application of an inverse to a concrete event
appInv : RenInv → ConcEvent₁ → Maybe ConcEvent₁
appInv inv (bt , b) = inv bt b

-- a concrete event, as an LTS `Event`
toEv : ConcEvent₁ → Event
toEv (at , a) = evLabel (proj₁ at) (proj₂ at) a

-------------------------------------------------------------------------------------
-- PART 0 : `Diverges` transfers both ways, CONSTRUCTIVELY (the `⊇D` half's engine).
--
-- Same shape as `CSP.Laws.Bisim.DRCongruence`'s `ren-Diverges→`/`←`, restated here at
-- the same alphabet so this module needs neither that module's `ι` telescope nor `E-≟`.
-------------------------------------------------------------------------------------

-- an infinite τ-run of the RENAMED tree reflects to one of the source (`ren-τ-inv` is a
-- Σ, so the copattern definition is pure projections — productive).
ren-Diverges→ : {inv : RenInv} (P : PTree E (ExtI E) Rr)
              → Diverges (P ⟦ inv ⟧ⁱ) → Diverges P
ren-Diverges→ {inv = inv} P d .Diverges.next =
  proj₁ (ren-τ-inv {inv = inv} {P = P} (d .Diverges.step))
ren-Diverges→ {inv = inv} P d .Diverges.step =
  proj₁ (proj₂ (ren-τ-inv {inv = inv} {P = P} (d .Diverges.step)))
ren-Diverges→ {inv = inv} P d .Diverges.rest =
  ren-Diverges→ _
    (subst Diverges (proj₂ (proj₂ (ren-τ-inv {inv = inv} {P = P} (d .Diverges.step))))
           (d .Diverges.rest))

-- an infinite τ-run of the source renames to one of the renamed tree.
ren-Diverges← : {inv : RenInv} (P : PTree E (ExtI E) Rr)
              → Diverges P → Diverges (P ⟦ inv ⟧ⁱ)
ren-Diverges← {inv = inv} P d .Diverges.next = (d .Diverges.next) ⟦ inv ⟧ⁱ
ren-Diverges← {inv = inv} P d .Diverges.step = ren-τ-fwd (d .Diverges.step)
ren-Diverges← {inv = inv} P d .Diverges.rest = ren-Diverges← _ (d .Diverges.rest)

-------------------------------------------------------------------------------------
-- PART 1 : `RenTr` list surgery, and run introduction that keeps the endpoint.
-------------------------------------------------------------------------------------

-- SPLIT a trace renaming along a source-side concatenation: the target trace splits at
-- the matching point.  (Needed because `⊇D` returns a divergence whose PREFIX is only a
-- prefix of the trace we handed it.)
RenTr-split : ∀ {inv} (s₁ : List (Event√ Rr)) {s₂ t}
            → RenTr inv (s₁ ++ s₂) t
            → Σ[ t₁ ∈ List (Event√ Rr) ] Σ[ t₂ ∈ List (Event√ Rr) ]
                (t ≡ t₁ ++ t₂ × RenTr inv s₁ t₁ × RenTr inv s₂ t₂)
RenTr-split []        rn                 = [] , _ , refl , []ᵣ , rn
RenTr-split (_ ∷ s₁) (evᵣ eqi rn) with RenTr-split s₁ rn
... | t₁ , t₂ , refl , r₁ , r₂ = _ ∷ t₁ , t₂ , refl , evᵣ eqi r₁ , r₂
RenTr-split (_ ∷ s₁) (√ᵣ rn)     with RenTr-split s₁ rn
... | t₁ , t₂ , refl , r₁ , r₂ = _ ∷ t₁ , t₂ , refl , √ᵣ r₁ , r₂

-- INTRO keeping the endpoint: a source run whose trace renames to `t` gives a renamed run
-- to the RENAMED endpoint.  (Unlike `ren-trace-intro`, which forgets the endpoint; the
-- `√` clause is impossible here because a `√`-tick lands in `deadlock`, whose renaming is
-- not syntactically `deadlock` — that clause is handled by `ren-fail-intro` instead.)
ren-run-intro : ∀ {inv} {P P′ : PTree E (ExtI E) Rr} {s t}
              → P ⟹⟨ s ⟩ P′ → RenTr inv s t → (P ⟦ inv ⟧ⁱ) ⟹⟨ t ⟩ (P′ ⟦ inv ⟧ⁱ)
              ⊎ Σ[ r ∈ Rr ] Σ[ s₀ ∈ List (Event√ Rr) ] Σ[ s₁ ∈ List (Event√ Rr) ]
                  (s ≡ s₀ ++ √ r ∷ s₁)
ren-run-intro ⟹-refl               []ᵣ            = inj₁ ⟹-refl
ren-run-intro (⟹-τ pτ rest)        rn with ren-run-intro rest rn
... | inj₁ run               = inj₁ (⟹-τ (ren-τ-fwd pτ) run)
... | inj₂ (r , s₀ , s₁ , e) = inj₂ (r , s₀ , s₁ , e)
ren-run-intro (⟹-ev pev rest)      (evᵣ eqi rn) with ren-run-intro rest rn
... | inj₁ run                  = inj₁ (⟹-ev (ren-ev-fwd pev eqi) run)
... | inj₂ (r , s₀ , s₁ , refl) = inj₂ (r , _ ∷ s₀ , s₁ , refl)
ren-run-intro (⟹-ev pev rest)      (√ᵣ {r = r} rn) = inj₂ (r , [] , _ , refl)

-- ELIM keeping the endpoint: a run of the renamed tree inverts to a source run whose
-- trace renames to it, AND the two endpoints correspond.  `CSP.Laws.Traces.TraceLawsRename`'s
-- `ren-trace-elim` drops the endpoint relation, which is precisely what a failure or a
-- divergence needs, so it is re-derived here with that extra component.  The `√` clause is
-- why the relation is a disjunction: a tick lands in `deadlock` on BOTH sides, and
-- `deadlock` is not syntactically `deadlock ⟦ inv ⟧ⁱ`.
ren-run-elim : ∀ {inv} {Q W : PTree E (ExtI E) Rr} {t}
             → (Q ⟦ inv ⟧ⁱ) ⟹⟨ t ⟩ W
             → Σ[ s ∈ List (Event√ Rr) ] Σ[ Q′ ∈ PTree E (ExtI E) Rr ]
                 ((Q ⟹⟨ s ⟩ Q′) × RenTr inv s t
                  × ((W ≡ Q′ ⟦ inv ⟧ⁱ) ⊎ (W ≡ deadlock × Q′ ≡ deadlock)))
ren-run-elim ⟹-refl = [] , _ , ⟹-refl , []ᵣ , inj₁ refl
ren-run-elim {inv = inv} {Q = Q} (⟹-τ step rest) with ren-τ-inv {inv = inv} {P = Q} step
... | Q₁ , Qτ , refl with ren-run-elim rest
...   | s , Q′ , Qreach , rn , eq = s , Q′ , ⟹-τ Qτ Qreach , rn , eq
ren-run-elim {inv = inv} {Q = Q} (⟹-ev step rest) with ren-ev-inv {inv = inv} {P = Q} step
... | inj₁ (at , a , bt , b , Q₁ , Qev , eqi , refl , refl) with ren-run-elim rest
...   | s , Q′ , Qreach , rn , eq =
        evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s , Q′ , ⟹-ev Qev Qreach , evᵣ eqi rn , eq
ren-run-elim {inv = inv} {Q = Q} (⟹-ev step rest) | inj₂ (r , refl , eqQ , refl)
  with deadlock-⟹-[] rest
...   | refl , refl =
        √ r ∷ [] , deadlock , ⟹-ev (sRet eqQ) ⟹-refl , √ᵣ []ᵣ , inj₂ (refl , refl)

-- A run whose trace PASSES a `√` lands in `deadlock`, which cannot diverge — so a
-- divergence's reach never crosses a tick.  (Local copy: `CSP.Laws.FD.IterateMonoFD` has
-- the same lemma, but importing it would drag an `E-≟` parameter into this module.)
no-div-through-√ : ∀ {ℓr₀} {R₀ : Set ℓr₀} {r : R₀} {V W : PTree E (ExtI E) R₀}
                   (s₀ s₁ : List (Event√ R₀))
                 → V ⟹⟨ s₀ ++ √ r ∷ s₁ ⟩ W → Diverges W → ⊥
no-div-through-√ []       s₁ (⟹-τ _ rest)         dv = no-div-through-√ [] s₁ rest dv
no-div-through-√ []       s₁ (⟹-ev (sRet _) rest) dv with deadlock-⟹-[] rest
... | refl , refl                                       = deadlock-converges dv
no-div-through-√ (_ ∷ es) s₁ (⟹-τ _ rest)         dv = no-div-through-√ (_ ∷ es) s₁ rest dv
no-div-through-√ (_ ∷ es) s₁ (⟹-ev _ rest)        dv = no-div-through-√ es s₁ rest dv

-------------------------------------------------------------------------------------
-- PART 2 : the `⊇D` half — UNCONDITIONAL.
-------------------------------------------------------------------------------------

-- ELIM a renamed divergence to a source one, remembering the trace renaming.
ren-div-elim : ∀ {inv} (Q : PTree E (ExtI E) Rr) {t}
             → divergences (Q ⟦ inv ⟧ⁱ) t
             → Σ[ s ∈ List (Event√ Rr) ] Σ[ t₁ ∈ List (Event√ Rr) ]
                 Σ[ t₂ ∈ List (Event√ Rr) ]
                   (t ≡ t₁ ++ t₂ × RenTr inv s t₁ × divergences Q s)
ren-div-elim {inv = inv} Q d with ren-run-elim {inv = inv} {Q = Q} (d .reach)
-- the reached state IS the renamed source state: reflect the `Diverges` and repackage.
... | s , Q′ , Qreach , rn , inj₁ refl =
      s , d .prefix , d .suffix , d .split , rn
      , record { prefix = s ; suffix = [] ; split = sym (++-identityʳ s)
               ; witness = Q′ ; reach = Qreach
               ; divwit = ren-Diverges→ Q′ (d .divwit) }
-- the reach passed a `√` and sits in `deadlock`, which cannot diverge.
... | s , Q′ , Qreach , rn , inj₂ (refl , refl) = ⊥-elim (deadlock-converges (d .divwit))

-- INTRO a source divergence back through the rename, at the renamed trace.
ren-div-intro : ∀ {inv} (P : PTree E (ExtI E) Rr) {s t}
              → RenTr inv s t → divergences P s → divergences (P ⟦ inv ⟧ⁱ) t
ren-div-intro {inv = inv} P {s} {t} rn d
  with RenTr-split (d .prefix) (subst (λ z → RenTr inv z t) (d .split) rn)
... | t₁ , t₂ , refl , r₁ , r₂ with ren-run-intro (d .reach) r₁
-- the divergence's own reach renames endpoint-and-all: push the `Diverges` through.
...   | inj₁ run =
        div-extension-closed {t = t₂}
          (record { prefix = t₁ ; suffix = [] ; split = sym (++-identityʳ t₁)
                  ; witness = (d .witness) ⟦ inv ⟧ⁱ ; reach = run
                  ; divwit = ren-Diverges← (d .witness) (d .divwit) })
-- a divergence reach cannot end in a `√`: the tick lands in `deadlock`, which is stable.
...   | inj₂ (r , s₀ , s₁ , eqs) =
        ⊥-elim (no-div-through-√ s₀ s₁ (subst (P ⟹⟨_⟩ _) eqs (d .reach)) (d .divwit))

-- RENAMING IS ⊇D-MONOTONE, unconditionally and constructively.
renameInv-mono-⊇D : ∀ {inv} {P Q : PTree E (ExtI E) Rr}
                  → P ⊇D Q → (P ⟦ inv ⟧ⁱ) ⊇D (Q ⟦ inv ⟧ⁱ)
renameInv-mono-⊇D {inv = inv} {P = P} {Q = Q} pq d
  with ren-div-elim {inv = inv} Q d
... | s , t₁ , t₂ , refl , rn , dQ =
      div-extension-closed {t = t₂} (ren-div-intro P rn (pq dQ))

-------------------------------------------------------------------------------------
-- PART 3 : stability and offers across the rename (both directions).
-------------------------------------------------------------------------------------

-- a stable renamed state has a stable source (its `react` node is the source's, and each
-- source τ would rename to a τ of the renamed state).
ren-stable-elim : ∀ {inv} {W : PTree E (ExtI E) Rr}
                → isStable (W ⟦ inv ⟧ⁱ) → isStable W
ren-stable-elim {inv = inv} {W = W} st with stable→react {t = W ⟦ inv ⟧ⁱ} st
... | v , τc , eqf , _ with force-ren-react-inv {inv = inv} {P = W} eqf
...   | vP , τcP , eqW , _ , _ =
        react-no-τ→stable {t = W} eqW (λ stp → stable-no-τ st (ren-τ-fwd stp))

-- …and conversely (each τ of the renamed state inverts to a source τ).
ren-stable-intro : ∀ {inv} {W : PTree E (ExtI E) Rr}
                 → isStable W → isStable (W ⟦ inv ⟧ⁱ)
ren-stable-intro {inv = inv} {W = W} st with stable→react {t = W} st
... | v , τc , eqf , _ =
      react-no-τ→stable {t = W ⟦ inv ⟧ⁱ} (force-ren-react {inv = inv} {P = W} eqf)
        (λ stp → stable-no-τ st (proj₁ (proj₂ (ren-τ-inv {inv = inv} {P = W} stp))))

-------------------------------------------------------------------------------------
-- PART 4 : `RenTight` and the pointwise ban-set pullback.
-------------------------------------------------------------------------------------

-- `inv` is a partial BIJECTION on concrete events: it has a forward section `fwd`, and
-- every `inv`-preimage of a source event IS that section's value (no visible fan-out).
record RenTight (inv : RenInv) : Set (lsuc ℓ ⊔ ℓe) where
  field
    fwd     : ConcEvent₁ → ConcEvent₁
    fwd-inv : ∀ ce → appInv inv (fwd ce) ≡ just ce
    inv-fwd : ∀ ce ce′ → appInv inv ce ≡ just ce′ → ce ≡ fwd ce′
open RenTight

-- POINTWISE pullback of a target ban set: ban a source event exactly when its unique
-- target counterpart is banned.  Bans no `√` (only a stable state refuses, and a stable
-- state never forces to a `ret`, so `√` is the one event it cannot offer) — the same
-- device as `CSP.Laws.FD.IterateMonoFD.banEvl` / `BindMonoFD.banP`.
banSrc : ∀ {inv} → RenTight inv → (Event√ Rr → Set ℓr) → Event√ Rr → Set ℓr
banSrc         tg B (evl (evLabel A e a)) = B (evl (toEv (fwd tg ((A , e) , a))))
banSrc {ℓr = ℓr} tg B (√ _)               = Lift ℓr ⊥

-- REFUSAL ELIM: a refusal of the renamed state IS the pulled-back refusal of the source.
refuses-ren-elim : ∀ {inv} (tg : RenTight inv) {W : PTree E (ExtI E) Rr}
                   {B : Event√ Rr → Set ℓr}
                 → Refuses (W ⟦ inv ⟧ⁱ) B → Refuses W (banSrc tg B)
refuses-ren-elim {inv = inv} tg {W} {B} (st , noff) = ren-stable-elim {inv = inv} {W = W} st , go
  where
    go : ∀ e → banSrc tg B e → ¬ Offers W e
    go (evl (evLabel A e a)) Be (t′ , stp) =
      noff (evl (toEv (fwd tg ((A , e) , a)))) Be
           (_ , ren-ev-fwd {inv = inv} stp (fwd-inv tg ((A , e) , a)))
    go (√ _) Be _ = ⊥-elim (lower Be)

-- REFUSAL INTRO: the pulled-back refusal of the source lifts back to the renamed state.
refuses-ren-intro : ∀ {inv} (tg : RenTight inv) {W : PTree E (ExtI E) Rr}
                    {B : Event√ Rr → Set ℓr}
                  → Refuses W (banSrc tg B) → Refuses (W ⟦ inv ⟧ⁱ) B
refuses-ren-intro {inv = inv} tg {W} {B} (stW , noff) = stR , go
  where
    stR : isStable (W ⟦ inv ⟧ⁱ)
    stR = ren-stable-intro {inv = inv} {W = W} stW
    go : ∀ e → B e → ¬ Offers (W ⟦ inv ⟧ⁱ) e
    go e Be (t′ , stp) with ren-ev-inv {inv = inv} {P = W} stp
    -- a visible offer: it comes from a source offer at `inv`'s value, and `RenTight`
    -- identifies the offered target event with `fwd` of that source event, which is
    -- exactly what `banSrc` bans.
    ... | inj₁ (at , a , bt , b , P₁ , Pev , eqi , refl , _) =
          noff (evl (toEv (at , a)))
               (subst (λ ce → B (evl (toEv ce))) (inv-fwd tg (bt , b) (at , a) eqi) Be)
               (P₁ , Pev)
    -- a `√` offer would force the renamed state to a `ret`, contradicting stability.
    ... | inj₂ (r , refl , eqf , _) =
          ⊥-elim (stable-not-ret {t = W ⟦ inv ⟧ⁱ} stR (force-ren-ret′ eqf))
      where force-ren-ret′ : force W ≡ ret r → force (W ⟦ inv ⟧ⁱ) ≡ ret r
            force-ren-ret′ eq with force W
            ... | ret _ = eq

-------------------------------------------------------------------------------------
-- PART 5 : the `⊇F⊥` half, and the paired laws.
-------------------------------------------------------------------------------------

-- INTRO a source FAILURE back through the rename, at the renamed trace.  Mirrors
-- `ren-trace-intro`'s three clauses, threading the (pulled-back) refusal; the `√` clause
-- ends at `deadlock` on BOTH sides, which refuses everything.
ren-fail-intro : ∀ {inv} (tg : RenTight inv) {P P′ : PTree E (ExtI E) Rr} {s t}
                 {B : Event√ Rr → Set ℓr}
               → P ⟹⟨ s ⟩ P′ → RenTr inv s t → Refuses P′ (banSrc tg B)
               → failures (P ⟦ inv ⟧ⁱ) t B
ren-fail-intro {inv = inv} tg ⟹-refl []ᵣ ref = _ , ⟹-refl , refuses-ren-intro tg ref
ren-fail-intro {inv = inv} tg (⟹-τ pτ rest) rn ref
  with ren-fail-intro tg rest rn ref
... | W , run , r = W , ⟹-τ (ren-τ-fwd pτ) run , r
ren-fail-intro {inv = inv} tg (⟹-ev pev rest) (evᵣ eqi rn) ref
  with ren-fail-intro tg rest rn ref
... | W , run , r = W , ⟹-ev (ren-ev-fwd pev eqi) run , r
ren-fail-intro {inv = inv} tg (⟹-ev (sRet eq) rest) (√ᵣ rn) ref
  with deadlock-⟹-[] rest
... | refl , refl with rn
...   | []ᵣ = deadlock , ⟹-ev (ren-√-fwd {inv = inv} eq) ⟹-refl , deadlock-refuses

-- RENAMING IS ⊇F⊥-MONOTONE for a tight `inv`: elim the impl-side failure⊥ to the source
-- (pulling the ban set back), transport it, re-intro at the SAME renamed trace.
renameInv-mono-⊇F⊥ : ∀ {inv} (tg : RenTight inv) {P Q : PTree E (ExtI E) Rr}
                   → P ⊇F⊥ Q → P ⊇D Q → (P ⟦ inv ⟧ⁱ) ⊇F⊥ (Q ⟦ inv ⟧ⁱ)
-- a genuine reached refusal of the renamed impl.
renameInv-mono-⊇F⊥ {inv = inv} tg {P} {Q} f d {t} {B} (inj₁ (W , run , ref))
  with ren-run-elim {inv = inv} {Q = Q} run
-- the refusing state IS the renamed source state: pull the ban set back pointwise.
... | s , Q′ , Qreach , rn , inj₁ refl
      with f {s} {banSrc tg B} (inj₁ (Q′ , Qreach , refuses-ren-elim tg ref))
...     | inj₁ (P′ , Preach , ref′) = inj₁ (ren-fail-intro tg Preach rn ref′)
...     | inj₂ dP                    = inj₂ (ren-div-intro P rn dP)
-- the run ticked and sits in `deadlock`, which refuses EVERYTHING on both sides — no
-- pullback needed, `deadlock-refuses` supplies the source refusal outright.
renameInv-mono-⊇F⊥ {inv = inv} tg {P} {Q} f d {t} {B} (inj₁ (W , run , ref))
    | s , Q′ , Qreach , rn , inj₂ (refl , refl)
      with f {s} {banSrc tg B} (inj₁ (Q′ , Qreach , deadlock-refuses))
...     | inj₁ (P′ , Preach , ref′) = inj₁ (ren-fail-intro tg Preach rn ref′)
...     | inj₂ dP                    = inj₂ (ren-div-intro P rn dP)
-- a divergence of the renamed impl: that is the `⊇D` half.
renameInv-mono-⊇F⊥ {inv = inv} tg {P} {Q} f d (inj₂ dv) =
  inj₂ (renameInv-mono-⊇D {inv = inv} d dv)

-- RENAMING IS A ⊑FD-PRECONGRUENCE for a tight `inv`.
renameInv-mono-⊑FD : ∀ {inv} (tg : RenTight inv) {P Q : PTree E (ExtI E) Rr}
                   → P ⊑FD Q → (P ⟦ inv ⟧ⁱ) ⊑FD (Q ⟦ inv ⟧ⁱ)
renameInv-mono-⊑FD {inv = inv} tg (f , d) =
  renameInv-mono-⊇F⊥ tg f d , renameInv-mono-⊇D {inv = inv} d

-------------------------------------------------------------------------------------
-- PART 6 : `renameMap` — the side condition DISCHARGES.
--
-- At the same alphabet `CSP.Rename` is instantiated with `ι = id`, `ι⁻¹ = just`, so
-- `ι-vis-inv (A , e) b = just ((A , e) , b)`: the identity partial inverse, trivially
-- tight (`fwd = id`, and `inv-fwd` is `just`-injectivity).  So `renameMap`'s laws are
-- UNCONDITIONAL at every level.
-------------------------------------------------------------------------------------

-- `ι-vis-inv` is tight, with the identity as its forward section.
ι-vis-inv-tight : RenTight ι-vis-inv
ι-vis-inv-tight .fwd     ce                  = ce
ι-vis-inv-tight .fwd-inv ((A , e) , a)      = refl
ι-vis-inv-tight .inv-fwd ((A , e) , a) ce′ eq = just-injective eq

-- `renameMap` is ⊇D-monotone (a `renameInv` instance).
renameMap-mono-⊇D : {P Q : PTree E (ExtI E) Rr} → P ⊇D Q → renameMap P ⊇D renameMap Q
renameMap-mono-⊇D = renameInv-mono-⊇D {inv = ι-vis-inv}

-- `renameMap` is ⊇F⊥-monotone, unconditionally.
renameMap-mono-⊇F⊥ : {P Q : PTree E (ExtI E) Rr}
                   → P ⊇F⊥ Q → P ⊇D Q → renameMap P ⊇F⊥ renameMap Q
renameMap-mono-⊇F⊥ = renameInv-mono-⊇F⊥ ι-vis-inv-tight

-- `renameMap` IS A ⊑FD-PRECONGRUENCE, unconditionally.
renameMap-mono-⊑FD : {P Q : PTree E (ExtI E) Rr} → P ⊑FD Q → renameMap P ⊑FD renameMap Q
renameMap-mono-⊑FD = renameInv-mono-⊑FD ι-vis-inv-tight

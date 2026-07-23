{-# OPTIONS --guardedness #-}

------------------------------------------------------------
-- WTrace ↪ Trace layer bridge (campaign milestone M0).
--
-- `⊨-DRWB-invariantᴿ→` (Semantics.LTL.WBisimInvariantR) concludes on the
-- WTrace layer (`Semantics.LTL.WTrace._⊨ᵂ_`), but the FourNode liveness
-- target `BlockLiveness⁺` is stated on the coinductive-Trace layer
-- (`Semantics.LTL.Traces_Based._⊨_` / `◇ᵗ` / `□ᵗ`).  The two layers share
-- the SAME visible step relation (`═[ ev e ]═►`, from WeakBisim) and differ
-- ONLY in terminators: a `Trace` `done`/`stuck` is immediate, a `WTrace`
-- `done`/`stuck` allows a `─[τ*]─►` prefix.  Hence every `Trace` embeds into
-- a `WTrace` by choosing `τ*-refl`, and satisfaction transfers along it in
-- the direction `⊨ᵂ ⇒ ⊨` — exactly the direction the M5 endgame needs.
--
-- Generic (model-agnostic): parametric in E, I, R, φ — no FourNode content.
-- This is the binding content of spike-report §3 (`Trace↪WTrace`,
-- `frame-agree`, `⊨ᵂ⇒⊨`), plus two constructive convenience wrappers for the
-- M5-consumed hypothesis/response formula shapes.
------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process_Trees using (PTree)

module Semantics.LTL.TraceBridge
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I} using (τ*-refl)

-- The Trace layer: qualified `T` for the pieces whose names clash with the
-- WTrace layer (Trace, frameOf, tail, drop, ⟦_⟧, _⊨_, constructors).
import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I} as T
-- The non-clashing syntax, derived operators, and §6.1 equivalences we reuse.
open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I}
  using ( Frame; LTLᵗ; ⊤'; atom; ¬_; _∧_; X_; _U_
        ; F_; G_; _∨_; □ᵗ; ◇ᵗ; F⇒◇ᵗ; □ᵗ⇒⟦G⟧⁺; ⟦G⟧⁺⇒⟦G⟧ )

-- The WTrace layer: qualified `W`.
import Semantics.LTL.WTrace {ℓ} {ℓe} {ℓi} {E} {I} as W

------------------------------------------------------------
-- §1  The embedding  Trace ↪ WTrace  (spike-report §3)
------------------------------------------------------------

-- Forward declarations (avoid a `mutual` block per repo convention).
Trace↪WTrace  : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
              → T.Trace R t → W.WTrace R t
∞Trace↪WTrace : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
              → T.∞Trace R t → W.∞WTrace R t

-- Embed a Trace into a WTrace: keep visible steps verbatim (same
-- `═[ ev e ]═►` transition), and give each immediate terminator the empty
-- `τ*-refl` prefix a WTrace terminator allows.
Trace↪WTrace (T.step x tr) = W.step x (∞Trace↪WTrace tr)
Trace↪WTrace (T.done eq)   = W.done τ*-refl eq
Trace↪WTrace (T.stuck st)  = W.stuck τ*-refl st
Trace↪WTrace (T.div dv)    = W.div dv

-- Coinductive tail of the embedding (guarded corecursion under `W.step`).
W.force (∞Trace↪WTrace tr) = Trace↪WTrace (T.force tr)

-- Frame-observation agreement: the embedded WTrace exposes the SAME frame as
-- the source Trace at the head (spike-report §3 `frame-agree`).  Refl in each
-- case because both layers read the same state/event/return from the head.
frame-agree : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} (tr : T.Trace R t)
            → W.frameOf (Trace↪WTrace tr) ≡ T.frameOf tr
frame-agree (T.step x tr) = refl
frame-agree (T.done eq)   = refl
frame-agree (T.stuck st)  = refl
frame-agree (T.div dv)    = refl

------------------------------------------------------------
-- §2  Semantic agreement of ⟦_⟧ along the embedding
--
-- Proved in both directions (the `¬` case needs the converse), by induction
-- on the formula.  `drop-sem-*` handle the `U` case: they recurse on the
-- drop index `n`, using that `W.tail (Trace↪WTrace tr) = Trace↪WTrace
-- (T.tail tr)` holds definitionally once `tr` is matched to a constructor,
-- so no propositional `drop`-commutation lemma (and no subst) is needed.
------------------------------------------------------------

-- Forward declarations of the four mutually-recursive agreement functions.
sem-fwd : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
            (φ : LTLᵗ ℓa R) (tr : T.Trace R t)
        → W.⟦ φ ⟧ᵂ (Trace↪WTrace tr) → T.⟦ φ ⟧ tr
sem-bwd : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
            (φ : LTLᵗ ℓa R) (tr : T.Trace R t)
        → T.⟦ φ ⟧ tr → W.⟦ φ ⟧ᵂ (Trace↪WTrace tr)
drop-sem-fwd : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
                 (φ : LTLᵗ ℓa R) (n : ℕ) (tr : T.Trace R t)
             → W.⟦ φ ⟧ᵂ (W.drop n (Trace↪WTrace tr)) → T.⟦ φ ⟧ (T.drop n tr)
drop-sem-bwd : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
                 (φ : LTLᵗ ℓa R) (n : ℕ) (tr : T.Trace R t)
             → T.⟦ φ ⟧ (T.drop n tr) → W.⟦ φ ⟧ᵂ (W.drop n (Trace↪WTrace tr))

-- ⟦ φ ⟧ᵂ (embed tr) ⇒ ⟦ φ ⟧ tr.
sem-fwd ⊤'        tr h            = h
sem-fwd (atom P)  tr h            rewrite sym (frame-agree tr) = h
sem-fwd (¬ φ)     tr h            = λ p → h (sem-bwd φ tr p)
sem-fwd (φ ∧ ψ)   tr (a , b)      = sem-fwd φ tr a , sem-fwd ψ tr b
sem-fwd (X φ) (T.step x tr) h     = sem-fwd φ (T.force tr) h
sem-fwd (X φ) (T.done eq)   h     = sem-fwd φ (T.done eq) h
sem-fwd (X φ) (T.stuck st)  h     = sem-fwd φ (T.stuck st) h
sem-fwd (X φ) (T.div dv)    h     = sem-fwd φ (T.div dv) h
sem-fwd (φ U ψ) tr (n , q , bef)  =
  n , drop-sem-fwd ψ n tr q , λ m m<n → drop-sem-fwd φ m tr (bef m m<n)

-- ⟦ φ ⟧ tr ⇒ ⟦ φ ⟧ᵂ (embed tr).
sem-bwd ⊤'        tr h            = h
sem-bwd (atom P)  tr h            rewrite frame-agree tr = h
sem-bwd (¬ φ)     tr h            = λ p → h (sem-fwd φ tr p)
sem-bwd (φ ∧ ψ)   tr (a , b)      = sem-bwd φ tr a , sem-bwd ψ tr b
sem-bwd (X φ) (T.step x tr) h     = sem-bwd φ (T.force tr) h
sem-bwd (X φ) (T.done eq)   h     = sem-bwd φ (T.done eq) h
sem-bwd (X φ) (T.stuck st)  h     = sem-bwd φ (T.stuck st) h
sem-bwd (X φ) (T.div dv)    h     = sem-bwd φ (T.div dv) h
sem-bwd (φ U ψ) tr (n , q , bef)  =
  n , drop-sem-bwd ψ n tr q , λ m m<n → drop-sem-bwd φ m tr (bef m m<n)

-- ⟦ φ ⟧ᵂ (drop n (embed tr)) ⇒ ⟦ φ ⟧ (drop n tr); recursion on n.
drop-sem-fwd φ zero    tr h            = sem-fwd φ tr h
drop-sem-fwd φ (suc n) (T.step x tr) h = drop-sem-fwd φ n (T.force tr) h
drop-sem-fwd φ (suc n) (T.done eq)   h = drop-sem-fwd φ n (T.done eq) h
drop-sem-fwd φ (suc n) (T.stuck st)  h = drop-sem-fwd φ n (T.stuck st) h
drop-sem-fwd φ (suc n) (T.div dv)    h = drop-sem-fwd φ n (T.div dv) h

-- ⟦ φ ⟧ (drop n tr) ⇒ ⟦ φ ⟧ᵂ (drop n (embed tr)); recursion on n.
drop-sem-bwd φ zero    tr h            = sem-bwd φ tr h
drop-sem-bwd φ (suc n) (T.step x tr) h = drop-sem-bwd φ n (T.force tr) h
drop-sem-bwd φ (suc n) (T.done eq)   h = drop-sem-bwd φ n (T.done eq) h
drop-sem-bwd φ (suc n) (T.stuck st)  h = drop-sem-bwd φ n (T.stuck st) h
drop-sem-bwd φ (suc n) (T.div dv)    h = drop-sem-bwd φ n (T.div dv) h

------------------------------------------------------------
-- §3  The corollary  ⊨ᵂ ⇒ ⊨  (spike-report §3; M5 consumes this)
------------------------------------------------------------

-- Every Trace-world satisfaction follows from WTrace-world satisfaction:
-- run the hypothesis on the embedded trace, then descend with `sem-fwd`.
-- This is the bridge the M5 endgame applies right after
-- `⊨-DRWB-invariantᴿ→` lands `systemBroken ⊨ᵂ φ`.
⊨ᵂ⇒⊨ : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R} {φ : LTLᵗ ℓa R}
      → t W.⊨ᵂ φ → t T.⊨ φ
⊨ᵂ⇒⊨ {φ = φ} h tr = sem-fwd φ tr (h (Trace↪WTrace tr))

------------------------------------------------------------
-- §4  Constructive convenience wrappers for the M5 endgame shapes
--
-- These do NOT cross the classical `⇒`/`G` (`¬F¬`) encodings — those
-- eliminations stay with M5 via the already-certified classical postulates
-- of Traces_Based §6.1 (`⟦G⟧⇒⟦G⟧⁺`, `¬G⇒F¬`).  What is offered here is only
-- the postulate-free glue for the two `BlockLiveness⁺` boundary shapes.
------------------------------------------------------------

-- Hypothesis side.  `BlockLiveness⁺` supplies `□ᵗ ψ₁ tr ⊎ □ᵗ ψ₂ tr`; the
-- classical `respondsAtoD` antecedent `confined` is `(G ψ₁) ∨ (G ψ₂)`.  This
-- packages the former into the latter (constructively: `□ᵗ⇒⟦G⟧⁺` then the
-- constructive `⟦G⟧⁺⇒⟦G⟧`, then the ∨ injection).
□ᵗ-⊎⇒∨G : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
            {ψ₁ ψ₂ : LTLᵗ ℓa R} {tr : T.Trace R t}
          → □ᵗ ψ₁ tr ⊎ □ᵗ ψ₂ tr → T.⟦ (G ψ₁) ∨ (G ψ₂) ⟧ tr
□ᵗ-⊎⇒∨G {ψ₁ = ψ₁} (inj₁ b) (nG₁ , _)   = nG₁ (⟦G⟧⁺⇒⟦G⟧ {φ = ψ₁} (□ᵗ⇒⟦G⟧⁺ {φ = ψ₁} b))
□ᵗ-⊎⇒∨G {ψ₂ = ψ₂} (inj₂ b) (_   , nG₂) = nG₂ (⟦G⟧⁺⇒⟦G⟧ {φ = ψ₂} (□ᵗ⇒⟦G⟧⁺ {φ = ψ₂} b))

-- Response side.  `BlockLiveness⁺` wants, at every suffix, `⟦ φ ⟧ → ◇ᵗ ρ`.
-- Given the (pointwise, per-`drop`) `⟦ φ ⟧ → ⟦ F ρ ⟧` that M5's progress
-- walk produces, this turns each `F` into the positive `◇ᵗ` via `F⇒◇ᵗ`.
Fpt⇒◇ᵗpt : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
             {φ ρ : LTLᵗ ℓa R} {tr : T.Trace R t}
           → (∀ n → T.⟦ φ ⟧ (T.drop n tr) → T.⟦ F ρ ⟧ (T.drop n tr))
           → (∀ n → T.⟦ φ ⟧ (T.drop n tr) → ◇ᵗ ρ (T.drop n tr))
Fpt⇒◇ᵗpt f n p = F⇒◇ᵗ (f n p)

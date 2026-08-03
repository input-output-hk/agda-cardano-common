{-# OPTIONS --guardedness #-}

-- Stability helpers for the pure-react LTS: what a STABLE state (a `react` node whose
-- τ-branch map is everywhere `nothing`) can and cannot do.
--
-- These were originally part of `Semantics.DRImpliesFD`, but that module carries the
-- one classical postulate (`¬-divergent→normal`).  They are split out here so that
-- postulate-free clients can use them without importing the postulate; `DRImpliesFD`
-- re-exports everything below, so its existing consumers are unaffected.

open import Level using (Level; Lift; lift; lower; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module Semantics.Stability
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}

-------------------------------------------------------------------------------------
-- Stability vs. steps.
-- A `with` on `isStable t` only reduces once `PTree.force t` is concrete, so each
-- helper splits the force AND lists `isStable t` (and the force-equality) in the
-- `with` so the predicate computes in every branch.
-------------------------------------------------------------------------------------

nothing≢just : ∀ {ℓa} {A : Set ℓa} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

-- a stable state's force cannot be `sil`
stable-not-sil : ∀ {ℓr} {R : Set ℓr} {t u : PTree E I R}
               → isStable t → PTree.force t ≡ sil u → ⊥
stable-not-sil {t = t} st eq with PTree.force t | st | eq
... | ret _    | _       | ()
... | sil _    | lift ()  | _
... | react _ _ | _       | ()

-- a stable state's force cannot be `ret` either (ret is not stable)
stable-not-ret : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} {r : R}
               → isStable t → PTree.force t ≡ ret r → ⊥
stable-not-ret {t = t} st eq with PTree.force t | st | eq
... | ret _    | lift ()  | _
... | sil _    | _        | ()
... | react _ _ | _        | ()

-- a stable state's τ-branch continuation is everywhere `nothing`
stable-react-τc : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                 {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))}
                 {τc : (i  : AnyTypes I) → ContinueType i  (Maybe (PTree E I R))}
               → isStable t → PTree.force t ≡ react v τc
               → ∀ (i : AnyTypes I) (a : proj₁ i) → τc i a ≡ nothing
stable-react-τc {t = t} st eq with PTree.force t | st | eq
... | ret _     | _    | ()
... | sil _     | _    | ()
... | react _ _  | stf  | refl = stf

-- hence a stable state performs no τ-step at all
stable-no-τ : ∀ {ℓr} {R : Set ℓr} {t u : PTree E I R}
            → isStable t → t ─[ τ ]─► u → ⊥
stable-no-τ {t = t} st (sSil eq) = stable-not-sil {t = t} st eq
stable-no-τ {t = t} st (sTau {τc = τc} {i = i} {a = a} eq br) =
  nothing≢just (trans (sym (stable-react-τc {t = t} st eq i a)) br)

-- … so a stable state cannot diverge …
stable→¬div : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
            → isStable t → ¬ Diverges t
stable→¬div st d = stable-no-τ st (d .Diverges.step)

-- … and a τ*-run out of a stable state is necessarily empty
stable→τ*-refl : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R}
               → isStable t → t ─[τ*]─► t′ → t′ ≡ t
stable→τ*-refl st τ*-refl        = refl
stable→τ*-refl st (τ*-step s _)  = ⊥-elim (stable-no-τ st s)

-------------------------------------------------------------------------------------
-- Introduction / elimination / transport for `isStable`.
--
-- These used to be copied per-operator across the FD layer (`mk-stable` alone had
-- FOUR identical copies, in `ThrowFD`, `InterruptFD`, `ParallelRefusals` and
-- `ExtChoiceFD`).  They are generic in `E`/`I` — nothing below mentions a CSP
-- operator — so they belong here, next to `stable-not-sil` / `stable-not-ret`.
-- The old homes keep their names as thin aliases so no client breaks.
-------------------------------------------------------------------------------------

-- INTRO: build stability from "the τ-branch map of `force t` is everywhere `nothing`"
-- (the constructive converse of `stable-react-τc`).
mk-stable : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
            {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))}
            {τc : (i  : AnyTypes I) → ContinueType i  (Maybe (PTree E I R))}
          → PTree.force t ≡ react v τc → (∀ i a → τc i a ≡ nothing) → isStable t
mk-stable {t = t} eqf h with PTree.force t | eqf
... | react _ _ | refl = h

-- ELIM (Σ-form): a stable state forces to a `react` node whose τ-map is everywhere
-- `nothing`; the visible map and the τ-map are returned as witnesses.
stable→react : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → isStable t
             → Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))) ]
               Σ[ τc ∈ ((i : AnyTypes I) → ContinueType i (Maybe (PTree E I R))) ]
                 (PTree.force t ≡ react v τc × (∀ i a → τc i a ≡ nothing))
stable→react {t = t} st with PTree.force t | st
... | ret _      | lift ()
... | sil _      | lift ()
... | react v τc | h = v , τc , refl , h

-- `isStable` reads only `force`, so it transports FORWARD along a force equality.
isStable-force-eq : ∀ {ℓr} {R : Set ℓr} {t u : PTree E I R}
                  → PTree.force t ≡ PTree.force u → isStable t → isStable u
isStable-force-eq {t = t} {u = u} eq st with PTree.force t | st
... | ret _      | lift ()
... | sil _      | lift ()
... | react v τc | stf = mk-stable {t = u} (sym eq) stf

-- the same transport in the BACKWARD orientation (the shape the bind / iterate
-- proofs use: an equal force pushes stability of the RIGHT tree onto the left).
stable-force-eq : ∀ {ℓr} {R : Set ℓr} {p q : PTree E I R}
                → PTree.force p ≡ PTree.force q → isStable q → isStable p
stable-force-eq {p = p} {q = q} eq st = isStable-force-eq {t = q} {u = p} (sym eq) st

-- INTRO from the LTS side: a `react`-forced state that performs no τ at all is
-- stable (the converse of `stable-no-τ`; the `react` hypothesis is essential —
-- `ret r` performs no τ either, yet is not stable).
react-no-τ→stable : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                    {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))}
                    {τc : (i  : AnyTypes I) → ContinueType i  (Maybe (PTree E I R))}
                  → PTree.force t ≡ react v τc
                  → (∀ {t′ : PTree E I R} → t ─[ τ ]─► t′ → ⊥) → isStable t
react-no-τ→stable {t = t} {τc = τc} eqf noτ = mk-stable {t = t} eqf go
  where
    -- any `just` in the τ-map would BE a τ-step, contradicting `noτ`
    go : ∀ i a → τc i a ≡ nothing
    go i a with τc i a in eq
    ... | nothing = refl
    ... | just t′ = ⊥-elim (noτ (sTau {p = t} eqf eq))

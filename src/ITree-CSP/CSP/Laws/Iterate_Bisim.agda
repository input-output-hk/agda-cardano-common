{-
  Coinductive weak-simulation refactor for `loop-mono-⊑F⊥` —
  in-progress skeleton.

  See `docs/superpowers/plans/2026-05-19-loop-mono-bisim-refactor.md`
  for the full design.
-}

{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _++_; _∷_; []; map)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Function using (case_of_)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences

module CSP.Laws.Iterate_Bisim
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Traces
open Failures
open Event√

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

import CSP.Definitions.Iterate {ℓ} {ℓe} {E} as CSPIter
open CSPIter E-≟

-- Generic iteration (parametric in the tag function `h : A → A ⊎ R`).
-- `genIter inj₁ body a ≡ genIter h body a` and
-- `genStep inj₁ body a ≡ body a >>= λ a' → Ret (h a')` definitionally.
open import CSP.Laws.Iterate_Gen {ℓ} {ℓe} {E} E-≟ using (genStep; genIter; whileTag)

-- Public helpers from Iterate.agda used for construct-on-X.
-- Iterate_Bisim is downstream of Iterate (Iterate doesn't depend on
-- this module yet), so this import is acyclic.
import CSP.Laws.Iterate {ℓ} {ℓe} {E} as CSPIterLaws
open CSPIterLaws E-≟ using
  ( lift-iter-bind-bigstep
  ; lift-iter-bind-bigstep-tick
  ; iter-bind-force-ret-inj₁
  ; iter-bind-force-ret-inj₂
  ; iter-bind-force-sil
  ; iter-bind-force-vis
  ; iter-bind-force-ndbr
  ; iter-bind-force-mix
  ; iter-bind-cont-vis-just
  ; iter-bind-cont-mix-just
  -- Helpers newly un-privatized in Iterate.agda for the bisim refactor:
  ; bind-left-step-lift
  ; Divergent-bind-left
  ; iter-bind-left-step-lift
  ; Divergent-iter-bind-left
  ; deadlock-ref
  ; tick-bigstep-lands-at-deadlock
  ; Divergent-deadlock-absurd
  ; prefix-tick-split
  ; Divergent-bind-pure-ret-inv
  )

-- Bind helpers (only what's needed for construct-on-X bodies; avoiding
-- the `bigstep-concat` name conflict with the local private one).
import CSP.Laws.Bind {ℓ} {ℓe} {E} as CSPBind
open CSPBind E-≟ using
  ( lift-bind-bigstep-tick
  ; bind-force-ret
  ; lift-bind-bigstep
  ; lift-bind-step-ev
  ; vis-isStable
  ; bind-force-vis
  )

-- `genStep`/`genIter` are imported from CSP.Laws.Iterate_Gen above.
-- `genStep h body a ≡ body a >>= λ a' → Ret (h a')` and
-- `genIter h body a ≡ iter (genStep h body) a` definitionally; with
-- `h := inj₁` these collapse to the former `loopStep body`/`loop body a`.

-----------------------------------------------------------------------------------------
-- Loop-Sim : one-sided weak simulation oriented for failures⊥
-- refinement.  `Loop-Sim P Q` ⇒ `P ⊑F⊥ Q` (refinement direction:
-- failures⊥(Q) ⊆ failures⊥(P), i.e. P has more behaviors).
--
-- `on-vis` ranges over `e : Event√ E R`, so it covers both visible
-- events (`evl _`) and the `√ x` tick event (via `sRet`).
-- Tick-shaped refusals (`ref-tick`) are derived from `on-vis` at
-- `e = √ x` in `loop-sim→⊑F⊥`.
-----------------------------------------------------------------------------------------

record Loop-Sim {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                (P Q : ITree E (ExtI I) R)
              : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB) where
  coinductive
  field
    -- Every step labelled `ev e` of Q is weakly matched by P, OR P
    -- diverges (CSP divergence-strict closure: a divergent prefix
    -- absorbs the failure-witness for the extended trace).
    on-vis : ∀ {e : Event√ E R} {Q'}
           → Q ─[ ev e ]─► Q'
           → ( Σ[ P' ∈ ITree E (ExtI I) R ]
               ( P ═[ ev e ]═► P'
               × Loop-Sim {ℓB = ℓB} P' Q' ) )
           ⊎ Divergent P

    -- Every τ-step of Q is weakly matched by P, OR P diverges.
    on-tau : ∀ {Q'} → Q ─[ τ ]─► Q'
           → ( Σ[ P' ∈ ITree E (ExtI I) R ]
               ( P ─[τ*]─► P'
               × Loop-Sim {ℓB = ℓB} P' Q' ) )
           ⊎ Divergent P

    -- Stable-shape refusal preservation, with a divergence escape.
    -- Given a stable refusing Q-state, P either τ*-progresses to a
    -- stable refusing state with the same no-ev predicate, OR
    -- diverges.  Argument order on `no-ev` matches `ref-stable`'s.
    on-stable-ref : ∀ {B : Event√ E R → Set ℓB}
                  → isStable Q
                  → (∀ (e : Event√ E R) → B e → ∀ {Q' : ITree E (ExtI I) R}
                       → ¬ Q ─[ ev e ]─► Q')
                  → (Σ[ P' ∈ ITree E (ExtI I) R ]
                      ( P ─[τ*]─► P'
                      × isStable P'
                      × (∀ (e : Event√ E R) → B e → ∀ {P'' : ITree E (ExtI I) R}
                           → ¬ P' ─[ ev e ]─► P'')))
                  ⊎ Divergent P

    -- Divergence preservation: this field has no escape because the
    -- conclusion `Divergent P` IS the divergence-side fact.
    on-div : Divergent Q → Divergent P

-----------------------------------------------------------------------------------------
-- Tail-Sim : body-tail weak simulation for mid-iteration matching.
--
-- Tail-Sim X Y relates body-tail ITrees X, Y : ITree E (ExtI I) (A ⊎ R).
-- Lifted to Loop-Sim on iter-bind states via `tail-sim→loop-sim` below.
--
-- Constructed from bF⊑/bD⊑/sim-rec via `bF⊑+bD⊑→Tail-Sim` (also below) at
-- the initial body-tails (body a) (body' a).
-----------------------------------------------------------------------------------------
record Tail-Sim {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                {body body' : HKTree E (ExtI I) A}
                {h : A → A ⊎ R}
                (X Y : ITree E (ExtI I) (A ⊎ R))
              : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB) where
  coinductive
  field
    -- Y fires ev e to Y' → X bigsteps ev e + Tail-Sim continuation, or X diverges.
    on-vis : ∀ {e : Event√ E (A ⊎ R)} {Y'}
           → Y ─[ ev e ]─► Y'
           → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
               ( X ═[ ev e ]═► X'
               × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
           ⊎ Divergent X

    -- Y τ-steps to Y' → X τ*-progresses to matching X', or X diverges.
    on-tau : ∀ {Y'} → Y ─[ τ ]─► Y'
           → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
               ( X ─[τ*]─► X'
               × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
           ⊎ Divergent X

    -- Stable refusal preservation, mirrors Loop-Sim.on-stable-ref.
    on-stable-ref : ∀ {B : Event√ E (A ⊎ R) → Set ℓB}
                  → isStable Y
                  → (∀ (e : Event√ E (A ⊎ R)) → B e → ∀ {Y' : ITree E (ExtI I) (A ⊎ R)}
                       → ¬ Y ─[ ev e ]─► Y')
                  → (Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                      ( X ─[τ*]─► X'
                      × isStable X'
                      × (∀ (e : Event√ E (A ⊎ R)) → B e → ∀ {X'' : ITree E (ExtI I) (A ⊎ R)}
                           → ¬ X' ─[ ev e ]─► X'')))
                  ⊎ Divergent X

    on-div : Divergent Y → Divergent X

    -- Iteration boundary: Y returns inj₁ a-next → X τ*-progresses to
    -- some matching ret(inj₁ a'-next), and the next iter cycle is
    -- related by Loop-Sim.  Carrying the Loop-Sim recursion data here
    -- (rather than via sim-rec at the lift layer) keeps tail-sim→loop-sim
    -- recursion-free: the boundary's "post-cycle behaviour" is frozen
    -- inside Tail-Sim itself.  The a'-next may differ from a-next (the
    -- spec is permissive; concrete instances may produce a-next = a'-next).
    on-ret-inj₁ : ∀ {a-next : A}
                → ITree.force Y ≡ ret (inj₁ a-next)
                → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
                    ( X ─[τ*]─► X'
                    × ITree.force X' ≡ ret (inj₁ a'-next)
                    × Loop-Sim {ℓB = ℓB} (genIter h body a'-next)
                                          (genIter h body' a-next) ) )
                ⊎ Divergent X

    -- Exit boundary: Y returns inj₂ r → X τ*-progresses to inj₂ r (same r).
    on-ret-inj₂ : ∀ {r : R}
                → ITree.force Y ≡ ret (inj₂ r)
                → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                    ( X ─[τ*]─► X'
                    × ITree.force X' ≡ ret (inj₂ r) ) )
                ⊎ Divergent X

-----------------------------------------------------------------------------------------
-- Small infrastructure for trace-walking
-----------------------------------------------------------------------------------------

private
  -- τ* chain → bigstep at trace [].
  τ*-to-bigstep : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                   {P P' : ITree E (ExtI I) R}
                → P ─[τ*]─► P' → P ═⟨ [] ⟩═► P'
  τ*-to-bigstep τ*-zero            = bNil
  τ*-to-bigstep (τ*-step step rest) = bTau step (τ*-to-bigstep rest)

  -- iter-bind-left-τ*: lift a τ*-chain on the input of iter-bind.
  -- Mirrors iter-bind-left-step-lift, folded across the chain.
  iter-bind-left-τ*
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        {Q Q' : ITree E (ExtI I) (A ⊎ R)}
        (k : A → ITree E (ExtI I) (A ⊎ R))
      → Q ─[τ*]─► Q'
      → iter-bind Q k ─[τ*]─► iter-bind Q' k
  iter-bind-left-τ* k τ*-zero            = τ*-zero
  iter-bind-left-τ* k (τ*-step s rest)   =
    τ*-step (iter-bind-left-step-lift _ k s) (iter-bind-left-τ* k rest)

  -- τ*-then-step: snoc a single τ-step onto the end of a τ*-chain.
  τ*-then-step
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {t t' t'' : ITree E (ExtI I) R}
      → t ─[τ*]─► t' → t' ─[ τ ]─► t'' → t ─[τ*]─► t''
  τ*-then-step τ*-zero            s = τ*-step s τ*-zero
  τ*-then-step (τ*-step step rest) s = τ*-step step (τ*-then-step rest s)

  -- Divergent-prepend-τ-step: prepend a single τ-step to a divergence.
  -- (Generalizes step-sil-diverges: works for any τ-step constructor.)
  Divergent-prepend-τ-step
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {t t' : ITree E (ExtI I) R}
      → t ─[ τ ]─► t' → Divergent t' → Divergent t
  Divergent-prepend-τ-step {t' = t'} st d .Divergent.next    = t'
  Divergent-prepend-τ-step             st d .Divergent.step    = st
  Divergent-prepend-τ-step             st d .Divergent.diverge = d

  -- Divergent-prepend-τ*: prepend a τ*-chain to a divergence.
  Divergent-prepend-τ*
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {t t' : ITree E (ExtI I) R}
      → t ─[τ*]─► t' → Divergent t' → Divergent t
  Divergent-prepend-τ* τ*-zero            d = d
  Divergent-prepend-τ* (τ*-step st rest)  d =
    Divergent-prepend-τ-step st (Divergent-prepend-τ* rest d)

  -- Second-component injectivity of the `mix` NodeKind constructor.
  mix-snd-injective
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {f g : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
        {Qt Qt' : ITree E (ExtI I) R}
      → _≡_ {A = NodeKind E (ExtI I) R} (mix f Qt) (mix g Qt') → Qt ≡ Qt'
  mix-snd-injective refl = refl


  -- iter-bind-force-ret-inv: ITree.force (iter-bind Q k) ≡ ret r forces
  -- Q.force ≡ ret (inj₂ r).  Inverse of iter-bind-force-ret-inj₂.
  iter-bind-force-ret-inv
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (Q : ITree E (ExtI I) (A ⊎ R)) {r : R}
        (k : A → ITree E (ExtI I) (A ⊎ R))
      → ITree.force (iter-bind Q k) ≡ ret r
      → ITree.force Q ≡ ret (inj₂ r)
  iter-bind-force-ret-inv Q k eq with Q .force
  ... | ret (inj₂ _) = case eq of λ { refl → refl }
  ... | ret (inj₁ _) = case eq of λ ()
  ... | sil _        = case eq of λ ()
  ... | vis _        = case eq of λ ()
  ... | ndbr _ _ _ _ = case eq of λ ()
  ... | mix _ _      = case eq of λ ()

  -- iter-bind-force-sil-inv: ITree.force (iter-bind Q k) ≡ sil c' is
  -- produced by exactly two iter-bind reductions: Q.force ≡ sil cY
  -- (with c' ≡ iter-bind cY k), OR Q.force ≡ ret (inj₁ a-next) (with
  -- c' ≡ iter k a-next).  Inverse of iter-bind-force-sil /
  -- iter-bind-force-ret-inj₁.
  iter-bind-force-sil-inv
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (Q : ITree E (ExtI I) (A ⊎ R)) {c' : ITree E (ExtI I) R}
        (k : A → ITree E (ExtI I) (A ⊎ R))
      → ITree.force (iter-bind Q k) ≡ sil c'
      → ( Σ[ cY ∈ ITree E (ExtI I) (A ⊎ R) ]
            ( ITree.force Q ≡ sil cY × c' ≡ iter-bind cY k ) )
      ⊎ ( Σ[ a-next ∈ A ]
            ( ITree.force Q ≡ ret (inj₁ a-next) × c' ≡ iter k a-next ) )
  iter-bind-force-sil-inv Q k eq with Q .force
  ... | sil cY       = inj₁ (cY , refl , (case eq of λ { refl → refl }))
  ... | ret (inj₁ a) = inj₂ (a  , refl , (case eq of λ { refl → refl }))
  ... | ret (inj₂ _) = case eq of λ ()
  ... | vis _        = case eq of λ ()
  ... | ndbr _ _ _ _ = case eq of λ ()
  ... | mix _ _      = case eq of λ ()

  -- iter-bind-force-vis-inv: ITree.force (iter-bind Q k) ≡ vis f' forces
  -- Q.force ≡ vis fY with f' ≡ iter-bind-cont-vis k fY.
  iter-bind-force-vis-inv
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (Q : ITree E (ExtI I) (A ⊎ R))
        {f' : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
        (k : A → ITree E (ExtI I) (A ⊎ R))
      → ITree.force (iter-bind Q k) ≡ vis f'
      → Σ[ fY ∈ ((at : AnyTypes E)
                  → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))) ]
          ( ITree.force Q ≡ vis fY
          × f' ≡ iter-bind-cont-vis k fY )
  iter-bind-force-vis-inv Q k eq with Q .force
  ... | vis fY       = fY , refl , (case eq of λ { refl → refl })
  ... | ret (inj₁ _) = case eq of λ ()
  ... | ret (inj₂ _) = case eq of λ ()
  ... | sil _        = case eq of λ ()
  ... | ndbr _ _ _ _ = case eq of λ ()
  ... | mix _ _      = case eq of λ ()

  -- iter-bind-force-mix-inv: ITree.force (iter-bind Q k) ≡ mix f' Qt'
  -- forces Q.force ≡ mix fY QtY with f' ≡ iter-bind-cont-mix k fY and
  -- Qt' ≡ iter-bind QtY k.
  iter-bind-force-mix-inv
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (Q : ITree E (ExtI I) (A ⊎ R))
        {f' : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
        {Qt' : ITree E (ExtI I) R}
        (k : A → ITree E (ExtI I) (A ⊎ R))
      → ITree.force (iter-bind Q k) ≡ mix f' Qt'
      → Σ[ fY ∈ ((at : AnyTypes E)
                  → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))) ]
        Σ[ QtY ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( ITree.force Q ≡ mix fY QtY
          × f' ≡ iter-bind-cont-mix k fY
          × Qt' ≡ iter-bind QtY k )
  iter-bind-force-mix-inv Q k eq with Q .force
  ... | mix fY QtY   = fY , QtY , refl ,
                       (case eq of λ { refl → refl }) ,
                       (case eq of λ { refl → refl })
  ... | ret (inj₁ _) = case eq of λ ()
  ... | ret (inj₂ _) = case eq of λ ()
  ... | sil _        = case eq of λ ()
  ... | vis _        = case eq of λ ()
  ... | ndbr _ _ _ _ = case eq of λ ()

  -- isStable-with-vis-force: a tree whose force is vis is stable.
  -- (isStable is defined by case on .force; the vis case yields ⊤.)
  isStable-with-vis-force
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        (t : ITree E I R)
        {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
      → ITree.force t ≡ vis f
      → isStable t
  isStable-with-vis-force t eq with t .force
  ... | vis _        = tt₀
  ... | ret _        = case eq of λ ()
  ... | sil _        = case eq of λ ()
  ... | ndbr _ _ _ _ = case eq of λ ()
  ... | mix _ _      = case eq of λ ()

  -- iter-bind-cont-vis-just-fwd: the forward direction of
  -- iter-bind-cont-vis-just-inv.  If `f at a ≡ just c` then
  -- `iter-bind-cont-vis k f at a ≡ just (iter-bind c k)`.
  iter-bind-cont-vis-just-fwd
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (k : A → ITree E (ExtI I) (A ⊎ R))
        (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R))))
        (at : AnyTypes E) (a : proj₁ at)
        {c : ITree E (ExtI I) (A ⊎ R)}
      → f at a ≡ just c
      → iter-bind-cont-vis k f at a ≡ just (iter-bind c k)
  iter-bind-cont-vis-just-fwd k f at a eq with f at a
  ... | just _  = case eq of λ { refl → refl }
  ... | nothing = case eq of λ ()

  -- iter-bind-cont-vis-just-inv: invert the cont-vis continuation.
  iter-bind-cont-vis-just-inv
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (k : A → ITree E (ExtI I) (A ⊎ R))
        (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R))))
        (at : AnyTypes E) (a : proj₁ at)
        {t-iter : ITree E (ExtI I) R}
      → iter-bind-cont-vis k f at a ≡ just t-iter
      → Σ[ c' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( f at a ≡ just c' × t-iter ≡ iter-bind c' k )
  iter-bind-cont-vis-just-inv k f at a eq with f at a
  ... | just c' = c' , refl , (case eq of λ { refl → refl })
  ... | nothing = case eq of λ ()

  -- iter-bind-force-ndbr-inv: ITree.force (iter-bind Q k) ≡ ndbr f' wi
  -- wa wp forces Q.force ≡ ndbr fY wi wa wp-Q with f' ≡ iter-bind-
  -- cont-ndbr k fY.  The wi/wa witness on the iter-bind level is the
  -- same as on Q's level (the cont-ndbr-witness wraps wp transparently).
  iter-bind-force-ndbr-inv
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (Q : ITree E (ExtI I) (A ⊎ R))
        {f' : (ai : AnyTypes (ExtI I))
              → ContinueType ai (Maybe (ITree E (ExtI I) R))}
        {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (f' wi wa)}
        (k : A → ITree E (ExtI I) (A ⊎ R))
      → ITree.force (iter-bind Q k) ≡ ndbr f' wi wa wp
      → Σ[ fY ∈ ((ai : AnyTypes (ExtI I))
                  → ContinueType ai (Maybe (ITree E (ExtI I) (A ⊎ R)))) ]
        Σ[ wp-Q ∈ Is-just (fY wi wa) ]
          ( ITree.force Q ≡ ndbr fY wi wa wp-Q
          × f' ≡ iter-bind-cont-ndbr k fY )
  iter-bind-force-ndbr-inv Q k eq with Q .force | eq
  ... | ndbr fY wi-Q wa-Q wp-Q | refl = fY , wp-Q , refl , refl
  ... | ret (inj₁ _) | ()
  ... | ret (inj₂ _) | ()
  ... | sil _        | ()
  ... | vis _        | ()
  ... | mix _ _      | ()

  -- iter-bind-cont-ndbr-just-inv: invert the cont-ndbr continuation.
  iter-bind-cont-ndbr-just-inv
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (k : A → ITree E (ExtI I) (A ⊎ R))
        (f : (ai : AnyTypes (ExtI I))
             → ContinueType ai (Maybe (ITree E (ExtI I) (A ⊎ R))))
        (ai : AnyTypes (ExtI I)) (a : proj₁ ai)
        {t-iter : ITree E (ExtI I) R}
      → iter-bind-cont-ndbr k f ai a ≡ just t-iter
      → Σ[ c' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( f ai a ≡ just c' × t-iter ≡ iter-bind c' k )
  iter-bind-cont-ndbr-just-inv k f ai a eq with f ai a
  ... | just c' = c' , refl , (case eq of λ { refl → refl })
  ... | nothing = case eq of λ ()

  -- iter-bind-cont-mix-just-inv: invert the cont-mix continuation.
  iter-bind-cont-mix-just-inv
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (k : A → ITree E (ExtI I) (A ⊎ R))
        (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R))))
        (at : AnyTypes E) (a : proj₁ at)
        {t-iter : ITree E (ExtI I) R}
      → iter-bind-cont-mix k f at a ≡ just t-iter
      → Σ[ c' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( f at a ≡ just c' × t-iter ≡ iter-bind c' k )
  iter-bind-cont-mix-just-inv k f at a eq with f at a
  ... | just c' = c' , refl , (case eq of λ { refl → refl })
  ... | nothing = case eq of λ ()

  -- Loop-Sim deadlock deadlock: the terminal sim.  Every transition
  -- from deadlock is structurally impossible (force is vis-shaped with
  -- no live branches), so each field discharges by case analysis.
  loop-sim-deadlock
    : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → Loop-Sim {ℓB = ℓB} {I = I} {R = R} deadlock deadlock
  loop-sim-deadlock {ℓi = ℓi} {ℓr = ℓr} {ℓB = ℓB} {I = I} {R = R} = record
    { on-vis        = no-vis
    ; on-tau        = no-tau
    ; on-stable-ref = stable-ref-deadlock
    ; on-div        = λ d → ⊥-elim (Divergent-deadlock-absurd d)
    }
    where
      no-vis : ∀ {e : Event√ E R} {Q'} → deadlock ─[ ev e ]─► Q' → _
      no-vis (sVis refl eq-j) = case eq-j of λ ()
      no-vis (sMixVis force≡mix _) = case force≡mix of λ ()
      no-vis (sRet force≡ret) = case force≡ret of λ ()

      no-tau : ∀ {Q'} → deadlock ─[ τ ]─► Q' → _
      no-tau step = ⊥-elim (τ-from-force-vis-impossible refl step)

      no-ev-from-deadlock : ∀ {e : Event√ E R} {Q' : ITree E (ExtI I) R}
                           → ¬ deadlock ─[ ev e ]─► Q'
      no-ev-from-deadlock (sVis refl eq-j) = case eq-j of λ ()
      no-ev-from-deadlock (sMixVis force≡mix _) = case force≡mix of λ ()
      no-ev-from-deadlock (sRet force≡ret) = case force≡ret of λ ()

      stable-ref-deadlock : ∀ {B : Event√ E R → Set ℓB}
                          → isStable (deadlock {E = E} {I = ExtI I} {R = R})
                          → (∀ e → B e → ∀ {Q' : ITree E (ExtI I) R}
                               → ¬ deadlock ─[ ev e ]─► Q')
                          → _
      stable-ref-deadlock _ _ =
        inj₁ ( deadlock , τ*-zero , tt₀ , (λ _ _ {_} → no-ev-from-deadlock) )

  -- bigstep-concat (local — same shape as the one in Bind.agda, but
  -- private to this module).
  bigstep-concat
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P P' P'' : ITree E (ExtI I) R} {s1 s2 : List (Event√ E R)}
    → P  ═⟨ s1 ⟩═► P'
    → P' ═⟨ s2 ⟩═► P''
    → P  ═⟨ s1 ++ s2 ⟩═► P''
  bigstep-concat bNil            bs2 = bs2
  bigstep-concat (bTau step rest) bs2 = bTau step (bigstep-concat rest bs2)
  bigstep-concat (bStep step rest) bs2 = bStep step (bigstep-concat rest bs2)

  -- Weak-ev → bigstep at trace `[ e ]`.
  weak-ev-to-bigstep
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P P' : ITree E (ExtI I) R} {e : Event√ E R}
    → P ═[ ev e ]═► P'
    → P ═⟨ e ∷ [] ⟩═► P'
  weak-ev-to-bigstep (weak-ev pre step post) =
      bigstep-concat (τ*-to-bigstep pre)
                     (bStep step (τ*-to-bigstep post))

  -- Trace walker: walk Q's bigstep through `s`, transporting through
  -- the simulation to get either a matching P-bigstep or a P-side
  -- divergence (whichever the simulation escapes to).
  --
  -- Return shape: either (P', P ═⟨ s ⟩═► P', Loop-Sim P' Q') for the
  -- normal walk, or (P', P ═⟨ s' ⟩═► P', Divergent P') for some prefix
  -- s' of s — the walker can short-circuit on `inj₂` from on-vis or
  -- on-tau by stopping mid-trace.
  --
  -- For the consumer `loop-sim→⊑F⊥`: the divergence form yields an
  -- inj₂ output failures⊥ at the (shorter) traversed-prefix trace,
  -- which extends to the full trace `s` by divergence-strict closure
  -- (the divergence witness's `suffix` absorbs the unwalked rest).
  -- WalkResult P Q Q' s: either a matching P-bigstep ending at some
  -- P' related to Q', or a divergence witness at a prefix of `s`.
  -- Q' is the trace's endpoint, fixed by the input Q-bigstep.
  WalkResult : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 (P Q Q' : ITree E (ExtI I) R)
                 (s : List (Event√ E R)) → Set _
  WalkResult {ℓB = ℓB} P Q Q' s =
      ( Σ[ P' ∈ ITree _ _ _ ]
        ( P ═⟨ s ⟩═► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ ( Σ[ s' ∈ List (Event√ E _) ] Σ[ s-rest ∈ List (Event√ E _) ]
        Σ[ P' ∈ ITree _ _ _ ]
        ( (s ≡ s' ++ s-rest)
        × P ═⟨ s' ⟩═► P'
        × Divergent P' ) )

  walk
    : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P Q Q' : ITree E (ExtI I) R}
        {s : List (Event√ E R)}
    → Loop-Sim {ℓB = ℓB} P Q
    → Q ═⟨ s ⟩═► Q'
    → WalkResult {ℓB = ℓB} P Q Q' s
  walk sim bNil = inj₁ (_ , bNil , sim)
  walk {s = s} sim (bTau q-step rest) =
      case Loop-Sim.on-tau sim q-step of λ where
        (inj₁ (P-mid , P-τ* , sim')) →
          case walk sim' rest of λ where
            (inj₁ (P'-end , P-bs , sim'')) →
              inj₁ ( P'-end
                   , bigstep-concat (τ*-to-bigstep P-τ*) P-bs
                   , sim'' )
            (inj₂ (s' , s-rest , P' , split , P-bs , dv)) →
              inj₂ ( s'
                   , s-rest
                   , P'
                   , split
                   , bigstep-concat (τ*-to-bigstep P-τ*) P-bs
                   , dv )
        (inj₂ dv-P) →
          inj₂ ( [] , s , _ , refl , bNil , dv-P )
  walk {s = e ∷ s-rest-trace} sim (bStep q-step rest) =
      case Loop-Sim.on-vis sim q-step of λ where
        (inj₁ (P-mid , P-weak , sim')) →
          case walk sim' rest of λ where
            (inj₁ (P'-end , P-bs , sim'')) →
              inj₁ ( P'-end
                   , bigstep-concat (weak-ev-to-bigstep P-weak) P-bs
                   , sim'' )
            (inj₂ (s' , s-rest' , P' , split , P-bs , dv)) →
              inj₂ ( e ∷ s'
                   , s-rest'
                   , P'
                   , cong (e ∷_) split
                   , bigstep-concat (weak-ev-to-bigstep P-weak) P-bs
                   , dv )
        (inj₂ dv-P) →
          inj₂ ( [] , e ∷ s-rest-trace , _ , refl , bNil , dv-P )

-----------------------------------------------------------------------------------------
-- Obligation 1: `Loop-Sim P Q ⇒ P ⊑F⊥ Q`.
-----------------------------------------------------------------------------------------

loop-sim→⊑F⊥
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P Q : ITree E (ExtI I) R}
    → Loop-Sim {ℓB = ℓB} P Q
    → _⊑F⊥_ {ℓB = ℓB} P Q
loop-sim→⊑F⊥ sim {s} {B} (inj₁ (Q' , Q-reach , Q-ref)) =
    -- Walk the failure's reach.  If the walker completes the full
    -- trace, dispatch on the refusal shape.  If the walker
    -- short-circuits on a P-side divergence, produce a divergence
    -- witness directly.
    case walk sim Q-reach of λ where
      (inj₁ (P' , P-reach , sim')) →
        dispatch-ref P' Q' P-reach sim' Q-ref
      (inj₂ (s' , s-rest , P' , split , P-bs , dv-P)) →
        inj₂ (record
                { prefix  = s'
                ; suffix  = s-rest
                ; split   = split
                ; witness = P'
                ; reach   = P-bs
                ; divwit  = dv-P
                })
  where
    dispatch-ref
      : ∀ (P' Q' : _) → _ ═⟨ s ⟩═► P'
      → Loop-Sim P' Q'
      → Q' ref B
      → failures⊥ _ s B
    dispatch-ref P' Q' P-reach sim' (ref-stable st-Q no-ev-Q) =
        case Loop-Sim.on-stable-ref sim' st-Q no-ev-Q of λ where
          (inj₁ (P-stable , P-τ* , st-P , no-ev-P)) →
            let P-extended : _ ═⟨ s ⟩═► P-stable
                P-extended =
                  subst (λ s* → _ ═⟨ s* ⟩═► P-stable)
                        (++-identityʳ s)
                        (bigstep-concat P-reach (τ*-to-bigstep P-τ*))
            in inj₁ (P-stable , P-extended , ref-stable st-P no-ev-P)
          (inj₂ Divergent-P') →
            inj₂ (record
                    { prefix  = s
                    ; suffix  = []
                    ; split   = sym (++-identityʳ s)
                    ; witness = P'
                    ; reach   = P-reach
                    ; divwit  = Divergent-P'
                    })
    -- ref-tick: Q' fires √ x; apply on-vis at e = √ x.  If on-vis
    -- escapes to divergence, produce a divergence witness at the
    -- traversed-prefix trace (the full input trace `s` works since
    -- on-vis was at the trace's endpoint).
    dispatch-ref P' Q' P-reach sim' (ref-tick {x = x} step-Q ¬Bx) =
        case Loop-Sim.on-vis sim' step-Q of λ where
          (inj₁ (P-end , weak-ev pre step-P _post , _sim'')) →
            let P-extended : _ ═⟨ s ⟩═► _
                P-extended =
                  subst (λ s* → _ ═⟨ s* ⟩═► _)
                        (++-identityʳ s)
                        (bigstep-concat P-reach (τ*-to-bigstep pre))
            in inj₁ (_ , P-extended , ref-tick step-P ¬Bx)
          (inj₂ Divergent-P') →
            inj₂ (record
                    { prefix  = s
                    ; suffix  = []
                    ; split   = sym (++-identityʳ s)
                    ; witness = P'
                    ; reach   = P-reach
                    ; divwit  = Divergent-P'
                    })

-- Divergence-input arm: lift Q's divergence to P via the walker +
-- `on-div`.  Walker may short-circuit on its own divergence escape
-- mid-trace; either way we produce a divergence witness.
loop-sim→⊑F⊥ sim {s} {B} (inj₂ Q-div) =
    case walk sim (Q-div .IsDivergence.reach) of λ where
      (inj₁ (P-witness , P-reach , sim')) →
        inj₂ (record
                { prefix  = Q-div .IsDivergence.prefix
                ; suffix  = Q-div .IsDivergence.suffix
                ; split   = Q-div .IsDivergence.split
                ; witness = P-witness
                ; reach   = P-reach
                ; divwit  = Loop-Sim.on-div sim' (Q-div .IsDivergence.divwit)
                })
      (inj₂ (s' , s-rest , P' , prefix-split , P-bs , dv-P)) →
        -- Walker short-circuited at s'.  Q-div.prefix ≡ s' ++ s-rest.
        -- Combine with Q-div.split to get s ≡ s' ++ (s-rest ++ Q-div.suffix).
        let split-eq : s ≡ s' ++ (s-rest ++ Q-div .IsDivergence.suffix)
            split-eq =
              trans (Q-div .IsDivergence.split)
                (trans (cong (_++ Q-div .IsDivergence.suffix) prefix-split)
                       (++-assoc s' s-rest (Q-div .IsDivergence.suffix)))
        in inj₂ (record
                  { prefix  = s'
                  ; suffix  = s-rest ++ Q-div .IsDivergence.suffix
                  ; split   = split-eq
                  ; witness = P'
                  ; reach   = P-bs
                  ; divwit  = dv-P
                  })

-- Divergence-inclusion extractor: a `Loop-Sim P Q` yields `P ⊑D Q`.
-- This is exactly the divergence-input arm of `loop-sim→⊑F⊥` above,
-- but returning the bare `divergences P s` rather than its `inj₂`
-- injection into `failures⊥`.  Used to assemble `loop-mono-⊑D-via-bisim`.
loop-sim→⊑D
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P Q : ITree E (ExtI I) R}
    → Loop-Sim {ℓB = ℓB} P Q → P ⊑D Q
loop-sim→⊑D sim {s} Q-div =
    case walk sim (Q-div .IsDivergence.reach) of λ where
      (inj₁ (P-witness , P-reach , sim')) →
        record
          { prefix  = Q-div .IsDivergence.prefix
          ; suffix  = Q-div .IsDivergence.suffix
          ; split   = Q-div .IsDivergence.split
          ; witness = P-witness
          ; reach   = P-reach
          ; divwit  = Loop-Sim.on-div sim' (Q-div .IsDivergence.divwit)
          }
      (inj₂ (s' , s-rest , P' , prefix-split , P-bs , dv-P)) →
        record
          { prefix  = s'
          ; suffix  = s-rest ++ Q-div .IsDivergence.suffix
          ; split   = trans (Q-div .IsDivergence.split)
                        (trans (cong (_++ Q-div .IsDivergence.suffix) prefix-split)
                               (++-assoc s' s-rest (Q-div .IsDivergence.suffix)))
          ; witness = P'
          ; reach   = P-bs
          ; divwit  = dv-P
          }

-----------------------------------------------------------------------------------------
-- Obligation 2: body refinement implies `Loop-Sim` on the loops.
--
-- Discharge strategy (see plan doc): construct each `Loop-Sim` field
-- coinductively, dispatching on body's force at each step.
-----------------------------------------------------------------------------------------

private
  -- Empty-trace bigstep → τ* chain.  Useful for going from `loop-mono-⊑D`'s
  -- divergence-transformer output (in `divergences` record form) to a
  -- raw `Divergent` witness on the original tree.
  bigstep-empty-to-τ*
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {t t' : ITree E (ExtI I) R}
    → t ═⟨ [] ⟩═► t' → t ─[τ*]─► t'
  bigstep-empty-to-τ* bNil             = τ*-zero
  bigstep-empty-to-τ* (bTau step rest) = τ*-step step (bigstep-empty-to-τ* rest)

  -- τ-closure of ⊑F⊥ on the right: a τ-step extends any refinement
  -- relation to the τ-successor.  Every failure⊥ of `c` lifts to a
  -- failure⊥ of `P` by prepending the τ-step (via bTau on the bigstep
  -- inside the failure / via bTau on the divergence record's reach).
  ⊑F⊥-τ-step-right
    : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {body-a Q c : ITree E I R}
    → Q ─[ τ ]─► c
    → _⊑F⊥_ {ℓB = ℓB} body-a Q
    → _⊑F⊥_ {ℓB = ℓB} body-a c
  ⊑F⊥-τ-step-right τ-step ba⊑Q (inj₁ (W , bs-W , ref-W)) =
      ba⊑Q (inj₁ (W , bTau τ-step bs-W , ref-W))
  ⊑F⊥-τ-step-right τ-step ba⊑Q (inj₂ d-c) =
      ba⊑Q (inj₂ (record
        { prefix  = d-c .IsDivergence.prefix
        ; suffix  = d-c .IsDivergence.suffix
        ; split   = d-c .IsDivergence.split
        ; witness = d-c .IsDivergence.witness
        ; reach   = bTau τ-step (d-c .IsDivergence.reach)
        ; divwit  = d-c .IsDivergence.divwit
        }))

  ⊑D-τ-step-right
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {body-a Q c : ITree E I R}
    → Q ─[ τ ]─► c
    → body-a ⊑D Q
    → body-a ⊑D c
  ⊑D-τ-step-right τ-step ba⊑DQ d-c =
      ba⊑DQ (record
        { prefix  = d-c .IsDivergence.prefix
        ; suffix  = d-c .IsDivergence.suffix
        ; split   = d-c .IsDivergence.split
        ; witness = d-c .IsDivergence.witness
        ; reach   = bTau τ-step (d-c .IsDivergence.reach)
        ; divwit  = d-c .IsDivergence.divwit
        })

-- `loop-mono-⊑D` is now discharged via the bisimulation (see
-- `loop-mono-⊑D-via-bisim` below); the `Loop-Sim.on-div` field is
-- built from `tail-on-div-lift`, so no postulate is consumed here.

private
  -- Split-empty inversion: `[] ≡ xs ++ ys` forces `xs ≡ []`.
  split-empty-l : ∀ {ℓX} {X : Set ℓX} {xs ys : List X}
                → [] ≡ xs ++ ys → xs ≡ []
  split-empty-l {xs = []}     refl = refl
  split-empty-l {xs = _ ∷ _} ()

-----------------------------------------------------------------------------------------
-- Mid-loop-sim infrastructure (mid-loop-sim plan, 2026-05-21).
--
-- `tail-sim→loop-sim`: lift Tail-Sim on body-tails to Loop-Sim on
-- iter-bind states.  Each Loop-Sim field dispatches on the input
-- step's iter-bind structure (via iter-bind-force-* inverses), then
-- routes through the matching Tail-Sim field, then re-packages into a
-- Loop-Sim transition.  The on-ret-inj₁ field of Tail-Sim provides
-- both the boundary equation and the post-cycle Loop-Sim recursion,
-- which is consumed inside this lift when a step crosses the
-- iteration boundary.
--
-- `bF⊑+bD⊑→Tail-Sim`: entry-point construction of Tail-Sim at the
-- initial body-tails `(body a >>= k')` `(body' a >>= k')`.  Each
-- Tail-Sim field dispatches on body' a's force shape and uses bF⊑/bD⊑
-- at the appropriate trace/refusal predicate.  The on-vis field
-- bottoms out at the residual body-tail stabilises-or-diverges
-- obligation identified in Task 1 (see comment near the deleted
-- spike).
--
-- `bF⊑+bD⊑→Tail-Sim` is split into six per-field constructors below;
-- the wrapper assembles them into a Tail-Sim record.  Each per-field
-- postulate has a smaller scope and can be discharged independently
-- in subsequent sessions.  The shape mirrors the corresponding
-- Tail-Sim field with X = body a >>= k' and Y = body' a >>= k', where
-- k' = λ a' → Ret (h a').
-----------------------------------------------------------------------------------------

-- `tail-on-vis-construct` is split into three per-shape narrow
-- postulates (sVis / sMixVis / sRet) mirroring the split pattern
-- used for `tail-on-tau-construct`.  The dispatcher below
-- pattern-matches on the visible-event step constructor and routes
-- to the matching per-shape postulate; each can be discharged
-- independently in subsequent sessions.
-- `tail-on-vis-sVis-body-vis-Y`: Y-parameterised core lemma.
-- The non-Y variant below derives from this by applying at Y = body' a.
-- Real definition appears after `Tail-Sim-deadlock` (below), where
-- `make-tail-sim-from-W-ref-c` (its main ingredient) is also defined.
tail-on-vis-sVis-body-vis-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) A))}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {c : ITree E (ExtI I) A}
    → ITree.force Y ≡ vis f'
    → f' at a-evt ≡ just c
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a' → Ret (h a')))
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
            X' (c >>= (λ a' → Ret (h a'))) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))

-- `tail-on-vis-sVis-body-vis`: narrower dispatcher — the only live case
-- of `tail-on-vis-sVis` after case-splitting on body' a's force shape.
-- Derived from the Y-parameterised variant by applying at Y = body' a.
tail-on-vis-sVis-body-vis
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) A))}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {c : ITree E (ExtI I) A}
    → ITree.force (body' a) ≡ vis f'
    → f' at a-evt ≡ just c
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a' → Ret (h a')))
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
            X' (c >>= (λ a' → Ret (h a'))) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-vis-sVis-body-vis bF⊑ bD⊑ sim-rec a body'-eq f-eq =
  tail-on-vis-sVis-body-vis-Y a (bF⊑ a) (bD⊑ a) sim-rec body'-eq f-eq

-- `tail-on-vis-sVis`: dispatcher.  Case-splits on body' a's force
-- shape.  Only `vis f'` is live (other shapes make the bind's force
-- non-`vis`, contradicting eq-f via `()`).  Inside the vis arm,
-- further case-splits on `f' at a-evt`: `nothing` makes bind-cont-vis
-- return `nothing`, contradicting eq-j; `just c` unifies Y' with
-- `c >>= k'` and routes to the narrower postulate.
tail-on-vis-sVis
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f : (at : AnyTypes E)
             → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {Y' : ITree E (ExtI I) (A ⊎ R)}
    → ITree.force (body' a >>= (λ a' → Ret (h a'))) ≡ vis f
    → f at a-evt ≡ just Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a')))
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-vis-sVis {body' = body'} {h = h} bF⊑ bD⊑ sim-rec a {at = at} {a-evt = a-evt}
                  eq-f eq-j
    with body' a .force in body'-eq | eq-f
... | ret _        | ()
... | sil _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | ()
... | vis f'       | refl
    with f' at a-evt in f-eq | eq-j
...   | nothing | ()
...   | just _  | refl =
        tail-on-vis-sVis-body-vis bF⊑ bD⊑ sim-rec a body'-eq f-eq

-- `tail-on-vis-sVis-Y`: Y-parameterised sibling dispatcher.  Case-
-- splits on Y's force shape; only `vis f'` is live.  Routes the live
-- arm to `tail-on-vis-sVis-body-vis-Y`.
-- Definition moved to after `Tail-Sim-deadlock`; forward declaration only.
tail-on-vis-sVis-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {f : (at : AnyTypes E)
             → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {Y' : ITree E (ExtI I) (A ⊎ R)}
    → ITree.force (Y >>= (λ a' → Ret (h a'))) ≡ vis f
    → f at a-evt ≡ just Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a')))
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))

-- `tail-on-vis-sMixVis-body-mix-Y`: Y-parameterised core lemma.
-- The non-Y variant below derives from this by applying at Y = body' a.
-- Real definition appears after `Tail-Sim-deadlock` (below).
tail-on-vis-sMixVis-body-mix-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) A))}
        {Qt' : ITree E (ExtI I) A}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {c : ITree E (ExtI I) A}
    → ITree.force Y ≡ mix f' Qt'
    → f' at a-evt ≡ just c
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a' → Ret (h a')))
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
            X' (c >>= (λ a' → Ret (h a'))) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))

-- `tail-on-vis-sMixVis-body-mix`: non-Y dispatcher, only live case of
-- `tail-on-vis-sMixVis` after case-splitting on body' a's force shape.
-- Derived from the Y-parameterised variant by applying at Y = body' a.
tail-on-vis-sMixVis-body-mix
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) A))}
        {Qt' : ITree E (ExtI I) A}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {c : ITree E (ExtI I) A}
    → ITree.force (body' a) ≡ mix f' Qt'
    → f' at a-evt ≡ just c
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a' → Ret (h a')))
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
            X' (c >>= (λ a' → Ret (h a'))) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-vis-sMixVis-body-mix bF⊑ bD⊑ sim-rec a body'-eq f-eq =
  tail-on-vis-sMixVis-body-mix-Y a (bF⊑ a) (bD⊑ a) sim-rec body'-eq f-eq

-- `tail-on-vis-sMixVis`: dispatcher.  Case-splits on body' a's force
-- shape.  Only `mix f' Qt'` is live (other shapes make the bind's
-- force non-`mix`, contradicting eq-f via `()`).  Inside the mix
-- arm, further case-splits on `f' at a-evt`: `nothing` makes
-- bind-cont-mix return `nothing`, contradicting eq-j; `just c`
-- unifies Y' with `c >>= k'` and routes to the narrower postulate.
tail-on-vis-sMixVis
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f : (at : AnyTypes E)
             → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))}
        {Qt : ITree E (ExtI I) (A ⊎ R)}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {Y' : ITree E (ExtI I) (A ⊎ R)}
    → ITree.force (body' a >>= (λ a' → Ret (h a'))) ≡ mix f Qt
    → f at a-evt ≡ just Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a')))
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-vis-sMixVis {body' = body'} {h = h} bF⊑ bD⊑ sim-rec a {at = at} {a-evt = a-evt}
                     eq-f eq-j
    with body' a .force in body'-eq | eq-f
... | ret _        | ()
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix f' _     | refl
    with f' at a-evt in f-eq | eq-j
...   | nothing | ()
...   | just _  | refl =
        tail-on-vis-sMixVis-body-mix bF⊑ bD⊑ sim-rec a body'-eq f-eq

-- `tail-on-vis-sMixVis-Y`: forward declaration only.
-- Definition moved to after `Tail-Sim-deadlock` (below).
tail-on-vis-sMixVis-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {f : (at : AnyTypes E)
             → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))}
        {Qt : ITree E (ExtI I) (A ⊎ R)}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {Y' : ITree E (ExtI I) (A ⊎ R)}
    → ITree.force (Y >>= (λ a' → Ret (h a'))) ≡ mix f Qt
    → f at a-evt ≡ just Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a')))
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))

-- `Tail-Sim-deadlock`: the terminal Tail-Sim.  Mirrors
-- `loop-sim-deadlock` (Loop-Sim version, line 467).  Every transition
-- from deadlock is structurally impossible since deadlock.force is
-- vis-shaped with no live branches.  Tail-Sim adds `on-ret-inj₁` and
-- `on-ret-inj₂` fields (absent in Loop-Sim); both are absurd here
-- since force(deadlock) ≡ vis _, not ret.
private
  Tail-Sim-deadlock
    : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        {body body' : HKTree E (ExtI I) A}
        {h : A → A ⊎ R}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
                (deadlock {E = E} {I = ExtI I} {R = A ⊎ R}) deadlock
  Tail-Sim-deadlock {ℓB = ℓB} {I = I} {A = A} {R = R} = record
    { on-vis        = no-vis
    ; on-tau        = no-tau
    ; on-stable-ref = stable-ref-deadlock
    ; on-div        = λ d → ⊥-elim (Divergent-deadlock-absurd d)
    ; on-ret-inj₁   = λ ()
    ; on-ret-inj₂   = λ ()
    }
    where
      no-vis : ∀ {e : Event√ E (A ⊎ R)} {Y'} → deadlock ─[ ev e ]─► Y' → _
      no-vis (sVis refl eq-j) = case eq-j of λ ()
      no-vis (sMixVis force≡mix _) = case force≡mix of λ ()
      no-vis (sRet force≡ret) = case force≡ret of λ ()

      no-tau : ∀ {Y'} → deadlock ─[ τ ]─► Y' → _
      no-tau step = ⊥-elim (τ-from-force-vis-impossible refl step)

      no-ev-from-deadlock : ∀ {e : Event√ E (A ⊎ R)} {Q'}
                          → ¬ deadlock ─[ ev e ]─► Q'
      no-ev-from-deadlock (sVis refl eq-j) = case eq-j of λ ()
      no-ev-from-deadlock (sMixVis force≡mix _) = case force≡mix of λ ()
      no-ev-from-deadlock (sRet force≡ret) = case force≡ret of λ ()

      stable-ref-deadlock : ∀ {B : Event√ E (A ⊎ R) → Set ℓB}
                          → isStable (deadlock {E = E} {I = ExtI I} {R = A ⊎ R})
                          → (∀ e → B e → ∀ {Q'} → ¬ deadlock ─[ ev e ]─► Q')
                          → _
      stable-ref-deadlock _ _ =
        inj₁ ( deadlock , τ*-zero , tt₀ , (λ _ _ {_} → no-ev-from-deadlock) )

-- `ev-step-closure-⊑F⊥`: classical ev-step lifting principle.
-- If P ⊑F⊥ Q + P ⊑D Q and Q fires e to c, then either P fires e
-- (weakly) to some W with W ⊑F⊥ c and W ⊑D c, or P diverges.
--
-- Status: postulated, sound in the CSP-FD model.  This is the
-- "P after e refines c" principle, irreducible without further
-- machinery.  Two routes to discharge it:
--   1. Denotationally: model P/Q/c as `(traces, failures, divergences)`
--      triples and define `W ≡ (P after e)` directly as the triple of
--      sets `{(s, X) : (e :: s, X) ∈ failures⊥ P}`.  Trivial there, but
--      requires a representation theorem connecting such triples back
--      to ITrees — not currently in this codebase.
--   2. Classically: pair `¬-divergent→τ-Acc` (already postulated in
--      `DRWeakBisim`) with excluded-middle on stable-leaf enumeration
--      to choose a single ITree W from P's possibly-many after-e states.
--      Constructively, no canonical choice exists, so a strict
--      derivation needs LEM beyond `¬-divergent→τ-Acc`.
--
-- The `W ⊑D c` conjunct lets `make-tail-sim-from-W-ref-c` discharge
-- its `on-div` field constructively (divergence-refinement applied
-- at the empty trace + Divergent extraction).
postulate
  ev-step-closure-⊑F⊥
    : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P Q c : ITree E I R}
        {e : Event√ E R}
    → _⊑F⊥_ {ℓB = ℓB} P Q
    → P ⊑D Q
    → Q ─[ ev e ]─► c
    → ( Σ[ W ∈ ITree E I R ]
        ( P ═[ ev e ]═► W
        × _⊑F⊥_ {ℓB = ℓB} W c
        × W ⊑D c ) )
    ⊎ Divergent P

-- `bind-left-τ*`: lift a τ*-chain on P through bind.
-- Mirrors `iter-bind-left-τ*` but for plain bind (not iter-bind).
-- Used inside `make-tail-sim-from-W-ref-c` to lift weak ev-steps.
private
  bind-left-τ*
    : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        {P P' : ITree E (ExtI I) R} (k : R → ITree E (ExtI I) S)
    → P ─[τ*]─► P'
    → (P >>= k) ─[τ*]─► (P' >>= k)
  bind-left-τ* k τ*-zero           = τ*-zero
  bind-left-τ* {P = P} k (τ*-step s rest) =
      τ*-step (bind-left-step-lift P k s) (bind-left-τ* k rest)

-- `make-tail-sim-from-W-ref-c`: coinductive helper that builds
-- `Tail-Sim (W >>= k') (c >>= k')` from `W ⊑F⊥ c` and `W ⊑D c`.
-- Marked NON_TERMINATING because Agda cannot verify coinductive
-- productivity through the dispatch on step constructors.
-- Used to discharge `tail-on-vis-sVis-body-vis-Y` and
-- `tail-on-vis-sMixVis-body-mix-Y`.
private
  {-# NON_TERMINATING #-}
  make-tail-sim-from-W-ref-c
    : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        {body body' : HKTree E (ExtI I) A}
        {h : A → A ⊎ R}
        (W c : ITree E (ExtI I) A)
      → (sim-rec : ∀ (a : A)
                   → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
      → _⊑F⊥_ {ℓB = ℓB} W c
      → W ⊑D c
      → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
                 (W >>= (λ a' → Ret (h a')))
                 (c >>= (λ a' → Ret (h a')))
  -- on-vis: c >>= k ─[ev e]─► Y' ; case-split on step constructor to
  -- recover the c-level step, then apply ev-step-closure-⊑F⊥.
  make-tail-sim-from-W-ref-c {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h}
                              W c sim-rec W⊑c W⊑Dc .Tail-Sim.on-vis
      = go-vis
    where
      k : A → ITree E (ExtI I) (A ⊎ R)
      k = λ a' → Ret (h a')

      -- lift a body-level weak evl-step through bind.
      -- The underlying Event E index is shared, so the evl label
      -- lives at Event√ E A before bind and Event√ E (A ⊎ R) after.
      lift-weak-ev
        : ∀ {P P₁ P' : ITree E (ExtI I) A} {e-E : Event E}
        → P ─[τ*]─► P₁
        → P₁ ─[ ev (evl e-E) ]─► P'
        → ∀ {P₁' : ITree E (ExtI I) A}
        → P' ─[τ*]─► P₁'
        → (P >>= k) ═[ ev (evl e-E) ]═► (P₁' >>= k)
      lift-weak-ev pre₁ step₁ post₁ =
          weak-ev (bind-left-τ* k pre₁)
                  (lift-bind-step-ev _ k step₁)
                  (bind-left-τ* k post₁)

      -- main dispatch for on-vis
      go-vis
        : ∀ {e : Event√ E (A ⊎ R)} {Y' : ITree E (ExtI I) (A ⊎ R)}
        → (c >>= k) ─[ ev e ]─► Y'
        → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
            ( (W >>= k) ═[ ev e ]═► X'
            × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
        ⊎ Divergent (W >>= k)
      go-vis (sVis {f = f-bind} {at = at} {a = a-evt} {t′ = Y'} c-bind-eq c-bind-j)
          with c .force in c-eq | c-bind-eq
      ... | ret _        | ()
      ... | sil _        | ()
      ... | ndbr _ _ _ _ | ()
      ... | mix _ _      | ()
      ... | vis fC       | refl
          with fC at a-evt in fC-eq | c-bind-j
      ...   | nothing | ()
      ...   | just c' | refl =
                -- After refl: Y' ≡ c' >>= k definitionally (bind-cont-vis-just)
                let c-step = sVis c-eq fC-eq
                in case ev-step-closure-⊑F⊥ {ℓB = ℓB} W⊑c W⊑Dc c-step of λ where
                     (inj₂ W-div) → inj₂ (Divergent-bind-left k W-div)
                     (inj₁ (W' , weak-ev pre₁ step₁ post₁ , W'⊑c' , W'⊑Dc')) →
                       inj₁ ( W' >>= k
                             , lift-weak-ev pre₁ step₁ post₁
                             , make-tail-sim-from-W-ref-c W' c' sim-rec W'⊑c' W'⊑Dc' )
      go-vis (sMixVis {f = f-bind} {at = at} {a = a-evt} {t′ = Y'} c-bind-eq c-bind-j)
          with c .force in c-eq | c-bind-eq
      ... | ret _        | ()
      ... | sil _        | ()
      ... | ndbr _ _ _ _ | ()
      ... | vis _        | ()
      ... | mix fC QtC   | refl
          with fC at a-evt in fC-eq | c-bind-j
      ...   | nothing | ()
      ...   | just c' | refl =
                -- After refl: Y' ≡ c' >>= k definitionally (bind-cont-mix-just)
                let c-step = sMixVis c-eq fC-eq
                in case ev-step-closure-⊑F⊥ {ℓB = ℓB} W⊑c W⊑Dc c-step of λ where
                     (inj₂ W-div) → inj₂ (Divergent-bind-left k W-div)
                     (inj₁ (W' , weak-ev pre₁ step₁ post₁ , W'⊑c' , W'⊑Dc')) →
                       inj₁ ( W' >>= k
                             , lift-weak-ev pre₁ step₁ post₁
                             , make-tail-sim-from-W-ref-c W' c' sim-rec W'⊑c' W'⊑Dc' )
      go-vis (sRet {x = x} c-bind-eq)
              with c .force in c-eq | c-bind-eq
      ... | sil _        | ()
      ... | vis _        | ()
      ... | ndbr _ _ _ _ | ()
      ... | mix _ _      | ()
      ... | ret a-val    | cbeq =
              -- After c .force = ret a-val, force(c >>= k) reduces to
              -- ret (h a-val), so cbeq : ret (h a-val) ≡ ret x.  `h` is a
              -- variable, so the payload `h a-val` is a stuck neutral that
              -- cannot be solved by the with-unifier directly; build the
              -- result at payload `h a-val` and transport to `x`.
              subst (λ z → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                             ( (W >>= k) ═[ ev (√ z) ]═► X'
                             × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
                                        X' deadlock ) )
                           ⊎ Divergent (W >>= k))
                    (ret-inj cbeq)
                    (dispatch (W⊑c (inj₁ (deadlock , bStep (sRet c-eq) bNil , deadlock-ref))))
            where
              ret-inj : ∀ {z : A ⊎ R}
                      → ret {E = E} {I = ExtI I} (h a-val) ≡ ret z → h a-val ≡ z
              ret-inj refl = refl

              handle-failure
                : Σ[ V ∈ ITree E (ExtI I) A ]
                  ( W ═⟨ √ a-val ∷ [] ⟩═► V × V ref (λ _ → Lift ℓB ⊥))
                → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                    ( (W >>= k) ═[ ev (√ (h a-val)) ]═► X'
                    × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
                ⊎ Divergent (W >>= k)
              handle-failure (V , bs-V , _) =
                let V-eq   = tick-bigstep-lands-at-deadlock {s1 = []} bs-V
                    bs-dl  = subst (λ Z → W ═⟨ √ a-val ∷ [] ⟩═► Z) V-eq bs-V
                    lb     = lift-bind-bigstep-tick W k [] bs-dl
                    P-bind = proj₁ lb
                    τ*-pre = bigstep-empty-to-τ* (proj₁ (proj₂ lb))
                    sRet-s = sRet (proj₂ (proj₂ lb))
                    weak   = weak-ev τ*-pre sRet-s τ*-zero
                in inj₁ (deadlock , weak , Tail-Sim-deadlock)
              handle-divergence
                : divergences W (√ a-val ∷ [])
                → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                    ( (W >>= k) ═[ ev (√ (h a-val)) ]═► X'
                    × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
                ⊎ Divergent (W >>= k)
              handle-divergence d-W =
                case prefix-tick-split [] {r = a-val}
                        (d-W .IsDivergence.prefix)
                        (d-W .IsDivergence.suffix)
                        (sym (d-W .IsDivergence.split))
                    of λ where
                  (inj₁ (pre0 , _ , s1-eq , pre-eq , _)) →
                    let pre0-eq  = split-empty-l s1-eq
                        prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
                        reach-[]  = subst (λ s → W ═⟨ s ⟩═► d-W .IsDivergence.witness)
                                          prefix-eq (d-W .IsDivergence.reach)
                        div-W = divergent-prefix (bigstep-empty-to-τ* reach-[])
                                  (d-W .IsDivergence.divwit)
                    in inj₂ (Divergent-bind-left k div-W)
                  (inj₂ (pre-eq , _)) →
                    let bs-V = subst (λ s → W ═⟨ s ⟩═► d-W .IsDivergence.witness)
                                     pre-eq (d-W .IsDivergence.reach)
                        V-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-V
                    in ⊥-elim (Divergent-deadlock-absurd
                                 (subst Divergent V-dl (d-W .IsDivergence.divwit)))
              dispatch : failures⊥ W (√ a-val ∷ []) (λ _ → Lift ℓB ⊥)
                       → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                           ( (W >>= k) ═[ ev (√ (h a-val)) ]═► X'
                           × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
                       ⊎ Divergent (W >>= k)
              dispatch (inj₁ f) = handle-failure f
              dispatch (inj₂ d) = handle-divergence d

  -- on-tau: case-split on step constructor; apply ⊑F⊥-τ-step-right,
  -- then recurse at the τ-successor.
  make-tail-sim-from-W-ref-c {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h}
                              W c sim-rec W⊑c W⊑Dc .Tail-Sim.on-tau
      = go-tau
    where
      k : A → ITree E (ExtI I) (A ⊎ R)
      k = λ a' → Ret (h a')

      go-tau
        : ∀ {Y' : ITree E (ExtI I) (A ⊎ R)}
        → (c >>= k) ─[ τ ]─► Y'
        → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
            ( (W >>= k) ─[τ*]─► X'
            × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
        ⊎ Divergent (W >>= k)
      go-tau (sSil c-bind-eq)
          with c .force in c-eq | c-bind-eq
      ... | ret _        | ()
      ... | vis _        | ()
      ... | ndbr _ _ _ _ | ()
      ... | mix _ _      | ()
      ... | sil c'       | refl =
              inj₁ ( W >>= k , τ*-zero
                   , make-tail-sim-from-W-ref-c W c' sim-rec
                       (⊑F⊥-τ-step-right (sSil c-eq) W⊑c)
                       (⊑D-τ-step-right  (sSil c-eq) W⊑Dc) )
      go-tau (sNdbr {f = f-bind} {i = i-idx} {a = a-idx} c-bind-eq c-bind-j)
          with c .force in c-eq | c-bind-eq
      ... | ret _        | ()
      ... | vis _        | ()
      ... | sil _        | ()
      ... | mix _ _      | ()
      ... | ndbr fC wi wa wp | refl
          with fC i-idx a-idx in fC-eq | c-bind-j
      ...   | nothing | ()
      ...   | just c' | refl =
              inj₁ ( W >>= k , τ*-zero
                   , make-tail-sim-from-W-ref-c W c' sim-rec
                       (⊑F⊥-τ-step-right (sNdbr c-eq fC-eq) W⊑c)
                       (⊑D-τ-step-right  (sNdbr c-eq fC-eq) W⊑Dc) )
      go-tau (sMixSlide {Qt = Y'} c-bind-eq)
          with c .force in c-eq | c-bind-eq
      ... | ret _        | ()
      ... | vis _        | ()
      ... | sil _        | ()
      ... | ndbr _ _ _ _ | ()
      ... | mix fC QtC   | refl =
              inj₁ ( W >>= k , τ*-zero
                   , make-tail-sim-from-W-ref-c W QtC sim-rec
                       (⊑F⊥-τ-step-right (sMixSlide c-eq) W⊑c)
                       (⊑D-τ-step-right  (sMixSlide c-eq) W⊑Dc) )

  -- on-stable-ref: same proof structure as tail-on-stable-ref-construct-Y
  -- but using W/c directly instead of (body a)/(body' a).
  make-tail-sim-from-W-ref-c {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h}
                              W c sim-rec W⊑c W⊑Dc .Tail-Sim.on-stable-ref {B = B}
      = go-stable-ref
    where
      k : A → ITree E (ExtI I) (A ⊎ R)
      k = λ a' → Ret (h a')

      go-stable-ref
        : isStable (c >>= k)
        → (∀ (e : Event√ E (A ⊎ R)) → B e
               → ∀ {Y' : ITree E (ExtI I) (A ⊎ R)} → ¬ (c >>= k) ─[ ev e ]─► Y')
        → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
            ( (W >>= k) ─[τ*]─► X'
            × isStable X'
            × (∀ (e : Event√ E (A ⊎ R)) → B e
                   → ∀ {X''} → ¬ X' ─[ ev e ]─► X'')) )
        ⊎ Divergent (W >>= k)
      go-stable-ref c-bind-stable c-bind-no-ev
          with c .force in c-eq
      ... | ret _        = ⊥-elim c-bind-stable
      ... | sil _        = ⊥-elim c-bind-stable
      ... | ndbr _ _ _ _ = ⊥-elim c-bind-stable
      ... | mix _ _      = ⊥-elim c-bind-stable
      ... | vis fC       = dispatch-out (W⊑c (inj₁ c-fail))
        where
          B* : Event√ E A → Set ℓB
          B* (evl e) = B (evl e)
          B* (√ _)   = ⊤ {ℓB}
          c-ref : c ref B*
          c-ref = ref-stable (vis-isStable {P = c} c-eq) λ where
            (evl e) Be step → c-bind-no-ev (evl e) Be (lift-bind-step-ev c k step)
            (√ _)   _   (sRet eq-ret) → case trans (sym c-eq) eq-ret of λ ()
          c-fail : failures c [] B*
          c-fail = c , bNil , c-ref
          invert-bind-step
            : ∀ {V : ITree E (ExtI I) A}
                {fV : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) A))}
                {e : Event√ E (A ⊎ R)} {t}
            → ITree.force V ≡ vis fV
            → (V >>= k) ─[ ev e ]─► t
            → Σ (Event E) λ e' → e ≡ evl e' ×
                  Σ (ITree E (ExtI I) A) λ Q' → V ─[ ev (evl e') ]─► Q'
          invert-bind-step {V = V} {fV = fV} eq-V (sVis {at = at} {a = a-evt} {t′ = tgt} eq-f eq-j) =
              cont-inv (fV at a-evt) refl
            where
              f≡ = vis-injective (trans (sym eq-f) (bind-force-vis V k eq-V))
              eq-j' = subst (λ g → g at a-evt ≡ just tgt) f≡ eq-j
              cont-inv : (m : Maybe (ITree E (ExtI I) A)) → fV at a-evt ≡ m
                       → Σ (Event E) λ e' → _ ≡ evl e' × Σ _ λ Q' → V ─[ ev (evl e') ]─► Q'
              cont-inv nothing  fi = ⊥-elim
                (case trans (sym (bind-cont-vis-nothing k fV at a-evt fi)) eq-j' of λ ())
              cont-inv (just t′) fi = _ , refl , t′ , sVis eq-V fi
          invert-bind-step {V = V} {fV = fV} eq-V (sMixVis eq-f _) =
              case trans (sym (bind-force-vis V k eq-V)) eq-f of λ ()
          invert-bind-step {V = V} {fV = fV} eq-V (sRet eq-f) =
              case trans (sym (bind-force-vis V k eq-V)) eq-f of λ ()
          failure-arm
            : Σ[ V ∈ ITree E (ExtI I) A ] ( W ═⟨ [] ⟩═► V × V ref B*)
            → Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                ( (W >>= k) ─[τ*]─► X' × isStable X'
                × (∀ e → B e → ∀ {X''} → ¬ X' ─[ ev e ]─► X''))
          failure-arm (V , bs-V , ref-tick {x = x} _ ¬Bx) = ⊥-elim (¬Bx tt)
          failure-arm (V , bs-V , ref-stable V-st V-no-ev)
              with V .force in v-eq
          ... | vis fV =
                  V >>= k
                , bigstep-empty-to-τ* (lift-bind-bigstep W k [] bs-V)
                , vis-isStable {P = V >>= k} (bind-force-vis V k v-eq)
                , λ e Be step → case invert-bind-step v-eq step of λ
                                   { (_ , refl , Q' , sV) → V-no-ev (evl _) Be sV }
          ... | ret _        = ⊥-elim V-st
          ... | sil _        = ⊥-elim V-st
          ... | ndbr _ _ _ _ = ⊥-elim V-st
          ... | mix _ _      = ⊥-elim V-st
          divergence-arm : IsDivergence W [] → Divergent (W >>= k)
          divergence-arm d-W =
            let prefix-≡-[] = split-empty-l (d-W .IsDivergence.split)
                reach-[]    = subst (λ s → W ═⟨ s ⟩═► d-W .IsDivergence.witness)
                                    prefix-≡-[] (d-W .IsDivergence.reach)
                div-W       = divergent-prefix (bigstep-empty-to-τ* reach-[])
                                  (d-W .IsDivergence.divwit)
            in Divergent-bind-left k div-W
          dispatch-out : failures⊥ W [] B*
                       → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                           ( (W >>= k) ─[τ*]─► X' × isStable X'
                           × (∀ e → B e → ∀ {X''} → ¬ X' ─[ ev e ]─► X'')) )
                       ⊎ Divergent (W >>= k)
          dispatch-out (inj₁ f) = inj₁ (failure-arm f)
          dispatch-out (inj₂ d) = inj₂ (divergence-arm d)

  -- on-div: lift divergence from (c >>= k) to (W >>= k) via W ⊑D c.
  -- Strip the pure-Ret continuation via Divergent-bind-pure-ret-inv,
  -- wrap as IsDivergence c [], apply W⊑Dc, extract Divergent W, lift
  -- back through bind via Divergent-bind-left.
  make-tail-sim-from-W-ref-c {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h}
                              W c sim-rec W⊑c W⊑Dc .Tail-Sim.on-div div-c-bind =
    let k : A → ITree E (ExtI I) (A ⊎ R)
        k = λ a' → Ret (h a')
        div-c : Divergent c
        div-c = Divergent-bind-pure-ret-inv h div-c-bind
        is-div-c : IsDivergence c []
        is-div-c = record
          { prefix  = []
          ; suffix  = []
          ; split   = refl
          ; witness = c
          ; reach   = bNil
          ; divwit  = div-c
          }
        is-div-W : IsDivergence W []
        is-div-W = W⊑Dc is-div-c
        prefix-≡-[] : is-div-W .IsDivergence.prefix ≡ []
        prefix-≡-[] = split-empty-l (is-div-W .IsDivergence.split)
        reach-at-[] : W ═⟨ [] ⟩═► is-div-W .IsDivergence.witness
        reach-at-[] = subst (λ s* → W ═⟨ s* ⟩═►
                                      is-div-W .IsDivergence.witness)
                            prefix-≡-[]
                            (is-div-W .IsDivergence.reach)
        div-W : Divergent W
        div-W = divergent-prefix
                  (bigstep-empty-to-τ* reach-at-[])
                  (is-div-W .IsDivergence.divwit)
    in Divergent-bind-left k div-W

  -- on-ret-inj₁: mirrors tail-on-ret-inj₁-construct-Y.
  make-tail-sim-from-W-ref-c {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h}
                              W c sim-rec W⊑c W⊑Dc .Tail-Sim.on-ret-inj₁ {a-next = a-next} eq-Y
      with c .force in c-eq
  ... | sil _        = case eq-Y of λ ()
  ... | vis _        = case eq-Y of λ ()
  ... | ndbr _ _ _ _ = case eq-Y of λ ()
  ... | mix _ _      = case eq-Y of λ ()
  ... | ret a-prime
      -- force(c >>= k) reduces to ret (h a-prime); the tag h a-prime
      -- decides whether this is a cycle boundary (inj₁) or an exit (inj₂,
      -- absurd against `ret (inj₁ a-next)`).
      with h a-prime in hav-eq | eq-Y
  ...   | inj₂ _     | ()
  ...   | inj₁ av'   | refl =
      dispatch (W⊑c (inj₁ (deadlock , bStep (sRet c-eq) bNil , deadlock-ref)))
    where
      k : A → ITree E (ExtI I) (A ⊎ R)
      k = λ a' → Ret (h a')
      -- After h a-prime = inj₁ av', the cycle continues at av' (= a-next).
      X'-force-eq : ∀ {X' : ITree E (ExtI I) (A ⊎ R)}
                  → ITree.force X' ≡ ret (h a-prime)
                  → ITree.force X' ≡ ret (inj₁ av')
      X'-force-eq {X'} fe = trans fe (cong (ret {E = E} {I = ExtI I}) hav-eq)
      handle-failure
        : Σ[ V ∈ ITree E (ExtI I) A ]
          ( W ═⟨ √ a-prime ∷ [] ⟩═► V × V ref (λ _ → Lift ℓB ⊥))
        → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
            ( (W >>= k) ─[τ*]─► X'
            × ITree.force X' ≡ ret (inj₁ a'-next)
            × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
        ⊎ Divergent (W >>= k)
      handle-failure (V , bs-V , _) =
        let V-eq   = tick-bigstep-lands-at-deadlock {s1 = []} bs-V
            bs-dl  = subst (λ Z → W ═⟨ √ a-prime ∷ [] ⟩═► Z) V-eq bs-V
            lb     = lift-bind-bigstep-tick W k [] bs-dl
            X'     = proj₁ lb
        in inj₁ ( X' , av'
                , bigstep-empty-to-τ* (proj₁ (proj₂ lb))
                , X'-force-eq {X' = proj₁ lb} (proj₂ (proj₂ lb))
                , sim-rec av' )
      handle-divergence
        : divergences W (√ a-prime ∷ [])
        → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
            ( (W >>= k) ─[τ*]─► X'
            × ITree.force X' ≡ ret (inj₁ a'-next)
            × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
        ⊎ Divergent (W >>= k)
      handle-divergence d-W =
        case prefix-tick-split [] {r = a-prime}
                (d-W .IsDivergence.prefix)
                (d-W .IsDivergence.suffix)
                (sym (d-W .IsDivergence.split))
            of λ where
          (inj₁ (pre0 , _ , s1-eq , pre-eq , _)) →
            let pre0-eq  = split-empty-l s1-eq
                prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
                reach-[]  = subst (λ s → W ═⟨ s ⟩═► d-W .IsDivergence.witness)
                                  prefix-eq (d-W .IsDivergence.reach)
                div-W = divergent-prefix (bigstep-empty-to-τ* reach-[])
                          (d-W .IsDivergence.divwit)
            in inj₂ (Divergent-bind-left k div-W)
          (inj₂ (pre-eq , _)) →
            let bs-V = subst (λ s → W ═⟨ s ⟩═► d-W .IsDivergence.witness)
                             pre-eq (d-W .IsDivergence.reach)
                V-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-V
            in ⊥-elim (Divergent-deadlock-absurd
                         (subst Divergent V-dl (d-W .IsDivergence.divwit)))
      dispatch : failures⊥ W (√ a-prime ∷ []) (λ _ → Lift ℓB ⊥)
               → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
                   ( (W >>= k) ─[τ*]─► X'
                   × ITree.force X' ≡ ret (inj₁ a'-next)
                   × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
               ⊎ Divergent (W >>= k)
      dispatch (inj₁ f) = handle-failure f
      dispatch (inj₂ d) = handle-divergence d

  -- on-ret-inj₂: real exit boundary.  force(c >>= k) ≡ ret (inj₂ r)
  -- forces c .force = ret a-val with h a-val = inj₂ r; W refines c so
  -- W bigsteps a √ a-val tick (or diverges), lift through bind to land
  -- (W >>= k) at ret (h a-val) ≡ ret (inj₂ r).
  make-tail-sim-from-W-ref-c {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h}
                              W c sim-rec W⊑c W⊑Dc .Tail-Sim.on-ret-inj₂ {r = r} eq-Y
      with c .force in c-eq
  ... | sil _        = case eq-Y of λ ()
  ... | vis _        = case eq-Y of λ ()
  ... | ndbr _ _ _ _ = case eq-Y of λ ()
  ... | mix _ _      = case eq-Y of λ ()
  ... | ret a-val
      with h a-val in hav-eq | eq-Y
  ...   | inj₁ _     | ()
  ...   | inj₂ r'    | refl =
      dispatch (W⊑c (inj₁ (deadlock , bStep (sRet c-eq) bNil , deadlock-ref)))
    where
      k : A → ITree E (ExtI I) (A ⊎ R)
      k = λ a' → Ret (h a')
      X'-force-eq : ∀ {X' : ITree E (ExtI I) (A ⊎ R)}
                  → ITree.force X' ≡ ret (h a-val)
                  → ITree.force X' ≡ ret (inj₂ r')
      X'-force-eq {X'} fe = trans fe (cong (ret {E = E} {I = ExtI I}) hav-eq)
      handle-failure
        : Σ[ V ∈ ITree E (ExtI I) A ]
          ( W ═⟨ √ a-val ∷ [] ⟩═► V × V ref (λ _ → Lift ℓB ⊥))
        → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
            ( (W >>= k) ─[τ*]─► X'
            × ITree.force X' ≡ ret (inj₂ r') ) )
        ⊎ Divergent (W >>= k)
      handle-failure (V , bs-V , _) =
        let V-eq   = tick-bigstep-lands-at-deadlock {s1 = []} bs-V
            bs-dl  = subst (λ Z → W ═⟨ √ a-val ∷ [] ⟩═► Z) V-eq bs-V
            lb     = lift-bind-bigstep-tick W k [] bs-dl
            X'     = proj₁ lb
        in inj₁ ( X'
                , bigstep-empty-to-τ* (proj₁ (proj₂ lb))
                , X'-force-eq {X' = proj₁ lb} (proj₂ (proj₂ lb)) )
      handle-divergence
        : divergences W (√ a-val ∷ [])
        → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
            ( (W >>= k) ─[τ*]─► X'
            × ITree.force X' ≡ ret (inj₂ r') ) )
        ⊎ Divergent (W >>= k)
      handle-divergence d-W =
        case prefix-tick-split [] {r = a-val}
                (d-W .IsDivergence.prefix)
                (d-W .IsDivergence.suffix)
                (sym (d-W .IsDivergence.split))
            of λ where
          (inj₁ (pre0 , _ , s1-eq , pre-eq , _)) →
            let pre0-eq  = split-empty-l s1-eq
                prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
                reach-[]  = subst (λ s → W ═⟨ s ⟩═► d-W .IsDivergence.witness)
                                  prefix-eq (d-W .IsDivergence.reach)
                div-W = divergent-prefix (bigstep-empty-to-τ* reach-[])
                          (d-W .IsDivergence.divwit)
            in inj₂ (Divergent-bind-left k div-W)
          (inj₂ (pre-eq , _)) →
            let bs-V = subst (λ s → W ═⟨ s ⟩═► d-W .IsDivergence.witness)
                             pre-eq (d-W .IsDivergence.reach)
                V-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-V
            in ⊥-elim (Divergent-deadlock-absurd
                         (subst Divergent V-dl (d-W .IsDivergence.divwit)))
      dispatch : failures⊥ W (√ a-val ∷ []) (λ _ → Lift ℓB ⊥)
               → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                   ( (W >>= k) ─[τ*]─► X'
                   × ITree.force X' ≡ ret (inj₂ r') ) )
               ⊎ Divergent (W >>= k)
      dispatch (inj₁ f) = handle-failure f
      dispatch (inj₂ d) = handle-divergence d

-- `tail-on-vis-sVis-body-vis-Y`: real definition.
-- Uses ev-step-closure-⊑F⊥ and make-tail-sim-from-W-ref-c.
tail-on-vis-sVis-body-vis-Y {body = body} {body' = body'} {h = h} a bF⊑Y bD⊑Y sim-rec Y-eq f-eq =
  case ev-step-closure-⊑F⊥ {ℓB = _} bF⊑Y bD⊑Y (sVis Y-eq f-eq) of λ where
    (inj₂ W-div) → inj₂ (Divergent-bind-left (λ a' → Ret (h a')) W-div)
    (inj₁ (W' , W-weak , W'⊑c , W'⊑Dc)) →
      let k = λ (a' : _) → Ret (h a')
          ts = make-tail-sim-from-W-ref-c W' _ sim-rec W'⊑c W'⊑Dc
          W-bind-weak : (body a >>= k) ═[ ev _ ]═► (W' >>= k)
          W-bind-weak = case W-weak of λ { (weak-ev pre₁ step₁ post₁) →
              weak-ev (bind-left-τ* k pre₁)
                      (lift-bind-step-ev _ k step₁)
                      (bind-left-τ* k post₁) }
      in inj₁ (W' >>= k , W-bind-weak , ts)

-- `tail-on-vis-sMixVis-body-mix-Y`: real definition.
-- Mirrors tail-on-vis-sVis-body-vis-Y with sMixVis in place of sVis.
tail-on-vis-sMixVis-body-mix-Y {body = body} {body' = body'} {h = h} a bF⊑Y bD⊑Y sim-rec Y-eq f-eq =
  case ev-step-closure-⊑F⊥ {ℓB = _} bF⊑Y bD⊑Y (sMixVis Y-eq f-eq) of λ where
    (inj₂ W-div) → inj₂ (Divergent-bind-left (λ a' → Ret (h a')) W-div)
    (inj₁ (W' , W-weak , W'⊑c , W'⊑Dc)) →
      let k = λ (a' : _) → Ret (h a')
          ts = make-tail-sim-from-W-ref-c W' _ sim-rec W'⊑c W'⊑Dc
          W-bind-weak : (body a >>= k) ═[ ev _ ]═► (W' >>= k)
          W-bind-weak = case W-weak of λ { (weak-ev pre₁ step₁ post₁) →
              weak-ev (bind-left-τ* k pre₁)
                      (lift-bind-step-ev _ k step₁)
                      (bind-left-τ* k post₁) }
      in inj₁ (W' >>= k , W-bind-weak , ts)

-- `tail-on-vis-sVis-Y`: real definition (moved from before Tail-Sim-deadlock).
-- Case-splits on Y's force shape; only `vis f'` is live.
tail-on-vis-sVis-Y {Y = Y} a bF⊑Y bD⊑Y sim-rec {at = at} {a-evt = a-evt}
                     eq-f eq-j
    with Y .force in Y-eq | eq-f
... | ret _        | ()
... | sil _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | ()
... | vis f'       | refl
    with f' at a-evt in f-eq | eq-j
...   | nothing | ()
...   | just _  | refl =
        tail-on-vis-sVis-body-vis-Y a bF⊑Y bD⊑Y sim-rec Y-eq f-eq

-- `tail-on-vis-sMixVis-Y`: real definition (moved from before Tail-Sim-deadlock).
-- Case-splits on Y's force shape; only `mix f' Qt'` is live.
tail-on-vis-sMixVis-Y {Y = Y} a bF⊑Y bD⊑Y sim-rec {at = at} {a-evt = a-evt}
                       eq-f eq-j
    with Y .force in Y-eq | eq-f
... | ret _        | ()
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix f' _     | refl
    with f' at a-evt in f-eq | eq-j
...   | nothing | ()
...   | just _  | refl =
        tail-on-vis-sMixVis-body-mix-Y a bF⊑Y bD⊑Y sim-rec Y-eq f-eq

-- `tail-on-vis-sRet-body-ret`: discharge the iteration-boundary tick
-- case.  body' a returns `ret a-prime`; we need the body a tail to
-- emit a `√ (inj₁ a-prime)` tick to deadlock (or diverge).
--
-- Pipeline (mirrors the sibling `tail-on-ret-inj₁-construct`):
--   1. Build a body' a failure at trace [√ a-prime] ending at
--      deadlock, with vacuous refusal `λ _ → Lift ℓB ⊥`.
--   2. Apply `bF⊑ a` to get a body a failure-or-divergence at the
--      same trace.
--   3. Failure arm: `tick-bigstep-lands-at-deadlock` forces W ≡
--      deadlock; `lift-bind-bigstep-tick` lifts the body-a tick
--      bigstep through bind, yielding a state P-bind with
--      `force P-bind ≡ ret (inj₁ a-prime)`.  Build a weak-event
--      step `(body a >>= k) ═[ ev (√(inj₁ a-prime)) ]═► deadlock`
--      via τ*-prefix → sRet → τ*-zero.  Tail-Sim deadlock deadlock
--      closes via `Tail-Sim-deadlock`.
--   4. Divergence arm: split the divergence prefix; either body a
--      diverges along the empty prefix (lift through bind) or the
--      witness lands at deadlock (absurd, contradicts Divergent).
tail-on-vis-sRet-body-ret
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {a' : A}
    → ITree.force (body' a) ≡ ret a'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a-in → Ret (h a-in)))
            ═[ ev (√ (h a')) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
    ⊎ Divergent (body a >>= (λ a-in → Ret (h a-in)))
tail-on-vis-sRet-body-ret {ℓB = ℓB} {I = I} {A = A} {R = R}
                           {body = body} {body' = body'} {h = h}
                           bF⊑ bD⊑ sim-rec a {a-prime} body'-eq =
    dispatch (bF⊑ a (inj₁ (deadlock , bs-body' , deadlock-ref)))
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a-in → Ret (h a-in)

    bs-body' : body' a ═⟨ √ a-prime ∷ [] ⟩═► deadlock
    bs-body' = bStep (sRet body'-eq) bNil

    handle-failure
      : Σ[ W ∈ ITree E (ExtI I) A ]
        ( body a ═⟨ √ a-prime ∷ [] ⟩═► W
        × W ref (λ _ → Lift ℓB ⊥))
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ═[ ev (√ (h a-prime)) ]═► X'
          × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
      ⊎ Divergent (body a >>= k)
    handle-failure (W , bs-W , _) =
      let W-eq : W ≡ deadlock
          W-eq = tick-bigstep-lands-at-deadlock {s1 = []} bs-W
          bs-W-dl : body a ═⟨ √ a-prime ∷ [] ⟩═► deadlock
          bs-W-dl = subst (λ X → body a ═⟨ √ a-prime ∷ [] ⟩═► X) W-eq bs-W
          lift-bind = lift-bind-bigstep-tick (body a) k [] bs-W-dl
          P-bind = proj₁ lift-bind
          bs-empty : (body a >>= k) ═⟨ [] ⟩═► P-bind
          bs-empty = proj₁ (proj₂ lift-bind)
          f-eq : ITree.force P-bind ≡ ret (h a-prime)
          f-eq = proj₂ (proj₂ lift-bind)
          τ*-pre : (body a >>= k) ─[τ*]─► P-bind
          τ*-pre = bigstep-empty-to-τ* bs-empty
          sRet-step : P-bind ─[ ev (√ (h a-prime)) ]─► deadlock
          sRet-step = sRet f-eq
          weak : (body a >>= k) ═[ ev (√ (h a-prime)) ]═► deadlock
          weak = weak-ev τ*-pre sRet-step τ*-zero
      in inj₁ (deadlock , weak , Tail-Sim-deadlock)

    handle-divergence
      : divergences (body a) (√ a-prime ∷ [])
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ═[ ev (√ (h a-prime)) ]═► X'
          × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
      ⊎ Divergent (body a >>= k)
    handle-divergence d-body =
      case prefix-tick-split [] {r = a-prime}
              (d-body .IsDivergence.prefix)
              (d-body .IsDivergence.suffix)
              (sym (d-body .IsDivergence.split))
          of λ where
        (inj₁ (pre0 , suf0 , s1-eq , pre-eq , _)) →
          let pre0-eq : pre0 ≡ []
              pre0-eq = split-empty-l s1-eq
              prefix-eq : d-body .IsDivergence.prefix ≡ []
              prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
              reach-at-[] : body a ═⟨ [] ⟩═► d-body .IsDivergence.witness
              reach-at-[] =
                subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                      prefix-eq
                      (d-body .IsDivergence.reach)
              div-body : Divergent (body a)
              div-body = divergent-prefix
                           (bigstep-empty-to-τ* reach-at-[])
                           (d-body .IsDivergence.divwit)
          in inj₂ (Divergent-bind-left k div-body)
        (inj₂ (pre-eq , _)) →
          let bs-to-W : body a ═⟨ √ a-prime ∷ [] ⟩═►
                          d-body .IsDivergence.witness
              bs-to-W =
                subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                      pre-eq
                      (d-body .IsDivergence.reach)
              W-dl : d-body .IsDivergence.witness ≡ deadlock
              W-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-to-W
          in ⊥-elim (Divergent-deadlock-absurd
                       (subst Divergent W-dl
                              (d-body .IsDivergence.divwit)))

    dispatch
      : failures⊥ (body a) (√ a-prime ∷ []) (λ _ → Lift ℓB ⊥)
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ═[ ev (√ (h a-prime)) ]═► X'
          × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
      ⊎ Divergent (body a >>= k)
    dispatch (inj₁ f-trip) = handle-failure f-trip
    dispatch (inj₂ d-body) = handle-divergence d-body

-- `tail-on-vis-sRet-body-ret-Y`: Y-parameterised sibling of
-- `tail-on-vis-sRet-body-ret`.  Same proof structure, with body' a
-- replaced by arbitrary Y and bF⊑ a / bD⊑ a replaced by direct
-- (body a) ⊑F⊥ Y / (body a) ⊑D Y hypotheses.
tail-on-vis-sRet-body-ret-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {a' : A}
    → ITree.force Y ≡ ret a'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a-in → Ret (h a-in)))
            ═[ ev (√ (h a')) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
    ⊎ Divergent (body a >>= (λ a-in → Ret (h a-in)))
tail-on-vis-sRet-body-ret-Y {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h} {Y = Y}
                              a bF⊑Y bD⊑Y sim-rec {a-prime} Y-eq =
    dispatch (bF⊑Y (inj₁ (deadlock , bs-Y , deadlock-ref)))
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a-in → Ret (h a-in)

    bs-Y : Y ═⟨ √ a-prime ∷ [] ⟩═► deadlock
    bs-Y = bStep (sRet Y-eq) bNil

    handle-failure
      : Σ[ W ∈ ITree E (ExtI I) A ]
        ( body a ═⟨ √ a-prime ∷ [] ⟩═► W
        × W ref (λ _ → Lift ℓB ⊥))
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ═[ ev (√ (h a-prime)) ]═► X'
          × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
      ⊎ Divergent (body a >>= k)
    handle-failure (W , bs-W , _) =
      let W-eq : W ≡ deadlock
          W-eq = tick-bigstep-lands-at-deadlock {s1 = []} bs-W
          bs-W-dl : body a ═⟨ √ a-prime ∷ [] ⟩═► deadlock
          bs-W-dl = subst (λ X → body a ═⟨ √ a-prime ∷ [] ⟩═► X) W-eq bs-W
          lift-bind = lift-bind-bigstep-tick (body a) k [] bs-W-dl
          P-bind = proj₁ lift-bind
          bs-empty : (body a >>= k) ═⟨ [] ⟩═► P-bind
          bs-empty = proj₁ (proj₂ lift-bind)
          f-eq : ITree.force P-bind ≡ ret (h a-prime)
          f-eq = proj₂ (proj₂ lift-bind)
          τ*-pre : (body a >>= k) ─[τ*]─► P-bind
          τ*-pre = bigstep-empty-to-τ* bs-empty
          sRet-step : P-bind ─[ ev (√ (h a-prime)) ]─► deadlock
          sRet-step = sRet f-eq
          weak : (body a >>= k) ═[ ev (√ (h a-prime)) ]═► deadlock
          weak = weak-ev τ*-pre sRet-step τ*-zero
      in inj₁ (deadlock , weak , Tail-Sim-deadlock)

    handle-divergence
      : divergences (body a) (√ a-prime ∷ [])
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ═[ ev (√ (h a-prime)) ]═► X'
          × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
      ⊎ Divergent (body a >>= k)
    handle-divergence d-body =
      case prefix-tick-split [] {r = a-prime}
              (d-body .IsDivergence.prefix)
              (d-body .IsDivergence.suffix)
              (sym (d-body .IsDivergence.split))
          of λ where
        (inj₁ (pre0 , suf0 , s1-eq , pre-eq , _)) →
          let pre0-eq : pre0 ≡ []
              pre0-eq = split-empty-l s1-eq
              prefix-eq : d-body .IsDivergence.prefix ≡ []
              prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
              reach-at-[] : body a ═⟨ [] ⟩═► d-body .IsDivergence.witness
              reach-at-[] =
                subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                      prefix-eq
                      (d-body .IsDivergence.reach)
              div-body : Divergent (body a)
              div-body = divergent-prefix
                           (bigstep-empty-to-τ* reach-at-[])
                           (d-body .IsDivergence.divwit)
          in inj₂ (Divergent-bind-left k div-body)
        (inj₂ (pre-eq , _)) →
          let bs-to-W : body a ═⟨ √ a-prime ∷ [] ⟩═►
                          d-body .IsDivergence.witness
              bs-to-W =
                subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                      pre-eq
                      (d-body .IsDivergence.reach)
              W-dl : d-body .IsDivergence.witness ≡ deadlock
              W-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-to-W
          in ⊥-elim (Divergent-deadlock-absurd
                       (subst Divergent W-dl
                              (d-body .IsDivergence.divwit)))

    dispatch
      : failures⊥ (body a) (√ a-prime ∷ []) (λ _ → Lift ℓB ⊥)
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ═[ ev (√ (h a-prime)) ]═► X'
          × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
      ⊎ Divergent (body a >>= k)
    dispatch (inj₁ f-trip) = handle-failure f-trip
    dispatch (inj₂ d-body) = handle-divergence d-body

-- `tail-on-vis-sRet`: dispatcher.  Case-splits on body' a's force
-- shape.  Only `ret a'` is live (other shapes make the bind's force
-- non-`ret`, contradicting eq-f via `()`).  In the live arm, the
-- bind reduces to `ret (inj₁ a')`, unifying x with `inj₁ a'` via
-- `refl`, and routes to the narrower postulate.
tail-on-vis-sRet
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {x : A ⊎ R}
    → ITree.force (body' a >>= (λ a' → Ret (h a'))) ≡ ret x
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a')))
            ═[ ev (√ x) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-vis-sRet {I = I} {A = A} {R = R} {body = body} {body' = body'} {h = h}
                  bF⊑ bD⊑ sim-rec a {x = x} eq-f
    with body' a .force in body'-eq | eq-f
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | ()
... | ret a-val    | cbeq =
      -- force(body' a >>= k) = ret (h a-val), cbeq : ret (h a-val) ≡ ret x;
      -- build at payload h a-val and transport to x.
      subst (λ z → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                     ( (body a >>= (λ a' → Ret (h a'))) ═[ ev (√ z) ]═► X'
                     × Tail-Sim {ℓB = _} {body = body} {body' = body'}
                                X' deadlock ) )
                   ⊎ Divergent (body a >>= (λ a' → Ret (h a'))))
            (ret-inj cbeq)
            (tail-on-vis-sRet-body-ret bF⊑ bD⊑ sim-rec a body'-eq)
  where
    ret-inj : ∀ {a-val : A} {z : A ⊎ R}
            → ret {E = E} {I = ExtI I} (h a-val) ≡ ret z → h a-val ≡ z
    ret-inj refl = refl

-- `tail-on-vis-sRet-Y`: Y-parameterised sibling dispatcher.  Case-
-- splits on Y's force shape; only `ret a'` is live.  Routes the live
-- arm to `tail-on-vis-sRet-body-ret-Y`.
tail-on-vis-sRet-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {x : A ⊎ R}
    → ITree.force (Y >>= (λ a' → Ret (h a'))) ≡ ret x
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a')))
            ═[ ev (√ x) ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' deadlock ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-vis-sRet-Y {I = I} {A = A} {R = R} {body = body} {body' = body'} {h = h} {Y = Y}
                    a bF⊑Y bD⊑Y sim-rec {x = x} eq-f
    with Y .force in Y-eq | eq-f
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | ()
... | ret a-val    | cbeq =
      subst (λ z → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                     ( (body a >>= (λ a' → Ret (h a'))) ═[ ev (√ z) ]═► X'
                     × Tail-Sim {ℓB = _} {body = body} {body' = body'}
                                X' deadlock ) )
                   ⊎ Divergent (body a >>= (λ a' → Ret (h a'))))
            (ret-inj cbeq)
            (tail-on-vis-sRet-body-ret-Y a bF⊑Y bD⊑Y sim-rec Y-eq)
  where
    ret-inj : ∀ {a-val : A} {z : A ⊎ R}
            → ret {E = E} {I = ExtI I} (h a-val) ≡ ret z → h a-val ≡ z
    ret-inj refl = refl

-- `tail-on-vis-construct`: dispatcher.  Pattern-matches on the
-- visible-event step constructor (sVis / sMixVis / sRet) and routes
-- to the matching per-shape postulate above.
tail-on-vis-construct
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {e : Event√ E (A ⊎ R)} {Y' : ITree E (ExtI I) (A ⊎ R)}
    → (body' a >>= (λ a' → Ret (h a'))) ─[ ev e ]─► Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ═[ ev e ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-vis-construct bF⊑ bD⊑ sim-rec a (sVis eq-f eq-j) =
    tail-on-vis-sVis    bF⊑ bD⊑ sim-rec a eq-f eq-j
tail-on-vis-construct bF⊑ bD⊑ sim-rec a (sMixVis eq-f eq-j) =
    tail-on-vis-sMixVis bF⊑ bD⊑ sim-rec a eq-f eq-j
tail-on-vis-construct bF⊑ bD⊑ sim-rec a (sRet eq-f) =
    tail-on-vis-sRet    bF⊑ bD⊑ sim-rec a eq-f

-- `tail-on-vis-construct-Y`: Y-parameterised sibling dispatcher.
-- Pattern-matches on the visible-event step constructor and routes
-- to the matching `-Y` per-shape dispatcher.
tail-on-vis-construct-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {e : Event√ E (A ⊎ R)} {Y' : ITree E (ExtI I) (A ⊎ R)}
    → (Y >>= (λ a' → Ret (h a'))) ─[ ev e ]─► Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a' → Ret (h a'))) ═[ ev e ]═► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-vis-construct-Y a bF⊑Y bD⊑Y sim-rec (sVis eq-f eq-j) =
    tail-on-vis-sVis-Y    a bF⊑Y bD⊑Y sim-rec eq-f eq-j
tail-on-vis-construct-Y a bF⊑Y bD⊑Y sim-rec (sMixVis eq-f eq-j) =
    tail-on-vis-sMixVis-Y a bF⊑Y bD⊑Y sim-rec eq-f eq-j
tail-on-vis-construct-Y a bF⊑Y bD⊑Y sim-rec (sRet eq-f) =
    tail-on-vis-sRet-Y    a bF⊑Y bD⊑Y sim-rec eq-f

-- Forward declaration: `bF⊑+bD⊑→Tail-Sim-Y` (full body at the end of
-- this section) builds Tail-Sim between body-tails of `body a` and an
-- arbitrary `Y`.  Used below to discharge the three τ-side body-tail
-- postulates via τ-closure: when body' a τ-steps to its successor Y,
-- `⊑F⊥-τ-step-right` / `⊑D-τ-step-right` carry the refinement
-- hypotheses across the τ, and `bF⊑+bD⊑→Tail-Sim-Y` builds the
-- continuation Tail-Sim at Y.
bF⊑+bD⊑→Tail-Sim-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
                (body a >>= (λ a' → Ret (h a')))
                (Y      >>= (λ a' → Ret (h a')))

-- `tail-on-tau-construct` is split into three per-shape narrow
-- postulates (sSil / sNdbr / sMixSlide) mirroring the split in
-- `construct-on-tau`.  The dispatcher below pattern-matches on the
-- τ-step constructor and routes to the matching per-shape postulate;
-- each can be discharged independently in subsequent sessions.
--
-- `tail-on-tau-sSil-body-sil`: discharged via τ-closure of the
-- refinement hypotheses through `body' a ─[τ]─► c` (constructed from
-- `body'-eq` via `sSil`), then `bF⊑+bD⊑→Tail-Sim-Y` builds the
-- continuation Tail-Sim at Y = c.  The body a side takes zero τ-steps
-- (X' = body a >>= k', τ*-zero).
tail-on-tau-sSil-body-sil
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {c : ITree E (ExtI I) A}
    → ITree.force (body' a) ≡ sil c
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
            X' (c >>= (λ a' → Ret (h a'))) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-tau-sSil-body-sil {body = body} {h = h} bF⊑ bD⊑ sim-rec a {c = c} body'-eq =
  let τ-step = sSil body'-eq
      bF⊑-c = ⊑F⊥-τ-step-right τ-step (bF⊑ a)
      bD⊑-c = ⊑D-τ-step-right  τ-step (bD⊑ a)
      ts-c  = bF⊑+bD⊑→Tail-Sim-Y {Y = c} a bF⊑-c bD⊑-c sim-rec
  in inj₁ (body a >>= (λ a' → Ret (h a')) , τ*-zero , ts-c)

-- The Y-parameterised sibling of `tail-on-tau-sSil-body-sil` was
-- previously postulated here (a self-recursive discharge via
-- `bF⊑+bD⊑→Tail-Sim-Y` failed Agda's productivity check through the
-- helper chain).  Resolved by inlining the τ-side dispatch directly
-- into `bF⊑+bD⊑→Tail-Sim-Y`'s `.on-tau` copattern clauses (see
-- bottom of this section).  The dispatcher chain and per-shape
-- `-Y` postulates are no longer needed.

-- `tail-on-tau-sSil`: dispatcher.  Case-splits on body' a's force
-- shape.  Only `sil c` is live (other shapes make the bind's force
-- non-`sil`, contradicting eq-f via `()`).  The live arm routes to
-- the narrower postulate above.
tail-on-tau-sSil
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {Y' : ITree E (ExtI I) (A ⊎ R)}
    → ITree.force (body' a >>= (λ a' → Ret (h a'))) ≡ sil Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-tau-sSil {body' = body'} {h = h} bF⊑ bD⊑ sim-rec a eq-f
    with body' a .force in body'-eq | eq-f
... | ret _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | ()
... | sil _        | refl =
      tail-on-tau-sSil-body-sil bF⊑ bD⊑ sim-rec a body'-eq

-- `tail-on-tau-sNdbr-body-ndbr`: discharged the same way as
-- `tail-on-tau-sSil-body-sil` — τ-step `sNdbr body'-eq f-eq` realises
-- the branch step `body' a ─[τ]─► c`, then τ-closure + `Tail-Sim-Y`.
tail-on-tau-sNdbr-body-ndbr
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f' : (ai : AnyTypes (ExtI I))
              → ContinueType ai (Maybe (ITree E (ExtI I) A))}
        {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp' : Is-just (f' wi wa)}
        {i : AnyTypes (ExtI I)} {ai : proj₁ i}
        {c : ITree E (ExtI I) A}
    → ITree.force (body' a) ≡ ndbr f' wi wa wp'
    → f' i ai ≡ just c
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
            X' (c >>= (λ a' → Ret (h a'))) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-tau-sNdbr-body-ndbr {body = body} {h = h} bF⊑ bD⊑ sim-rec a {c = c}
                              body'-eq f-eq =
  let τ-step = sNdbr body'-eq f-eq
      bF⊑-c = ⊑F⊥-τ-step-right τ-step (bF⊑ a)
      bD⊑-c = ⊑D-τ-step-right  τ-step (bD⊑ a)
      ts-c  = bF⊑+bD⊑→Tail-Sim-Y {Y = c} a bF⊑-c bD⊑-c sim-rec
  in inj₁ (body a >>= (λ a' → Ret (h a')) , τ*-zero , ts-c)

-- `tail-on-tau-sNdbr`: dispatcher.  Case-splits on body' a's force
-- shape.  Only `ndbr f' wi' wa' wp'` is live (other shapes make the
-- bind's force non-`ndbr`, contradicting eq-f via `()`).  Inside the
-- ndbr arm, further case-splits on `f' i ai`: `nothing` makes
-- bind-cont-ndbr return `nothing`, contradicting eq-j; `just c`
-- unifies Y' with `c >>= k'` and routes to the narrower postulate.
tail-on-tau-sNdbr
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f : (ai : AnyTypes (ExtI I))
             → ContinueType ai (Maybe (ITree E (ExtI I) (A ⊎ R)))}
        {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (f wi wa)}
        {i : AnyTypes (ExtI I)} {ai : proj₁ i}
        {Y' : ITree E (ExtI I) (A ⊎ R)}
    → ITree.force (body' a >>= (λ a' → Ret (h a')))
        ≡ ndbr f wi wa wp
    → f i ai ≡ just Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-tau-sNdbr {body' = body'} {h = h} bF⊑ bD⊑ sim-rec a {i = i} {ai = ai} eq-f eq-j
    with body' a .force in body'-eq | eq-f
... | ret _   | ()
... | sil _   | ()
... | vis _   | ()
... | mix _ _ | ()
... | ndbr f' _ _ _ | refl
    with f' i ai in f-eq | eq-j
...   | nothing | ()
...   | just _  | refl =
        tail-on-tau-sNdbr-body-ndbr bF⊑ bD⊑ sim-rec a body'-eq f-eq

-- `tail-on-tau-sMixSlide-body-mix`: discharged via the same recipe —
-- `sMixSlide body'-eq` builds `body' a ─[τ]─► Qt'`, τ-closure carries
-- bF⊑/bD⊑ to Y = Qt', then `Tail-Sim-Y` assembles the continuation.
tail-on-tau-sMixSlide-body-mix
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) A))}
        {Qt' : ITree E (ExtI I) A}
    → ITree.force (body' a) ≡ mix f' Qt'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
            X' (Qt' >>= (λ a' → Ret (h a'))) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-tau-sMixSlide-body-mix {body = body} {h = h} bF⊑ bD⊑ sim-rec a {Qt' = Qt'}
                                 body'-eq =
  let τ-step  = sMixSlide body'-eq
      bF⊑-Qt' = ⊑F⊥-τ-step-right τ-step (bF⊑ a)
      bD⊑-Qt' = ⊑D-τ-step-right  τ-step (bD⊑ a)
      ts-Qt'  = bF⊑+bD⊑→Tail-Sim-Y {Y = Qt'} a bF⊑-Qt' bD⊑-Qt' sim-rec
  in inj₁ (body a >>= (λ a' → Ret (h a')) , τ*-zero , ts-Qt')

-- `tail-on-tau-sMixSlide`: dispatcher.  Case-splits on body' a's force
-- shape.  Only `mix f' Qt'` is live (other shapes make the bind's
-- force non-`mix`, contradicting eq-f via `()`).  The live arm
-- unifies Y' with `Qt' >>= k'` via `refl` and routes to the narrower
-- postulate.
tail-on-tau-sMixSlide
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f : (at : AnyTypes E)
             → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))}
        {Y' : ITree E (ExtI I) (A ⊎ R)}
    → ITree.force (body' a >>= (λ a' → Ret (h a'))) ≡ mix f Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-tau-sMixSlide {body' = body'} {h = h} bF⊑ bD⊑ sim-rec a eq-f
    with body' a .force in body'-eq | eq-f
... | ret _        | ()
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | refl =
      tail-on-tau-sMixSlide-body-mix bF⊑ bD⊑ sim-rec a body'-eq

-- `tail-on-tau-construct`: dispatcher.  Pattern-matches on the τ-step
-- constructor (sSil / sNdbr / sMixSlide) and routes to the matching
-- per-shape postulate above.  No body'-force sub-dispatch is needed
-- here — each τ-step constructor uniquely determines Y's force shape.
tail-on-tau-construct
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {Y' : ITree E (ExtI I) (A ⊎ R)}
    → (body' a >>= (λ a' → Ret (h a'))) ─[ τ ]─► Y'
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X' Y' ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-tau-construct bF⊑ bD⊑ sim-rec a (sSil eq-f) =
    tail-on-tau-sSil      bF⊑ bD⊑ sim-rec a eq-f
tail-on-tau-construct bF⊑ bD⊑ sim-rec a (sNdbr eq-f eq-j) =
    tail-on-tau-sNdbr     bF⊑ bD⊑ sim-rec a eq-f eq-j
tail-on-tau-construct bF⊑ bD⊑ sim-rec a (sMixSlide eq-f) =
    tail-on-tau-sMixSlide bF⊑ bD⊑ sim-rec a eq-f

-- `tail-on-ret-inj₂-construct`: real exit boundary.  With generic `h`,
-- force(body' a >>= k) ≡ ret (inj₂ r) forces body' a .force = ret a-val
-- with h a-val = inj₂ r.  body a refines body' a, so it bigsteps a
-- √ a-val tick to deadlock (or diverges); lift through bind to land
-- (body a >>= k) at ret (h a-val) ≡ ret (inj₂ r).  Mirrors the failure/
-- divergence dispatch of `tail-on-ret-inj₁-construct`.
tail-on-ret-inj₂-construct
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {r : R}
    → ITree.force (body' a >>= (λ a' → Ret (h a')))
        ≡ ret (inj₂ r)
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × ITree.force X' ≡ ret (inj₂ r) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-ret-inj₂-construct {ℓB = ℓB} {I = I} {A = A} {R = R}
                            {body = body} {body' = body'} {h = h}
                            bF⊑ bD⊑ sim-rec a {r} eq-Y
    with body' a .force in body'-eq
... | sil _        = case eq-Y of λ ()
... | vis _        = case eq-Y of λ ()
... | ndbr _ _ _ _ = case eq-Y of λ ()
... | mix _ _      = case eq-Y of λ ()
... | ret a-val
    with h a-val in hav-eq | eq-Y
...   | inj₁ _    | ()
...   | inj₂ r'   | refl =
    dispatch (bF⊑ a (inj₁ (deadlock , bs-body' , deadlock-ref)))
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a' → Ret (h a')
    X'-force-eq : ∀ {X' : ITree E (ExtI I) (A ⊎ R)}
                → ITree.force X' ≡ ret (h a-val)
                → ITree.force X' ≡ ret (inj₂ r')
    X'-force-eq {X'} fe = trans fe (cong (ret {E = E} {I = ExtI I}) hav-eq)
    bs-body' : body' a ═⟨ √ a-val ∷ [] ⟩═► deadlock
    bs-body' = bStep (sRet body'-eq) bNil
    handle-failure
      : Σ[ W ∈ ITree E (ExtI I) A ]
        ( body a ═⟨ √ a-val ∷ [] ⟩═► W × W ref (λ _ → Lift ℓB ⊥))
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₂ r') ) )
      ⊎ Divergent (body a >>= k)
    handle-failure (W , bs-W , _) =
      let W-eq   = tick-bigstep-lands-at-deadlock {s1 = []} bs-W
          bs-dl  = subst (λ Z → body a ═⟨ √ a-val ∷ [] ⟩═► Z) W-eq bs-W
          lb     = lift-bind-bigstep-tick (body a) k [] bs-dl
          X'     = proj₁ lb
      in inj₁ ( X'
              , bigstep-empty-to-τ* (proj₁ (proj₂ lb))
              , X'-force-eq {X' = X'} (proj₂ (proj₂ lb)) )
    handle-divergence
      : divergences (body a) (√ a-val ∷ [])
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₂ r') ) )
      ⊎ Divergent (body a >>= k)
    handle-divergence d-body =
      case prefix-tick-split [] {r = a-val}
              (d-body .IsDivergence.prefix)
              (d-body .IsDivergence.suffix)
              (sym (d-body .IsDivergence.split))
          of λ where
        (inj₁ (pre0 , _ , s1-eq , pre-eq , _)) →
          let pre0-eq  = split-empty-l s1-eq
              prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
              reach-[]  = subst (λ s → body a ═⟨ s ⟩═► d-body .IsDivergence.witness)
                                prefix-eq (d-body .IsDivergence.reach)
              div-body = divergent-prefix (bigstep-empty-to-τ* reach-[])
                          (d-body .IsDivergence.divwit)
          in inj₂ (Divergent-bind-left k div-body)
        (inj₂ (pre-eq , _)) →
          let bs-to-W = subst (λ s → body a ═⟨ s ⟩═► d-body .IsDivergence.witness)
                              pre-eq (d-body .IsDivergence.reach)
              W-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-to-W
          in ⊥-elim (Divergent-deadlock-absurd
                       (subst Divergent W-dl (d-body .IsDivergence.divwit)))
    dispatch : failures⊥ (body a) (√ a-val ∷ []) (λ _ → Lift ℓB ⊥)
             → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                 ( (body a >>= k) ─[τ*]─► X'
                 × ITree.force X' ≡ ret (inj₂ r') ) )
             ⊎ Divergent (body a >>= k)
    dispatch (inj₁ f-trip) = handle-failure f-trip
    dispatch (inj₂ d-body) = handle-divergence d-body

-- `tail-on-ret-inj₂-construct-Y`: Y-parameterised sibling.  Mirrors
-- `tail-on-ret-inj₂-construct` with `body' a` → `Y`.  Structurally
-- absurd in the same way (all five force-shapes of Y reduce the
-- bind's force away from `ret (inj₂ r)`).
tail-on-ret-inj₂-construct-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {r : R}
    → ITree.force (Y >>= (λ a' → Ret (h a')))
        ≡ ret (inj₂ r)
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × ITree.force X' ≡ ret (inj₂ r) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-ret-inj₂-construct-Y {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h} {Y = Y}
                              a bF⊑Y bD⊑Y sim-rec {r} eq-Y
    with Y .force in Y-eq
... | sil _        = case eq-Y of λ ()
... | vis _        = case eq-Y of λ ()
... | ndbr _ _ _ _ = case eq-Y of λ ()
... | mix _ _      = case eq-Y of λ ()
... | ret a-val
    with h a-val in hav-eq | eq-Y
...   | inj₁ _    | ()
...   | inj₂ r'   | refl =
    dispatch (bF⊑Y (inj₁ (deadlock , bs-Y , deadlock-ref)))
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a' → Ret (h a')
    X'-force-eq : ∀ {X' : ITree E (ExtI I) (A ⊎ R)}
                → ITree.force X' ≡ ret (h a-val)
                → ITree.force X' ≡ ret (inj₂ r')
    X'-force-eq {X'} fe = trans fe (cong (ret {E = E} {I = ExtI I}) hav-eq)
    bs-Y : Y ═⟨ √ a-val ∷ [] ⟩═► deadlock
    bs-Y = bStep (sRet Y-eq) bNil
    handle-failure
      : Σ[ W ∈ ITree E (ExtI I) A ]
        ( body a ═⟨ √ a-val ∷ [] ⟩═► W × W ref (λ _ → Lift ℓB ⊥))
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₂ r') ) )
      ⊎ Divergent (body a >>= k)
    handle-failure (W , bs-W , _) =
      let W-eq   = tick-bigstep-lands-at-deadlock {s1 = []} bs-W
          bs-dl  = subst (λ Z → body a ═⟨ √ a-val ∷ [] ⟩═► Z) W-eq bs-W
          lb     = lift-bind-bigstep-tick (body a) k [] bs-dl
          X'     = proj₁ lb
      in inj₁ ( X'
              , bigstep-empty-to-τ* (proj₁ (proj₂ lb))
              , X'-force-eq {X' = X'} (proj₂ (proj₂ lb)) )
    handle-divergence
      : divergences (body a) (√ a-val ∷ [])
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₂ r') ) )
      ⊎ Divergent (body a >>= k)
    handle-divergence d-body =
      case prefix-tick-split [] {r = a-val}
              (d-body .IsDivergence.prefix)
              (d-body .IsDivergence.suffix)
              (sym (d-body .IsDivergence.split))
          of λ where
        (inj₁ (pre0 , _ , s1-eq , pre-eq , _)) →
          let pre0-eq  = split-empty-l s1-eq
              prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
              reach-[]  = subst (λ s → body a ═⟨ s ⟩═► d-body .IsDivergence.witness)
                                prefix-eq (d-body .IsDivergence.reach)
              div-body = divergent-prefix (bigstep-empty-to-τ* reach-[])
                          (d-body .IsDivergence.divwit)
          in inj₂ (Divergent-bind-left k div-body)
        (inj₂ (pre-eq , _)) →
          let bs-to-W = subst (λ s → body a ═⟨ s ⟩═► d-body .IsDivergence.witness)
                              pre-eq (d-body .IsDivergence.reach)
              W-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-to-W
          in ⊥-elim (Divergent-deadlock-absurd
                       (subst Divergent W-dl (d-body .IsDivergence.divwit)))
    dispatch : failures⊥ (body a) (√ a-val ∷ []) (λ _ → Lift ℓB ⊥)
             → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
                 ( (body a >>= k) ─[τ*]─► X'
                 × ITree.force X' ≡ ret (inj₂ r') ) )
             ⊎ Divergent (body a >>= k)
    dispatch (inj₁ f-trip) = handle-failure f-trip
    dispatch (inj₂ d-body) = handle-divergence d-body

-- `tail-on-div-construct`: lift divergence from body' a >>= k to
-- body a >>= k.  Chain:
--   1. Strip pure-Ret continuation: Divergent (body' a >>= k) →
--      Divergent (body' a)   via  Divergent-bind-pure-ret-inv inj₁
--      (k = λ a' → Ret (h a') has no τ-outgoing).
--   2. Lift body' to body via bD⊑ a: wrap as IsDivergence (body' a) []
--      with the trivial bNil bigstep and the body' divergence as
--      divwit; apply bD⊑ a; obtain IsDivergence (body a) [].
--   3. Extract Divergent (body a): from [] ≡ prefix ++ suffix conclude
--      prefix ≡ [] (split-empty-l), transport the prefix-reach onto
--      a bigstep at [], chain via divergent-prefix.
--   4. Lift back through bind: Divergent-bind-left.
tail-on-div-construct
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
    → Divergent (body' a >>= (λ a' → Ret (h a')))
    → Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-div-construct {R = R} {body = body} {body' = body'} {h = h}
                       bF⊑ bD⊑ sim-rec a div-bind =
  let div-body' : Divergent (body' a)
      div-body' = Divergent-bind-pure-ret-inv h div-bind

      is-div-body' : IsDivergence (body' a) []
      is-div-body' = record
        { prefix  = []
        ; suffix  = []
        ; split   = refl
        ; witness = body' a
        ; reach   = bNil
        ; divwit  = div-body'
        }

      is-div-body : IsDivergence (body a) []
      is-div-body = bD⊑ a is-div-body'

      prefix-≡-[] : is-div-body .IsDivergence.prefix ≡ []
      prefix-≡-[] = split-empty-l (is-div-body .IsDivergence.split)

      reach-at-[] : (body a) ═⟨ [] ⟩═► is-div-body .IsDivergence.witness
      reach-at-[] = subst (λ s* → (body a) ═⟨ s* ⟩═►
                                    is-div-body .IsDivergence.witness)
                          prefix-≡-[]
                          (is-div-body .IsDivergence.reach)

      div-body : Divergent (body a)
      div-body = divergent-prefix
                   (bigstep-empty-to-τ* reach-at-[])
                   (is-div-body .IsDivergence.divwit)
  in Divergent-bind-left (λ a' → Ret (h a')) div-body

-- `tail-on-div-construct-Y`: Y-parameterised sibling.  Mirrors
-- `tail-on-div-construct` with `body' a` → `Y` and direct refinement
-- hypothesis `body a ⊑D Y` (in place of `bD⊑ a`).
tail-on-div-construct-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → Divergent (Y >>= (λ a' → Ret (h a')))
    → Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-div-construct-Y {R = R} {body = body} {body' = body'} {h = h} {Y = Y}
                         a bF⊑Y bD⊑Y sim-rec div-bind =
  let div-Y : Divergent Y
      div-Y = Divergent-bind-pure-ret-inv h div-bind

      is-div-Y : IsDivergence Y []
      is-div-Y = record
        { prefix  = []
        ; suffix  = []
        ; split   = refl
        ; witness = Y
        ; reach   = bNil
        ; divwit  = div-Y
        }

      is-div-body : IsDivergence (body a) []
      is-div-body = bD⊑Y is-div-Y

      prefix-≡-[] : is-div-body .IsDivergence.prefix ≡ []
      prefix-≡-[] = split-empty-l (is-div-body .IsDivergence.split)

      reach-at-[] : (body a) ═⟨ [] ⟩═► is-div-body .IsDivergence.witness
      reach-at-[] = subst (λ s* → (body a) ═⟨ s* ⟩═►
                                    is-div-body .IsDivergence.witness)
                          prefix-≡-[]
                          (is-div-body .IsDivergence.reach)

      div-body : Divergent (body a)
      div-body = divergent-prefix
                   (bigstep-empty-to-τ* reach-at-[])
                   (is-div-body .IsDivergence.divwit)
  in Divergent-bind-left (λ a' → Ret (h a')) div-body

-- `tail-on-stable-ref-construct`: discharge via bF⊑ at trace `[]`.
--
-- Pipeline:
--   1.  Y = body' a >>= k with k = λ a' → Ret (h a'). `Y-stable`
--       forces `body' a .force ≡ vis fY`; other shapes contradict
--       `Y-stable` because bind-force inherits ret/sil/ndbr/mix.
--   2.  Lift the bind-level refusal back to a body-level refusal at
--       predicate `B*` where `B* (evl e) = B (evl e)` and `B* (√ a')
--       = ⊤` (so that `bF⊑`'s `ref-tick` arm is ruled out by ¬⊤).
--       For `evl e`: an ev-step from `body' a` lifts through bind via
--       `lift-bind-step-ev`, then `Y-no-ev` refutes it.  For `√ a'`:
--       `body' a` at vis cannot fire `sRet`, so the no-ev is vacuous.
--   3.  Apply `bF⊑ a` to `failures⊥ (body' a) [] B*` (built via
--       `inj₁`) → `failures⊥ (body a) [] B*`.
--   4.  Failure arm `(W , bs-W , ref-W)`:
--         * `ref-stable W-st no-ev-B*`: lift to `(W >>= k) ref B`.
--           `(W >>= k).force = vis (bind-cont-vis k fW)` so it is
--           stable; ev-steps invert back to `W`-steps via
--           `bind-cont-vis`-inversion.
--         * `ref-tick step ¬Bx`: `¬Bx tt` derives `⊥` because
--           `B* (√ x) = ⊤`.
--       The bigstep `bs-W : body a ═⟨ [] ⟩═► W` lifts to
--       `(body a >>= k) ═⟨ [] ⟩═► (W >>= k)` via `lift-bind-bigstep`,
--       then to a τ*-chain via `bigstep-empty-to-τ*`.
--   5.  Divergence arm: mirror `tail-on-div-construct` — extract
--       `Divergent (body a)`, then lift through bind via
--       `Divergent-bind-left`.
tail-on-stable-ref-construct
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {B : Event√ E (A ⊎ R) → Set ℓB}
    → isStable (body' a >>= (λ a' → Ret (h a')))
    → (∀ (e : Event√ E (A ⊎ R)) → B e
         → ∀ {Y' : ITree E (ExtI I) (A ⊎ R)}
         → ¬ (body' a >>= (λ a' → Ret (h a'))) ─[ ev e ]─► Y')
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × isStable X'
        × (∀ (e : Event√ E (A ⊎ R)) → B e
             → ∀ {X'' : ITree E (ExtI I) (A ⊎ R)}
             → ¬ X' ─[ ev e ]─► X'')) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-stable-ref-construct {ℓi = ℓi} {ℓr = ℓr} {ℓB = ℓB}
                              {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h}
                              bF⊑ bD⊑ sim-rec a {B = B} Y-stable Y-no-ev
    with body' a .force in body'-eq
... | ret _        = ⊥-elim Y-stable
... | sil _        = ⊥-elim Y-stable
... | ndbr _ _ _ _ = ⊥-elim Y-stable
... | mix _ _      = ⊥-elim Y-stable
... | vis fY       = dispatch-out (bF⊑ a (inj₁ body'-fail))
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a' → Ret (h a')

    -- Refusal predicate lifted to body's event type.  Visible events
    -- pass through unchanged; body ticks are always in B*, so the
    -- ref-tick arm of `bF⊑`'s output is structurally absurd.
    B* : Event√ E A → Set ℓB
    B* (evl e) = B (evl e)
    B* (√ _)   = ⊤ {ℓB}

    body'-stable : isStable (body' a)
    body'-stable = vis-isStable {P = body' a} body'-eq

    -- ev (evl e) step on body' a lifts to ev (evl e) step on
    -- (body' a >>= k); `Y-no-ev` refutes it.
    body'-no-ev-evl
      : ∀ (e : Event E) {Q' : ITree E (ExtI I) A}
      → B (evl e) → ¬ (body' a) ─[ ev (evl e) ]─► Q'
    body'-no-ev-evl e Be step =
        Y-no-ev (evl e) Be (lift-bind-step-ev (body' a) k step)

    -- Promote to B* refusal: evl via body'-no-ev-evl; √ a' is vacuous
    -- because body' a is vis-shaped (cannot fire sRet).
    body'-no-ev-B*
      : ∀ (e : Event√ E A) → B* e
      → ∀ {Q : ITree E (ExtI I) A}
      → ¬ (body' a) ─[ ev e ]─► Q
    body'-no-ev-B* (evl e) Be step = body'-no-ev-evl e Be step
    body'-no-ev-B* (√ _)   _   (sRet eq-ret) =
        case trans (sym body'-eq) eq-ret of λ ()

    body'-ref : (body' a) ref B*
    body'-ref = ref-stable body'-stable body'-no-ev-B*

    body'-fail : failures (body' a) [] B*
    body'-fail = body' a , bNil , body'-ref

    -- Invert an ev-step on (W >>= k) back to an ev (evl e') step on W.
    -- W is stable (vis-shaped) by assumption.
    invert-bind-step
      : ∀ {W : ITree E (ExtI I) A}
          {fW : (at : AnyTypes E)
                → ContinueType at (Maybe (ITree E (ExtI I) A))}
          {e : Event√ E (A ⊎ R)} {t : ITree E (ExtI I) (A ⊎ R)}
      → ITree.force W ≡ vis fW
      → (W >>= k) ─[ ev e ]─► t
      → Σ (Event E) λ e' → e ≡ evl e' ×
            Σ (ITree E (ExtI I) A) λ Q' → W ─[ ev (evl e') ]─► Q'
    invert-bind-step {W = W} {fW = fW} eq-W
                     (sVis {f = f'} {at = at} {a = a-evt} {t′ = tgt}
                           eq-f eq-j) =
        cont-inv (fW at a-evt) refl
      where
        f≡bcv : f' ≡ bind-cont-vis k fW
        f≡bcv = vis-injective
                  (trans (sym eq-f) (bind-force-vis W k eq-W))
        eq-j' : bind-cont-vis k fW at a-evt ≡ just tgt
        eq-j' = subst (λ g → g at a-evt ≡ just tgt) f≡bcv eq-j
        cont-inv : (m : Maybe (ITree E (ExtI I) A))
                 → fW at a-evt ≡ m
                 → Σ (Event E) λ e' →
                     evl (evLabel (proj₁ at) (proj₂ at) a-evt) ≡ evl e' ×
                     Σ (ITree E (ExtI I) A) λ Q' →
                       W ─[ ev (evl e') ]─► Q'
        cont-inv nothing  fia-eq =
            ⊥-elim
              (case trans (sym (bind-cont-vis-nothing k fW at a-evt fia-eq))
                          eq-j'
                    of λ ())
        cont-inv (just t′) fia-eq =
            evLabel (proj₁ at) (proj₂ at) a-evt , refl ,
            t′ , sVis eq-W fia-eq
    invert-bind-step {W = W} {fW = fW} eq-W (sMixVis eq-f _) =
        case trans (sym (bind-force-vis W k eq-W)) eq-f of λ ()
    invert-bind-step {W = W} {fW = fW} eq-W (sRet eq-f) =
        case trans (sym (bind-force-vis W k eq-W)) eq-f of λ ()

    -- Failure arm: route `(W , bs-W , ref-W)` directly, threading the
    -- bigstep through `lift-bind-bigstep` and the refusal through
    -- `invert-bind-step`.
    failure-arm
      : Σ[ W ∈ ITree E (ExtI I) A ]
          ( body a ═⟨ [] ⟩═► W × W ref B*)
      → Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body  a >>= k) ─[τ*]─► X'
          × isStable X'
          × (∀ (e : Event√ E (A ⊎ R)) → B e
               → ∀ {X''} → ¬ X' ─[ ev e ]─► X''))
    failure-arm (W , bs-W , ref-tick {x = x} _ ¬Bx) = ⊥-elim (¬Bx tt)
    failure-arm (W , bs-W , ref-stable W-st W-no-ev)
        with W .force in w-eq
    ... | vis fW =
            W >>= k
          , bigstep-empty-to-τ* (lift-bind-bigstep (body a) k [] bs-W)
          , vis-isStable {P = W >>= k} (bind-force-vis W k w-eq)
          , bind-no-ev
      where
        bind-no-ev : ∀ (e : Event√ E (A ⊎ R)) → B e
                   → ∀ {X''} → ¬ (W >>= k) ─[ ev e ]─► X''
        bind-no-ev e Be step with invert-bind-step w-eq step
        ... | e' , refl , Q' , step-W = W-no-ev (evl e') Be step-W
    ... | ret _        = ⊥-elim W-st
    ... | sil _        = ⊥-elim W-st
    ... | ndbr _ _ _ _ = ⊥-elim W-st
    ... | mix _ _      = ⊥-elim W-st

    -- Divergence arm: mirror tail-on-div-construct.  Extract
    -- `Divergent (body a)` from the empty-trace `IsDivergence`
    -- record, then lift through bind via `Divergent-bind-left`.
    divergence-arm
      : IsDivergence (body a) []
      → Divergent (body a >>= k)
    divergence-arm d-body =
      let prefix-≡-[] : d-body .IsDivergence.prefix ≡ []
          prefix-≡-[] = split-empty-l (d-body .IsDivergence.split)
          reach-at-[] : (body a) ═⟨ [] ⟩═► d-body .IsDivergence.witness
          reach-at-[] =
            subst (λ s* → (body a) ═⟨ s* ⟩═► d-body .IsDivergence.witness)
                  prefix-≡-[]
                  (d-body .IsDivergence.reach)
          div-body : Divergent (body a)
          div-body = divergent-prefix
                       (bigstep-empty-to-τ* reach-at-[])
                       (d-body .IsDivergence.divwit)
      in Divergent-bind-left k div-body

    dispatch-out
      : failures⊥ (body a) [] B*
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body  a >>= k) ─[τ*]─► X'
          × isStable X'
          × (∀ (e : Event√ E (A ⊎ R)) → B e
               → ∀ {X''} → ¬ X' ─[ ev e ]─► X'')) )
      ⊎ Divergent (body a >>= k)
    dispatch-out (inj₁ f-trip) = inj₁ (failure-arm f-trip)
    dispatch-out (inj₂ d-body) = inj₂ (divergence-arm d-body)

-- `tail-on-stable-ref-construct-Y`: Y-parameterised sibling.  Mirrors
-- `tail-on-stable-ref-construct` with `body' a` → `Y` and direct
-- refinement hypotheses `body a ⊑F⊥ Y`, `body a ⊑D Y` (in place of
-- `bF⊑ a`, `bD⊑ a`).  Proof body is identical modulo the
-- substitution.
tail-on-stable-ref-construct-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {B : Event√ E (A ⊎ R) → Set ℓB}
    → isStable (Y >>= (λ a' → Ret (h a')))
    → (∀ (e : Event√ E (A ⊎ R)) → B e
         → ∀ {Y' : ITree E (ExtI I) (A ⊎ R)}
         → ¬ (Y >>= (λ a' → Ret (h a'))) ─[ ev e ]─► Y')
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × isStable X'
        × (∀ (e : Event√ E (A ⊎ R)) → B e
             → ∀ {X'' : ITree E (ExtI I) (A ⊎ R)}
             → ¬ X' ─[ ev e ]─► X'')) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-stable-ref-construct-Y {ℓi = ℓi} {ℓr = ℓr} {ℓB = ℓB}
                                {I = I} {A = A} {R = R}
                                {body = body} {body' = body'} {h = h} {Y = Y}
                                a bF⊑Y bD⊑Y sim-rec {B = B} Y-stable Y-no-ev
    with Y .force in Y-eq
... | ret _        = ⊥-elim Y-stable
... | sil _        = ⊥-elim Y-stable
... | ndbr _ _ _ _ = ⊥-elim Y-stable
... | mix _ _      = ⊥-elim Y-stable
... | vis fY       = dispatch-out (bF⊑Y (inj₁ Y-fail))
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a' → Ret (h a')

    -- Refusal predicate lifted to body's event type.  Visible events
    -- pass through unchanged; body ticks are always in B*, so the
    -- ref-tick arm of `bF⊑Y`'s output is structurally absurd.
    B* : Event√ E A → Set ℓB
    B* (evl e) = B (evl e)
    B* (√ _)   = ⊤ {ℓB}

    Y-stable* : isStable Y
    Y-stable* = vis-isStable {P = Y} Y-eq

    -- ev (evl e) step on Y lifts to ev (evl e) step on
    -- (Y >>= k); `Y-no-ev` refutes it.
    Y-no-ev-evl
      : ∀ (e : Event E) {Q' : ITree E (ExtI I) A}
      → B (evl e) → ¬ Y ─[ ev (evl e) ]─► Q'
    Y-no-ev-evl e Be step =
        Y-no-ev (evl e) Be (lift-bind-step-ev Y k step)

    -- Promote to B* refusal: evl via Y-no-ev-evl; √ a' is vacuous
    -- because Y is vis-shaped (cannot fire sRet).
    Y-no-ev-B*
      : ∀ (e : Event√ E A) → B* e
      → ∀ {Q : ITree E (ExtI I) A}
      → ¬ Y ─[ ev e ]─► Q
    Y-no-ev-B* (evl e) Be step = Y-no-ev-evl e Be step
    Y-no-ev-B* (√ _)   _   (sRet eq-ret) =
        case trans (sym Y-eq) eq-ret of λ ()

    Y-ref : Y ref B*
    Y-ref = ref-stable Y-stable* Y-no-ev-B*

    Y-fail : failures Y [] B*
    Y-fail = Y , bNil , Y-ref

    -- Invert an ev-step on (W >>= k) back to an ev (evl e') step on W.
    -- W is stable (vis-shaped) by assumption.
    invert-bind-step
      : ∀ {W : ITree E (ExtI I) A}
          {fW : (at : AnyTypes E)
                → ContinueType at (Maybe (ITree E (ExtI I) A))}
          {e : Event√ E (A ⊎ R)} {t : ITree E (ExtI I) (A ⊎ R)}
      → ITree.force W ≡ vis fW
      → (W >>= k) ─[ ev e ]─► t
      → Σ (Event E) λ e' → e ≡ evl e' ×
            Σ (ITree E (ExtI I) A) λ Q' → W ─[ ev (evl e') ]─► Q'
    invert-bind-step {W = W} {fW = fW} eq-W
                     (sVis {f = f'} {at = at} {a = a-evt} {t′ = tgt}
                           eq-f eq-j) =
        cont-inv (fW at a-evt) refl
      where
        f≡bcv : f' ≡ bind-cont-vis k fW
        f≡bcv = vis-injective
                  (trans (sym eq-f) (bind-force-vis W k eq-W))
        eq-j' : bind-cont-vis k fW at a-evt ≡ just tgt
        eq-j' = subst (λ g → g at a-evt ≡ just tgt) f≡bcv eq-j
        cont-inv : (m : Maybe (ITree E (ExtI I) A))
                 → fW at a-evt ≡ m
                 → Σ (Event E) λ e' →
                     evl (evLabel (proj₁ at) (proj₂ at) a-evt) ≡ evl e' ×
                     Σ (ITree E (ExtI I) A) λ Q' →
                       W ─[ ev (evl e') ]─► Q'
        cont-inv nothing  fia-eq =
            ⊥-elim
              (case trans (sym (bind-cont-vis-nothing k fW at a-evt fia-eq))
                          eq-j'
                    of λ ())
        cont-inv (just t′) fia-eq =
            evLabel (proj₁ at) (proj₂ at) a-evt , refl ,
            t′ , sVis eq-W fia-eq
    invert-bind-step {W = W} {fW = fW} eq-W (sMixVis eq-f _) =
        case trans (sym (bind-force-vis W k eq-W)) eq-f of λ ()
    invert-bind-step {W = W} {fW = fW} eq-W (sRet eq-f) =
        case trans (sym (bind-force-vis W k eq-W)) eq-f of λ ()

    -- Failure arm: route `(W , bs-W , ref-W)` directly, threading the
    -- bigstep through `lift-bind-bigstep` and the refusal through
    -- `invert-bind-step`.
    failure-arm
      : Σ[ W ∈ ITree E (ExtI I) A ]
          ( body a ═⟨ [] ⟩═► W × W ref B*)
      → Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body  a >>= k) ─[τ*]─► X'
          × isStable X'
          × (∀ (e : Event√ E (A ⊎ R)) → B e
               → ∀ {X''} → ¬ X' ─[ ev e ]─► X''))
    failure-arm (W , bs-W , ref-tick {x = x} _ ¬Bx) = ⊥-elim (¬Bx tt)
    failure-arm (W , bs-W , ref-stable W-st W-no-ev)
        with W .force in w-eq
    ... | vis fW =
            W >>= k
          , bigstep-empty-to-τ* (lift-bind-bigstep (body a) k [] bs-W)
          , vis-isStable {P = W >>= k} (bind-force-vis W k w-eq)
          , bind-no-ev
      where
        bind-no-ev : ∀ (e : Event√ E (A ⊎ R)) → B e
                   → ∀ {X''} → ¬ (W >>= k) ─[ ev e ]─► X''
        bind-no-ev e Be step with invert-bind-step w-eq step
        ... | e' , refl , Q' , step-W = W-no-ev (evl e') Be step-W
    ... | ret _        = ⊥-elim W-st
    ... | sil _        = ⊥-elim W-st
    ... | ndbr _ _ _ _ = ⊥-elim W-st
    ... | mix _ _      = ⊥-elim W-st

    -- Divergence arm: mirror tail-on-div-construct.  Extract
    -- `Divergent (body a)` from the empty-trace `IsDivergence`
    -- record, then lift through bind via `Divergent-bind-left`.
    divergence-arm
      : IsDivergence (body a) []
      → Divergent (body a >>= k)
    divergence-arm d-body =
      let prefix-≡-[] : d-body .IsDivergence.prefix ≡ []
          prefix-≡-[] = split-empty-l (d-body .IsDivergence.split)
          reach-at-[] : (body a) ═⟨ [] ⟩═► d-body .IsDivergence.witness
          reach-at-[] =
            subst (λ s* → (body a) ═⟨ s* ⟩═► d-body .IsDivergence.witness)
                  prefix-≡-[]
                  (d-body .IsDivergence.reach)
          div-body : Divergent (body a)
          div-body = divergent-prefix
                       (bigstep-empty-to-τ* reach-at-[])
                       (d-body .IsDivergence.divwit)
      in Divergent-bind-left k div-body

    dispatch-out
      : failures⊥ (body a) [] B*
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ]
          ( (body  a >>= k) ─[τ*]─► X'
          × isStable X'
          × (∀ (e : Event√ E (A ⊎ R)) → B e
               → ∀ {X''} → ¬ X' ─[ ev e ]─► X'')) )
      ⊎ Divergent (body a >>= k)
    dispatch-out (inj₁ f-trip) = inj₁ (failure-arm f-trip)
    dispatch-out (inj₂ d-body) = inj₂ (divergence-arm d-body)

-- `tail-on-ret-inj₁-construct`: handle the body'-iterates boundary.
-- force(body' a >>= k) ≡ ret(inj₁ a-next) forces body' a .force =
-- ret a-prime with a-prime ≡ a-next (since k a-prime = Ret(inj₁
-- a-prime), so the bind's force reduces to ret(inj₁ a-prime); refl
-- unifies a-next := a-prime).  Then mirror the failure/divergence
-- dispatch of `construct-on-tau-body'-ret`, but stop at the bind
-- level (no iter-bind lift):
--   * Failure arm: body a has bigstep `body a ═⟨ √ a-prime ∷ [] ⟩→
--     deadlock`; lift through bind via `lift-bind-bigstep-tick` to
--     `(body a >>= k) ═⟨ [] ⟩→ X'` with `force X' ≡ ret(inj₁
--     a-prime)`.  Convert to τ*-chain via `bigstep-empty-to-τ*`.
--     Use sim-rec a-prime for the post-cycle Loop-Sim.
--   * Divergence arm: prefix-tick-split.  Prefix-≤-empty arm: body
--     a τ*-diverges before the √; lift via Divergent-bind-left.
--     Prefix-swallows-√ arm: bigstep lands at deadlock, which can't
--     host a divergence (Divergent-deadlock-absurd).
tail-on-ret-inj₁-construct
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {a-next : A}
    → ITree.force (body' a >>= (λ a' → Ret (h a')))
        ≡ ret (inj₁ a-next)
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × ITree.force X' ≡ ret (inj₁ a'-next)
        × Loop-Sim {ℓB = ℓB} (genIter h body a'-next)
                              (genIter h body' a-next) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-ret-inj₁-construct {ℓB = ℓB} {I = I} {A = A} {R = R}
                            {body = body} {body' = body'} {h = h}
                            bF⊑ bD⊑ sim-rec a {a-next} eq-Y
    with body' a .force in body'-eq
... | sil _        = case eq-Y of λ ()
... | vis _        = case eq-Y of λ ()
... | ndbr _ _ _ _ = case eq-Y of λ ()
... | mix _ _      = case eq-Y of λ ()
... | ret a-prime
    -- force(body' a >>= k) = ret (h a-prime); tag decides cycle (inj₁) vs
    -- exit (inj₂, absurd against ret (inj₁ a-next)).
    with h a-prime in hav-eq | eq-Y
...   | inj₂ _    | ()
...   | inj₁ av'  | refl =
    dispatch (bF⊑ a (inj₁ (deadlock , bs-body' , deadlock-ref)))
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a' → Ret (h a')

    X'-force-eq : ∀ {X' : ITree E (ExtI I) (A ⊎ R)}
                → ITree.force X' ≡ ret (h a-prime)
                → ITree.force X' ≡ ret (inj₁ av')
    X'-force-eq {X'} fe = trans fe (cong (ret {E = E} {I = ExtI I}) hav-eq)

    bs-body' : body' a ═⟨ √ a-prime ∷ [] ⟩═► deadlock
    bs-body' = bStep (sRet body'-eq) bNil

    handle-failure
      : Σ[ W ∈ ITree E (ExtI I) A ]
        ( body a ═⟨ √ a-prime ∷ [] ⟩═► W
        × W ref (λ _ → Lift ℓB ⊥))
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₁ a'-next)
          × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
      ⊎ Divergent (body a >>= k)
    handle-failure (W , bs-W , _) =
      let W-eq : W ≡ deadlock
          W-eq = tick-bigstep-lands-at-deadlock {s1 = []} bs-W
          bs-W-dl : body a ═⟨ √ a-prime ∷ [] ⟩═► deadlock
          bs-W-dl = subst (λ X → body a ═⟨ √ a-prime ∷ [] ⟩═► X) W-eq bs-W
          lift-bind = lift-bind-bigstep-tick (body a) k [] bs-W-dl
          X' = proj₁ lift-bind
          bs-bind : (body a >>= k) ═⟨ [] ⟩═► X'
          bs-bind = proj₁ (proj₂ lift-bind)
          X'-force : ITree.force X' ≡ ret (inj₁ av')
          X'-force = X'-force-eq {X' = X'} (proj₂ (proj₂ lift-bind))
      in inj₁ ( X'
              , av'
              , bigstep-empty-to-τ* bs-bind
              , X'-force
              , sim-rec av'
              )

    handle-divergence
      : divergences (body a) (√ a-prime ∷ [])
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₁ a'-next)
          × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
      ⊎ Divergent (body a >>= k)
    handle-divergence d-body =
      case prefix-tick-split [] {r = a-prime}
              (d-body .IsDivergence.prefix)
              (d-body .IsDivergence.suffix)
              (sym (d-body .IsDivergence.split))
          of λ where
        (inj₁ (pre0 , suf0 , s1-eq , pre-eq , _)) →
          let pre0-eq : pre0 ≡ []
              pre0-eq = split-empty-l s1-eq
              prefix-eq : d-body .IsDivergence.prefix ≡ []
              prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
              reach-at-[] : body a ═⟨ [] ⟩═► d-body .IsDivergence.witness
              reach-at-[] =
                subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                      prefix-eq
                      (d-body .IsDivergence.reach)
              div-body : Divergent (body a)
              div-body = divergent-prefix
                           (bigstep-empty-to-τ* reach-at-[])
                           (d-body .IsDivergence.divwit)
          in inj₂ (Divergent-bind-left k div-body)
        (inj₂ (pre-eq , _)) →
          let bs-to-W : body a ═⟨ √ a-prime ∷ [] ⟩═►
                          d-body .IsDivergence.witness
              bs-to-W =
                subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                      pre-eq
                      (d-body .IsDivergence.reach)
              W-dl : d-body .IsDivergence.witness ≡ deadlock
              W-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-to-W
          in ⊥-elim (Divergent-deadlock-absurd
                       (subst Divergent W-dl
                              (d-body .IsDivergence.divwit)))

    dispatch
      : failures⊥ (body a) (√ a-prime ∷ []) (λ _ → Lift ℓB ⊥)
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₁ a'-next)
          × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
      ⊎ Divergent (body a >>= k)
    dispatch (inj₁ f-trip) = handle-failure f-trip
    dispatch (inj₂ d-body) = handle-divergence d-body

-- `tail-on-ret-inj₁-construct-Y`: Y-parameterised sibling.  Mirrors
-- `tail-on-ret-inj₁-construct` with `body' a` → `Y` and direct
-- refinement hypotheses `body a ⊑F⊥ Y`, `body a ⊑D Y` (in place of
-- `bF⊑ a`, `bD⊑ a`).  The recursion target via `sim-rec a-prime`
-- keeps `a-prime` from `Y .force ≡ ret a-prime`; this stays valid
-- because `sim-rec` is body/body'-indexed, not Y-indexed.
tail-on-ret-inj₁-construct-Y
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {Y : ITree E (ExtI I) A}
    → ∀ (a : A)
    → _⊑F⊥_ {ℓB = ℓB} (body a) Y
    → body a ⊑D Y
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ {a-next : A}
    → ITree.force (Y >>= (λ a' → Ret (h a')))
        ≡ ret (inj₁ a-next)
    → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
        ( (body  a >>= (λ a' → Ret (h a'))) ─[τ*]─► X'
        × ITree.force X' ≡ ret (inj₁ a'-next)
        × Loop-Sim {ℓB = ℓB} (genIter h body a'-next)
                              (genIter h body' a-next) ) )
    ⊎ Divergent (body a >>= (λ a' → Ret (h a')))
tail-on-ret-inj₁-construct-Y {ℓB = ℓB} {I = I} {A = A} {R = R}
                              {body = body} {body' = body'} {h = h} {Y = Y}
                              a bF⊑Y bD⊑Y sim-rec {a-next} eq-Y
    with Y .force in Y-eq
... | sil _        = case eq-Y of λ ()
... | vis _        = case eq-Y of λ ()
... | ndbr _ _ _ _ = case eq-Y of λ ()
... | mix _ _      = case eq-Y of λ ()
... | ret a-prime
    with h a-prime in hav-eq | eq-Y
...   | inj₂ _    | ()
...   | inj₁ av'  | refl =
    dispatch (bF⊑Y (inj₁ (deadlock , bs-Y , deadlock-ref)))
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a' → Ret (h a')

    X'-force-eq : ∀ {X' : ITree E (ExtI I) (A ⊎ R)}
                → ITree.force X' ≡ ret (h a-prime)
                → ITree.force X' ≡ ret (inj₁ av')
    X'-force-eq {X'} fe = trans fe (cong (ret {E = E} {I = ExtI I}) hav-eq)

    bs-Y : Y ═⟨ √ a-prime ∷ [] ⟩═► deadlock
    bs-Y = bStep (sRet Y-eq) bNil

    handle-failure
      : Σ[ W ∈ ITree E (ExtI I) A ]
        ( body a ═⟨ √ a-prime ∷ [] ⟩═► W
        × W ref (λ _ → Lift ℓB ⊥))
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₁ a'-next)
          × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
      ⊎ Divergent (body a >>= k)
    handle-failure (W , bs-W , _) =
      let W-eq : W ≡ deadlock
          W-eq = tick-bigstep-lands-at-deadlock {s1 = []} bs-W
          bs-W-dl : body a ═⟨ √ a-prime ∷ [] ⟩═► deadlock
          bs-W-dl = subst (λ X → body a ═⟨ √ a-prime ∷ [] ⟩═► X) W-eq bs-W
          lift-bind = lift-bind-bigstep-tick (body a) k [] bs-W-dl
          X' = proj₁ lift-bind
          bs-bind : (body a >>= k) ═⟨ [] ⟩═► X'
          bs-bind = proj₁ (proj₂ lift-bind)
          X'-force : ITree.force X' ≡ ret (inj₁ av')
          X'-force = X'-force-eq {X' = X'} (proj₂ (proj₂ lift-bind))
      in inj₁ ( X'
              , av'
              , bigstep-empty-to-τ* bs-bind
              , X'-force
              , sim-rec av'
              )

    handle-divergence
      : divergences (body a) (√ a-prime ∷ [])
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₁ a'-next)
          × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
      ⊎ Divergent (body a >>= k)
    handle-divergence d-body =
      case prefix-tick-split [] {r = a-prime}
              (d-body .IsDivergence.prefix)
              (d-body .IsDivergence.suffix)
              (sym (d-body .IsDivergence.split))
          of λ where
        (inj₁ (pre0 , suf0 , s1-eq , pre-eq , _)) →
          let pre0-eq : pre0 ≡ []
              pre0-eq = split-empty-l s1-eq
              prefix-eq : d-body .IsDivergence.prefix ≡ []
              prefix-eq = trans pre-eq (cong (map evl) pre0-eq)
              reach-at-[] : body a ═⟨ [] ⟩═► d-body .IsDivergence.witness
              reach-at-[] =
                subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                      prefix-eq
                      (d-body .IsDivergence.reach)
              div-body : Divergent (body a)
              div-body = divergent-prefix
                           (bigstep-empty-to-τ* reach-at-[])
                           (d-body .IsDivergence.divwit)
          in inj₂ (Divergent-bind-left k div-body)
        (inj₂ (pre-eq , _)) →
          let bs-to-W : body a ═⟨ √ a-prime ∷ [] ⟩═►
                          d-body .IsDivergence.witness
              bs-to-W =
                subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                      pre-eq
                      (d-body .IsDivergence.reach)
              W-dl : d-body .IsDivergence.witness ≡ deadlock
              W-dl = tick-bigstep-lands-at-deadlock {s1 = []} bs-to-W
          in ⊥-elim (Divergent-deadlock-absurd
                       (subst Divergent W-dl
                              (d-body .IsDivergence.divwit)))

    dispatch
      : failures⊥ (body a) (√ a-prime ∷ []) (λ _ → Lift ℓB ⊥)
      → ( Σ[ X' ∈ ITree E (ExtI I) (A ⊎ R) ] Σ[ a'-next ∈ A ]
          ( (body a >>= k) ─[τ*]─► X'
          × ITree.force X' ≡ ret (inj₁ a'-next)
          × Loop-Sim {ℓB = ℓB} (genIter h body a'-next) (genIter h body' av') ) )
      ⊎ Divergent (body a >>= k)
    dispatch (inj₁ f-trip) = handle-failure f-trip
    dispatch (inj₂ d-body) = handle-divergence d-body

-- `bF⊑+bD⊑→Tail-Sim`: assemble the six per-field constructors above
-- into a Tail-Sim record.  Each field projection delegates to the
-- corresponding narrow postulate (or, for `on-ret-inj₂`, the
-- structural-absurd helper defined just above).
bF⊑+bD⊑→Tail-Sim
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h}
                (body  a >>= (λ a' → Ret (h a')))
                (body' a >>= (λ a' → Ret (h a')))
bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ sim-rec a = record
  { on-vis        = tail-on-vis-construct        bF⊑ bD⊑ sim-rec a
  ; on-tau        = tail-on-tau-construct        bF⊑ bD⊑ sim-rec a
  ; on-stable-ref = tail-on-stable-ref-construct bF⊑ bD⊑ sim-rec a
  ; on-div        = tail-on-div-construct        bF⊑ bD⊑ sim-rec a
  ; on-ret-inj₁   = tail-on-ret-inj₁-construct   bF⊑ bD⊑ sim-rec a
  ; on-ret-inj₂   = tail-on-ret-inj₂-construct   bF⊑ bD⊑ sim-rec a
  }

-- `bF⊑+bD⊑→Tail-Sim-Y`: Y-parameterised sibling assembly.  Takes
-- direct refinement hypotheses `body a ⊑F⊥ Y` and `body a ⊑D Y` at
-- an arbitrary intermediate Y (in place of `body' a`).  Defined with
-- copattern clauses: the five non-τ fields delegate to existing
-- `-Y` per-field constructors, while `on-tau` is inlined below so the
-- corecursive call to `bF⊑+bD⊑→Tail-Sim-Y` at the τ-successor sits
-- directly under the `.Tail-Sim.on-tau` copattern projection — Agda's
-- productivity checker sees this as guarded.  Inlining is the only
-- option for `on-tau`: routing through helpers
-- (`tail-on-tau-construct-Y` → `tail-on-tau-sSil-Y` → …) breaks the
-- guardedness chain because Agda doesn't see those helpers as part of
-- the same productivity group.
bF⊑+bD⊑→Tail-Sim-Y a bF⊑Y bD⊑Y sim-rec .Tail-Sim.on-vis        = tail-on-vis-construct-Y        a bF⊑Y bD⊑Y sim-rec
bF⊑+bD⊑→Tail-Sim-Y a bF⊑Y bD⊑Y sim-rec .Tail-Sim.on-stable-ref = tail-on-stable-ref-construct-Y a bF⊑Y bD⊑Y sim-rec
bF⊑+bD⊑→Tail-Sim-Y a bF⊑Y bD⊑Y sim-rec .Tail-Sim.on-div        = tail-on-div-construct-Y        a bF⊑Y bD⊑Y sim-rec
bF⊑+bD⊑→Tail-Sim-Y a bF⊑Y bD⊑Y sim-rec .Tail-Sim.on-ret-inj₁   = tail-on-ret-inj₁-construct-Y   a bF⊑Y bD⊑Y sim-rec
bF⊑+bD⊑→Tail-Sim-Y a bF⊑Y bD⊑Y sim-rec .Tail-Sim.on-ret-inj₂   = tail-on-ret-inj₂-construct-Y   a bF⊑Y bD⊑Y sim-rec

-- `.on-tau` inlined: case-split on the τ-step constructor, then on
-- Y's force to eliminate impossible shapes.  In each live arm, build
-- the τ-step `Y ─[τ]─► c` (or `Qt'`) from Y-eq, push the refinement
-- hypotheses across via `⊑F⊥-τ-step-right` / `⊑D-τ-step-right`, and
-- recursively call `bF⊑+bD⊑→Tail-Sim-Y` at the successor.  The body-a
-- side takes zero τ-steps (`τ*-zero`); the bind reduces Y' to
-- `c >>= k'` (resp. `Qt' >>= k'`) under the live arm's refl.
bF⊑+bD⊑→Tail-Sim-Y {body = body} {h = h} {Y = Y} a bF⊑Y bD⊑Y sim-rec .Tail-Sim.on-tau (sSil eq-f)
    with Y .force in Y-eq | eq-f
... | ret _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | ()
... | sil c        | refl =
        let τ-step = sSil Y-eq
            bF⊑-c  = ⊑F⊥-τ-step-right τ-step bF⊑Y
            bD⊑-c  = ⊑D-τ-step-right  τ-step bD⊑Y
            ts-c   = bF⊑+bD⊑→Tail-Sim-Y {Y = c} a bF⊑-c bD⊑-c sim-rec
        in inj₁ (body a >>= (λ a' → Ret (h a')) , τ*-zero , ts-c)
bF⊑+bD⊑→Tail-Sim-Y {body = body} {h = h} {Y = Y} a bF⊑Y bD⊑Y sim-rec
                    .Tail-Sim.on-tau (sNdbr {i = i} {a = ai} eq-f eq-j)
    with Y .force in Y-eq | eq-f
... | ret _        | ()
... | sil _        | ()
... | vis _        | ()
... | mix _ _      | ()
... | ndbr f' _ _ _ | refl
    with f' i ai in f-eq | eq-j
...   | nothing | ()
...   | just c  | refl =
        let τ-step = sNdbr Y-eq f-eq
            bF⊑-c  = ⊑F⊥-τ-step-right τ-step bF⊑Y
            bD⊑-c  = ⊑D-τ-step-right  τ-step bD⊑Y
            ts-c   = bF⊑+bD⊑→Tail-Sim-Y {Y = c} a bF⊑-c bD⊑-c sim-rec
        in inj₁ (body a >>= (λ a' → Ret (h a')) , τ*-zero , ts-c)
bF⊑+bD⊑→Tail-Sim-Y {body = body} {h = h} {Y = Y} a bF⊑Y bD⊑Y sim-rec
                    .Tail-Sim.on-tau (sMixSlide eq-f)
    with Y .force in Y-eq | eq-f
... | ret _        | ()
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ Qt'    | refl =
        let τ-step  = sMixSlide Y-eq
            bF⊑-Qt' = ⊑F⊥-τ-step-right τ-step bF⊑Y
            bD⊑-Qt' = ⊑D-τ-step-right  τ-step bD⊑Y
            ts-Qt'  = bF⊑+bD⊑→Tail-Sim-Y {Y = Qt'} a bF⊑-Qt' bD⊑-Qt' sim-rec
        in inj₁ (body a >>= (λ a' → Ret (h a')) , τ*-zero , ts-Qt')

-- tail-sim→loop-sim: assemble the four field helpers into a Loop-Sim.
tail-sim→loop-sim
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → Loop-Sim {ℓB = ℓB} (iter-bind X (genStep h body))
                          (iter-bind Y (genStep h body'))
-- Helper: lift an evl-event step on Q to iter-bind Q k.  The sRet
-- constructor doesn't unify (it produces √, not evl), so only the
-- sVis and sMixVis cases apply.
private
  lift-step-evl
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {Q Q' : ITree E (ExtI I) (A ⊎ R)}
        (k : A → ITree E (ExtI I) (A ⊎ R))
      → Q ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]─► Q'
      → iter-bind Q k
          ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]─►
        iter-bind Q' k
  lift-step-evl {at = at} {a-evt = a-evt} {Q = Q} k (sVis {f = fX} eq-f eq-j) =
      sVis (iter-bind-force-vis Q k eq-f)
           (iter-bind-cont-vis-just k fX at a-evt eq-j)
  lift-step-evl {at = at} {a-evt = a-evt} {Q = Q} k (sMixVis {f = fX} eq-f eq-j) =
      sMixVis (iter-bind-force-mix Q k eq-f)
              (iter-bind-cont-mix-just k fX at a-evt eq-j)

-- tail-on-vis-lift-sVis: discharged via Tail-Sim.on-vis.  Invert
-- iter-bind force = vis f' to Y.force = vis fY with f' = iter-bind-cont-vis k fY;
-- invert the cont-vis to recover c' with fY at a-evt = just c' and
-- Q' = iter-bind c' k.  Build Y's sVis step, apply on-vis, lift the
-- resulting X bigstep through iter-bind via lift-step-evl + left-τ*.
tail-on-vis-lift-sVis
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) R))}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {Q' : ITree E (ExtI I) R}
    → ITree.force (iter-bind Y (genStep h body')) ≡ vis f'
    → f' at a-evt ≡ just Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body)
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-vis-lift-sVis {body = body} {body' = body'} {h = h} {X = X} {Y = Y}
                       ts {at = at} {a-evt = a-evt} eq-iter-vis eq-iter-j
  with iter-bind-force-vis-inv Y (genStep h body') eq-iter-vis
... | (fY , y-eq , refl)
  with iter-bind-cont-vis-just-inv (genStep h body') fY at a-evt eq-iter-j
... | (c' , fY-just , refl)
  with Tail-Sim.on-vis ts (sVis y-eq fY-just)
... | inj₂ X-div = inj₂ (Divergent-iter-bind-left (genStep h body) X-div)
... | inj₁ (X' , weak-ev pre x-step post , ts') =
        inj₁ ( iter-bind X' (genStep h body)
             , weak-ev (iter-bind-left-τ* (genStep h body) pre)
                       (lift-step-evl (genStep h body) x-step)
                       (iter-bind-left-τ* (genStep h body) post)
             , tail-sim→loop-sim ts'
             )

-- tail-on-vis-lift-sMixVis: symmetric to sVis, with mix replacing vis.
tail-on-vis-lift-sMixVis
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) R))}
        {Qt' : ITree E (ExtI I) R}
        {at : AnyTypes E} {a-evt : proj₁ at}
        {Q' : ITree E (ExtI I) R}
    → ITree.force (iter-bind Y (genStep h body')) ≡ mix f' Qt'
    → f' at a-evt ≡ just Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body)
            ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a-evt)) ]═► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-vis-lift-sMixVis {body = body} {body' = body'} {h = h} {X = X} {Y = Y}
                          ts {at = at} {a-evt = a-evt} eq-iter-mix eq-iter-j
  with iter-bind-force-mix-inv Y (genStep h body') eq-iter-mix
... | (fY , QtY , y-eq , refl , _)
  with iter-bind-cont-mix-just-inv (genStep h body') fY at a-evt eq-iter-j
... | (c' , fY-just , refl)
  with Tail-Sim.on-vis ts (sMixVis y-eq fY-just)
... | inj₂ X-div = inj₂ (Divergent-iter-bind-left (genStep h body) X-div)
... | inj₁ (X' , weak-ev pre x-step post , ts') =
        inj₁ ( iter-bind X' (genStep h body)
             , weak-ev (iter-bind-left-τ* (genStep h body) pre)
                       (lift-step-evl (genStep h body) x-step)
                       (iter-bind-left-τ* (genStep h body) post)
             , tail-sim→loop-sim ts'
             )

-- tail-on-vis-lift-sRet: discharged via Tail-Sim.on-ret-inj₂.  iter-bind
-- Y k force = ret r inverts to Y.force = ret(inj₂ r); on-ret-inj₂
-- produces X' with force = ret(inj₂ r); lift τ*-chain through iter-bind
-- and fire sRet at iter-bind X' k to land at deadlock.
tail-on-vis-lift-sRet
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {r : R}
    → ITree.force (iter-bind Y (genStep h body')) ≡ ret r
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body) ═[ ev (√ r) ]═► P'
        × Loop-Sim {ℓB = ℓB} P' deadlock ) )
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-vis-lift-sRet {body = body} {body' = body'} {h = h} {X = X} {Y = Y}
                       ts {r = r} eq-iter-ret =
    let y-eq : ITree.force Y ≡ ret (inj₂ r)
        y-eq = iter-bind-force-ret-inv Y (genStep h body') eq-iter-ret
    in case Tail-Sim.on-ret-inj₂ ts y-eq of λ where
         (inj₁ (X' , X→X' , X'-eq)) →
           let iter-X→X' : iter-bind X (genStep h body) ─[τ*]─► iter-bind X' (genStep h body)
               iter-X→X' = iter-bind-left-τ* (genStep h body) X→X'
               iter-X'-eq : ITree.force (iter-bind X' (genStep h body)) ≡ ret r
               iter-X'-eq = iter-bind-force-ret-inj₂ X' (genStep h body) X'-eq
               step-final : iter-bind X' (genStep h body) ─[ ev (√ r) ]─► deadlock
               step-final = sRet iter-X'-eq
               weak : iter-bind X (genStep h body) ═[ ev (√ r) ]═► deadlock
               weak = weak-ev iter-X→X' step-final τ*-zero
           in inj₁ (deadlock , weak , loop-sim-deadlock)
         (inj₂ X-div) →
           inj₂ (Divergent-iter-bind-left (genStep h body) X-div)

-- tail-on-vis-lift: dispatch on the step's constructor.  Each
-- constructor pins iter-bind Y k's force shape, which determines
-- which sub-helper applies.
tail-on-vis-lift
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {e : Event√ E R} {Q' : ITree E (ExtI I) R}
    → iter-bind Y (genStep h body') ─[ ev e ]─► Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body) ═[ ev e ]═► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-vis-lift ts (sVis    eq-f eq-j) = tail-on-vis-lift-sVis    ts eq-f eq-j
tail-on-vis-lift ts (sMixVis eq-f eq-j) = tail-on-vis-lift-sMixVis ts eq-f eq-j
tail-on-vis-lift ts (sRet    eq-f)      = tail-on-vis-lift-sRet    ts eq-f

-- tail-on-tau-lift-sSil: discharged via Tail-Sim.on-tau / on-ret-inj₁.
-- iter-bind force ≡ sil Q' factors via iter-bind-force-sil-inv into
-- two sub-cases on Y.force: sil cY (Y τ-progresses) or ret (inj₁
-- a-next) (iteration boundary crossing).
--
--   sil cY  : Q' ≡ iter-bind cY (genStep h body'); rebuild Y's sSil
--             step and route through Tail-Sim.on-tau.
--   ret (inj₁ a-next) : Q' ≡ iter (genStep h body') a-next; route
--             through Tail-Sim.on-ret-inj₁ to obtain X', a'-next and
--             the post-cycle Loop-Sim recursion, then append one
--             extra τ-step `iter-bind X' k ─[τ]→ iter (genStep h
--             body) a'-next` via iter-bind-force-ret-inj₁.
tail-on-tau-lift-sSil
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {Q' : ITree E (ExtI I) R}
    → ITree.force (iter-bind Y (genStep h body')) ≡ sil Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-tau-lift-sSil {body = body} {body' = body'} {h = h} {Y = Y} ts eq-iter-sil
  with iter-bind-force-sil-inv Y (genStep h body') eq-iter-sil
... | inj₁ (cY , y-eq , refl)
  with Tail-Sim.on-tau ts (sSil y-eq)
...   | inj₂ X-div = inj₂ (Divergent-iter-bind-left (genStep h body) X-div)
...   | inj₁ (X' , X→X' , ts') =
          inj₁ ( iter-bind X' (genStep h body)
               , iter-bind-left-τ* (genStep h body) X→X'
               , tail-sim→loop-sim ts'
               )
tail-on-tau-lift-sSil {body = body} {body' = body'} {h = h} {Y = Y} ts _
    | inj₂ (a-next , y-eq , refl)
  with Tail-Sim.on-ret-inj₁ ts y-eq
...   | inj₂ X-div = inj₂ (Divergent-iter-bind-left (genStep h body) X-div)
...   | inj₁ (X' , a'-next , X→X' , X'-eq , loop-sim) =
          inj₁ ( iter (genStep h body) a'-next
               , τ*-then-step (iter-bind-left-τ* (genStep h body) X→X')
                              (sSil (iter-bind-force-ret-inj₁ X'
                                       (genStep h body) X'-eq))
               , loop-sim
               )

-- tail-on-tau-lift-sNdbr: discharged via Tail-Sim.on-tau.  iter-bind
-- force = ndbr f' wi wa wp inverts to Y.force = ndbr fY wi wa wp-Q;
-- the cont-ndbr inverts to fY i a = just c' with Q' = iter-bind c' k.
-- Build Y's sNdbr step and route through Tail-Sim.on-tau.
tail-on-tau-lift-sNdbr
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {f' : (ai : AnyTypes (ExtI I))
              → ContinueType ai (Maybe (ITree E (ExtI I) R))}
        {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (f' wi wa)}
        {i : AnyTypes (ExtI I)} {a : proj₁ i} {Q' : ITree E (ExtI I) R}
    → ITree.force (iter-bind Y (genStep h body')) ≡ ndbr f' wi wa wp
    → f' i a ≡ just Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-tau-lift-sNdbr {body = body} {body' = body'} {h = h} {Y = Y}
                       ts {i = i} {a = a} eq-iter-ndbr eq-iter-j
  with iter-bind-force-ndbr-inv Y (genStep h body') eq-iter-ndbr
... | (fY , wp-Q , y-eq , refl)
  with iter-bind-cont-ndbr-just-inv (genStep h body') fY i a eq-iter-j
... | (c' , fY-just , refl)
  with Tail-Sim.on-tau ts (sNdbr y-eq fY-just)
... | inj₂ X-div = inj₂ (Divergent-iter-bind-left (genStep h body) X-div)
... | inj₁ (X' , X→X' , ts') =
        inj₁ ( iter-bind X' (genStep h body)
             , iter-bind-left-τ* (genStep h body) X→X'
             , tail-sim→loop-sim ts'
             )

-- tail-on-tau-lift-sMixSlide: discharged via Tail-Sim.on-tau.
-- iter-bind force = mix f' Qt' inverts to Y.force = mix fY QtY with
-- Qt' = iter-bind QtY k; build Y's sMixSlide step and route through
-- Tail-Sim.on-tau.
tail-on-tau-lift-sMixSlide
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) R))}
        {Qt' : ITree E (ExtI I) R}
    → ITree.force (iter-bind Y (genStep h body')) ≡ mix f' Qt'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Qt' ) )
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-tau-lift-sMixSlide {body = body} {body' = body'} {h = h} {Y = Y} ts eq-iter-mix
  with iter-bind-force-mix-inv Y (genStep h body') eq-iter-mix
... | (fY , QtY , y-eq , _ , refl)
  with Tail-Sim.on-tau ts (sMixSlide y-eq)
... | inj₂ X-div = inj₂ (Divergent-iter-bind-left (genStep h body) X-div)
... | inj₁ (X' , X→X' , ts') =
        inj₁ ( iter-bind X' (genStep h body)
             , iter-bind-left-τ* (genStep h body) X→X'
             , tail-sim→loop-sim ts'
             )

-- tail-on-tau-lift: dispatch on the τ-step's constructor.  sSil
-- requires further sub-dispatch on Y.force (sil vs ret-inj₁) inside
-- the sub-helper.
tail-on-tau-lift
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {Q' : ITree E (ExtI I) R}
    → iter-bind Y (genStep h body') ─[ τ ]─► Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-tau-lift ts (sSil       eq-f)      = tail-on-tau-lift-sSil      ts eq-f
tail-on-tau-lift ts (sNdbr      eq-f eq-j) = tail-on-tau-lift-sNdbr     ts eq-f eq-j
tail-on-tau-lift ts (sMixSlide  eq-f)      = tail-on-tau-lift-sMixSlide ts eq-f

-- tail-on-stable-ref-lift: discharged via Tail-Sim.on-stable-ref.
-- iter-bind Y k is stable iff Y.force ≡ vis fY (the only iter-bind
-- force shape that yields a vis); all other Y.force shapes contradict
-- y-iter-stable.  Build a Y-level refusal predicate B-Y on
-- Event√ E (A ⊎ R) by re-using B on evl-events and refusing nothing
-- on √-events (Y stable ⇒ Y can't fire sRet anyway).  Route the Tail
-- side through Tail-Sim.on-stable-ref ts; on success, lift X' back to
-- iter-bind X' k preserving stability and the refusal predicate.
tail-on-stable-ref-lift
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → ∀ {B : Event√ E R → Set ℓB}
    → isStable (iter-bind Y (genStep h body'))
    → (∀ (e : Event√ E R) → B e
         → ∀ {Q' : ITree E (ExtI I) R}
         → ¬ iter-bind Y (genStep h body') ─[ ev e ]─► Q')
    → (Σ[ P' ∈ ITree E (ExtI I) R ]
        ( iter-bind X (genStep h body) ─[τ*]─► P'
        × isStable P'
        × (∀ (e : Event√ E R) → B e
            → ∀ {P'' : ITree E (ExtI I) R}
            → ¬ P' ─[ ev e ]─► P'')))
    ⊎ Divergent (iter-bind X (genStep h body))
tail-on-stable-ref-lift {ℓB = ℓB} {I = I} {A = A} {R = R}
                        {body = body} {body' = body'} {h = h} {X = X} {Y = Y}
                        ts {B = B} y-iter-stable y-iter-no-ev
  with Y .force in y-force-eq
... | ret (inj₁ _) = ⊥-elim y-iter-stable
... | ret (inj₂ _) = ⊥-elim y-iter-stable
... | sil _        = ⊥-elim y-iter-stable
... | ndbr _ _ _ _ = ⊥-elim y-iter-stable
... | mix _ _      = ⊥-elim y-iter-stable
... | vis fY       =
  case Tail-Sim.on-stable-ref ts {B = B-Y}
         (isStable-with-vis-force Y y-force-eq) (no-ev-Y y-force-eq) of λ where
    (inj₂ X-div) → inj₂ (Divergent-iter-bind-left (genStep h body) X-div)
    (inj₁ (X' , X→X' , X'-stable , no-ev-X')) →
      inj₁ ( iter-bind X' (genStep h body)
           , iter-bind-left-τ* (genStep h body) X→X'
           , lift-X'-isStable X' X'-stable
           , lift-X'-no-ev X' X'-stable no-ev-X'
           )
  where
    -- Lift B (on Event√ E R) to B-Y (on Event√ E (A ⊎ R)).  Evl events
    -- carry the same EventLabel type, so re-use B on evl; refuse nothing
    -- on √ (Y stable forbids √-shaped steps anyway).
    B-Y : Event√ E (A ⊎ R) → Set ℓB
    B-Y (evl ℓ) = B (evl ℓ)
    B-Y (√ _)   = Lift _ ⊥

    -- Y-level no-ev predicate, parameterized by Y.force ≡ vis fY.  An
    -- sVis step from Y lifts to iter-bind Y k via iter-bind-force-vis +
    -- iter-bind-cont-vis-just-fwd; sMixVis is forbidden by Y.force = vis.
    no-ev-Y
      : ∀ {fY : (at : AnyTypes E) → ContinueType at
                  (Maybe (ITree E (ExtI I) (A ⊎ R)))}
      → ITree.force Y ≡ vis fY
      → ∀ (e : Event√ E (A ⊎ R)) → B-Y e
      → ∀ {Y' : ITree E (ExtI I) (A ⊎ R)} → ¬ Y ─[ ev e ]─► Y'
    no-ev-Y _ (evl ℓ) b (sVis {f = fY-step} {at = at} {a = a} Y-vis fY'-just) =
      let iter-Y-vis = iter-bind-force-vis Y (genStep h body') Y-vis
          iter-cont-just = iter-bind-cont-vis-just-fwd
                             (genStep h body') fY-step at a fY'-just
      in y-iter-no-ev (evl ℓ) b (sVis iter-Y-vis iter-cont-just)
    no-ev-Y y-force-eq (evl _) _ (sMixVis Y-mix _) =
      case trans (sym Y-mix) y-force-eq of λ ()
    no-ev-Y _ (√ _) (lift ()) _

    -- Lift X' stable to iter-bind X' k stable.
    lift-X'-isStable
      : ∀ (X' : ITree E (ExtI I) (A ⊎ R))
      → isStable X'
      → isStable (iter-bind X' (genStep h body))
    lift-X'-isStable X' X'-stable with X' .force
    ... | vis _        = tt₀
    ... | ret _        = ⊥-elim X'-stable
    ... | sil _        = ⊥-elim X'-stable
    ... | ndbr _ _ _ _ = ⊥-elim X'-stable
    ... | mix _ _      = ⊥-elim X'-stable

    -- Lift X'-level no-ev (under B-Y) to iter-bind X' k level no-ev
    -- (under B).  X' stable forces X'.force ≡ vis fX', so any ev-step
    -- on iter-bind X' k is sVis (sMixVis/sRet require mix/ret forces).
    lift-X'-no-ev
      : ∀ (X' : ITree E (ExtI I) (A ⊎ R))
      → isStable X'
      → (∀ (e : Event√ E (A ⊎ R)) → B-Y e
           → ∀ {X'' : ITree E (ExtI I) (A ⊎ R)} → ¬ X' ─[ ev e ]─► X'')
      → ∀ (e : Event√ E R) → B e
      → ∀ {P'' : ITree E (ExtI I) R}
      → ¬ iter-bind X' (genStep h body) ─[ ev e ]─► P''
    lift-X'-no-ev X' X'-stable no-ev-X' (evl ℓ) b step
      with X' .force in X'-force-eq
    lift-X'-no-ev X' _ no-ev-X' (evl ℓ) b
                  (sVis {at = at} {a = a} iter-vis iter-just) | vis fX'
      with trans (sym iter-vis)
                  (iter-bind-force-vis X' (genStep h body) X'-force-eq)
    ... | refl =
      -- Matching refl on `vis f' ≡ vis (iter-bind-cont-vis (genStep h body) fX')`
      -- unifies the sVis-bound f' with `iter-bind-cont-vis (genStep h body) fX'`,
      -- so iter-just's type rewrites accordingly.
      case iter-bind-cont-vis-just-inv (genStep h body) fX' at a iter-just
           of λ where
           (_ , fX'-just , _) →
             no-ev-X' (evl ℓ) b (sVis X'-force-eq fX'-just)
    lift-X'-no-ev X' _ _ (evl _) _ (sMixVis iter-mix _) | vis _
      with trans (sym iter-mix)
                  (iter-bind-force-vis X' (genStep h body) X'-force-eq)
    ... | ()
    lift-X'-no-ev _ X'-stable _ (evl _) _ _ | ret _        = ⊥-elim X'-stable
    lift-X'-no-ev _ X'-stable _ (evl _) _ _ | sil _        = ⊥-elim X'-stable
    lift-X'-no-ev _ X'-stable _ (evl _) _ _ | ndbr _ _ _ _ = ⊥-elim X'-stable
    lift-X'-no-ev _ X'-stable _ (evl _) _ _ | mix _ _      = ⊥-elim X'-stable
    lift-X'-no-ev X' X'-stable no-ev-X' (√ _) b step
      with X' .force in X'-force-eq
    lift-X'-no-ev X' _ _ (√ _) _ (sRet iter-ret) | vis _
      with trans (sym iter-ret)
                  (iter-bind-force-vis X' (genStep h body) X'-force-eq)
    ... | ()
    lift-X'-no-ev _ X'-stable _ (√ _) _ _ | ret _        = ⊥-elim X'-stable
    lift-X'-no-ev _ X'-stable _ (√ _) _ _ | sil _        = ⊥-elim X'-stable
    lift-X'-no-ev _ X'-stable _ (√ _) _ _ | ndbr _ _ _ _ = ⊥-elim X'-stable
    lift-X'-no-ev _ X'-stable _ (√ _) _ _ | mix _ _      = ⊥-elim X'-stable

-- tail-on-div-lift: dispatch on Y .force.
--
-- TERMINATION NOTE: the corecursive calls in the sil/ndbr/mix arms
-- sit inside `Divergent-prepend-τ*` applied to `iter-bind-left-τ*
-- X→X'`.  When Tail-Sim.on-tau returns a non-empty X→X' chain, the
-- corecursive call is guarded by Divergent-prepend-τ-step (one
-- Divergent constructor per τ-step).  When X→X' is τ*-zero, the
-- call is unguarded — productivity then relies on a Tail-Sim
-- invariant (the bF⊑+bD⊑→Tail-Sim construction ensures non-zero
-- X-side progress whenever Y τ-steps non-trivially in body).  Agda
-- cannot verify this through syntactic termination, so we mark the
-- function NON_TERMINATING following the precedent of CSP.Hide /
-- CSP.Parallel; the model-level coinduction is sound.
{-# NON_TERMINATING #-}
--   ret (inj₁ a)  : iter-bind force = sil (iter k a); use Tail-Sim.on-ret-inj₁
--                   to get post-cycle Loop-Sim, then Loop-Sim.on-div on the
--                   divergence of (iter k a).  Prepend the X-side τ*-chain
--                   plus one extra sSil (iter-bind-force-ret-inj₁) to land
--                   at iter (genStep h body) a'-next.
--   ret (inj₂ _)  : iter-bind force = ret r — no τ-step exists; contradict.
--   sil / ndbr /  : Y has its own τ-step; rebuild it, route through
--   mix             Tail-Sim.on-tau; on success prepend X's τ*-chain and
--                   corecursively lift the rest of the divergence.
--   vis           : iter-bind force = vis — no τ-step possible; contradict.
tail-on-div-lift
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
      {X Y : ITree E (ExtI I) (A ⊎ R)}
    → Tail-Sim {ℓB = ℓB} {body = body} {body' = body'} {h = h} X Y
    → Divergent (iter-bind Y (genStep h body'))
    → Divergent (iter-bind X (genStep h body))
tail-on-div-lift {I = I} {A = A} {R = R}
                  {body = body} {body' = body'} {h = h} {X = X} {Y = Y} ts d
  with Y .force in y-force-eq
... | vis _ =
    ⊥-elim (τ-from-force-vis-impossible
              (iter-bind-force-vis Y (genStep h body') y-force-eq)
              (d .Divergent.step))
... | ret (inj₂ _) =
    ⊥-elim (no-τ-from-ret
              (iter-bind-force-ret-inj₂ Y (genStep h body') y-force-eq)
              (d .Divergent.step))
... | ret (inj₁ a-y) =
  let iter-force-sil : ITree.force (iter-bind Y (genStep h body'))
                        ≡ sil (iter (genStep h body') a-y)
      iter-force-sil = iter-bind-force-ret-inj₁ Y (genStep h body') y-force-eq
      next-eq : d .Divergent.next ≡ iter (genStep h body') a-y
      next-eq = extract-next-eq (d .Divergent.step) iter-force-sil
      div-loop-Y : Divergent (iter (genStep h body') a-y)
      div-loop-Y = subst Divergent next-eq (d .Divergent.diverge)
  in case Tail-Sim.on-ret-inj₁ ts y-force-eq of λ where
       (inj₂ X-div) → Divergent-iter-bind-left (genStep h body) X-div
       (inj₁ (X' , a'-next , X→X' , X'-eq , loop-sim)) →
         let div-loop-X : Divergent (iter (genStep h body) a'-next)
             div-loop-X = Loop-Sim.on-div loop-sim div-loop-Y
             chain : iter-bind X (genStep h body) ─[τ*]─►
                       iter (genStep h body) a'-next
             chain = τ*-then-step (iter-bind-left-τ* (genStep h body) X→X')
                                   (sSil (iter-bind-force-ret-inj₁
                                            X' (genStep h body) X'-eq))
         in Divergent-prepend-τ* chain div-loop-X
  where
    extract-next-eq
      : ∀ {t' : ITree E (ExtI I) R}
      → (s : iter-bind Y (genStep h body') ─[ τ ]─► d .Divergent.next)
      → ITree.force (iter-bind Y (genStep h body')) ≡ sil t'
      → d .Divergent.next ≡ t'
    extract-next-eq (sSil step-eq) iter-sil =
      sil-injective (trans (sym step-eq) iter-sil)
    extract-next-eq (sNdbr ndbr-eq _) iter-sil =
      case trans (sym ndbr-eq) iter-sil of λ ()
    extract-next-eq (sMixSlide mix-eq) iter-sil =
      case trans (sym mix-eq) iter-sil of λ ()
tail-on-div-lift {I = I} {A = A} {R = R}
                  {body = body} {body' = body'} {h = h} {X = X} {Y = Y} ts d
    | sil cY = handle-Y-τ (sSil y-force-eq) d
  where
    handle-Y-τ
      : Y ─[ τ ]─► cY → Divergent (iter-bind Y (genStep h body'))
      → Divergent (iter-bind _ (genStep h body))
    handle-Y-τ y-step d with Tail-Sim.on-tau ts y-step
    ... | inj₂ X-div = Divergent-iter-bind-left (genStep h body) X-div
    ... | inj₁ (X' , X→X' , ts') =
      Divergent-prepend-τ*
        (iter-bind-left-τ* (genStep h body) X→X')
        (tail-on-div-lift ts'
           (subst Divergent
              (cong (λ t → iter-bind t (genStep h body'))
                    (refl {x = cY}))
              -- d's diverge field describes Divergent at d.next.  Since
              -- iter-bind Y k force = sil (iter-bind cY k) for Y.force = sil cY,
              -- d.step must be sSil and d.next ≡ iter-bind cY k.
              (extract-diverge-cY (d .Divergent.step) (d .Divergent.diverge))))
      where
        extract-diverge-cY
          : (s : iter-bind Y (genStep h body') ─[ τ ]─► d .Divergent.next)
          → Divergent (d .Divergent.next)
          → Divergent (iter-bind cY (genStep h body'))
        extract-diverge-cY (sSil step-eq) div =
          let iter-from-Y : ITree.force (iter-bind Y (genStep h body'))
                             ≡ sil (iter-bind cY (genStep h body'))
              iter-from-Y = iter-bind-force-sil Y (genStep h body') y-force-eq
              next-eq : d .Divergent.next ≡ iter-bind cY (genStep h body')
              next-eq = sil-injective (trans (sym step-eq) iter-from-Y)
          in subst Divergent next-eq div
        extract-diverge-cY (sNdbr ndbr-eq _) _ =
          case trans (sym ndbr-eq)
                (iter-bind-force-sil Y (genStep h body') y-force-eq)
               of λ ()
        extract-diverge-cY (sMixSlide mix-eq) _ =
          case trans (sym mix-eq)
                (iter-bind-force-sil Y (genStep h body') y-force-eq)
               of λ ()
tail-on-div-lift {I = I} {A = A} {R = R}
                  {body = body} {body' = body'} {h = h} {X = X} {Y = Y} ts d
    | ndbr fY wi wa wp = handle-ndbr (d .Divergent.step) (d .Divergent.diverge)
  where
    handle-ndbr
      : (s : iter-bind Y (genStep h body') ─[ τ ]─► d .Divergent.next)
      → Divergent (d .Divergent.next)
      → Divergent (iter-bind _ (genStep h body))
    handle-ndbr (sSil step-eq) _ =
      case trans (sym step-eq)
            (iter-bind-force-ndbr Y (genStep h body') y-force-eq)
           of λ ()
    handle-ndbr (sMixSlide mix-eq) _ =
      case trans (sym mix-eq)
            (iter-bind-force-ndbr Y (genStep h body') y-force-eq)
           of λ ()
    handle-ndbr (sNdbr {i = i} {a = a} {t′ = next} ndbr-eq cont-just) div
      with trans (sym ndbr-eq)
                  (iter-bind-force-ndbr Y (genStep h body') y-force-eq)
    ... | refl =
      -- ndbr-eq unifies the iter-bind ndbr witnesses with fY's; cont-just
      -- becomes iter-bind-cont-ndbr (genStep h body') fY i a ≡ just next.
      case iter-bind-cont-ndbr-just-inv (genStep h body') fY i a cont-just
           of λ where
        (cY-branch , fY-just , next≡) →
          -- Y has sNdbr y-force-eq fY-just : Y ─[τ]→ cY-branch.
          case Tail-Sim.on-tau ts (sNdbr y-force-eq fY-just) of λ where
            (inj₂ X-div) → Divergent-iter-bind-left (genStep h body) X-div
            (inj₁ (X' , X→X' , ts')) →
              Divergent-prepend-τ*
                (iter-bind-left-τ* (genStep h body) X→X')
                (tail-on-div-lift ts'
                   (subst Divergent next≡ div))
tail-on-div-lift {I = I} {A = A} {R = R}
                  {body = body} {body' = body'} {h = h} {X = X} {Y = Y} ts d
    | mix fY QtY = handle-mix (d .Divergent.step) (d .Divergent.diverge)
  where
    handle-mix
      : (s : iter-bind Y (genStep h body') ─[ τ ]─► d .Divergent.next)
      → Divergent (d .Divergent.next)
      → Divergent (iter-bind _ (genStep h body))
    handle-mix (sSil step-eq) _ =
      case trans (sym step-eq)
            (iter-bind-force-mix Y (genStep h body') y-force-eq)
           of λ ()
    handle-mix (sNdbr ndbr-eq _) _ =
      case trans (sym ndbr-eq)
            (iter-bind-force-mix Y (genStep h body') y-force-eq)
           of λ ()
    handle-mix (sMixSlide mix-eq) div =
      let next-eq : d .Divergent.next ≡ iter-bind QtY (genStep h body')
          next-eq = mix-snd-injective
                      (trans (sym mix-eq)
                              (iter-bind-force-mix Y (genStep h body') y-force-eq))
      in case Tail-Sim.on-tau ts (sMixSlide y-force-eq) of λ where
           (inj₂ X-div) → Divergent-iter-bind-left (genStep h body) X-div
           (inj₁ (X' , X→X' , ts')) →
             Divergent-prepend-τ*
               (iter-bind-left-τ* (genStep h body) X→X')
               (tail-on-div-lift ts' (subst Divergent next-eq div))

(tail-sim→loop-sim ts) .Loop-Sim.on-vis        = tail-on-vis-lift        ts
(tail-sim→loop-sim ts) .Loop-Sim.on-tau        = tail-on-tau-lift        ts
(tail-sim→loop-sim ts) .Loop-Sim.on-stable-ref = tail-on-stable-ref-lift ts
(tail-sim→loop-sim ts) .Loop-Sim.on-div        = tail-on-div-lift        ts

-- Narrow postulates for the live vis/mix sub-cases of `construct-on-vis`.
-- Both arms are blocked by the same structural obstacle: the post-event
-- target Q' is `iter-bind (t-body' >>= k') (genStep h body')` (a
-- mid-iteration state), so the body-monotonicity hypotheses (`bF⊑`,
-- `bD⊑`) and the `sim-rec : ∀ a → Loop-Sim (genIter h body a) (genIter h body' a)`
-- callback don't directly apply — the recursive `Loop-Sim` would need
-- to relate mid-iter states, not fresh `genIter h body a''` shapes.
--
-- Discharged via the mid-loop-sim infrastructure: build a Tail-Sim at
-- the initial body-tails via `bF⊑+bD⊑→Tail-Sim` (passing in sim-rec
-- as `bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑`), lift to a Loop-Sim on the iter-bind
-- states via `tail-sim→loop-sim`, project the on-vis field.  The
-- input q-step at `genIter h body' a` lands at the iter-bind level
-- definitionally, so no subst is needed.
construct-on-vis-sVis-body-vis
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f1 : (at : AnyTypes E)
            → ContinueType at (Maybe (ITree E (ExtI I) A))}
    → ITree.force (body' a) ≡ vis f1
    → ∀ {e : Event√ E R} {Q' : ITree E (ExtI I) R}
    → (genIter h body' a) ─[ ev e ]─► Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ═[ ev e ]═► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (genIter h body a)
construct-on-vis-sVis-body-vis bF⊑ bD⊑ sim-rec a _ q-step =
    Loop-Sim.on-vis
      (tail-sim→loop-sim (bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ sim-rec a))
      q-step

construct-on-vis-sMixVis-body-mix
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f1 : (at : AnyTypes E)
            → ContinueType at (Maybe (ITree E (ExtI I) A))}
        {Qt : ITree E (ExtI I) A}
    → ITree.force (body' a) ≡ mix f1 Qt
    → ∀ {e : Event√ E R} {Q' : ITree E (ExtI I) R}
    → (genIter h body' a) ─[ ev e ]─► Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ═[ ev e ]═► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (genIter h body a)
construct-on-vis-sMixVis-body-mix bF⊑ bD⊑ sim-rec a _ q-step =
    Loop-Sim.on-vis
      (tail-sim→loop-sim (bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ sim-rec a))
      q-step

-- Field accessors with named documentation, to make the residual
-- proof obligations explicit.  Replacing the bodies of these three
-- with real constructions (without the `postulated` projection)
-- discharges the corresponding parts of Loop-Sim.

-- Forward declaration: `bF⊑+bD⊑→Iter-Sim` is mutually recursive with
-- the `construct-on-X` helpers below (via the `sim-rec` callback
-- passed to `construct-on-tau-body'-ret`).  The full definition
-- appears after the constructs.
bF⊑+bD⊑→Iter-Sim
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → ∀ (a : A) → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a)

construct-on-vis
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → ∀ (a : A) {e : Event√ E R} {Q' : ITree E (ExtI I) R}
    → (genIter h body' a) ─[ ev e ]─► Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ═[ ev e ]═► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (genIter h body a)
-- `construct-on-vis`: dispatches on q-step's constructor, then on
-- body' a's force inside each arm to discharge the structurally
-- impossible sub-cases.
--
-- * `sVis eq-f eq-j` — only body' a force = vis is live; absurd
--   shapes ret/sil/ndbr/mix dispatched via `()`.  Live arm routed
--   to `construct-on-vis-sVis-body-vis`, which derives the Loop-Sim
--   transition via the mid-loop-sim infrastructure (Tail-Sim lift).
-- * `sMixVis eq-f eq-j` — symmetric: only body' a force = mix is
--   live; absurd shapes ret/sil/vis/ndbr dispatched via `()`.  Live
--   arm routed to `construct-on-vis-sMixVis-body-mix`.
-- * `sRet eq-f` — structurally impossible: genIter h body' a's `force`
--   can never be `ret`, since k = λ a' → Ret (h a') only emits
--   `ret(inj₁ _)`, and iter-bind on `ret(inj₁ _)` is `sil`.
construct-on-vis {body' = body'} {h = h} bF⊑ bD⊑ a (sVis eq-f eq-j)
    with body' a .force in body'-eq | eq-f
... | vis _        | _    =
      construct-on-vis-sVis-body-vis bF⊑ bD⊑ (bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑)
                                      a body'-eq (sVis eq-f eq-j)
... | sil _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | ()
-- body' a = ret a': force(genIter ...) is sil (h a' = inj₁) or ret
-- (h a' = inj₂); both contradict `≡ vis f`.
... | ret a'       | eqf2 with h a' | eqf2
...   | inj₁ _ | ()
...   | inj₂ _ | ()
construct-on-vis {body' = body'} {h = h} bF⊑ bD⊑ a (sMixVis eq-f eq-j)
    with body' a .force in body'-eq | eq-f
... | mix _ _      | _    =
      construct-on-vis-sMixVis-body-mix bF⊑ bD⊑ (bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑)
                                         a body'-eq (sMixVis eq-f eq-j)
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | ret a'       | eqf2 with h a' | eqf2
...   | inj₁ _ | ()
...   | inj₂ _ | ()
-- `sRet eq-f` — with generic `h`, `genIter h body' a` CAN fire a √-tick
-- (exit) when the body returns an `a'` with `h a' = inj₂ r`.  Route this
-- exit-tick through the mid-loop-sim infrastructure exactly like the
-- vis/mix cases: project the on-vis field of the lifted Tail-Sim, which
-- handles `sRet` via `tail-on-vis-lift-sRet`.
construct-on-vis {body' = body'} {h = h} bF⊑ bD⊑ a (sRet eq-f) =
    Loop-Sim.on-vis
      (tail-sim→loop-sim (bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ (bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑) a))
      (sRet eq-f)

construct-on-tau
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → ∀ (a : A) {Q' : ITree E (ExtI I) R}
    → (genIter h body' a) ─[ τ ]─► Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (genIter h body a)
-- `construct-on-tau-body'-ret`: handles the sub-case where
-- `body' a .force ≡ ret a'-prime`, i.e. body' completes one iteration
-- to `a'-prime`.  Return type uses `iter (genStep h body') a'-prime`
-- rather than `genIter h body' a'-prime` so that the caller's Q' (which
-- after `with body' a .force | ret a'-prime` reduces to
-- `iter (genStep h body') a'-prime` via iter-bind-force-ret-inj₁)
-- matches via `refl`.  Both forms are definitionally equal —
-- `loop≡iter-genStep h` above witnesses this.
construct-on-tau-body'-ret
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {a'-prime : A} {a-cont : A}
    → ITree.force (body' a) ≡ ret a'-prime
    → h a'-prime ≡ inj₁ a-cont
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' (iter (genStep h body') a-cont) ) )
    ⊎ Divergent (genIter h body a)
construct-on-tau-body'-ret {ℓB = ℓB} {I = I} {A = A} {R = R}
                            {body = body} {body' = body'} {h = h}
                            bF⊑ bD⊑ sim-rec a {a'-prime} {a-cont} body'-eq hav-eq =
    let -- k = the loop's bind continuation.
        k : A → ITree E (ExtI I) (A ⊎ R)
        k = λ a' → Ret (h a')

        -- Step 1: body' a fires √ a'-prime to deadlock.
        bs-body' : body' a ═⟨ √ a'-prime ∷ [] ⟩═► deadlock
        bs-body' = bStep (sRet body'-eq) bNil

        -- Body' a's failure⊥ at trace [√ a'-prime] with vacuous refusal.
        f-body' : failures⊥ (body' a) (√ a'-prime ∷ []) (λ _ → Lift ℓB ⊥)
        f-body' = inj₁ (deadlock , bs-body' , deadlock-ref)

        -- Apply bF⊑ a.
        f-body : failures⊥ (body a) (√ a'-prime ∷ []) (λ _ → Lift ℓB ⊥)
        f-body = bF⊑ a f-body'
    in dispatch-f-body f-body
  where
    k : A → ITree E (ExtI I) (A ⊎ R)
    k = λ a' → Ret (h a')

    -- After h a'-prime = inj₁ a-cont, the iter step lands at a-cont.
    P-bind-force-cont : ∀ {P-bind : ITree E (ExtI I) (A ⊎ R)}
                      → ITree.force P-bind ≡ ret (h a'-prime)
                      → ITree.force P-bind ≡ ret (inj₁ a-cont)
    P-bind-force-cont {P-bind} fe = trans fe (cong (ret {E = E} {I = ExtI I}) hav-eq)

    -- Failure arm: body a fires √ a'-prime; lift to genIter h body a's
    -- τ*-progression to genIter h body a-cont; recurse via sim-rec a-cont.
    handle-failure
      : Σ[ W ∈ ITree E (ExtI I) A ]
        ( (body a) ═⟨ √ a'-prime ∷ [] ⟩═► W
        × W ref (λ _ → Lift ℓB ⊥))
      → ( Σ[ P' ∈ ITree E (ExtI I) R ]
          ( (genIter h body a) ─[τ*]─► P'
          × Loop-Sim {ℓB = ℓB} P' (genIter h body' a-cont) ) )
      ⊎ Divergent (genIter h body a)
    handle-failure (W , bs-W , _) =
        -- By tick-bigstep-lands-at-deadlock (s1 = []), W ≡ deadlock.
        let W-eq : W ≡ deadlock
            W-eq = tick-bigstep-lands-at-deadlock {s1 = []} bs-W
            bs-W-deadlock : body a ═⟨ √ a'-prime ∷ [] ⟩═► deadlock
            bs-W-deadlock = subst (λ X → body a ═⟨ √ a'-prime ∷ [] ⟩═► X)
                                  W-eq bs-W
            -- Lift the tick-bigstep through bind.  Yields:
            --   P-bind : (body a >>= k) ═⟨ [] ⟩═► P-bind
            --   force P-bind ≡ ret (h a'-prime) ≡ ret (inj₁ a-cont).
            lift-bind = lift-bind-bigstep-tick (body a) k [] bs-W-deadlock
            P-bind = proj₁ lift-bind
            bs-bind : (body a >>= k) ═⟨ [] ⟩═► P-bind
            bs-bind = proj₁ (proj₂ lift-bind)
            P-bind-force : ITree.force P-bind ≡ ret (inj₁ a-cont)
            P-bind-force = P-bind-force-cont {P-bind = P-bind} (proj₂ (proj₂ lift-bind))
            -- Lift through iter-bind.
            bs-iter : iter-bind (body a >>= k) (genStep h body) ═⟨ [] ⟩═►
                        iter-bind P-bind (genStep h body)
            bs-iter = lift-iter-bind-bigstep (body a >>= k) (genStep h body) []
                        bs-bind
            -- iter-bind P-bind has force = sil(iter (genStep h body) a-cont)
            -- = sil(genIter h body a-cont).
            iter-force-eq : ITree.force (iter-bind P-bind (genStep h body))
                            ≡ sil (genIter h body a-cont)
            iter-force-eq = iter-bind-force-ret-inj₁ P-bind (genStep h body)
                              P-bind-force
            -- One more τ-step: iter-bind P-bind ─[τ]→ genIter h body a-cont.
            step-final : iter-bind P-bind (genStep h body) ─[ τ ]─►
                           genIter h body a-cont
            step-final = sSil iter-force-eq
            -- Full τ*-chain: genIter h body a → iter-bind P-bind → genIter h body a-cont.
            τ*-chain : genIter h body a ─[τ*]─► genIter h body a-cont
            τ*-chain = bigstep-empty-to-τ*-extend bs-iter step-final
        in inj₁ (genIter h body a-cont , τ*-chain , sim-rec a-cont)
      where
        -- Convert (bs : t ═⟨ [] ⟩═► t') and (s : t' ─[τ]→ t'') to a
        -- τ*-chain t → t''.
        bigstep-empty-to-τ*-extend
          : ∀ {t t' t'' : ITree E (ExtI I) R}
          → t ═⟨ [] ⟩═► t' → t' ─[ τ ]─► t'' → t ─[τ*]─► t''
        bigstep-empty-to-τ*-extend bNil               s = τ*-step s τ*-zero
        bigstep-empty-to-τ*-extend (bTau step rest)   s =
            τ*-step step (bigstep-empty-to-τ*-extend rest s)

    -- Divergence arm: dispatch via prefix-tick-split.
    handle-divergence
      : divergences (body a) (√ a'-prime ∷ [])
      → ( Σ[ P' ∈ ITree E (ExtI I) R ]
          ( (genIter h body a) ─[τ*]─► P'
          × Loop-Sim {ℓB = ℓB} P' (genIter h body' a-cont) ) )
      ⊎ Divergent (genIter h body a)
    handle-divergence d-body =
        case prefix-tick-split [] {r = a'-prime}
                (d-body .IsDivergence.prefix)
                (d-body .IsDivergence.suffix)
                (sym (d-body .IsDivergence.split))
            of λ where
          (inj₁ (pre0 , suf0 , s1-eq , pre-eq , _)) →
            -- pre0 ≤ s1 = [].  From s1-eq : [] ≡ pre0 ++ suf0, pre0 ≡ [].
            -- Then d-body.prefix ≡ map evl pre0 ≡ map evl [] ≡ [].
            let pre0-eq : pre0 ≡ []
                pre0-eq = split-empty-l s1-eq
                prefix-eq : d-body .IsDivergence.prefix ≡ []
                prefix-eq =
                  trans pre-eq (cong (map evl) pre0-eq)
                reach-at-[] : body a ═⟨ [] ⟩═► d-body .IsDivergence.witness
                reach-at-[] =
                  subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                        prefix-eq
                        (d-body .IsDivergence.reach)
                div-body : Divergent (body a)
                div-body = divergent-prefix
                             (bigstep-empty-to-τ* reach-at-[])
                             (d-body .IsDivergence.divwit)
            in inj₂ (Divergent-iter-bind-left (genStep h body)
                       (Divergent-bind-left k div-body))
          (inj₂ (pre-eq , _)) →
            -- d-body.prefix swallows the √.  Bigstep lands at deadlock.
            -- Divergent deadlock is absurd.
            let bs-to-W : body a ═⟨ √ a'-prime ∷ [] ⟩═►
                          d-body .IsDivergence.witness
                bs-to-W =
                  subst (λ pre → body a ═⟨ pre ⟩═► d-body .IsDivergence.witness)
                        pre-eq
                        (d-body .IsDivergence.reach)
                W-deadlock : d-body .IsDivergence.witness ≡ deadlock
                W-deadlock =
                  tick-bigstep-lands-at-deadlock {s1 = []} bs-to-W
            in ⊥-elim (Divergent-deadlock-absurd
                         (subst Divergent W-deadlock
                                (d-body .IsDivergence.divwit)))

    dispatch-f-body
      : failures⊥ (body a) (√ a'-prime ∷ []) (λ _ → Lift ℓB ⊥)
      → ( Σ[ P' ∈ ITree E (ExtI I) R ]
          ( (genIter h body a) ─[τ*]─► P'
          × Loop-Sim {ℓB = ℓB} P' (genIter h body' a-cont) ) )
      ⊎ Divergent (genIter h body a)
    dispatch-f-body (inj₁ f-trip) = handle-failure f-trip
    dispatch-f-body (inj₂ d-body) = handle-divergence d-body

-- `construct-on-tau`: dispatches on q-step's constructor.
-- The sSil + body'-iterates sub-case is wired in via explicit subst
-- using a manually-proved `Q-eq : iter-bind (body' a'-prime >>= k)
-- (genStep h body') ≡ Q'`.
-- Sub-cases of construct-on-tau-sSil that aren't the body'-ret arm.
-- The ret sub-case (body' iterates) is handled constructively via
-- `construct-on-tau-body'-ret`; the sil/vis/ndbr/mix sub-cases are
-- discharged here via the mid-loop-sim infrastructure: build a
-- Tail-Sim at the initial body-tails via `bF⊑+bD⊑→Tail-Sim` (passing
-- in sim-rec), lift to a Loop-Sim on the iter-bind states via
-- `tail-sim→loop-sim`, project the on-tau field.  The input
-- `eq-f : force (genIter h body' a) ≡ sil Q'` repackages as `sSil eq-f`,
-- which Loop-Sim.on-tau accepts at the iter-bind level
-- definitionally (no subst needed — same as the sibling
-- construct-on-vis-sVis-body-vis at line 1413).
construct-on-tau-sSil-non-ret
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {Q' : ITree E (ExtI I) R}
    → ITree.force (genIter h body' a) ≡ sil Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (genIter h body a)
construct-on-tau-sSil-non-ret bF⊑ bD⊑ sim-rec a eq-f =
    Loop-Sim.on-tau
      (tail-sim→loop-sim (bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ sim-rec a))
      (sSil eq-f)

-- `construct-on-tau-sSil`: handles the sSil arm of construct-on-tau.
-- Takes `eq-f : force(genIter h body' a) ≡ sil Q'` directly and
-- pattern-matches on `body' a .force` *inside* the helper.  This
-- side-steps the boundary-level reduction issue: Agda computes
-- `force(genIter h body' a)` using the refinement from the inner
-- with-pattern, exposing the chain `loop → iter → iter-bind → bind →
-- body' a .force = ret a'-prime → sil(iter (genStep h body') a'-prime)`.
-- Pattern-matching eq-f as `refl` then unifies Q' definitionally
-- with `iter (genStep h body') a'-prime`.
{-# TERMINATING #-}
construct-on-tau-sSil
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A) {Q' : ITree E (ExtI I) R}
    → ITree.force (genIter h body' a) ≡ sil Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (genIter h body a)
construct-on-tau-sSil {ℓB = ℓB} {I = I} {A = A} {R = R}
                       {body = body} {body' = body'} {h = h}
                       bF⊑ bD⊑ sim-rec a {Q'} eq-f
    with body' a .force in body'-eq | eq-f
... | sil _        | _ =
      -- Body' τ-progresses internally.  Routed via tail-sim→loop-sim.
      construct-on-tau-sSil-non-ret bF⊑ bD⊑ sim-rec a eq-f
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | mix _ _      | ()
... | ret a'-prime | eqf2
      -- Body' completes one iteration to a'-prime.  The tag h a'-prime
      -- decides whether the loop continues (inj₁: force = sil → route to
      -- the body-iterates helper, Q' unifies with iter (genStep h body')
      -- a-cont) or exits (inj₂: force = ret → eqf2's `≡ sil Q'` absurd).
    with h a'-prime in hav-eq | eqf2
...   | inj₁ a-cont | refl =
      construct-on-tau-body'-ret bF⊑ bD⊑ sim-rec a body'-eq hav-eq
...   | inj₂ _      | ()

-- `construct-on-tau-sNdbr`: sNdbr arm.  No body'-force sub-dispatch
-- needed (genIter h body' a's force = ndbr only when body' a's force =
-- ndbr).  Route through `tail-sim→loop-sim`: build a Tail-Sim via
-- `bF⊑+bD⊑→Tail-Sim` (passing sim-rec), lift to Loop-Sim, project
-- on-tau with the same `sNdbr eq-f eq-j`.  Same definitional
-- argument as sSil-non-ret: `force (genIter h body' a) ≡ force (iter-bind
-- (body' a >>= k) (genStep h body'))` unfolds so the Loop-Sim's
-- iter-bind Q accepts the eq-f at face value.
construct-on-tau-sNdbr
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f' : (ai : AnyTypes (ExtI I))
              → ContinueType ai (Maybe (ITree E (ExtI I) R))}
        {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (f' wi wa)}
        {i : AnyTypes (ExtI I)} {ai : proj₁ i} {Q' : ITree E (ExtI I) R}
    → ITree.force (genIter h body' a) ≡ ndbr f' wi wa wp
    → f' i ai ≡ just Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (genIter h body a)
construct-on-tau-sNdbr bF⊑ bD⊑ sim-rec a eq-f eq-j =
    Loop-Sim.on-tau
      (tail-sim→loop-sim (bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ sim-rec a))
      (sNdbr eq-f eq-j)

-- `construct-on-tau-sMixSlide`: sMixSlide arm.  Same shape as
-- construct-on-tau-sNdbr.
construct-on-tau-sMixSlide
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → (sim-rec : ∀ (a : A)
                 → Loop-Sim {ℓB = ℓB} (genIter h body a) (genIter h body' a))
    → ∀ (a : A)
        {f' : (at : AnyTypes E)
              → ContinueType at (Maybe (ITree E (ExtI I) R))}
        {Q' : ITree E (ExtI I) R}
    → ITree.force (genIter h body' a) ≡ mix f' Q'
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ─[τ*]─► P'
        × Loop-Sim {ℓB = ℓB} P' Q' ) )
    ⊎ Divergent (genIter h body a)
construct-on-tau-sMixSlide bF⊑ bD⊑ sim-rec a eq-f =
    Loop-Sim.on-tau
      (tail-sim→loop-sim (bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ sim-rec a))
      (sMixSlide eq-f)

-- `construct-on-tau`: dispatches on q-step's constructor.  All three
-- τ-step shapes (sSil, sNdbr, sMixSlide) route through the
-- per-constructor helpers above.
construct-on-tau bF⊑ bD⊑ a (sSil eq-f) =
    construct-on-tau-sSil bF⊑ bD⊑ (bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑) a eq-f
construct-on-tau bF⊑ bD⊑ a (sNdbr eq-f eq-j) =
    construct-on-tau-sNdbr bF⊑ bD⊑ (bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑) a eq-f eq-j
construct-on-tau bF⊑ bD⊑ a (sMixSlide eq-f) =
    construct-on-tau-sMixSlide bF⊑ bD⊑ (bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑) a eq-f

construct-on-stable-ref
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
      {h : A → A ⊎ R}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → ∀ (a : A) {B : Event√ E R → Set ℓB}
    → isStable (genIter h body' a)
    → (∀ (e : Event√ E R) → B e → ∀ {Q' : ITree E (ExtI I) R}
         → ¬ (genIter h body' a) ─[ ev e ]─► Q')
    → ( Σ[ P' ∈ ITree E (ExtI I) R ]
        ( (genIter h body a) ─[τ*]─► P'
        × isStable P'
        × (∀ (e : Event√ E R) → B e → ∀ {P'' : ITree E (ExtI I) R}
             → ¬ P' ─[ ev e ]─► P'')))
    ⊎ Divergent (genIter h body a)
construct-on-stable-ref bF⊑ bD⊑ a q-st q-no-ev =
    Loop-Sim.on-stable-ref
      (tail-sim→loop-sim
         (bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ (bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑) a))
      q-st q-no-ev

-- `bF⊑+bD⊑→Iter-Sim`: plumb the discharged `on-div` plus the three
-- step-field constructors into a single `Loop-Sim`.  Type was
-- forward-declared above for mutual recursion with the constructs.
bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑ a = record
  { on-vis        = construct-on-vis        bF⊑ bD⊑ a
  ; on-tau        = construct-on-tau        bF⊑ bD⊑ a
  ; on-stable-ref = construct-on-stable-ref bF⊑ bD⊑ a
  ; on-div        = tail-on-div-lift
                       (bF⊑+bD⊑→Tail-Sim bF⊑ bD⊑ (bF⊑+bD⊑→Iter-Sim bF⊑ bD⊑) a)
  }

-----------------------------------------------------------------------------------------
-- Obligation 3: the public lemma.  Composes the two obligations.
-- Once Obligation 2 is discharged, this replaces the entire current
-- `loop-mono-⊑F⊥` (and the `body-body-iter-stop` postulate).
-----------------------------------------------------------------------------------------

loop-mono-⊑F⊥-via-bisim
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → ∀ a → _⊑F⊥_ {ℓB = ℓB} (loop {R = R} body a) (loop body' a)
loop-mono-⊑F⊥-via-bisim bF⊑ bD⊑ a =
    loop-sim→⊑F⊥ (bF⊑+bD⊑→Iter-Sim {h = inj₁} bF⊑ bD⊑ a)

-- `loop-mono-⊑D-via-bisim`: divergence monotonicity for `loop`,
-- extracted from the same `Loop-Sim` that drives F⊥ monotonicity.  Its
-- `on-div` field is now a real (postulate-free) construction
-- (`tail-on-div-lift`), so this fully discharges the former
-- `loop-mono-⊑D` postulate.
loop-mono-⊑D-via-bisim
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body' : HKTree E (ExtI I) A}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → ∀ a → loop {R = R} body a ⊑D loop body' a
loop-mono-⊑D-via-bisim bF⊑ bD⊑ a =
    loop-sim→⊑D (bF⊑+bD⊑→Iter-Sim {h = inj₁} bF⊑ bD⊑ a)

-- `while-mono-⊑F⊥-via-bisim`: failure-refinement monotonicity for
-- `while`.  Uses the tag `whileTag cond` so that
-- `genIter (whileTag cond) body a ≡ while cond body a` definitionally;
-- the `Loop-Sim` produced by `bF⊑+bD⊑→Iter-Sim` is therefore a
-- `Loop-Sim (while …) (while …)`, and `loop-sim→⊑F⊥` extracts the
-- `⊑F⊥` directly.  Discharges the former `while-mono-⊑F⊥` postulate.
while-mono-⊑F⊥-via-bisim
  : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
      (cond : A → Bool) {body body' : HKTree E (ExtI I) A}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → ∀ a → _⊑F⊥_ {ℓB = ℓB} (while cond body a) (while cond body' a)
while-mono-⊑F⊥-via-bisim cond bF⊑ bD⊑ a =
    loop-sim→⊑F⊥ (bF⊑+bD⊑→Iter-Sim {h = whileTag cond} bF⊑ bD⊑ a)

-- `while-mono-⊑D-via-bisim`: divergence monotonicity for `while`,
-- extracted from the same `Loop-Sim` as the F⊥ version.  Discharges
-- the former `while-mono-⊑D` postulate.
while-mono-⊑D-via-bisim
  : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
      (cond : A → Bool) {body body' : HKTree E (ExtI I) A}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body' a))
    → (∀ a → body a ⊑D body' a)
    → ∀ a → while cond body a ⊑D while cond body' a
while-mono-⊑D-via-bisim cond bF⊑ bD⊑ a =
    loop-sim→⊑D (bF⊑+bD⊑→Iter-Sim {h = whileTag cond} bF⊑ bD⊑ a)

-----------------------------------------------------------------------------------------
-- Task 1 spike outcome (mid-loop-sim plan, 2026-05-21):
--
--   We probed the on-vis init obligation at the body-tail layer.  The
--   residual constructive gap is "body-tail post-event stabilises-or-
--   diverges": given `body' a .force ≡ vis f1` and `f1 at a-evt ≡ just
--   t-body'`, derive that `body a >>= (λ a' → Ret (h a'))` either
--   bigsteps `ev (evl ...)` to some matching X' (a tail-sim continuation)
--   or diverges.
--
--   Searched for constructive helpers: only `refuse-stabilise` (in
--   `DRWeakBisim`) provides this structure, but it requires a
--   `DRWbisim` hypothesis and the classical `¬-divergent→τ-Acc`
--   postulate.  No `⊑F⊥`-only stabilisation helper exists.
--
--   Decision per plan Step 6(b): introduce a narrow body-tail-layer
--   postulate in Task 3 inside `bF⊑+bD⊑→Tail-Sim`'s on-vis field.  Net
--   effect of Tasks 1–4: 2 iter-bind-layer postulates → 1 body-tail-
--   layer postulate, plus Tail-Sim infrastructure.
-----------------------------------------------------------------------------------------

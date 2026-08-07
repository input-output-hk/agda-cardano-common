{-# OPTIONS --guardedness #-}

-- FACT-SHAPED (`⊑FD → ⊑FD`) monotonicity for the WHOLE LOOP FAMILY:
--
--   `iter-mono-⊑FD`  general iterate `iter k a`   (state-indexed step, `A → PTree (A ⊎ R)`)
--   `loop-mono-⊑FD`  stateful forever loop        (via `iter`, see the unfoldings below)
--   `while-mono-⊑FD` conditional loop             (via `iter`)
--   `loopc-mono-⊑FD` non-stateful forever loop     (`loopc` IS `loop0`, see below)
--
-- These are TRUE PRECONGRUENCES (shape 2 in `CSP.Laws.FD.IChoiceMonoFD`'s taxonomy):
-- `⊑FD` FACTS in, `⊑FD` fact out.  They SUPERSEDE and REPLACE the four shape-3
-- (`FSim → ⊑FD`) wrappers of the same names that used to sit in `CSP.Laws.FD.LoopMonoFD`
-- (now deleted).  The FSim congruences themselves (`iter-fsim` &c.) stay in
-- `CSP.Laws.FSim.LoopCong` for FSim towers.
--
-- ── THE DEFINITIONAL RELATIONSHIPS (all checked by `refl`, `CSP.Operators`:1017-1063) ──
--
--   iter k a       = iter-bind (k a) k
--   loop body a    = iter (iterStep body) a         `iterStep body a = body a >>= Ret ∘ inj₁`
--   while c body a = iter (whileStep c body) a      `whileStep` tags with `if c a′ …`
--   loop0 body     = loop (λ _ → body) tt
--   loopc body     = loop (λ _ → body) tt           ⟵ TEXTUALLY IDENTICAL to `loop0`
--
-- So `loopc` is NOT merely "like" `loop0`: the two definitions are the same term, hence
-- `loopc-mono-⊑FD` IS `CSP.Laws.FD.IterateMonoFD.loop0-mono-⊑FD` (re-exported here under
-- the `loopc` name for discoverability).  And `loop`/`while` both go through `iter` with a
-- PURE-continuation bind as the step, so the general `iter` law plus
-- `CSP.Laws.FD.BindMonoFD.bindκ-mono-⊑FD` gives both for free — which is exactly how they
-- are proved below.  `loop0` could be derived the same way, but the direct FD proof in
-- `IterateMonoFD` predates this module and is kept as-is.
--
-- ── THE ONE SIDE CONDITION: A PINNED RESULT LEVEL ──────────────────────────────────
--
-- `A R : Set ℓ` (not `A : Set ℓ`, `R : Set ℓr`).  A LEVEL constraint, not a mathematical
-- one, and the SAME one `CSP.Laws.FD.IterateMonoFD` already imposes for `loop0`: for
-- `P : PTree E I R` with `R : Set ℓr`, `_⊑F⊥_` pins the ban set to `Event√ R → Set ℓr`.
-- A failure of `iter k₂ a` bans a set over `Event√ R`; transferring the still-in-body case
-- through `k₁ a ⊑F⊥ k₂ a` needs that set RETAGGED over `Event√ (A ⊎ R)` (`banEvl`), whose
-- level must be `ℓ` because `A : Set ℓ` is forced by `iter`'s own signature.  `Lift` only
-- raises levels, so there is no way around it; the loop's `R` is phantom anyway (`iter`
-- returns only through `inj₂`), and every FD refinement in this repo is at one level.
--
-- ── POSTULATES: NONE LOCAL.  Inherited, per lemma: ─────────────────────────────────
--
--   * `iter-mono-⊑D` (hence every law here) inherits the ITERATE KÖNIG STEP
--     `CSP.Laws.FSim.LoopCong.iter-div-split`, which is CLASSICAL: it is discharged from
--     `Diverges-LEM` (`CSP.Laws.FD.FDTransfer`) plus `¬DivModA→MAcc`
--     (`CSP.Laws.FD.HideDivergence`), both pre-existing and certified from the single
--     `dne` of `CSP.Laws.ClassicalFromLEM`.  It is needed exactly once, in the `in-body`
--     arm: deciding whether an infinite τ-chain of `iter-bind t k` stays inside the
--     current iteration `t` forever or leaves it through a loop-back is not
--     constructively decidable.
--     NOTE this is a WEAKER inheritance than `IterateMonoFD`'s `loop0`: that one leans on
--     `CSP.Laws.FD.IterateFD.loop-Diverges→`, a `loop0`-SPECIFIC postulate.  `iter-div-split`
--     is a derived (postulate-free-in-itself) lemma covering every `k`, so nothing new is
--     assumed here.
--   * `iter-mono-⊑F⊥` needs NO classical ingredient of its own: the body-side
--     reconstruction is constructive (`recover-term`, via the `√` tick — a terminating run
--     yields a `√`-extended failure with the EMPTY ban set, which `⊑F⊥` transfers, and
--     `√`-run inversion is structural).  Its `⊑F⊥`-of-a-divergence arm calls `⊑D`, so the
--     PAIRED law inherits the above.
--   * `loop-mono-⊑FD` / `while-mono-⊑FD` add only `bindκ-mono-⊑FD`'s inheritance, which is
--     `Diverges-LEM` again (its König split is discharged constructively by
--     `pure→NoTauRoot`, the step's continuation being `Ret …`).
--   * `loopc-mono-⊑FD` is `loop0-mono-⊑FD` and inherits exactly what that does.

open import Level using (Level; Lift; lift; lower) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ; map-++; ++-assoc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded; Acc; acc)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.IterMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim           {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Refusals            {E = E} {I = ExtI E}
  using (Refuses; Offers; deadlock-refuses)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊑F⊥_; _⊑D_; _⊑FD_; failures⊥; divergences; IsDivergence
        ; div-extension-closed; empty-div; force-≡→⊑FD)
open import Semantics.DRBisim             {E = E} {I = ExtI E}
  using (Diverges; deadlock-converges)
open import CSP.Laws.FD.BindFD E-≟ using (⟹-trans; evl-split)
open import CSP.Laws.FD.IterateFD E-≟ using (lift-iter-bigstep)
open import CSP.Laws.FD.IterateMonoFD E-≟
  using (banEvl; runLen; IterSplitN; in-bodyN; in-doneN; in-loopN; iter-bind-invN
        ; map-evl-inj; ⟹[]→Diverges; loop0-mono-⊑FD)
open import CSP.Laws.FD.FDTransfer E-≟
  using (term→√failure; √-run-split-gen; div-√-truncate; ⟹-then-τ*)
open import CSP.Laws.Bisim.IterCong E-≟ using (iter-loop-τ; fIter-r2)
open import CSP.Laws.FSim.LoopCong E-≟
  using (iter-stable-elim; iter-stable-intro; Iter-offer-elim-stable; Iter-offer-intro-evl
        ; iter-div-split; Diverges-iter)
open import CSP.Laws.FD.BindMonoFD E-≟ using (bindκ-mono-⊑FD)
open IsDivergence

-------------------------------------------------------------------------------------
-- PART 0 : ban-set retagging across the iterate's carrier change `A ⊎ R → R`.
--
-- Only a STABLE state can refuse, and a stable iterate state sits at a stable `react`
-- of the body — which offers no `√` on either side.  So the ban set crosses the carrier
-- change by keeping its visible part and banning no `√` (`banEvl`, from `IterateMonoFD`).
-------------------------------------------------------------------------------------

-- REFUSAL ELIM: a refusal of the composite `iter-bind Q k` IS a retagged refusal of `Q`.
refuses-iter-elimᴬ : ∀ {A R : Set ℓ} {k : A → PTree E (ExtI E) (A ⊎ R)}
   {Q : PTree E (ExtI E) (A ⊎ R)} {B : Event√ R → Set ℓ}
   → Refuses (iter-bind Q k) B → Refuses Q (banEvl {X = A ⊎ R} (λ e → B (evl e)))
refuses-iter-elimᴬ {A = A} {R = R} {k = k} {Q = Q} {B = B} (st , noff) =
  iter-stable-elim Q k st , noff′
  where noff′ : ∀ e → banEvl {X = A ⊎ R} (λ e → B (evl e)) e → ¬ Offers Q e
        noff′ (evl l) Be off = noff (evl l) Be (Iter-offer-intro-evl Q k l off)
        noff′ (√ _)   Be _   = ⊥-elim (lower Be)

-- REFUSAL INTRO: a retagged refusal of `Q` lifts to one of `iter-bind Q k`.
refuses-iter-introᴬ : ∀ {A R : Set ℓ} {k : A → PTree E (ExtI E) (A ⊎ R)}
   {Q : PTree E (ExtI E) (A ⊎ R)} {B : Event√ R → Set ℓ}
   → Refuses Q (banEvl {X = A ⊎ R} (λ e → B (evl e))) → Refuses (iter-bind Q k) B
refuses-iter-introᴬ {A = A} {R = R} {k = k} {Q = Q} {B = B} (stQ , noff) =
  iter-stable-intro Q k stQ , noff′
  where noff′ : ∀ e → B e → ¬ Offers (iter-bind Q k) e
        noff′ e Be off with Iter-offer-elim-stable Q k stQ e off
        ... | l , refl , o = noff (evl l) Be o

-- DIVERGENCE INTRO: a body divergence on a purely-visible trace lifts to the iterate.
iter-div-introᴬ : ∀ {A R : Set ℓ}
   (Q : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R)) {vs : List Event}
   → divergences Q (map evl vs) → divergences (iter-bind Q k) (map evl vs)
iter-div-introᴬ Q k {vs} dd with evl-split (dd .prefix) vs (dd .suffix) (dd .split)
... | vs₁ , vs₂ , refl , refl , evs = record
  { prefix  = map evl vs₁
  ; suffix  = map evl vs₂
  ; split   = trans (cong (map evl) evs) (map-++ evl vs₁ vs₂)
  ; witness = iter-bind (dd .witness) k
  ; reach   = lift-iter-bigstep Q (dd .witness) k vs₁ (dd .reach)
  ; divwit  = Diverges-iter (dd .witness) k (dd .divwit)
  }

-------------------------------------------------------------------------------------
-- PART 1 : one complete iteration, as a run and as a prepend.
-------------------------------------------------------------------------------------

-- ONE COMPLETE ITERATION as a big-step run: the body visibly reaches a `ret (inj₁ a′)`
-- loop-back state on `s₁`, and the loop-back τ hands over to `iter k a′` (trace unchanged).
iteration-run : ∀ {A R : Set ℓ} (k : A → PTree E (ExtI E) (A ⊎ R)) {a a′ : A}
   {s₁ : List Event} {Pᵣ : PTree E (ExtI E) (A ⊎ R)}
   → k a ⟹⟨ map evl s₁ ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ a′)
   → iter k a ⟹⟨ map evl s₁ ⟩ iter k a′
iteration-run k {a} {s₁ = s₁} {Pᵣ = Pᵣ} run fe =
  ⟹-then-τ* (lift-iter-bigstep (k a) Pᵣ k s₁ run)
            (τ*-step (iter-loop-τ k Pᵣ fe) τ*-refl)

-- PREPEND a complete iteration before a divergence of the NEXT iterate.
iter-prepend-div : ∀ {A R : Set ℓ} {k : A → PTree E (ExtI E) (A ⊎ R)} {a a′ : A}
   {s₁ : List Event} {s₂ : List (Event√ R)}
   → iter k a ⟹⟨ map evl s₁ ⟩ iter k a′
   → divergences (iter k a′) s₂ → divergences (iter k a) (map evl s₁ ++ s₂)
iter-prepend-div {s₁ = s₁} run dd = record
  { prefix  = map evl s₁ ++ dd .prefix
  ; suffix  = dd .suffix
  ; split   = trans (cong (map evl s₁ ++_) (dd .split))
                    (sym (++-assoc (map evl s₁) (dd .prefix) (dd .suffix)))
  ; witness = dd .witness
  ; reach   = ⟹-trans run (dd .reach)
  ; divwit  = dd .divwit
  }

-- PREPEND a complete iteration before a failure⊥ of the NEXT iterate.
iter-prepend-fail : ∀ {A R : Set ℓ} {k : A → PTree E (ExtI E) (A ⊎ R)} {a a′ : A}
   {s₁ : List Event} {s₂ : List (Event√ R)} {B : Event√ R → Set ℓ}
   → iter k a ⟹⟨ map evl s₁ ⟩ iter k a′
   → failures⊥ (iter k a′) s₂ B → failures⊥ (iter k a) (map evl s₁ ++ s₂) B
iter-prepend-fail run (inj₁ (T , run₂ , ref)) = inj₁ (T , ⟹-trans run run₂ , ref)
iter-prepend-fail run (inj₂ dd)               = inj₂ (iter-prepend-div run dd)

-- WRAP a body-side failure⊥ on a purely-visible trace into one of the iterate (the
-- still-in-body case: re-lift the run and re-tag the refusal, or push the divergence up).
iter-wrap-fail : ∀ {A R : Set ℓ} (k : A → PTree E (ExtI E) (A ⊎ R)) (a : A)
   {vs : List Event} {B : Event√ R → Set ℓ}
   → failures⊥ (k a) (map evl vs) (banEvl {X = A ⊎ R} (λ e → B (evl e)))
   → failures⊥ (iter k a) (map evl vs) B
iter-wrap-fail k a {vs} (inj₁ (P₀ , run₀ , ref₀)) =
  inj₁ (iter-bind P₀ k , lift-iter-bigstep (k a) P₀ k vs run₀ , refuses-iter-introᴬ ref₀)
iter-wrap-fail k a {vs} (inj₂ dd) = inj₂ (iter-div-introᴬ (k a) k dd)

-------------------------------------------------------------------------------------
-- PART 2 : the RECONSTRUCTION — transporting the impl body's TERMINATION to the spec.
--
-- THE CRUX, and it is CONSTRUCTIVE.  `k₂ a` reaching a `ret x` state on the visible
-- trace `s₁` gives a `√ x`-extended failure of `k₂ a` for ANY ban set — take the EMPTY
-- one — which `k₁ a ⊑F⊥ k₂ a` transfers.  Inverting the `√`-extended run (`√-run-split-gen`,
-- structural) yields a `k₁ a`-run to a `ret x` state on the SAME `s₁` and — crucially —
-- with the SAME `x`, because the `√` event CARRIES the returned value.  That is what makes
-- the loop-back states agree on the next loop state `a′`.  The `failures⊥` alternative is
-- a divergence at `s₁ ++ √ x ∷ []`, truncated to `s₁` by `div-√-truncate`.
-------------------------------------------------------------------------------------

-- Recover the spec body's termination at the SAME value, or else a spec-side divergence.
recover-term : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (∀ a → k₁ a ⊑F⊥ k₂ a)
   → ∀ {a : A} {x : A ⊎ R} {s₁ : List Event} {Pᵣ′ : PTree E (ExtI E) (A ⊎ R)}
   → k₂ a ⟹⟨ map evl s₁ ⟩ Pᵣ′ → force Pᵣ′ ≡ ret x
   → (Σ[ Pᵣ ∈ PTree E (ExtI E) (A ⊎ R) ]
        (k₁ a ⟹⟨ map evl s₁ ⟩ Pᵣ × force Pᵣ ≡ ret x))
   ⊎ divergences (k₁ a) (map evl s₁)
recover-term k₁ k₂ f {a} {x} {s₁} run fe
  with f a {map evl s₁ ++ √ x ∷ []} {λ _ → Lift ℓ ⊥} (inj₁ (term→√failure run fe))
... | inj₁ (T , srun , _) with √-run-split-gen (map evl s₁) srun
...   | (Pᵣ , run₁ , fe₁) = inj₁ (Pᵣ , run₁ , fe₁)
recover-term k₁ k₂ f {a} {x} {s₁} run fe | inj₂ dd = inj₂ (div-√-truncate dd)

-------------------------------------------------------------------------------------
-- PART 3 : the SILENT-SPIN TRANSFER (coinductive).
--
-- A bare `Diverges (iter k₂ a)` is a τ-only chain.  At each peel (`iter-div-split`) it is
-- EITHER (a) internal to the current iteration `k₂ a` — a FINITE transfer via `k₁ a ⊑D k₂ a`,
-- pushed up by `iter-div-introᴬ` and collapsed back to a bare `Diverges` — OR (b) the
-- iteration completes silently and `iter k₂ a′` still spins: reconstruct `k₁ a`'s own silent
-- loop-back (`recover-term` at the EMPTY visible trace, via `⊑F⊥`), emit the spec-side
-- τ-chain, and CORECURSE on the residual.
--
-- Productivity is bought exactly as in `IterateMonoFD.loopD-transfer`: the corecursive call
-- sits SYNTACTICALLY in a `.rest` copattern clause, routed through the thin indirections
-- `corecurse-nowᴬ` / `loopback-tailᴬ` so the cycle never passes through a `with`-auxiliary.
-------------------------------------------------------------------------------------

-- collapse an empty-trace divergence record into a bare `Diverges` (generic carrier).
div[]→Diverges : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R}
               → divergences P [] → Diverges P
div[]→Diverges {P = P} dd = go (dd .prefix) (dd .split) (dd .reach) (dd .divwit)
  where go : ∀ {W} (pre : List (Event√ _))
           → [] ≡ pre ++ _ → P ⟹⟨ pre ⟩ W → Diverges W → Diverges P
        go []      _  reach dW = ⟹[]→Diverges reach dW
        go (_ ∷ _) () _     _

-- Transfer a body-internal silent divergence of the current iteration to the iterate.
-- FINITE (no corecursion): one `⊑D` use, one lift, one collapse.
body-spin→iter-spin : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (∀ a → k₁ a ⊑D k₂ a) → ∀ (a : A) → Diverges (k₂ a) → Diverges (iter k₁ a)
body-spin→iter-spin k₁ k₂ d a dv =
  div[]→Diverges (iter-div-introᴬ (k₁ a) k₁ {vs = []} (d a (empty-div dv)))

-- Forward declarations (no old-style `mutual`): the coinductive transfer, its thin
-- guarding indirection, and the prefix-tail walk.
iterD-transfer : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (∀ a → k₁ a ⊑F⊥ k₂ a) → (∀ a → k₁ a ⊑D k₂ a)
   → ∀ (a : A) → Diverges (iter k₂ a) → Diverges (iter k₁ a)

-- Thin guarding indirection: a clean top-level function whose body IS the corecursion, so
-- the corecursive cycle passes through a separate name rather than through
-- `iterD-transfer`'s own `with`-auxiliaries.
corecurse-nowᴬ : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (f : ∀ a → k₁ a ⊑F⊥ k₂ a) (d : ∀ a → k₁ a ⊑D k₂ a)
   → ∀ (a : A) → Diverges (iter k₂ a) → Diverges (iter k₁ a)
corecurse-nowᴬ k₁ k₂ f d a dv = iterD-transfer k₁ k₂ f d a dv

-- View the lifted spec-iteration prefix run by its FIRST τ-step.  `inj₁`: the prefix is
-- EMPTY, so the only remaining transition is the loop-back `P ─[τ]─► iter k₁ a′` (the
-- transport is discharged HERE, where the run's endpoint is still a flexible variable).
-- `inj₂`: a head τ followed by a tail run still to walk.
loopback-headᴬ : ∀ {A R : Set ℓ} (k₁ : A → PTree E (ExtI E) (A ⊎ R))
   {Pᵣ : PTree E (ExtI E) (A ⊎ R)} {a′ : A} → force Pᵣ ≡ ret (inj₁ a′)
   → {P : PTree E (ExtI E) R} → P ⟹⟨ [] ⟩ (iter-bind Pᵣ k₁)
   → (P ─[ τ ]─► iter k₁ a′)
   ⊎ (Σ[ M ∈ PTree E (ExtI E) R ]
        ((P ─[ τ ]─► M) × (M ⟹⟨ [] ⟩ iter-bind Pᵣ k₁)))
loopback-headᴬ k₁ {Pᵣ = Pᵣ} fe ⟹-refl          = inj₁ (iter-loop-τ k₁ Pᵣ fe)
loopback-headᴬ k₁          fe (⟹-τ step rest) = inj₂ (_ , step , rest)

-- GUARDED tail walk: emit each prefix τ as a `Diverges` `.step`; at the run's END emit the
-- LOOP-BACK τ and CORECURSE directly under `.rest`.  EVERY clause emits a record, so the
-- corecursion is never returned bare.
loopback-tailᴬ : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (f : ∀ a → k₁ a ⊑F⊥ k₂ a) (d : ∀ a → k₁ a ⊑D k₂ a)
   → {Pᵣ : PTree E (ExtI E) (A ⊎ R)} {a′ : A} → force Pᵣ ≡ ret (inj₁ a′)
   → Diverges (iter k₂ a′)
   → {P : PTree E (ExtI E) R} → P ⟹⟨ [] ⟩ (iter-bind Pᵣ k₁) → Diverges P
loopback-tailᴬ k₁ k₂ f d {Pᵣ = Pᵣ} {a′ = a′} fe dv ⟹-refl = record
  { step = iter-loop-τ k₁ Pᵣ fe
  ; rest = iterD-transfer k₁ k₂ f d a′ dv }
loopback-tailᴬ k₁ k₂ f d fe dv (⟹-τ step rest) = record
  { step = step
  ; rest = loopback-tailᴬ k₁ k₂ f d fe dv rest }

-- COPATTERN-based (productivity-critical): each `Diverges` projection re-runs the same
-- `iter-div-split` / `recover-term` / `loopback-headᴬ` decision chain and reads off the
-- corresponding field, so `.next`/`.step`/`.rest` stay consistent.
iterD-transfer k₁ k₂ f d a dv .Diverges.next
  with iter-div-split k₂ (k₂ a) dv
... | inj₁ dBody = body-spin→iter-spin k₁ k₂ d a dBody .Diverges.next
... | inj₂ (tᵣ , a′ , silr , feQ , dvIter)
      with recover-term k₁ k₂ f (⟹-then-τ* ⟹-refl silr) feQ
...     | inj₂ ddiv = div[]→Diverges (iter-div-introᴬ (k₁ a) k₁ {vs = []} ddiv) .Diverges.next
...     | inj₁ (Pᵣ , bodybs , bodyfe)
          with loopback-headᴬ k₁ bodyfe (lift-iter-bigstep (k₁ a) Pᵣ k₁ [] bodybs)
...         | inj₁ _           = iter k₁ a′
...         | inj₂ (M , _ , _) = M

iterD-transfer k₁ k₂ f d a dv .Diverges.step
  with iter-div-split k₂ (k₂ a) dv
... | inj₁ dBody = body-spin→iter-spin k₁ k₂ d a dBody .Diverges.step
... | inj₂ (tᵣ , a′ , silr , feQ , dvIter)
      with recover-term k₁ k₂ f (⟹-then-τ* ⟹-refl silr) feQ
...     | inj₂ ddiv = div[]→Diverges (iter-div-introᴬ (k₁ a) k₁ {vs = []} ddiv) .Diverges.step
...     | inj₁ (Pᵣ , bodybs , bodyfe)
          with loopback-headᴬ k₁ bodyfe (lift-iter-bigstep (k₁ a) Pᵣ k₁ [] bodybs)
...         | inj₁ head            = head
...         | inj₂ (M , head , _)  = head

iterD-transfer k₁ k₂ f d a dv .Diverges.rest
  with iter-div-split k₂ (k₂ a) dv
... | inj₁ dBody = body-spin→iter-spin k₁ k₂ d a dBody .Diverges.rest
... | inj₂ (tᵣ , a′ , silr , feQ , dvIter)
      with recover-term k₁ k₂ f (⟹-then-τ* ⟹-refl silr) feQ
...     | inj₂ ddiv = div[]→Diverges (iter-div-introᴬ (k₁ a) k₁ {vs = []} ddiv) .Diverges.rest
...     | inj₁ (Pᵣ , bodybs , bodyfe)
          with loopback-headᴬ k₁ bodyfe (lift-iter-bigstep (k₁ a) Pᵣ k₁ [] bodybs)
...         | inj₁ _              = corecurse-nowᴬ k₁ k₂ f d a′ dvIter
...         | inj₂ (M , _ , tail) = loopback-tailᴬ k₁ k₂ f d bodyfe dvIter tail

-------------------------------------------------------------------------------------
-- PART 4 : the two halves of `iter-mono-⊑FD`, by well-founded recursion on `runLen`.
--
-- A run of `iter k₂ a` decomposes (`iter-bind-invN`) into three arms; the `in-loop` arm's
-- residual run is SHORTER (the loop-back consumes ≥1 τ), which is what `Acc _<_` consumes.
-------------------------------------------------------------------------------------

-- the ⊑D half's worker.
mono-div : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (∀ a → k₁ a ⊑F⊥ k₂ a) → (∀ a → k₁ a ⊑D k₂ a)
   → ∀ (a : A) {s : List (Event√ R)} (Q : PTree E (ExtI E) R)
   → (run : iter k₂ a ⟹⟨ s ⟩ Q) → Acc _<_ (runLen run) → Diverges Q
   → divergences (iter k₁ a) s

-- the ⊑F⊥ half's worker.
mono-fail : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (∀ a → k₁ a ⊑F⊥ k₂ a) → (∀ a → k₁ a ⊑D k₂ a)
   → ∀ (a : A) {s : List (Event√ R)} {B : Event√ R → Set ℓ} (Q : PTree E (ExtI E) R)
   → (run : iter k₂ a ⟹⟨ s ⟩ Q) → Acc _<_ (runLen run) → Refuses Q B
   → failures⊥ (iter k₁ a) s B

mono-div {A = A} {R = R} k₁ k₂ f d a Q run (acc rs) dvQ
  with iter-bind-invN (k₂ a) k₂ run
-- ── in-body : the divergence is inside the CURRENT iteration.  THE classical step.
... | in-bodyN {P′ = P′} {vs = vs} bs refl
      with iter-div-split k₂ P′ dvQ
-- (a) it stays in the body: transfer via `⊑D` and push up.
...     | inj₁ dP′ =
          iter-div-introᴬ (k₁ a) k₁
            (d a (record { prefix  = map evl vs ; suffix = []
                         ; split   = sym (++-identityʳ (map evl vs))
                         ; witness = P′ ; reach = bs ; divwit = dP′ }))
-- (b) the iteration completes silently and the NEXT iterate spins: reconstruct the
--     spec-side loop-back and transfer the spin coinductively.
mono-div {A = A} {R = R} k₁ k₂ f d a Q run (acc rs) dvQ
    | in-bodyN {P′ = P′} {vs = vs} bs refl
      | inj₂ (tᵣ , a′ , silr , feQ , dvIter)
        with recover-term k₁ k₂ f (⟹-then-τ* bs silr) feQ
...       | inj₁ (Pᵣ , bodybs , bodyfe) =
            subst (divergences (iter k₁ a)) (++-identityʳ (map evl vs))
              (iter-prepend-div (iteration-run k₁ bodybs bodyfe)
                 (empty-div (iterD-transfer k₁ k₂ f d a′ dvIter)))
...       | inj₂ ddiv = iter-div-introᴬ (k₁ a) k₁ ddiv
-- ── in-done : the iterate TERMINATED, so `Q ≡ deadlock`, which cannot diverge.
mono-div {A = A} {R = R} k₁ k₂ f d a Q run (acc rs) dvQ
    | in-doneN bs fe refl = ⊥-elim (deadlock-converges dvQ)
-- ── in-loop : one complete iteration then a SHORTER run.  Recurse and prepend.
mono-div {A = A} {R = R} k₁ k₂ f d a Q run (acc rs) dvQ
    | in-loopN {a′ = a′} {s₁ = s₁} {s₂ = s₂} bs fe kr lt
      with recover-term k₁ k₂ f bs fe
...   | inj₁ (Pᵣ , bodybs , bodyfe) =
        iter-prepend-div (iteration-run k₁ bodybs bodyfe)
          (mono-div k₁ k₂ f d a′ Q kr (rs lt) dvQ)
...   | inj₂ ddiv =
        div-extension-closed {t = s₂} (iter-div-introᴬ (k₁ a) k₁ ddiv)

mono-fail {A = A} {R = R} k₁ k₂ f d a {B = B} Q run (acc rs) ref
  with iter-bind-invN (k₂ a) k₂ run
-- ── in-body : an in-progress iteration refuses; map the refusal body-wise via `⊑F⊥`.
... | in-bodyN {P′ = P′} {vs = vs} bs refl =
      iter-wrap-fail k₁ a
        (f a (inj₁ (P′ , bs , refuses-iter-elimᴬ {k = k₂} {Q = P′} {B = B} ref)))
-- ── in-done : the iterate terminated on `s₁ ++ √ r ∷ []`.  Reconstruct the spec's OWN
--    termination at the same `r` and re-tick; the endpoint `deadlock` refuses everything.
... | in-doneN {r = r} {s₁ = s₁} {Pᵣ = Pᵣ} bs fe refl
      with recover-term k₁ k₂ f bs fe
...     | inj₁ (Pᵣ₁ , bodybs , bodyfe) =
          inj₁ (term→√failure (lift-iter-bigstep (k₁ a) Pᵣ₁ k₁ s₁ bodybs)
                              (fIter-r2 k₁ Pᵣ₁ bodyfe))
...     | inj₂ ddiv =
          inj₂ (div-extension-closed {t = √ r ∷ []} (iter-div-introᴬ (k₁ a) k₁ ddiv))
-- ── in-loop : one complete iteration then a SHORTER run.  Recurse and prepend.
mono-fail {A = A} {R = R} k₁ k₂ f d a {B = B} Q run (acc rs) ref
    | in-loopN {a′ = a′} {s₁ = s₁} {s₂ = s₂} bs fe kr lt
      with recover-term k₁ k₂ f bs fe
...   | inj₁ (Pᵣ , bodybs , bodyfe) =
        iter-prepend-fail (iteration-run k₁ bodybs bodyfe)
          (mono-fail k₁ k₂ f d a′ Q kr (rs lt) ref)
...   | inj₂ ddiv =
        inj₂ (div-extension-closed {t = s₂} (iter-div-introᴬ (k₁ a) k₁ ddiv))

-------------------------------------------------------------------------------------
-- PART 5 : the laws.
-------------------------------------------------------------------------------------

-- the DIVERGENCE half: `iter` is ⊑D-monotone in its step, pointwise.
iter-mono-⊑D : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (∀ a → k₁ a ⊑F⊥ k₂ a) → (∀ a → k₁ a ⊑D k₂ a)
   → ∀ (a : A) → iter k₁ a ⊑D iter k₂ a
iter-mono-⊑D k₁ k₂ f d a {s} dv =
  subst (divergences (iter k₁ a)) (sym (dv .split))
    (div-extension-closed {t = dv .suffix}
      (mono-div k₁ k₂ f d a (dv .witness) (dv .reach)
                (<-wellFounded (runLen (dv .reach))) (dv .divwit)))

-- the STABLE-FAILURE half: `iter` is ⊑F⊥-monotone in its step, pointwise.
iter-mono-⊑F⊥ : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (∀ a → k₁ a ⊑F⊥ k₂ a) → (∀ a → k₁ a ⊑D k₂ a)
   → ∀ (a : A) → iter k₁ a ⊑F⊥ iter k₂ a
iter-mono-⊑F⊥ k₁ k₂ f d a (inj₁ (Q , run , ref)) =
  mono-fail k₁ k₂ f d a Q run (<-wellFounded (runLen run)) ref
iter-mono-⊑F⊥ k₁ k₂ f d a (inj₂ dv) = inj₂ (iter-mono-⊑D k₁ k₂ f d a dv)

-- ITERATION IS A ⊑FD-PRECONGRUENCE in its step, pointwise in the loop state.
iter-mono-⊑FD : ∀ {A R : Set ℓ} (k₁ k₂ : A → PTree E (ExtI E) (A ⊎ R))
   → (∀ a → k₁ a ⊑FD k₂ a) → ∀ (a : A) → iter k₁ a ⊑FD iter k₂ a
iter-mono-⊑FD k₁ k₂ kk a =
  iter-mono-⊑F⊥ k₁ k₂ (λ b → proj₁ (kk b)) (λ b → proj₂ (kk b)) a
  , iter-mono-⊑D  k₁ k₂ (λ b → proj₁ (kk b)) (λ b → proj₂ (kk b)) a

-- `loop`'s step, as a TOP-LEVEL name (`loop`'s own is `where`-bound).  Definitionally
-- equal to it, so `loop body a` reduces to `iter (loopStepᴬ body) a` by `refl`.
loopStepᴬ : ∀ {A R : Set ℓ}
          → (A → PTree E (ExtI E) A) → A → PTree E (ExtI E) (A ⊎ R)
loopStepᴬ body a = body a >>= λ a′ → Ret (inj₁ a′)

-- sanity: `loop` IS `iter` over `loopStepᴬ`.
loop-unfoldᴬ : ∀ {A R : Set ℓ} (body : A → PTree E (ExtI E) A) (a : A)
             → loop {R = R} body a ≡ iter (loopStepᴬ body) a
loop-unfoldᴬ body a = refl

-- THE STATEFUL FOREVER LOOP IS A ⊑FD-PRECONGRUENCE in its body, pointwise in the state.
-- The step's continuation is PURE (`Ret …`), so `bindκ-mono-⊑FD` needs no side condition.
loop-mono-⊑FD : ∀ {A R : Set ℓ} (body₁ body₂ : A → PTree E (ExtI E) A)
   → (∀ a → body₁ a ⊑FD body₂ a) → ∀ (a : A) → loop {R = R} body₁ a ⊑FD loop {R = R} body₂ a
loop-mono-⊑FD {A = A} {R = R} body₁ body₂ bb =
  iter-mono-⊑FD (loopStepᴬ body₁) (loopStepᴬ body₂) step-mono
  where
    κ : A → PTree E (ExtI E) (A ⊎ R)
    κ a′ = Ret (inj₁ a′)
    step-mono : ∀ a → loopStepᴬ {R = R} body₁ a ⊑FD loopStepᴬ {R = R} body₂ a
    step-mono a = bindκ-mono-⊑FD κ κ (λ a′ → inj₁ a′ , refl) (bb a)
                                 (λ a′ → force-≡→⊑FD refl)

-- `while`'s step, as a TOP-LEVEL name (definitionally `while`'s own `where`-bound one).
whileStepᴬ : ∀ {A : Set ℓ}
           → (A → Bool) → (A → PTree E (ExtI E) A) → A → PTree E (ExtI E) (A ⊎ A)
whileStepᴬ cond body a = body a >>= λ a′ → Ret (if cond a′ then inj₁ a′ else inj₂ a′)

-- sanity: `while` IS `iter` over `whileStepᴬ`.
while-unfoldᴬ : ∀ {A : Set ℓ} (cond : A → Bool) (body : A → PTree E (ExtI E) A) (a : A)
              → while cond body a ≡ iter (whileStepᴬ cond body) a
while-unfoldᴬ cond body a = refl

-- THE CONDITIONAL LOOP IS A ⊑FD-PRECONGRUENCE in its body, pointwise in the state.  The
-- condition is SHARED (it is not an operand: `while` is monotone in `body` for each fixed
-- `cond`, and two different conditions give unrelated processes).
while-mono-⊑FD : ∀ {A : Set ℓ} (cond : A → Bool) (body₁ body₂ : A → PTree E (ExtI E) A)
   → (∀ a → body₁ a ⊑FD body₂ a) → ∀ (a : A) → while cond body₁ a ⊑FD while cond body₂ a
while-mono-⊑FD {A = A} cond body₁ body₂ bb =
  iter-mono-⊑FD (whileStepᴬ cond body₁) (whileStepᴬ cond body₂) step-mono
  where
    κ : A → PTree E (ExtI E) (A ⊎ A)
    κ a′ = Ret (if cond a′ then inj₁ a′ else inj₂ a′)
    step-mono : ∀ a → whileStepᴬ cond body₁ a ⊑FD whileStepᴬ cond body₂ a
    step-mono a = bindκ-mono-⊑FD κ κ
                    (λ a′ → (if cond a′ then inj₁ a′ else inj₂ a′) , refl)
                    (bb a) (λ a′ → force-≡→⊑FD refl)

-- THE NON-STATEFUL FOREVER LOOP IS A ⊑FD-PRECONGRUENCE in its body.  `loopc` and `loop0`
-- are the SAME definition (`loop (λ _ → body) tt`), so this IS
-- `CSP.Laws.FD.IterateMonoFD.loop0-mono-⊑FD`, named after `loopc` for discoverability.
loopc-mono-⊑FD : ∀ {R : Set ℓ} (B₁ B₂ : PTree E (ExtI E) (⊤ {ℓ}))
   → B₁ ⊑FD B₂ → loopc {R = R} B₁ ⊑FD loopc {R = R} B₂
loopc-mono-⊑FD = loop0-mono-⊑FD

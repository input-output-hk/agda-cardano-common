{-# OPTIONS --guardedness #-}

-- FACT-SHAPED `⊑FD`-MONOTONICITY for THROW: `Θ-mono-⊑FD` takes two `⊑FD` FACTS and
-- returns a `⊑FD` fact.  This is the TRUE PRECONGRUENCE for `_⟦_▷_`, monotone in BOTH
-- the body and the handler, unconditionally (no divergence-freedom, no alphabet
-- restriction, no König side condition).
--
-- WHY A SEPARATE LAW: see `CSP.Laws.FD.IChoiceMonoFD`'s header for the three-shape
-- taxonomy (`FSim → FSim` congruence / `⊑FD → ⊑FD` precongruence / `FSim → ⊑FD`
-- cash-out).  The shape-3 `Θ-mono-⊑FD` that used to live in `CSP.Laws.FSim.ThrowCong`
-- was RETIRED in favour of the law below, which is strictly stronger (write
-- `fsim→⊑FD (Θ-fsim …)` to recover the old use).  Keep `Θ-fsim` for FSim towers and
-- this law for facts.
--
-- PROOF ARCHITECTURE.  The whole proof rests on ONE new structural decomposition,
-- `Θ-reach-split` (Layer 2): a weak run of `P ⟦ A ▷ Q` is exactly one of
--   • `θNo`   — the run never left the body: an `A`-free (hence throw-free) trace `u`
--               with `P ⟹⟨ u ⟩ P*` and the residual `P* ⟦ A ▷ Q`;
--   • `θFire` — an `A`-free `u`, then a body event IN `A` that fires the throw, then the
--               remainder of the run belongs entirely to the HANDLER (`Q ⟹⟨ v ⟩ W`);
--   • `θDone` — an `A`-free `u`, then the body terminated (`force P* ≡ ret r`) and the
--               composite `√`s into `deadlock`.
-- This is possible because throw's τ-space IS the body's (`Θ-τ-elim`) and the handler is
-- dormant until a visible `A`-event fires it — the same reason `Θ-Diverges→` is
-- structural.  `A`-freeness is tracked by the inductive `ΘFree` (Layer 1) and is what
-- lets a transferred body divergence / failure be LIFTED back through the throw
-- (`Θ-run-lift` / `Θ-div-lift`): a prefix of an `A`-free trace is `A`-free.
--
-- Each half then transfers the decomposed pieces through the hypotheses:
--   ⊑D  half : `θNo` → `Θ-Diverges→` + the body's `⊑D` + `Θ-div-lift`;
--              `θFire` → the handler's `⊑D` prepended to a re-fired composite run
--              (`Θ-fire-transfer`, via `FD→trace⊥` on the body);
--              `θDone` → vacuous (`deadlock` cannot diverge).
--   ⊑F⊥ half : `θNo` → offers/stability of `P ⟦ A ▷ ·` ARE the body's
--              (`Θ-Refuses→`/`Θ-Refuses←`), so the composite refusal is a body refusal;
--              `θFire` → the handler's `⊑F⊥` prepended to the re-fired run;
--              `θDone` → the body's √-extension trick (`term→√failure`).
--
-- POSTULATES: ZERO local.  INHERITED: exactly the two that sit behind
-- `CSP.Laws.FD.FDTransfer`'s `FD→trace⊥` — `Diverges-LEM` (`FDTransfer`) and
-- `¬-divergent→normal` (`Semantics.DRImpliesFD`), each certified derivable from a single
-- `dne` in `CSP.Laws.ClassicalFromLEM`.  This is the SAME inheritance as
-- `Par-mono-⊑FD`, and `FD→trace⊥` is used in exactly one place: `Θ-fire-transfer`, to
-- learn that the refined body can still reach and fire the same `A`-event.
--
-- `agda --safe CSP/Laws/FD/ThrowMonoFD.agda` therefore FAILS, and it fails only on
-- `¬-divergent→normal`.  Note precisely WHAT is *not* inherited: there is NO
-- König-style `Θ-Diverges→` postulate.  Throw's divergence inversion is STRUCTURAL
-- (`CSP.Laws.Traces.TraceLawsThrowInterrupt`, itself `--safe` clean), unlike
-- `□-Diverges→` / `Par-Diverges→` / `△-Diverges→`.  So the `θNo` and `θDone` arms of both
-- halves are fully constructive; only the fire arm reaches for classical strength.

open import Level using (Level; Lift; lift; lower; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.ThrowMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Refusals            {E = E} {I = ExtI E}
  using (Refuses; Offers; deadlock-refuses)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.DRBisim             {E = E} {I = ExtI E}
  using (Diverges; deadlock-converges)
open import Semantics.Stability           {E = E} {I = ExtI E}
  using (mk-stable; stable-not-ret; stable-not-sil; stable-no-τ; stable-react-τc)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊑F⊥_; _⊑D_; _⊑FD_; failures⊥; divergences; IsDivergence; div-extension-closed)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using (force-Θ-ret; force-Θ-sil; force-Θ-react;
         Θ-τ-elim; Θ-ev-elim; ΘevR; Θthrow; Θpass; Θdone;
         Θ-τ-lift-P; Θ-Diverges-L; Θ-Diverges→; Θ-throw-step; Θ-pass-step)
open import CSP.Laws.FD.FDTransfer E-≟
  using (FD→trace⊥; term→√failure; √-run-split-gen; div-√-truncate;
         snoc-split; deadlock-run-inv)
open IsDivergence

private
  variable
    ℓr : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- Layer 0 : tiny generic plumbing (local copies, per the FDTransfer precedent).
-------------------------------------------------------------------------------------

-- compose two weak runs, concatenating their traces
-- (local copy of `CSP.Laws.FD.SeqDistR`'s `⟹-trans`, kept here to avoid the import)
⟹-trans : {p q r : PTree E (ExtI E) R} {s t : List (Event√ R)}
        → p ⟹⟨ s ⟩ q → q ⟹⟨ t ⟩ r → p ⟹⟨ s ++ t ⟩ r
⟹-trans ⟹-refl          qr = qr
⟹-trans (⟹-τ st rest)   qr = ⟹-τ  st (⟹-trans rest qr)
⟹-trans (⟹-ev st rest)  qr = ⟹-ev st (⟹-trans rest qr)

-- package a full-trace reach to a diverging state as an `IsDivergence` (empty suffix)
-- (local copy of `CSP.Laws.FD.ParallelMonoFD`'s `mk-full-div`)
mk-full-div : {T T* : PTree E (ExtI E) R} {s : List (Event√ R)}
            → T ⟹⟨ s ⟩ T* → Diverges T* → IsDivergence T s
mk-full-div {T* = T*} {s = s} run dv = record
  { prefix = s ; suffix = [] ; split = sym (++-identityʳ s)
  ; witness = T* ; reach = run ; divwit = dv }

-- prepend a weak run to a divergence: the reaches compose and the prefix grows
div-prepend-run : {P Q : PTree E (ExtI E) R} {t v : List (Event√ R)}
                → P ⟹⟨ t ⟩ Q → divergences Q v → divergences P (t ++ v)
div-prepend-run {t = t} run d = record
  { prefix  = t ++ d .prefix
  ; suffix  = d .suffix
  ; split   = trans (cong (t ++_) (d .split)) (sym (++-assoc t (d .prefix) (d .suffix)))
  ; witness = d .witness
  ; reach   = ⟹-trans run (d .reach)
  ; divwit  = d .divwit
  }

-- prepend a weak run to a stable failure (same refusing witness, longer trace)
fail-prepend-run : {P Q : PTree E (ExtI E) R} {t v : List (Event√ R)}
                   {X : Event√ R → Set ℓr}
                 → P ⟹⟨ t ⟩ Q → failures Q v X → failures P (t ++ v) X
fail-prepend-run run (W , reach , ref) = W , ⟹-trans run reach , ref

-------------------------------------------------------------------------------------
-- Layer 1 : `A`-FREE (throw-free) traces.  A trace the throw lets PASS: every element
-- is a visible event OUTSIDE `A` (never a `√`, which would end the body).  A prefix of
-- an `A`-free trace is `A`-free, which is exactly what the divergence lift needs.
-------------------------------------------------------------------------------------

-- every event of the trace is visible and outside the throw set `A`
data ΘFree (A : EventSet) {ℓr} {R : Set ℓr} : List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  []ᶠ  : ΘFree A []
  _∷ᶠ_ : ∀ {at : AnyTypes E} {a : proj₁ at} {s : List (Event√ R)}
       → ¬ (A .mem at a) → ΘFree A s
       → ΘFree A (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)

-- `A`-freeness is prefix-closed
ΘFree-prefix : {A : EventSet} (p : List (Event√ R)) {q : List (Event√ R)}
             → ΘFree A (p ++ q) → ΘFree A p
ΘFree-prefix []      f          = []ᶠ
ΘFree-prefix (_ ∷ p) (¬m ∷ᶠ f) = ¬m ∷ᶠ ΘFree-prefix p f

-------------------------------------------------------------------------------------
-- Layer 2 : the RUN DECOMPOSITION for throw.  A weak run of `P ⟦ A ▷ Q` is a body run
-- over an `A`-free trace, optionally followed by a fire (handing the rest of the run to
-- the handler) or by the body's termination (handing it to `deadlock`).
-------------------------------------------------------------------------------------

-- the three shapes a weak run of `P ⟦ A ▷ Q` can take
data ΘReach (A : EventSet) {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R)
     : List (Event√ R) → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  -- the throw never fired: the trace is `A`-free and the residual still carries it
  θNo   : ∀ {u : List (Event√ R)} {P* : PTree E (ExtI E) R}
        → ΘFree A u → P ⟹⟨ u ⟩ P*
        → ΘReach A P Q u (P* ⟦ A ▷ Q)
  -- the throw FIRED on a body event in `A`; the rest of the run is the handler's
  θFire : ∀ {u : List (Event√ R)} {at : AnyTypes E} {a : proj₁ at}
            {P* P′ : PTree E (ExtI E) R} {v : List (Event√ R)} {W : PTree E (ExtI E) R}
        → ΘFree A u → P ⟹⟨ u ⟩ P*
        → P* ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P′
        → A .mem at a
        → Q ⟹⟨ v ⟩ W
        → ΘReach A P Q (u ++ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ v) W
  -- the body TERMINATED: the composite ticks `√ r` and strands at `deadlock`
  θDone : ∀ {u : List (Event√ R)} {P* : PTree E (ExtI E) R} {r : R}
            {v : List (Event√ R)} {W : PTree E (ExtI E) R}
        → ΘFree A u → P ⟹⟨ u ⟩ P* → PTree.force P* ≡ ret r
        → deadlock ⟹⟨ v ⟩ W
        → ΘReach A P Q (u ++ √ r ∷ v) W

-- prepend a body τ-step to a decomposition (the trace is unchanged)
ΘReach-τ : {A : EventSet} {P P′ Q : PTree E (ExtI E) R}
           {s : List (Event√ R)} {W : PTree E (ExtI E) R}
         → P ─[ τ ]─► P′ → ΘReach A P′ Q s W → ΘReach A P Q s W
ΘReach-τ st (θNo f r)               = θNo f (⟹-τ st r)
ΘReach-τ st (θFire f r st′ m rQ)    = θFire f (⟹-τ st r) st′ m rQ
ΘReach-τ st (θDone f r eq rd)       = θDone f (⟹-τ st r) eq rd

-- prepend a PASSED body event (outside `A`) to a decomposition
ΘReach-ev : {A : EventSet} {P P′ Q : PTree E (ExtI E) R}
            {at : AnyTypes E} {a : proj₁ at}
            {s : List (Event√ R)} {W : PTree E (ExtI E) R}
          → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P′ → ¬ (A .mem at a)
          → ΘReach A P′ Q s W
          → ΘReach A P Q (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) W
ΘReach-ev st ¬m (θNo f r)            = θNo (¬m ∷ᶠ f) (⟹-ev st r)
ΘReach-ev st ¬m (θFire f r st′ m rQ) = θFire (¬m ∷ᶠ f) (⟹-ev st r) st′ m rQ
ΘReach-ev st ¬m (θDone f r eq rd)    = θDone (¬m ∷ᶠ f) (⟹-ev st r) eq rd

-- THE DECOMPOSITION: recursion on the composite run, inverting each step with
-- `Θ-τ-elim` / `Θ-ev-elim` and prepending it to the residual decomposition
Θ-reach-split : (P Q : PTree E (ExtI E) R) (A : EventSet)
                {s : List (Event√ R)} {W : PTree E (ExtI E) R}
              → (P ⟦ A ▷ Q) ⟹⟨ s ⟩ W → ΘReach A P Q s W
Θ-reach-split P Q A ⟹-refl = θNo []ᶠ ⟹-refl
Θ-reach-split P Q A (⟹-τ step rest) with Θ-τ-elim P Q step
... | (P′ , sP , refl) = ΘReach-τ sP (Θ-reach-split P′ Q A rest)
Θ-reach-split P Q A (⟹-ev step rest) with Θ-ev-elim P Q step
... | Θthrow {at = at} {a = a} sP m  = θFire []ᶠ ⟹-refl sP m rest
... | Θpass {at = at} {a = a} {P₁ = P′} sP ¬m =
      ΘReach-ev {at = at} {a = a} sP ¬m (Θ-reach-split P′ Q A rest)
... | Θdone eqPr = θDone []ᶠ ⟹-refl eqPr rest

-------------------------------------------------------------------------------------
-- Layer 3 : LIFTS.  An `A`-free body run / body divergence lifts back through the
-- throw; an `A`-free run followed by an `A`-event re-fires the throw.
-------------------------------------------------------------------------------------

-- lift an `A`-free body run through the throw (τ's by `Θ-τ-lift-P`, events by
-- `Θ-pass-step` — the `A`-freeness certificate says every event passes)
Θ-run-lift : (Q : PTree E (ExtI E) R) (A : EventSet)
             {u : List (Event√ R)} {P P* : PTree E (ExtI E) R}
           → ΘFree A u → P ⟹⟨ u ⟩ P* → (P ⟦ A ▷ Q) ⟹⟨ u ⟩ (P* ⟦ A ▷ Q)
Θ-run-lift Q A f ⟹-refl = ⟹-refl
Θ-run-lift Q A f (⟹-τ st rest) = ⟹-τ (Θ-τ-lift-P st) (Θ-run-lift Q A f rest)
Θ-run-lift Q A (_∷ᶠ_ {at = at} {a = a} ¬m f) (⟹-ev st rest) =
  ⟹-ev (Θ-pass-step {at = at} {a = a} st ¬m) (Θ-run-lift Q A f rest)

-- lift a body divergence at an `A`-free trace through the throw (the divergence prefix
-- is a prefix of an `A`-free trace, hence itself `A`-free)
Θ-div-lift : (Q : PTree E (ExtI E) R) (A : EventSet)
             {u : List (Event√ R)} {P : PTree E (ExtI E) R}
           → ΘFree A u → divergences P u → divergences (P ⟦ A ▷ Q) u
Θ-div-lift Q A f d = record
  { prefix  = d .prefix
  ; suffix  = d .suffix
  ; split   = d .split
  ; witness = (d .witness) ⟦ A ▷ Q
  ; reach   = Θ-run-lift Q A (ΘFree-prefix (d .prefix) (subst (ΘFree _) (d .split) f))
                             (d .reach)
  ; divwit  = Θ-Diverges-L (d .divwit)
  }

-- the run's leading τ's lift, then the `A`-event FIRES the throw onto the handler
Θ-fire-peel : (Q : PTree E (ExtI E) R) (A : EventSet)
              {at : AnyTypes E} {a : proj₁ at}
              {P V : PTree E (ExtI E) R} {w : List (Event√ R)}
            → A .mem at a
            → P ⟹⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ w ⟩ V
            → (P ⟦ A ▷ Q) ⟹⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ [] ⟩ Q
Θ-fire-peel Q A m (⟹-τ st rest) = ⟹-τ (Θ-τ-lift-P st) (Θ-fire-peel Q A m rest)
Θ-fire-peel Q A {at = at} {a = a} m (⟹-ev st rest) =
  ⟹-ev (Θ-throw-step {at = at} {a = a} st m) ⟹-refl

-- a body run over `u ++ ev x ∷ w` with `u` `A`-free and `x ∈ A` gives a composite run
-- that passes `u` and then fires, landing exactly on the handler
Θ-run-fire : (Q : PTree E (ExtI E) R) (A : EventSet)
             {u : List (Event√ R)} {at : AnyTypes E} {a : proj₁ at}
             {w : List (Event√ R)} {P V : PTree E (ExtI E) R}
           → ΘFree A u → A .mem at a
           → P ⟹⟨ u ++ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ w ⟩ V
           → (P ⟦ A ▷ Q) ⟹⟨ u ++ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ [] ⟩ Q
Θ-run-fire Q A []ᶠ m run = Θ-fire-peel Q A m run
Θ-run-fire Q A (¬m ∷ᶠ f) m (⟹-τ st rest) =
  ⟹-τ (Θ-τ-lift-P st) (Θ-run-fire Q A (¬m ∷ᶠ f) m rest)
Θ-run-fire Q A (_∷ᶠ_ {at = at} {a = a} ¬m f) m (⟹-ev st rest) =
  ⟹-ev (Θ-pass-step {at = at} {a = a} st ¬m) (Θ-run-fire Q A f m rest)

-------------------------------------------------------------------------------------
-- Layer 4 : OFFERS / STABILITY of `P ⟦ A ▷ ·` ARE the body's.  `Θ-vis` offers an event
-- exactly when the body does (the throw only redirects the TARGET), and throw's τ-space
-- is the body's — so refusals transfer in BOTH directions between body and composite.
-- (Contrast `ThrowFD`'s `Θ-refuses-handler-indep`, which moves between two HANDLERS.)
-------------------------------------------------------------------------------------

-- force-shape trichotomy as propositional equalities (local copy of `ThrowFD`'s
-- `Θ-force-tri`; a `with PTree.force P` would reduce the `isStable` hypotheses' types)
Θ-tri : (P : PTree E (ExtI E) R)
      → (Σ[ r ∈ R ] (PTree.force P ≡ ret r))
      ⊎ (Σ[ P₁ ∈ PTree E (ExtI E) R ] (PTree.force P ≡ sil P₁))
      ⊎ (Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
         Σ[ τc ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
           (PTree.force P ≡ react v τc))
Θ-tri P with PTree.force P
... | ret r      = inj₁ (r , refl)
... | sil P₁     = inj₂ (inj₁ (P₁ , refl))
... | react v τc = inj₂ (inj₂ (v , τc , refl))

-- the throw's τ-branch is `nothing` wherever the body's is
Θ-τ-nothing-from : (nP : NodeKind E (ExtI E) R) (A : EventSet) (Q : PTree E (ExtI E) R)
                   {i : AnyTypes (ExtI E)} {a : proj₁ i}
                 → viewT nP i a ≡ nothing → Θ-τ A nP Q i a ≡ nothing
Θ-τ-nothing-from nP A Q {i = i} {a = a} eq with viewT nP i a
... | nothing = refl
... | just _  = case eq of λ ()

-- a stable composite has a stable body (throw's τ-space IS the body's, so any body τ
-- would show up as a composite τ)
Θ-isStable→ : (P Q : PTree E (ExtI E) R) (A : EventSet)
            → isStable (P ⟦ A ▷ Q) → isStable P
Θ-isStable→ P Q A st with Θ-tri P
... | inj₁ (r , eqP) =
      ⊥-elim (stable-not-ret {t = P ⟦ A ▷ Q} st (force-Θ-ret {P = P} {Q = Q} {A = A} eqP))
... | inj₂ (inj₁ (P₁ , eqP)) =
      ⊥-elim (stable-no-τ {t = P ⟦ A ▷ Q} st (Θ-τ-lift-P {Q = Q} {A = A} (sSil eqP)))
... | inj₂ (inj₂ (v , τc , eqP)) = mk-stable {t = P} eqP go
  where
  go : ∀ i a → τc i a ≡ nothing
  go i a with τc i a in teq
  ... | nothing = refl
  ... | just P′ =
        ⊥-elim (stable-no-τ {t = P ⟦ A ▷ Q} st (Θ-τ-lift-P {Q = Q} {A = A} (sTau eqP teq)))

-- a stable body gives a stable composite (same reason, read backwards)
Θ-isStable← : (P Q : PTree E (ExtI E) R) (A : EventSet)
            → isStable P → isStable (P ⟦ A ▷ Q)
Θ-isStable← P Q A stP with Θ-tri P
... | inj₁ (r , eqP)         = ⊥-elim (stable-not-ret {t = P} stP eqP)
... | inj₂ (inj₁ (P₁ , eqP)) = ⊥-elim (stable-not-sil {t = P} stP eqP)
... | inj₂ (inj₂ (v , τc , eqP)) =
      mk-stable {t = P ⟦ A ▷ Q} (force-Θ-react {P = P} {Q = Q} {A = A} eqP)
        (λ i a → Θ-τ-nothing-from (react v τc) A Q {i = i} {a = a}
                   (stable-react-τc {t = P} stP eqP i a))

-- an offer of the composite is an offer of the body at the SAME event (fire, pass and
-- √ all read a body step off `Θ-ev-elim`)
Θ-Offers→ : (P Q : PTree E (ExtI E) R) (A : EventSet) {e : Event√ R}
          → Offers (P ⟦ A ▷ Q) e → Offers P e
Θ-Offers→ P Q A (M , step) with Θ-ev-elim P Q step
... | Θthrow {P₁ = P′} sP m  = P′ , sP
... | Θpass  {P₁ = P′} sP ¬m = P′ , sP
... | Θdone eqPr             = deadlock , sRet eqPr

-- an offer of the body is an offer of the composite at the SAME event (the throw only
-- redirects the target: `A`-membership decides fire vs pass)
Θ-Offers← : (P Q : PTree E (ExtI E) R) (A : EventSet) {e : Event√ R}
          → Offers P e → Offers (P ⟦ A ▷ Q) e
Θ-Offers← P Q A (M , sRet eqf) =
  deadlock , sRet (force-Θ-ret {P = P} {Q = Q} {A = A} eqf)
Θ-Offers← P Q A (M , sVis {at = at} {a = a} eqf breq) with A .dec at a
... | yes m = Q , Θ-throw-step {at = at} {a = a} (sVis eqf breq) m
... | no ¬m = (M ⟦ A ▷ Q) , Θ-pass-step {at = at} {a = a} (sVis eqf breq) ¬m

-- a composite refusal IS a body refusal
Θ-Refuses→ : (P Q : PTree E (ExtI E) R) (A : EventSet) {X : Event√ R → Set ℓr}
           → Refuses (P ⟦ A ▷ Q) X → Refuses P X
Θ-Refuses→ P Q A (st , noff) =
  Θ-isStable→ P Q A st , λ e xe off → noff e xe (Θ-Offers← P Q A off)

-- … and conversely
Θ-Refuses← : (P Q : PTree E (ExtI E) R) (A : EventSet) {X : Event√ R → Set ℓr}
           → Refuses P X → Refuses (P ⟦ A ▷ Q) X
Θ-Refuses← P Q A (st , noff) =
  Θ-isStable← P Q A st , λ e xe off → noff e xe (Θ-Offers→ P Q A off)

-------------------------------------------------------------------------------------
-- Layer 5 : the FIRE transfer.  Push the body's run-up-to-the-fire through the body
-- hypothesis: either the refined body can still reach and fire the same `A`-event (so
-- the refined composite reaches the handler on the same trace), or it diverges strictly
-- inside the `A`-free prefix (so the refined composite diverges there).
-------------------------------------------------------------------------------------

-- transfer a fire: `FD→trace⊥` on the body run extended by the firing event; a returned
-- divergence is split by `snoc-split` — inside the `A`-free prefix it lifts, and at the
-- firing event itself it still supplies the trace needed to re-fire
Θ-fire-transfer : (A : EventSet) (P₁ P₂ Q₁ : PTree E (ExtI E) R)
                → P₁ ⊑F⊥ P₂ → P₁ ⊑D P₂
                → {u : List (Event√ R)} {at : AnyTypes E} {a : proj₁ at}
                  {P₂* P₂′ : PTree E (ExtI E) R}
                → ΘFree A u → P₂ ⟹⟨ u ⟩ P₂*
                → P₂* ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₂′
                → A .mem at a
                → ((P₁ ⟦ A ▷ Q₁) ⟹⟨ u ++ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ [] ⟩ Q₁)
                  ⊎ divergences (P₁ ⟦ A ▷ Q₁) u
Θ-fire-transfer A P₁ P₂ Q₁ fP dP {u = u} {at = at} {a = a} f rP st m
  with FD→trace⊥ fP dP (⟹-trans rP (⟹-ev st ⟹-refl))
... | inj₁ (P₁′ , run₁) = inj₁ (Θ-run-fire Q₁ A f m run₁)
... | inj₂ dv
      with snoc-split (dv .prefix) {dv .suffix} {u}
                      {evl (evLabel (proj₁ at) (proj₂ at) a)} (dv .split)
-- the divergence prefix stops inside the `A`-free part: lift it into the composite
...   | inj₁ (q′ , _ , seq) = inj₂ (record
          { prefix  = dv .prefix
          ; suffix  = q′
          ; split   = seq
          ; witness = (dv .witness) ⟦ A ▷ Q₁
          ; reach   = Θ-run-lift Q₁ A
                        (ΘFree-prefix (dv .prefix) (subst (ΘFree A) seq f)) (dv .reach)
          ; divwit  = Θ-Diverges-L (dv .divwit)
          })
-- the divergence prefix IS the fired trace: its reach re-fires the throw
...   | inj₂ (_ , peq) =
        inj₁ (Θ-run-fire Q₁ A f m
               (subst (λ z → P₁ ⟹⟨ z ⟩ (dv .witness)) peq (dv .reach)))

-------------------------------------------------------------------------------------
-- Layer 6 : the ⊑D half.
-------------------------------------------------------------------------------------

-- worker: decompose the target composite's divergence-reach and transfer each shape
Θ-mono-div-reach : (A : EventSet) (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R)
                 → P₁ ⊑F⊥ P₂ → P₁ ⊑D P₂ → Q₁ ⊑D Q₂
                 → {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
                 → (P₂ ⟦ A ▷ Q₂) ⟹⟨ pre ⟩ W → Diverges W
                 → divergences (P₁ ⟦ A ▷ Q₁) pre
Θ-mono-div-reach A P₁ P₂ Q₁ Q₂ fP dP dQ reach divW
  with Θ-reach-split P₂ Q₂ A reach
-- never fired: the composite divergence is the BODY's (`Θ-Diverges→`), transferred by
-- the body's `⊑D` and lifted back through the throw
... | θNo f rP = Θ-div-lift Q₁ A f (dP (mk-full-div rP (Θ-Diverges→ divW)))
-- fired: the divergence is the HANDLER's, transferred by the handler's `⊑D` and
-- prepended to the refined composite's re-fired run (or the body diverges first)
... | θFire {u = u} {at = at} {a = a} {v = v} f rP st m rQ =
      case Θ-fire-transfer A P₁ P₂ Q₁ fP dP f rP st m of λ where
        (inj₁ fire) →
          subst (divergences (P₁ ⟦ A ▷ Q₁))
                (++-assoc u (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ []) v)
                (div-prepend-run fire (dQ (mk-full-div rQ divW)))
        (inj₂ dv) → div-extension-closed dv
-- the body terminated: the run is stranded at `deadlock`, which cannot diverge
... | θDone f rP eqret rd =
      ⊥-elim (deadlock-converges (subst Diverges (proj₂ (deadlock-run-inv rd)) divW))

-- HEADLINE (⊑D half): throw is ⊑D-monotone in body and handler
Θ-mono-⊑D : (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
          → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ ⟦ A ▷ Q₁) ⊑D (P₂ ⟦ A ▷ Q₂)
Θ-mono-⊑D A {P₁} {P₂} {Q₁} {Q₂} (fP , dP) (fQ , dQ) d =
  subst (divergences (P₁ ⟦ A ▷ Q₁))
        (sym (d .split))
        (div-extension-closed
          (Θ-mono-div-reach A P₁ P₂ Q₁ Q₂ fP dP dQ (d .reach) (d .divwit)))

-------------------------------------------------------------------------------------
-- Layer 7 : the ⊑F⊥ half.
-------------------------------------------------------------------------------------

-- worker: decompose the target composite's failure-reach and transfer each shape
Θ-mono-fail-reach : (A : EventSet) (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R)
                  → P₁ ⊑F⊥ P₂ → P₁ ⊑D P₂ → Q₁ ⊑F⊥ Q₂
                  → {s : List (Event√ R)} {X : Event√ R → Set ℓr}
                    {W : PTree E (ExtI E) R}
                  → (P₂ ⟦ A ▷ Q₂) ⟹⟨ s ⟩ W → Refuses W X
                  → failures⊥ (P₁ ⟦ A ▷ Q₁) s X
Θ-mono-fail-reach A P₁ P₂ Q₁ Q₂ fP dP fQ {X = X} reach ref
  with Θ-reach-split P₂ Q₂ A reach
-- never fired: the composite refusal IS the body's; transfer through the body's `⊑F⊥`
-- and rebuild (or lift the returned divergence)
... | θNo {P* = P₂*} f rP =
      case fP {B = X} (inj₁ (P₂* , rP , Θ-Refuses→ P₂* Q₂ A ref)) of λ where
        (inj₁ (P₁* , rP₁ , ref₁)) →
          inj₁ ((P₁* ⟦ A ▷ Q₁) , Θ-run-lift Q₁ A f rP₁ , Θ-Refuses← P₁* Q₁ A ref₁)
        (inj₂ dv) → inj₂ (Θ-div-lift Q₁ A f dv)
-- fired: the refusal is the HANDLER's; transfer through the handler's `⊑F⊥` and prepend
-- the refined composite's re-fired run (or the body diverges first)
... | θFire {u = u} {at = at} {a = a} {v = v} f rP st m rQ =
      case Θ-fire-transfer A P₁ P₂ Q₁ fP dP f rP st m of λ where
        (inj₁ fire) → case fQ {B = X} (inj₁ (_ , rQ , ref)) of λ where
          (inj₁ fQ₁) →
            inj₁ (subst (λ z → failures (P₁ ⟦ A ▷ Q₁) z X)
                        (++-assoc u (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ []) v)
                        (fail-prepend-run fire fQ₁))
          (inj₂ dQ₁) →
            inj₂ (subst (divergences (P₁ ⟦ A ▷ Q₁))
                        (++-assoc u (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ []) v)
                        (div-prepend-run fire dQ₁))
        (inj₂ dv) → inj₂ (div-extension-closed dv)
-- the body terminated: √-extend the body run, push it through the body's `⊑F⊥`, and
-- re-tick the refined composite into `deadlock` (which refuses everything)
... | θDone {u = u} {r = r} f rP eqret rd with deadlock-run-inv rd
...   | refl , refl =
        case fP {B = X} (inj₁ (term→√failure rP eqret)) of λ where
          (inj₁ (T , run√ , _)) → case √-run-split-gen u run√ of λ where
            (P₁ᵣ , run , feq) →
              inj₁ (deadlock
                   , ⟹-trans (Θ-run-lift Q₁ A f run)
                             (⟹-ev (sRet (force-Θ-ret {P = P₁ᵣ} {Q = Q₁} {A = A} feq))
                                   ⟹-refl)
                   , deadlock-refuses)
          (inj₂ dv) →
            inj₂ (div-extension-closed (Θ-div-lift Q₁ A f (div-√-truncate dv)))

-- HEADLINE (⊑F⊥ half): throw is ⊑F⊥-monotone in body and handler
Θ-mono-⊑F⊥ : (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
           → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ ⟦ A ▷ Q₁) ⊑F⊥ (P₂ ⟦ A ▷ Q₂)
Θ-mono-⊑F⊥ A {P₁} {P₂} {Q₁} {Q₂} hP hQ (inj₂ d) = inj₂ (Θ-mono-⊑D A hP hQ d)
Θ-mono-⊑F⊥ A {P₁} {P₂} {Q₁} {Q₂} (fP , dP) (fQ , dQ) (inj₁ (W , reach , ref)) =
  Θ-mono-fail-reach A P₁ P₂ Q₁ Q₂ fP dP fQ reach ref

-------------------------------------------------------------------------------------
-- Layer 8 : the headline.
-------------------------------------------------------------------------------------

-- HEADLINE: throw is a ⊑FD-PRECONGRUENCE — `⊑FD` facts in, `⊑FD` fact out, in BOTH
-- operands, unconditionally
Θ-mono-⊑FD : (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
           → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ ⟦ A ▷ Q₁) ⊑FD (P₂ ⟦ A ▷ Q₂)
Θ-mono-⊑FD A hP hQ = Θ-mono-⊑F⊥ A hP hQ , Θ-mono-⊑D A hP hQ

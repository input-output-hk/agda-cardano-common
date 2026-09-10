{-# OPTIONS --guardedness #-}

-- Alphabet-confinement invariant `OffersOnly α P` for the replicated-interleaving
-- ≈DR congruence (`NetworkLink ≈FD CopySpec`).
--
-- `OffersOnly α P` says: every visible (non-√) event that P can EVER offer (now or
-- after any run) lies within the value-level alphabet `α`.  It is the generic tool
-- that discharges the `Sep` side-condition of `cong-⦀`/`cong-Par⊤` (in
-- `CSP.Laws.Bisim.DRCongruence`): if the two operands confine to alphabets that
-- clash on nothing outside the sync set, they can never both-offer a non-sync event,
-- so `Sep` holds by corecursion (`sep-from-OffersOnly`).
--
-- This module is the GENERIC layer: the `OffersOnly` core, its `Sep` discharge, and
-- intro rules for the leaf-node builders (`pchoice`/`Prefix`/`Output`/`Ret`).
-- Tasks 3–5 append the closure lemmas (`>>=`, `iter`, `Par`, `hide`, folds) and the
-- congruences to THIS file, so the section structure is kept clean.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
-- `NonRet` (TraceLawsExtChoice) lands in the NON-polymorphic `Data.Unit.⊤`
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.Bisim.DRCongruenceRep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import CSP.Laws.Bisim.DRCongruence E-≟ using (Sep; Sep△; cong-⦀)
-- the interrupt `_△_` step-inversion layer + the `NonRet` node predicate, for the
-- `OffersOnly-△` / `NoRet` / `sep△-from-OffersOnly` section at the end of this module
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using ( △τR; △τP; △τQ; △τQret; △τ⊓P; △τ⊓Q; △-τ-elim
        ; △evR; △evP; △evQ; △evPQ; △-ev-elim )
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev; wτ; WSimF )
open import Semantics.DRBisim {E = E} {I = ExtI E} using (_≈DR_; drbisim-refl; DRbisim)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (deadlock-no-ev)
open import CSP.Laws.Traces.PrefixInversion E-≟ using (Prefix-cont-fires)
-- bind / iterate force- and branch-inversion lemmas reused from the trace / bisim layers
open import CSP.Laws.Traces.TraceLawsBind E-≟
  using (fBind-ret; fBind-sil; fBind-react; bindV-elim; bindT-elim)
open import CSP.Laws.Bisim.IterCong E-≟
  using (fIter-r1; fIter-r2; fIter-sil; fIter-react; iterV-elim; iterT-elim)
-- parallel / hide single-step ELIM lemmas reused for the closure proofs below
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (Par-τ-elim; Par-ev-elim; ParτR; τL; τR
        ; ParevR; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ-elim; Hide-ev-elim; HideτR; hτP; hτH; HideevR; heV; he√)
open EventSet

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- Value-level alphabets
-------------------------------------------------------------------------------------

-- A value-level alphabet: a predicate on an event index `at` together with its value.
Alpha : Set (lsuc ℓ ⊔ ℓe)
Alpha = (at : AnyTypes E) → proj₁ at → Set

-- Two alphabets are disjoint when no (index,value) pair belongs to both.
Disj : Alpha → Alpha → Set (lsuc ℓ ⊔ ℓe)
Disj α β = ∀ at a → α at a → β at a → ⊥

private
  variable
    α β : Alpha

-------------------------------------------------------------------------------------
-- The `OffersOnly` core invariant
-------------------------------------------------------------------------------------

-- `OffersOnly α P`: every visible event P can offer (immediately, `now`) is in `α`,
-- and this is preserved under ANY step of P (`step`, over all labels incl. τ and √).
record OffersOnly {ℓr} {R : Set ℓr} (α : Alpha) (P : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    now  : ∀ {X} {e : E X} {a : X} {P′ : PTree E (ExtI E) R}
         → P ─[ ev (evl (evLabel X e a)) ]─► P′
         → α (X , e) a
    step : ∀ {l} {P′ : PTree E (ExtI E) R}
         → P ─[ l ]─► P′ → OffersOnly α P′

-- weaken the confining alphabet pointwise
OffersOnly-mono : ∀ {P : PTree E (ExtI E) R}
                → (∀ at a → α at a → β at a)
                → OffersOnly α P → OffersOnly β P
OffersOnly-mono α⊆β oo .OffersOnly.now  st = α⊆β _ _ (OffersOnly.now  oo st)
OffersOnly-mono α⊆β oo .OffersOnly.step st = OffersOnly-mono α⊆β (OffersOnly.step oo st)

-------------------------------------------------------------------------------------
-- Transport of `OffersOnly` along τ-runs and BACKWARD across ≈DR
-- (hoisted from `…/Liveness/NodeDOffers`; generic in `α`, `P`, `Q`, `R`).
-- Any ≈DR-established bisim lets its abstract-side alphabet confinement transfer
-- to the concrete side for free, so per-node impl-side `OffersOnly`s need not be
-- re-derived from source.
-------------------------------------------------------------------------------------

-- walk an `OffersOnly` witness along a τ*-run
OO-τ* : ∀ {α} {P P′ : PTree E (ExtI E) R}
      → P ─[τ*]─► P′ → OffersOnly α P → OffersOnly α P′
OO-τ* τ*-refl        oo = oo
OO-τ* (τ*-step st rs) oo = OO-τ* rs (OffersOnly.step oo st)

-- ≈DR transfers `OffersOnly` BACKWARD: the offers of `P` are (weakly) matched by
-- `Q`, so any alphabet confining `Q` confines `P`.
≈DR-OO : ∀ {α} {P Q : PTree E (ExtI E) R}
       → P ≈DR Q → OffersOnly α Q → OffersOnly α P
≈DR-OO pq ooQ .OffersOnly.now Pstep
  with WSimF.on-ev (DRbisim.fwd pq) Pstep
... | _ , wev q→q₁ q₁ev _ , _ = OffersOnly.now (OO-τ* q→q₁ ooQ) q₁ev
≈DR-OO pq ooQ .OffersOnly.step {l = τ} Pstep
  with WSimF.on-tau (DRbisim.fwd pq) Pstep
... | _ , wτ q→q′ , p′q′ = ≈DR-OO p′q′ (OO-τ* q→q′ ooQ)
≈DR-OO pq ooQ .OffersOnly.step {l = ev _} Pstep
  with WSimF.on-ev (DRbisim.fwd pq) Pstep
... | _ , wev q→q₁ q₁ev q₂→q′ , p′q′ =
      ≈DR-OO p′q′ (OO-τ* q₂→q′ (OffersOnly.step (OO-τ* q→q₁ ooQ) q₁ev))

-------------------------------------------------------------------------------------
-- Base cases: deadlock and Ret (hence Skip)
-------------------------------------------------------------------------------------

-- deadlock offers nothing and cannot step, so it confines to every alphabet.
OffersOnly-deadlock : OffersOnly α (deadlock {E = E} {I = ExtI E} {R = R})
OffersOnly-deadlock .OffersOnly.now  st = ⊥-elim (deadlock-no-ev st)
OffersOnly-deadlock .OffersOnly.step (sRet ())
OffersOnly-deadlock .OffersOnly.step (sSil ())
OffersOnly-deadlock .OffersOnly.step (sVis refl ())
OffersOnly-deadlock .OffersOnly.step (sTau refl ())

-- `Ret r` offers only its terminal √ (never a visible event) and slides to deadlock.
OffersOnly-Ret : ∀ {r : R} → OffersOnly α (Ret r)
OffersOnly-Ret .OffersOnly.now  (sVis () _)
OffersOnly-Ret .OffersOnly.step (sRet _)   = OffersOnly-deadlock
OffersOnly-Ret .OffersOnly.step (sSil ())
OffersOnly-Ret .OffersOnly.step (sVis () _)
OffersOnly-Ret .OffersOnly.step (sTau () _)

-- Skip = Ret tt is confined to every alphabet.
OffersOnly-Skip : OffersOnly α (Skip {ℓr})
OffersOnly-Skip = OffersOnly-Ret

-- An alphabet holding of EVERYTHING confines every process: the invariant is vacuous.
-- Used to read a renamed process's confinement straight off the renaming's IMAGE
-- (`CSP.Laws.Bisim.RenameOffers.OffersOnly-renameMap-image`) without any source-side work.
OffersOnly-full : ∀ {P : PTree E (ExtI E) R} → (∀ at a → α at a) → OffersOnly α P
OffersOnly-full h .OffersOnly.now  _ = h _ _
OffersOnly-full h .OffersOnly.step _ = OffersOnly-full h

-------------------------------------------------------------------------------------
-- The `Sep` discharge — the heart of the module
-------------------------------------------------------------------------------------

-- two alphabet-confined processes whose non-sync alphabets clash on nothing
-- can never both-offer a non-sync event, now or ever: `Sep` by corecursion.
sep-from-OffersOnly : (A : EventSet) {P Q : PTree E (ExtI E) (⊤ {ℓr})}
                    → (∀ {at a} → ¬ A .mem at a → α at a → β at a → ⊥)
                    → OffersOnly α P → OffersOnly β Q → Sep A P Q
sep-from-OffersOnly A disj ooP ooQ .Sep.now ¬cs Pst Qst =
  disj ¬cs (OffersOnly.now ooP Pst) (OffersOnly.now ooQ Qst)
sep-from-OffersOnly A disj ooP ooQ .Sep.stepL Pst =
  sep-from-OffersOnly A disj (OffersOnly.step ooP Pst) ooQ
sep-from-OffersOnly A disj ooP ooQ .Sep.stepR Qst =
  sep-from-OffersOnly A disj ooP (OffersOnly.step ooQ Qst)

-------------------------------------------------------------------------------------
-- Leaf-node intro rules: pchoice / Prefix / Output
-------------------------------------------------------------------------------------

-- A menu `v` is `α`-confined when every offered branch fires within `α` and its
-- continuation is itself `α`-confined.
MenuConf : ∀ {ℓr} {R : Set ℓr}
         → Alpha → ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
MenuConf α v = ∀ at a {t′} → v at a ≡ just t′ → α at a × OffersOnly α t′

-- a stable visible menu `pchoice v` is `α`-confined whenever `v` is `MenuConf`.
OffersOnly-pchoice : ∀ {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   → MenuConf α v → OffersOnly α (pchoice v)
OffersOnly-pchoice mc .OffersOnly.now  (sVis refl br) = proj₁ (mc _ _ br)
OffersOnly-pchoice mc .OffersOnly.step (sRet ())
OffersOnly-pchoice mc .OffersOnly.step (sSil ())
OffersOnly-pchoice mc .OffersOnly.step (sVis refl br) = proj₂ (mc _ _ br)
OffersOnly-pchoice mc .OffersOnly.step (sTau refl ())

-- prefix `e ⟶ P`: confined when every value fires within `α` and every continuation
-- is confined (the menu fires only on the prefix's own channel, via Prefix-cont-fires).
OffersOnly-Prefix : ∀ {A : Set ℓ} {e : E A} {P : A → PTree E (ExtI E) R}
                  → (∀ a → α (A , e) a)
                  → (∀ a → OffersOnly α (P a))
                  → OffersOnly α (Prefix e P)
OffersOnly-Prefix {A = A} {e = e} {P = P} hα hP .OffersOnly.now (sVis {a = a} refl br)
  with Prefix-cont-fires br
... | refl , _ , _ = hα a
OffersOnly-Prefix hα hP .OffersOnly.step (sRet ())
OffersOnly-Prefix hα hP .OffersOnly.step (sSil ())
OffersOnly-Prefix hα hP .OffersOnly.step (sVis refl br)
  with Prefix-cont-fires br
... | refl , w , refl = hP w
OffersOnly-Prefix hα hP .OffersOnly.step (sTau refl ())

-- parameterless prefix `e ⟶₀ P` = `Prefix e (λ _ → P)`.
OffersOnly-Prefix₀ : ∀ {A : Set ℓ} {e : E A} {P : PTree E (ExtI E) R}
                   → (∀ a → α (A , e) a)
                   → OffersOnly α P
                   → OffersOnly α (Prefix₀ e P)
OffersOnly-Prefix₀ hα oP = OffersOnly-Prefix hα (λ _ → oP)

-- output `e ! v ⟶ P`: confined when the single offered event `(A,e) v` is in `α`
-- and the continuation is confined (the menu fires only on channel `e`, value `v`).
OffersOnly-Output : ∀ {A : Set ℓ} ⦃ _ : DecEq A ⦄
                      {e : E A} {v : A} {Pk : PTree E (ExtI E) R}
                  → α (A , e) v
                  → OffersOnly α Pk
                  → OffersOnly α (Output e v Pk)
OffersOnly-Output {A = A} {e = e} {v = v} hα oP .OffersOnly.now (sVis {at = at} {a = a} refl br)
  with E-≟ (A , e) at
... | no  _    = ⊥-elim (case br of λ ())
... | yes refl with a ≟ v
...   | no  _    = ⊥-elim (case br of λ ())
...   | yes refl = hα
OffersOnly-Output hα oP .OffersOnly.step (sRet ())
OffersOnly-Output hα oP .OffersOnly.step (sSil ())
OffersOnly-Output {A = A} {e = e} {v = v} hα oP .OffersOnly.step (sVis {at = at} {a = a} refl br)
  with E-≟ (A , e) at
... | no  _    = ⊥-elim (case br of λ ())
... | yes refl with a ≟ v
...   | no  _    = ⊥-elim (case br of λ ())
...   | yes refl = subst (OffersOnly _) (just-injective br) oP
OffersOnly-Output hα oP .OffersOnly.step (sTau refl ())

-------------------------------------------------------------------------------------
-- Closure under sequential composition `_>>=_`
-------------------------------------------------------------------------------------

private
  variable
    ℓs : Level
    S  : Set ℓs

-- retarget a single step along a force-equation (force-equal trees have equal steps).
retarget : ∀ {ℓr'} {R' : Set ℓr'} {a b u : PTree E (ExtI E) R'} {l : Label R'}
         → PTree.force a ≡ PTree.force b → b ─[ l ]─► u → a ─[ l ]─► u
retarget eq (sRet eqf)    = sRet (trans eq eqf)
retarget eq (sSil eqf)    = sSil (trans eq eqf)
retarget eq (sVis eqf br) = sVis (trans eq eqf) br
retarget eq (sTau eqf br) = sTau (trans eq eqf) br

-- `P >>= k` is α-confined when P is and every continuation `k r` is.  On the `ret r`
-- boundary `P >>= k` IS `k r` (force-equal), so steps delegate to `k r` non-corecursively;
-- on `sil`/`react` the residual is again a bind, discharged by corecursion.
OffersOnly->>= : ∀ {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
               → OffersOnly α P → (∀ r → OffersOnly α (k r)) → OffersOnly α (P >>= k)
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.now (sVis {at = at} {a = a} eqf br)
  with PTree.force P in eqP
-- eqf was matched in the head, so the `with` above reduces `force (P >>= k)` inside it.
... | ret r      = OffersOnly.now (ook r) (sVis eqf br)
... | sil c      = ⊥-elim (case eqf of λ ())
... | react v τc with bindV-elim k (react v τc)
                        (subst (λ g → g at a ≡ just _)
                               (sym (proj₁ (react-injective eqf)))
                               br)
...   | t , vv , _ = OffersOnly.now ooP (sVis eqP vv)
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.step st with PTree.force P in eqP
... | ret r = OffersOnly.step (ook r) (retarget (sym (fBind-ret k P eqP)) st)
... | sil c with st
...   | sSil eqf with sil-injective (trans (sym (fBind-sil k P eqP)) eqf)
...     | refl   = OffersOnly->>= (OffersOnly.step ooP (sSil eqP)) ook
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.step st | sil c | sRet eqf =
  ⊥-elim (case trans (sym (fBind-sil k P eqP)) eqf of λ ())
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.step st | sil c | sVis eqf _ =
  ⊥-elim (case trans (sym (fBind-sil k P eqP)) eqf of λ ())
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.step st | sil c | sTau eqf _ =
  ⊥-elim (case trans (sym (fBind-sil k P eqP)) eqf of λ ())
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.step st | react v τc with st
...   | sVis {at = at} {a = a} eqf br with bindV-elim k (react v τc)
                                            (subst (λ g → g at a ≡ just _)
                                                   (sym (proj₁ (react-injective (trans (sym (fBind-react k P eqP)) eqf))))
                                                   br)
...     | t , vv , refl = OffersOnly->>= (OffersOnly.step ooP (sVis eqP vv)) ook
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.step st | react v τc | sTau {i = i} {a = a} eqf br
  with bindT-elim k (react v τc)
         (subst (λ g → g i a ≡ just _)
                (sym (proj₂ (react-injective (trans (sym (fBind-react k P eqP)) eqf))))
                br)
...   | t , vv , refl = OffersOnly->>= (OffersOnly.step ooP (sTau eqP vv)) ook
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.step st | react v τc | sRet eqf =
  ⊥-elim (case trans (sym (fBind-react k P eqP)) eqf of λ ())
OffersOnly->>= {P = P} {k = k} ooP ook .OffersOnly.step st | react v τc | sSil eqf =
  ⊥-elim (case trans (sym (fBind-react k P eqP)) eqf of λ ())

-------------------------------------------------------------------------------------
-- Closure under iteration `iter-bind` / `iter`
-------------------------------------------------------------------------------------

-- `iter-bind t k` is α-confined when the body `t` and every re-entry `k a` are.  The
-- four `force t` clauses mirror `iter-bind`'s own: `ret (inj₁ a′)` loops (guarded by a
-- τ into `iter k a′`), `ret (inj₂ r)` finishes (a √ into deadlock), `sil`/`react` recurse.
OffersOnly-iter-bind : ∀ {A : Set ℓ} {t : PTree E (ExtI E) (A ⊎ R)}
                         {k : A → PTree E (ExtI E) (A ⊎ R)}
                     → OffersOnly α t → (∀ a → OffersOnly α (k a))
                     → OffersOnly α (iter-bind t k)
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.now (sVis {at = at} {a = a} eqf br)
  with PTree.force t in eqt
-- eqf was matched in the head, so the `with` above reduces `force (iter-bind t k)` inside it.
... | ret (inj₁ a′) = ⊥-elim (case eqf of λ ())
... | ret (inj₂ r)  = ⊥-elim (case eqf of λ ())
... | sil c         = ⊥-elim (case eqf of λ ())
... | react v τc with iterV-elim k (react v τc)
                        (subst (λ g → g at a ≡ just _)
                               (sym (proj₁ (react-injective eqf)))
                               br)
...   | t′ , vv , _ = OffersOnly.now oot (sVis eqt vv)
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st with PTree.force t in eqt
... | ret (inj₁ a′) with st
...   | sSil eqf with sil-injective (trans (sym (fIter-r1 k t eqt)) eqf)
...     | refl   = OffersOnly-iter-bind (ook a′) ook
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | ret (inj₁ a′) | sRet eqf =
  ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | ret (inj₁ a′) | sVis eqf _ =
  ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | ret (inj₁ a′) | sTau eqf _ =
  ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | ret (inj₂ r) with st
...   | sRet eqf   = OffersOnly-deadlock
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | ret (inj₂ r) | sSil eqf =
  ⊥-elim (case trans (sym (fIter-r2 k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | ret (inj₂ r) | sVis eqf _ =
  ⊥-elim (case trans (sym (fIter-r2 k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | ret (inj₂ r) | sTau eqf _ =
  ⊥-elim (case trans (sym (fIter-r2 k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | sil c with st
...   | sSil eqf with sil-injective (trans (sym (fIter-sil k t eqt)) eqf)
...     | refl   = OffersOnly-iter-bind (OffersOnly.step oot (sSil eqt)) ook
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | sil c | sRet eqf =
  ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | sil c | sVis eqf _ =
  ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | sil c | sTau eqf _ =
  ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | react v τc with st
...   | sVis {at = at} {a = a} eqf br with iterV-elim k (react v τc)
                                            (subst (λ g → g at a ≡ just _)
                                                   (sym (proj₁ (react-injective (trans (sym (fIter-react k t eqt)) eqf))))
                                                   br)
...     | t′ , vv , refl = OffersOnly-iter-bind (OffersOnly.step oot (sVis eqt vv)) ook
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | react v τc | sTau {i = i} {a = a} eqf br
  with iterT-elim k (react v τc)
         (subst (λ g → g i a ≡ just _)
                (sym (proj₂ (react-injective (trans (sym (fIter-react k t eqt)) eqf))))
                br)
...   | t′ , vv , refl = OffersOnly-iter-bind (OffersOnly.step oot (sTau eqt vv)) ook
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | react v τc | sRet eqf =
  ⊥-elim (case trans (sym (fIter-react k t eqt)) eqf of λ ())
OffersOnly-iter-bind {t = t} {k = k} oot ook .OffersOnly.step st | react v τc | sSil eqf =
  ⊥-elim (case trans (sym (fIter-react k t eqt)) eqf of λ ())

-- `iter k a` = `iter-bind (k a) k`, so confinement follows directly.
OffersOnly-iter : ∀ {A : Set ℓ} {k : A → PTree E (ExtI E) (A ⊎ R)} {a : A}
                → (∀ a → OffersOnly α (k a)) → OffersOnly α (iter k a)
OffersOnly-iter {a = a} ook = OffersOnly-iter-bind (ook a) ook

-------------------------------------------------------------------------------------
-- Closure under the forever loops `loop` / `loop0`
-------------------------------------------------------------------------------------

-- a stateful loop whose every body-state is α-confined is α-confined:
-- `loop body a = iter step a` with `step a = body a >>= λ a′ → Ret (inj₁ a′)`.
OffersOnly-loop : ∀ {A : Set ℓ} {body : A → PTree E (ExtI E) A} {a : A}
                → (∀ a → OffersOnly α (body a)) → OffersOnly {R = R} α (loop body a)
OffersOnly-loop oob = OffersOnly-iter (λ a → OffersOnly->>= (oob a) (λ _ → OffersOnly-Ret))

-- the non-stateful loop `loop0 body = loop (λ _ → body) tt`.
OffersOnly-loop0 : ∀ {body : PTree E (ExtI E) (⊤ {ℓ})}
                 → OffersOnly α body → OffersOnly {R = R} α (loop0 body)
OffersOnly-loop0 oob = OffersOnly-loop (λ _ → oob)

-------------------------------------------------------------------------------------
-- Closure under parallel composition `Par` (and its overlap node `par-brBoth`)
-------------------------------------------------------------------------------------

private
  variable
    ℓ₁ ℓ₂ : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂

-- forward declarations for the mutually-corecursive Par / overlap-node pair
-- `Par A merge P Q` is α-confined when both operands are (SAME alphabet α, no
-- disjointness needed: the both-offer overlap node is closed by `OffersOnly-brBoth`).
OffersOnly-Par : ∀ {R : Set ℓs} {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
                 (A : EventSet) (merge : Mg R₁ R₂ R)
               → OffersOnly α P → OffersOnly α Q → OffersOnly α (Par A merge P Q)
-- the inline both-offer overlap node `(P′∥Q) ⊓ (P∥Q′)` is α-confined when all four
-- constituent trees are: its visible menu is empty, its τ-branches land in `Par`s.
OffersOnly-brBoth : ∀ {R : Set ℓs} {A : EventSet} {merge : Mg R₁ R₂ R}
                      {P P′ : PTree E (ExtI E) R₁} {Q Q′ : PTree E (ExtI E) R₂}
                  → OffersOnly α P → OffersOnly α Q → OffersOnly α P′ → OffersOnly α Q′
                  → OffersOnly α (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P′ Q′)))

-- `Par` : a visible offer is one operand's offer (or a both-offer, still that operand's
-- own visible event); `now` reflects it back into that operand's `now`.  Steps invert
-- via `Par-τ-elim` / `Par-ev-elim`: τ / solo / sync corecurse on the `Par` residual,
-- both-offer produces the overlap node, joint √ lands in deadlock.
OffersOnly-Par {P = P} {Q = Q} A merge ooP ooQ .OffersOnly.now st with Par-ev-elim A merge P Q st
... | evSync _ Pst _  = OffersOnly.now ooP Pst
... | evL    _ Pst    = OffersOnly.now ooP Pst
... | evR    _ Qst    = OffersOnly.now ooQ Qst
... | evBoth _ Pst _  = OffersOnly.now ooP Pst
OffersOnly-Par {P = P} {Q = Q} A merge ooP ooQ .OffersOnly.step {l = τ} st with Par-τ-elim A merge P Q st
... | τL P′ Pst refl  = OffersOnly-Par A merge (OffersOnly.step ooP Pst) ooQ
... | τR Q′ Qst refl  = OffersOnly-Par A merge ooP (OffersOnly.step ooQ Qst)
OffersOnly-Par {P = P} {Q = Q} A merge ooP ooQ .OffersOnly.step {l = ev e} st with Par-ev-elim A merge P Q st
... | evSync _ Pst Qst = OffersOnly-Par A merge (OffersOnly.step ooP Pst) (OffersOnly.step ooQ Qst)
... | evL    _ Pst     = OffersOnly-Par A merge (OffersOnly.step ooP Pst) ooQ
... | evR    _ Qst     = OffersOnly-Par A merge ooP (OffersOnly.step ooQ Qst)
... | evBoth _ Pst Qst = OffersOnly-brBoth ooP ooQ (OffersOnly.step ooP Pst) (OffersOnly.step ooQ Qst)
... | ev√    _ _       = OffersOnly-deadlock

-- overlap node: `now` is vacuous (visible map is literally `λ _ _ → nothing`); `step`
-- has τ-branches only, answering `just` at `fin`-indices `fzero`→`Par P′ Q`,
-- `fsuc fzero`→`Par P Q′`, `nothing` elsewhere — all corecursing into `OffersOnly-Par`.
OffersOnly-brBoth ooP ooQ ooP′ ooQ′ .OffersOnly.now (sVis refl ())
OffersOnly-brBoth ooP ooQ ooP′ ooQ′ .OffersOnly.step (sRet ())
OffersOnly-brBoth ooP ooQ ooP′ ooQ′ .OffersOnly.step (sSil ())
OffersOnly-brBoth ooP ooQ ooP′ ooQ′ .OffersOnly.step (sVis refl ())
OffersOnly-brBoth {A = A} {merge = merge} ooP ooQ ooP′ ooQ′ .OffersOnly.step
  (sTau {i = _ , fin} {a = lift fzero} refl refl) = OffersOnly-Par A merge ooP′ ooQ
OffersOnly-brBoth {A = A} {merge = merge} ooP ooQ ooP′ ooQ′ .OffersOnly.step
  (sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl) = OffersOnly-Par A merge ooP ooQ′
OffersOnly-brBoth ooP ooQ ooP′ ooQ′ .OffersOnly.step
  (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ())
OffersOnly-brBoth ooP ooQ ooP′ ooQ′ .OffersOnly.step (sTau {i = _ , base _} refl ())
OffersOnly-brBoth ooP ooQ ooP′ ooQ′ .OffersOnly.step (sTau {i = _ , pair _ _} refl ())

-------------------------------------------------------------------------------------
-- Closure under hiding `_∖_`
-------------------------------------------------------------------------------------

-- `P ∖ A` is α-confined when P is: a kept visible event is P's own (via `Hide-ev-elim`
-- `heV`), so `now`/`step` reflect into P; a τ is P's τ (`hτP`) or P's HIDDEN visible
-- step (`hτH`) — both feed `P .step` and corecurse on `P′ ∖ A`; a `√` lands in deadlock.
OffersOnly-∖ : ∀ {P : PTree E (ExtI E) R} (A : EventSet) → OffersOnly α P → OffersOnly α (P ∖ A)
OffersOnly-∖ {P = P} A ooP .OffersOnly.now st with Hide-ev-elim A P st
... | heV _ _ Pst = OffersOnly.now ooP Pst
OffersOnly-∖ {P = P} A ooP .OffersOnly.step {l = τ} st with Hide-τ-elim A P st
... | hτP P′ Pst   refl = OffersOnly-∖ A (OffersOnly.step ooP Pst)
... | hτH P′ _ Pst refl = OffersOnly-∖ A (OffersOnly.step ooP Pst)
OffersOnly-∖ {P = P} A ooP .OffersOnly.step {l = ev e} st with Hide-ev-elim A P st
... | heV _ _ Pst = OffersOnly-∖ A (OffersOnly.step ooP Pst)
... | he√ _       = OffersOnly-deadlock

-------------------------------------------------------------------------------------
-- Closure under the interleaving folds `_⦀_` / `⦀⋆` / `⦀Fin`
-------------------------------------------------------------------------------------

-- interleaving = parallel with empty sync set (a direct instance of `OffersOnly-Par`).
OffersOnly-⦀ : {P Q : PTree E (ExtI E) (⊤ {ℓr})}
             → OffersOnly α P → OffersOnly α Q → OffersOnly α (P ⦀ Q)
OffersOnly-⦀ ooP ooQ = OffersOnly-Par ∅ES (λ _ _ → tt) ooP ooQ

-- replicated interleaving over a list: `Skip` is the unit, otherwise fold with `_⦀_`.
OffersOnly-⦀⋆ : {Ps : List (PTree E (ExtI E) (⊤ {ℓr}))}
              → All (OffersOnly α) Ps → OffersOnly α (⦀⋆ Ps)
OffersOnly-⦀⋆ []            = OffersOnly-Skip
OffersOnly-⦀⋆ (ooP ∷ ooPs)  = OffersOnly-⦀ ooP (OffersOnly-⦀⋆ ooPs)

-- the pointwise-union of a finite family of alphabets.
unionAlpha : ∀ {n} → (Fin n → Alpha) → Alpha
unionAlpha αs at a = Σ[ i ∈ Fin _ ] αs i at a

-- replicated interleaving over a finite index with per-index alphabets: the composite
-- confines to the UNION of the leaf alphabets (each leaf injected via `OffersOnly-mono`).
OffersOnly-⦀Fin : ∀ {n} {αs : Fin n → Alpha} {f : Fin n → PTree E (ExtI E) (⊤ {ℓr})}
                → (∀ i → OffersOnly (αs i) (f i)) → OffersOnly (unionAlpha αs) (⦀Fin n f)
OffersOnly-⦀Fin {n = zero}  oo = OffersOnly-Skip
OffersOnly-⦀Fin {n = suc n} {αs = αs} oo =
  OffersOnly-⦀ (OffersOnly-mono inj-head (oo fzero))
               (OffersOnly-mono inj-tail (OffersOnly-⦀Fin (λ i → oo (fsuc i))))
  where
  -- head alphabet `αs fzero` embeds into the union at index `fzero`
  inj-head : ∀ at a → αs fzero at a → unionAlpha αs at a
  inj-head at a p = fzero , p
  -- tail union `unionAlpha (αs ∘ fsuc)` embeds into the union via `fsuc`
  inj-tail : ∀ at a → unionAlpha (λ i → αs (fsuc i)) at a → unionAlpha αs at a
  inj-tail at a (j , p) = fsuc j , p

-------------------------------------------------------------------------------------
-- The replicated-interleaving ≈DR congruences `cong-⦀Fin` / `cong-⦀⋆`
-------------------------------------------------------------------------------------

-- `⦀Fin`-congruence over a finite index: given per-index alphabets that are pairwise
-- disjoint and confine both families, and a pointwise ≈DR, the two folds are ≈DR.  By
-- induction on `n`: the `zero` fold is `Skip` (reflexivity); the `suc n` fold is
-- `f fzero ⦀ ⦀Fin n (f ∘ fsuc)`, closed by `cong-⦀` — its three `Sep` obligations are
-- discharged by `sep-from-OffersOnly` from head-vs-tail-union disjointness (pairwise
-- disj + `fzero ≢ fsuc j`), and the tail equivalence is the IH at `αs ∘ fsuc` (disj
-- transported through `suc-injective`).
cong-⦀Fin : ∀ {n} (αs : Fin n → Alpha)
            {f g : Fin n → PTree E (ExtI E) (⊤ {ℓr})}
          → (∀ i j → i ≢ j → Disj (αs i) (αs j))
          → (∀ i → OffersOnly (αs i) (f i))
          → (∀ i → OffersOnly (αs i) (g i))
          → (∀ i → f i ≈DR g i)
          → ⦀Fin n f ≈DR ⦀Fin n g
cong-⦀Fin {n = zero}  αs disj oof oog eq = drbisim-refl Skip
cong-⦀Fin {n = suc n} αs {f} {g} disj oof oog eq =
  cong-⦀ (mkSep (oof fzero) tailF)
         (mkSep (oog fzero) tailF)
         (mkSep (oog fzero) tailG)
         (eq fzero)
         (cong-⦀Fin (λ i → αs (fsuc i))
                    (λ i j i≢j → disj (fsuc i) (fsuc j) (λ e → i≢j (suc-injective e)))
                    (λ i → oof (fsuc i)) (λ i → oog (fsuc i)) (λ i → eq (fsuc i)))
  where
  -- the two tail folds confine to the tail-union alphabet
  tailF = OffersOnly-⦀Fin (λ i → oof (fsuc i))
  tailG = OffersOnly-⦀Fin (λ i → oog (fsuc i))
  -- head alphabet clashes with nothing in the tail union (pairwise disj + fzero ≢ fsuc j)
  hdDisj : ∀ {at a} → ¬ ∅ES .mem at a
         → αs fzero at a → unionAlpha (λ i → αs (fsuc i)) at a → ⊥
  hdDisj _ p (j , q) = disj fzero (fsuc j) (λ ()) _ _ p q
  -- the shared `Sep ∅ES` builder for a head confined by `αs fzero` and a tail-union fold
  mkSep : ∀ {P Q : PTree E (ExtI E) (⊤ {ℓr})}
        → OffersOnly (αs fzero) P → OffersOnly (unionAlpha (λ i → αs (fsuc i))) Q
        → Sep ∅ES P Q
  mkSep = sep-from-OffersOnly ∅ES hdDisj

-- the non-empty fold confines to the union of its leaf alphabets
OffersOnly-⦀Fin⁺ : ∀ {n} {αs : Fin (suc n) → Alpha}
                     {f : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr})}
                 → (∀ i → OffersOnly (αs i) (f i))
                 → OffersOnly (unionAlpha αs) (⦀Fin⁺ n f)
OffersOnly-⦀Fin⁺ {n = zero}  {αs = αs} oo = OffersOnly-mono inj-only (oo fzero)
  where
  -- at n = 0 the fold IS the single leaf, so its alphabet embeds at index fzero
  inj-only : ∀ at a → αs fzero at a → unionAlpha αs at a
  inj-only at a p = fzero , p
OffersOnly-⦀Fin⁺ {n = suc n} {αs = αs} oo =
  OffersOnly-⦀ (OffersOnly-mono inj-head (oo fzero))
               (OffersOnly-mono inj-tail (OffersOnly-⦀Fin⁺ (λ i → oo (fsuc i))))
  where
  -- head alphabet embeds into the union at index fzero
  inj-head : ∀ at a → αs fzero at a → unionAlpha αs at a
  inj-head at a p = fzero , p
  -- tail union embeds into the full union via fsuc
  inj-tail : ∀ at a → unionAlpha (λ i → αs (fsuc i)) at a → unionAlpha αs at a
  inj-tail at a (j , p) = fsuc j , p

-- `⦀Fin⁺`-congruence: pairwise-disjoint per-index alphabets confining both families
-- plus a pointwise ≈DR give ≈DR of the two folds.
cong-⦀Fin⁺ : ∀ {n} (αs : Fin (suc n) → Alpha)
               {f g : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr})}
           → (∀ i j → i ≢ j → Disj (αs i) (αs j))
           → (∀ i → OffersOnly (αs i) (f i))
           → (∀ i → OffersOnly (αs i) (g i))
           → (∀ i → f i ≈DR g i)
           → ⦀Fin⁺ n f ≈DR ⦀Fin⁺ n g
cong-⦀Fin⁺ {n = zero}  αs disj oof oog eq = eq fzero
cong-⦀Fin⁺ {n = suc n} αs {f} {g} disj oof oog eq =
  cong-⦀ (mkSep (oof fzero) tailF)
         (mkSep (oog fzero) tailF)
         (mkSep (oog fzero) tailG)
         (eq fzero)
         (cong-⦀Fin⁺ (λ i → αs (fsuc i))
                     (λ i j i≢j → disj (fsuc i) (fsuc j) (λ e → i≢j (suc-injective e)))
                     (λ i → oof (fsuc i)) (λ i → oog (fsuc i)) (λ i → eq (fsuc i)))
  where
  -- the two tail folds confine to the tail-union alphabet
  tailF = OffersOnly-⦀Fin⁺ (λ i → oof (fsuc i))
  tailG = OffersOnly-⦀Fin⁺ (λ i → oog (fsuc i))
  -- head alphabet clashes with nothing in the tail union (pairwise disj + fzero ≢ fsuc j)
  hdDisj : ∀ {at a} → ¬ ∅ES .mem at a
         → αs fzero at a → unionAlpha (λ i → αs (fsuc i)) at a → ⊥
  hdDisj _ p (j , q) = disj fzero (fsuc j) (λ ()) _ _ p q
  -- the shared `Sep ∅ES` builder for a head confined by `αs fzero` and a tail-union fold
  mkSep : ∀ {P Q : PTree E (ExtI E) (⊤ {ℓr})}
        → OffersOnly (αs fzero) P → OffersOnly (unionAlpha (λ i → αs (fsuc i))) Q
        → Sep ∅ES P Q
  mkSep = sep-from-OffersOnly ∅ES hdDisj

-- a cell of the list-indexed congruence: an alphabet, a matched pair of processes both
-- confined to it, and a proof they are ≈DR.
-- NOTE: the field is named `alph` (not `α`) to avoid a ClashingDefinition with the
-- module-level generalizable `variable α : Alpha`; the shape is otherwise the contract.
-- `ℓr` is an EXPLICIT parameter (rather than a generalized `variable`) so it is pinned
-- unambiguously wherever a `CongCell` is used below.
record CongCell (ℓr : Level) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  field
    alph : Alpha
    P Q  : PTree E (ExtI E) (⊤ {ℓr})
    ooP  : OffersOnly alph P
    ooQ  : OffersOnly alph Q
    eq   : P ≈DR Q

-- the pointwise-union of a list of cell alphabets: membership in ANY cell's alphabet.
-- Defined by recursion (into `⊎`/`⊥`) rather than `Any` so the result stays in `Set₀`
-- (the codomain of `Alpha`), unaffected by the big level of the `CongCell` element type.
unionAlphaL : List (CongCell ℓr) → Alpha
unionAlphaL []       at a = ⊥
unionAlphaL (c ∷ cs) at a = CongCell.alph c at a ⊎ unionAlphaL cs at a

-- a fold `⦀⋆ (map sel cs)` confines to the list-union of the cell alphabets, provided
-- each selected process is confined by its own cell alphabet (proved like `OffersOnly-⦀Fin`:
-- head injected via `inj₁`, tail via `inj₂`).
OffersOnly-⦀⋆-u : (sel : CongCell ℓr → PTree E (ExtI E) (⊤ {ℓr}))
                → (∀ c → OffersOnly (CongCell.alph c) (sel c))
                → (cs : List (CongCell ℓr))
                → OffersOnly (unionAlphaL cs) (⦀⋆ (map sel cs))
OffersOnly-⦀⋆-u sel hoo []       = OffersOnly-Skip
OffersOnly-⦀⋆-u sel hoo (c ∷ cs) =
  OffersOnly-⦀ (OffersOnly-mono (λ _ _ p → inj₁ p) (hoo c))
               (OffersOnly-mono (λ _ _ p → inj₂ p) (OffersOnly-⦀⋆-u sel hoo cs))

-- `⦀⋆`-congruence over a list of cells whose alphabets are pairwise disjoint (`AllPairs`):
-- by induction on the list, mirroring `cong-⦀Fin`.  The `AllPairs` head gives head-vs-each-
-- tail-cell disjointness (an `All`), folded (via the local `sepDisj`/`go`) into head-vs-
-- tail-union, which discharges `cong-⦀`'s three `Sep` obligations; the tail is the IH.
cong-⦀⋆ : (cs : List (CongCell ℓr))
        → AllPairs (λ c c′ → Disj (CongCell.alph c) (CongCell.alph c′)) cs
        → ⦀⋆ (map CongCell.P cs) ≈DR ⦀⋆ (map CongCell.Q cs)
cong-⦀⋆ []       []ᵖ        = drbisim-refl Skip
cong-⦀⋆ (c ∷ cs) (hd ∷ᵖ tl) =
  cong-⦀ (sep-from-OffersOnly ∅ES sepDisj (CongCell.ooP c) tailP)
         (sep-from-OffersOnly ∅ES sepDisj (CongCell.ooQ c) tailP)
         (sep-from-OffersOnly ∅ES sepDisj (CongCell.ooQ c) tailQ)
         (CongCell.eq c)
         (cong-⦀⋆ cs tl)
  where
  -- the two tail folds confine to the tail list-union alphabet
  tailP = OffersOnly-⦀⋆-u CongCell.P CongCell.ooP cs
  tailQ = OffersOnly-⦀⋆-u CongCell.Q CongCell.ooQ cs
  -- the head alphabet clashes with nothing in the tail union: recurse over the
  -- head-vs-each-tail `All` and split the tail-union membership (`inj₁`/`inj₂`).
  sepDisj : ∀ {at a} → ¬ ∅ES .mem at a
          → CongCell.alph c at a → unionAlphaL cs at a → ⊥
  sepDisj {at} {a} _ p q = go hd q
    where
    -- walk the head-vs-tail `All` in lockstep with the tail-union membership: `inj₁`
    -- picks out the matching cell (whose `Disj` head refutes `p`/`r` directly), `inj₂`
    -- recurses into the rest of the union.
    go : ∀ {cs′} → All (λ c′ → Disj (CongCell.alph c) (CongCell.alph c′)) cs′
       → unionAlphaL cs′ at a → ⊥
    go []       ()
    go (d ∷ ds) (inj₁ r) = d _ _ p r
    go (d ∷ ds) (inj₂ r) = go ds r

-------------------------------------------------------------------------------------
-- Closure of `OffersOnly` under the INTERRUPT `_△_`
-------------------------------------------------------------------------------------

-- forward declarations for the mutually-corecursive interrupt pair.
-- `P △ Q` is α-confined when BOTH operands are: every visible offer of the composite is
-- one operand's own offer (`△-ev-elim`), and every residual is again an interrupt, a bare
-- operand, or the both-offer `⊓` node below.
OffersOnly-△ : {P Q : PTree E (ExtI E) R}
             → OffersOnly α P → OffersOnly α Q → OffersOnly α (P △ Q)
-- the inline both-offer node `(P₁ △ Q) ⊓ Q₁` produced by `△-merge`: its visible menu is
-- empty (`∅v`), its two τ-branches land in `P₁ △ Q` (tag0) and `Q₁` (tag1).
OffersOnly-△-br2 : {P₁ Q Q₁ : PTree E (ExtI E) R}
                 → OffersOnly α P₁ → OffersOnly α Q → OffersOnly α Q₁
                 → OffersOnly α (ptree (react ∅v (△-br2 P₁ Q Q₁)))

OffersOnly-△ {P = P} {Q = Q} ooP ooQ .OffersOnly.now st with △-ev-elim P Q st
... | △evP  Pst   = OffersOnly.now ooP Pst
... | △evQ  Qst   = OffersOnly.now ooQ Qst
... | △evPQ Pst _ = OffersOnly.now ooP Pst
OffersOnly-△ {P = P} {Q = Q} ooP ooQ .OffersOnly.step {l = τ} st with △-τ-elim P Q st
... | △τP    Pst = OffersOnly-△ (OffersOnly.step ooP Pst) ooQ
... | △τQ    Qst = OffersOnly-△ ooP (OffersOnly.step ooQ Qst)
... | △τQret _   = ooQ
... | △τ⊓P   _   = ooP
... | △τ⊓Q   _   = ooQ
OffersOnly-△ {P = P} {Q = Q} ooP ooQ .OffersOnly.step {l = ev e} st with △-ev-elim P Q st
... | △evP  Pst     = OffersOnly-△ (OffersOnly.step ooP Pst) ooQ
... | △evQ  Qst     = OffersOnly.step ooQ Qst
... | △evPQ Pst Qst = OffersOnly-△-br2 (OffersOnly.step ooP Pst) ooQ (OffersOnly.step ooQ Qst)

OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.now  (sVis refl ())
OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.step (sRet ())
OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.step (sSil ())
OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.step (sVis refl ())
OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.step
  (sTau {i = _ , fin} {a = lift fzero} refl refl) = OffersOnly-△ ooP₁ ooQ
OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.step
  (sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl) = ooQ₁
OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.step
  (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ())
OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.step (sTau {i = _ , base _}   refl ())
OffersOnly-△-br2 ooP₁ ooQ ooQ₁ .OffersOnly.step (sTau {i = _ , pair _ _} refl ())

-------------------------------------------------------------------------------------
-- The "never terminates" invariant `NoRet`, and the `Sep△` discharge for `cong-△`
-------------------------------------------------------------------------------------

-- `NoRet P`: P never terminates — its own node is not a `ret`, and neither is that of
-- any state reachable from it.  It is exactly what `Sep△`'s `liveL` field needs.
record NoRet {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    nowNR  : NonRet (PTree.force P)
    stepNR : ∀ {l} {P′ : PTree E (ExtI E) R} → P ─[ l ]─► P′ → NoRet P′

-- walk a `NoRet` witness along a τ*-run
NoRet-τ* : {P P′ : PTree E (ExtI E) R} → P ─[τ*]─► P′ → NoRet P → NoRet P′
NoRet-τ* τ*-refl         nr = nr
NoRet-τ* (τ*-step st rs) nr = NoRet-τ* rs (NoRet.stepNR nr st)

-- ≈DR transfers `NoRet` BACKWARD: a √ of P is weakly matched by a √ of Q, so if no state
-- reachable from Q is a `ret`, none reachable from P is either.  (The `≈DR-OO` shape.)
≈DR-NoRet : {P Q : PTree E (ExtI E) R} → P ≈DR Q → NoRet Q → NoRet P
≈DR-NoRet {P = P} pq nrQ .NoRet.nowNR with PTree.force P in eqP
... | sil _      = tt₀
... | react _ _  = tt₀
... | ret r      with WSimF.on-ev (DRbisim.fwd pq) (sRet eqP)
...   | _ , wev q→q₁ (sRet eq₁) _ , _ =
        subst NonRet eq₁ (NoRet.nowNR (NoRet-τ* q→q₁ nrQ))
≈DR-NoRet pq nrQ .NoRet.stepNR {l = τ} st with WSimF.on-tau (DRbisim.fwd pq) st
... | _ , wτ q→q′ , p′q′ = ≈DR-NoRet p′q′ (NoRet-τ* q→q′ nrQ)
≈DR-NoRet pq nrQ .NoRet.stepNR {l = ev _} st with WSimF.on-ev (DRbisim.fwd pq) st
... | _ , wev q→q₁ q₁ev q₂→q′ , p′q′ =
      ≈DR-NoRet p′q′ (NoRet-τ* q₂→q′ (NoRet.stepNR (NoRet-τ* q→q₁ nrQ) q₁ev))

-- THE `Sep△` DISCHARGE, mirroring `sep-from-OffersOnly`: disjoint confining alphabets
-- refute the both-offer overlap (`now△`), and a `NoRet` on the LEFT operand supplies
-- `liveL`; both invariants are closed under stepping, so the record corecurses.
sep△-from-OffersOnly : {P Q : PTree E (ExtI E) R}
                     → Disj α β → NoRet P
                     → OffersOnly α P → OffersOnly β Q → Sep△ P Q
sep△-from-OffersOnly dj nr ooP ooQ .Sep△.liveL = NoRet.nowNR nr
sep△-from-OffersOnly dj nr ooP ooQ .Sep△.now△ Pst Qst =
  dj _ _ (OffersOnly.now ooP Pst) (OffersOnly.now ooQ Qst)
sep△-from-OffersOnly dj nr ooP ooQ .Sep△.stepL△ Pst =
  sep△-from-OffersOnly dj (NoRet.stepNR nr Pst) (OffersOnly.step ooP Pst) ooQ
sep△-from-OffersOnly dj nr ooP ooQ .Sep△.stepR△ Qst =
  sep△-from-OffersOnly dj nr ooP (OffersOnly.step ooQ Qst)

-------------------------------------------------------------------------------------
-- `NoRet` closure: deadlock, parallel, interleaving
-------------------------------------------------------------------------------------

-- `deadlock` is a stuck `react` node, hence never a `ret`
NoRet-deadlock : NoRet (deadlock {E = E} {I = ExtI E} {R = R})
NoRet-deadlock .NoRet.nowNR = tt₀
NoRet-deadlock .NoRet.stepNR (sRet ())
NoRet-deadlock .NoRet.stepNR (sSil ())
NoRet-deadlock .NoRet.stepNR (sVis refl ())
NoRet-deadlock .NoRet.stepNR (sTau refl ())

-- forward declarations for the mutually-corecursive Par / overlap-node pair.
-- `Par A merge P Q` returns only when BOTH operands do, so a `NoRet` on the LEFT
-- operand alone already forbids termination of the composite.
NoRet-Par : ∀ {R : Set ℓs} {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
            (A : EventSet) (merge : Mg R₁ R₂ R)
          → NoRet P → NoRet (Par A merge P Q)
-- the inline both-offer overlap node `(P′∥Q) ⊓ (P∥Q′)`: a `react` node whose τ-branches
-- land in `Par P′ Q` (tag0) and `Par P Q′` (tag1)
NoRet-brBoth : ∀ {R : Set ℓs} {A : EventSet} {merge : Mg R₁ R₂ R}
                 {P P′ : PTree E (ExtI E) R₁} {Q Q′ : PTree E (ExtI E) R₂}
             → NoRet P → NoRet P′
             → NoRet (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P′ Q′)))

NoRet-Par {P = P} {Q = Q} A merge nrP .NoRet.nowNR
  with PTree.force (Par A merge P Q) in eqPQ
... | sil _     = tt₀
... | react _ _ = tt₀
... | ret r     with Par-ev-elim A merge P Q (sRet eqPQ)
...   | ev√ eqP _ = subst NonRet eqP (NoRet.nowNR nrP)
NoRet-Par {P = P} {Q = Q} A merge nrP .NoRet.stepNR {l = τ} st
  with Par-τ-elim A merge P Q st
... | τL P′ Pst refl = NoRet-Par A merge (NoRet.stepNR nrP Pst)
... | τR Q′ Qst refl = NoRet-Par A merge nrP
NoRet-Par {P = P} {Q = Q} A merge nrP .NoRet.stepNR {l = ev e} st
  with Par-ev-elim A merge P Q st
... | evSync _ Pst _ = NoRet-Par A merge (NoRet.stepNR nrP Pst)
... | evL    _ Pst   = NoRet-Par A merge (NoRet.stepNR nrP Pst)
... | evR    _ Qst   = NoRet-Par A merge nrP
... | evBoth _ Pst _ = NoRet-brBoth nrP (NoRet.stepNR nrP Pst)
... | ev√    eqP _   = ⊥-elim (subst NonRet eqP (NoRet.nowNR nrP))

NoRet-brBoth nrP nrP′ .NoRet.nowNR = tt₀
NoRet-brBoth nrP nrP′ .NoRet.stepNR (sRet ())
NoRet-brBoth nrP nrP′ .NoRet.stepNR (sSil ())
NoRet-brBoth nrP nrP′ .NoRet.stepNR (sVis refl ())
NoRet-brBoth {A = A} {merge = merge} nrP nrP′ .NoRet.stepNR
  (sTau {i = _ , fin} {a = lift fzero} refl refl) = NoRet-Par A merge nrP′
NoRet-brBoth {A = A} {merge = merge} nrP nrP′ .NoRet.stepNR
  (sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl) = NoRet-Par A merge nrP
NoRet-brBoth nrP nrP′ .NoRet.stepNR
  (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ())
NoRet-brBoth nrP nrP′ .NoRet.stepNR (sTau {i = _ , base _}   refl ())
NoRet-brBoth nrP nrP′ .NoRet.stepNR (sTau {i = _ , pair _ _} refl ())

-- interleaving = parallel with the empty sync set (a direct `NoRet-Par` instance)
NoRet-⦀ : {P Q : PTree E (ExtI E) (⊤ {ℓr})} → NoRet P → NoRet (P ⦀ Q)
NoRet-⦀ nrP = NoRet-Par ∅ES (λ _ _ → tt) nrP

-------------------------------------------------------------------------------------
-- `NoRet` for the forever loops `iter` / `loop` / `loop0`
-------------------------------------------------------------------------------------

-- `NoInj₂ t`: the `A ⊎ R`-valued tree `t` only ever returns LEFT (`inj₁`) values, now and
-- after any run.  It is what makes `iter … t` loop forever instead of finishing.
record NoInj₂ {ℓr} {A : Set ℓ} {R : Set ℓr} (t : PTree E (ExtI E) (A ⊎ R))
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    nowNI  : ∀ {x} → PTree.force t ≡ ret x → Σ[ a ∈ A ] x ≡ inj₁ a
    stepNI : ∀ {l} {t′ : PTree E (ExtI E) (A ⊎ R)} → t ─[ l ]─► t′ → NoInj₂ t′

-- `deadlock` returns nothing at all, so vacuously nothing on the right
NoInj₂-deadlock : ∀ {A : Set ℓ} → NoInj₂ {A = A} (deadlock {E = E} {I = ExtI E} {R = A ⊎ R})
NoInj₂-deadlock .NoInj₂.nowNI ()
NoInj₂-deadlock .NoInj₂.stepNI (sRet ())
NoInj₂-deadlock .NoInj₂.stepNI (sSil ())
NoInj₂-deadlock .NoInj₂.stepNI (sVis refl ())
NoInj₂-deadlock .NoInj₂.stepNI (sTau refl ())

-- `Ret (inj₁ a)` returns exactly one value, a left one
NoInj₂-Ret : ∀ {A : Set ℓ} {a : A} → NoInj₂ {A = A} {R = R} (Ret (inj₁ a))
NoInj₂-Ret {a = a} .NoInj₂.nowNI refl = a , refl
NoInj₂-Ret .NoInj₂.stepNI (sRet _)  = NoInj₂-deadlock
NoInj₂-Ret .NoInj₂.stepNI (sSil ())
NoInj₂-Ret .NoInj₂.stepNI (sVis () _)
NoInj₂-Ret .NoInj₂.stepNI (sTau () _)

-- force-inversion: a `ret` node of `t >>= λ a → Ret (inj₁ a)` can only carry a LEFT
-- value.  Cased on a NAMED node for `force t` (the `force-ren-ret-inv` idiom) rather than
-- with `with`, which would abstract the stuck `force t` inside the hypothesis's own type.
bind-inj₁-ret : ∀ {A : Set ℓ} (t : PTree E (ExtI E) A) {x : A ⊎ R}
              → PTree.force (t >>= λ a → Ret (inj₁ a)) ≡ ret x → Σ[ a ∈ A ] x ≡ inj₁ a
bind-inj₁-ret {A = A} t {x = x} eq = aux (PTree.force t) refl
  where
  aux : (nf : NodeKind E (ExtI E) A) → PTree.force t ≡ nf → Σ[ a ∈ A ] x ≡ inj₁ a
  aux (ret a)      eqt = case trans (sym (fBind-ret (λ a′ → Ret (inj₁ a′)) t eqt)) eq of
                           λ { refl → a , refl }
  aux (sil c)      eqt = case trans (sym (fBind-sil (λ a′ → Ret (inj₁ a′)) t eqt)) eq of λ ()
  aux (react v τc) eqt = case trans (sym (fBind-react (λ a′ → Ret (inj₁ a′)) t eqt)) eq of λ ()

-- `t >>= λ a → Ret (inj₁ a)` returns only left values, WHATEVER `t` does — the loop
-- re-entry shape of `loop`.  (Proof shape: `OffersOnly->>=`.)
NoInj₂->>=inj₁ : ∀ {A : Set ℓ} (t : PTree E (ExtI E) A)
               → NoInj₂ {A = A} {R = R} (t >>= λ a → Ret (inj₁ a))
NoInj₂->>=inj₁ t .NoInj₂.nowNI eq = bind-inj₁-ret t eq
NoInj₂->>=inj₁ t .NoInj₂.stepNI st with PTree.force t in eqt
... | ret a = NoInj₂.stepNI NoInj₂-Ret
                (retarget (sym (fBind-ret (λ a → Ret (inj₁ a)) t eqt)) st)
... | sil c with st
...   | sSil eqf with sil-injective (trans (sym (fBind-sil (λ a → Ret (inj₁ a)) t eqt)) eqf)
...     | refl = NoInj₂->>=inj₁ c
NoInj₂->>=inj₁ t .NoInj₂.stepNI st | sil c | sRet eqf =
  ⊥-elim (case trans (sym (fBind-sil (λ a → Ret (inj₁ a)) t eqt)) eqf of λ ())
NoInj₂->>=inj₁ t .NoInj₂.stepNI st | sil c | sVis eqf _ =
  ⊥-elim (case trans (sym (fBind-sil (λ a → Ret (inj₁ a)) t eqt)) eqf of λ ())
NoInj₂->>=inj₁ t .NoInj₂.stepNI st | sil c | sTau eqf _ =
  ⊥-elim (case trans (sym (fBind-sil (λ a → Ret (inj₁ a)) t eqt)) eqf of λ ())
NoInj₂->>=inj₁ t .NoInj₂.stepNI st | react v τc with st
...   | sVis {at = at} {a = a} eqf br
        with bindV-elim (λ a → Ret (inj₁ a)) (react v τc)
               (subst (λ g → g at a ≡ just _)
                      (sym (proj₁ (react-injective
                             (trans (sym (fBind-react (λ a → Ret (inj₁ a)) t eqt)) eqf))))
                      br)
...     | t′ , vv , refl = NoInj₂->>=inj₁ t′
NoInj₂->>=inj₁ t .NoInj₂.stepNI st | react v τc | sTau {i = i} {a = a} eqf br
  with bindT-elim (λ a → Ret (inj₁ a)) (react v τc)
         (subst (λ g → g i a ≡ just _)
                (sym (proj₂ (react-injective
                       (trans (sym (fBind-react (λ a → Ret (inj₁ a)) t eqt)) eqf))))
                br)
...   | t′ , vv , refl = NoInj₂->>=inj₁ t′
NoInj₂->>=inj₁ t .NoInj₂.stepNI st | react v τc | sRet eqf =
  ⊥-elim (case trans (sym (fBind-react (λ a → Ret (inj₁ a)) t eqt)) eqf of λ ())
NoInj₂->>=inj₁ t .NoInj₂.stepNI st | react v τc | sSil eqf =
  ⊥-elim (case trans (sym (fBind-react (λ a → Ret (inj₁ a)) t eqt)) eqf of λ ())

-- `iter-bind t k` never returns when neither the body `t` nor any re-entry `k a` ever
-- returns a RIGHT value: the `ret (inj₂ r)` clause — iteration's only exit — is
-- unreachable, so every node is a `sil`/`react`.  (Proof shape: `OffersOnly-iter-bind`.)
NoRet-iter-bind : ∀ {A : Set ℓ} {t : PTree E (ExtI E) (A ⊎ R)}
                    {k : A → PTree E (ExtI E) (A ⊎ R)}
                → NoInj₂ t → (∀ a → NoInj₂ (k a)) → NoRet (iter-bind t k)
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.nowNR with PTree.force t in eqt
... | ret (inj₁ a′) = tt₀
... | ret (inj₂ r)  = ⊥-elim (case proj₂ (NoInj₂.nowNI ni eqt) of λ ())
... | sil c         = tt₀
... | react v τc    = tt₀
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st with PTree.force t in eqt
... | ret (inj₁ a′) with st
...   | sSil eqf with sil-injective (trans (sym (fIter-r1 k t eqt)) eqf)
...     | refl   = NoRet-iter-bind (nik a′) nik
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | ret (inj₁ a′) | sRet eqf =
  ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | ret (inj₁ a′) | sVis eqf _ =
  ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | ret (inj₁ a′) | sTau eqf _ =
  ⊥-elim (case trans (sym (fIter-r1 k t eqt)) eqf of λ ())
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | ret (inj₂ r) =
  ⊥-elim (case proj₂ (NoInj₂.nowNI ni eqt) of λ ())
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | sil c with st
...   | sSil eqf with sil-injective (trans (sym (fIter-sil k t eqt)) eqf)
...     | refl   = NoRet-iter-bind (NoInj₂.stepNI ni (sSil eqt)) nik
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | sil c | sRet eqf =
  ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | sil c | sVis eqf _ =
  ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | sil c | sTau eqf _ =
  ⊥-elim (case trans (sym (fIter-sil k t eqt)) eqf of λ ())
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | react v τc with st
...   | sVis {at = at} {a = a} eqf br
        with iterV-elim k (react v τc)
               (subst (λ g → g at a ≡ just _)
                      (sym (proj₁ (react-injective (trans (sym (fIter-react k t eqt)) eqf))))
                      br)
...     | t′ , vv , refl = NoRet-iter-bind (NoInj₂.stepNI ni (sVis eqt vv)) nik
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | react v τc | sTau {i = i} {a = a} eqf br
  with iterT-elim k (react v τc)
         (subst (λ g → g i a ≡ just _)
                (sym (proj₂ (react-injective (trans (sym (fIter-react k t eqt)) eqf))))
                br)
...   | t′ , vv , refl = NoRet-iter-bind (NoInj₂.stepNI ni (sTau eqt vv)) nik
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | react v τc | sRet eqf =
  ⊥-elim (case trans (sym (fIter-react k t eqt)) eqf of λ ())
NoRet-iter-bind {t = t} {k = k} ni nik .NoRet.stepNR st | react v τc | sSil eqf =
  ⊥-elim (case trans (sym (fIter-react k t eqt)) eqf of λ ())

-- `iter k a` = `iter-bind (k a) k`, so non-termination follows directly
NoRet-iter : ∀ {A : Set ℓ} {k : A → PTree E (ExtI E) (A ⊎ R)} {a : A}
           → (∀ a → NoInj₂ (k a)) → NoRet (iter k a)
NoRet-iter {a = a} nik = NoRet-iter-bind (nik a) nik

-- the stateful forever loop never terminates, for ANY body: `loop body a = iter step a`
-- with `step a = body a >>= λ a′ → Ret (inj₁ a′)`, which only ever returns left values.
NoRet-loop : ∀ {A : Set ℓ} {body : A → PTree E (ExtI E) A} {a : A}
           → NoRet {R = R} (loop body a)
NoRet-loop {body = body} = NoRet-iter (λ a → NoInj₂->>=inj₁ (body a))

-- the non-stateful forever loop `loop0 body = loop (λ _ → body) tt`
NoRet-loop0 : ∀ {body : PTree E (ExtI E) (⊤ {ℓ})} → NoRet {R = R} (loop0 body)
NoRet-loop0 = NoRet-loop

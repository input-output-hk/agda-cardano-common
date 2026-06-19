{-# OPTIONS --guardedness #-}

-- Sequential composition (>>= / >>) laws — the monad-law fragment of TPC §6 / UCS §7.
--   ;-unit-l (T6.4):  SKIP ; P = P            (left identity — bind is strict-at-ret)
-- (The right identity P;SKIP=P (T6.5 = bind-ret), associativity (T6.3 = bind-assoc) and
--  ;-step (T6.7) are genuine coinductive bind bisimulations; ;-dist-l (T6.1) is the
--  already-proved seq-⊓-distrib-FD; ;-dist-r (T6.2) is FD-direct.)

open import Level using (Level)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Process_Trees

module CSP.Laws.FD.SeqLaws {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_>>=_; _>>_; Ret; Skip; Prefix; Prefix-cont; ∅t; bindV; bindT; pchoice)
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.Bisim   {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Bisim.IterCong        E-≟
  using (ret-no-τ; sil-no-ev; sil-τ-inv; react-τ-inv)
open import CSP.Laws.Bisim.LoopCong        E-≟
  using (fBind-ret; fBind-sil; fBind-react; bindV-elim; bindT-elim; bind-ev; bind-τ)

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

-- retarget a step across a force-equation; force-equal trees are strongly bisimilar.
retarget : {a b u : PTree E (ExtI E) R} {l : Label R}
         → PTree.force a ≡ PTree.force b → b ─[ l ]─► u → a ─[ l ]─► u
retarget eq (sRet eqf)    = sRet (trans eq eqf)
retarget eq (sSil eqf)    = sSil (trans eq eqf)
retarget eq (sVis eqf br) = sVis (trans eq eqf) br
retarget eq (sTau eqf br) = sTau (trans eq eqf) br

sbisim-force-eq : {t u : PTree E (ExtI E) R} → PTree.force t ≡ PTree.force u → t ∼ u
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-ev  step = _ , retarget (sym eq) step , sbisim-refl _
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-tau step = _ , retarget (sym eq) step , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-ev  step = _ , retarget eq step , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-tau step = _ , retarget eq step , sbisim-refl _

-- ;-unit-l (T6.4 / U7.2):  SKIP ; P = P.  SKIP = Ret tt, and bind is force-transparent
-- at ret (force(Ret tt >>= k) ≡ force (k tt) = force P), so the two are force-equal.
seq-unit-l-∼ : (P : PTree E (ExtI E) R) → (Skip {ℓr = ℓr} >> P) ∼ P
seq-unit-l-∼ {ℓr = ℓr} P =
  sbisim-force-eq {t = Skip {ℓr = ℓr} >> P} {u = P}
    (fBind-ret (λ _ → P) (Skip {ℓr = ℓr}) {r = tt} refl)

seq-unit-l-FD : (P : PTree E (ExtI E) R) → (Skip {ℓr = ℓr} >> P) ≈FD P
seq-unit-l-FD P = drbisim→≈FD (sbisim→drbisim (seq-unit-l-∼ P))

-- ;-unit-r (T6.5 / U7.1) = the monad RIGHT identity:  P >>= Ret ∼ P.
--
-- Guardedness story (the wall this file hit): a `with` clause in a coinductive
-- definition desugars to a top-level auxiliary, and the corecursive bind-ret call routed
-- through that auxiliary is no longer syntactically guarded under Sbisim's fwd/bwd
-- copattern.  Fix = SEPARATE the two concerns:
--   (1) decompose-ev/τ  — with-HEAVY, NO recursion, lives OUTSIDE the mutual block, so
--       it is plain terminating pattern matching; it turns a step of (P>>=Ret) into a
--       step of P plus the residual `M ≡ t″ >>= Ret`.
--   (2) mk-ev/τ, simB    — with-FREE assemblers INSIDE the mutual block; the corecursive
--       call sits directly under the Σ/record constructor, so it stays guarded.
-- The reversed bisim bind-retR : P ∼ (P>>=Ret) is defined mutually so simB can refer to
-- it WITHOUT sbisim-sym (which unguards by projecting the corecursive call).

-- (1) decomposition — terminating, no corecursion, with-heavy.
decompose-ev : (P : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
  → (P >>= Ret) ─[ ev l ]─► M
  → (P ─[ ev l ]─► M)
    ⊎ (Σ[ t″ ∈ PTree E (ExtI E) R ] (P ─[ ev l ]─► t″) × (M ≡ (t″ >>= Ret)))
decompose-ev P step with PTree.force P in eqP
... | sil c  = ⊥-elim (sil-no-ev (fBind-sil Ret P eqP) step)
... | ret r  = inj₁ (retarget (trans eqP (sym (fBind-ret Ret P eqP))) step)
... | react v τc with step
...   | sRet eqf = ⊥-elim (case trans (sym (fBind-react Ret P eqP)) eqf of λ ())
...   | sVis {at = at} {a = a} eqf br with bindV-elim Ret (react v τc)
          (subst (λ g → g at a ≡ just _)
                 (sym (proj₁ (react-injective (trans (sym (fBind-react Ret P eqP)) eqf)))) br)
...     | t″ , vv , refl = inj₂ (t″ , sVis eqP vv , refl)

decompose-τ : (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
  → (P >>= Ret) ─[ τ ]─► M
  → Σ[ t″ ∈ PTree E (ExtI E) R ] (P ─[ τ ]─► t″) × (M ≡ (t″ >>= Ret))
decompose-τ P step with PTree.force P in eqP
... | ret r  = ⊥-elim (ret-no-τ (fBind-ret Ret P eqP) step)
... | sil c with sil-τ-inv (fBind-sil Ret P eqP) step
...   | refl = c , sSil eqP , refl
decompose-τ P step | react v τc with react-τ-inv (fBind-react Ret P eqP) step
... | i , a , br with bindT-elim Ret (react v τc) br
...   | t″ , vτ , refl = t″ , sTau eqP vτ , refl

-- (2) the mutual block: forward declarations, then with-free definitions.
bind-ret  : (P : PTree E (ExtI E) R) → (P >>= Ret) ∼ P
bind-retR : (P : PTree E (ExtI E) R) → P ∼ (P >>= Ret)
mk-ev : (P : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
      → (P ─[ ev l ]─► M)
        ⊎ (Σ[ t″ ∈ PTree E (ExtI E) R ] (P ─[ ev l ]─► t″) × (M ≡ (t″ >>= Ret)))
      → Σ[ M′ ∈ PTree E (ExtI E) R ] (P ─[ ev l ]─► M′ × Sbisim R M M′)
mk-τ : (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
     → Σ[ t″ ∈ PTree E (ExtI E) R ] (P ─[ τ ]─► t″) × (M ≡ (t″ >>= Ret))
     → Σ[ M′ ∈ PTree E (ExtI E) R ] (P ─[ τ ]─► M′ × Sbisim R M M′)
simB : (P : PTree E (ExtI E) R) → SSimF (Sbisim R) P (P >>= Ret)

bind-ret  P .Sbisim.fwd .SSimF.on-ev  step = mk-ev P (decompose-ev P step)
bind-ret  P .Sbisim.fwd .SSimF.on-tau step = mk-τ  P (decompose-τ  P step)
bind-ret  P .Sbisim.bwd = simB P
bind-retR P .Sbisim.fwd = simB P
bind-retR P .Sbisim.bwd .SSimF.on-ev  step = mk-ev P (decompose-ev P step)
bind-retR P .Sbisim.bwd .SSimF.on-tau step = mk-τ  P (decompose-τ  P step)

mk-ev P (inj₁ pstep)                = _  , pstep , sbisim-refl _
mk-ev P (inj₂ (t″ , pstep , refl))  = t″ , pstep , bind-ret t″
mk-τ  P (t″ , pstep , refl)          = t″ , pstep , bind-ret t″

simB P .SSimF.on-ev (sVis eqP br) = _ , bind-ev Ret P (sVis eqP br) , bind-retR _
simB P .SSimF.on-ev (sRet eqP)    = deadlock , sRet (fBind-ret Ret P eqP) , sbisim-refl deadlock
simB P .SSimF.on-tau step          = _ , bind-τ Ret P step , bind-retR _

-- P >> Skip = P >>= (λ _ → Ret tt) = P >>= Ret on ⊤ (η), so ;-unit-r is bind-ret.
seq-unit-r-∼ : (P : PTree E (ExtI E) (⊤ {ℓr})) → (P >> Skip {ℓr = ℓr}) ∼ P
seq-unit-r-∼ P = bind-ret P

seq-unit-r-FD : (P : PTree E (ExtI E) (⊤ {ℓr})) → (P >> Skip {ℓr = ℓr}) ≈FD P
seq-unit-r-FD P = drbisim→≈FD (sbisim→drbisim (seq-unit-r-∼ P))

-- ;-step (T6.7):  (?x:A→P) ; Q = ?x:A→(P;Q), i.e. (Prefix e P) >>= k ∼ Prefix e (λ x → P x >>= k).
-- A prefix is a pure-visible react (∅t τ-part), so both sides have empty τ (vacuous on-tau
-- via the ∅t/bindT-of-∅t = nothing reductions) and identical visible behaviour: binding k
-- through the prefix continuation matches Prefix-cont of the post-bound continuation.  No
-- recursion (the matched targets coincide), so guardedness is immediate.

-- the visible-map fusion, both directions, by casing the event-decision E-≟.
prefix-cont-bind : {A : Set ℓ} (e : E A) (P : A → PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                   {at : AnyTypes E} {a : proj₁ at} {t : PTree E (ExtI E) R}
                 → Prefix-cont e P at a ≡ just t
                 → Prefix-cont e (λ x → P x >>= k) at a ≡ just (t >>= k)
prefix-cont-bind {A = A} e P k {at = at} eq with E-≟ (A , e) at
... | yes refl = case eq of λ { refl → refl }
... | no  _    = case eq of λ ()

prefix-cont-bind-bwd : {A : Set ℓ} (e : E A) (P : A → PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                       {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) S}
                     → Prefix-cont e (λ x → P x >>= k) at a ≡ just M
                     → bindV k (react (Prefix-cont e P) ∅t) at a ≡ just M
prefix-cont-bind-bwd {A = A} e P k {at = at} eq with E-≟ (A , e) at
... | yes refl = eq
... | no  _    = case eq of λ ()

prefix-step-∼ : {A : Set ℓ} (e : E A) (P : A → PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
              → (Prefix e P >>= k) ∼ Prefix e (λ x → P x >>= k)
prefix-step-∼ e P k .Sbisim.fwd .SSimF.on-ev (sRet eqf) =
  ⊥-elim (case trans (sym (fBind-react k (Prefix e P) refl)) eqf of λ ())
prefix-step-∼ e P k .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqf br)
  with bindV-elim k (react (Prefix-cont e P) ∅t)
         (subst (λ g → g at a ≡ just _)
                (sym (proj₁ (react-injective (trans (sym (fBind-react k (Prefix e P) refl)) eqf)))) br)
... | t , vt , refl =
      t >>= k , sVis refl (prefix-cont-bind e P k vt) , sbisim-refl (t >>= k)
prefix-step-∼ e P k .Sbisim.fwd .SSimF.on-tau step
  with react-τ-inv (fBind-react k (Prefix e P) refl) step
... | i , a , br = ⊥-elim (case br of λ ())
prefix-step-∼ e P k .Sbisim.bwd .SSimF.on-ev (sRet eqf) = ⊥-elim (case eqf of λ ())
prefix-step-∼ e P k .Sbisim.bwd .SSimF.on-ev (sVis {at = at} {a = a} eqf br) =
  _ , sVis (fBind-react k (Prefix e P) refl)
           (prefix-cont-bind-bwd e P k
             (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) br))
    , sbisim-refl _
prefix-step-∼ e P k .Sbisim.bwd .SSimF.on-tau step with react-τ-inv refl step
... | i , a , br = ⊥-elim (case br of λ ())

prefix-step-FD : {A : Set ℓ} (e : E A) (P : A → PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
               → (Prefix e P >>= k) ≈FD Prefix e (λ x → P x >>= k)
prefix-step-FD e P k = drbisim→≈FD (sbisim→drbisim (prefix-step-∼ e P k))

-------------------------------------------------------------------------------------
-- ;-step, MENU version (T6.7 / U7.4):  (?x:A→P) ; Q = ?x:A→(P;Q) over an arbitrary
-- prefix-CHOICE menu `pchoice v` (A = any set of events, multi-channel), not just the
-- single channel `Prefix e P`.  RHS = the menu of post-bound continuations
-- `mapBind k v at a = map (_>>= k) (v at a)`.  Same shape as prefix-step-∼: a pure-visible
-- menu has empty τ, so binding only threads k through the visible continuations.
-------------------------------------------------------------------------------------

mapBind : (k : R → PTree E (ExtI E) S)
          (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
        → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) S))
mapBind k v at a = map (_>>= k) (v at a)

menu-cont-bind : (k : R → PTree E (ExtI E) S)
                 (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                 {at : AnyTypes E} {a : proj₁ at} {t : PTree E (ExtI E) R}
               → v at a ≡ just t → mapBind k v at a ≡ just (t >>= k)
menu-cont-bind k v eq = cong (map (_>>= k)) eq

menu-cont-bind-bwd : (k : R → PTree E (ExtI E) S)
                     (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                     {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) S}
                   → mapBind k v at a ≡ just M → bindV k (react v ∅t) at a ≡ just M
menu-cont-bind-bwd k v {at = at} {a = a} eq with v at a
... | just t  = eq
... | nothing = case eq of λ ()

seq-step-menu-∼ : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                  (k : R → PTree E (ExtI E) S)
                → (pchoice v >>= k) ∼ pchoice (mapBind k v)
seq-step-menu-∼ v k .Sbisim.fwd .SSimF.on-ev (sRet eqf) =
  ⊥-elim (case trans (sym (fBind-react k (pchoice v) refl)) eqf of λ ())
seq-step-menu-∼ v k .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqf br)
  with bindV-elim k (react v ∅t)
         (subst (λ g → g at a ≡ just _)
                (sym (proj₁ (react-injective (trans (sym (fBind-react k (pchoice v) refl)) eqf)))) br)
... | t , vt , refl =
      t >>= k , sVis refl (menu-cont-bind k v vt) , sbisim-refl (t >>= k)
seq-step-menu-∼ v k .Sbisim.fwd .SSimF.on-tau step
  with react-τ-inv (fBind-react k (pchoice v) refl) step
... | i , a , br = ⊥-elim (case br of λ ())
seq-step-menu-∼ v k .Sbisim.bwd .SSimF.on-ev (sRet eqf) = ⊥-elim (case eqf of λ ())
seq-step-menu-∼ v k .Sbisim.bwd .SSimF.on-ev (sVis {at = at} {a = a} eqf br) =
  _ , sVis (fBind-react k (pchoice v) refl)
           (menu-cont-bind-bwd k v
             (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) br))
    , sbisim-refl _
seq-step-menu-∼ v k .Sbisim.bwd .SSimF.on-tau step with react-τ-inv refl step
... | i , a , br = ⊥-elim (case br of λ ())

-- (?x:A→P) ; Q  ≈FD  ?x:A→(P;Q)      (full prefix-choice menu)
seq-step-menu-FD : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                   (k : R → PTree E (ExtI E) S)
                 → (pchoice v >>= k) ≈FD pchoice (mapBind k v)
seq-step-menu-FD v k = drbisim→≈FD (sbisim→drbisim (seq-step-menu-∼ v k))

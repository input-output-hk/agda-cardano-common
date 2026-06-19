{-# OPTIONS --guardedness #-}

-- Hide FAILURES decomposition — the unary analogue of CSP.Laws.FD.ParallelFailures,
-- and the first foundation piece for hide-∥-dist (T3.7/T3.8).
--
-- A stable failure of `P ∖ Z` de-hides (via the `HideTr Z` relation) to a `P`-reach to a
-- residual `P′` whose hide `P′ ∖ Z` refuses the same set — and back.  Built straight from
-- the existing hide step/trace inversions (`Hide-τ-elim`/`Hide-ev-elim`, `Hide-keep`/
-- `Hide-hidden`/`Hide-√`).  No postulate (the divergence half — which needs a `Hide-Diverges→`
-- König step — is separate).
--
-- The √/termination step of hiding reaches the plain `deadlock`, whose hide `deadlock ∖ Z`
-- forces to an all-`nothing` react node, hence is stable and refuses everything
-- (`hide-deadlock-refuses`).

open import Level using (Level; Lift; lift)
open import Data.Maybe using (nothing)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Process_Trees

module CSP.Laws.FD.HideFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Refusals {E = E} {I = ExtI E}
  using (Offers; Refuses; deadlock-refuses; deadlock-no-offer)
open import Semantics.Failures {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.DRBisim  {E = E} {I = ExtI E} using (Diverges; deadlock-no-τ; deadlock-converges)
open import Semantics.DRImpliesFD {E = E} {I = ExtI E} using (stable-no-τ)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; IsDivergence; empty-div)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (HideTr; hnil; hkeep; hdrop; h√; Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√; Hide-keep; Hide-hidden; Hide-√; Hide-τ)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- `deadlock ∖ Z` is stable and refuses everything.
-------------------------------------------------------------------------------------

-- the τ-emit branch over the all-nothing deadlock node is everywhere `nothing`.
hide-emit-dl : (Z : EventSet) {B : Set ℓ} (i′ : ExtI E B) (a : B)
             → hide-emit Z (PTree.force (deadlock {R = R})) i′ a ≡ nothing
hide-emit-dl Z (base e) a with EventSet.dec Z (_ , e) a
... | yes _ = refl
... | no  _ = refl
hide-emit-dl Z (pair _ _) a = refl
hide-emit-dl Z fin       a = refl

hide-deadlock-stable : (Z : EventSet) → isStable (deadlock {R = R} ∖ Z)
hide-deadlock-stable Z (_ , base _)            a = refl
hide-deadlock-stable Z (_ , fin)               a = refl
hide-deadlock-stable Z (_ , pair (base _)   _) a = refl
hide-deadlock-stable Z (_ , pair (pair _ _) _) a = refl
hide-deadlock-stable Z (_ , pair fin i′) (lift fzero           , a) = refl
hide-deadlock-stable Z (_ , pair fin i′) (lift (fsuc fzero)    , a) = hide-emit-dl Z i′ a
hide-deadlock-stable Z (_ , pair fin i′) (lift (fsuc (fsuc _)) , a) = refl

hide-deadlock-no-offer : (Z : EventSet) {e : Event√ R} {t′ : PTree E (ExtI E) R}
                       → ¬ ((deadlock ∖ Z) ─[ ev e ]─► t′)
hide-deadlock-no-offer Z step with Hide-ev-elim Z deadlock step
... | heV P′ ¬mem dev = deadlock-no-offer dev
... | he√ ()

hide-deadlock-refuses : (Z : EventSet) {X : Event√ R → Set ℓx} → Refuses (deadlock ∖ Z) X
hide-deadlock-refuses Z = hide-deadlock-stable Z , λ e Xe off → hide-deadlock-no-offer Z (proj₂ off)

-------------------------------------------------------------------------------------
-- failures decomposition
-------------------------------------------------------------------------------------

-- a de-hidden witness: P reaches P′ along s′, s′ projects to s by HideTr, and P′∖Z refuses X.
HideFailOut : EventSet → PTree E (ExtI E) R → List (Event√ R) → (Event√ R → Set ℓx) → Set _
HideFailOut {R = R} Z P s X =
  Σ[ s′ ∈ List (Event√ R) ] Σ[ P′ ∈ PTree E (ExtI E) R ]
    (P ⟹⟨ s′ ⟩ P′) × HideTr Z s′ s × Refuses (P′ ∖ Z) X

-- a stable-failure reach of P∖Z de-hides.
Hide-reach-fail : (Z : EventSet) (P : PTree E (ExtI E) R)
                  {s : List (Event√ R)} {W : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
                → (P ∖ Z) ⟹⟨ s ⟩ W → Refuses W X → HideFailOut Z P s X
Hide-reach-fail Z P ⟹-refl refW = [] , P , ⟹-refl , hnil , refW
Hide-reach-fail Z P (⟹-τ step rest) refW with Hide-τ-elim Z P step
... | hτP P'' Pτ refl with Hide-reach-fail Z P'' rest refW
...   | s′ , Pr , r , h , rf = s′ , Pr , ⟹-τ Pτ r , h , rf
Hide-reach-fail Z P (⟹-τ step rest) refW | hτH {B = B} {e = e} {a = a} P'' csat Pev refl
  with Hide-reach-fail Z P'' rest refW
...   | s′ , Pr , r , h , rf = (evl (evLabel B e a) ∷ s′) , Pr , ⟹-ev Pev r , hdrop csat h , rf
Hide-reach-fail Z P (⟹-ev step rest) refW with Hide-ev-elim Z P step
... | heV {B = B} {e = e} {a = a} P'' ¬csat Pev with Hide-reach-fail Z P'' rest refW
...   | s′ , Pr , r , h , rf = (evl (evLabel B e a) ∷ s′) , Pr , ⟹-ev Pev r , hkeep ¬csat h , rf
Hide-reach-fail Z P (⟹-ev step rest) refW | he√ {r = r} fpP with rest
...   | ⟹-refl      = (√ r ∷ []) , deadlock , ⟹-ev (sRet fpP) ⟹-refl , h√ , hide-deadlock-refuses Z
...   | ⟹-τ st _    = ⊥-elim (deadlock-no-τ st)
...   | ⟹-ev st _   = ⊥-elim (deadlock-no-offer st)

Hide-failures-elim : (Z : EventSet) (P : PTree E (ExtI E) R)
                     {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                   → failures (P ∖ Z) s X → HideFailOut Z P s X
Hide-failures-elim Z P (W , reach , refW) = Hide-reach-fail Z P reach refW

-- dual: re-hide a P-failure per a HideTr witness into a (P∖Z)-failure.
Hide-failures-intro : (Z : EventSet) (P : PTree E (ExtI E) R)
                      {P′ : PTree E (ExtI E) R} {s′ s : List (Event√ R)} {X : Event√ R → Set ℓx}
                    → P ⟹⟨ s′ ⟩ P′ → HideTr Z s′ s → Refuses (P′ ∖ Z) X → failures (P ∖ Z) s X
Hide-failures-intro Z P (⟹-τ Pτ restP) h rf with Hide-failures-intro Z _ restP h rf
... | W , bs , ref = W , ⟹-τ (Hide-τ Z P Pτ) bs , ref
Hide-failures-intro Z P ⟹-refl hnil rf = (P ∖ Z) , ⟹-refl , rf
Hide-failures-intro Z P (⟹-ev Pev restP) (hkeep ¬csat h) rf with Hide-failures-intro Z _ restP h rf
... | W , bs , ref = W , ⟹-ev (Hide-keep Z P ¬csat Pev) bs , ref
Hide-failures-intro Z P (⟹-ev Pev restP) (hdrop csat h) rf with Hide-failures-intro Z _ restP h rf
... | W , bs , ref = W , ⟹-τ (Hide-hidden Z P csat Pev) bs , ref
Hide-failures-intro Z P (⟹-ev (sRet fpP) restP) h√ rf =
  deadlock , ⟹-ev (Hide-√ Z P fpP) ⟹-refl , deadlock-refuses

-------------------------------------------------------------------------------------
-- divergence decomposition (threading `Diverges (P′∖Z)` through the de-hiding;
-- the König step `Hide-Diverges→`, which pushes such a divergence into P's own
-- divergence vs an infinite hidden-event stream, is separate — needed only for the
-- combine, not here).
-------------------------------------------------------------------------------------

-- τ / event prepends for divergences (a τ does not extend the visible trace).
div-τ-prepend : {P P′ : PTree E (ExtI E) R} {s : List (Event√ R)}
              → P ─[ τ ]─► P′ → divergences P′ s → divergences P s
div-τ-prepend step d = record
  { prefix = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = d .IsDivergence.split  ; witness = d .IsDivergence.witness
  ; reach  = ⟹-τ step (d .IsDivergence.reach) ; divwit = d .IsDivergence.divwit }

div-ev-prepend : {P P′ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
               → P ─[ ev e ]─► P′ → divergences P′ s → divergences P (e ∷ s)
div-ev-prepend {e = e} step d = record
  { prefix = e ∷ d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = cong (e ∷_) (d .IsDivergence.split) ; witness = d .IsDivergence.witness
  ; reach  = ⟹-ev step (d .IsDivergence.reach) ; divwit = d .IsDivergence.divwit }

-- hiding only ADDS divergence: a τ-divergence of P lifts to one of P∖Z (each P-τ
-- becomes a (P∖Z)-τ via Hide-τ).  Coinductive, no König.
hide-Diverges-lift : {P : PTree E (ExtI E) R} (Z : EventSet) → Diverges P → Diverges (P ∖ Z)
hide-Diverges-lift         Z d .Diverges.next = (d .Diverges.next) ∖ Z
hide-Diverges-lift {P = P} Z d .Diverges.step = Hide-τ Z P (d .Diverges.step)
hide-Diverges-lift         Z d .Diverges.rest = hide-Diverges-lift Z (d .Diverges.rest)

HideDivOut : EventSet → PTree E (ExtI E) R → List (Event√ R) → Set _
HideDivOut {R = R} Z P pre =
  Σ[ pre′ ∈ List (Event√ R) ] Σ[ P′ ∈ PTree E (ExtI E) R ]
    (P ⟹⟨ pre′ ⟩ P′) × HideTr Z pre′ pre × Diverges (P′ ∖ Z)

Hide-reach-div : (Z : EventSet) (P : PTree E (ExtI E) R)
                 {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
               → (P ∖ Z) ⟹⟨ pre ⟩ W → Diverges W → HideDivOut Z P pre
Hide-reach-div Z P ⟹-refl divW = [] , P , ⟹-refl , hnil , divW
Hide-reach-div Z P (⟹-τ step rest) divW with Hide-τ-elim Z P step
... | hτP P'' Pτ refl with Hide-reach-div Z P'' rest divW
...   | pre′ , Pr , r , h , dv = pre′ , Pr , ⟹-τ Pτ r , h , dv
Hide-reach-div Z P (⟹-τ step rest) divW | hτH {B = B} {e = e} {a = a} P'' csat Pev refl
  with Hide-reach-div Z P'' rest divW
...   | pre′ , Pr , r , h , dv = (evl (evLabel B e a) ∷ pre′) , Pr , ⟹-ev Pev r , hdrop csat h , dv
Hide-reach-div Z P (⟹-ev step rest) divW with Hide-ev-elim Z P step
... | heV {B = B} {e = e} {a = a} P'' ¬csat Pev with Hide-reach-div Z P'' rest divW
...   | pre′ , Pr , r , h , dv = (evl (evLabel B e a) ∷ pre′) , Pr , ⟹-ev Pev r , hkeep ¬csat h , dv
Hide-reach-div Z P (⟹-ev step rest) divW | he√ {r = r} fpP with rest
...   | ⟹-refl    = ⊥-elim (deadlock-converges divW)
...   | ⟹-τ st _  = ⊥-elim (deadlock-no-τ st)
...   | ⟹-ev st _ = ⊥-elim (deadlock-no-offer st)

Hide-div-elim : (Z : EventSet) (P : PTree E (ExtI E) R) {s : List (Event√ R)}
              → divergences (P ∖ Z) s
              → Σ[ pre ∈ List (Event√ R) ] HideDivOut Z P pre
Hide-div-elim Z P d =
  d .IsDivergence.prefix , Hide-reach-div Z P (d .IsDivergence.reach) (d .IsDivergence.divwit)

Hide-div-intro : (Z : EventSet) (P : PTree E (ExtI E) R)
                 {P′ : PTree E (ExtI E) R} {pre′ s : List (Event√ R)}
               → P ⟹⟨ pre′ ⟩ P′ → HideTr Z pre′ s → Diverges (P′ ∖ Z) → divergences (P ∖ Z) s
Hide-div-intro Z P (⟹-τ Pτ restP) h dv = div-τ-prepend (Hide-τ Z P Pτ) (Hide-div-intro Z _ restP h dv)
Hide-div-intro Z P ⟹-refl hnil dv = empty-div dv
Hide-div-intro Z P (⟹-ev Pev restP) (hkeep ¬csat h) dv =
  div-ev-prepend (Hide-keep Z P ¬csat Pev) (Hide-div-intro Z _ restP h dv)
Hide-div-intro Z P (⟹-ev Pev restP) (hdrop csat h) dv =
  div-τ-prepend (Hide-hidden Z P csat Pev) (Hide-div-intro Z _ restP h dv)
Hide-div-intro Z P (⟹-ev (sRet fpP) ⟹-refl)     h√ dv = ⊥-elim (stable-no-τ (hide-deadlock-stable Z) (dv .Diverges.step))
Hide-div-intro Z P (⟹-ev (sRet fpP) (⟹-τ st _)) h√ dv = ⊥-elim (deadlock-no-τ st)

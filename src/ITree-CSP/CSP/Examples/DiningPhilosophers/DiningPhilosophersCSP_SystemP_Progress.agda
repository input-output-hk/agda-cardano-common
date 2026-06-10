{-# OPTIONS --guardedness #-}
module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Progress where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; suc; zero; _<_; _≤_; s≤s; z≤n; _<?_; s<s⁻¹) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n<1+n; ≤-refl; ≤-trans; <⇒≤; ≤⇒≯;
  m≤n⇒m≤1+n; m<1+n⇒m<n∨m≡n; ≤-total; <-irrefl; ≤∧≢⇒<; ≤-pred; ≤-reflexive)
open import Data.Fin using (Fin; toℕ; fromℕ<; inject₁) ; import Data.Fin as Fin
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective; toℕ<n; toℕ-inject₁)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂; ∃)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using (tabulate; toList)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Function using (case_of_; _∘_)

open import Interaction_Trees
open ITree
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS

import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP            as M
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_States     as St
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Deadlock   as D
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_SysStates  as SysSt

module Prog (m : ℕ) where
  open M.Sys     m
  open St.St     m
  open D.Pf      m
  open SysSt.SysSt m

  import CSP.Definitions.Parallel {E = DP} as ParD
  open ParD DP-AnyTypes-≟ using (_⦀_; ⦀-choice; _∥⇘_¿_⇙_)

  -- Local carrier alias (the `D.Pf` one is `private`).
  DPTree : ∀ {ℓr} → Set ℓr → Set _
  DPTree R = ITree DP (ExtI DP) R

  -- `allPhils = toList (tabulate id)` lists every `Phil`: `g i ∈ toList (tabulate g)`.
  private
    ∈-toList-tabulate : ∀ {ℓa} {A : Set ℓa} {n} (g : Fin n → A) (i : Fin n)
                      → g i ∈ toList (tabulate g)
    ∈-toList-tabulate g Fin.zero    = here refl
    ∈-toList-tabulate g (Fin.suc i) = there (∈-toList-tabulate (g ∘ Fin.suc) i)

  allPhils-complete : ∀ (i : Phil) → i ∈ allPhils
  allPhils-complete i = ∈-toList-tabulate (λ k → k) i

  -- No process sits at `reloop` (⇒ every component is vis-headed).
  NoReloop : Config → Set
  NoReloop (cfgP , cfgF) = (∀ i → cfgP i ≢ reloop) × (∀ j → cfgF j ≢ reloop)

  -- A configuration can make a SYSTEM′ move: either a visible config-event step
  -- (some `_⊳⟨ e ⟩_`, only when no component is at `reloop` — `sil` has priority so a
  -- `reloop` member would block every `ev`-step) or an internal `_⊳τ_` (a reloop loop-back).
  EnabledCfg : (f s : Phil → Fork) → Config → Set₁
  EnabledCfg f s cfg =
      (NoReloop cfg × Σ[ e ∈ Event DP ] Σ[ cfg′ ∈ Config ] (_⊳⟨_⟩_ {f} {s} cfg e cfg′))
    ⊎ (Σ[ cfg′ ∈ Config ] (cfg ⊳τ cfg′))

  -------------------------------------------------------------------------------------
  -- Task 3 (3e′-iv): component fire lemmas `philResid-fire` / `forkResid-fire`.
  --
  -- These are the *construction* analogue of the *inversion* lemmas
  -- `philResid-advance` / `forkResid-advance` (in `…_SysStates`): given a single
  -- component's visible step they build the matching step of the whole `philResid`
  -- (resp. `forkResid`) interleaving.  The clean route is NOT via `D.Pf`'s
  -- `FiresAt` / `⦀list-fires` (those land on the `⦀list` carrier `fireRes`, a
  -- *transported* residual), but directly via the public binary builders
  -- `⦀-step-L` / `⦀-step-R` / `⦀-step-L-ret` over the source-carrier nested-`_⦀_`
  -- fold that `philResid` / `forkResid` literally are.  Induction peels the head
  -- component, exactly mirroring `philResid-advance`'s case split.
  --
  -- REFUSE-PREMISE SHAPE.  A `sVis eqf gja` step out of `philState f s i (cfgP i)`
  -- carries an event `evl (evLabel (proj₁ at) (proj₂ at) a)`, so the supplied
  -- `e : Event DP` is `evLabel (proj₁ at) (proj₂ at) a`; hence
  -- `(Event.A e , Event.e e) ≐ at` and `Event.a e ≐ a` definitionally (Σ-eta).  Each
  -- other component must refuse precisely that `(at , a)` — i.e. be vis-headed with
  -- `fb at a ≡ nothing` — which is exactly what `⦀-step-R` / `⦀-step-L` need from the
  -- stationary side.  This is the per-component element of `D.Pf`'s `AllRefuse`,
  -- keyed off `e`.
  -------------------------------------------------------------------------------------

  -- `pos` refuses event `e` from index `i′`: vis-headed, offering `nothing` on `e`.
  PhilRefuses : (f s : Phil → Fork) → Phil → PhilPos → Event DP → Set₁
  PhilRefuses f s i′ pos e =
    Σ[ fq ∈ ((at : AnyTypes DP) → ContinueType at (Maybe (DPTree ⊥))) ]
      ( (philState f s i′ pos) .force ≡ vis fq
      × fq (Event.A e , Event.e e) (Event.a e) ≡ nothing )

  ForkRefuses : Fork → ForkPos → Event DP → Set₁
  ForkRefuses j′ pos e =
    Σ[ fq ∈ ((at : AnyTypes DP) → ContinueType at (Maybe (DPTree ⊥))) ]
      ( (forkState j′ pos) .force ≡ vis fq
      × fq (Event.A e , Event.e e) (Event.a e) ≡ nothing )

  -- The whole residual of a list of refusing components is either ret-headed (the
  -- empty `Skip`) or vis-headed and itself refuses `e`.  Mirrors `D.Pf.⦀list-refuse`
  -- on the source-carrier `philResid` / `forkResid` fold.
  private
    philResid-refuse : ∀ {f s} (S : List Phil) (cfgP : Phil → PhilPos) {e}
      → All (λ k → PhilRefuses f s k (cfgP k) e) S
      → (Σ[ r ∈ _ ] (philResid {f}{s} S cfgP) .force ≡ ret r)
      ⊎ (Σ[ g ∈ _ ] ((philResid {f}{s} S cfgP) .force ≡ vis g
                     × g (Event.A e , Event.e e) (Event.a e) ≡ nothing))
    -- Generic merge-refusers, parametric in BOTH carriers (so the head `⊥` and the
    -- tail `IProd …` are kept honest).  `g at a ≡ nothing` is proved by reducing the
    -- `_⦀_`-merge under `eqP`/`eqQ`/`bP`(/`bQ`).
    -- `rewrite eqP | eqQ` makes the composite force concrete; matching its `vis`-shape
    -- with `feq` (bound by `… .force in feq`) reflects the merge function, so `rewrite
    -- bP`(/`bQ`) collapses its `case` to `nothing` (mirrors `o⦀ref-vr/vv`).
    -- Force-helpers (composite is vis-headed); proved by `rewrite eqP | eqQ` (these are
    -- about `(P ⦀ Q).force`'s SHAPE, which `rewrite` CAN reduce — it forces the
    -- `with P.force | Q.force` since both become constructor-headed).
    ⦀-fvr : ∀ {ℓs} {S : Set ℓs} {P : DPTree ⊥} {Q : DPTree S} {fP} {s : S}
          → P .force ≡ vis fP → Q .force ≡ ret s
          → Σ[ g ∈ _ ] ((P ⦀ Q) .force ≡ vis g)
    ⦀-fvr eqP eqQ rewrite eqP | eqQ = _ , refl

    ⦀-fvv : ∀ {ℓs} {S : Set ℓs} {P : DPTree ⊥} {Q : DPTree S} {fP fQ}
          → P .force ≡ vis fP → Q .force ≡ vis fQ
          → Σ[ g ∈ _ ] ((P ⦀ Q) .force ≡ vis g)
    ⦀-fvv eqP eqQ rewrite eqP | eqQ = _ , refl

    -- Refuse-offer helpers: `fe` is a genuine ARGUMENT (so `with fe … | refl` is legal),
    -- exactly as in `D.Pf`'s private `o⦀ref-vr` / `o⦀ref-vv`.
    o-refuse-vr : ∀ {ℓs} {S : Set ℓs} {at : AnyTypes DP} {a : proj₁ at}
        {P : DPTree ⊥} {Q : DPTree S} {fP} {s : S} {g}
      → P .force ≡ vis fP → fP at a ≡ nothing → Q .force ≡ ret s
      → (P ⦀ Q) .force ≡ vis g → g at a ≡ nothing
    o-refuse-vr eqP bP eqQ fe rewrite eqP | eqQ with fe
    ... | refl rewrite bP = refl

    o-refuse-vv : ∀ {ℓs} {S : Set ℓs} {at : AnyTypes DP} {a : proj₁ at}
        {P : DPTree ⊥} {Q : DPTree S} {fP fQ} {g}
      → P .force ≡ vis fP → fP at a ≡ nothing
      → Q .force ≡ vis fQ → fQ at a ≡ nothing
      → (P ⦀ Q) .force ≡ vis g → g at a ≡ nothing
    o-refuse-vv eqP bP eqQ bQ fe rewrite eqP | eqQ with fe
    ... | refl rewrite bP | bQ = refl

    ⦀-refuse-vr : ∀ {ℓs} {S : Set ℓs} {at : AnyTypes DP} {a : proj₁ at}
        {P : DPTree ⊥} {Q : DPTree S} {fP} {s : S}
      → P .force ≡ vis fP → fP at a ≡ nothing → Q .force ≡ ret s
      → Σ[ g ∈ _ ] ((P ⦀ Q) .force ≡ vis g × g at a ≡ nothing)
    ⦀-refuse-vr {P = P} {Q = Q} eqP bP eqQ =
      let g , fe = ⦀-fvr {P = P} {Q = Q} eqP eqQ
      in  g , fe , o-refuse-vr eqP bP eqQ fe

    ⦀-refuse-vv : ∀ {ℓs} {S : Set ℓs} {at : AnyTypes DP} {a : proj₁ at}
        {P : DPTree ⊥} {Q : DPTree S} {fP fQ}
      → P .force ≡ vis fP → fP at a ≡ nothing
      → Q .force ≡ vis fQ → fQ at a ≡ nothing
      → Σ[ g ∈ _ ] ((P ⦀ Q) .force ≡ vis g × g at a ≡ nothing)
    ⦀-refuse-vv {P = P} {Q = Q} eqP bP eqQ bQ =
      let g , fe = ⦀-fvv {P = P} {Q = Q} eqP eqQ
      in  g , fe , o-refuse-vv eqP bP eqQ bQ fe

    philResid-refuse [] cfgP _ = inj₁ (tt , refl)
    philResid-refuse {f}{s} (i ∷ S′) cfgP {e} ((fq , eqq , bq) ∷ tl)
      with philResid-refuse {f}{s} S′ cfgP tl
    ... | inj₁ (r , retEq)      = inj₂ (⦀-refuse-vr eqq bq retEq)
    ... | inj₂ (g , eqg , bg)   = inj₂ (⦀-refuse-vv eqq bq eqg bg)

    forkResid-refuse : ∀ (S : List Fork) (cfgF : Fork → ForkPos) {e}
      → All (λ k → ForkRefuses k (cfgF k) e) S
      → (Σ[ r ∈ _ ] (forkResid S cfgF) .force ≡ ret r)
      ⊎ (Σ[ g ∈ _ ] ((forkResid S cfgF) .force ≡ vis g
                     × g (Event.A e , Event.e e) (Event.a e) ≡ nothing))
    forkResid-refuse [] cfgF _ = inj₁ (tt , refl)
    forkResid-refuse (j ∷ S′) cfgF {e} ((fq , eqq , bq) ∷ tl)
      with forkResid-refuse S′ cfgF tl
    ... | inj₁ (r , retEq)      = inj₂ (⦀-refuse-vr eqq bq retEq)
    ... | inj₂ (g , eqg , bg)   = inj₂ (⦀-refuse-vv eqq bq eqg bg)

    -- `P.force ≡ mix _ _` (used to state non-mix-headedness).
    MixHeaded : ∀ {ℓr} {R : Set ℓr} → DPTree R → Set _
    MixHeaded {R = R} P = Σ[ f ∈ _ ] Σ[ Qt ∈ DPTree R ] (P .force ≡ mix f Qt)

    -- `_⦀_` is `mix`-headed only when an operand is: if neither operand is, nor is the
    -- composite.  Per non-mix combo, `rewrite eqP | eqQ` reduces the composite `force`
    -- (the `_⦀_` `with P.force | Q.force` fires), so the supplied `(P⦀Q).force ≡ mix _`
    -- becomes `<non-mix> ≡ mix _`, absurd.
    ⦀-not-mix : ∀ {ℓs} {S : Set ℓs} {P : DPTree ⊥} {Q : DPTree S}
              → ¬ MixHeaded P → ¬ MixHeaded Q → ¬ MixHeaded (P ⦀ Q)
    ⦀-not-mix {P = P} {Q} ¬mP ¬mQ (_ , _ , eqM)
      with P .force in eqP | Q .force in eqQ
    ... | mix _ _  | _        = ¬mP (_ , _ , refl)
    ... | _        | mix _ _  = ¬mQ (_ , _ , refl)
    ... | sil _        | _            = case eqM of λ ()
    ... | ret _        | ret _        = case eqM of λ ()
    ... | ret _        | sil _        = case eqM of λ ()
    ... | ret _        | vis _        = case eqM of λ ()
    ... | ret _        | ndbr _ _ _ _ = case eqM of λ ()
    ... | vis _        | sil _        = case eqM of λ ()
    ... | vis _        | ret _        = case eqM of λ ()
    ... | vis _        | vis _        = case eqM of λ ()
    ... | vis _        | ndbr _ _ _ _ = case eqM of λ ()
    ... | ndbr _ _ _ _ | sil _        = case eqM of λ ()
    ... | ndbr _ _ _ _ | ret _        = case eqM of λ ()
    ... | ndbr _ _ _ _ | vis _        = case eqM of λ ()
    ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eqM of λ ()

    -- Positions are never `mix`-headed (they are vis- or sil-headed).
    philState-not-mix : ∀ {f s} i pos → ¬ MixHeaded (philState f s i pos)
    philState-not-mix {f}{s} i think  (_ , _ , eqM) = case trans (sym (philState-force-think  {f}{s} i)) eqM of λ ()
    philState-not-mix {f}{s} i held1  (_ , _ , eqM) = case trans (sym (philState-force-held1  {f}{s} i)) eqM of λ ()
    philState-not-mix {f}{s} i held2  (_ , _ , eqM) = case trans (sym (philState-force-held2  {f}{s} i)) eqM of λ ()
    philState-not-mix {f}{s} i down1  (_ , _ , eqM) = case trans (sym (philState-force-down1  {f}{s} i)) eqM of λ ()
    philState-not-mix {f}{s} i reloop (_ , _ , eqM) = case trans (sym (philState-force-reloop {f}{s} i)) eqM of λ ()

    forkState-not-mix : ∀ j pos → ¬ MixHeaded (forkState j pos)
    forkState-not-mix j free    (_ , _ , eqM) = case trans (sym (forkState-force-free    j)) eqM of λ ()
    forkState-not-mix j heldOwn (_ , _ , eqM) = case trans (sym (forkState-force-heldOwn j)) eqM of λ ()
    forkState-not-mix j heldNbr (_ , _ , eqM) = case trans (sym (forkResNbr-force        j)) eqM of λ ()
    forkState-not-mix j reloop  (_ , _ , eqM) = case trans (sym (forkState-force-reloop  j)) eqM of λ ()

    -- Hence the residuals are never `mix`-headed (`Skip` is ret-headed; the cons case is
    -- `philState ⦀ philResid`, neither operand `mix` by induction).
    philResid-not-mix : ∀ {f s} (S : List Phil) (cfg : Phil → PhilPos)
                      → ¬ MixHeaded (philResid {f}{s} S cfg)
    philResid-not-mix []       cfg (_ , _ , eqM) = case eqM of λ ()
    philResid-not-mix {f}{s} (i ∷ S′) cfg =
      ⦀-not-mix (philState-not-mix i (cfg i)) (philResid-not-mix S′ cfg)

    forkResid-not-mix : (S : List Fork) (cfg : Fork → ForkPos)
                      → ¬ MixHeaded (forkResid S cfg)
    forkResid-not-mix []       cfg (_ , _ , eqM) = case eqM of λ ()
    forkResid-not-mix (j ∷ S′) cfg =
      ⦀-not-mix (forkState-not-mix j (cfg j)) (forkResid-not-mix S′ cfg)

    -- A visible step out of a non-mix-headed tree is `sVis` (its source is vis-headed).
    step-vis-of-not-mix : ∀ {ℓs} {S : Set ℓs} {e} {Q Q′ : DPTree S}
      → ¬ MixHeaded Q → Q ─[ ev (evl e) ]─► Q′ → Σ[ fQ ∈ _ ] (Q .force ≡ vis fQ)
    step-vis-of-not-mix ¬m (sVis eqQ _)    = _ , eqQ
    step-vis-of-not-mix ¬m (sMixVis eqQ _) = ⊥-elim (¬m (_ , _ , eqQ))

    -- Lift a tail STEP through a refusing (vis-headed) head: `P` refuses `e`, `Q` fires
    -- `e` to `Q′`, so `P ⦀ Q` fires `e` to `P ⦀ Q′`.  Taking the step (not raw offer
    -- facts) keeps the event `evl e` shared, so the head/tail `at`/`a` unify cleanly.
    -- The `sMixVis` case (a `mix`-headed tail) cannot arise here — `philResid`/`forkResid`
    -- are never `mix`-headed (`*Resid-not-mix`) — so the caller supplies `Q .force ≡ vis
    -- fQ`, which refutes it.
    ⦀-lift-R : ∀ {ℓs} {S : Set ℓs} {e}
        {P : DPTree ⊥} {Q Q′ : DPTree S} {fP fQ}
      → P .force ≡ vis fP → fP (Event.A e , Event.e e) (Event.a e) ≡ nothing
      → Q .force ≡ vis fQ
      → Q ─[ ev (evl e) ]─► Q′
      → (P ⦀ Q) ─[ ev (evl e) ]─► (P ⦀ Q′)
    ⦀-lift-R eqP bP eqQv (sVis eqQ bQ)   = ⦀-step-R eqP bP eqQ bQ
    ⦀-lift-R eqP bP eqQv (sMixVis eqQ _) = case trans (sym eqQv) eqQ of λ ()

  -- A philosopher `i` whose position can fire event `e` (advancing
  -- `philState f s i (cfgP i)` to `philState f s i pos′`) makes the whole
  -- `philResid allPhils cfgP` fire `e`, advancing exactly component `i` to `pos′`.
  -- Generalised over a DISTINCT list `S` (so the head-fire case knows the tail is all
  -- `≢ i` and hence refuses), then instantiated at `allPhils`.
  -- Tail congruence: when `cfg`/`cfg′` agree on the entries of `S`, the residuals are
  -- equal.  (`D.Pf`/`SysSt`'s `philResid-cong` is private, so re-derive locally.)
  private
    philResidTail-cong : ∀ {f s} (S : List Phil) {cfg cfg′ : Phil → PhilPos}
                       → All (λ k → cfg k ≡ cfg′ k) S
                       → philResid {f}{s} S cfg ≡ philResid {f}{s} S cfg′
    philResidTail-cong []       _              = refl
    philResidTail-cong {f}{s} (i ∷ S′) (eq ∷ eqs) =
      cong₂ _⦀_ (cong (philState f s i) eq) (philResidTail-cong S′ eqs)

    forkResidTail-cong : (S : List Fork) {cfg cfg′ : Fork → ForkPos}
                       → All (λ k → cfg k ≡ cfg′ k) S
                       → forkResid S cfg ≡ forkResid S cfg′
    forkResidTail-cong []       _              = refl
    forkResidTail-cong (j ∷ S′) (eq ∷ eqs) =
      cong₂ _⦀_ (cong (forkState j) eq) (forkResidTail-cong S′ eqs)

  private
    philResid-fire-S : ∀ {f s} (S : List Phil) → Distinct S
      → (cfgP : Phil → PhilPos) (i : Phil) → ∀ {pos′ e}
      → i ∈ S
      → philState f s i (cfgP i) ─[ ev (evl e) ]─► philState f s i pos′
      → (∀ i′ → i′ ≢ i → PhilRefuses f s i′ (cfgP i′) e)
      → philResid {f}{s} S cfgP ─[ ev (evl e) ]─► philResid {f}{s} S (patch cfgP i pos′)
    philResid-fire-S {f}{s} (i₀ ∷ S′) dist cfgP i {pos′}{e} i∈ (sMixVis eqf _) ref =
      ⊥-elim (philState-not-mix i (cfgP i) (_ , _ , eqf))
    philResid-fire-S {f}{s} (i₀ ∷ S′) dist cfgP i {pos′}{e} i∈ (sVis eqf gja) ref
      with i Fin.≟ i₀
    -- head IS the firing component: it fires, the tail (all ≢ i, by Distinctness) refuses.
    ... | yes refl
        with philResid-refuse {f}{s} S′ cfgP
               (All.map (λ {k} i≢k → ref k (λ eq → i≢k (sym eq))) (proj₁ dist))
    ...   | inj₁ (r , retEq) =
            subst (λ t → (philState f s i (cfgP i) ⦀ philResid {f}{s} S′ cfgP)
                            ─[ ev (evl e) ]─► t)
                  head-tail-eq
                  (⦀-step-L-ret eqf gja retEq)
            where
              head-tail-eq :
                (philState f s i pos′ ⦀ philResid {f}{s} S′ cfgP)
                ≡ (philState f s i pos′ ⦀ philResid {f}{s} S′ (patch cfgP i pos′))
              head-tail-eq = cong (philState f s i pos′ ⦀_)
                (philResidTail-cong S′
                  (All.map (λ {k} i≢k → sym (patch-tail cfgP i pos′ i≢k)) (proj₁ dist)))
    ...   | inj₂ (g , eqg , bg) =
            subst (λ t → (philState f s i (cfgP i) ⦀ philResid {f}{s} S′ cfgP)
                            ─[ ev (evl e) ]─► t)
                  head-tail-eq
                  (⦀-step-L eqf gja eqg bg)
            where
              head-tail-eq :
                (philState f s i pos′ ⦀ philResid {f}{s} S′ cfgP)
                ≡ (philState f s i pos′ ⦀ philResid {f}{s} S′ (patch cfgP i pos′))
              head-tail-eq = cong (philState f s i pos′ ⦀_)
                (philResidTail-cong S′
                  (All.map (λ {k} i≢k → sym (patch-tail cfgP i pos′ i≢k)) (proj₁ dist)))
    -- head is NOT the firing component: it refuses (premise), the tail fires (recursion).
    philResid-fire-S {f}{s} (i₀ ∷ S′) dist cfgP i {pos′}{e} (here refl) step@(sVis eqf gja) ref
        | no i≢i₀ = ⊥-elim (i≢i₀ refl)
    philResid-fire-S {f}{s} (i₀ ∷ S′) dist cfgP i {pos′}{e} (there i∈S′) step@(sVis eqf gja) ref
        | no i≢i₀
        with ref i₀ (λ eq → i≢i₀ (sym eq))
    ...   | (fq , eqq , bq) =
            -- `patch cfgP i pos′ i₀` reduces to `cfgP i₀` (the outer `with i Fin.≟ i₀`
            -- already fixed the `no i≢i₀` branch), so the head is unchanged: no subst.
            ⦀-lift-R eqq bq
              (proj₂ (step-vis-of-not-mix (philResid-not-mix S′ cfgP) tailStep))
              tailStep
            where
              tailStep = philResid-fire-S {f}{s} S′ (proj₂ dist) cfgP i i∈S′ step ref

  philResid-fire : ∀ {f s} (cfgP : Phil → PhilPos) (i : Phil) {pos′ e}
    → philState f s i (cfgP i) ─[ ev (evl e) ]─► philState f s i pos′
    → (∀ i′ → i′ ≢ i → PhilRefuses f s i′ (cfgP i′) e)
    → philResid {f}{s} allPhils cfgP ─[ ev (evl e) ]─► philResid {f}{s} allPhils (patch cfgP i pos′)
  philResid-fire cfgP i = philResid-fire-S allPhils allPhils-distinct cfgP i (allPhils-complete i)

  private
    forkResid-fire-S : ∀ (S : List Fork) → Distinct S
      → (cfgF : Fork → ForkPos) (j : Fork) → ∀ {fpos′ e}
      → j ∈ S
      → forkState j (cfgF j) ─[ ev (evl e) ]─► forkState j fpos′
      → (∀ j′ → j′ ≢ j → ForkRefuses j′ (cfgF j′) e)
      → forkResid S cfgF ─[ ev (evl e) ]─► forkResid S (patch cfgF j fpos′)
    forkResid-fire-S (j₀ ∷ S′) dist cfgF j {fpos′}{e} j∈ (sMixVis eqf _) ref =
      ⊥-elim (forkState-not-mix j (cfgF j) (_ , _ , eqf))
    forkResid-fire-S (j₀ ∷ S′) dist cfgF j {fpos′}{e} j∈ (sVis eqf gja) ref
      with j Fin.≟ j₀
    ... | yes refl
        with forkResid-refuse S′ cfgF
               (All.map (λ {k} j≢k → ref k (λ eq → j≢k (sym eq))) (proj₁ dist))
    ...   | inj₁ (r , retEq) =
            subst (λ t → (forkState j (cfgF j) ⦀ forkResid S′ cfgF)
                            ─[ ev (evl e) ]─► t)
                  head-tail-eq
                  (⦀-step-L-ret eqf gja retEq)
            where
              head-tail-eq :
                (forkState j fpos′ ⦀ forkResid S′ cfgF)
                ≡ (forkState j fpos′ ⦀ forkResid S′ (patch cfgF j fpos′))
              head-tail-eq = cong (forkState j fpos′ ⦀_)
                (forkResidTail-cong S′
                  (All.map (λ {k} j≢k → sym (patch-tail cfgF j fpos′ j≢k)) (proj₁ dist)))
    ...   | inj₂ (g , eqg , bg) =
            subst (λ t → (forkState j (cfgF j) ⦀ forkResid S′ cfgF)
                            ─[ ev (evl e) ]─► t)
                  head-tail-eq
                  (⦀-step-L eqf gja eqg bg)
            where
              head-tail-eq :
                (forkState j fpos′ ⦀ forkResid S′ cfgF)
                ≡ (forkState j fpos′ ⦀ forkResid S′ (patch cfgF j fpos′))
              head-tail-eq = cong (forkState j fpos′ ⦀_)
                (forkResidTail-cong S′
                  (All.map (λ {k} j≢k → sym (patch-tail cfgF j fpos′ j≢k)) (proj₁ dist)))
    forkResid-fire-S (j₀ ∷ S′) dist cfgF j {fpos′}{e} (here refl) step@(sVis eqf gja) ref
        | no j≢j₀ = ⊥-elim (j≢j₀ refl)
    forkResid-fire-S (j₀ ∷ S′) dist cfgF j {fpos′}{e} (there j∈S′) step@(sVis eqf gja) ref
        | no j≢j₀
        with ref j₀ (λ eq → j≢j₀ (sym eq))
    ...   | (fq , eqq , bq) =
            ⦀-lift-R eqq bq
              (proj₂ (step-vis-of-not-mix (forkResid-not-mix S′ cfgF) tailStep))
              tailStep
            where
              tailStep = forkResid-fire-S S′ (proj₂ dist) cfgF j j∈S′ step ref

  forkResid-fire : ∀ (cfgF : Fork → ForkPos) (j : Fork) {fpos′ e}
    → forkState j (cfgF j) ─[ ev (evl e) ]─► forkState j fpos′
    → (∀ j′ → j′ ≢ j → ForkRefuses j′ (cfgF j′) e)
    → forkResid allPhils cfgF ─[ ev (evl e) ]─► forkResid allPhils (patch cfgF j fpos′)
  forkResid-fire cfgF j = forkResid-fire-S allPhils allPhils-distinct cfgF j (allPhils-complete j)

  -------------------------------------------------------------------------------------
  -- Task 4 (3e′-iv): `⊳-ev-complete` / `reloop⇒τ` / `enabled⇒¬stuck`.
  --
  -- This is the *completeness* direction (the converse of `⊳-ev-sound`/`⊳τ-sound` in
  -- `…_SysStates`): a config-step `cfg ⊳⟨ e ⟩ cfg′` (resp. a reloop) is realised by a
  -- genuine `sysState` LTS-step.  The visible cases compose the per-component fire lemmas
  -- `philResid-fire` / `forkResid-fire` through the synchroniser `∥⇘-sync-step′`; the τ
  -- cases lift a sil-headed residual through the parallel.  The `⊳pd-*` cases need the
  -- `ValidCfg` invariant to pin the *fork*'s position (the philosopher's `held2`/`down1`
  -- only tells us the fork it holds is `heldOwn`/`heldNbr`, via `ForkConsistent`).
  -------------------------------------------------------------------------------------

  -- Per-position refuse witnesses for a `picks`/`putsdown` event at indices `(ei , ej)`.
  -- A vis-headed position whose offer is `nothing` at the queried event refuses it; the
  -- index mismatch (`i′ ≢ ei`, resp. `j′ ≢ ej`) discharges the refuse lemma's premise.
  -- `reloop` is sil-headed (not vis): excluded via the supplied `pos ≢ reloop`.
  private
    phil-refuses-pk : ∀ {f s} i′ (pos : PhilPos) (ei ej : Fork)
      → pos ≢ reloop → i′ ≢ ei
      → PhilRefuses f s i′ pos (evLabel _ (picks ei ej) tt)
    phil-refuses-pk {f}{s} i′ think  ei ej _   i′≢ =
      _ , philState-force-think {f}{s} i′
        , phil-think-refuses-picks {f}{s} i′ ei ej (λ { (eq , _) → i′≢ eq })
    phil-refuses-pk {f}{s} i′ held1  ei ej _   i′≢ =
      _ , philState-force-held1 {f}{s} i′
        , phil-held1-refuses-picks {f}{s} i′ ei ej (λ { (eq , _) → i′≢ eq })
    phil-refuses-pk {f}{s} i′ held2  ei ej _   _   =
      _ , philState-force-held2 {f}{s} i′ , phil-held2-refuses-pk {f}{s} i′ ei ej
    phil-refuses-pk {f}{s} i′ down1  ei ej _   _   =
      _ , philState-force-down1 {f}{s} i′ , phil-down1-refuses-pk {f}{s} i′ ei ej
    phil-refuses-pk {f}{s} i′ reloop ei ej ≢rl _   = ⊥-elim (≢rl refl)

    phil-refuses-pd : ∀ {f s} i′ (pos : PhilPos) (ei ej : Fork)
      → pos ≢ reloop → i′ ≢ ei
      → PhilRefuses f s i′ pos (evLabel _ (putsdown ei ej) tt)
    phil-refuses-pd {f}{s} i′ think  ei ej _   _   =
      _ , philState-force-think {f}{s} i′ , phil-think-refuses-pd {f}{s} i′ ei ej
    phil-refuses-pd {f}{s} i′ held1  ei ej _   _   =
      _ , philState-force-held1 {f}{s} i′ , phil-held1-refuses-pd {f}{s} i′ ei ej
    phil-refuses-pd {f}{s} i′ held2  ei ej _   i′≢ =
      _ , philState-force-held2 {f}{s} i′
        , phil-held2-refuses-pd {f}{s} i′ ei ej (λ { (eq , _) → i′≢ eq })
    phil-refuses-pd {f}{s} i′ down1  ei ej _   i′≢ =
      _ , philState-force-down1 {f}{s} i′
        , phil-down1-refuses-pd {f}{s} i′ ei ej (λ { (eq , _) → i′≢ eq })
    phil-refuses-pd {f}{s} i′ reloop ei ej ≢rl _   = ⊥-elim (≢rl refl)

    fork-refuses-pk : ∀ j′ (pos : ForkPos) (ei ej : Fork)
      → pos ≢ reloop → j′ ≢ ej
      → ForkRefuses j′ pos (evLabel _ (picks ei ej) tt)
    fork-refuses-pk j′ free    ei ej _   j′≢ =
      _ , forkState-force-free j′
        , fork-free-refuses-pk j′ ei ej (λ { (_ , eq) → j′≢ eq })
                                        (λ { (_ , eq) → j′≢ eq })
    fork-refuses-pk j′ heldOwn ei ej _   _   =
      _ , forkState-force-heldOwn j′ , fork-heldOwn-refuses-pk j′ ei ej
    fork-refuses-pk j′ heldNbr ei ej _   _   =
      _ , forkResNbr-force j′ , fork-heldNbr-refuses-pk j′ ei ej
    fork-refuses-pk j′ reloop  ei ej ≢rl _   = ⊥-elim (≢rl refl)

    fork-refuses-pd : ∀ j′ (pos : ForkPos) (ei ej : Fork)
      → pos ≢ reloop → j′ ≢ ej
      → ForkRefuses j′ pos (evLabel _ (putsdown ei ej) tt)
    fork-refuses-pd j′ free    ei ej _   _   =
      _ , forkState-force-free j′ , fork-free-refuses-pd j′ ei ej
    fork-refuses-pd j′ heldOwn ei ej _   j′≢ =
      _ , forkState-force-heldOwn j′
        , fork-heldOwn-refuses-pd j′ ei ej (λ { (_ , eq) → j′≢ eq })
    fork-refuses-pd j′ heldNbr ei ej _   j′≢ =
      _ , forkResNbr-force j′
        , fork-heldNbr-refuses-pd j′ ei ej (λ { (_ , eq) → j′≢ eq })
    fork-refuses-pd j′ reloop  ei ej ≢rl _   = ⊥-elim (≢rl refl)

  -- Local re-derivation of the ring round trip `⊕⊖′` (`SysSt`'s are private).
  private
    toℕ-⊖1-zero′ : toℕ (Fin.zero {n = suc m} ⊖1) ≡ suc m
    toℕ-⊖1-zero′ = toℕ-fromℕ< (n<1+n (suc m))

    ⊕⊖′ : ∀ (i : Fork) → (i ⊕1) ⊖1 ≡ i
    ⊕⊖′ i with suc (toℕ i) <? n
    ... | no ¬p = toℕ-injective (trans toℕ-⊖1-zero′ (sym (≮⇒max ¬p)))
      where
        ≮⇒max : ¬ (suc (toℕ i) < n) → toℕ i ≡ suc m
        ≮⇒max np with toℕ i ≟ℕ suc m
        ... | yes e  = e
        ... | no  ne = ⊥-elim (np (s≤s (≤∧≢⇒< (≤-pred (toℕ<n i)) ne)))
    ... | yes p =
          toℕ-injective (trans (toℕ-inject₁ (fromℕ< (s<s⁻¹ p))) (toℕ-fromℕ< (s<s⁻¹ p)))

  -- `heldBy` witnesses read off a known philosopher position (the `⊳pd-*` sources).
  private
    heldBy-held2-si : ∀ {f s} (cfgP : Phil → PhilPos) i
                    → cfgP i ≡ held2 → heldBy {f}{s} cfgP i (s i)
    heldBy-held2-si cfgP i eq with cfgP i | eq
    ... | held2 | refl = inj₂ refl

    heldBy-down1-fi : ∀ {f s} (cfgP : Phil → PhilPos) i
                    → cfgP i ≡ down1 → heldBy {f}{s} cfgP i (f i)
    heldBy-down1-fi cfgP i eq with cfgP i | eq
    ... | down1 | refl = refl

  -- Compose the two component fires into one synchronised SYSTEM′ step.
  private
    mk-step : ∀ {f s} {cfgP : Phil → PhilPos} {cfgF : Fork → ForkPos}
        {i : Phil} {j : Fork} {pos′ fpos′ e}
      → philState f s i (cfgP i) ─[ ev (evl e) ]─► philState f s i pos′
      → forkState j (cfgF j) ─[ ev (evl e) ]─► forkState j fpos′
      → (∀ i′ → i′ ≢ i → PhilRefuses f s i′ (cfgP i′) e)
      → (∀ j′ → j′ ≢ j → ForkRefuses j′ (cfgF j′) e)
      → sysState f s (cfgP , cfgF)
          ─[ ev (evl e) ]─►
        sysState f s (patch cfgP i pos′ , patch cfgF j fpos′)
    mk-step {f}{s}{cfgP}{cfgF}{i}{j} pStep fStep pRef fRef =
      let pFire = philResid-fire {f}{s} cfgP i pStep pRef
          fFire = forkResid-fire cfgF j fStep fRef
          _ , eqgP = step-vis-of-not-mix (philResid-not-mix {f}{s} allPhils cfgP) pFire
          _ , eqgQ = step-vis-of-not-mix (forkResid-not-mix allPhils cfgF) fFire
      in ∥⇘-sync-step′ eqgP eqgQ pFire fFire

  -- A config-step is realised by a genuine `sysState` LTS step.  Needs `NoReloop` so the
  -- *other* components are vis-headed (a `reloop` member is sil-headed and would refuse no
  -- `ev`), and `ValidCfg` so the `⊳pd-*` cases can pin the fork's `heldOwn`/`heldNbr`.
  ⊳-ev-complete : ∀ {f s} {cfg e cfg′}
    → ValidCfg {f}{s} cfg → NoReloop cfg
    → (_⊳⟨_⟩_ {f}{s} cfg e cfg′)
    → sysState f s cfg ─[ ev (evl e) ]─► sysState f s cfg′
  -- ── pk1-own: think → held1, fork (f i = i) free → heldOwn, event `picks i (f i)`.
  ⊳-ev-complete {f}{s} {(cfgP , cfgF)} V (nrP , nrF) (⊳pk1-own {i = i} pe fi≡i freeF) =
    mk-step {f}{s} {i = i} {j = f i}
      (subst (λ p → philState f s i p ─[ ev (evl (evLabel _ (picks i (f i)) tt)) ]─► philState f s i held1)
             (sym pe) (phil-step-think {f}{s} i))
      (subst (λ q → forkState (f i) q ─[ ev (evl (evLabel _ (picks i (f i)) tt)) ]─► forkState (f i) heldOwn) (sym freeF)
        (subst (λ x → forkState (f i) free ─[ ev (evl (evLabel _ (picks x (f i)) tt)) ]─► forkState (f i) heldOwn)
               fi≡i (fork-step-own (f i))))
      (λ i′ i′≢i → phil-refuses-pk {f}{s} i′ (cfgP i′) i (f i) (nrP i′) i′≢i)
      (λ j′ j′≢fi → fork-refuses-pk j′ (cfgF j′) i (f i) (nrF j′) j′≢fi)
  -- ── pk1-nbr: think → held1, fork (f i = i ⊕1) free → heldNbr, event `picks i (f i)`.
  ⊳-ev-complete {f}{s} {(cfgP , cfgF)} V (nrP , nrF) (⊳pk1-nbr {i = i} pe fi≡i⊕1 freeF) =
    mk-step {f}{s} {i = i} {j = f i}
      (subst (λ p → philState f s i p ─[ ev (evl (evLabel _ (picks i (f i)) tt)) ]─► philState f s i held1)
             (sym pe) (phil-step-think {f}{s} i))
      (subst (λ q → forkState (f i) q ─[ ev (evl (evLabel _ (picks i (f i)) tt)) ]─► forkState (f i) heldNbr) (sym freeF)
        (subst (λ x → forkState (f i) free ─[ ev (evl (evLabel _ (picks x (f i)) tt)) ]─► forkState (f i) heldNbr)
               (trans (cong _⊖1 fi≡i⊕1) (⊕⊖′ i)) (fork-step-nbr (f i))))
      (λ i′ i′≢i → phil-refuses-pk {f}{s} i′ (cfgP i′) i (f i) (nrP i′) i′≢i)
      (λ j′ j′≢fi → fork-refuses-pk j′ (cfgF j′) i (f i) (nrF j′) j′≢fi)
  -- ── pk2-own: held1 → held2, fork (s i = i) free → heldOwn, event `picks i (s i)`.
  ⊳-ev-complete {f}{s} {(cfgP , cfgF)} V (nrP , nrF) (⊳pk2-own {i = i} pe si≡i freeF) =
    mk-step {f}{s} {i = i} {j = s i}
      (subst (λ p → philState f s i p ─[ ev (evl (evLabel _ (picks i (s i)) tt)) ]─► philState f s i held2)
             (sym pe) (phil-step-held1 {f}{s} i))
      (subst (λ q → forkState (s i) q ─[ ev (evl (evLabel _ (picks i (s i)) tt)) ]─► forkState (s i) heldOwn) (sym freeF)
        (subst (λ x → forkState (s i) free ─[ ev (evl (evLabel _ (picks x (s i)) tt)) ]─► forkState (s i) heldOwn)
               si≡i (fork-step-own (s i))))
      (λ i′ i′≢i → phil-refuses-pk {f}{s} i′ (cfgP i′) i (s i) (nrP i′) i′≢i)
      (λ j′ j′≢si → fork-refuses-pk j′ (cfgF j′) i (s i) (nrF j′) j′≢si)
  -- ── pk2-nbr: held1 → held2, fork (s i = i ⊕1) free → heldNbr, event `picks i (s i)`.
  ⊳-ev-complete {f}{s} {(cfgP , cfgF)} V (nrP , nrF) (⊳pk2-nbr {i = i} pe si≡i⊕1 freeF) =
    mk-step {f}{s} {i = i} {j = s i}
      (subst (λ p → philState f s i p ─[ ev (evl (evLabel _ (picks i (s i)) tt)) ]─► philState f s i held2)
             (sym pe) (phil-step-held1 {f}{s} i))
      (subst (λ q → forkState (s i) q ─[ ev (evl (evLabel _ (picks i (s i)) tt)) ]─► forkState (s i) heldNbr) (sym freeF)
        (subst (λ x → forkState (s i) free ─[ ev (evl (evLabel _ (picks x (s i)) tt)) ]─► forkState (s i) heldNbr)
               (trans (cong _⊖1 si≡i⊕1) (⊕⊖′ i)) (fork-step-nbr (s i))))
      (λ i′ i′≢i → phil-refuses-pk {f}{s} i′ (cfgP i′) i (s i) (nrP i′) i′≢i)
      (λ j′ j′≢si → fork-refuses-pk j′ (cfgF j′) i (s i) (nrF j′) j′≢si)
  -- ── pd-s: held2 → down1, fork (s i) → reloop, event `putsdown i (s i)`.  Fork's old
  -- position pinned by `ValidCfg`: `heldBy cfgP i (s i)` (= inj₂ refl) ⇒ `ForkConsistent`'s
  -- third conjunct gives `(i ≡ s i ∧ heldOwn) ⊎ (i ≡ (s i)⊖1 ∧ heldNbr)`.
  ⊳-ev-complete {f}{s} {(cfgP , cfgF)} V (nrP , nrF) (⊳pd-s {i = i} pe) =
    case proj₂ (proj₂ (V (s i))) i (heldBy-held2-si {f}{s} cfgP i pe) of λ
       { (inj₁ (i≡si , own)) →
           mk-step {f}{s} {i = i} {j = s i}
             (subst (λ p → philState f s i p ─[ ev (evl (evLabel _ (putsdown i (s i)) tt)) ]─► philState f s i down1)
                    (sym pe) (phil-step-held2 {f}{s} i))
             (subst (λ q → forkState (s i) q ─[ ev (evl (evLabel _ (putsdown i (s i)) tt)) ]─► forkState (s i) reloop) (sym own)
               (subst (λ x → forkState (s i) heldOwn ─[ ev (evl (evLabel _ (putsdown x (s i)) tt)) ]─► forkState (s i) reloop)
                      (sym i≡si) (fork-step-heldOwn (s i))))
             (λ i′ i′≢i → phil-refuses-pd {f}{s} i′ (cfgP i′) i (s i) (nrP i′) i′≢i)
             (λ j′ j′≢si → fork-refuses-pd j′ (cfgF j′) i (s i) (nrF j′) j′≢si)
       ; (inj₂ (i≡si⊖1 , nbr)) →
           mk-step {f}{s} {i = i} {j = s i}
             (subst (λ p → philState f s i p ─[ ev (evl (evLabel _ (putsdown i (s i)) tt)) ]─► philState f s i down1)
                    (sym pe) (phil-step-held2 {f}{s} i))
             (subst (λ q → forkState (s i) q ─[ ev (evl (evLabel _ (putsdown i (s i)) tt)) ]─► forkState (s i) reloop) (sym nbr)
               (subst (λ x → forkState (s i) heldNbr ─[ ev (evl (evLabel _ (putsdown x (s i)) tt)) ]─► forkState (s i) reloop)
                      (sym i≡si⊖1) (fork-step-heldNbr (s i))))
             (λ i′ i′≢i → phil-refuses-pd {f}{s} i′ (cfgP i′) i (s i) (nrP i′) i′≢i)
             (λ j′ j′≢si → fork-refuses-pd j′ (cfgF j′) i (s i) (nrF j′) j′≢si)
       }
  -- ── pd-f: down1 → reloop, fork (f i) → reloop, event `putsdown i (f i)`.  Fork pinned by
  -- `ValidCfg`: `heldBy cfgP i (f i)` (= refl) ⇒ third conjunct as above, holder `i` at `f i`.
  ⊳-ev-complete {f}{s} {(cfgP , cfgF)} V (nrP , nrF) (⊳pd-f {i = i} pe) =
    case proj₂ (proj₂ (V (f i))) i (heldBy-down1-fi {f}{s} cfgP i pe) of λ
       { (inj₁ (i≡fi , own)) →
           mk-step {f}{s} {i = i} {j = f i}
             (subst (λ p → philState f s i p ─[ ev (evl (evLabel _ (putsdown i (f i)) tt)) ]─► philState f s i reloop)
                    (sym pe) (phil-step-down1 {f}{s} i))
             (subst (λ q → forkState (f i) q ─[ ev (evl (evLabel _ (putsdown i (f i)) tt)) ]─► forkState (f i) reloop) (sym own)
               (subst (λ x → forkState (f i) heldOwn ─[ ev (evl (evLabel _ (putsdown x (f i)) tt)) ]─► forkState (f i) reloop)
                      (sym i≡fi) (fork-step-heldOwn (f i))))
             (λ i′ i′≢i → phil-refuses-pd {f}{s} i′ (cfgP i′) i (f i) (nrP i′) i′≢i)
             (λ j′ j′≢fi → fork-refuses-pd j′ (cfgF j′) i (f i) (nrF j′) j′≢fi)
       ; (inj₂ (i≡fi⊖1 , nbr)) →
           mk-step {f}{s} {i = i} {j = f i}
             (subst (λ p → philState f s i p ─[ ev (evl (evLabel _ (putsdown i (f i)) tt)) ]─► philState f s i reloop)
                    (sym pe) (phil-step-down1 {f}{s} i))
             (subst (λ q → forkState (f i) q ─[ ev (evl (evLabel _ (putsdown i (f i)) tt)) ]─► forkState (f i) reloop) (sym nbr)
               (subst (λ x → forkState (f i) heldNbr ─[ ev (evl (evLabel _ (putsdown x (f i)) tt)) ]─► forkState (f i) reloop)
                      (sym i≡fi⊖1) (fork-step-heldNbr (f i))))
             (λ i′ i′≢i → phil-refuses-pd {f}{s} i′ (cfgP i′) i (f i) (nrP i′) i′≢i)
             (λ j′ j′≢fi → fork-refuses-pd j′ (cfgF j′) i (f i) (nrF j′) j′≢fi)
       }

  -------------------------------------------------------------------------------------
  -- `reloop⇒τ`: a `reloop` member makes the whole `sysState` sil-headed (so it offers a τ).
  -- `_⦀_` (and `_∥⇘_`) give the `sil` clause priority on the LEFT, then on the RIGHT — so a
  -- sil-headed component anywhere in either residual forces the whole tree sil-headed.
  -------------------------------------------------------------------------------------

  private
    -- `_⦀_` is sil-headed when an operand is (left clause has priority; right clause needs
    -- the left non-sil, supplied by a vis head).
    ⦀-sil-L : ∀ {ℓs} {S : Set ℓs} {P P′ : DPTree ⊥} {Q : DPTree S}
            → P .force ≡ sil P′ → (P ⦀ Q) .force ≡ sil (P′ ⦀ Q)
    ⦀-sil-L eqP rewrite eqP = refl

    ⦀-sil-R : ∀ {ℓs} {S : Set ℓs} {P : DPTree ⊥} {Q Q′ : DPTree S} {fP}
            → P .force ≡ vis fP → Q .force ≡ sil Q′ → (P ⦀ Q) .force ≡ sil (P ⦀ Q′)
    ⦀-sil-R eqP eqQ rewrite eqP | eqQ = refl

    -- Head classification of a single position (vis for the progress positions, sil for
    -- `reloop`).  Cases on `pos`; applied at the stuck `cfgP i₀` it stays a call, so it
    -- avoids the goal-abstraction a `with cfgP i₀` would force.
    phil-vis-or-sil : ∀ {f s} i (pos : PhilPos)
                    → (Σ[ g  ∈ _ ] ((philState f s i pos) .force ≡ vis g))
                    ⊎ (Σ[ t′ ∈ _ ] ((philState f s i pos) .force ≡ sil t′))
    phil-vis-or-sil {f}{s} i think  = inj₁ (_ , philState-force-think  {f}{s} i)
    phil-vis-or-sil {f}{s} i held1  = inj₁ (_ , philState-force-held1  {f}{s} i)
    phil-vis-or-sil {f}{s} i held2  = inj₁ (_ , philState-force-held2  {f}{s} i)
    phil-vis-or-sil {f}{s} i down1  = inj₁ (_ , philState-force-down1  {f}{s} i)
    phil-vis-or-sil {f}{s} i reloop = inj₂ (_ , philState-force-reloop {f}{s} i)

    fork-vis-or-sil : ∀ j (pos : ForkPos)
                    → (Σ[ g  ∈ _ ] ((forkState j pos) .force ≡ vis g))
                    ⊎ (Σ[ t′ ∈ _ ] ((forkState j pos) .force ≡ sil t′))
    fork-vis-or-sil j free    = inj₁ (_ , forkState-force-free    j)
    fork-vis-or-sil j heldOwn = inj₁ (_ , forkState-force-heldOwn j)
    fork-vis-or-sil j heldNbr = inj₁ (_ , forkResNbr-force        j)
    fork-vis-or-sil j reloop  = inj₂ (_ , forkState-force-reloop  j)

    -- A reloop philosopher in the list ⇒ the `philResid` fold is sil-headed.  The head's
    -- own sil/vis classification comes from `phil-vis-or-sil (cfgP i₀)`: if the head is sil
    -- the fold is (left clause), else recurse on the tail (right clause).  (Membership only
    -- guarantees the reloop is somewhere; the head needn't be it.)
    philResid-sil : ∀ {f s} (S : List Phil) (cfgP : Phil → PhilPos) {i}
                  → i ∈ S → cfgP i ≡ reloop
                  → Σ[ t′ ∈ _ ] ((philResid {f}{s} S cfgP) .force ≡ sil t′)
    philResid-sil {f}{s} (i₀ ∷ S′) cfgP (here refl) re =
      _ , ⦀-sil-L (subst (λ p → (philState f s i₀ p) .force ≡ sil (philState f s i₀ think))
                         (sym re) (philState-force-reloop {f}{s} i₀))
    philResid-sil {f}{s} (i₀ ∷ S′) cfgP {i} (there i∈) re
      with phil-vis-or-sil {f}{s} i₀ (cfgP i₀)
    ... | inj₂ (_ , hsil) = _ , ⦀-sil-L hsil
    ... | inj₁ (_ , hv)   = let _ , eqsil = philResid-sil {f}{s} S′ cfgP i∈ re
                            in _ , ⦀-sil-R hv eqsil

    forkResid-sil : ∀ (S : List Fork) (cfgF : Fork → ForkPos) {j}
                  → j ∈ S → cfgF j ≡ reloop
                  → Σ[ t′ ∈ _ ] ((forkResid S cfgF) .force ≡ sil t′)
    forkResid-sil (j₀ ∷ S′) cfgF (here refl) re =
      _ , ⦀-sil-L (subst (λ p → (forkState j₀ p) .force ≡ sil (forkState j₀ free))
                         (sym re) (forkState-force-reloop j₀))
    forkResid-sil (j₀ ∷ S′) cfgF {j} (there j∈) re
      with fork-vis-or-sil j₀ (cfgF j₀)
    ... | inj₂ (_ , hsil) = _ , ⦀-sil-L hsil
    ... | inj₁ (_ , hv)   = let _ , eqsil = forkResid-sil S′ cfgF j∈ re
                            in _ , ⦀-sil-R hv eqsil

    -- The synchronised parallel inherits sil-headedness from EITHER operand (left clause
    -- has priority; the right clause needs the left non-sil, covered by case-splitting it).
    ∥⇘-sil-L : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} {P P′ : DPTree R} {Q : DPTree S}
             → P .force ≡ sil P′
             → Σ[ t′ ∈ _ ] ((P ∥⇘ syncAll ¿ syncAll-dec ⇙ Q) .force ≡ sil t′)
    ∥⇘-sil-L eqP rewrite eqP = _ , refl

    -- A vis-headed P with a sil-headed Q ⇒ composite sil via the right `_ | sil Q′` clause.
    ∥⇘-sil-R : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} {P : DPTree R} {Q Q′ : DPTree S} {fP}
             → P .force ≡ vis fP → Q .force ≡ sil Q′
             → Σ[ t′ ∈ _ ] ((P ∥⇘ syncAll ¿ syncAll-dec ⇙ Q) .force ≡ sil t′)
    ∥⇘-sil-R eqP eqQ rewrite eqP | eqQ = _ , refl

    -- Classify a `philResid` fold's head: sil (a reloop member) / vis / ret (empty `Skip`).
    -- The head's own sil/vis classification is read off `phil-vis-or-sil (cfgP i₀)` (no
    -- `with cfgP i₀`, which would wrongly abstract the goal's `cfgP i₀` to a literal).
    philResid-TVR : ∀ {f s} (S : List Phil) (cfgP : Phil → PhilPos)
      → (Σ[ t′ ∈ _ ] (philResid {f}{s} S cfgP) .force ≡ sil t′)
      ⊎ (Σ[ g  ∈ _ ] (philResid {f}{s} S cfgP) .force ≡ vis g)
      ⊎ (Σ[ r  ∈ _ ] (philResid {f}{s} S cfgP) .force ≡ ret r)
    philResid-TVR []       cfgP = inj₂ (inj₂ (tt , refl))
    philResid-TVR {f}{s} (i₀ ∷ S′) cfgP
      with phil-vis-or-sil {f}{s} i₀ (cfgP i₀) | philResid-TVR {f}{s} S′ cfgP
    ... | inj₂ (_ , hsil) | _                      = inj₁ (_ , ⦀-sil-L hsil)
    ... | inj₁ (_ , hv)   | inj₁ (_ , tsil)        = inj₁ (_ , ⦀-sil-R hv tsil)
    ... | inj₁ (_ , hv)   | inj₂ (inj₁ (_ , tvis)) = inj₂ (inj₁ (⦀-fvv hv tvis))
    ... | inj₁ (_ , hv)   | inj₂ (inj₂ (_ , tret)) = inj₂ (inj₁ (⦀-fvr hv tret))

  reloop⇒τ : ∀ {f s} {cfg}
    → ((Σ[ i ∈ Phil ] proj₁ cfg i ≡ reloop) ⊎ (Σ[ j ∈ Fork ] proj₂ cfg j ≡ reloop))
    → Σ[ t′ ∈ ITree DP (ExtI DP) _ ] (sysState f s cfg ─[ τ ]─► t′)
  reloop⇒τ {f}{s} {(cfgP , cfgF)} (inj₁ (i , re)) =
    let _ , eqsil = philResid-sil {f}{s} allPhils cfgP (allPhils-complete i) re
        _ , eq∥   = ∥⇘-sil-L {Q = forkResid allPhils cfgF} eqsil
    in _ , sSil eq∥
  reloop⇒τ {f}{s} {(cfgP , cfgF)} (inj₂ (j , re))
    with forkResid-sil allPhils cfgF (allPhils-complete j) re | philResid-TVR {f}{s} allPhils cfgP
  ... | _ , eqsilF | inj₁ (_ , eqsilP)        = _ , sSil (proj₂ (∥⇘-sil-L {Q = forkResid allPhils cfgF} eqsilP))
  ... | _ , eqsilF | inj₂ (inj₁ (_ , eqvisP)) = _ , sSil (proj₂ (∥⇘-sil-R eqvisP eqsilF))
  ... | _ , eqsilF | inj₂ (inj₂ (_ , eqretP)) with allPhils-cons
  ...   | i₀ , rest , refl = ⊥-elim (philResid-not-ret {f}{s} i₀ rest cfgP eqretP)

  -------------------------------------------------------------------------------------
  -- `enabled⇒¬stuck`: an `EnabledCfg` configuration is never `IsStuck` — its enabling
  -- witness (a visible config-step or a reloop τ) is realised by an LTS step out of
  -- `sysState`, which the `IsStuck` hypothesis then refutes.
  -------------------------------------------------------------------------------------
  enabled⇒¬stuck : ∀ {f s cfg}
    → ValidCfg {f}{s} cfg → EnabledCfg f s cfg → ¬ IsStuck (sysState f s cfg)
  enabled⇒¬stuck V (inj₁ (nr , e , cfg′ , st)) stuck = stuck (⊳-ev-complete V nr st)
  enabled⇒¬stuck V (inj₂ (cfg′ , ⊳τ-phil {i = i} re)) stuck =
    stuck (proj₂ (reloop⇒τ (inj₁ (i , re))))
  enabled⇒¬stuck V (inj₂ (cfg′ , ⊳τ-fork {j = j} re)) stuck =
    stuck (proj₂ (reloop⇒τ (inj₂ (j , re))))

  -------------------------------------------------------------------------------------
  -- Task 5 (3e′-iv), Layer B: per-philosopher "top fork" + fork-position helper.
  --
  -- `topFork` identifies, for any holder `P`, a single witness fork `x` dominating (by
  -- the abstract `rank`) every fork `P` holds.  A `held1`/`down1` holder holds only `f P`
  -- (the unique held fork); a `held2` holder holds `f P` and `s P`, and under the
  -- ordering hypothesis `ra P : rank (f P) < rank (s P)` the larger is `s P`.  We carry
  -- the held proof and the domination proof together (`TopOf`).  This generalises the
  -- relational `topFork` (DiningPhilosophers.lagda.md §8.1) from `toℕ` to an abstract
  -- `rank`, and from `_∈heldBy_` to `heldBy`.
  --
  -- `not-held⇒free` is the fork-position helper: a fork `j` that is not `reloop` and that
  -- no philosopher holds must be `free`.  The non-`free`/non-`reloop` cases (`heldOwn` /
  -- `heldNbr`) are refuted by `ValidCfg`'s first/second `ForkConsistent` conjuncts, which
  -- would force a holder (`j` itself, resp. `j ⊖1`) contradicting the "holds nothing"
  -- premise.
  -------------------------------------------------------------------------------------

  -- "holds nothing" refutations off `heldBy`'s `think`/`reloop` ⊥-clauses (the SysSt ones
  -- are private; these `rewrite`-based one-liners are the public re-derivation).
  heldBy-think-⊥ : ∀ {f s} (cfgP : Phil → PhilPos) i {x}
                 → cfgP i ≡ think → ¬ heldBy {f}{s} cfgP i x
  heldBy-think-⊥ cfgP i pe h rewrite pe = h

  heldBy-reloop-⊥ : ∀ {f s} (cfgP : Phil → PhilPos) i {x}
                  → cfgP i ≡ reloop → ¬ heldBy {f}{s} cfgP i x
  heldBy-reloop-⊥ cfgP i pe h rewrite pe = h

  TopOf : (f s : Phil → Fork) (rank : Fork → ℕ) → Config → Phil → Set
  TopOf f s rank (cfgP , _) P =
    Σ[ x ∈ Fork ] (heldBy {f}{s} cfgP P x
                  × (∀ y → heldBy {f}{s} cfgP P y → rank y ≤ rank x))

  topFork : ∀ {f s} (rank : Fork → ℕ) → (∀ i → rank (f i) < rank (s i))
          → ∀ {cfg} P → (Σ[ x ∈ Fork ] heldBy {f}{s} (proj₁ cfg) P x)
          → TopOf f s rank cfg P
  topFork {f}{s} rank ra {cfgP , cfgF} P (x , hx) = topFork′ (cfgP P) refl
    where
      -- The held forks of `P` read off its position (`pe : cfgP P ≡ pos`); after
      -- `rewrite pe`, `heldBy cfgP P y` reduces to the position's body so `hx` becomes
      -- the equation pinning `x`, and a fresh `held` witness / `dom` are direct.
      topFork′ : (pos : PhilPos) → cfgP P ≡ pos → TopOf f s rank (cfgP , cfgF) P
      topFork′ think  pe = ⊥-elim (heldBy-think-⊥  {f}{s} cfgP P pe hx)
      topFork′ reloop pe = ⊥-elim (heldBy-reloop-⊥ {f}{s} cfgP P pe hx)
      topFork′ held1  pe = f P , held , dom
        where
          held : heldBy {f}{s} cfgP P (f P)
          held rewrite pe = refl
          dom : ∀ y → heldBy {f}{s} cfgP P y → rank y ≤ rank (f P)
          dom y hy rewrite pe = ≤-reflexive (cong rank hy)
      topFork′ down1  pe = f P , held , dom
        where
          held : heldBy {f}{s} cfgP P (f P)
          held rewrite pe = refl
          dom : ∀ y → heldBy {f}{s} cfgP P y → rank y ≤ rank (f P)
          dom y hy rewrite pe = ≤-reflexive (cong rank hy)
      topFork′ held2  pe = s P , held , dom
        where
          held : heldBy {f}{s} cfgP P (s P)
          held rewrite pe = inj₂ refl
          dom : ∀ y → heldBy {f}{s} cfgP P y → rank y ≤ rank (s P)
          dom y hy rewrite pe =
            [ (λ y≡f → ≤-trans (≤-reflexive (cong rank y≡f)) (<⇒≤ (ra P)))
            , (λ y≡s → ≤-reflexive (cong rank y≡s))
            ] hy

  not-held⇒free : ∀ {f s} {cfgP cfgF}
    → ValidCfg {f}{s} (cfgP , cfgF)
    → ∀ j → cfgF j ≢ reloop
    → (∀ Q → ¬ heldBy {f}{s} cfgP Q j)
    → cfgF j ≡ free
  not-held⇒free {f}{s} {cfgP}{cfgF} V j ¬reloop noholder with cfgF j in eq
  ... | free    = refl
  ... | reloop  = ⊥-elim (¬reloop refl)
  ... | heldOwn = ⊥-elim (noholder j      (proj₁ (V j) eq))
  ... | heldNbr = ⊥-elim (noholder (j ⊖1) (proj₁ (proj₂ (V j)) eq))

  -------------------------------------------------------------------------------------
  -- Task 6 (3e′-iv), Layer B: resource-ordering search `scan` / `maxHeld`.
  --
  -- A faithful native port of DiningPhilosophers.lagda.md §8.2: `scan k` examines
  -- philosophers of index `< k` and reports either that none of them holds any fork, or
  -- a held fork `x` (held by some `P`, `toℕ P < k`) that `rank`-dominates every fork held
  -- by any philosopher of index `< k`.  `maxHeld` runs it at `k = n`.  The relational
  -- `toℕ` order is replaced by the abstract `rank`; `_∈heldBy_` by `heldBy`; the
  -- thinking-holder refutation `held-think` by applying the holds-nothing predicate.
  -------------------------------------------------------------------------------------

  -- The held-fork witness for `topFork`, read off a known position (`eqk : cfgP P ≡ pos`).
  -- After `rewrite eqk` the body of `heldBy cfgP P _` is exposed, so the witness is direct.
  -- `held1` companion to the (private, Task-5) `heldBy-down1-fi` / `heldBy-held2-si`.
  heldBy-held1-fi : ∀ {f s} (cfgP : Phil → PhilPos) P
                  → cfgP P ≡ held1 → heldBy {f}{s} cfgP P (f P)
  heldBy-held1-fi cfgP P eqk rewrite eqk = refl

  ScanResult : (f s : Phil → Fork) (rank : Fork → ℕ) → Config → ℕ → Set
  ScanResult f s rank cfg k =
      (∀ i → toℕ i < k → ∀ x → ¬ heldBy {f}{s} (proj₁ cfg) i x)
    ⊎ Σ[ x ∈ Fork ] Σ[ P ∈ Phil ]
        ( toℕ P < k
        × heldBy {f}{s} (proj₁ cfg) P x
        × (∀ y i → toℕ i < k → heldBy {f}{s} (proj₁ cfg) i y → rank y ≤ rank x) )

  -- split "toℕ i < suc k" into "below k" or "equal to the k-th philosopher"
  splitPhil : ∀ {k} (p : suc k ≤ n) (i : Phil)
            → toℕ i < suc k → toℕ i < k ⊎ i ≡ fromℕ< p
  splitPhil {k} p i lt with m<1+n⇒m<n∨m≡n lt
  ... | inj₁ below = inj₁ below
  ... | inj₂ eqk   = inj₂ (toℕ-injective (trans eqk (sym (toℕ-fromℕ< p))))

  scan : ∀ {f s} (rank : Fork → ℕ) → (∀ i → rank (f i) < rank (s i))
       → ∀ {cfg} k → k ≤ n → ScanResult f s rank cfg k
  scan rank ra zero _ = inj₁ (λ i () )
  scan {f}{s} rank ra {cfg} (suc k) p with scan {f}{s} rank ra {cfg} k (<⇒≤ p)
  scan {f}{s} rank ra {cfgP , cfgF} (suc k) p | inj₁ allHold
    with cfgP (fromℕ< p) in eqk
  ... | think = inj₁ ext
    where
      ext : ∀ i → toℕ i < suc k → ∀ x → ¬ heldBy {f}{s} cfgP i x
      ext i lt x h with splitPhil p i lt
      ... | inj₁ below = allHold i below x h
      ... | inj₂ refl  = heldBy-think-⊥ {f}{s} cfgP i eqk h
  ... | reloop = inj₁ ext
    where
      ext : ∀ i → toℕ i < suc k → ∀ x → ¬ heldBy {f}{s} cfgP i x
      ext i lt x h with splitPhil p i lt
      ... | inj₁ below = allHold i below x h
      ... | inj₂ refl  = heldBy-reloop-⊥ {f}{s} cfgP i eqk h
  ... | held1 = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
    where
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ x → x < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      top : TopOf f s rank (cfgP , cfgF) (fromℕ< p)
      top = topFork {f}{s} rank ra {cfgP , cfgF} (fromℕ< p)
              (f (fromℕ< p) , heldBy-held1-fi {f}{s} cfgP (fromℕ< p) eqk)
      dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank (proj₁ top)
      dom y i lt h with splitPhil p i lt
      ... | inj₂ refl  = proj₂ (proj₂ top) y h
      ... | inj₁ below = ⊥-elim (allHold i below y h)
  ... | down1 = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
    where
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ x → x < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      top : TopOf f s rank (cfgP , cfgF) (fromℕ< p)
      top = topFork {f}{s} rank ra {cfgP , cfgF} (fromℕ< p)
              (f (fromℕ< p) , heldBy-down1-fi {f}{s} cfgP (fromℕ< p) eqk)
      dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank (proj₁ top)
      dom y i lt h with splitPhil p i lt
      ... | inj₂ refl  = proj₂ (proj₂ top) y h
      ... | inj₁ below = ⊥-elim (allHold i below y h)
  ... | held2 = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
    where
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ x → x < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      top : TopOf f s rank (cfgP , cfgF) (fromℕ< p)
      top = topFork {f}{s} rank ra {cfgP , cfgF} (fromℕ< p)
              (s (fromℕ< p) , heldBy-held2-si {f}{s} cfgP (fromℕ< p) eqk)
      dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank (proj₁ top)
      dom y i lt h with splitPhil p i lt
      ... | inj₂ refl  = proj₂ (proj₂ top) y h
      ... | inj₁ below = ⊥-elim (allHold i below y h)
  scan {f}{s} rank ra {cfgP , cfgF} (suc k) p | inj₂ (x , P , P<k , x∈P , xdom)
    with cfgP (fromℕ< p) in eqk
  ... | think = inj₂ (x , P , m≤n⇒m≤1+n P<k , x∈P , dom)
    where
      dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank x
      dom y i lt h with splitPhil p i lt
      ... | inj₁ below = xdom y i below h
      ... | inj₂ refl  = ⊥-elim (heldBy-think-⊥ {f}{s} cfgP i eqk h)
  ... | reloop = inj₂ (x , P , m≤n⇒m≤1+n P<k , x∈P , dom)
    where
      dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank x
      dom y i lt h with splitPhil p i lt
      ... | inj₁ below = xdom y i below h
      ... | inj₂ refl  = ⊥-elim (heldBy-reloop-⊥ {f}{s} cfgP i eqk h)
  ... | held1 = merge
    where
      top : TopOf f s rank (cfgP , cfgF) (fromℕ< p)
      top = topFork {f}{s} rank ra {cfgP , cfgF} (fromℕ< p)
              (f (fromℕ< p) , heldBy-held1-fi {f}{s} cfgP (fromℕ< p) eqk)
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ z → z < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      merge : ScanResult f s rank (cfgP , cfgF) (suc k)
      merge with ≤-total (rank (proj₁ top)) (rank x)
      ... | inj₁ top≤x = inj₂ (x , P , m≤n⇒m≤1+n P<k , x∈P , dom)
        where
          dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank x
          dom y i lt h with splitPhil p i lt
          ... | inj₁ below = xdom y i below h
          ... | inj₂ refl  = ≤-trans (proj₂ (proj₂ top) y h) top≤x
      ... | inj₂ x≤top = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
        where
          dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank (proj₁ top)
          dom y i lt h with splitPhil p i lt
          ... | inj₁ below = ≤-trans (xdom y i below h) x≤top
          ... | inj₂ refl  = proj₂ (proj₂ top) y h
  ... | down1 = merge
    where
      top : TopOf f s rank (cfgP , cfgF) (fromℕ< p)
      top = topFork {f}{s} rank ra {cfgP , cfgF} (fromℕ< p)
              (f (fromℕ< p) , heldBy-down1-fi {f}{s} cfgP (fromℕ< p) eqk)
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ z → z < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      merge : ScanResult f s rank (cfgP , cfgF) (suc k)
      merge with ≤-total (rank (proj₁ top)) (rank x)
      ... | inj₁ top≤x = inj₂ (x , P , m≤n⇒m≤1+n P<k , x∈P , dom)
        where
          dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank x
          dom y i lt h with splitPhil p i lt
          ... | inj₁ below = xdom y i below h
          ... | inj₂ refl  = ≤-trans (proj₂ (proj₂ top) y h) top≤x
      ... | inj₂ x≤top = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
        where
          dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank (proj₁ top)
          dom y i lt h with splitPhil p i lt
          ... | inj₁ below = ≤-trans (xdom y i below h) x≤top
          ... | inj₂ refl  = proj₂ (proj₂ top) y h
  ... | held2 = merge
    where
      top : TopOf f s rank (cfgP , cfgF) (fromℕ< p)
      top = topFork {f}{s} rank ra {cfgP , cfgF} (fromℕ< p)
              (s (fromℕ< p) , heldBy-held2-si {f}{s} cfgP (fromℕ< p) eqk)
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ z → z < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      merge : ScanResult f s rank (cfgP , cfgF) (suc k)
      merge with ≤-total (rank (proj₁ top)) (rank x)
      ... | inj₁ top≤x = inj₂ (x , P , m≤n⇒m≤1+n P<k , x∈P , dom)
        where
          dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank x
          dom y i lt h with splitPhil p i lt
          ... | inj₁ below = xdom y i below h
          ... | inj₂ refl  = ≤-trans (proj₂ (proj₂ top) y h) top≤x
      ... | inj₂ x≤top = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
        where
          dom : ∀ y i → toℕ i < suc k → heldBy {f}{s} cfgP i y → rank y ≤ rank (proj₁ top)
          dom y i lt h with splitPhil p i lt
          ... | inj₁ below = ≤-trans (xdom y i below h) x≤top
          ... | inj₂ refl  = proj₂ (proj₂ top) y h

  maxHeld : ∀ {f s} (rank : Fork → ℕ) → (∀ i → rank (f i) < rank (s i)) → ∀ {cfg}
          → (∀ i → ∀ x → ¬ heldBy {f}{s} (proj₁ cfg) i x)
          ⊎ Σ[ x ∈ Fork ] Σ[ P ∈ Phil ]
              ( heldBy {f}{s} (proj₁ cfg) P x
              × (∀ y i → heldBy {f}{s} (proj₁ cfg) i y → rank y ≤ rank x) )
  maxHeld {f}{s} rank ra {cfg} with scan {f}{s} rank ra {cfg} n ≤-refl
  ... | inj₁ none = inj₁ (λ i → none i (toℕ<n i))
  ... | inj₂ (x , P , _ , h , dom) = inj₂ (x , P , h , λ y i hy → dom y i (toℕ<n i) hy)

  -------------------------------------------------------------------------------------
  -- Task 7 (3e′-iv): progress assembly `enabledCfg` / `no-deadlock-cfg`.
  --
  -- `enabledCfg` wires Layer B (the resource-ordering search `maxHeld`) through Layer A
  -- (the completeness bridge `enabled⇒¬stuck`) to conclude `EnabledCfg`, hence
  -- `¬ IsStuck`.  It first dispatches the sil-headed cases (a `reloop` philosopher or
  -- fork ⇒ a `_⊳τ_` step), then the eating cases (a `held2`/`down1` philosopher ⇒ a
  -- `⊳pd-*` putsdown), and only then runs `maxHeld` to find the globally maximal
  -- fork-holder, which can always advance (take its next fork).
  --
  -- OWN/NBR PREMISE.  Unlike the relational `no-deadlock` (DiningPhilosophers.lagda.md
  -- §8.4), the `⊳pk*-own`/`⊳pk*-nbr` constructors of `_⊳⟨_⟩_` split the fork-acquisition
  -- on whether the fork is the philosopher's OWN (`f i ≡ i`, resp. `s i ≡ i`) or its
  -- NEIGHBOUR's (`f i ≡ i ⊕1`, resp. `s i ≡ i ⊕1`).  For an ARBITRARY `f`/`s` neither may
  -- hold, so the constructor is unsatisfiable: we must take the own/nbr discriminant as a
  -- HYPOTHESIS `fown`/`sown`.  Task 8 discharges it for the asym instance
  -- (`asymFirst i ∈ {i, i ⊕1}`, `asymSecond i ∈ {i, i ⊕1}` by construction).
  -------------------------------------------------------------------------------------

  private
    -- Finite scan for a `reloop` philosopher.
    find-phil-reloop : ∀ (cfgP : Phil → PhilPos)
      → (Σ[ i ∈ Phil ] cfgP i ≡ reloop) ⊎ (∀ i → cfgP i ≢ reloop)
    find-phil-reloop cfgP = case go n ≤-refl of λ
      { (inj₁ found)    → inj₁ found
      ; (inj₂ none-all) → inj₂ (λ i → none-all i (toℕ<n i)) }
      where
        go : ∀ k → k ≤ n
           → (Σ[ i ∈ Phil ] cfgP i ≡ reloop) ⊎ (∀ i → toℕ i < k → cfgP i ≢ reloop)
        go zero    _ = inj₂ (λ i ())
        go (suc k) p with go k (<⇒≤ p)
        ... | inj₁ found = inj₁ found
        ... | inj₂ none  with cfgP (fromℕ< p) in eqk
        ...   | reloop = inj₁ (fromℕ< p , eqk)
        ...   | think  = inj₂ ext where
                  ext : ∀ i → toℕ i < suc k → cfgP i ≢ reloop
                  ext i lt re with splitPhil p i lt
                  ... | inj₁ below = none i below re
                  ... | inj₂ refl  = case trans (sym eqk) re of λ ()
        ...   | held1  = inj₂ ext where
                  ext : ∀ i → toℕ i < suc k → cfgP i ≢ reloop
                  ext i lt re with splitPhil p i lt
                  ... | inj₁ below = none i below re
                  ... | inj₂ refl  = case trans (sym eqk) re of λ ()
        ...   | held2  = inj₂ ext where
                  ext : ∀ i → toℕ i < suc k → cfgP i ≢ reloop
                  ext i lt re with splitPhil p i lt
                  ... | inj₁ below = none i below re
                  ... | inj₂ refl  = case trans (sym eqk) re of λ ()
        ...   | down1  = inj₂ ext where
                  ext : ∀ i → toℕ i < suc k → cfgP i ≢ reloop
                  ext i lt re with splitPhil p i lt
                  ... | inj₁ below = none i below re
                  ... | inj₂ refl  = case trans (sym eqk) re of λ ()

    -- Finite scan for a `reloop` fork.
    find-fork-reloop : ∀ (cfgF : Fork → ForkPos)
      → (Σ[ j ∈ Fork ] cfgF j ≡ reloop) ⊎ (∀ j → cfgF j ≢ reloop)
    find-fork-reloop cfgF = case go n ≤-refl of λ
      { (inj₁ found)    → inj₁ found
      ; (inj₂ none-all) → inj₂ (λ j → none-all j (toℕ<n j)) }
      where
        go : ∀ k → k ≤ n
           → (Σ[ j ∈ Fork ] cfgF j ≡ reloop) ⊎ (∀ j → toℕ j < k → cfgF j ≢ reloop)
        go zero    _ = inj₂ (λ j ())
        go (suc k) p with go k (<⇒≤ p)
        ... | inj₁ found = inj₁ found
        ... | inj₂ none  with cfgF (fromℕ< p) in eqk
        ...   | reloop  = inj₁ (fromℕ< p , eqk)
        ...   | free    = inj₂ ext where
                  ext : ∀ j → toℕ j < suc k → cfgF j ≢ reloop
                  ext j lt re with splitPhil p j lt
                  ... | inj₁ below = none j below re
                  ... | inj₂ refl  = case trans (sym eqk) re of λ ()
        ...   | heldOwn = inj₂ ext where
                  ext : ∀ j → toℕ j < suc k → cfgF j ≢ reloop
                  ext j lt re with splitPhil p j lt
                  ... | inj₁ below = none j below re
                  ... | inj₂ refl  = case trans (sym eqk) re of λ ()
        ...   | heldNbr = inj₂ ext where
                  ext : ∀ j → toℕ j < suc k → cfgF j ≢ reloop
                  ext j lt re with splitPhil p j lt
                  ... | inj₁ below = none j below re
                  ... | inj₂ refl  = case trans (sym eqk) re of λ ()

    -- Finite scan for an eating (`held2` or `down1`) philosopher.
    find-phil-eating : ∀ (cfgP : Phil → PhilPos)
      → (Σ[ i ∈ Phil ] (cfgP i ≡ held2 ⊎ cfgP i ≡ down1))
      ⊎ (∀ i → cfgP i ≢ held2 × cfgP i ≢ down1)
    find-phil-eating cfgP = case go n ≤-refl of λ
      { (inj₁ found)    → inj₁ found
      ; (inj₂ none-all) → inj₂ (λ i → (λ e → none-all i (toℕ<n i) (inj₁ e))
                                     , (λ e → none-all i (toℕ<n i) (inj₂ e))) }
      where
        go : ∀ k → k ≤ n
           → (Σ[ i ∈ Phil ] (cfgP i ≡ held2 ⊎ cfgP i ≡ down1))
           ⊎ (∀ i → toℕ i < k → ¬ (cfgP i ≡ held2 ⊎ cfgP i ≡ down1))
        go zero    _ = inj₂ (λ i ())
        go (suc k) p with go k (<⇒≤ p)
        ... | inj₁ found = inj₁ found
        ... | inj₂ none  with cfgP (fromℕ< p) in eqk
        ...   | held2  = inj₁ (fromℕ< p , inj₁ eqk)
        ...   | down1  = inj₁ (fromℕ< p , inj₂ eqk)
        ...   | think  = inj₂ ext where
                  ext : ∀ i → toℕ i < suc k → ¬ (cfgP i ≡ held2 ⊎ cfgP i ≡ down1)
                  ext i lt e with splitPhil p i lt
                  ... | inj₁ below = none i below e
                  ... | inj₂ refl  = case e of λ { (inj₁ h) → case trans (sym eqk) h of λ ()
                                                  ; (inj₂ d) → case trans (sym eqk) d of λ () }
        ...   | held1  = inj₂ ext where
                  ext : ∀ i → toℕ i < suc k → ¬ (cfgP i ≡ held2 ⊎ cfgP i ≡ down1)
                  ext i lt e with splitPhil p i lt
                  ... | inj₁ below = none i below e
                  ... | inj₂ refl  = case e of λ { (inj₁ h) → case trans (sym eqk) h of λ ()
                                                  ; (inj₂ d) → case trans (sym eqk) d of λ () }
        ...   | reloop = inj₂ ext where
                  ext : ∀ i → toℕ i < suc k → ¬ (cfgP i ≡ held2 ⊎ cfgP i ≡ down1)
                  ext i lt e with splitPhil p i lt
                  ... | inj₁ below = none i below e
                  ... | inj₂ refl  = case e of λ { (inj₁ h) → case trans (sym eqk) h of λ ()
                                                  ; (inj₂ d) → case trans (sym eqk) d of λ () }

  -- `heldBy` witness off a held2 holder for its FIRST fork: a held2 philosopher holds
  -- both `f i` and `s i`, hence holds `f i`.  (Companion to the private `heldBy-held2-si`,
  -- which gives the SECOND fork `s i`.)
  heldBy-held2-fi : ∀ {f s} (cfgP : Phil → PhilPos) i
                   → cfgP i ≡ held2 → heldBy {f}{s} cfgP i (f i)
  heldBy-held2-fi cfgP i eq rewrite eq = inj₁ refl

  enabledCfg : ∀ {f s} (rank : Fork → ℕ) → (∀ i → rank (f i) < rank (s i))
             → (∀ i → (f i ≡ i) ⊎ (f i ≡ i ⊕1))
             → (∀ i → (s i ≡ i) ⊎ (s i ≡ i ⊕1))
             → ∀ {cfg} → ValidCfg {f}{s} cfg → EnabledCfg f s cfg
  enabledCfg {f}{s} rank ra fown sown {cfgP , cfgF} V
    with find-phil-reloop cfgP
  ... | inj₁ (i , re) = inj₂ (_ , ⊳τ-phil re)
  ... | inj₂ noPhilRe with find-fork-reloop cfgF
  ...   | inj₁ (j , re) = inj₂ (_ , ⊳τ-fork re)
  ...   | inj₂ noForkRe with find-phil-eating cfgP
  ...     | inj₁ (i , inj₁ h2) = inj₁ ((noPhilRe , noForkRe) , _ , _ , ⊳pd-s {i = i} h2)
  ...     | inj₁ (i , inj₂ d1) = inj₁ ((noPhilRe , noForkRe) , _ , _ , ⊳pd-f {i = i} d1)
  ...     | inj₂ noEat with maxHeld {f}{s} rank ra {cfgP , cfgF}
  -- ── all think: `fzero` takes its first fork `f fzero` (which is free).
  ...       | inj₁ none = think-branch (cfgP zero′) refl
    where
      zero′ : Phil
      zero′ = Fin.zero
      free-f0 : cfgF (f zero′) ≡ free
      free-f0 = not-held⇒free {f}{s} {cfgP}{cfgF} V (f zero′)
                  (noForkRe (f zero′)) (λ Q hQ → none Q (f zero′) hQ)
      think-branch : (pos : PhilPos) → cfgP zero′ ≡ pos → EnabledCfg f s (cfgP , cfgF)
      think-branch think  pe with fown zero′
      ... | inj₁ own = inj₁ ((noPhilRe , noForkRe) , _ , _ , ⊳pk1-own {i = zero′} pe own free-f0)
      ... | inj₂ nbr = inj₁ ((noPhilRe , noForkRe) , _ , _ , ⊳pk1-nbr {i = zero′} pe nbr free-f0)
      think-branch held1  pe = ⊥-elim (none zero′ (f zero′) (heldBy-held1-fi {f}{s} cfgP zero′ pe))
      think-branch held2  pe = ⊥-elim (none zero′ (f zero′) (heldBy-held2-fi {f}{s} cfgP zero′ pe))
      think-branch down1  pe = ⊥-elim (none zero′ (f zero′) (heldBy-down1-fi {f}{s} cfgP zero′ pe))
      think-branch reloop pe = ⊥-elim (noPhilRe zero′ pe)
  -- ── max-fork: its owner `P` holds `x` (= `f P`), and `s P` (strictly bigger) is free.
  ...       | inj₂ (x , P , h , dom) = max-branch (cfgP P) refl
    where
      max-branch : (pos : PhilPos) → cfgP P ≡ pos → EnabledCfg f s (cfgP , cfgF)
      max-branch think  pe = ⊥-elim (heldBy-think-⊥ {f}{s} cfgP P pe h)
      max-branch reloop pe = ⊥-elim (noPhilRe P pe)
      max-branch held2  pe = ⊥-elim (proj₁ (noEat P) pe)
      max-branch down1  pe = ⊥-elim (proj₂ (noEat P) pe)
      max-branch held1  pe = step
        where
          -- a held1 holder holds exactly `f P`, so `x ≡ f P`.
          x≡fP : x ≡ f P
          x≡fP = helper h where
            helper : heldBy {f}{s} cfgP P x → x ≡ f P
            helper hh rewrite pe = hh
          fP<sP : rank (f P) < rank (s P)
          fP<sP = ra P
          -- `s P` is free: nobody holds it (a holder Q would give `rank (s P) ≤ rank x`).
          noHold-sP : ∀ Q → ¬ heldBy {f}{s} cfgP Q (s P)
          noHold-sP Q hQ = ≤⇒≯ (dom (s P) Q hQ)
                                (subst (λ z → rank z < rank (s P)) (sym x≡fP) fP<sP)
          free-sP : cfgF (s P) ≡ free
          free-sP = not-held⇒free {f}{s} {cfgP}{cfgF} V (s P) (noForkRe (s P)) noHold-sP
          step : EnabledCfg f s (cfgP , cfgF)
          step with sown P
          ... | inj₁ own = inj₁ ((noPhilRe , noForkRe) , _ , _ , ⊳pk2-own {i = P} pe own free-sP)
          ... | inj₂ nbr = inj₁ ((noPhilRe , noForkRe) , _ , _ , ⊳pk2-nbr {i = P} pe nbr free-sP)

  no-deadlock-cfg : ∀ {f s} (rank : Fork → ℕ) → (∀ i → rank (f i) < rank (s i))
                  → (∀ i → (f i ≡ i) ⊎ (f i ≡ i ⊕1))
                  → (∀ i → (s i ≡ i) ⊎ (s i ≡ i ⊕1))
                  → ∀ {cfg} → ValidCfg {f}{s} cfg → ¬ IsStuck (sysState f s cfg)
  no-deadlock-cfg rank ra fown sown V =
    enabled⇒¬stuck V (enabledCfg rank ra fown sown V)

  -------------------------------------------------------------------------------------
  -- Task 8 (3e′-iv): discharge `no-deadlock-cfg` for the COMMITTED asymmetric instance
  -- (`asymFirst`/`asymSecond`, "philosopher 0 left-handed") via the permutation rank
  -- `rank j = toℕ (j ⊖1)`.  This is the final substantive deliverable of iv.
  --
  -- The rank is the predecessor index, which is a bijection on the ring; the asymmetric
  -- ordering makes `rank (first i) < rank (second i)` hold uniformly:
  --   • philosopher 0:  first = 0 ⊕1,  second = 0     ⇒ rank 0 = 0 < suc m = rank(0⊖1).
  --   • philosopher i≠0: first = i,      second = i ⊕1  ⇒ rank(i⊖1) < rank i = rank((i⊕1)⊖1).
  -------------------------------------------------------------------------------------

  -- `toℕ ∘ _⊖1` strictly decreases off `fzero` (the non-wrap case).
  toℕ-⊖1-suc< : ∀ (i : Fork) → i ≢ Fin.zero → toℕ (i ⊖1) < toℕ i
  toℕ-⊖1-suc< Fin.zero    i≢0 = ⊥-elim (i≢0 refl)
  toℕ-⊖1-suc< (Fin.suc i) _   =
    -- `Fin.suc i ⊖1 = inject₁ i`, so `toℕ (Fin.suc i ⊖1) = toℕ i < suc (toℕ i)`.
    subst (λ z → z < suc (toℕ i)) (sym (toℕ-inject₁ i)) (n<1+n (toℕ i))

  rank-asym : ∀ i → toℕ (asymFirst i ⊖1) < toℕ (asymSecond i ⊖1)
  rank-asym i with i Fin.≟ Fin.zero
  ... | yes refl =
    -- asymFirst 0 = 0 ⊕1, asymSecond 0 = 0.  rank((0⊕1)⊖1) = toℕ 0 = 0 < suc m = rank(0⊖1).
    subst (λ z → toℕ z < toℕ (Fin.zero ⊖1)) (sym (⊕⊖′ Fin.zero))
      (subst (0 <_) (sym toℕ-⊖1-zero′) (s≤s z≤n))
  ... | no  i≢0  =
    -- asymFirst i = i, asymSecond i = i ⊕1.  rank(i⊖1) < toℕ i = rank((i⊕1)⊖1).
    subst (λ z → toℕ (i ⊖1) < toℕ z) (sym (⊕⊖′ i)) (toℕ-⊖1-suc< i i≢0)

  fown-asym : ∀ i → (asymFirst i ≡ i) ⊎ (asymFirst i ≡ i ⊕1)
  fown-asym i with i Fin.≟ Fin.zero
  ... | yes refl = inj₂ refl   -- asymFirst 0 = 0 ⊕1
  ... | no  _    = inj₁ refl   -- asymFirst i = i

  sown-asym : ∀ i → (asymSecond i ≡ i) ⊎ (asymSecond i ≡ i ⊕1)
  sown-asym i with i Fin.≟ Fin.zero
  ... | yes refl = inj₁ refl   -- asymSecond 0 = 0
  ... | no  _    = inj₂ refl   -- asymSecond i = i ⊕1

  asym-no-deadlock : ∀ {cfg} → ValidCfg {asymFirst}{asymSecond} cfg
                   → ¬ IsStuck (sysState asymFirst asymSecond cfg)
  asym-no-deadlock V =
    no-deadlock-cfg (λ j → toℕ (j ⊖1)) rank-asym fown-asym sown-asym V

-------------------------------------------------------------------------------------
-- Task 9 (3e′-iv): non-vacuity witnesses at the smallest instance (`open Prog 0`, so
-- `n = 2`, `Phil = Fork = Fin 2`).  These anonymous `_`-bindings FORCE the Task-8
-- progress machinery to COMPUTE on concrete data — not merely type-check — confirming
-- the definitions are non-vacuous (reduce to genuine values).
-------------------------------------------------------------------------------------

module Sanity where
  open M.Sys 0   -- asymFirst / asymSecond / Config / think / free / _⊖1 at n = 2
  open St.St 0   -- PhilPos / ForkPos at n = 2
  open Prog 0    -- rank-asym / enabledCfg / EnabledCfg / asym-no-deadlock at n = 2
  open SysSt.SysSt 0 using (valid-init; sysState)  -- the validity invariant's start witness + carrier

  -- `rank-asym` computes both ring branches (philosopher 0 wraps, others step) to
  -- genuine strict-`<` proofs on the predecessor-index rank.
  _ : toℕ (asymFirst Fin.zero ⊖1) < toℕ (asymSecond Fin.zero ⊖1)
  _ = rank-asym Fin.zero
  _ : toℕ (asymFirst (Fin.suc Fin.zero) ⊖1) < toℕ (asymSecond (Fin.suc Fin.zero) ⊖1)
  _ = rank-asym (Fin.suc Fin.zero)

  -- `enabledCfg` computes a genuine `EnabledCfg` witness on the all-`think` valid config
  -- (valid by `valid-init`): the resource-ordering search picks philosopher 0 to take its
  -- free first fork (the `think`/`maxHeld inj₁ none` branch fires `⊳pk1-*`).
  _ : EnabledCfg asymFirst asymSecond ((λ _ → think) , (λ _ → free))
  _ = enabledCfg (λ j → toℕ (j ⊖1)) rank-asym fown-asym sown-asym
        (valid-init {asymFirst} {asymSecond})

  -- `asym-no-deadlock` computes a genuine "not stuck" witness on the same valid config.
  _ : ¬ IsStuck (sysState asymFirst asymSecond ((λ _ → think) , (λ _ → free)))
  _ = asym-no-deadlock {cfg = (λ _ → think) , (λ _ → free)}
        (valid-init {asymFirst} {asymSecond})

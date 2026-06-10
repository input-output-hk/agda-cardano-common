{-# OPTIONS --guardedness #-}
module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Deadlock where

open import Level using (lift) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Function using (case_of_; _∘_)
open import Data.Vec using (Vec; tabulate; toList)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)

open import Interaction_Trees
open ITree
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.Deadlock using (HasDeadlock; DeadlockFree; hasDeadlock⇒¬deadlockFree)
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP as M

module Pf (m : ℕ) where
  open M.Sys m

  -- Operator + iterate definitions (loop0, ⟶₀, >>=, iter-bind, Prefix-cont,
  -- bind-cont-vis, …) at the dining-philosophers event decidability.
  import CSP.Definitions.Operators {E = DP} as OpsD
  open OpsD DP-AnyTypes-≟
  import CSP.Definitions.Iterate {E = DP} as IterD
  open IterD DP-AnyTypes-≟
  import CSP.Definitions.Parallel {E = DP} as ParD
  open ParD DP-AnyTypes-≟ using (_⦀_; _∥⇘_¿_⇙_)

  -- Law modules instantiated at the dining-philosophers event decidability.
  import CSP.Laws.Bind {E = DP} as BindL
  open BindL DP-AnyTypes-≟ using (lift-bind-bigstep; bind-force-vis)
  import CSP.Laws.Iterate {E = DP} as IterL
  open IterL DP-AnyTypes-≟ using (iter-bind-force-vis; iter-bind-cont-vis-just)

  -- The continuation appended by loop / loop0.
  loop-k : ⊤ {lzero} → ITree DP (ExtI DP) (⊤ {lzero} ⊎ ⊥)
  loop-k = λ a' → Ret (inj₁ a')

  -- loopStep for loop0 (ch ⟶₀ rest): loop (λ _ → ch ⟶₀ rest), so
  -- step a = (ch ⟶₀ rest) >>= loop-k, independent of a.
  loopStep : ∀ {A} (ch : DP A) (rest : ITree DP (ExtI DP) (⊤ {lzero}))
           → ⊤ {lzero} → ITree DP (ExtI DP) (⊤ {lzero} ⊎ ⊥)
  loopStep ch rest = λ _ → (ch ⟶₀ rest) >>= loop-k

  -- The residual after firing the head event of loop0 (ch ⟶₀ rest).
  loop0-tail : ∀ {A} (ch : DP A) (a : A) (rest : ITree DP (ExtI DP) (⊤ {lzero}))
             → ITree DP (ExtI DP) ⊥
  loop0-tail ch a rest =
    iter-bind (rest >>= loop-k) (loopStep ch rest)

  loop0-prefix-step :
    ∀ {A} (ch : DP A) (a : A) (rest : ITree DP (ExtI DP) (⊤ {lzero}))
    → loop0 (ch ⟶₀ rest)
        ─[ ev (evl (evLabel A ch a)) ]─►
      loop0-tail ch a rest
  loop0-prefix-step {A} ch a rest =
    sVis {at = A , ch} {a = a} refl
      (iter-bind-cont-vis-just (loopStep ch rest)
        (bind-cont-vis loop-k (Prefix-cont ch (λ _ → rest)))
        (A , ch) a
        (bind-cont-vis-just loop-k (Prefix-cont ch (λ _ → rest)) (A , ch) a
          (Prefix-cont-just ch (λ _ → rest) a)))

  -- When `rest` is itself a prefix `ch′ ⟶₀ rest′`, the residual's force is a
  -- `vis` node (offering `ch′`): the (ch′ ⟶₀ rest′) >>= loop-k bind layer and
  -- the outer iter-bind layer both keep a `vis` force.
  loop0-tail-vis :
    ∀ {A B} (ch : DP A) (a : A) (ch′ : DP B) (rest′ : ITree DP (ExtI DP) (⊤ {lzero}))
    → Σ[ f ∈ _ ] (ITree.force (loop0-tail ch a (ch′ ⟶₀ rest′)) ≡ vis f)
  loop0-tail-vis ch a ch′ rest′ =
    _ ,
    iter-bind-force-vis ((ch′ ⟶₀ rest′) >>= loop-k) (loopStep ch (ch′ ⟶₀ rest′))
      (bind-force-vis (ch′ ⟶₀ rest′) loop-k refl)

  -------------------------------------------------------------------------------------
  -- Task 2: single-step / τ-propagation lemmas for the binary interleave `_⦀_`,
  -- and the replicated-interleave fold lemmas `⦀list-vis` / `⦀list-fires`.
  --
  -- `_⦀_` is the *un-alphabetised* interleave: there is no `dec`/alphabet routing, so
  -- the proofs are simpler than the `αpar-*` proofs in `CSP/Laws/AlphaParallel.agda`,
  -- which we mirror.  After `rewrite eqP | eqQ` the relevant `_⦀_` force clause is
  -- exposed; the `fQ at a ≡ nothing` (resp. `fP at a ≡ nothing`) premise selects the
  -- clean single-mover branch (avoiding the `Fin 2` ndbr).

  private
    -- The DP interaction-tree carrier with a generic return type.
    DPTree : ∀ {ℓr} → Set ℓr → Set _
    DPTree R = ITree DP (ExtI DP) R

  -------------------------------------------------------------------------------------
  -- (A) Binary `⦀` single steps: only one side moves.  Mirrors the `αpar-soloL/R-step`
  -- idiom: a force-helper exposes the composite's `vis` shape, and an offer-helper
  -- (after `rewrite eqP | eqQ … with fe | refl`) computes the merged branch.

  private
    -- force-helper: vis|vis composite is vis-headed.
    f⦀vv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fP fQ}
      → P .force ≡ vis fP → Q .force ≡ vis fQ
      → Σ[ f ∈ _ ] ((P ⦀ Q) .force ≡ vis f)
    f⦀vv eqP eqQ rewrite eqP | eqQ = _ , refl

    -- force-helper: vis|ret composite is vis-headed.
    f⦀vr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fP} {s : S}
      → P .force ≡ vis fP → Q .force ≡ ret s
      → Σ[ f ∈ _ ] ((P ⦀ Q) .force ≡ vis f)
    f⦀vr eqP eqQ rewrite eqP | eqQ = _ , refl

    -- offer-helper for solo-L (vis|vis): only P offers, Q refuses.
    o⦀L : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q : DPTree S} {fP fQ} {at a} {f}
      → P .force ≡ vis fP → fP at a ≡ just P′
      → Q .force ≡ vis fQ → fQ at a ≡ nothing
      → (P ⦀ Q) .force ≡ vis f
      → f at a ≡ just (P′ ⦀ Q)
    o⦀L eqP bP eqQ bQ fe rewrite eqP | eqQ with fe
    ... | refl rewrite bP | bQ = refl

    -- offer-helper for solo-R (vis|vis): only Q offers, P refuses.
    o⦀R : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q Q′ : DPTree S} {fP fQ} {at a} {f}
      → P .force ≡ vis fP → fP at a ≡ nothing
      → Q .force ≡ vis fQ → fQ at a ≡ just Q′
      → (P ⦀ Q) .force ≡ vis f
      → f at a ≡ just (P ⦀ Q′)
    o⦀R eqP bP eqQ bQ fe rewrite eqP | eqQ with fe
    ... | refl rewrite bP | bQ = refl

    -- offer-helper for solo-L against a ret-headed Q (vis|ret).
    o⦀Lret : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q : DPTree S} {fP} {s : S} {at a} {f}
      → P .force ≡ vis fP → fP at a ≡ just P′ → Q .force ≡ ret s
      → (P ⦀ Q) .force ≡ vis f
      → f at a ≡ just (P′ ⦀ Q)
    o⦀Lret eqP bP eqQ fe rewrite eqP | eqQ with fe
    ... | refl rewrite bP = refl

    -- refuse offer-helper (vis|ret): P refuses, Q ret-headed → composite refuses.
    o⦀ref-vr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fP} {s : S} {at a} {f}
      → P .force ≡ vis fP → fP at a ≡ nothing → Q .force ≡ ret s
      → (P ⦀ Q) .force ≡ vis f
      → f at a ≡ nothing
    o⦀ref-vr eqP bP eqQ fe rewrite eqP | eqQ with fe
    ... | refl rewrite bP = refl

    -- refuse offer-helper (vis|vis): both refuse → composite refuses.
    o⦀ref-vv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fP fQ} {at a} {f}
      → P .force ≡ vis fP → fP at a ≡ nothing
      → Q .force ≡ vis fQ → fQ at a ≡ nothing
      → (P ⦀ Q) .force ≡ vis f
      → f at a ≡ nothing
    o⦀ref-vv eqP bP eqQ bQ fe rewrite eqP | eqQ with fe
    ... | refl rewrite bP | bQ = refl

  -- P offers the event, Q (vis-headed) refuses it: P moves solo.
  ⦀-step-L : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P P′ : DPTree R} {Q : DPTree S}
      {fP fQ} {at : AnyTypes DP} {a : proj₁ at}
    → P .force ≡ vis fP → fP at a ≡ just P′
    → Q .force ≡ vis fQ → fQ at a ≡ nothing
    → (P ⦀ Q) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► (P′ ⦀ Q)
  ⦀-step-L eqP bP eqQ bQ with f⦀vv eqP eqQ
  ... | f , fe = sVis fe (o⦀L eqP bP eqQ bQ fe)

  -- Q offers the event, P (vis-headed) refuses it: Q moves solo.
  ⦀-step-R : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P : DPTree R} {Q Q′ : DPTree S}
      {fP fQ} {at : AnyTypes DP} {a : proj₁ at}
    → P .force ≡ vis fP → fP at a ≡ nothing
    → Q .force ≡ vis fQ → fQ at a ≡ just Q′
    → (P ⦀ Q) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► (P ⦀ Q′)
  ⦀-step-R eqP bP eqQ bQ with f⦀vv eqP eqQ
  ... | f , fe = sVis fe (o⦀R eqP bP eqQ bQ fe)

  -- P offers the event, Q is ret-headed (terminated/Skip): P moves solo.
  ⦀-step-L-ret : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P P′ : DPTree R} {Q : DPTree S}
      {fP} {s : S} {at : AnyTypes DP} {a : proj₁ at}
    → P .force ≡ vis fP → fP at a ≡ just P′ → Q .force ≡ ret s
    → (P ⦀ Q) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► (P′ ⦀ Q)
  ⦀-step-L-ret eqP bP eqQ with f⦀vr eqP eqQ
  ... | f , fe = sVis fe (o⦀Lret eqP bP eqQ fe)

  -------------------------------------------------------------------------------------
  -- (B) `⦀` τ-propagation.
  --
  -- DESIGN NOTE.  The literal statement “any τ from P lifts to (P ⦀ Q) ─[τ]─► (P′ ⦀ Q)
  -- whenever Q is non-sil-headed” is *unsound* for `_⦀_`: the operator's clause order
  -- gives Q's `ndbr` distribution priority over P's `mix`-slide (clause
  -- `mix fP P' | ndbr …` distributes Q, not P), and an `ndbr | ndbr` head re-indexes
  -- with `pair`, so P's chosen branch is not preserved.  The mathematically honest
  -- side condition under which P's τ (be it sSil, sNdbr, or sMixSlide) lifts verbatim
  -- to `(P′ ⦀ Q)` is that the *stationary* side Q be ret- or vis-headed — which is
  -- precisely the situation in the dining-philosophers proof (the partner `⦀list` is
  -- vis-headed by `⦀list-vis`, or `Skip`/ret for the singleton).  We thread that as
  -- `RetVisHead Q`.  (For a pure `sSil` the side condition is not needed, but keeping a
  -- uniform premise across the three τ-constructors keeps the lemma simple.)

  RetVisHead : ∀ {ℓr} {R : Set ℓr} → DPTree R → Set _
  RetVisHead {R = R} P =
      (Σ[ r ∈ _ ] P .force ≡ ret r)
    ⊎ (Σ[ f ∈ _ ] P .force ≡ vis f)

  private
    -- ----- force-helpers for τ-L (P moves), Q ret/vis-headed -----
    -- sSil from P: `sil P′ | _` clause has priority, so lifts unconditionally.
    f⦀τL-sil : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q : DPTree S}
      → P .force ≡ sil P′
      → (P ⦀ Q) .force ≡ sil (P′ ⦀ Q)
    f⦀τL-sil eqP rewrite eqP = refl

    -- mix-slide from P, Q ret/vis-headed: composite is mix-headed, sliding to P′ ⦀ Q.
    f⦀τL-mix : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fP P′}
      → RetVisHead Q
      → P .force ≡ mix fP P′
      → Σ[ g ∈ _ ] ((P ⦀ Q) .force ≡ mix g (P′ ⦀ Q))
    f⦀τL-mix (inj₁ (_ , qeq)) eqP rewrite eqP | qeq = _ , refl
    f⦀τL-mix (inj₂ (_ , qeq)) eqP rewrite eqP | qeq = _ , refl

    -- ndbr from P, Q ret/vis-headed: composite is ndbr-headed.
    f⦀τL-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q : DPTree S} {fP wi wa prf} {i a}
      → RetVisHead Q
      → P .force ≡ ndbr fP wi wa prf → fP i a ≡ just P′
      → Σ[ g ∈ _ ] Σ[ wi ∈ _ ] Σ[ wa ∈ _ ] Σ[ prf ∈ _ ]
          ((P ⦀ Q) .force ≡ ndbr g wi wa prf)
    f⦀τL-ndbr (inj₁ (_ , qeq)) eqP fb rewrite eqP | qeq = _ , _ , _ , _ , refl
    f⦀τL-ndbr (inj₂ (_ , qeq)) eqP fb rewrite eqP | qeq = _ , _ , _ , _ , refl

    -- … and its merged branch at (i , a) is `just (P′ ⦀ Q)` when `fP i a ≡ just P′`.
    o⦀τL-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q : DPTree S} {fP wi wa prf} {i a} {g wi′ wa′ prf′}
      → RetVisHead Q
      → P .force ≡ ndbr fP wi wa prf → fP i a ≡ just P′
      → (P ⦀ Q) .force ≡ ndbr g wi′ wa′ prf′
      → g i a ≡ just (P′ ⦀ Q)
    o⦀τL-ndbr (inj₁ (_ , qeq)) eqP fb fe rewrite eqP | qeq with fe
    ... | refl rewrite fb = refl
    o⦀τL-ndbr (inj₂ (_ , qeq)) eqP fb fe rewrite eqP | qeq with fe
    ... | refl rewrite fb = refl

    -- ----- force-helpers for τ-R (Q moves), P ret/vis-headed -----
    f⦀τR-sil : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q Q′ : DPTree S}
      → RetVisHead P
      → Q .force ≡ sil Q′
      → (P ⦀ Q) .force ≡ sil (P ⦀ Q′)
    f⦀τR-sil (inj₁ (_ , peq)) eqQ rewrite peq | eqQ = refl
    f⦀τR-sil (inj₂ (_ , peq)) eqQ rewrite peq | eqQ = refl

    f⦀τR-mix : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fQ Q′}
      → RetVisHead P
      → Q .force ≡ mix fQ Q′
      → Σ[ g ∈ _ ] ((P ⦀ Q) .force ≡ mix g (P ⦀ Q′))
    f⦀τR-mix (inj₁ (_ , peq)) eqQ rewrite peq | eqQ = _ , refl
    f⦀τR-mix (inj₂ (_ , peq)) eqQ rewrite peq | eqQ = _ , refl

    f⦀τR-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q Q′ : DPTree S} {fQ wi wa prf} {i a}
      → RetVisHead P
      → Q .force ≡ ndbr fQ wi wa prf → fQ i a ≡ just Q′
      → Σ[ g ∈ _ ] Σ[ wi ∈ _ ] Σ[ wa ∈ _ ] Σ[ prf ∈ _ ]
          ((P ⦀ Q) .force ≡ ndbr g wi wa prf)
    f⦀τR-ndbr (inj₁ (_ , peq)) eqQ fb rewrite peq | eqQ = _ , _ , _ , _ , refl
    f⦀τR-ndbr (inj₂ (_ , peq)) eqQ fb rewrite peq | eqQ = _ , _ , _ , _ , refl

    o⦀τR-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q Q′ : DPTree S} {fQ wi wa prf} {i a} {g wi′ wa′ prf′}
      → RetVisHead P
      → Q .force ≡ ndbr fQ wi wa prf → fQ i a ≡ just Q′
      → (P ⦀ Q) .force ≡ ndbr g wi′ wa′ prf′
      → g i a ≡ just (P ⦀ Q′)
    o⦀τR-ndbr (inj₁ (_ , peq)) eqQ fb fe rewrite peq | eqQ with fe
    ... | refl rewrite fb = refl
    o⦀τR-ndbr (inj₂ (_ , peq)) eqQ fb fe rewrite peq | eqQ with fe
    ... | refl rewrite fb = refl

  -- A τ from P lifts to a τ of the interleave (Q stationary, ret/vis-headed).
  ⦀-τ-L : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P P′ : DPTree R} {Q : DPTree S}
    → RetVisHead Q
    → P ─[ τ ]─► P′ → (P ⦀ Q) ─[ τ ]─► (P′ ⦀ Q)
  ⦀-τ-L _   (sSil eqP)               = sSil (f⦀τL-sil eqP)
  ⦀-τ-L rvQ (sNdbr {i = i} {a = a} eqP fb)
    with f⦀τL-ndbr rvQ eqP fb
  ... | g , wi , wa , prf , fe = sNdbr fe (o⦀τL-ndbr rvQ eqP fb fe)
  ⦀-τ-L rvQ (sMixSlide eqP)
    with f⦀τL-mix rvQ eqP
  ... | g , fe = sMixSlide fe

  -- A τ from Q lifts to a τ of the interleave (P stationary, ret/vis-headed).
  ⦀-τ-R : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P : DPTree R} {Q Q′ : DPTree S}
    → RetVisHead P
    → Q ─[ τ ]─► Q′ → (P ⦀ Q) ─[ τ ]─► (P ⦀ Q′)
  ⦀-τ-R rvP (sSil eqQ)               = sSil (f⦀τR-sil rvP eqQ)
  ⦀-τ-R rvP (sNdbr {i = i} {a = a} eqQ fb)
    with f⦀τR-ndbr rvP eqQ fb
  ... | g , wi , wa , prf , fe = sNdbr fe (o⦀τR-ndbr rvP eqQ fb fe)
  ⦀-τ-R rvP (sMixSlide eqQ)
    with f⦀τR-mix rvP eqQ
  ... | g , fe = sMixSlide fe

  -------------------------------------------------------------------------------------
  -- (C) Fold lemmas for `⦀list`.

  -- `⦀list` of a non-empty list of vis-headed processes is itself vis-headed.
  -- Mirrors `∥list-headed` in `CSP/Laws/AlphaParallelList.agda`.
  --   base `p ∷ []`  : `p ⦀ Skip` is vis via the vis|ret clause.
  --   cons `p ∷ q ∷` : `p ⦀ ⦀list (q ∷ …)` is vis via the vis|vis clause.
  ⦀list-vis : (p : DPTree ⊥) (ps : List (DPTree ⊥))
            → All (λ q → Σ[ f ∈ _ ] q .force ≡ vis f) (p ∷ ps)
            → Σ[ g ∈ _ ] (⦀list (p ∷ ps)) .force ≡ vis g
  ⦀list-vis p [] ((fp , eqp) ∷ _) rewrite eqp = _ , refl
  ⦀list-vis p (q ∷ ps) ((fp , eqp) ∷ tl)
    with ⦀list-vis q ps tl
  ... | (gtl , eqtl) rewrite eqp | eqtl = _ , refl

  -------------------------------------------------------------------------------------
  -- (D) `⦀list-fires`: the replicated interleave fires event `e` when exactly one
  -- component offers it (→ its residual) and every *other* component (which is
  -- vis-headed) refuses it.
  --
  -- The firing situation is captured by the inductive relation `FiresAt ps at a ps′`,
  -- which both inducts cleanly and is exactly the shape Task 4 needs (philosopher `i`
  -- at the front fires `picks i i`; all others, being vis-headed, refuse it):
  --
  --   fires-head : the head offers `e` (residual `p′`); every tail component is
  --                vis-headed and refuses `e`.  → ps′ = p′ ∷ ps.
  --   fires-tail : the head is vis-headed and refuses `e`; the tail fires `e`
  --                (recursively).             → ps′ = p ∷ (tail residual).
  --
  -- The residual list `ps′` keeps the same length as `ps`, so its `IProd` type is
  -- unchanged and the transition `⦀list ps ─[ev e]─► ⦀list ps′` is well-typed.

  -- All listed components are vis-headed and refuse the event (at , a).
  AllRefuse : List (DPTree ⊥) → (at : AnyTypes DP) → proj₁ at → Set _
  AllRefuse ps at a =
    All (λ q → Σ[ fq ∈ _ ] (q .force ≡ vis fq × fq at a ≡ nothing)) ps

  data FiresAt : (ps : List (DPTree ⊥)) (at : AnyTypes DP) (a : proj₁ at)
                 (ps′ : List (DPTree ⊥)) → Set (lsuc lzero) where
    fires-head : ∀ {p p′ ps} {fp} {at} {a}
               → p .force ≡ vis fp → fp at a ≡ just p′
               → AllRefuse ps at a
               → FiresAt (p ∷ ps) at a (p′ ∷ ps)
    fires-tail : ∀ {p ps ps′} {fp} {at} {a}
               → p .force ≡ vis fp → fp at a ≡ nothing
               → FiresAt ps at a ps′
               → FiresAt (p ∷ ps) at a (p ∷ ps′)

  -- ⦀list of a refusing, all-vis list is vis-headed and refuses (at , a).
  -- (Used by the head case to discharge the stationary tail.)
  ⦀list-refuse : (ps : List (DPTree ⊥)) {at : AnyTypes DP} {a : proj₁ at}
               → AllRefuse ps at a
               → (Σ[ s ∈ _ ] (⦀list ps) .force ≡ ret s)
               ⊎ (Σ[ g ∈ _ ] ((⦀list ps) .force ≡ vis g × g at a ≡ nothing))
  ⦀list-refuse [] _ = inj₁ (_ , refl)           -- ⦀list [] = Skip = Ret tt
  ⦀list-refuse (q ∷ ps) {at = at} {a = a} ((fq , eqq , bq) ∷ tl)
    with ⦀list-refuse ps tl
  ... | inj₁ (_ , retEq) with f⦀vr eqq retEq
  ...   | f , fe = inj₂ (_ , fe , o⦀ref-vr eqq bq retEq fe)
  ⦀list-refuse (q ∷ ps) {at = at} {a = a} ((fq , eqq , bq) ∷ tl)
    | inj₂ (gtl , eqtl , btl) with f⦀vv eqq eqtl
  ...   | f , fe = inj₂ (_ , fe , o⦀ref-vv eqq bq eqtl btl fe)

  -- The firing residual, built at the SOURCE carrier `IProd ps` (it equals the
  -- transported `⦀list ps′`; see `fireRes≡` below).  Keeping the carrier fixed makes
  -- the *homogeneous* transition relation `─[_]─►` well-typed without any transport.
  fireRes : ∀ {ps : List (DPTree ⊥)} {at : AnyTypes DP} {a : proj₁ at}
              {ps′ : List (DPTree ⊥)}
          → FiresAt ps at a ps′ → DPTree (IProd ps)
  fireRes {ps = p ∷ ps} (fires-head {p′ = p′} _ _ _) = p′ ⦀ ⦀list ps
  fireRes {ps = p ∷ ps} (fires-tail {p = p} _ _ fires) = p ⦀ fireRes fires

  -- A firing list is vis-headed (no carrier dependence on ps′ — easy recursion).
  ⦀list-fires-headed :
      ∀ {ps : List (DPTree ⊥)} {at : AnyTypes DP} {a : proj₁ at} {ps′ : List (DPTree ⊥)}
    → FiresAt ps at a ps′ → Σ[ g ∈ _ ] (⦀list ps) .force ≡ vis g
  ⦀list-fires-headed {ps′ = p′ ∷ ps} (fires-head {p = p} {ps = ps} eqp bp allref)
    with ⦀list-refuse ps allref
  ... | inj₁ (_ , retEq) = f⦀vr eqp retEq
  ... | inj₂ (g , eqg , bg) = f⦀vv eqp eqg
  ⦀list-fires-headed (fires-tail {p = p} eqp bp fires)
    with ⦀list-fires-headed fires
  ... | (gtl , eqtl) = f⦀vv eqp eqtl

  -- ⦀list fires the event: one visible LTS step from a `FiresAt` derivation, landing
  -- in `fireRes fires`.  `fires-head` fires the head solo (against the refusing,
  -- ret-/vis-headed tail); `fires-tail` fires the tail solo, lifting the recursive
  -- tail step (necessarily a `sVis`, since `⦀list ps` is vis-headed) through the
  -- refusing head with `⦀-step-R`.
  ⦀list-fires : ∀ {ps : List (DPTree ⊥)} {at : AnyTypes DP} {a : proj₁ at}
                  {ps′ : List (DPTree ⊥)}
    → (fires : FiresAt ps at a ps′)
    → (⦀list ps) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► fireRes fires
  ⦀list-fires {ps′ = p′ ∷ ps} (fires-head {p = p} {ps = ps} eqp bp allref)
    with ⦀list-refuse ps allref
  ... | inj₁ (_ , retEq) = ⦀-step-L-ret eqp bp retEq      -- tail = Skip/ret
  ... | inj₂ (g , eqg , bg) = ⦀-step-L eqp bp eqg bg        -- tail vis, refuses
  ⦀list-fires (fires-tail {p = p} {ps = ps} {ps′ = ps′} eqp bp fires)
    with ⦀list-fires-headed fires | ⦀list-fires fires
  ... | (gtl , eqtl) | sVis {f = g} eqg bg
        rewrite eqtl with eqg
  ...     | refl = ⦀-step-R eqp bp eqtl bg
  ⦀list-fires (fires-tail {p = p} eqp bp fires)
    | (gtl , eqtl) | sMixVis em _ rewrite eqtl = case em of λ ()

  -- `fireRes` is exactly the residual list `⦀list ps′`, transported to the source
  -- carrier.  This lets callers (Task 4) read the residual as a genuine `⦀list`.
  FiresAt-IProd : ∀ {ps at a ps′} → FiresAt ps at a ps′ → IProd ps ≡ IProd ps′
  FiresAt-IProd (fires-head _ _ _)     = refl
  FiresAt-IProd (fires-tail _ _ fires) = cong (⊥ ×_) (FiresAt-IProd fires)

  private
    -- Generic subst-push across `p ⦀_` (proved by `J` on an equality between abstract
    -- Sets, side-stepping the non-injectivity of `IProd`).  `sym (FiresAt-IProd
    -- (fires-tail …))` is, by definition and `cong`-`sym` commutation, `cong (⊥ ×_)
    -- (sym (FiresAt-IProd fires))`, so this lemma rewrites the goal directly.
    subst-⦀ : ∀ {ℓr ℓs} {S : Set ℓs} {X Y : Set ℓr}
                (e : X ≡ Y) (p : DPTree S) (x : DPTree X)
            → p ⦀ subst DPTree e x ≡ subst DPTree (cong (S ×_) e) (p ⦀ x)
    subst-⦀ refl p x = refl

    -- `cong`/`sym` commute (J).
    cong-sym : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} (f : A → B) {x y : A}
               (e : x ≡ y) → cong f (sym e) ≡ sym (cong f e)
    cong-sym f refl = refl

  fireRes≡ : ∀ {ps at a ps′} (fires : FiresAt ps at a ps′)
           → fireRes fires ≡ subst DPTree (sym (FiresAt-IProd fires)) (⦀list ps′)
  fireRes≡ (fires-head _ _ _) = refl
  fireRes≡ (fires-tail {p = p} {ps′ = ps′} _ _ fires)
    rewrite fireRes≡ fires | sym (cong-sym (⊥ ×_) (FiresAt-IProd fires)) =
      subst-⦀ (sym (FiresAt-IProd fires)) p (⦀list ps′)

  -------------------------------------------------------------------------------------
  -- Task 3: sync-step + τ-propagation lemmas for the interface parallel
  -- `_∥⇘_¿_⇙_`, plus a full-synchronisation `IsStuck` lemma.
  --
  -- The `_∥⇘_¿_⇙_` force (CSP.Definitions.Parallel) routes every event by alphabet
  -- membership `dec at`.  For the in-`cs` branch (`yes _`), the merged offer at
  -- (at , a) is `case (fP at a , fQ at a) of (just,just) → just (P′ ∥⇘ cs ¿ dec ⇙ Q′);
  -- _ → nothing` — i.e. both operands must synchronise, deterministically (no `Fin 2`
  -- ndbr).  These proofs mirror `αpar-sync-step`/`αpar-IsStuck`/`αpar-τ-L/R`
  -- (`CSP/Laws/AlphaParallel.agda`).
  --
  -- SIDE-CONDITION NOTE (τ lemmas).  The `_∥⇘_¿_⇙_` force gives the `sil P′ | _` clause
  -- priority over the `_ | sil Q′` clause; and a P-headed `ndbr`/`mix` lifts to an
  -- `ndbr`/`mix` composite *only when the stationary side Q is not sil-headed*
  -- (otherwise the `_ | sil Q′` clause fires, producing `sil`, and the ndbr/mix branch
  -- is not preserved).  So — exactly as Task 2's `⦀-τ-L` — `∥⇘-τ-L` carries the side
  -- condition `RetVisHead Q` (a bare `sSil` would not need it, but the uniform premise
  -- keeps all three τ-constructors in one clean statement).  `∥⇘-τ-R` needs `P` to be
  -- non-sil-headed so that the `_ | sil Q′` clause fires (the plan's `≢ sil` premise),
  -- *and* — for its ndbr/mix sub-cases — `RetVisHead P`, for the same reason as above.

  private
    -- ----- sync-step force / offer helpers (vis | vis, in-cs branch) -----
    -- force-helper: vis|vis composite is vis-headed.
    f∥vv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fP fQ}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → P .force ≡ vis fP → Q .force ≡ vis fQ
      → Σ[ f ∈ _ ] ((P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ vis f)
    f∥vv eqP eqQ rewrite eqP | eqQ = _ , refl

    -- offer-helper: in-cs synchronisation merges to `just (P′ ∥⇘…⇙ Q′)`.
    o∥sync : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q Q′ : DPTree S} {fP fQ} {at a} {f}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → cs at
      → P .force ≡ vis fP → fP at a ≡ just P′
      → Q .force ≡ vis fQ → fQ at a ≡ just Q′
      → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ vis f
      → f at a ≡ just (P′ ∥⇘ cs ¿ dec ⇙ Q′)
    o∥sync {at = at} {dec = dec} csAt eqP bP eqQ bQ fe
      rewrite eqP | eqQ with fe
    ... | refl with dec at
    ...   | yes _ rewrite bP | bQ = refl
    o∥sync csAt eqP bP eqQ bQ fe | refl | no ¬cs = ⊥-elim (¬cs csAt)

  -- Synchronisation step: an event in `cs` offered by *both* operands fires, landing
  -- in the synchronised residual `(P′ ∥⇘ cs ¿ dec ⇙ Q′)`.
  ∥⇘-sync-step : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P P′ : ITree DP (ExtI DP) R} {Q Q′ : ITree DP (ExtI DP) S}
      {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      {fP fQ} {at : AnyTypes DP} {a : proj₁ at}
    → cs at
    → P .force ≡ vis fP → fP at a ≡ just P′
    → Q .force ≡ vis fQ → fQ at a ≡ just Q′
    → (P ∥⇘ cs ¿ dec ⇙ Q) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► (P′ ∥⇘ cs ¿ dec ⇙ Q′)
  ∥⇘-sync-step csAt eqP bP eqQ bQ with f∥vv eqP eqQ
  ... | f , fe = sVis fe (o∥sync csAt eqP bP eqQ bQ fe)

  private
    -- ----- τ-L force/offer helpers (P moves, Q stationary & non-sil-headed) -----
    -- sSil from P: `sil P′ | _` clause has priority, so lifts unconditionally.
    f∥τL-sil : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q : DPTree S}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → P .force ≡ sil P′
      → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ sil (P′ ∥⇘ cs ¿ dec ⇙ Q)
    f∥τL-sil eqP rewrite eqP = refl

    -- mix-slide from P, Q ret/vis-headed: composite is mix-headed, sliding to P′ ∥⇘ Q.
    f∥τL-mix : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fP P′}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RetVisHead Q
      → P .force ≡ mix fP P′
      → Σ[ g ∈ _ ] ((P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ mix g (P′ ∥⇘ cs ¿ dec ⇙ Q))
    f∥τL-mix (inj₁ (_ , qeq)) eqP rewrite eqP | qeq = _ , refl
    f∥τL-mix (inj₂ (_ , qeq)) eqP rewrite eqP | qeq = _ , refl

    -- ndbr from P, Q ret/vis-headed: composite is ndbr-headed (∥-distribution of P).
    f∥τL-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q : DPTree S} {fP wi wa prf} {i a}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RetVisHead Q
      → P .force ≡ ndbr fP wi wa prf → fP i a ≡ just P′
      → Σ[ g ∈ _ ] Σ[ wi ∈ _ ] Σ[ wa ∈ _ ] Σ[ prf ∈ _ ]
          ((P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ ndbr g wi wa prf)
    f∥τL-ndbr (inj₁ (_ , qeq)) eqP fb rewrite eqP | qeq = _ , _ , _ , _ , refl
    f∥τL-ndbr (inj₂ (_ , qeq)) eqP fb rewrite eqP | qeq = _ , _ , _ , _ , refl

    -- … and its merged branch at (i , a) is `just (P′ ∥⇘ Q)` when `fP i a ≡ just P′`.
    o∥τL-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : DPTree R} {Q : DPTree S} {fP wi wa prf} {i a} {g wi′ wa′ prf′}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RetVisHead Q
      → P .force ≡ ndbr fP wi wa prf → fP i a ≡ just P′
      → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ ndbr g wi′ wa′ prf′
      → g i a ≡ just (P′ ∥⇘ cs ¿ dec ⇙ Q)
    o∥τL-ndbr (inj₁ (_ , qeq)) eqP fb fe rewrite eqP | qeq with fe
    ... | refl rewrite fb = refl
    o∥τL-ndbr (inj₂ (_ , qeq)) eqP fb fe rewrite eqP | qeq with fe
    ... | refl rewrite fb = refl

    -- ----- τ-R force/offer helpers (Q moves, P stationary, non-sil-headed) -----
    -- sSil from Q: needs P not sil-headed so the `_ | sil Q′` clause fires.  We drive
    -- the case-split on P's head from `RetVisHead P` (so the `_ | sil Q′` clause fires).
    f∥τR-sil : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q Q′ : DPTree S}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RetVisHead P
      → Q .force ≡ sil Q′
      → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ sil (P ∥⇘ cs ¿ dec ⇙ Q′)
    f∥τR-sil (inj₁ (_ , peq)) eqQ rewrite peq | eqQ = refl
    f∥τR-sil (inj₂ (_ , peq)) eqQ rewrite peq | eqQ = refl

    -- mix-slide from Q, P ret/vis-headed: composite is mix-headed, sliding to P ∥⇘ Q′.
    f∥τR-mix : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q : DPTree S} {fQ Q′}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RetVisHead P
      → Q .force ≡ mix fQ Q′
      → Σ[ g ∈ _ ] ((P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ mix g (P ∥⇘ cs ¿ dec ⇙ Q′))
    f∥τR-mix (inj₁ (_ , peq)) eqQ rewrite peq | eqQ = _ , refl
    f∥τR-mix (inj₂ (_ , peq)) eqQ rewrite peq | eqQ = _ , refl

    -- ndbr from Q, P ret/vis-headed: composite is ndbr-headed (∥-distribution of Q).
    f∥τR-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q Q′ : DPTree S} {fQ wi wa prf} {i a}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RetVisHead P
      → Q .force ≡ ndbr fQ wi wa prf → fQ i a ≡ just Q′
      → Σ[ g ∈ _ ] Σ[ wi ∈ _ ] Σ[ wa ∈ _ ] Σ[ prf ∈ _ ]
          ((P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ ndbr g wi wa prf)
    f∥τR-ndbr (inj₁ (_ , peq)) eqQ fb rewrite peq | eqQ = _ , _ , _ , _ , refl
    f∥τR-ndbr (inj₂ (_ , peq)) eqQ fb rewrite peq | eqQ = _ , _ , _ , _ , refl

    o∥τR-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : DPTree R} {Q Q′ : DPTree S} {fQ wi wa prf} {i a} {g wi′ wa′ prf′}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RetVisHead P
      → Q .force ≡ ndbr fQ wi wa prf → fQ i a ≡ just Q′
      → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ ndbr g wi′ wa′ prf′
      → g i a ≡ just (P ∥⇘ cs ¿ dec ⇙ Q′)
    o∥τR-ndbr (inj₁ (_ , peq)) eqQ fb fe rewrite peq | eqQ with fe
    ... | refl rewrite fb = refl
    o∥τR-ndbr (inj₂ (_ , peq)) eqQ fb fe rewrite peq | eqQ with fe
    ... | refl rewrite fb = refl

  -- A τ from P lifts to a τ of the parallel (Q stationary, ret/vis-headed).
  ∥⇘-τ-L : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P P′ : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S}
      {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
    → RetVisHead Q
    → P ─[ τ ]─► P′ → (P ∥⇘ cs ¿ dec ⇙ Q) ─[ τ ]─► (P′ ∥⇘ cs ¿ dec ⇙ Q)
  ∥⇘-τ-L _   (sSil eqP)              = sSil (f∥τL-sil eqP)
  ∥⇘-τ-L rvQ (sNdbr {i = i} {a = a} eqP fb)
    with f∥τL-ndbr rvQ eqP fb
  ... | g , wi , wa , prf , fe = sNdbr fe (o∥τL-ndbr rvQ eqP fb fe)
  ∥⇘-τ-L rvQ (sMixSlide eqP)
    with f∥τL-mix rvQ eqP
  ... | g , fe = sMixSlide fe

  -- A τ from Q lifts to a τ of the parallel (P stationary, non-sil-headed; ndbr/mix
  -- sub-cases additionally require P ret/vis-headed via `RetVisHead P`).
  ∥⇘-τ-R : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P : ITree DP (ExtI DP) R} {Q Q′ : ITree DP (ExtI DP) S}
      {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
    → RetVisHead P
    → Q ─[ τ ]─► Q′ → (P ∥⇘ cs ¿ dec ⇙ Q) ─[ τ ]─► (P ∥⇘ cs ¿ dec ⇙ Q′)
  ∥⇘-τ-R rvP (sSil eqQ)              = sSil (f∥τR-sil rvP eqQ)
  ∥⇘-τ-R rvP (sNdbr {i = i} {a = a} eqQ fb)
    with f∥τR-ndbr rvP eqQ fb
  ... | g , wi , wa , prf , fe = sNdbr fe (o∥τR-ndbr rvP eqQ fb fe)
  ∥⇘-τ-R rvP (sMixSlide eqQ)
    with f∥τR-mix rvP eqQ
  ... | g , fe = sMixSlide fe

  -------------------------------------------------------------------------------------
  -- Full-synchronisation `IsStuck`: when both operands are `vis`-headed, synchronise on
  -- *everything* (`syncAll`), and the two offer functions are pointwise disjoint (at
  -- every (at , a) at least one side refuses), the composite can fire no event.
  -- Mirrors `αpar-IsStuck` (the `yes , yes` routing of `Blocked`).
  ∥⇘-full-stuck : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S} {fP fQ}
    → P .force ≡ vis fP → Q .force ≡ vis fQ
    → (∀ (at : AnyTypes DP) (a : proj₁ at) → (fP at a ≡ nothing) ⊎ (fQ at a ≡ nothing))
    → IsStuck (P ∥⇘ syncAll ¿ syncAll-dec ⇙ Q)
  -- silent / ndbr / mix / ret steps: force is `vis`, contradicting the head equation.
  ∥⇘-full-stuck eqP eqQ disj (sRet eq)      rewrite eqP | eqQ = case eq of λ ()
  ∥⇘-full-stuck eqP eqQ disj (sSil eq)      rewrite eqP | eqQ = case eq of λ ()
  ∥⇘-full-stuck eqP eqQ disj (sNdbr eq _)   rewrite eqP | eqQ = case eq of λ ()
  ∥⇘-full-stuck eqP eqQ disj (sMixSlide eq) rewrite eqP | eqQ = case eq of λ ()
  ∥⇘-full-stuck eqP eqQ disj (sMixVis eq _) rewrite eqP | eqQ = case eq of λ ()
  -- visible step: under `syncAll-dec at = yes tt`, the merged offer at (at , a) is
  -- `case (fP at a , fQ at a) of (just,just)→just…; _→nothing`; disjointness forces a
  -- `nothing` factor, hence the merged offer is `nothing`, contradicting `branch-eq`.
  ∥⇘-full-stuck {fP = fP} {fQ = fQ} eqP eqQ disj
                (sVis {at = at} {a = a} feq branch-eq)
    rewrite eqP | eqQ with feq
  ... | refl with fP at a | fQ at a | disj at a
  ...   | nothing  | _        | inj₁ refl = case branch-eq of λ ()
  ...   | just _   | nothing  | inj₂ refl = case branch-eq of λ ()
  ...   | nothing  | just _   | inj₂ ()
  ...   | just _   | just _   | inj₁ ()

  -------------------------------------------------------------------------------------
  -- Task 4: the symmetric SYSTEM′ reaches a deadlock by `n` synchronised left-picks.
  --
  -- Step A.  Generalise `loop0-prefix-step` to fire ANY vis-headed loop0 body to a
  -- given offer.  FORK's body is a `□` (not a single prefix), so the single-prefix
  -- lemma does not apply directly.

  -- The loop step function for a bare `body` (loop0 body = iter (loopStep0 body) tt).
  loopStep0 : (body : ITree DP (ExtI DP) (⊤ {lzero}))
            → ⊤ {lzero} → ITree DP (ExtI DP) (⊤ {lzero} ⊎ ⊥)
  loopStep0 body = λ _ → body >>= loop-k

  -- The residual after firing the offer `b` of a vis-headed loop0 body.
  loop0-body-tail : (body : ITree DP (ExtI DP) (⊤ {lzero}))
                  → ITree DP (ExtI DP) (⊤ {lzero}) → ITree DP (ExtI DP) ⊥
  loop0-body-tail body b = iter-bind (b >>= loop-k) (loopStep0 body)

  loop0-body-step :
    ∀ {at : AnyTypes DP} {a : proj₁ at}
      {fb : (at′ : AnyTypes DP) → ContinueType at′ (Maybe (ITree DP (ExtI DP) (⊤ {lzero})))}
      {b : ITree DP (ExtI DP) (⊤ {lzero})}
      (body : ITree DP (ExtI DP) (⊤ {lzero}))
    → body .force ≡ vis fb → fb at a ≡ just b
    → loop0 body
        ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
      loop0-body-tail body b
  loop0-body-step {at = at} {a = a} {fb = fb} {b = b} body eqb fbja =
    sVis {at = at} {a = a}
      (iter-bind-force-vis (body >>= loop-k) (loopStep0 body)
        (bind-force-vis body loop-k eqb))
      (iter-bind-cont-vis-just (loopStep0 body)
        (bind-cont-vis loop-k fb) at a
        (bind-cont-vis-just loop-k fb at a fbja))

  -------------------------------------------------------------------------------------
  -- Elementary offer/refusal facts for `Prefix-cont` at DP `picks` events.

  -- The event-type wrapper of a `picks i f`.
  pAt : Phil → Fork → AnyTypes DP
  pAt i f = (⊤ {lzero} , picks i f)

  -- `picks i f` offers a `just` exactly at its own event-type.
  prefix-picks-offer :
    ∀ {ℓr} {R : Set ℓr} (i f : Fin n) (P : ⊤ {lzero} → ITree DP (ExtI DP) R)
    → Prefix-cont (picks i f) P (pAt i f) tt ≡ just (P tt)
  prefix-picks-offer i f P = Prefix-cont-just (picks i f) P tt

  -- `picks i f` refuses `picks i′ f′` whenever the indices differ.
  prefix-picks-refuse :
    ∀ {ℓr} {R : Set ℓr} (i f i′ f′ : Fin n) (P : ⊤ {lzero} → ITree DP (ExtI DP) R)
    → ¬ ((i ≡ i′) × (f ≡ f′))
    → Prefix-cont (picks i f) P (pAt i′ f′) tt ≡ nothing
  prefix-picks-refuse i f i′ f′ P ¬eq
    with DP-AnyTypes-≟ (⊤ {lzero} , picks i f) (⊤ {lzero} , picks i′ f′)
  ... | yes refl = ⊥-elim (¬eq (refl , refl))
  ... | no  _    = refl

  -- `picks` refuses every `putsdown` event.
  prefix-picks-refuse-pd :
    ∀ {ℓr} {R : Set ℓr} (i f i′ f′ : Fin n) (P : ⊤ {lzero} → ITree DP (ExtI DP) R)
    → Prefix-cont (picks i f) P (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  prefix-picks-refuse-pd i f i′ f′ P
    with DP-AnyTypes-≟ (⊤ {lzero} , picks i f) (⊤ {lzero} , putsdown i′ f′)
  ... | no _ = refl

  -- `putsdown` refuses every `picks` event.
  prefix-putsdown-refuse-pk :
    ∀ {ℓr} {R : Set ℓr} (i f i′ f′ : Fork) (P : ⊤ {lzero} → ITree DP (ExtI DP) R)
    → Prefix-cont (putsdown i f) P (pAt i′ f′) tt ≡ nothing
  prefix-putsdown-refuse-pk i f i′ f′ P
    with DP-AnyTypes-≟ (⊤ {lzero} , putsdown i f) (⊤ {lzero} , picks i′ f′)
  ... | no _ = refl

  -------------------------------------------------------------------------------------
  -- Ring fact: predecessor has no fixed point (n = suc (suc m) ≥ 2), so a fork's two
  -- branches `picks j j` and `picks (j ⊖1) j` are genuinely distinct events.
  open import Data.Nat.Properties using (n<1+n; 1+n≢n)
  open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-inject₁)

  ⊖1-≢ : ∀ (j : Fork) → (j ⊖1) ≢ j
  ⊖1-≢ Fin.zero    eq =
    case trans (sym (toℕ-fromℕ< (n<1+n (suc m)))) (cong Fin.toℕ eq) of λ ()
  ⊖1-≢ (Fin.suc i) eq =
    1+n≢n (sym (trans (sym (toℕ-inject₁ i)) (cong Fin.toℕ eq)))

  -------------------------------------------------------------------------------------
  -- Step A′.  Force + offer/refuse of a vis-headed `loop0`.  `loop0 body` is vis-headed
  -- offering exactly `body`'s events; its offer at `(at , a)` is `just (residual)` /
  -- `nothing` precisely as `body`'s `fb` is.  This packages everything a `FiresAt`
  -- proof needs for a single `loop0` component.

  -- The (named) offer function of `loop0 body` when `body .force ≡ vis fb`.
  loop0-fb : (body : ITree DP (ExtI DP) (⊤ {lzero}))
           → ((at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) (⊤ {lzero}))))
           → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))
  loop0-fb body fb = iter-bind-cont-vis (loopStep0 body) (bind-cont-vis loop-k fb)

  loop0-force :
    ∀ {fb} (body : ITree DP (ExtI DP) (⊤ {lzero}))
    → body .force ≡ vis fb
    → (loop0 body) .force ≡ vis (loop0-fb body fb)
  loop0-force {fb} body eqb =
    iter-bind-force-vis (body >>= loop-k) (loopStep0 body)
      (bind-force-vis body loop-k eqb)

  loop0-offer-just :
    ∀ {at : AnyTypes DP} {a : proj₁ at} {b}
      (body : ITree DP (ExtI DP) (⊤ {lzero}))
      (fb : (at′ : AnyTypes DP) → ContinueType at′ (Maybe (ITree DP (ExtI DP) (⊤ {lzero}))))
    → fb at a ≡ just b
    → loop0-fb body fb at a ≡ just (loop0-body-tail body b)
  loop0-offer-just {at} {a} body fb fbja =
    iter-bind-cont-vis-just (loopStep0 body) (bind-cont-vis loop-k fb) at a
      (bind-cont-vis-just loop-k fb at a fbja)

  loop0-offer-nothing :
    ∀ {at : AnyTypes DP} {a : proj₁ at}
      (body : ITree DP (ExtI DP) (⊤ {lzero}))
      (fb : (at′ : AnyTypes DP) → ContinueType at′ (Maybe (ITree DP (ExtI DP) (⊤ {lzero}))))
    → fb at a ≡ nothing
    → loop0-fb body fb at a ≡ nothing
  loop0-offer-nothing {at} {a} body fb fbn
    rewrite bind-cont-vis-nothing loop-k fb at a fbn = refl

  -------------------------------------------------------------------------------------
  -- Step A″.  External-choice `□` of two vis-headed processes is vis-headed, merging
  -- the two offer functions with `mergeVis`/`mergeMaybe`.  (FORK's body is such a `□`.)

  □-force-vv :
    ∀ {fP fQ} (P Q : ITree DP (ExtI DP) (⊤ {lzero}))
    → P .force ≡ vis fP → Q .force ≡ vis fQ
    → (P □ Q) .force ≡ vis (λ Ae → mergeVis (fP Ae) (fQ Ae))
  □-force-vv P Q eqP eqQ rewrite eqP | eqQ = refl

  -- `□`'s merged offer when the LEFT branch offers and the RIGHT refuses.
  □-offer-L :
    ∀ {at : AnyTypes DP}
      (fP fQ : (at′ : AnyTypes DP) → ContinueType at′ (Maybe (ITree DP (ExtI DP) (⊤ {lzero}))))
      (a : proj₁ at) {p}
    → fP at a ≡ just p → fQ at a ≡ nothing
    → (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just p
  □-offer-L {at} fP fQ a eP eQ
    rewrite eP | eQ = refl

  -- `□`'s merged offer when BOTH branches refuse → refuse.
  □-offer-refuse :
    ∀ {at : AnyTypes DP}
      (fP fQ : (at′ : AnyTypes DP) → ContinueType at′ (Maybe (ITree DP (ExtI DP) (⊤ {lzero}))))
      (a : proj₁ at)
    → fP at a ≡ nothing → fQ at a ≡ nothing
    → (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ nothing
  □-offer-refuse {at} fP fQ a eP eQ
    rewrite eP | eQ = refl

  -------------------------------------------------------------------------------------
  -- Step B.  Per-component firing of `picks i i`.
  --
  -- The symmetric philosopher / the fork bodies and their post-`picks.i.i` residuals.

  -- PHIL (symmetric) body and its tail-after-first-pick.
  Prest : Phil → ITree DP (ExtI DP) (⊤ {lzero})
  Prest i = picks i (i ⊕1) ⟶₀ putsdown i (i ⊕1) ⟶₀ putsdown i i ⟶₀ Skip

  Pbody : Phil → ITree DP (ExtI DP) (⊤ {lzero})
  Pbody i = picks i i ⟶₀ Prest i

  philRes : Phil → ITree DP (ExtI DP) ⊥
  philRes i = loop0-body-tail (Pbody i) (Prest i)

  -- FORK body branches and tail-after-first-pick.
  Fbr1 : Fork → ITree DP (ExtI DP) (⊤ {lzero})
  Fbr1 j = picks j j ⟶₀ putsdown j j ⟶₀ Skip

  Fbr2 : Fork → ITree DP (ExtI DP) (⊤ {lzero})
  Fbr2 j = picks (j ⊖1) j ⟶₀ putsdown (j ⊖1) j ⟶₀ Skip

  Fbody : Fork → ITree DP (ExtI DP) (⊤ {lzero})
  Fbody j = Fbr1 j □ Fbr2 j

  forkRes : Fork → ITree DP (ExtI DP) ⊥
  forkRes j = loop0-body-tail (Fbody j) (putsdown j j ⟶₀ Skip)

  -- Sanity: the model's PHIL/FORK ARE the above loop0s (definitional check).
  _ : ∀ i → PHIL symFirst symSecond i ≡ loop0 (Pbody i)
  _ = λ i → refl

  _ : ∀ j → FORK j ≡ loop0 (Fbody j)
  _ = λ j → refl

  -------------------------------------------------------------------------------------
  -- Component force witnesses (every component is vis-headed, advanced or not).

  -- An unadvanced philosopher.
  PHIL-force : ∀ i → (loop0 (Pbody i)) .force
                   ≡ vis (loop0-fb (Pbody i) (Prefix-cont (picks i i) (λ _ → Prest i)))
  PHIL-force i = loop0-force (Pbody i) refl

  -- An advanced philosopher (after picks i i).
  philRes-fb : ∀ i → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))
  philRes-fb i = iter-bind-cont-vis (loopStep0 (Pbody i))
                   (bind-cont-vis loop-k
                     (Prefix-cont (picks i (i ⊕1))
                       (λ _ → putsdown i (i ⊕1) ⟶₀ putsdown i i ⟶₀ Skip)))

  philRes-force : ∀ i → (philRes i) .force ≡ vis (philRes-fb i)
  philRes-force i =
    iter-bind-force-vis (Prest i >>= loop-k) (loopStep0 (Pbody i))
      (bind-force-vis (Prest i) loop-k refl)

  -- An unadvanced fork.
  FORK-fb : ∀ j → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) (⊤ {lzero})))
  FORK-fb j = λ Ae → mergeVis (Prefix-cont (picks j j)      (λ _ → putsdown j j      ⟶₀ Skip) Ae)
                              (Prefix-cont (picks (j ⊖1) j) (λ _ → putsdown (j ⊖1) j ⟶₀ Skip) Ae)

  FORK-body-force : ∀ j → (Fbody j) .force ≡ vis (FORK-fb j)
  FORK-body-force j = □-force-vv (Fbr1 j) (Fbr2 j) refl refl

  FORK-force : ∀ j → (loop0 (Fbody j)) .force ≡ vis (loop0-fb (Fbody j) (FORK-fb j))
  FORK-force j = loop0-force (Fbody j) (FORK-body-force j)

  -- An advanced fork (after granting picks j j to its own philosopher) offers putsdown.
  forkRes-fb : ∀ j → (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))
  forkRes-fb j = iter-bind-cont-vis (loopStep0 (Fbody j))
                   (bind-cont-vis loop-k (Prefix-cont (putsdown j j) (λ _ → Skip)))

  forkRes-force : ∀ j → (forkRes j) .force ≡ vis (forkRes-fb j)
  forkRes-force j =
    iter-bind-force-vis ((putsdown j j ⟶₀ Skip) >>= loop-k) (loopStep0 (Fbody j))
      (bind-force-vis (putsdown j j ⟶₀ Skip) loop-k refl)

  -------------------------------------------------------------------------------------
  -- Component offer/refuse facts at the event `picks k k`.

  -- An unadvanced philosopher `k` FIRES `picks k k` to `philRes k`.
  PHIL-fires : ∀ k
    → loop0-fb (Pbody k) (Prefix-cont (picks k k) (λ _ → Prest k)) (pAt k k) tt
        ≡ just (philRes k)
  PHIL-fires k =
    loop0-offer-just (Pbody k) (Prefix-cont (picks k k) (λ _ → Prest k))
      (prefix-picks-offer k k (λ _ → Prest k))

  -- An unadvanced philosopher `i` (i ≢ k) REFUSES `picks k k`.
  PHIL-refuses : ∀ i k → i ≢ k
    → loop0-fb (Pbody i) (Prefix-cont (picks i i) (λ _ → Prest i)) (pAt k k) tt ≡ nothing
  PHIL-refuses i k i≢k =
    loop0-offer-nothing (Pbody i) (Prefix-cont (picks i i) (λ _ → Prest i))
      (prefix-picks-refuse i i k k (λ _ → Prest i) (λ { (e , _) → i≢k e }))

  -- An advanced philosopher `i` (i ≢ k) REFUSES `picks k k`.
  philRes-refuses : ∀ i k → i ≢ k → philRes-fb i (pAt k k) tt ≡ nothing
  philRes-refuses i k i≢k =
    loop0-offer-nothing (Pbody i)
      (Prefix-cont (picks i (i ⊕1)) (λ _ → putsdown i (i ⊕1) ⟶₀ putsdown i i ⟶₀ Skip))
      (prefix-picks-refuse i (i ⊕1) k k _ (λ { (e , _) → i≢k e }))

  -- An unadvanced fork `k` FIRES `picks k k` (its own-philosopher branch) to `forkRes k`.
  FORK-fires : ∀ k
    → loop0-fb (Fbody k) (FORK-fb k) (pAt k k) tt ≡ just (forkRes k)
  FORK-fires k =
    loop0-offer-just (Fbody k) (FORK-fb k)
      (□-offer-L (Prefix-cont (picks k k)      (λ _ → putsdown k k      ⟶₀ Skip))
                 (Prefix-cont (picks (k ⊖1) k) (λ _ → putsdown (k ⊖1) k ⟶₀ Skip))
                 tt
                 (prefix-picks-offer k k (λ _ → putsdown k k ⟶₀ Skip))
                 (prefix-picks-refuse (k ⊖1) k k k (λ _ → putsdown (k ⊖1) k ⟶₀ Skip)
                   (λ { (e , _) → ⊖1-≢ k e })))

  -- An unadvanced fork `j` (j ≢ k) REFUSES `picks k k`.
  FORK-refuses : ∀ j k → j ≢ k
    → loop0-fb (Fbody j) (FORK-fb j) (pAt k k) tt ≡ nothing
  FORK-refuses j k j≢k =
    loop0-offer-nothing (Fbody j) (FORK-fb j)
      (□-offer-refuse (Prefix-cont (picks j j)      (λ _ → putsdown j j      ⟶₀ Skip))
                      (Prefix-cont (picks (j ⊖1) j) (λ _ → putsdown (j ⊖1) j ⟶₀ Skip))
                      tt
                      (prefix-picks-refuse j j k k (λ _ → putsdown j j ⟶₀ Skip)
                        (λ { (e , _) → j≢k e }))
                      (prefix-picks-refuse (j ⊖1) j k k (λ _ → putsdown (j ⊖1) j ⟶₀ Skip)
                        (λ { (_ , e) → j≢k e })))

  -- An advanced fork `j` REFUSES every `picks` event (it offers only putsdown).
  forkRes-refuses : ∀ j k → forkRes-fb j (pAt k k) tt ≡ nothing
  forkRes-refuses j k =
    loop0-offer-nothing {at = pAt k k} {a = tt} (Fbody j)
      (Prefix-cont (putsdown j j) (λ _ → Skip))
      (prefix-putsdown-refuse-pk j j k k (λ _ → Skip))

  -------------------------------------------------------------------------------------
  -- Step C.  Generic `FiresAt` builder: a single component fires inside an enclosing
  -- list whose other components all refuse the event.

  -- `FiresAt` for `before ++ p ∷ after` where `before`/`after` all refuse and `p` fires.
  fires-split :
    ∀ (before : List (DPTree ⊥)) {p p′} {fp} {at : AnyTypes DP} {a : proj₁ at}
      {after : List (DPTree ⊥)}
    → AllRefuse before at a
    → p .force ≡ vis fp → fp at a ≡ just p′
    → AllRefuse after at a
    → FiresAt (before ++ p ∷ after) at a (before ++ p′ ∷ after)
  fires-split []           _              eqp bp aft = fires-head eqp bp aft
  fires-split (q ∷ before) ((fq , eqq , bq) ∷ bref) eqp bp aft =
    fires-tail eqq bq (fires-split before bref eqp bp aft)

  -- A vis-headed process's `ev`-step must come from its `vis` offer (not a `mix`).
  ev-offer-from-vis :
    ∀ {ℓr} {R : Set ℓr} {P : ITree DP (ExtI DP) R} {P′}
      {g} {at : AnyTypes DP} {a : proj₁ at}
    → P .force ≡ vis g
    → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P′
    → g at a ≡ just P′
  ev-offer-from-vis eqv (sVis eqf bf)
    with trans (sym eqf) eqv
  ... | refl = bf
  ev-offer-from-vis eqv (sMixVis eqm _) = case trans (sym eqm) eqv of λ ()

  -- Step-form synchronisation wrapper: two `ev e` steps from vis-headed operands sync
  -- into one step of the full-sync parallel.
  ∥⇘-sync-step′ :
    ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P P′ : ITree DP (ExtI DP) R} {Q Q′ : ITree DP (ExtI DP) S}
      {gP gQ} {at : AnyTypes DP} {a : proj₁ at}
    → P .force ≡ vis gP → Q .force ≡ vis gQ
    → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P′
    → Q ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Q′
    → (P ∥⇘ syncAll ¿ syncAll-dec ⇙ Q)
        ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
      (P′ ∥⇘ syncAll ¿ syncAll-dec ⇙ Q′)
  ∥⇘-sync-step′ eqP eqQ sP sQ =
    ∥⇘-sync-step tt eqP (ev-offer-from-vis eqP sP) eqQ (ev-offer-from-vis eqQ sQ)

  -------------------------------------------------------------------------------------
  -- Step D.  A τ-free big-step (sequence of ev-steps).  Our `loop0`-based components
  -- never offer a τ between picks (Task 1's `iter` has no Tau guard), so the whole
  -- deadlock run is `n` consecutive ev-steps with NO τ.  Working with this τ-free
  -- relation keeps the per-block / combine inductions in clean lock-step (no `bTau`
  -- interleavings to invert), and it embeds into `═⟨_⟩═►` trivially.

  -- The τ-free step bakes in vis-headedness of the source (offer ≡ just), so no `mix`
  -- case ever arises and the chain inducts cleanly.
  -- The trace is a list of plain (R-independent) `Event DP`s; `⟹→═` maps `evl` over it.
  data _⟹⟨_⟩_ {R : Set lzero}
    : ITree DP (ExtI DP) R → List (Event DP) → ITree DP (ExtI DP) R → Set (lsuc lzero) where
    ⟹nil  : ∀ {t} → t ⟹⟨ [] ⟩ t
    ⟹cons : ∀ {t t′ t″ A e a els} {fQ}
          → t .force ≡ vis fQ → fQ (A , e) a ≡ just t′
          → t′ ⟹⟨ els ⟩ t″
          → t ⟹⟨ evLabel A e a ∷ els ⟩ t″

  -- Embed the τ-free big-step into `═⟨_⟩═►` (mapping `evl` over the trace).
  ⟹→═ : ∀ {R : Set lzero} {t t′ : ITree DP (ExtI DP) R} {els}
       → t ⟹⟨ els ⟩ t′ → t ═⟨ map evl els ⟩═► t′
  ⟹→═ ⟹nil                = bNil
  ⟹→═ (⟹cons eqf bf rest) = bStep (sVis eqf bf) (⟹→═ rest)

  -- `p` (vis-headed via `fp`) refuses the event `ev`.
  RefusesAt : (fp : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
            → Event DP → Set (lsuc lzero)
  RefusesAt fp (evLabel A e a) = fp (A , e) a ≡ nothing

  -- Lift a τ-free big-step through a vis-headed left `⦀`-head `p` that refuses every
  -- event occurring in the trace `els`.
  lift-⦀R :
    ∀ {S : Set lzero} {p : DPTree ⊥} {fp} {Q Q′ : DPTree S} {els}
    → p .force ≡ vis fp
    → All (RefusesAt fp) els
    → Q ⟹⟨ els ⟩ Q′
    → (p ⦀ Q) ⟹⟨ els ⟩ (p ⦀ Q′)
  lift-⦀R _ _ ⟹nil = ⟹nil
  lift-⦀R {fp = fp} eqp (pr ∷ prs) (⟹cons {A = A} {e = e} {a = a} eqQ bQ rest)
    with f⦀vv eqp eqQ | ⦀-step-R {at = A , e} {a = a} eqp pr eqQ bQ
  ... | _ , feq | sVis eqf bf = ⟹cons eqf bf (lift-⦀R eqp prs rest)
  ... | _ , feq | sMixVis eqm _ = ⊥-elim (vis≢mix (trans (sym feq) eqm))

  -------------------------------------------------------------------------------------
  -- Step E.  Per-block firing of all left-picks.

  -- The left-pick trace for an index list.
  picksTrace : List Phil → List (Event DP)
  picksTrace = map (λ i → evLabel (⊤ {lzero}) (picks i i) tt)

  -- `i ∉ rest`: a fresh index w.r.t. a list (drives the others-refuse facts).
  Fresh : Phil → List Phil → Set _
  Fresh i rest = All (λ k → i ≢ k) rest

  -- Distinct list: every head is fresh against its tail.
  Distinct : List Phil → Set _
  Distinct []        = ⊤ {lzero}
  Distinct (i ∷ rest) = Fresh i rest × Distinct rest

  -- An advanced philosopher `i` (vis-headed via `philRes-fb i`) refuses every
  -- left-pick `picks k k` with `k ≢ i` (i.e. every event of `picksTrace rest`, given
  -- `i` is fresh against `rest`).
  philRes-refuses-trace :
    ∀ i (rest : List Phil) → Fresh i rest
    → All (RefusesAt (philRes-fb i)) (picksTrace rest)
  philRes-refuses-trace i []          _              = []
  philRes-refuses-trace i (k ∷ rest) (i≢k ∷ fr) =
    philRes-refuses i k i≢k ∷ philRes-refuses-trace i rest fr

  -- An advanced fork `i` (vis-headed via `forkRes-fb i`) refuses every left-pick.
  forkRes-refuses-trace :
    ∀ i (rest : List Phil)
    → All (RefusesAt (forkRes-fb i)) (picksTrace rest)
  forkRes-refuses-trace i []         = []
  forkRes-refuses-trace i (k ∷ rest) =
    forkRes-refuses i k ∷ forkRes-refuses-trace i rest

  -- The unadvanced-tail refuses `picks i i` (each other unadvanced philosopher k ≢ i).
  phils-tail-refuse :
    ∀ i (rest : List Phil) → Fresh i rest
    → AllRefuse (map (λ k → loop0 (Pbody k)) rest) (pAt i i) tt
  phils-tail-refuse i []         _           = []
  phils-tail-refuse i (k ∷ rest) (i≢k ∷ fr) =
    (_ , PHIL-force k , PHIL-refuses k i (λ e → i≢k (sym e)))
      ∷ phils-tail-refuse i rest fr

  forks-tail-refuse :
    ∀ i (rest : List Phil) → Fresh i rest
    → AllRefuse (map (λ k → loop0 (Fbody k)) rest) (pAt i i) tt
  forks-tail-refuse i []         _           = []
  forks-tail-refuse i (k ∷ rest) (i≢k ∷ fr) =
    (_ , FORK-force k , FORK-refuses k i (λ e → i≢k (sym e)))
      ∷ forks-tail-refuse i rest fr

  -- The all-advanced PHILS / FORKS residuals, built at the SOURCE carrier
  -- `IProd (map (loop0∘body) rest)` (so the firing transition stays homogeneous — the
  -- same trick `fireRes` uses: advance the head, keep the carrier `⊥ × …`).
  allAdvP : (rest : List Phil) → DPTree (IProd (map (λ i → loop0 (Pbody i)) rest))
  allAdvP []         = Skip
  allAdvP (i ∷ rest) = philRes i ⦀ allAdvP rest

  allAdvF : (rest : List Fork) → DPTree (IProd (map (λ j → loop0 (Fbody j)) rest))
  allAdvF []         = Skip
  allAdvF (j ∷ rest) = forkRes j ⦀ allAdvF rest

  -- The PHILS block fires all its left-picks: `⦀list (map (loop0∘Pbody) rest)` advances
  -- to `allAdvP rest` over `picksTrace rest` (τ-free).
  phils-chain :
    ∀ (rest : List Phil) → Distinct rest
    → ⦀list (map (λ i → loop0 (Pbody i)) rest)
        ⟹⟨ picksTrace rest ⟩
      allAdvP rest
  phils-chain []          _              = ⟹nil
  phils-chain (i ∷ rest) (fr , dist)
    with ⦀list-refuse (map (λ k → loop0 (Pbody k)) rest) (phils-tail-refuse i rest fr)
       | lift-⦀R (philRes-force i) (philRes-refuses-trace i rest fr) (phils-chain rest dist)
  ... | inj₁ (_ , retEq) | lifted
        with f⦀vr (PHIL-force i) retEq | ⦀-step-L-ret (PHIL-force i) (PHIL-fires i) retEq
  ...     | _ , feq | sVis eqf bf    = ⟹cons eqf bf lifted
  ...     | _ , feq | sMixVis eqm _  = ⊥-elim (vis≢mix (trans (sym feq) eqm))
  phils-chain (i ∷ rest) (fr , dist)
      | inj₂ (_ , eqg , bg) | lifted
        with f⦀vv (PHIL-force i) eqg | ⦀-step-L (PHIL-force i) (PHIL-fires i) eqg bg
  ...     | _ , feq | sVis eqf bf    = ⟹cons eqf bf lifted
  ...     | _ , feq | sMixVis eqm _  = ⊥-elim (vis≢mix (trans (sym feq) eqm))

  -- The FORKS block fires all its left-picks, advancing to `allAdvF rest`.
  forks-chain :
    ∀ (rest : List Fork) → Distinct rest
    → ⦀list (map (λ j → loop0 (Fbody j)) rest)
        ⟹⟨ picksTrace rest ⟩
      allAdvF rest
  forks-chain []          _              = ⟹nil
  forks-chain (i ∷ rest) (fr , dist)
    with ⦀list-refuse (map (λ k → loop0 (Fbody k)) rest) (forks-tail-refuse i rest fr)
       | lift-⦀R (forkRes-force i) (forkRes-refuses-trace i rest) (forks-chain rest dist)
  ... | inj₁ (_ , retEq) | lifted
        with f⦀vr (FORK-force i) retEq | ⦀-step-L-ret (FORK-force i) (FORK-fires i) retEq
  ...     | _ , feq | sVis eqf bf    = ⟹cons eqf bf lifted
  ...     | _ , feq | sMixVis eqm _  = ⊥-elim (vis≢mix (trans (sym feq) eqm))
  forks-chain (i ∷ rest) (fr , dist)
      | inj₂ (_ , eqg , bg) | lifted
        with f⦀vv (FORK-force i) eqg | ⦀-step-L (FORK-force i) (FORK-fires i) eqg bg
  ...     | _ , feq | sVis eqf bf    = ⟹cons eqf bf lifted
  ...     | _ , feq | sMixVis eqm _  = ⊥-elim (vis≢mix (trans (sym feq) eqm))

  -------------------------------------------------------------------------------------
  -- Step F.  Combine two τ-free block chains over the SAME trace into one synchronised
  -- system chain (every event fires in BOTH operands, so synchronises under full sync).

  -- vis|vis full-sync parallel is vis-headed.
  ∥⇘-vis : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S} {fP fQ}
    → P .force ≡ vis fP → Q .force ≡ vis fQ
    → Σ[ f ∈ _ ] ((P ∥⇘ syncAll ¿ syncAll-dec ⇙ Q) .force ≡ vis f)
  ∥⇘-vis eqP eqQ rewrite eqP | eqQ = _ , refl

  combine-sync :
    ∀ {R S : Set lzero} {P P′ : DPTree R} {Q Q′ : DPTree S} {els}
    → P ⟹⟨ els ⟩ P′ → Q ⟹⟨ els ⟩ Q′
    → (P ∥⇘ syncAll ¿ syncAll-dec ⇙ Q) ⟹⟨ els ⟩ (P′ ∥⇘ syncAll ¿ syncAll-dec ⇙ Q′)
  combine-sync ⟹nil ⟹nil = ⟹nil
  combine-sync (⟹cons {A = A} {e = e} {a = a} eqfP bfP restP)
               (⟹cons eqfQ bfQ restQ)
    with ∥⇘-vis eqfP eqfQ | ∥⇘-sync-step′ {at = A , e} {a = a} eqfP eqfQ (sVis eqfP bfP) (sVis eqfQ bfQ)
  ... | _ , feq | sVis eqf bf   = ⟹cons eqf bf (combine-sync restP restQ)
  ... | _ , feq | sMixVis eqm _ = ⊥-elim (vis≢mix (trans (sym feq) eqm))

  -------------------------------------------------------------------------------------
  -- `allPhils = toList (tabulate id)` is `Distinct` (it lists each `Fin n` exactly once).

  -- Every element of `toList (tabulate g)` differs from `x`, given `x ≢ g a` always.
  all-fresh-tabulate :
    ∀ {k} (x : Phil) (g : Fin k → Phil) → (∀ a → x ≢ g a)
    → All (λ y → x ≢ y) (toList (tabulate g))
  all-fresh-tabulate {zero}  x g _   = []
  all-fresh-tabulate {suc k} x g xne =
    xne Fin.zero ∷ all-fresh-tabulate x (g ∘ Fin.suc) (λ a → xne (Fin.suc a))

  distinct-tabulate :
    ∀ {k} (g : Fin k → Phil) → (∀ {a b} → g a ≡ g b → a ≡ b)
    → Distinct (toList (tabulate g))
  distinct-tabulate {zero}  g _   = tt
  distinct-tabulate {suc k} g inj =
    all-fresh-tabulate (g Fin.zero) (g ∘ Fin.suc)
      (λ a eq → case inj eq of λ ())
    , distinct-tabulate (g ∘ Fin.suc) (λ eq → case inj eq of λ { refl → refl })

  allPhils-distinct : Distinct allPhils
  allPhils-distinct = distinct-tabulate (λ i → i) (λ eq → eq)

  -------------------------------------------------------------------------------------
  -- THE CRUX.  The symmetric system reaches a fully-left-picked state via `n`
  -- synchronised `picks i i` events (one per philosopher/fork), with no τ in between.

  -- The fully-advanced ("everyone holds their left fork") deadlock state.
  PHILS′ : DPTree (IProd (map (λ i → loop0 (Pbody i)) allPhils))
  PHILS′ = allAdvP allPhils

  FORKS′ : DPTree (IProd (map (λ j → loop0 (Fbody j)) allPhils))
  FORKS′ = allAdvF allPhils

  deadlock-reachable :
    SYSTEM′sym ═⟨ map evl (picksTrace allPhils) ⟩═►
      (PHILS′ ∥⇘ syncAll ¿ syncAll-dec ⇙ FORKS′)
  deadlock-reachable =
    ⟹→═ (combine-sync (phils-chain allPhils allPhils-distinct)
                        (forks-chain allPhils allPhils-distinct))

  -------------------------------------------------------------------------------------
  -- Task 5.  The all-hold-left state is `IsStuck`, hence `SYSTEM′sym` has a deadlock.
  --
  -- The deadlock essence: every PHIL residual now offers ONLY its second pick
  -- (`picks i (i ⊕1)`), so it refuses every `putsdown`; every FORK residual now offers
  -- ONLY a `putsdown`, so it refuses every `picks`.  Under full synchronisation each
  -- side needs the partner to co-offer, but at any DP event one side refuses:
  --   • a `picks _ _`    : FORKS′ refuses → disjoint;
  --   • a `putsdown _ _` : PHILS′ refuses → disjoint.

  -- Wrong-category per-residual refusals (general over the offending event).
  -- An advanced philosopher offers only `picks i (i ⊕1)`, so refuses every `putsdown`.
  philRes-refuses-pd : ∀ i i′ f′ → philRes-fb i (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing
  philRes-refuses-pd i i′ f′ =
    loop0-offer-nothing {at = ⊤ {lzero} , putsdown i′ f′} {a = tt} (Pbody i)
      (Prefix-cont (picks i (i ⊕1)) (λ _ → putsdown i (i ⊕1) ⟶₀ putsdown i i ⟶₀ Skip))
      (prefix-picks-refuse-pd i (i ⊕1) i′ f′
        (λ _ → putsdown i (i ⊕1) ⟶₀ putsdown i i ⟶₀ Skip))

  -- An advanced fork offers only `putsdown j j`, so refuses every `picks`.
  forkRes-refuses-pk : ∀ j i′ f′ → forkRes-fb j (pAt i′ f′) tt ≡ nothing
  forkRes-refuses-pk j i′ f′ =
    loop0-offer-nothing {at = pAt i′ f′} {a = tt} (Fbody j)
      (Prefix-cont (putsdown j j) (λ _ → Skip))
      (prefix-putsdown-refuse-pk j j i′ f′ (λ _ → Skip))

  -- If every advanced philosopher in the block refuses `(at , a)`, the block refuses it:
  -- either it is `Skip` (ret-headed; empty block) or it is vis-headed and its canonical
  -- offer at `(at , a)` is `nothing`.  Mirrors `⦀list-refuse`, computing the merged offer
  -- with the `o⦀ref-*` helpers from Task 2 (and recursing structurally on the tail list).
  allAdvP-refuses :
    ∀ (rest : List Phil) {at : AnyTypes DP} {a : proj₁ at}
    → (∀ i → philRes-fb i at a ≡ nothing)
    → (Σ[ s ∈ _ ] (allAdvP rest) .force ≡ ret s)
    ⊎ (Σ[ f ∈ _ ] ((allAdvP rest) .force ≡ vis f × f at a ≡ nothing))
  allAdvP-refuses []       _   = inj₁ (_ , refl)
  allAdvP-refuses (p ∷ rest) ref
    with allAdvP-refuses rest ref
  ... | inj₁ (_ , retEq) with f⦀vr (philRes-force p) retEq
  ...   | f , fe = inj₂ (_ , fe , o⦀ref-vr (philRes-force p) (ref p) retEq fe)
  allAdvP-refuses (p ∷ rest) ref
    | inj₂ (g , eqg , bg) with f⦀vv (philRes-force p) eqg
  ...   | f , fe = inj₂ (_ , fe , o⦀ref-vv (philRes-force p) (ref p) eqg bg fe)

  allAdvF-refuses :
    ∀ (rest : List Fork) {at : AnyTypes DP} {a : proj₁ at}
    → (∀ j → forkRes-fb j at a ≡ nothing)
    → (Σ[ s ∈ _ ] (allAdvF rest) .force ≡ ret s)
    ⊎ (Σ[ f ∈ _ ] ((allAdvF rest) .force ≡ vis f × f at a ≡ nothing))
  allAdvF-refuses []       _   = inj₁ (_ , refl)
  allAdvF-refuses (p ∷ rest) ref
    with allAdvF-refuses rest ref
  ... | inj₁ (_ , retEq) with f⦀vr (forkRes-force p) retEq
  ...   | f , fe = inj₂ (_ , fe , o⦀ref-vr (forkRes-force p) (ref p) retEq fe)
  allAdvF-refuses (p ∷ rest) ref
    | inj₂ (g , eqg , bg) with f⦀vv (forkRes-force p) eqg
  ...   | f , fe = inj₂ (_ , fe , o⦀ref-vv (forkRes-force p) (ref p) eqg bg fe)

  -- Vis-headedness of a non-empty all-advanced block (mirrors `⦀list-vis`, but for the
  -- `allAdvP`/`allAdvF` folds, whose head residuals are vis via `philRes`/`forkRes-force`).
  allAdvP-vis : (p : Phil) (rest : List Phil)
              → Σ[ f ∈ _ ] (allAdvP (p ∷ rest)) .force ≡ vis f
  allAdvP-vis p []          rewrite philRes-force p = _ , refl
  allAdvP-vis p (q ∷ rest)
    with allAdvP-vis q rest
  ... | _ , eqtl = f⦀vv (philRes-force p) eqtl

  allAdvF-vis : (p : Fork) (rest : List Fork)
              → Σ[ f ∈ _ ] (allAdvF (p ∷ rest)) .force ≡ vis f
  allAdvF-vis p []          rewrite forkRes-force p = _ , refl
  allAdvF-vis p (q ∷ rest)
    with allAdvF-vis q rest
  ... | _ , eqtl = f⦀vv (forkRes-force p) eqtl

  -- `allPhils = toList (tabulate id)` over `Fin (suc (suc m))` definitionally reduces to
  -- `Fin.zero ∷ toList (tabulate suc)`, so both all-advanced blocks are genuinely
  -- vis-headed (head `philRes`/`forkRes` is vis-headed via `philRes`/`forkRes-force`).
  PHILS′-vis : Σ[ f ∈ _ ] (PHILS′ .force ≡ vis f)
  PHILS′-vis = allAdvP-vis Fin.zero (toList (tabulate (λ (i : Fin (suc m)) → Fin.suc i)))

  FORKS′-vis : Σ[ g ∈ _ ] (FORKS′ .force ≡ vis g)
  FORKS′-vis = allAdvF-vis Fin.zero (toList (tabulate (λ (i : Fin (suc m)) → Fin.suc i)))

  -- vis-injectivity (NodeKind `vis` is a constructor), used to transport a block-refusal
  -- proof from the refusal lemma's own force witness onto `PHILS′-vis`/`FORKS′-vis`'s.
  vis-inj : ∀ {ℓr} {R : Set ℓr} {f g : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) R))}
          → (vis f) ≡ (vis g) → f ≡ g
  vis-inj refl = refl

  -- The block-refusal lemma, specialised to the canonical `PHILS′-vis`/`FORKS′-vis`
  -- force witness (the `ret` branch is impossible — both blocks are vis-headed).
  PHILS′-refuses : ∀ {at : AnyTypes DP} {a : proj₁ at}
                 → (∀ i → philRes-fb i at a ≡ nothing)
                 → proj₁ PHILS′-vis at a ≡ nothing
  PHILS′-refuses ref with allAdvP-refuses allPhils ref
  ... | inj₁ (_ , retEq) = case trans (sym (proj₂ PHILS′-vis)) retEq of λ ()
  ... | inj₂ (g , eqg , bg)
        rewrite vis-inj (trans (sym eqg) (proj₂ PHILS′-vis)) = bg

  FORKS′-refuses : ∀ {at : AnyTypes DP} {a : proj₁ at}
                 → (∀ j → forkRes-fb j at a ≡ nothing)
                 → proj₁ FORKS′-vis at a ≡ nothing
  FORKS′-refuses ref with allAdvF-refuses allPhils ref
  ... | inj₁ (_ , retEq) = case trans (sym (proj₂ FORKS′-vis)) retEq of λ ()
  ... | inj₂ (g , eqg , bg)
        rewrite vis-inj (trans (sym eqg) (proj₂ FORKS′-vis)) = bg

  -- The deadlock essence: at every DP event, one block refuses.
  disjoint-offers :
    ∀ (at : AnyTypes DP) (a : proj₁ at)
    → (proj₁ PHILS′-vis at a ≡ nothing) ⊎ (proj₁ FORKS′-vis at a ≡ nothing)
  disjoint-offers (_ , picks i f) a =
    inj₂ (FORKS′-refuses (λ j → forkRes-refuses-pk j i f))
  disjoint-offers (_ , putsdown i f) a =
    inj₁ (PHILS′-refuses (λ i′ → philRes-refuses-pd i′ i f))

  deadlock-stuck : IsStuck (PHILS′ ∥⇘ syncAll ¿ syncAll-dec ⇙ FORKS′)
  deadlock-stuck =
    ∥⇘-full-stuck (proj₂ PHILS′-vis) (proj₂ FORKS′-vis) disjoint-offers

  philosophers-deadlock′ : HasDeadlock SYSTEM′sym
  philosophers-deadlock′ =
    _ , _ , deadlock-reachable , deadlock-stuck

  ¬deadlock-free′ : ¬ DeadlockFree SYSTEM′sym
  ¬deadlock-free′ = hasDeadlock⇒¬deadlockFree philosophers-deadlock′

-- Sanity: force full elaboration of `philosophers-deadlock′` at m = 0 (n = 2).
private
  module Sanity where
    open Pf 0
    _ = philosophers-deadlock′
    _ = ¬deadlock-free′
    _ = deadlock-reachable
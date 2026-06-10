{-# OPTIONS --guardedness #-}
module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_SysStates where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; suc; _<_; s≤s; z≤n; _≤_; pred; s<s⁻¹)
open import Data.Nat using (_<?_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n<1+n; <-irrefl; suc-injective; ≤∧≢⇒<; ≤-pred)
open import Data.Fin using (Fin; toℕ; fromℕ<; inject₁) ; import Data.Fin as Fin
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-fromℕ<; toℕ-injective; toℕ<n)
open import Data.Sum using (_⊎_; inj₁; inj₂) ; import Data.Sum
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_; map; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Function using (case_of_)

open import Interaction_Trees
open ITree
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS

import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP          as M
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_States   as St
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Deadlock as D

module SysSt (m : ℕ) where
  open M.Sys m
  open St.St m
  open D.Pf  m

  -- The library interleave `_⦀_` (and the named collision node `⦀-choice`) at the DP event
  -- decidability — re-opened here so this module can name `_⦀_` in signatures.
  import CSP.Definitions.Parallel {E = DP} as ParD
  open ParD DP-AnyTypes-≟ using (_⦀_; ⦀-choice; _∥⇘_¿_⇙_)

  -- The binary interleave state-closure split (in-progress / collision / done), used to
  -- fold the n-ary `⦀list-reach` below.
  import CSP.Laws.Parallel as L
  open L DP-AnyTypes-≟ using (Interleave-reach; ParInterleaveSplit; Parallel-reach; ParReachSplit)
  -- NB: `ParReachSplit` (∥⇘, ctors in-progress/done) and `ParInterleaveSplit` (⦀, ctors
  -- in-progress/collision/done) share the unqualified names `in-progress`/`done`.  Both are
  -- opened; Agda disambiguates each use by the expected datatype (e.g. the `SYSTEM′-states`
  -- matches resolve to `ParReachSplit` via `Parallel-reach`'s result type).
  open ParInterleaveSplit
  open ParReachSplit

  -------------------------------------------------------------------------------------
  -- Step 2: Event-index extractors.
  --
  -- `picks`/`putsdown` are the only `DP` constructors; every visible `DP` event has the
  -- shape `evLabel _ (picks i j) tt` or `evLabel _ (putsdown i j) tt`.  `philIndex`
  -- projects the philosopher (first) index, `forkIndex` the fork (second) index.
  -------------------------------------------------------------------------------------

  philIndex : Event DP → Phil
  philIndex (evLabel _ (picks    i _) _) = i
  philIndex (evLabel _ (putsdown i _) _) = i

  forkIndex : Event DP → Fork
  forkIndex (evLabel _ (picks    _ j) _) = j
  forkIndex (evLabel _ (putsdown _ j) _) = j

  -------------------------------------------------------------------------------------
  -- Step 3: per-process step-index (Lemma A).
  --
  -- Any visible step out of a philosopher position `i` carries a `philIndex ≡ i`; any
  -- visible step out of a fork position `j` carries a `forkIndex ≡ j`.  Cased on the
  -- position; each vis-position is `vis`-headed (`philState-force-…`) so only `sVis`
  -- survives — the other step constructors (`sMixVis`/`sSil`/`sRet`/`sNdbr`/`sMixSlide`)
  -- carry a `force≡…` premise contradicting the force lemma.  `reloop` is `sil`-headed
  -- so it offers no `ev` step at all.
  --
  -- For the index itself we pattern-match the event into its concrete head
  -- (`picks i′ f′` / `putsdown i′ f′`, with `a = tt`), `rewrite` the offer function by
  -- the force lemma, then reuse 3e′-i's `*-refuses-*` lemmas via abstract-`fb` classifiers
  -- (mirroring `St`'s `phil-pk-det`/`phil-pd-det`): keeping `fb` abstract stops the offer's
  -- buried `DP-AnyTypes-≟` from entangling with the goal.  When the offered index matches
  -- the head index the conclusion is `refl`; otherwise the matching refuse lemma turns
  -- `gja : … ≡ just t′` into `nothing ≡ just t′` (absurd).
  -------------------------------------------------------------------------------------

  -- Index classifiers (abstract offer fn `fb`).  Conclude only the head-index equality
  -- `i′ ≡ i` (resp. `f′ ≡ j`); the offer's internal `with` stays out of the goal.

  -- A `picks`-headed philosopher position (think/held1): the head philosopher index is `i`.
  phil-pk-index :
    ∀ i (hd : Fork)
    → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
    → (refuse : ∀ i′ f′ → ¬ ((i ≡ i′) × (hd ≡ f′)) → fb (pAt i′ f′) tt ≡ nothing)
    → ∀ {t′} i′ f′ → fb (pAt i′ f′) tt ≡ just t′ → i′ ≡ i
  phil-pk-index i hd fb refuse i′ f′ gja with i Fin.≟ i′
  ... | yes refl = refl
  ... | no ¬i = case trans (sym (refuse i′ f′ (λ { (e , _) → ¬i e }))) gja of λ ()

  -- A `putsdown`-headed philosopher position (held2/down1): the head philosopher index is `i`.
  phil-pd-index :
    ∀ i (hd : Fork)
    → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
    → (refuse : ∀ i′ f′ → ¬ ((i ≡ i′) × (hd ≡ f′)) → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing)
    → ∀ {t′} i′ f′ → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ just t′ → i′ ≡ i
  phil-pd-index i hd fb refuse i′ f′ gja with i Fin.≟ i′
  ... | yes refl = refl
  ... | no ¬i = case trans (sym (refuse i′ f′ (λ { (e , _) → ¬i e }))) gja of λ ()

  -- Fork index-classifiers (abstract offer fn `fb`).  Every offered fork event has
  -- second index `j`; conclude only `f′ ≡ j`.  As with the philosopher classifiers,
  -- keeping `fb` abstract stops the offer's buried `DP-AnyTypes-≟` from entangling with
  -- the goal's `with`.

  -- A `picks`-headed fork position (`free`): both offered `picks` events carry fork
  -- index `j`, so an offered `picks i′ f′` forces `f′ ≡ j`.
  fork-pk-index :
    ∀ j (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
    → (refuse : ∀ i′ f′ → f′ ≢ j → fb (pAt i′ f′) tt ≡ nothing)
    → ∀ {t′} i′ f′ → fb (pAt i′ f′) tt ≡ just t′ → f′ ≡ j
  fork-pk-index j fb refuse i′ f′ gja with j Fin.≟ f′
  ... | yes refl = refl
  ... | no ¬f = case trans (sym (refuse i′ f′ (λ e → ¬f (sym e)))) gja of λ ()

  -- A `putsdown`-headed fork position (`heldOwn`/`heldNbr`): the single offered
  -- `putsdown` event carries fork index `j`, so an offered `putsdown i′ f′` forces `f′ ≡ j`.
  fork-pd-index :
    ∀ j (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
    → (refuse : ∀ i′ f′ → f′ ≢ j → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing)
    → ∀ {t′} i′ f′ → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ just t′ → f′ ≡ j
  fork-pd-index j fb refuse i′ f′ gja with j Fin.≟ f′
  ... | yes refl = refl
  ... | no ¬f = case trans (sym (refuse i′ f′ (λ e → ¬f (sym e)))) gja of λ ()

  philState-step-index : ∀ {f s} i (pos : PhilPos) {e t′}
    → philState f s i pos ─[ ev (evl e) ]─► t′ → philIndex e ≡ i
  -- reloop: sil-headed, rejects every ev-step.
  philState-step-index {f}{s} i reloop (sVis eqf _) =
    case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()
  philState-step-index {f}{s} i reloop (sMixVis eqf _) =
    case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()
  -- think: head `picks i (f i)`.
  philState-step-index {f}{s} i think
    (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (philState-force-think {f}{s} i)) =
        phil-pk-index i (f i) (pfb-think f s i)
          (λ i″ f″ ¬eq → phil-think-refuses-picks {f}{s} i i″ f″ ¬eq) i′ f′ gja
  philState-step-index {f}{s} i think
    (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (philState-force-think {f}{s} i)) =
        case trans (sym (phil-think-refuses-pd {f}{s} i i′ f′)) gja of λ ()
  philState-step-index {f}{s} i think (sMixVis eqf _) =
    case trans (sym eqf) (philState-force-think {f}{s} i) of λ ()
  -- held1: head `picks i (s i)`.
  philState-step-index {f}{s} i held1
    (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (philState-force-held1 {f}{s} i)) =
        phil-pk-index i (s i) (pfb-held1 f s i)
          (λ i″ f″ ¬eq → phil-held1-refuses-picks {f}{s} i i″ f″ ¬eq) i′ f′ gja
  philState-step-index {f}{s} i held1
    (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (philState-force-held1 {f}{s} i)) =
        case trans (sym (phil-held1-refuses-pd {f}{s} i i′ f′)) gja of λ ()
  philState-step-index {f}{s} i held1 (sMixVis eqf _) =
    case trans (sym eqf) (philState-force-held1 {f}{s} i) of λ ()
  -- held2: head `putsdown i (s i)`.
  philState-step-index {f}{s} i held2
    (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (philState-force-held2 {f}{s} i)) =
        phil-pd-index i (s i) (pfb-held2 f s i)
          (λ i″ f″ ¬eq → phil-held2-refuses-pd {f}{s} i i″ f″ ¬eq) i′ f′ gja
  philState-step-index {f}{s} i held2
    (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (philState-force-held2 {f}{s} i)) =
        case trans (sym (phil-held2-refuses-pk {f}{s} i i′ f′)) gja of λ ()
  philState-step-index {f}{s} i held2 (sMixVis eqf _) =
    case trans (sym eqf) (philState-force-held2 {f}{s} i) of λ ()
  -- down1: head `putsdown i (f i)`.
  philState-step-index {f}{s} i down1
    (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (philState-force-down1 {f}{s} i)) =
        phil-pd-index i (f i) (pfb-down1 f s i)
          (λ i″ f″ ¬eq → phil-down1-refuses-pd {f}{s} i i″ f″ ¬eq) i′ f′ gja
  philState-step-index {f}{s} i down1
    (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (philState-force-down1 {f}{s} i)) =
        case trans (sym (phil-down1-refuses-pk {f}{s} i i′ f′)) gja of λ ()
  philState-step-index {f}{s} i down1 (sMixVis eqf _) =
    case trans (sym eqf) (philState-force-down1 {f}{s} i) of λ ()

  -- Fork analogue.  The only branching position is `free`, which offers TWO `picks`
  -- events (`picks j j` own, `picks (j ⊖1) j` neighbour) — but BOTH have second index
  -- `j`, so `forkIndex e ≡ j` for either branch.  heldOwn/heldNbr/reloop are single (or
  -- no) event positions, all with second index `j`.
  forkState-step-index : ∀ j (pos : ForkPos) {e t′}
    → forkState j pos ─[ ev (evl e) ]─► t′ → forkIndex e ≡ j
  -- reloop: sil-headed.
  forkState-step-index j reloop (sVis eqf _) =
    case trans (sym eqf) (forkState-force-reloop j) of λ ()
  forkState-step-index j reloop (sMixVis eqf _) =
    case trans (sym eqf) (forkState-force-reloop j) of λ ()
  -- free: two `picks` heads, both with fork index `j`; refuses other picks and putsdown.
  forkState-step-index j free
    (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (forkState-force-free j)) =
        fork-pk-index j (loop0-fb (Fbody j) (FORK-fb j))
          (λ i″ f″ f″≢j → fork-free-refuses-pk j i″ f″
                            (λ { (_ , e) → f″≢j (sym e) }) (λ { (_ , e) → f″≢j (sym e) }))
          i′ f′ gja
  forkState-step-index j free
    (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (forkState-force-free j)) =
        case trans (sym (fork-free-refuses-pd j i′ f′)) gja of λ ()
  forkState-step-index j free (sMixVis eqf _) =
    case trans (sym eqf) (forkState-force-free j) of λ ()
  -- heldOwn: single head `putsdown j j`; fork index `j`.
  forkState-step-index j heldOwn
    (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (forkState-force-heldOwn j)) =
        fork-pd-index j (forkRes-fb j)
          (λ i″ f″ f″≢j → fork-heldOwn-refuses-pd j i″ f″ (λ { (_ , e) → f″≢j (sym e) }))
          i′ f′ gja
  forkState-step-index j heldOwn
    (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (forkState-force-heldOwn j)) =
        case trans (sym (fork-heldOwn-refuses-pk j i′ f′)) gja of λ ()
  forkState-step-index j heldOwn (sMixVis eqf _) =
    case trans (sym eqf) (forkState-force-heldOwn j) of λ ()
  -- heldNbr: single head `putsdown (j ⊖1) j`; fork index `j`.
  forkState-step-index j heldNbr
    (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (forkResNbr-force j)) =
        fork-pd-index j (forkResNbr-fb j)
          (λ i″ f″ f″≢j → fork-heldNbr-refuses-pd j i″ f″ (λ { (_ , e) → f″≢j (sym e) }))
          i′ f′ gja
  forkState-step-index j heldNbr
    (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
    rewrite vis-inj (trans (sym eqf) (forkResNbr-force j)) =
        case trans (sym (fork-heldNbr-refuses-pk j i′ f′)) gja of λ ()
  forkState-step-index j heldNbr (sMixVis eqf _) =
    case trans (sym eqf) (forkResNbr-force j) of λ ()

  -------------------------------------------------------------------------------------
  -- Step 4: `_⦀_`-step offer inversion (BACKWARD direction of `D.Pf`'s `⦀-step-L/R`).
  --
  -- A composite visible step `(p ⦀ rest) ─[ ev (evl e) ]─► t′` comes from one side
  -- offering the event.  We `with p .force | rest .force`; in each combo the step's `eqf`
  -- reduces to `<head> ≡ vis f` (resp. `mix f Qt`).  Non-(vis/mix)-headed combos are head
  -- clashes (`λ ()`).  For the productive combos `vis-inj`/`mix-inj eqf : merged ≡ f`,
  -- `rewrite`n, turns the step offer `gja` into the operator's merged `case (fP at a ,
  -- fQ at a)`; a nested `with fP at a in bP | fQ at a in bQ` reads off the firing side —
  --   fP just (fQ either) → P fired (left, incl. the `⦀-choice` collision node);
  --   fP nothing / fQ just → Q fired (right);  both nothing → `gja : nothing ≡ just _`.
  -- Under the plain `with`, `p .force`/`rest .force` are definitionally their refined heads,
  -- so `sVis refl _` / `sMixVis refl _` rebuild the per-side step.  (We rewrite the actual
  -- operator merge rather than reconstruct it: two `λ where` extended-lambdas are not
  -- definitionally equal under --guardedness, so a hand-copied merge would not typecheck.)
  -- Productive combos are split into their own clauses (full repeated LHS) so each nested
  -- `with` does not entangle the outer combo enumeration.
  -------------------------------------------------------------------------------------

  private
    -- `mix` is injective in its offer function (NodeKind `mix` is a constructor).
    mix-inj : ∀ {ℓr} {R : Set ℓr}
        {f g : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) R))}
        {Qt Qt′ : ITree DP (ExtI DP) R}
      → mix f Qt ≡ mix g Qt′ → f ≡ g
    mix-inj refl = refl

  ⦀-step-offer : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {p : ITree DP (ExtI DP) R} {rest : ITree DP (ExtI DP) S} {e t′}
    → (p ⦀ rest) ─[ ev (evl e) ]─► t′
    → (Σ[ p′ ∈ ITree DP (ExtI DP) R ] (p    ─[ ev (evl e) ]─► p′))
    ⊎ (Σ[ r′ ∈ ITree DP (ExtI DP) S ] (rest ─[ ev (evl e) ]─► r′))
  ⦀-step-offer {p = p} {rest = rest} (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    with p .force in eqP | rest .force in eqQ
  ... | sil _ | _ = case eqf of λ ()
  ... | ret _ | sil _ = case eqf of λ ()
  ... | ret _ | ret _ = case eqf of λ ()
  ... | ret _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ret _ | mix _ _ = case eqf of λ ()
  ... | vis _ | sil _ = case eqf of λ ()
  ... | vis _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | vis _ | mix _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | sil _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ret _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | vis _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | mix _ _ = case eqf of λ ()
  ... | mix _ _ | sil _ = case eqf of λ ()
  ... | mix _ _ | ret _ = case eqf of λ ()
  ... | mix _ _ | vis _ = case eqf of λ ()
  ... | mix _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | mix _ _ | mix _ _ = case eqf of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | ret _ | vis fQ rewrite sym (vis-inj eqf) with fQ at a in bQ
  ...   | just r′ = inj₂ (r′ , sVis eqQ bQ)
  ...   | nothing = case gja of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | ret _ rewrite sym (vis-inj eqf) with fP at a in bP
  ...   | just p′ = inj₁ (p′ , sVis eqP bP)
  ...   | nothing = case gja of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | vis fQ rewrite sym (vis-inj eqf) with fP at a in bP | fQ at a in bQ
  ...   | just p′ | _       = inj₁ (p′ , sVis eqP bP)
  ...   | nothing | just r′ = inj₂ (r′ , sVis eqQ bQ)
  ...   | nothing | nothing = case gja of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    with p .force in eqP | rest .force in eqQ
  ... | sil _ | _ = case eqf of λ ()
  ... | ret _ | sil _ = case eqf of λ ()
  ... | ret _ | ret _ = case eqf of λ ()
  ... | ret _ | vis _ = case eqf of λ ()
  ... | ret _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | vis _ | sil _ = case eqf of λ ()
  ... | vis _ | ret _ = case eqf of λ ()
  ... | vis _ | vis _ = case eqf of λ ()
  ... | vis _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | sil _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ret _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | vis _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | mix _ _ = case eqf of λ ()
  ... | mix _ _ | sil _ = case eqf of λ ()
  ... | mix _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | ret _ | mix fQ Q′ rewrite sym (mix-inj eqf) with fQ at a in bQ
  ...   | just r′ = inj₂ (r′ , sMixVis eqQ bQ)
  ...   | nothing = case gja of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | mix fQ Q′ rewrite sym (mix-inj eqf) with fP at a in bP | fQ at a in bQ
  ...   | just p′ | _       = inj₁ (p′ , sVis eqP bP)
  ...   | nothing | just r′ = inj₂ (r′ , sMixVis eqQ bQ)
  ...   | nothing | nothing = case gja of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P′ | ret _ rewrite sym (mix-inj eqf) with fP at a in bP
  ...   | just p′ = inj₁ (p′ , sMixVis eqP bP)
  ...   | nothing = case gja of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P′ | vis fQ rewrite sym (mix-inj eqf) with fP at a in bP | fQ at a in bQ
  ...   | just p′ | _       = inj₁ (p′ , sMixVis eqP bP)
  ...   | nothing | just r′ = inj₂ (r′ , sVis eqQ bQ)
  ...   | nothing | nothing = case gja of λ ()
  ⦀-step-offer {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P′ | mix fQ Q′ rewrite sym (mix-inj eqf) with fP at a in bP | fQ at a in bQ
  ...   | just p′ | _       = inj₁ (p′ , sMixVis eqP bP)
  ...   | nothing | just r′ = inj₂ (r′ , sMixVis eqQ bQ)
  ...   | nothing | nothing = case gja of λ ()

  -------------------------------------------------------------------------------------
  -- Residual-tracking offer inversion (`⦀-offer-res`).  Like `⦀-step-offer`, but ALSO
  -- pins the composite residual `t′`: a P-only firing lands on `p′ ⦀ rest`, a Q-only
  -- firing on `p ⦀ r′`, and a simultaneous (collision) firing on the `⦀-choice` node —
  -- in which case BOTH a P-step and a Q-step are produced, so the caller can refute it by
  -- index-disjointness.  Three outcomes (`P-only` / `Q-only` / `both`); the `both`
  -- outcome carries no residual eq (the caller discharges it from the two steps).
  -------------------------------------------------------------------------------------

  ⦀-offer-res : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {p : ITree DP (ExtI DP) R} {rest : ITree DP (ExtI DP) S} {e t′}
    → (p ⦀ rest) ─[ ev (evl e) ]─► t′
    → (Σ[ p′ ∈ ITree DP (ExtI DP) R ] ((p ─[ ev (evl e) ]─► p′) × (t′ ≡ p′ ⦀ rest)))
    ⊎ (Σ[ r′ ∈ ITree DP (ExtI DP) S ] ((rest ─[ ev (evl e) ]─► r′) × (t′ ≡ p ⦀ r′)))
    ⊎ (Σ[ p′ ∈ ITree DP (ExtI DP) R ] Σ[ r′ ∈ ITree DP (ExtI DP) S ]
         ((p ─[ ev (evl e) ]─► p′) × (rest ─[ ev (evl e) ]─► r′)))
  ⦀-offer-res {p = p} {rest = rest} (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    with p .force in eqP | rest .force in eqQ
  ... | sil _ | _ = case eqf of λ ()
  ... | ret _ | sil _ = case eqf of λ ()
  ... | ret _ | ret _ = case eqf of λ ()
  ... | ret _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ret _ | mix _ _ = case eqf of λ ()
  ... | vis _ | sil _ = case eqf of λ ()
  ... | vis _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | vis _ | mix _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | sil _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ret _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | vis _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | mix _ _ = case eqf of λ ()
  ... | mix _ _ | sil _ = case eqf of λ ()
  ... | mix _ _ | ret _ = case eqf of λ ()
  ... | mix _ _ | vis _ = case eqf of λ ()
  ... | mix _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | mix _ _ | mix _ _ = case eqf of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | ret _ | vis fQ rewrite sym (vis-inj eqf) with fQ at a in bQ
  ...   | just r′ = inj₂ (inj₁ (r′ , sVis eqQ bQ , sym (just-injective gja)))
  ...   | nothing = case gja of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | ret _ rewrite sym (vis-inj eqf) with fP at a in bP
  ...   | just p′ = inj₁ (p′ , sVis eqP bP , sym (just-injective gja))
  ...   | nothing = case gja of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | vis fQ rewrite sym (vis-inj eqf) with fP at a in bP | fQ at a in bQ
  ...   | just p′ | nothing = inj₁ (p′ , sVis eqP bP , sym (just-injective gja))
  ...   | nothing | just r′ = inj₂ (inj₁ (r′ , sVis eqQ bQ , sym (just-injective gja)))
  ...   | just p′ | just r′ = inj₂ (inj₂ (p′ , r′ , sVis eqP bP , sVis eqQ bQ))
  ...   | nothing | nothing = case gja of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    with p .force in eqP | rest .force in eqQ
  ... | sil _ | _ = case eqf of λ ()
  ... | ret _ | sil _ = case eqf of λ ()
  ... | ret _ | ret _ = case eqf of λ ()
  ... | ret _ | vis _ = case eqf of λ ()
  ... | ret _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | vis _ | sil _ = case eqf of λ ()
  ... | vis _ | ret _ = case eqf of λ ()
  ... | vis _ | vis _ = case eqf of λ ()
  ... | vis _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | sil _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ret _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | vis _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | mix _ _ = case eqf of λ ()
  ... | mix _ _ | sil _ = case eqf of λ ()
  ... | mix _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | ret _ | mix fQ Q′ rewrite sym (mix-inj eqf) with fQ at a in bQ
  ...   | just r′ = inj₂ (inj₁ (r′ , sMixVis eqQ bQ , sym (just-injective gja)))
  ...   | nothing = case gja of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | mix fQ Q′ rewrite sym (mix-inj eqf) with fP at a in bP | fQ at a in bQ
  ...   | just p′ | nothing = inj₁ (p′ , sVis eqP bP , sym (just-injective gja))
  ...   | nothing | just r′ = inj₂ (inj₁ (r′ , sMixVis eqQ bQ , sym (just-injective gja)))
  ...   | just p′ | just r′ = inj₂ (inj₂ (p′ , r′ , sVis eqP bP , sMixVis eqQ bQ))
  ...   | nothing | nothing = case gja of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P′ | ret _ rewrite sym (mix-inj eqf) with fP at a in bP
  ...   | just p′ = inj₁ (p′ , sMixVis eqP bP , sym (just-injective gja))
  ...   | nothing = case gja of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P′ | vis fQ rewrite sym (mix-inj eqf) with fP at a in bP | fQ at a in bQ
  ...   | just p′ | nothing = inj₁ (p′ , sMixVis eqP bP , sym (just-injective gja))
  ...   | nothing | just r′ = inj₂ (inj₁ (r′ , sVis eqQ bQ , sym (just-injective gja)))
  ...   | just p′ | just r′ = inj₂ (inj₂ (p′ , r′ , sMixVis eqP bP , sVis eqQ bQ))
  ...   | nothing | nothing = case gja of λ ()
  ⦀-offer-res {p = p} {rest = rest} (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P′ | mix fQ Q′ rewrite sym (mix-inj eqf) with fP at a in bP | fQ at a in bQ
  ...   | just p′ | nothing = inj₁ (p′ , sMixVis eqP bP , sym (just-injective gja))
  ...   | nothing | just r′ = inj₂ (inj₁ (r′ , sMixVis eqQ bQ , sym (just-injective gja)))
  ...   | just p′ | just r′ = inj₂ (inj₂ (p′ , r′ , sMixVis eqP bP , sMixVis eqQ bQ))
  ...   | nothing | nothing = case gja of λ ()

  -------------------------------------------------------------------------------------
  -- Residual interleavings, typed at the SOURCE carrier `IProd (map (PHIL f s) S)` (resp.
  -- `IProd (map FORK S)`).  `philResid S cfg` IS `⦀list (map (λ i → philState f s i (cfg
  -- i)) S)` by construction, but typed so its carrier matches the residual `t′` of a
  -- big-step out of `⦀list (map (PHIL f s) S)` definitionally (the `_⦀_`-cons only
  -- contributes `⊥ ×`, whose ITree `IProd` discards — mirroring `D.Pf`'s `fireRes` trick
  -- that keeps the dependent carrier fixed without any transport).
  -------------------------------------------------------------------------------------

  philResid : ∀ {f s} (S : List Phil) (cfg : Phil → PhilPos)
            → ITree DP (ExtI DP) (IProd (map (PHIL f s) S))
  philResid             []       cfg = Skip
  philResid {f}{s} (i ∷ S′) cfg = philState f s i (cfg i) ⦀ philResid S′ cfg

  forkResid : (S : List Fork) (cfg : Fork → ForkPos)
            → ITree DP (ExtI DP) (IProd (map FORK S))
  forkResid []       cfg = Skip
  forkResid (j ∷ S′) cfg = forkState j (cfg j) ⦀ forkResid S′ cfg

  -------------------------------------------------------------------------------------
  -- Step 5: n-ary `⦀list` step-index (Lemma B).
  --
  -- Any visible step out of an interleaving of philosopher (resp. fork) states indexed by
  -- a list `S` carries an event whose `philIndex` (resp. `forkIndex`) lies in `S`.  Stated
  -- on `philResid`/`forkResid` (so it applies directly to the source-carrier residuals
  -- `Interleave-reach` hands back).  Induction on `S`: the empty list is `Skip` (ret-headed,
  -- no `ev` step); the cons case splits the composite step with `⦀-step-offer` — a head
  -- step gives the index by `philState-step-index`/`forkState-step-index` (→ `here`), a
  -- tail step recurses (→ `there`).
  -------------------------------------------------------------------------------------

  ⦀list-step-index-P : ∀ {f s} (S : List Phil) (cfg : Phil → PhilPos) {e t′}
    → philResid {f}{s} S cfg ─[ ev (evl e) ]─► t′
    → philIndex e ∈ S
  ⦀list-step-index-P [] cfg (sVis eqf _) = case eqf of λ ()
  ⦀list-step-index-P [] cfg (sMixVis eqf _) = case eqf of λ ()
  ⦀list-step-index-P {f}{s} (i ∷ S′) cfg {e} step
    with ⦀-step-offer step
  ... | inj₁ (_ , pStep) = here (philState-step-index i (cfg i) pStep)
  ... | inj₂ (_ , tStep) = there (⦀list-step-index-P S′ cfg tStep)

  ⦀list-step-index-F : ∀ (S : List Fork) (cfg : Fork → ForkPos) {e t′}
    → forkResid S cfg ─[ ev (evl e) ]─► t′
    → forkIndex e ∈ S
  ⦀list-step-index-F [] cfg (sVis eqf _) = case eqf of λ ()
  ⦀list-step-index-F [] cfg (sMixVis eqf _) = case eqf of λ ()
  ⦀list-step-index-F (j ∷ S′) cfg {e} step
    with ⦀-step-offer step
  ... | inj₁ (_ , pStep) = here (forkState-step-index j (cfg j) pStep)
  ... | inj₂ (_ , tStep) = there (⦀list-step-index-F S′ cfg tStep)

  -------------------------------------------------------------------------------------
  -- Step 6 (3e′-ii-c-1): philosopher / fork processes never terminate (never do a `√`).
  --
  -- Every `philState …`/`forkState …` position is vis-headed or sil-headed (the
  -- `*-force-*` lemmas), NEVER ret-headed.  A `√ r` element in a big-step trace can only
  -- arise from `bStep (sRet eqf) …` where `eqf : force p ≡ ret r` (the ONLY step that
  -- offers `ev (√ r)`).  So a `√` in the trace contradicts ret-freeness.
  -------------------------------------------------------------------------------------

  -- Step 1: positions are never ret-headed.
  philState-not-ret : ∀ {f s} i (pos : PhilPos) {r} → (philState f s i pos) .force ≢ ret r
  philState-not-ret {f}{s} i think  eq = case trans (sym (philState-force-think  {f}{s} i)) eq of λ ()
  philState-not-ret {f}{s} i held1  eq = case trans (sym (philState-force-held1  {f}{s} i)) eq of λ ()
  philState-not-ret {f}{s} i held2  eq = case trans (sym (philState-force-held2  {f}{s} i)) eq of λ ()
  philState-not-ret {f}{s} i down1  eq = case trans (sym (philState-force-down1  {f}{s} i)) eq of λ ()
  philState-not-ret {f}{s} i reloop eq = case trans (sym (philState-force-reloop {f}{s} i)) eq of λ ()

  forkState-not-ret : ∀ j (pos : ForkPos) {r} → (forkState j pos) .force ≢ ret r
  forkState-not-ret j free    eq = case trans (sym (forkState-force-free    j)) eq of λ ()
  forkState-not-ret j heldOwn eq = case trans (sym (forkState-force-heldOwn j)) eq of λ ()
  forkState-not-ret j heldNbr eq = case trans (sym (forkResNbr-force        j)) eq of λ ()
  forkState-not-ret j reloop  eq = case trans (sym (forkState-force-reloop  j)) eq of λ ()

  -- Step 2: a big-step out of any `philState`/`forkState` position whose trace ENDS in
  -- `√ r` (the exact shape of `ParReachSplit.done`'s `traces P (map evl sP ++ [ √ r ])`)
  -- is impossible.  Induction on the position-list `s′` exposing the trace head, then on
  -- the big-step: `bTau` advances to the next position (via `phil-/fork-reach-closed` on a
  -- one-step prefix) and recurses on the structurally-smaller residual; a productive
  -- `bStep` whose head is `evl e` likewise advances and recurses on the shorter tail; the
  -- terminal `bStep (sRet eqf)` (the `√ r` head) hands `eqf : force ≡ ret r` to
  -- `*-not-ret`.
  philState-no-√ : ∀ {f s} i (pos : PhilPos) {s′ : List (Event DP)} {r t′}
    → ¬ (philState f s i pos ═⟨ map evl s′ ++ [ √ r ] ⟩═► t′)
  philState-no-√ {f}{s} i pos {[]}     (bStep (sRet eqf) _) = philState-not-ret i pos eqf
  philState-no-√ {f}{s} i pos {[]}     (bTau  τstep rest)
    with phil-reach-closed i pos (bTau τstep bNil)
  ... | pos′ , refl = philState-no-√ i pos′ {[]} rest
  philState-no-√ {f}{s} i pos {_ ∷ s″} (bTau  τstep rest)
    with phil-reach-closed i pos (bTau τstep bNil)
  ... | pos′ , refl = philState-no-√ i pos′ {_ ∷ s″} rest
  philState-no-√ {f}{s} i pos {_ ∷ s″} (bStep estep rest)
    with phil-reach-closed i pos (bStep estep bNil)
  ... | pos′ , refl = philState-no-√ i pos′ {s″} rest

  forkState-no-√ : ∀ j (pos : ForkPos) {s′ : List (Event DP)} {r t′}
    → ¬ (forkState j pos ═⟨ map evl s′ ++ [ √ r ] ⟩═► t′)
  forkState-no-√ j pos {[]}     (bStep (sRet eqf) _) = forkState-not-ret j pos eqf
  forkState-no-√ j pos {[]}     (bTau  τstep rest)
    with fork-reach-closed j pos (bTau τstep bNil)
  ... | pos′ , refl = forkState-no-√ j pos′ {[]} rest
  forkState-no-√ j pos {_ ∷ s″} (bTau  τstep rest)
    with fork-reach-closed j pos (bTau τstep bNil)
  ... | pos′ , refl = forkState-no-√ j pos′ {_ ∷ s″} rest
  forkState-no-√ j pos {_ ∷ s″} (bStep estep rest)
    with fork-reach-closed j pos (bStep estep bNil)
  ... | pos′ , refl = forkState-no-√ j pos′ {s″} rest

  -- The corollaries ii-c-2 consumes: `PHIL`/`FORK` (≡ `philState … think` / `forkState …
  -- free` definitionally) never produce a `√`-terminating trace, matching exactly the
  -- `traces P (map evl sP ++ [ √ r ])` premise of `ParReachSplit.done`.
  PHIL-no-√ : ∀ {f s} i {s′ : List (Event DP)} {r t′}
    → ¬ (PHIL f s i ═⟨ map evl s′ ++ [ √ r ] ⟩═► t′)
  PHIL-no-√ {f}{s} i big = philState-no-√ {f}{s} i think big

  FORK-no-√ : ∀ j {s′ : List (Event DP)} {r t′}
    → ¬ (FORK j ═⟨ map evl s′ ++ [ √ r ] ⟩═► t′)
  FORK-no-√ j big = forkState-no-√ j free big

  -------------------------------------------------------------------------------------
  -- Step 7 (3e′-ii-c-1, the crux): n-ary `⦀list` state-closure.
  --
  -- `Distinct`/`Fresh`/`allPhils-distinct` are reused from `D.Pf` (already in scope):
  -- `Distinct (i ∷ rest) = Fresh i rest × Distinct rest`, `Fresh i rest = All (i ≢_) rest`,
  -- and `allPhils-distinct : Distinct allPhils` (`allPhils = toList (tabulate id)`).
  --
  -- `⦀list-reach-P`/`-F`: every state reachable from an interleaving of philosopher (resp.
  -- fork) start-processes indexed by a DISTINCT list `S` is itself an interleaving of the
  -- corresponding positions, recorded by a configuration `cfg : Phil → PhilPos`.  We
  -- restrict the trace to the √-free shape `map evl s′`: a √ from the head `PHIL`/`FORK`
  -- is impossible (`PHIL-no-√`/`FORK-no-√`, discharging `Interleave-reach`'s `done`), and
  -- the empty tail `⦀list [] = Skip` admits no √-free non-empty trace (`Skip` is
  -- ret-headed, offering only the √ event that `map evl s′` never contains).
  --
  -- The function `cfg` is patched at the head index `i` to `posᵢ` and left as the tail's
  -- `cfg′` elsewhere; the residual equality reassembles via a tail map-congruence
  -- (`map-cong-local`), pointwise `cfg k ≡ cfg′ k` for `k ∈ S′` justified by `Fresh i S′`
  -- (so `k ≢ i`, the `Fin.≟` override picks the `cfg′` branch).  `collision` is discharged
  -- by disjointness: the fired event's index is `≡ i` (head) and `∈ S′` (tail), but
  -- `Fresh i S′` forbids `i ∈ S′`.  Recursion is structural on the list `S`.
  -------------------------------------------------------------------------------------

  -- A √-free trace: every element is a visible `evl` event (no `√`).  Threaded through
  -- `⦀list-reach-*` so the empty-list base case (`Skip`) can reject the standalone `√` it
  -- would otherwise offer.  The cons case never relies on the incoming hypothesis: each
  -- recursion supplies a fresh `evl-√Free` for the `map evl _` sub-trace `Interleave-reach`
  -- hands back.  We keep the trace itself a FREE variable (not the literal `map evl s′`),
  -- so that matching `Interleave-reach`'s `in-progress`/`collision`/`done` indices unifies
  -- without getting stuck inverting the non-injective `map evl`.
  NotTick : ∀ {ℓr} {R : Set ℓr} → Event√ DP R → Set
  NotTick (evl _) = ⊤ {lzero}
  NotTick (√ _)   = ⊥

  √Free : ∀ {ℓr} {R : Set ℓr} → List (Event√ DP R) → Set _
  √Free = All NotTick

  -- Override a configuration at the head index `i`.
  patch : ∀ {ℓv} {V : Set ℓv} → (Phil → V) → Phil → V → Phil → V
  patch cfg′ i v k with i Fin.≟ k
  ... | yes _ = v
  ... | no  _ = cfg′ k

  patch-head : ∀ {ℓv} {V : Set ℓv} (cfg′ : Phil → V) i v → patch cfg′ i v i ≡ v
  patch-head cfg′ i v with i Fin.≟ i
  ... | yes _  = refl
  ... | no ¬p  = ⊥-elim (¬p refl)

  patch-tail : ∀ {ℓv} {V : Set ℓv} (cfg′ : Phil → V) i v {k}
             → i ≢ k → patch cfg′ i v k ≡ cfg′ k
  patch-tail cfg′ i v {k} i≢k with i Fin.≟ k
  ... | yes p  = ⊥-elim (i≢k p)
  ... | no  _  = refl

  private
    evl-√Free : ∀ {ℓr} {R : Set ℓr} (s : List (Event DP)) → √Free {R = R} (map evl s)
    evl-√Free []      = All.[]
    evl-√Free (_ ∷ s) = tt All.∷ evl-√Free s

    -- `Fresh i S′` (= `All (i ≢_) S′`) forbids `i ∈ S′`.
    fresh-∉ : ∀ {i} {S′ : List Phil} → Fresh i S′ → ¬ (i ∈ S′)
    fresh-∉ fr i∈ = All.lookup fr i∈ refl

    -- `philResid`/`forkResid` respect configurations that agree on the list's entries.
    philResid-cong : ∀ {f s} (S : List Phil) {cfg cfg′ : Phil → PhilPos}
                   → All (λ k → cfg k ≡ cfg′ k) S
                   → philResid {f}{s} S cfg ≡ philResid {f}{s} S cfg′
    philResid-cong []       _              = refl
    philResid-cong {f}{s} (i ∷ S′) (eq All.∷ eqs) =
      cong₂ _⦀_ (cong (philState f s i) eq) (philResid-cong S′ eqs)

    -- Tree-level congruence: `philResid`/`forkResid` agree if the per-index STATES (trees)
    -- agree, even where the positions are only propositionally equal (used to rewrite a
    -- residual through `philState f s i posᵢ ≡ philState f s i held1` without needing the
    -- — non-trivial — position injectivity `posᵢ ≡ held1`).
    philResid-congT : ∀ {f s} (S : List Phil) {cfg cfg′ : Phil → PhilPos}
                    → All (λ k → philState f s k (cfg k) ≡ philState f s k (cfg′ k)) S
                    → philResid {f}{s} S cfg ≡ philResid {f}{s} S cfg′
    philResid-congT []       _              = refl
    philResid-congT (i ∷ S′) (eq All.∷ eqs) =
      cong₂ _⦀_ eq (philResid-congT S′ eqs)

    forkResid-congT : (S : List Fork) {cfg cfg′ : Fork → ForkPos}
                    → All (λ k → forkState k (cfg k) ≡ forkState k (cfg′ k)) S
                    → forkResid S cfg ≡ forkResid S cfg′
    forkResid-congT []       _              = refl
    forkResid-congT (j ∷ S′) (eq All.∷ eqs) =
      cong₂ _⦀_ eq (forkResid-congT S′ eqs)

    forkResid-cong : (S : List Fork) {cfg cfg′ : Fork → ForkPos}
                   → All (λ k → cfg k ≡ cfg′ k) S
                   → forkResid S cfg ≡ forkResid S cfg′
    forkResid-cong []       _              = refl
    forkResid-cong (j ∷ S′) (eq All.∷ eqs) =
      cong₂ _⦀_ (cong (forkState j) eq) (forkResid-cong S′ eqs)

  -------------------------------------------------------------------------------------
  -- The crux.
  -------------------------------------------------------------------------------------

  ⦀list-reach-P : ∀ {f s} (S : List Phil) → Distinct S → ∀ {tr t′}
    → √Free tr → ⦀list (map (PHIL f s) S) ═⟨ tr ⟩═► t′
    → Σ[ cfg ∈ (Phil → PhilPos) ] (t′ ≡ philResid {f}{s} S cfg)
  -- [] : `⦀list [] = Skip` (ret-headed); the only √-free big-step is `bNil`.  A `bStep
  -- (sRet …)` offers the standalone √, contradicting `√Free`; vis/mix steps and `bTau` are
  -- head clashes against `Skip`'s `ret` head.
  ⦀list-reach-P [] _ _              bNil = (λ _ → think) , refl
  ⦀list-reach-P [] _ _              (bTau (sSil ()) _)
  ⦀list-reach-P [] _ (() All.∷ _)   (bStep (sRet refl) _)
  ⦀list-reach-P [] _ _              (bStep (sVis    () _) _)
  ⦀list-reach-P [] _ _              (bStep (sMixVis () _) _)
  -- i ∷ S′ : split the head step from the tail via `Interleave-reach`.
  ⦀list-reach-P {f}{s} (i ∷ S′) dist _ bigstep
    with Interleave-reach (PHIL f s i) (⦀list (map (PHIL f s) S′)) bigstep
  ... | in-progress {sQ = sQ} merge pStep tailStep
        with PHIL-states {f}{s} i pStep | ⦀list-reach-P {f}{s} S′ (proj₂ dist) (evl-√Free sQ) tailStep
  ...     | posᵢ , refl | cfg′ , refl =
            patch cfg′ i posᵢ
            , cong₂ _⦀_
                (cong (philState f s i) (sym (patch-head cfg′ i posᵢ)))
                (philResid-cong {f}{s} S′
                  (All.map (λ {k} i≢k → sym (patch-tail cfg′ i posᵢ i≢k)) (proj₁ dist)))
  ⦀list-reach-P {f}{s} (i ∷ S′) dist _ bigstep
    | collision {sQ = sQ} merge pStep tailStep pFire qFire
        with PHIL-states {f}{s} i pStep | ⦀list-reach-P {f}{s} S′ (proj₂ dist) (evl-√Free sQ) tailStep
  ...     | posᵢ , refl | cfg′ , refl =
            ⊥-elim (fresh-∉ (proj₁ dist)
              (subst (_∈ S′) (philState-step-index {f}{s} i posᵢ pFire)
                     (⦀list-step-index-P {f}{s} S′ cfg′ qFire)))
  ⦀list-reach-P {f}{s} (i ∷ S′) dist _ bigstep
    | done merge pTerm tailTerm = ⊥-elim (PHIL-no-√ {f}{s} i pTerm)

  ⦀list-reach-F : ∀ (S : List Fork) → Distinct S → ∀ {tr t′}
    → √Free tr → ⦀list (map FORK S) ═⟨ tr ⟩═► t′
    → Σ[ cfg ∈ (Fork → ForkPos) ] (t′ ≡ forkResid S cfg)
  ⦀list-reach-F [] _ _              bNil = (λ _ → free) , refl
  ⦀list-reach-F [] _ _              (bTau (sSil ()) _)
  ⦀list-reach-F [] _ (() All.∷ _)   (bStep (sRet refl) _)
  ⦀list-reach-F [] _ _              (bStep (sVis    () _) _)
  ⦀list-reach-F [] _ _              (bStep (sMixVis () _) _)
  ⦀list-reach-F (j ∷ S′) dist _ bigstep
    with Interleave-reach (FORK j) (⦀list (map FORK S′)) bigstep
  ... | in-progress {sQ = sQ} merge pStep tailStep
        with FORK-states j pStep | ⦀list-reach-F S′ (proj₂ dist) (evl-√Free sQ) tailStep
  ...     | posⱼ , refl | cfg′ , refl =
            patch cfg′ j posⱼ
            , cong₂ _⦀_
                (cong (forkState j) (sym (patch-head cfg′ j posⱼ)))
                (forkResid-cong S′
                  (All.map (λ {k} j≢k → sym (patch-tail cfg′ j posⱼ j≢k)) (proj₁ dist)))
  ⦀list-reach-F (j ∷ S′) dist _ bigstep
    | collision {sQ = sQ} merge pStep tailStep pFire qFire
        with FORK-states j pStep | ⦀list-reach-F S′ (proj₂ dist) (evl-√Free sQ) tailStep
  ...     | posⱼ , refl | cfg′ , refl =
            ⊥-elim (fresh-∉ (proj₁ dist)
              (subst (_∈ S′) (forkState-step-index j posⱼ pFire)
                     (⦀list-step-index-F S′ cfg′ qFire)))
  ⦀list-reach-F (j ∷ S′) dist _ bigstep
    | done merge pTerm tailTerm = ⊥-elim (FORK-no-√ j pTerm)

  -------------------------------------------------------------------------------------
  -- Step 8 (3e′-ii-c-1): `PHILS`/`FORKS` corollaries.
  --
  -- `PHILS f s = ⦀list (map (PHIL f s) allPhils)` and `FORKS = ⦀list (map FORK allPhils)`
  -- definitionally, and `allPhils` is `Distinct` (reused from `D.Pf`).  Restricting the
  -- system-level trace to the √-free shape `map evl s′` (no philosopher/fork ever performs
  -- a `√`), every reachable state of the all-philosophers (resp. all-forks) interleaving
  -- is `philResid allPhils cfg` (resp. `forkResid allPhils cfg`).
  -------------------------------------------------------------------------------------

  PHILS-states : ∀ {f s s′ t′} → PHILS f s ═⟨ map evl s′ ⟩═► t′
    → Σ[ cfg ∈ (Phil → PhilPos) ] (t′ ≡ philResid {f}{s} allPhils cfg)
  PHILS-states {s′ = s′} bs = ⦀list-reach-P allPhils allPhils-distinct (evl-√Free s′) bs

  FORKS-states : ∀ {s′ t′} → FORKS ═⟨ map evl s′ ⟩═► t′
    → Σ[ cfg ∈ (Fork → ForkPos) ] (t′ ≡ forkResid allPhils cfg)
  FORKS-states {s′ = s′} bs = ⦀list-reach-F allPhils allPhils-distinct (evl-√Free s′) bs

  -------------------------------------------------------------------------------------
  -- 3e′-ii-c-2, Task 1: the interleaved philosopher / fork BLOCKS never terminate.
  --
  -- Lifts the per-process non-termination (`PHIL-no-√`/`FORK-no-√`) to the whole
  -- interleaving `PHILS f s` / `FORKS`.  A `√ r` at the tail of a trace forces, at the
  -- end of the √-free prefix, a residual `P-pre` with `P-pre .force ≡ ret r`; but every
  -- reachable residual is a non-empty `philResid`/`forkResid` interleaving (head process
  -- present), which is NEVER ret-headed (`philResid-not-ret`/`forkResid-not-ret`,
  -- mirroring the per-process `*-not-ret`).
  -------------------------------------------------------------------------------------

  -- Step 1: a non-empty `philResid`/`forkResid` interleaving is never ret-headed.  Its
  -- force is `force (philState … ⦀ rest)`, which matches both sub-heads; the ONLY
  -- ret-producing combo is `ret | ret`, but the head `philState …` is never ret-headed
  -- (`philState-not-ret`), so every reachable combo gives a non-`ret` node.
  philResid-not-ret : ∀ {f s} i (S′ : List Phil) (cfg : Phil → PhilPos) {r}
    → (philResid {f}{s} (i ∷ S′) cfg) .force ≢ ret r
  philResid-not-ret {f}{s} i S′ cfg eq
    with philState f s i (cfg i) .force in p-eq | philResid {f}{s} S′ cfg .force
  ... | ret _      | ret _          = philState-not-ret i (cfg i) p-eq
  ... | ret _      | sil _          = case eq of λ ()
  ... | ret _      | vis _          = case eq of λ ()
  ... | ret _      | ndbr _ _ _ _   = case eq of λ ()
  ... | ret _      | mix _ _        = case eq of λ ()
  ... | sil _      | _              = case eq of λ ()
  ... | vis _      | ret _          = case eq of λ ()
  ... | vis _      | sil _          = case eq of λ ()
  ... | vis _      | vis _          = case eq of λ ()
  ... | vis _      | ndbr _ _ _ _   = case eq of λ ()
  ... | vis _      | mix _ _        = case eq of λ ()
  ... | ndbr _ _ _ _ | ret _        = case eq of λ ()
  ... | ndbr _ _ _ _ | sil _        = case eq of λ ()
  ... | ndbr _ _ _ _ | vis _        = case eq of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eq of λ ()
  ... | ndbr _ _ _ _ | mix _ _      = case eq of λ ()
  ... | mix _ _    | ret _          = case eq of λ ()
  ... | mix _ _    | sil _          = case eq of λ ()
  ... | mix _ _    | vis _          = case eq of λ ()
  ... | mix _ _    | ndbr _ _ _ _   = case eq of λ ()
  ... | mix _ _    | mix _ _        = case eq of λ ()

  forkResid-not-ret : ∀ j (S′ : List Fork) (cfg : Fork → ForkPos) {r}
    → (forkResid (j ∷ S′) cfg) .force ≢ ret r
  forkResid-not-ret j S′ cfg eq
    with forkState j (cfg j) .force in p-eq | forkResid S′ cfg .force
  ... | ret _      | ret _          = forkState-not-ret j (cfg j) p-eq
  ... | ret _      | sil _          = case eq of λ ()
  ... | ret _      | vis _          = case eq of λ ()
  ... | ret _      | ndbr _ _ _ _   = case eq of λ ()
  ... | ret _      | mix _ _        = case eq of λ ()
  ... | sil _      | _              = case eq of λ ()
  ... | vis _      | ret _          = case eq of λ ()
  ... | vis _      | sil _          = case eq of λ ()
  ... | vis _      | vis _          = case eq of λ ()
  ... | vis _      | ndbr _ _ _ _   = case eq of λ ()
  ... | vis _      | mix _ _        = case eq of λ ()
  ... | ndbr _ _ _ _ | ret _        = case eq of λ ()
  ... | ndbr _ _ _ _ | sil _        = case eq of λ ()
  ... | ndbr _ _ _ _ | vis _        = case eq of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eq of λ ()
  ... | ndbr _ _ _ _ | mix _ _      = case eq of λ ()
  ... | mix _ _    | ret _          = case eq of λ ()
  ... | mix _ _    | sil _          = case eq of λ ()
  ... | mix _ _    | vis _          = case eq of λ ()
  ... | mix _ _    | ndbr _ _ _ _   = case eq of λ ()
  ... | mix _ _    | mix _ _        = case eq of λ ()

  -- Step 2: `allPhils = toList (tabulate id)` over `Fin (suc (suc m))` reduces to a literal
  -- cons (`fzero ∷ …`), so the head/tail split is `refl`.
  allPhils-cons : Σ[ i₀ ∈ Phil ] Σ[ rest ∈ List Phil ] (allPhils ≡ i₀ ∷ rest)
  allPhils-cons = _ , _ , refl

  -- Step 3: split a `√`-terminated trace `map evl s′ ++ [ √ r ]` into the √-free prefix
  -- `map evl s′` (reaching a residual `P-pre`) and the terminal `P-pre .force ≡ ret r`.
  -- Generic in `P`; induction on `s′` peeling `bTau` and the leading `ev`-step.
  private
    √-split : ∀ {f s} {P : ITree DP (ExtI DP) (IProd (map (PHIL f s) allPhils))}
                {s′ : List (Event DP)} {r t′}
            → P ═⟨ map evl s′ ++ [ √ r ] ⟩═► t′
            → Σ[ P-pre ∈ ITree DP (ExtI DP) (IProd (map (PHIL f s) allPhils)) ]
                ((P ═⟨ map evl s′ ⟩═► P-pre) × (P-pre .force ≡ ret r))
    √-split {s′ = []}     (bStep (sRet eqf) _)   = _ , bNil , eqf
    √-split {s′ = []}     (bTau τstep rest)
      with √-split {s′ = []} rest
    ... | P-pre , pre , eqf = P-pre , bTau τstep pre , eqf
    √-split {s′ = _ ∷ s″} (bTau τstep rest)
      with √-split {s′ = _ ∷ s″} rest
    ... | P-pre , pre , eqf = P-pre , bTau τstep pre , eqf
    √-split {s′ = _ ∷ s″} (bStep estep rest)
      with √-split {s′ = s″} rest
    ... | P-pre , pre , eqf = P-pre , bStep estep pre , eqf

    √-splitF : ∀ {P : ITree DP (ExtI DP) (IProd (map FORK allPhils))}
                {s′ : List (Event DP)} {r t′}
             → P ═⟨ map evl s′ ++ [ √ r ] ⟩═► t′
             → Σ[ P-pre ∈ ITree DP (ExtI DP) (IProd (map FORK allPhils)) ]
                 ((P ═⟨ map evl s′ ⟩═► P-pre) × (P-pre .force ≡ ret r))
    √-splitF {s′ = []}     (bStep (sRet eqf) _)   = _ , bNil , eqf
    √-splitF {s′ = []}     (bTau τstep rest)
      with √-splitF {s′ = []} rest
    ... | P-pre , pre , eqf = P-pre , bTau τstep pre , eqf
    √-splitF {s′ = _ ∷ s″} (bTau τstep rest)
      with √-splitF {s′ = _ ∷ s″} rest
    ... | P-pre , pre , eqf = P-pre , bTau τstep pre , eqf
    √-splitF {s′ = _ ∷ s″} (bStep estep rest)
      with √-splitF {s′ = s″} rest
    ... | P-pre , pre , eqf = P-pre , bStep estep pre , eqf

  -- The corollaries Task 2 consumes: `PHILS`/`FORKS` never produce a `√`-terminating
  -- trace, matching exactly the `P ═⟨ map evl sP ++ [ √ r ] ⟩═► …` premise of
  -- `ParInterleaveSplit.done`.  Split off the trailing `√`, read the √-free prefix's
  -- residual via `PHILS-states`/`FORKS-states` (a non-empty `philResid`/`forkResid`
  -- since `allPhils` is a cons), then refute the terminal `ret` via `*Resid-not-ret`.
  PHILS-no-√ : ∀ {f s} {s′ : List (Event DP)} {r t′}
    → ¬ (PHILS f s ═⟨ map evl s′ ++ [ √ r ] ⟩═► t′)
  PHILS-no-√ {f}{s} {s′} {r} big
    with √-split {f}{s} {s′ = s′} big
  ... | P-pre , pre , eqf
        with PHILS-states {f}{s} {s′ = s′} pre | allPhils-cons
  -- NB: match `allPhils-cons` as `refl` (NOT `subst`/`rewrite`): unifying `allPhils` with
  -- `i₀ ∷ rest` realigns the dependent `IProd (map (PHIL f s) allPhils)` carrier so
  -- `philResid-not-ret i₀ rest cfg` typechecks against `eqf`.  Do not "simplify" to a named eq.
  ...     | cfg , refl | i₀ , rest , refl =
            philResid-not-ret {f}{s} i₀ rest cfg eqf

  FORKS-no-√ : ∀ {s′ : List (Event DP)} {r t′}
    → ¬ (FORKS ═⟨ map evl s′ ++ [ √ r ] ⟩═► t′)
  FORKS-no-√ {s′} {r} big
    with √-splitF {s′ = s′} big
  ... | P-pre , pre , eqf
        with FORKS-states {s′ = s′} pre | allPhils-cons
  -- (as PHILS-no-√) match `allPhils-cons` as `refl` to realign the dependent carrier.
  ...     | cfg , refl | j₀ , rest , refl =
            forkResid-not-ret j₀ rest cfg eqf

  -------------------------------------------------------------------------------------
  -- 3e′-ii-c-2, Task 2 (headline): every reachable `SYSTEM′` state is `sysState f s cfg`.
  --
  -- `SYSTEM′ f s = PHILS f s ∥⇘ syncAll ¿ syncAll-dec ⇙ FORKS`.  The sync set `syncAll`
  -- is full (every event must synchronise), so `Parallel-reach` applies and rules out the
  -- `collision`/interleave-without-sync cases: any reachable state is `P′ ∥⇘ … ⇙ Q′` where
  -- `P′`/`Q′` are √-free residuals of `PHILS`/`FORKS`, characterised by `PHILS-states`/
  -- `FORKS-states` as `philResid`/`forkResid` interleavings.  A `done` (√-terminated)
  -- split is impossible because `PHILS` never performs a `√` (`PHILS-no-√`).
  -------------------------------------------------------------------------------------

  -- Step 1: the sync set is full — every `DP` event must synchronise.
  syncAll-full : (at : AnyTypes DP) → syncAll at
  syncAll-full _ = tt

  -- Step 2: a system configuration pairs a philosopher-position map and a fork-position
  -- map; `sysState` reassembles the synchronised parallel of the corresponding residuals.
  Config : Set
  Config = (Phil → PhilPos) × (Fork → ForkPos)

  sysState : (first second : Phil → Fork) → Config
           → ITree DP (ExtI DP) (IProd (map (PHIL first second) allPhils) × IProd (map FORK allPhils))
  sysState f s (cfgP , cfgF) =
    philResid {f}{s} allPhils cfgP ∥⇘ syncAll ¿ syncAll-dec ⇙ forkResid allPhils cfgF

  -- sanity: the all-think/all-free config IS `SYSTEM′`.  This is NOT definitional for an
  -- abstract `m` (`PHILS = ⦀list (map (PHIL f s) allPhils)` needs `map … allPhils` to
  -- reduce to a cons, but `allPhils = toList (tabulate id)` over `Fin (suc (suc m))` is
  -- stuck), so we prove it propositionally by induction on the index list, using the
  -- definitional `PHIL f s i ≡ philState f s i think` / `FORK j ≡ forkState j free`.
  private
    philResid-start : ∀ {f s} (S : List Phil)
                    → philResid {f}{s} S (λ _ → think) ≡ ⦀list (map (PHIL f s) S)
    philResid-start []       = refl
    philResid-start {f}{s} (i ∷ S′) = cong (philState f s i think ⦀_) (philResid-start S′)

    forkResid-start : (S : List Fork)
                    → forkResid S (λ _ → free) ≡ ⦀list (map FORK S)
    forkResid-start []       = refl
    forkResid-start (j ∷ S′) = cong (forkState j free ⦀_) (forkResid-start S′)

  _ : ∀ {f s} → sysState f s ((λ _ → think) , (λ _ → free)) ≡ SYSTEM′ f s
  _ = cong₂ (λ P Q → P ∥⇘ syncAll ¿ syncAll-dec ⇙ Q)
        (philResid-start allPhils) (forkResid-start allPhils)

  -- Step 3: the headline state-closure.  Split the system big-step with `Parallel-reach`
  -- (full sync), characterise each √-free side residual via `PHILS-states`/`FORKS-states`,
  -- and refute the √-terminated split via `PHILS-no-√`.
  SYSTEM′-states : ∀ {f s} {tr t′} → SYSTEM′ f s ═⟨ tr ⟩═► t′
    → Σ[ cfg ∈ Config ] (t′ ≡ sysState f s cfg)
  SYSTEM′-states {f}{s} bigstep
    with Parallel-reach (PHILS f s) FORKS syncAll syncAll-dec syncAll-full bigstep
  ... | in-progress {sP = sP} {sQ = sQ} merge pStep qStep
        with PHILS-states {f}{s} {s′ = sP} pStep | FORKS-states {s′ = sQ} qStep
  ...     | cfgP , refl | cfgF , refl = (cfgP , cfgF) , refl
  SYSTEM′-states {f}{s} _ | done merge pTerm qTerm = ⊥-elim (PHILS-no-√ pTerm)

  -------------------------------------------------------------------------------------
  -- 3e′-iii-a: config-level step relations.
  --
  -- `_⊳⟨_⟩_` / `_⊳τ_` describe how a system `Config` advances under a synchronised
  -- SYSTEM′ event (resp. an internal τ).  They are parametrised by the fork-order
  -- functions `{f s : Phil → Fork}` (= the `first`/`second` of `PHIL f s`), since these
  -- are NOT globally fixed in this module (`philState`/`philResid`/`sysState` all take
  -- them as implicits).  The visible-event constructor jointly advances one philosopher
  -- and the fork it shares; `patch` (private, `Fin n`-indexed, so it serves both the
  -- `Phil`-indexed `cfgP` and the `Fork`-indexed `cfgF`) records the override.
  -------------------------------------------------------------------------------------

  -- A synchronised SYSTEM′ event jointly advances one philosopher and the fork it shares.
  -- Fork `j`'s "own" philosopher is `j`, its neighbour is `j ⊖1`; so philosopher `i` picking
  -- fork `(f i)` is the fork's own iff `f i ≡ i`, its neighbour iff `f i ≡ i ⊕1`.
  data _⊳⟨_⟩_ {f s : Phil → Fork} : Config → Event DP → Config → Set where
    ⊳pk1-own : ∀ {cfgP cfgF i} → cfgP i ≡ think → (f i) ≡ i → cfgF (f i) ≡ free
             → (cfgP , cfgF) ⊳⟨ evLabel _ (picks i (f i)) tt ⟩
               (patch cfgP i held1 , patch cfgF (f i) heldOwn)
    ⊳pk1-nbr : ∀ {cfgP cfgF i} → cfgP i ≡ think → (f i) ≡ (i ⊕1) → cfgF (f i) ≡ free
             → (cfgP , cfgF) ⊳⟨ evLabel _ (picks i (f i)) tt ⟩
               (patch cfgP i held1 , patch cfgF (f i) heldNbr)
    ⊳pk2-own : ∀ {cfgP cfgF i} → cfgP i ≡ held1 → (s i) ≡ i → cfgF (s i) ≡ free
             → (cfgP , cfgF) ⊳⟨ evLabel _ (picks i (s i)) tt ⟩
               (patch cfgP i held2 , patch cfgF (s i) heldOwn)
    ⊳pk2-nbr : ∀ {cfgP cfgF i} → cfgP i ≡ held1 → (s i) ≡ (i ⊕1) → cfgF (s i) ≡ free
             → (cfgP , cfgF) ⊳⟨ evLabel _ (picks i (s i)) tt ⟩
               (patch cfgP i held2 , patch cfgF (s i) heldNbr)
    ⊳pd-s    : ∀ {cfgP cfgF i} → cfgP i ≡ held2
             → (cfgP , cfgF) ⊳⟨ evLabel _ (putsdown i (s i)) tt ⟩
               (patch cfgP i down1 , patch cfgF (s i) reloop)
    ⊳pd-f    : ∀ {cfgP cfgF i} → cfgP i ≡ down1
             → (cfgP , cfgF) ⊳⟨ evLabel _ (putsdown i (f i)) tt ⟩
               (patch cfgP i reloop , patch cfgF (f i) reloop)

  data _⊳τ_ : Config → Config → Set where
    ⊳τ-phil : ∀ {cfgP cfgF i} → cfgP i ≡ reloop → (cfgP , cfgF) ⊳τ (patch cfgP i think , cfgF)
    ⊳τ-fork : ∀ {cfgP cfgF j} → cfgF j ≡ reloop → (cfgP , cfgF) ⊳τ (cfgP , patch cfgF j free)

  -------------------------------------------------------------------------------------
  -- 3e′-iii-a, Task 2 (hard machinery).
  -------------------------------------------------------------------------------------

  -- Step 1: single-component advance.  A visible step out of one position lands on a
  -- (unique) next position; we read off that position via `phil-/fork-reach-closed`
  -- (feed it the one-step big-step `bStep hstep bNil`).
  private
    philState-step-target : ∀ {f s} i (pos : PhilPos) {e t′}
      → philState f s i pos ─[ ev (evl e) ]─► t′
      → Σ[ pos′ ∈ PhilPos ] (t′ ≡ philState f s i pos′)
    philState-step-target i pos hstep = phil-reach-closed i pos (bStep hstep bNil)

    forkState-step-target : ∀ j (pos : ForkPos) {e t′}
      → forkState j pos ─[ ev (evl e) ]─► t′
      → Σ[ pos′ ∈ ForkPos ] (t′ ≡ forkState j pos′)
    forkState-step-target j pos hstep = fork-reach-closed j pos (bStep hstep bNil)

    -- `Fresh i S′` (= `All (i ≢_) S′`) gives `i ≢ k` for every `k ∈ S′`.
    fresh-≢ : ∀ {i} {S′ : List Phil} → Fresh i S′ → ∀ {k} → k ∈ S′ → i ≢ k
    fresh-≢ fr k∈ = All.lookup fr k∈

  -- A single visible step of an interleaved philosopher block advances exactly the
  -- component named by `philIndex e` to a specific next position, leaving the rest fixed.
  philResid-advance : ∀ {f s} (S : List Phil) → Distinct S → (cfg : Phil → PhilPos) → ∀ {e t′}
    → philResid {f}{s} S cfg ─[ ev (evl e) ]─► t′
    → Σ[ pos′ ∈ PhilPos ]
        ( (philState f s (philIndex e) (cfg (philIndex e)))
            ─[ ev (evl e) ]─► philState f s (philIndex e) pos′
        × (philIndex e ∈ S)
        × (t′ ≡ philResid {f}{s} S (patch cfg (philIndex e) pos′)) )
  philResid-advance [] _ _ (sVis eqf _)    = case eqf of λ ()
  philResid-advance [] _ _ (sMixVis eqf _) = case eqf of λ ()
  philResid-advance {f}{s} (i ∷ S′) dist cfg {e} step
    with ⦀-offer-res step
  ... | inj₁ (p′ , hstep , refl)
        with philState-step-index {f}{s} i (cfg i) hstep
           | philState-step-target {f}{s} i (cfg i) hstep
  ...     | refl | pos′ , refl =
            pos′
            , hstep
            , here refl
            , cong₂ _⦀_
                (cong (philState f s i) (sym (patch-head cfg i pos′)))
                (philResid-cong {f}{s} S′
                   (All.map (λ {k} i≢k → sym (patch-tail cfg i pos′ i≢k)) (proj₁ dist)))
  philResid-advance {f}{s} (i ∷ S′) dist cfg {e} step
    | inj₂ (inj₁ (r′ , tstep , refl))
        with philResid-advance {f}{s} S′ (proj₂ dist) cfg tstep
  ...     | pos′ , hstep′ , idx∈ , refl =
            pos′
            , hstep′
            , there idx∈
            , cong₂ _⦀_
                (cong (philState f s i)
                      (sym (patch-tail cfg (philIndex e) pos′
                              (λ eq → fresh-≢ (proj₁ dist) idx∈ (sym eq)))))
                refl
  -- collision: head fires (index ≡ i) AND tail fires (index ∈ S′) ⇒ i ∈ S′, refuting Fresh.
  philResid-advance {f}{s} (i ∷ S′) dist cfg {e} step
    | inj₂ (inj₂ (p′ , r′ , hstep , tstep))
        with philResid-advance {f}{s} S′ (proj₂ dist) cfg tstep
  ...     | _ , _ , idx∈ , _ =
            ⊥-elim (fresh-∉ (proj₁ dist)
              (subst (_∈ S′) (philState-step-index {f}{s} i (cfg i) hstep) idx∈))

  forkResid-advance : ∀ (S : List Fork) → Distinct S → (cfg : Fork → ForkPos) → ∀ {e t′}
    → forkResid S cfg ─[ ev (evl e) ]─► t′
    → Σ[ pos′ ∈ ForkPos ]
        ( (forkState (forkIndex e) (cfg (forkIndex e)))
            ─[ ev (evl e) ]─► forkState (forkIndex e) pos′
        × (forkIndex e ∈ S)
        × (t′ ≡ forkResid S (patch cfg (forkIndex e) pos′)) )
  forkResid-advance [] _ _ (sVis eqf _)    = case eqf of λ ()
  forkResid-advance [] _ _ (sMixVis eqf _) = case eqf of λ ()
  forkResid-advance (j ∷ S′) dist cfg {e} step
    with ⦀-offer-res step
  ... | inj₁ (p′ , hstep , refl)
        with forkState-step-index j (cfg j) hstep
           | forkState-step-target j (cfg j) hstep
  ...     | refl | pos′ , refl =
            pos′
            , hstep
            , here refl
            , cong₂ _⦀_
                (cong (forkState j) (sym (patch-head cfg j pos′)))
                (forkResid-cong S′
                   (All.map (λ {k} j≢k → sym (patch-tail cfg j pos′ j≢k)) (proj₁ dist)))
  forkResid-advance (j ∷ S′) dist cfg {e} step
    | inj₂ (inj₁ (r′ , tstep , refl))
        with forkResid-advance S′ (proj₂ dist) cfg tstep
  ...     | pos′ , hstep′ , idx∈ , refl =
            pos′
            , hstep′
            , there idx∈
            , cong₂ _⦀_
                (cong (forkState j)
                      (sym (patch-tail cfg (forkIndex e) pos′
                              (λ eq → fresh-≢ (proj₁ dist) idx∈ (sym eq)))))
                refl
  forkResid-advance (j ∷ S′) dist cfg {e} step
    | inj₂ (inj₂ (p′ , r′ , hstep , tstep))
        with forkResid-advance S′ (proj₂ dist) cfg tstep
  ...     | _ , _ , idx∈ , _ =
            ⊥-elim (fresh-∉ (proj₁ dist)
              (subst (_∈ S′) (forkState-step-index j (cfg j) hstep) idx∈))

  -------------------------------------------------------------------------------------
  -- Step 2: `∥⇘` single-step inversion (BACKWARD direction of 3c′'s `∥⇘-sync-step` /
  -- `∥⇘-τ-L`/`∥⇘-τ-R`).  Specialised to a FULL sync set (`full : ∀ at → cs at`), which is
  -- exactly the dining-philosophers setting (`cs = syncAll`, `full = syncAll-full`):
  -- every event must synchronise, so the interleave (`dec at = no`) branches are
  -- vacuous (refuted by `full at`).
  --
  --  * `∥⇘-sync-inv`: a visible step of `P ∥⇘ Q` decomposes into a synchronised pair of
  --    component steps.  `with P.force | Q.force | eqf | dec at`: only the vis|vis (and
  --    mix-combo) heads are vis/mix-headed, and only the `yes`-sync branch can hand back
  --    `just t′`; we read `fP at a ≡ just P′`/`fQ at a ≡ just Q′` off `gja` (a `nothing`
  --    on either side makes `gja : nothing ≡ just` absurd) and rebuild the two steps.
  --  * `∥⇘-τ-inv`: a τ of `P ∥⇘ Q` is one side's silent move.  The composite is sil-headed
  --    iff `P.force ≡ sil P′` (→ left) or (P not sil-headed and) `Q.force ≡ sil Q′`
  --    (→ right); an ndbr/mix-headed composite only arises when a component is itself
  --    ndbr/mix-headed.  We invert `sSil`/`sNdbr`/`sMixSlide` against the force-combo.
  -------------------------------------------------------------------------------------

  ∥⇘-sync-inv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S}
      {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      (full : (at : AnyTypes DP) → cs at) {e t′}
    → (P ∥⇘ cs ¿ dec ⇙ Q) ─[ ev (evl e) ]─► t′
    → Σ[ P′ ∈ ITree DP (ExtI DP) R ] Σ[ Q′ ∈ ITree DP (ExtI DP) S ]
        ( (P ─[ ev (evl e) ]─► P′)
        × (Q ─[ ev (evl e) ]─► Q′)
        × (t′ ≡ P′ ∥⇘ cs ¿ dec ⇙ Q′) )
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    with P .force in eqP | Q .force in eqQ
  ... | sil _ | _ = case eqf of λ ()
  ... | ret _ | sil _ = case eqf of λ ()
  ... | ret _ | ret _ = case eqf of λ ()
  ... | ret _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | vis _ | sil _ = case eqf of λ ()
  ... | vis _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | sil _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ret _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | vis _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | mix _ _ = case eqf of λ ()
  ... | mix _ _ | sil _ = case eqf of λ ()
  ... | mix _ _ | ndbr _ _ _ _ = case eqf of λ ()
  -- ret | vis : P terminated; in-sync → refuse (offer nothing).
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | ret _ | vis fQ rewrite sym (vis-inj eqf) with dec at
  ...   | yes _ = case gja of λ ()
  ...   | no ¬cs = ⊥-elim (¬cs (full at))
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | ret _ rewrite sym (vis-inj eqf) with dec at
  ...   | yes _ = case gja of λ ()
  ...   | no ¬cs = ⊥-elim (¬cs (full at))
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | vis fQ rewrite sym (vis-inj eqf) with dec at
  ...   | no ¬cs = ⊥-elim (¬cs (full at))
  ...   | yes _ with fP at a in bP | fQ at a in bQ
  ...     | just P′ | just Q′ = P′ , Q′ , sVis eqP bP , sVis eqQ bQ , sym (just-injective gja)
  ...     | just _  | nothing = case gja of λ ()
  ...     | nothing | just _  = case gja of λ ()
  ...     | nothing | nothing = case gja of λ ()
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    with P .force in eqP | Q .force in eqQ
  ... | sil _ | _ = case eqf of λ ()
  ... | ret _ | sil _ = case eqf of λ ()
  ... | ret _ | ret _ = case eqf of λ ()
  ... | ret _ | vis _ = case eqf of λ ()
  ... | ret _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | vis _ | sil _ = case eqf of λ ()
  ... | vis _ | ret _ = case eqf of λ ()
  ... | vis _ | vis _ = case eqf of λ ()
  ... | vis _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | sil _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ret _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | vis _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ... | ndbr _ _ _ _ | mix _ _ = case eqf of λ ()
  ... | mix _ _ | sil _ = case eqf of λ ()
  ... | mix _ _ | ndbr _ _ _ _ = case eqf of λ ()
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | ret _ | mix fQ Q₀ rewrite sym (mix-inj eqf) with dec at
  ...   | yes _ = case gja of λ ()
  ...   | no ¬cs = ⊥-elim (¬cs (full at))
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P₀ | ret _ rewrite sym (mix-inj eqf) with dec at
  ...   | yes _ = case gja of λ ()
  ...   | no ¬cs = ⊥-elim (¬cs (full at))
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P₀ | vis fQ rewrite sym (mix-inj eqf) with dec at
  ...   | no ¬cs = ⊥-elim (¬cs (full at))
  ...   | yes _ with fP at a in bP | fQ at a in bQ
  ...     | just P′ | just Q′ = P′ , Q′ , sMixVis eqP bP , sVis eqQ bQ , sym (just-injective gja)
  ...     | just _  | nothing = case gja of λ ()
  ...     | nothing | just _  = case gja of λ ()
  ...     | nothing | nothing = case gja of λ ()
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | vis fP | mix fQ Q₀ rewrite sym (mix-inj eqf) with dec at
  ...   | no ¬cs = ⊥-elim (¬cs (full at))
  ...   | yes _ with fP at a in bP | fQ at a in bQ
  ...     | just P′ | just Q′ = P′ , Q′ , sVis eqP bP , sMixVis eqQ bQ , sym (just-injective gja)
  ...     | just _  | nothing = case gja of λ ()
  ...     | nothing | just _  = case gja of λ ()
  ...     | nothing | nothing = case gja of λ ()
  ∥⇘-sync-inv {P = P} {Q = Q} {dec = dec} full (sMixVis {at = at} {a = a} {t′ = t′} eqf gja)
    | mix fP P₀ | mix fQ Q₀ rewrite sym (mix-inj eqf) with dec at
  ...   | no ¬cs = ⊥-elim (¬cs (full at))
  ...   | yes _ with fP at a in bP | fQ at a in bQ
  ...     | just P′ | just Q′ = P′ , Q′ , sMixVis eqP bP , sMixVis eqQ bQ , sym (just-injective gja)
  ...     | just _  | nothing = case gja of λ ()
  ...     | nothing | just _  = case gja of λ ()
  ...     | nothing | nothing = case gja of λ ()

  -- A τ of `P ∥⇘ Q` is one side's silent move.  Stated with the side condition that the
  -- STATIONARY operand is ret/vis/sil-headed (never ndbr/mix), which holds for the
  -- dining-philosophers components (`philResid`/`forkResid` are vis- or sil-headed): this
  -- rules out the ndbr/mix-headed composites whose τ (`sNdbr`/`sMixSlide`) decompose into a
  -- ∥-distribution rather than a verbatim `P′ ∥⇘ Q` / `P ∥⇘ Q′`.  Under the side condition
  -- the only τ is a component `sSil` lifted by the `sil P′ | _` / `_ | sil Q′` force clauses.
  --
  -- `NoBranchHead P` ≡ `P` is ret-, vis-, or sil-headed (i.e. NOT ndbr/mix-headed).
  NoBranchHead : ∀ {ℓr} {R : Set ℓr} → ITree DP (ExtI DP) R → Set _
  NoBranchHead {R = R} P =
      (Σ[ r ∈ R ] P .force ≡ ret r)
    ⊎ (Σ[ f ∈ _ ] P .force ≡ vis f)
    ⊎ (Σ[ P′ ∈ _ ] P .force ≡ sil P′)

  private
    -- Composite-force helpers: P sil-headed ⇒ composite slides left (`sil P′ | _`);
    -- P ret/vis-headed & Q sil-headed ⇒ composite slides right (`_ | sil Q′`).
    ∥sil-L : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P P′ : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → P .force ≡ sil P′
      → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ sil (P′ ∥⇘ cs ¿ dec ⇙ Q)
    ∥sil-L eqP rewrite eqP = refl

    ∥sil-Rret : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : ITree DP (ExtI DP) R} {Q Q′ : ITree DP (ExtI DP) S} {r}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → P .force ≡ ret r → Q .force ≡ sil Q′
      → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ sil (P ∥⇘ cs ¿ dec ⇙ Q′)
    ∥sil-Rret eqP eqQ rewrite eqP | eqQ = refl

    ∥sil-Rvis : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : ITree DP (ExtI DP) R} {Q Q′ : ITree DP (ExtI DP) S} {fP}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → P .force ≡ vis fP → Q .force ≡ sil Q′
      → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≡ sil (P ∥⇘ cs ¿ dec ⇙ Q′)
    ∥sil-Rvis eqP eqQ rewrite eqP | eqQ = refl

    -- Both ret/vis-headed ⇒ composite is ret/vis/ndbr-headed but never sil/mix.
    -- (ret|ret → ret, ret|vis/vis|ret → vis, vis|vis → vis.)  So a composite τ-step's
    -- force witness (`≡ sil`/`≡ mix`/`≡ ndbr`) is refuted — except ret|vis*-distribution
    -- never makes a τ since both heads are ret/vis (no sil/ndbr/mix component).  We expose
    -- the four combos and refute the τ-step's force premise directly.
    -- Ret-or-vis-headed (the offer fn / ret value is existentially bundled, so no leftover
    -- metas leak when a side is ret-headed).
    RVHead : ∀ {ℓr} {R : Set ℓr} → ITree DP (ExtI DP) R → Set _
    RVHead {R = R} P = (Σ[ r ∈ R ] P .force ≡ ret r) ⊎ (Σ[ f ∈ _ ] P .force ≡ vis f)

    ∥rv-no-sil : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S} {t′}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RVHead P → RVHead Q → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≢ sil t′
    ∥rv-no-sil (inj₁ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-sil (inj₁ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-sil (inj₂ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-sil (inj₂ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()

    ∥rv-no-mix : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S} {g t′}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RVHead P → RVHead Q → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≢ mix g t′
    ∥rv-no-mix (inj₁ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-mix (inj₁ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-mix (inj₂ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-mix (inj₂ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()

    ∥rv-no-ndbr : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S} {g wi wa prf}
        {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
      → RVHead P → RVHead Q → (P ∥⇘ cs ¿ dec ⇙ Q) .force ≢ ndbr g wi wa prf
    ∥rv-no-ndbr (inj₁ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-ndbr (inj₁ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-ndbr (inj₂ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ∥rv-no-ndbr (inj₂ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()

  ∥⇘-τ-inv : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S}
      {cs : AnyTypes DP → Set} {dec : (at : AnyTypes DP) → Dec (cs at)}
    → NoBranchHead P → NoBranchHead Q
    → ∀ {t′}
    → (P ∥⇘ cs ¿ dec ⇙ Q) ─[ τ ]─► t′
    → (Σ[ P′ ∈ ITree DP (ExtI DP) R ] ((P ─[ τ ]─► P′) × (t′ ≡ P′ ∥⇘ cs ¿ dec ⇙ Q)))
    ⊎ (Σ[ Q′ ∈ ITree DP (ExtI DP) S ] ((Q ─[ τ ]─► Q′) × (t′ ≡ P ∥⇘ cs ¿ dec ⇙ Q′)))
  -- P sil-headed: composite slides left (`sil P′ | _` clause), regardless of Q's head.
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₂ (P′ , peq))) _ (sSil eqf) =
    inj₁ (P′ , sSil peq , sym (sil-injective (trans (sym (∥sil-L peq)) eqf)))
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₂ (P′ , peq))) _ (sNdbr eqf _) =
    case trans (sym eqf) (∥sil-L peq) of λ ()
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₂ (P′ , peq))) _ (sMixSlide eqf) =
    case trans (sym eqf) (∥sil-L peq) of λ ()
  -- P ret-headed, Q sil-headed: composite slides right (`_ | sil Q′` clause).
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ (_ , peq)) (inj₂ (inj₂ (Q′ , qeq))) (sSil eqf) =
    inj₂ (Q′ , sSil qeq , sym (sil-injective (trans (sym (∥sil-Rret peq qeq)) eqf)))
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ (_ , peq)) (inj₂ (inj₂ (Q′ , qeq))) (sNdbr eqf _) =
    case trans (sym eqf) (∥sil-Rret peq qeq) of λ ()
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ (_ , peq)) (inj₂ (inj₂ (Q′ , qeq))) (sMixSlide eqf) =
    case trans (sym eqf) (∥sil-Rret peq qeq) of λ ()
  -- P vis-headed, Q sil-headed: composite slides right.
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ (_ , peq))) (inj₂ (inj₂ (Q′ , qeq))) (sSil eqf) =
    inj₂ (Q′ , sSil qeq , sym (sil-injective (trans (sym (∥sil-Rvis peq qeq)) eqf)))
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ (_ , peq))) (inj₂ (inj₂ (Q′ , qeq))) (sNdbr eqf _) =
    case trans (sym eqf) (∥sil-Rvis peq qeq) of λ ()
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ (_ , peq))) (inj₂ (inj₂ (Q′ , qeq))) (sMixSlide eqf) =
    case trans (sym eqf) (∥sil-Rvis peq qeq) of λ ()
  -- Both ret/vis-headed: composite is ret/vis-headed, so it has NO τ-step.
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ p) (inj₁ q) (sSil eqf) =
    ⊥-elim (∥rv-no-sil (inj₁ p) (inj₁ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ p) (inj₁ q) (sNdbr eqf _) =
    ⊥-elim (∥rv-no-ndbr (inj₁ p) (inj₁ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ p) (inj₁ q) (sMixSlide eqf) =
    ⊥-elim (∥rv-no-mix (inj₁ p) (inj₁ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ p) (inj₂ (inj₁ q)) (sSil eqf) =
    ⊥-elim (∥rv-no-sil (inj₁ p) (inj₂ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ p) (inj₂ (inj₁ q)) (sNdbr eqf _) =
    ⊥-elim (∥rv-no-ndbr (inj₁ p) (inj₂ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₁ p) (inj₂ (inj₁ q)) (sMixSlide eqf) =
    ⊥-elim (∥rv-no-mix (inj₁ p) (inj₂ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ p)) (inj₁ q) (sSil eqf) =
    ⊥-elim (∥rv-no-sil (inj₂ p) (inj₁ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ p)) (inj₁ q) (sNdbr eqf _) =
    ⊥-elim (∥rv-no-ndbr (inj₂ p) (inj₁ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ p)) (inj₁ q) (sMixSlide eqf) =
    ⊥-elim (∥rv-no-mix (inj₂ p) (inj₁ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) (sSil eqf) =
    ⊥-elim (∥rv-no-sil (inj₂ p) (inj₂ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) (sNdbr eqf _) =
    ⊥-elim (∥rv-no-ndbr (inj₂ p) (inj₂ q) eqf)
  ∥⇘-τ-inv {P = P} {Q = Q} (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) (sMixSlide eqf) =
    ⊥-elim (∥rv-no-mix (inj₂ p) (inj₂ q) eqf)

  -------------------------------------------------------------------------------------
  -- 3e′-iii-a, Task 3.
  --
  -- Step 1: `philResid`/`forkResid` are `NoBranchHead` (ret/vis/sil-headed, never
  -- ndbr/mix), so they may be fed to `∥⇘-τ-inv`.  An interleave `P ⦀ Q` of two
  -- `NoBranchHead` trees is itself `NoBranchHead` (`⦀-NBH`): every `_⦀_` force combo of
  -- ret/vis/sil heads is ret/vis/sil (only ndbr/mix inputs yield ndbr/mix outputs).  Each
  -- `philState`/`forkState` position is vis- or sil-headed (`*-force-*`), and `Skip`
  -- (the `[]` residual) is ret-headed; induction on the index list lifts this to the
  -- whole interleaving.
  -------------------------------------------------------------------------------------

  private
    -- `_⦀_` of two ret/vis/sil-headed trees is ret/vis/sil-headed.  We `rewrite` both
    -- component force-witnesses; the `_⦀_` force then computes to a concrete ret/vis/sil
    -- node, named by `inj₁`/`inj₂ (inj₁ …)`/`inj₂ (inj₂ …)`.  (The `sil P′ | _` clause
    -- fires first when P is sil-headed; otherwise the `_ | sil Q′` clause; the remaining
    -- ret/vis|ret/vis combos give ret or vis.)
    ⦀-NBH : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S}
      → NoBranchHead P → NoBranchHead Q → NoBranchHead (P ⦀ Q)
    -- P sil-headed: `sil P′ | _` ⇒ composite sil.
    ⦀-NBH {P = P} {Q = Q} (inj₂ (inj₂ (P′ , pe))) _ rewrite pe = inj₂ (inj₂ (P′ ⦀ Q , refl))
    -- P ret-headed.
    ⦀-NBH {P = P} {Q = Q} (inj₁ (r , pe)) (inj₁ (s , qe)) rewrite pe | qe = inj₁ ((r , s) , refl)
    ⦀-NBH {P = P} {Q = Q} (inj₁ (r , pe)) (inj₂ (inj₁ (fQ , qe))) rewrite pe | qe = inj₂ (inj₁ (_ , refl))
    ⦀-NBH {P = P} {Q = Q} (inj₁ (r , pe)) (inj₂ (inj₂ (Q′ , qe))) rewrite pe | qe = inj₂ (inj₂ (P ⦀ Q′ , refl))
    -- P vis-headed.
    ⦀-NBH {P = P} {Q = Q} (inj₂ (inj₁ (fP , pe))) (inj₁ (s , qe)) rewrite pe | qe = inj₂ (inj₁ (_ , refl))
    ⦀-NBH {P = P} {Q = Q} (inj₂ (inj₁ (fP , pe))) (inj₂ (inj₁ (fQ , qe))) rewrite pe | qe = inj₂ (inj₁ (_ , refl))
    ⦀-NBH {P = P} {Q = Q} (inj₂ (inj₁ (fP , pe))) (inj₂ (inj₂ (Q′ , qe))) rewrite pe | qe = inj₂ (inj₂ (P ⦀ Q′ , refl))

    -- positions are vis- or sil-headed (NoBranchHead), never ret/ndbr/mix.
    philState-NBH : ∀ {f s} i (pos : PhilPos) → NoBranchHead (philState f s i pos)
    philState-NBH {f}{s} i think  = inj₂ (inj₁ (_ , philState-force-think  {f}{s} i))
    philState-NBH {f}{s} i held1  = inj₂ (inj₁ (_ , philState-force-held1  {f}{s} i))
    philState-NBH {f}{s} i held2  = inj₂ (inj₁ (_ , philState-force-held2  {f}{s} i))
    philState-NBH {f}{s} i down1  = inj₂ (inj₁ (_ , philState-force-down1  {f}{s} i))
    philState-NBH {f}{s} i reloop = inj₂ (inj₂ (_ , philState-force-reloop {f}{s} i))

    forkState-NBH : ∀ j (pos : ForkPos) → NoBranchHead (forkState j pos)
    forkState-NBH j free    = inj₂ (inj₁ (_ , forkState-force-free    j))
    forkState-NBH j heldOwn = inj₂ (inj₁ (_ , forkState-force-heldOwn j))
    forkState-NBH j heldNbr = inj₂ (inj₁ (_ , forkResNbr-force        j))
    forkState-NBH j reloop  = inj₂ (inj₂ (_ , forkState-force-reloop  j))

  philResid-NBH : ∀ {f s} (S : List Phil) (cfg : Phil → PhilPos)
                → NoBranchHead (philResid {f}{s} S cfg)
  philResid-NBH []       cfg = inj₁ (tt , refl)
  philResid-NBH {f}{s} (i ∷ S′) cfg =
    ⦀-NBH (philState-NBH {f}{s} i (cfg i)) (philResid-NBH {f}{s} S′ cfg)

  forkResid-NBH : (S : List Fork) (cfg : Fork → ForkPos)
                → NoBranchHead (forkResid S cfg)
  forkResid-NBH []       cfg = inj₁ (tt , refl)
  forkResid-NBH (j ∷ S′) cfg =
    ⦀-NBH (forkState-NBH j (cfg j)) (forkResid-NBH S′ cfg)

  -------------------------------------------------------------------------------------
  -- Step 2: `⊳-ev-sound` — a visible SYSTEM′ step realises a config-step `⊳⟨ e ⟩`.
  --
  -- `∥⇘-sync-inv` (full sync) splits the step into synchronised phil/fork sub-steps;
  -- `philResid-advance`/`forkResid-advance` (Task 2) advance the named components to
  -- `philState … posᵢ` / `forkState … posⱼ` and pin the residual.  We then INVERT the
  -- two per-component steps to (a) pin the event `e` to one of the four philosopher
  -- transitions (`picks i (f i)` / `picks i (s i)` / `putsdown i (s i)` / `putsdown i
  -- (f i)`) and the target `posᵢ`, and (b) read the OWN/NBR discriminant off the fork
  -- step (`free` firing own `picks j j` vs neighbour `picks (j ⊖1) j`).  Each
  -- (position, event) combo selects its `⊳⟨_⟩` constructor.
  -------------------------------------------------------------------------------------

  -- The cyclic-arithmetic round trip `(k ⊖1) ⊕1 ≡ k`, used to turn the fork's neighbour
  -- equation `i ≡ (f i) ⊖1` into the constructor's `f i ≡ i ⊕1`.
  private
    ⊖⊕ : ∀ (k : Fork) → (k ⊖1) ⊕1 ≡ k
    ⊖⊕ Fin.zero with suc (toℕ {n} (fromℕ< (n<1+n (suc m)))) <? n
    ... | yes p = ⊥-elim (<-irrefl (cong suc (toℕ-fromℕ< (n<1+n (suc m)))) p)
    ... | no ¬p = refl
    ⊖⊕ (Fin.suc i) with suc (toℕ {n} (inject₁ i)) <? n
    ... | yes p = toℕ-injective (trans (toℕ-fromℕ< p) (cong suc (toℕ-inject₁ i)))
    ... | no ¬p rewrite toℕ-inject₁ i = ⊥-elim (¬p (toℕ<n (Fin.suc i)))

    -- `toℕ (x ⊖1)` read off the shape of `x` (`fzero` ↦ `suc m`).
    toℕ-⊖1-zero : toℕ (Fin.zero {n = suc m} ⊖1) ≡ suc m
    toℕ-⊖1-zero = toℕ-fromℕ< (n<1+n (suc m))

    -- The other round trip `(i ⊕1) ⊖1 ≡ i`, needed for the neighbour `valid-step` cases
    -- (`f i ≡ i ⊕1` ⇒ `(f i) ⊖1 ≡ i`).
    ⊕⊖ : ∀ (i : Fork) → (i ⊕1) ⊖1 ≡ i
    ⊕⊖ i with suc (toℕ i) <? n
    ... | no ¬p =
          -- `i` is the maximum (`toℕ i ≡ suc m`); `i ⊕1 = fzero`, `fzero ⊖1` has `toℕ ≡ suc m`.
          toℕ-injective (trans toℕ-⊖1-zero (sym (≮⇒max ¬p)))
      where
        -- `toℕ i < n = suc (suc m)` gives `toℕ i ≤ suc m`; `¬ (suc (toℕ i) < n)` forbids
        -- `toℕ i < suc m`; hence `toℕ i ≡ suc m`.
        ≮⇒max : ¬ (suc (toℕ i) < n) → toℕ i ≡ suc m
        ≮⇒max np with toℕ i ≟ℕ suc m
        ... | yes e  = e
        ... | no  ne = ⊥-elim (np (s≤s (≤∧≢⇒< (≤-pred (toℕ<n i)) ne)))
    ... | yes p =
          -- `fromℕ<`'s first implicit `suc (toℕ i)` is `suc _`, so `i ⊕1 = fromℕ< p` reduces
          -- DEFINITIONALLY to `Fin.suc (fromℕ< (s<s⁻¹ p))`; hence `(i ⊕1) ⊖1 = inject₁ (fromℕ<
          -- (s<s⁻¹ p))`, whose `toℕ` is `toℕ (fromℕ< (s<s⁻¹ p)) ≡ toℕ i`.
          toℕ-injective (trans (toℕ-inject₁ (fromℕ< (s<s⁻¹ p))) (toℕ-fromℕ< (s<s⁻¹ p)))

    -- Head-pinning determinacy: a `picks`-headed position firing `pAt i′ f′` to `just t″`
    -- forces `i′ ≡ i`, `f′ ≡ hd`, and `t″ ≡ philState f s i res`.
    phil-pk-detH :
      ∀ {f s} i (hd : Fork) {t″}
      → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
      → (res : PhilPos)
      → (fires  : fb (pAt i hd) tt ≡ just (philState f s i res))
      → (refuse : ∀ i′ f′ → ¬ ((i ≡ i′) × (hd ≡ f′)) → fb (pAt i′ f′) tt ≡ nothing)
      → ∀ i′ f′ → fb (pAt i′ f′) tt ≡ just t″
      → (i′ ≡ i) × (f′ ≡ hd) × (t″ ≡ philState f s i res)
    phil-pk-detH {f}{s} i hd fb res fires refuse i′ f′ gja
      with i Fin.≟ i′ | hd Fin.≟ f′
    ... | yes refl | yes refl = refl , refl , sym (just-injective (trans (sym fires) gja))
    ... | no ¬i | _ = case trans (sym (refuse i′ f′ (λ { (e , _) → ¬i e }))) gja of λ ()
    ... | _ | no ¬h = case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬h e }))) gja of λ ()

    phil-pd-detH :
      ∀ {f s} i (hd : Fork) {t″}
      → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
      → (res : PhilPos)
      → (fires  : fb (⊤ {lzero} , putsdown i hd) tt ≡ just (philState f s i res))
      → (refuse : ∀ i′ f′ → ¬ ((i ≡ i′) × (hd ≡ f′)) → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing)
      → ∀ i′ f′ → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ just t″
      → (i′ ≡ i) × (f′ ≡ hd) × (t″ ≡ philState f s i res)
    phil-pd-detH {f}{s} i hd fb res fires refuse i′ f′ gja
      with i Fin.≟ i′ | hd Fin.≟ f′
    ... | yes refl | yes refl = refl , refl , sym (just-injective (trans (sym fires) gja))
    ... | no ¬i | _ = case trans (sym (refuse i′ f′ (λ { (e , _) → ¬i e }))) gja of λ ()
    ... | _ | no ¬h = case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬h e }))) gja of λ ()

    -- Fork `free` head-pinning: a `picks i′ f′` firing of `free` to `just t″` is either
    -- OWN (`i′ ≡ j`, `f′ ≡ j`, `t″ ≡ heldOwn`) or NEIGHBOUR (`i′ ≡ j ⊖1`, `f′ ≡ j`,
    -- `t″ ≡ heldNbr`).
    fork-free-detH :
      ∀ j {t″}
      → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
      → (fires-own : fb (pAt j j) tt ≡ just (forkState j heldOwn))
      → (fires-nbr : fb (pAt (j ⊖1) j) tt ≡ just (forkState j heldNbr))
      → (refuse : ∀ i′ f′ → ¬ ((j ≡ i′) × (j ≡ f′)) → ¬ (((j ⊖1) ≡ i′) × (j ≡ f′))
                → fb (pAt i′ f′) tt ≡ nothing)
      → ∀ i′ f′ → fb (pAt i′ f′) tt ≡ just t″
      → ((i′ ≡ j) × (f′ ≡ j) × (t″ ≡ forkState j heldOwn))
      ⊎ ((i′ ≡ j ⊖1) × (f′ ≡ j) × (t″ ≡ forkState j heldNbr))
    fork-free-detH j fb fires-own fires-nbr refuse i′ f′ gja
      with j Fin.≟ i′ | (j ⊖1) Fin.≟ i′ | j Fin.≟ f′
    ... | yes refl | _        | yes refl =
          inj₁ (refl , refl , sym (just-injective (trans (sym fires-own) gja)))
    ... | no ¬o    | yes refl | yes refl =
          inj₂ (refl , refl , sym (just-injective (trans (sym fires-nbr) gja)))
    ... | no ¬o    | no ¬nb   | yes refl =
          case trans (sym (refuse i′ f′ (λ { (e , _) → ¬o e }) (λ { (e , _) → ¬nb e }))) gja
            of λ ()
    ... | yes refl | _        | no ¬f =
          case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬f e }) (λ { (_ , e) → ¬f e }))) gja
            of λ ()
    ... | no ¬o    | yes refl | no ¬f =
          case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬f e }) (λ { (_ , e) → ¬f e }))) gja
            of λ ()
    ... | no ¬o    | no ¬nb   | no ¬f =
          case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬f e }) (λ { (_ , e) → ¬f e }))) gja
            of λ ()

  -- Per-position philosopher step inversion: pin the event `e` and the target position.
  -- Matching `sVis {at}{a}` unifies `e ≡ evLabel _ (proj₂ at) a`; splitting `at` into a
  -- concrete `picks`/`putsdown` head and `a = tt`, then `rewrite`ing the offer by the
  -- position's force lemma, hands `gja` to the head-pinning det/refuse facts.
  private
    philStep-think : ∀ {f s} i {e t′}
      → philState f s i think ─[ ev (evl e) ]─► t′
      → (e ≡ evLabel _ (picks i (f i)) tt) × (t′ ≡ philState f s i held1)
    philStep-think {f}{s} i (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (philState-force-think {f}{s} i))
      with phil-pk-detH {f}{s} i (f i) (pfb-think f s i) held1
             (phil-think-fires {f}{s} i)
             (λ i″ f″ ¬eq → phil-think-refuses-picks {f}{s} i i″ f″ ¬eq) i′ f′ gja
    ... | refl , refl , teq = refl , teq
    philStep-think {f}{s} i (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (philState-force-think {f}{s} i)) =
        case trans (sym (phil-think-refuses-pd {f}{s} i i′ f′)) gja of λ ()
    philStep-think {f}{s} i (sMixVis eqf _) =
      case trans (sym eqf) (philState-force-think {f}{s} i) of λ ()

    philStep-held1 : ∀ {f s} i {e t′}
      → philState f s i held1 ─[ ev (evl e) ]─► t′
      → (e ≡ evLabel _ (picks i (s i)) tt) × (t′ ≡ philState f s i held2)
    philStep-held1 {f}{s} i (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (philState-force-held1 {f}{s} i))
      with phil-pk-detH {f}{s} i (s i) (pfb-held1 f s i) held2
             (phil-held1-fires {f}{s} i)
             (λ i″ f″ ¬eq → phil-held1-refuses-picks {f}{s} i i″ f″ ¬eq) i′ f′ gja
    ... | refl , refl , teq = refl , teq
    philStep-held1 {f}{s} i (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (philState-force-held1 {f}{s} i)) =
        case trans (sym (phil-held1-refuses-pd {f}{s} i i′ f′)) gja of λ ()
    philStep-held1 {f}{s} i (sMixVis eqf _) =
      case trans (sym eqf) (philState-force-held1 {f}{s} i) of λ ()

    philStep-held2 : ∀ {f s} i {e t′}
      → philState f s i held2 ─[ ev (evl e) ]─► t′
      → (e ≡ evLabel _ (putsdown i (s i)) tt) × (t′ ≡ philState f s i down1)
    philStep-held2 {f}{s} i (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (philState-force-held2 {f}{s} i))
      with phil-pd-detH {f}{s} i (s i) (pfb-held2 f s i) down1
             (phil-held2-fires {f}{s} i)
             (λ i″ f″ ¬eq → phil-held2-refuses-pd {f}{s} i i″ f″ ¬eq) i′ f′ gja
    ... | refl , refl , teq = refl , teq
    philStep-held2 {f}{s} i (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (philState-force-held2 {f}{s} i)) =
        case trans (sym (phil-held2-refuses-pk {f}{s} i i′ f′)) gja of λ ()
    philStep-held2 {f}{s} i (sMixVis eqf _) =
      case trans (sym eqf) (philState-force-held2 {f}{s} i) of λ ()

    philStep-down1 : ∀ {f s} i {e t′}
      → philState f s i down1 ─[ ev (evl e) ]─► t′
      → (e ≡ evLabel _ (putsdown i (f i)) tt) × (t′ ≡ philState f s i reloop)
    philStep-down1 {f}{s} i (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (philState-force-down1 {f}{s} i))
      with phil-pd-detH {f}{s} i (f i) (pfb-down1 f s i) reloop
             (phil-down1-fires {f}{s} i)
             (λ i″ f″ ¬eq → phil-down1-refuses-pd {f}{s} i i″ f″ ¬eq) i′ f′ gja
    ... | refl , refl , teq = refl , teq
    philStep-down1 {f}{s} i (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (philState-force-down1 {f}{s} i)) =
        case trans (sym (phil-down1-refuses-pk {f}{s} i i′ f′)) gja of λ ()
    philStep-down1 {f}{s} i (sMixVis eqf _) =
      case trans (sym eqf) (philState-force-down1 {f}{s} i) of λ ()

    -- `reloop` is sil-headed: it has no `ev` step.
    philStep-reloop-⊥ : ∀ {f s} i {e t′ ℓ} {A : Set ℓ}
      → philState f s i reloop ─[ ev (evl e) ]─► t′ → A
    philStep-reloop-⊥ {f}{s} i (sVis eqf _) =
      case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()
    philStep-reloop-⊥ {f}{s} i (sMixVis eqf _) =
      case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()

    -- Fork step inversion at the branching `free` position (own / neighbour).
    forkStep-free : ∀ j {e t′}
      → forkState j free ─[ ev (evl e) ]─► t′
      → ((e ≡ evLabel _ (picks j j) tt)        × (t′ ≡ forkState j heldOwn))
      ⊎ ((e ≡ evLabel _ (picks (j ⊖1) j) tt)   × (t′ ≡ forkState j heldNbr))
    forkStep-free j (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (forkState-force-free j))
      with fork-free-detH j (loop0-fb (Fbody j) (FORK-fb j))
             (FORK-fires j) (FORK-fires-nbr′ j)
             (λ i″ f″ ¬own ¬nbr → fork-free-refuses-pk j i″ f″ ¬own ¬nbr) i′ f′ gja
    ... | inj₁ (refl , refl , teq) = inj₁ (refl , teq)
    ... | inj₂ (refl , refl , teq) = inj₂ (refl , teq)
    forkStep-free j (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (forkState-force-free j)) =
        case trans (sym (fork-free-refuses-pd j i′ f′)) gja of λ ()
    forkStep-free j (sMixVis eqf _) =
      case trans (sym eqf) (forkState-force-free j) of λ ()

    -- A fork firing a concrete `picks pi pf` event: it must be at `free`, and the firing
    -- is own (`pi ≡ j`, `pf ≡ j`, → heldOwn) or neighbour (`pi ≡ j ⊖1`, `pf ≡ j`, →
    -- heldNbr).  heldOwn/heldNbr offer only `putsdown` (refuse picks); reloop is sil.
    -- The returned `pos ≡ free` records that the fork was idle before the `picks` (a
    -- `picks` fires only at `free`); `valid-step` uses it as the fork-prior-free fact.
    forkStep-picks : ∀ j (pos : ForkPos) {pi pf t′}
      → forkState j pos ─[ ev (evl (evLabel _ (picks pi pf) tt)) ]─► t′
      → ( ((pi ≡ j) × (pf ≡ j) × (t′ ≡ forkState j heldOwn))
        ⊎ ((pi ≡ j ⊖1) × (pf ≡ j) × (t′ ≡ forkState j heldNbr)) )
        × (pos ≡ free)
    forkStep-picks j free {pi}{pf}
      (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (forkState-force-free j)) =
        fork-free-detH j (loop0-fb (Fbody j) (FORK-fb j))
          (FORK-fires j) (FORK-fires-nbr′ j)
          (λ i″ f″ ¬own ¬nbr → fork-free-refuses-pk j i″ f″ ¬own ¬nbr) pi pf gja
        , refl
    forkStep-picks j free (sMixVis eqf _) =
      case trans (sym eqf) (forkState-force-free j) of λ ()
    forkStep-picks j heldOwn
      (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (forkState-force-heldOwn j)) =
        case trans (sym (fork-heldOwn-refuses-pk j i′ f′)) gja of λ ()
    forkStep-picks j heldOwn (sMixVis eqf _) =
      case trans (sym eqf) (forkState-force-heldOwn j) of λ ()
    forkStep-picks j heldNbr
      (sVis {at = _ , picks i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (forkResNbr-force j)) =
        case trans (sym (fork-heldNbr-refuses-pk j i′ f′)) gja of λ ()
    forkStep-picks j heldNbr (sMixVis eqf _) =
      case trans (sym eqf) (forkResNbr-force j) of λ ()
    forkStep-picks j reloop (sVis eqf _) =
      case trans (sym eqf) (forkState-force-reloop j) of λ ()
    forkStep-picks j reloop (sMixVis eqf _) =
      case trans (sym eqf) (forkState-force-reloop j) of λ ()

    -- Head-pinning det for a single-head `putsdown`-position (heldOwn/heldNbr → reloop):
    -- the offered second index `f′ ≡ hf` (= j), and the target is `reloop`.
    fork-pd-detH :
      ∀ j (hi hf : Fork) {t″}
      → (fb : (at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥)))
      → (fires  : fb (⊤ {lzero} , putsdown hi hf) tt ≡ just (forkState j reloop))
      → (refuse : ∀ i′ f′ → ¬ ((hi ≡ i′) × (hf ≡ f′)) → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ nothing)
      → ∀ i′ f′ → fb (⊤ {lzero} , putsdown i′ f′) tt ≡ just t″
      → (f′ ≡ hf) × (t″ ≡ forkState j reloop)
    fork-pd-detH j hi hf fb fires refuse i′ f′ gja
      with hi Fin.≟ i′ | hf Fin.≟ f′
    ... | yes refl | yes refl = refl , sym (just-injective (trans (sym fires) gja))
    ... | no ¬i | _ = case trans (sym (refuse i′ f′ (λ { (e , _) → ¬i e }))) gja of λ ()
    ... | _ | no ¬h = case trans (sym (refuse i′ f′ (λ { (_ , e) → ¬h e }))) gja of λ ()

    -- A fork firing a concrete `putsdown` event: it must be at heldOwn or heldNbr; the
    -- event's second index equals `j` and the target is `reloop`.  free offers only `picks`
    -- (refuse putsdown); reloop is sil.
    forkStep-putsdown : ∀ j (pos : ForkPos) {pi pf t′}
      → forkState j pos ─[ ev (evl (evLabel _ (putsdown pi pf) tt)) ]─► t′
      → (pf ≡ j) × (t′ ≡ forkState j reloop)
    forkStep-putsdown j heldOwn {pi}{pf}
      (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (forkState-force-heldOwn j)) =
        fork-pd-detH j j j (forkRes-fb j) (fork-heldOwn-fires j)
          (λ i″ f″ ¬eq → fork-heldOwn-refuses-pd j i″ f″ ¬eq) pi pf gja
    forkStep-putsdown j heldOwn (sMixVis eqf _) =
      case trans (sym eqf) (forkState-force-heldOwn j) of λ ()
    forkStep-putsdown j heldNbr {pi}{pf}
      (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (forkResNbr-force j)) =
        fork-pd-detH j (j ⊖1) j (forkResNbr-fb j) (fork-heldNbr-fires j)
          (λ i″ f″ ¬eq → fork-heldNbr-refuses-pd j i″ f″ ¬eq) pi pf gja
    forkStep-putsdown j heldNbr (sMixVis eqf _) =
      case trans (sym eqf) (forkResNbr-force j) of λ ()
    forkStep-putsdown j free
      (sVis {at = _ , putsdown i′ f′} {a = tt} eqf gja)
      rewrite vis-inj (trans (sym eqf) (forkState-force-free j)) =
        case trans (sym (fork-free-refuses-pd j i′ f′)) gja of λ ()
    forkStep-putsdown j free (sMixVis eqf _) =
      case trans (sym eqf) (forkState-force-free j) of λ ()
    forkStep-putsdown j reloop (sVis eqf _) =
      case trans (sym eqf) (forkState-force-reloop j) of λ ()
    forkStep-putsdown j reloop (sMixVis eqf _) =
      case trans (sym eqf) (forkState-force-reloop j) of λ ()

  -- The config-step soundness for a visible event.  `∥⇘-sync-inv` (full sync) splits into
  -- synchronised sub-steps; the Task-2 advances move the named phil/fork components and pin
  -- the composite residual; the per-position step inversions pin the event + targets and
  -- the OWN/NBR discriminant, selecting the `⊳⟨_⟩` constructor.
  --
  -- A combined per-component assembler with the indices `i`/`j` and the residual
  -- reassembly ABSTRACTED.  Taking `i`/`j` as ordinary arguments (rather than `philIndex
  -- e` / `forkIndex e`) breaks the self-reference that blocks inverting the phil step's
  -- event equation `e ≡ evLabel _ (picks i (f i)) tt` (Agda cannot unify `e` against an
  -- RHS that mentions `philIndex e`).  The caller passes `i ≔ philIndex e`, `j ≔ forkIndex
  -- e` and supplies the residual-equality witnesses, but here they are opaque.
  private
    -- Rebuild the phil residual through a STATE (tree) equality at `i`, avoiding the
    -- (non-trivial) position injectivity: at `k = i` use the tree-eq `teq`; off-`i` the
    -- two patches agree (refl).
    resP-eq : ∀ {f s} (cfgP : Phil → PhilPos) i {p q}
            → philState f s i p ≡ philState f s i q
            → philResid {f}{s} allPhils (patch cfgP i p)
            ≡ philResid {f}{s} allPhils (patch cfgP i q)
    resP-eq {f}{s} cfgP i {p}{q} teq =
      philResid-congT {f}{s} allPhils
        (All.tabulate (λ {k} _ → lem k))
      where
        lem : ∀ k → philState f s k (patch cfgP i p k) ≡ philState f s k (patch cfgP i q k)
        lem k with i Fin.≟ k
        ... | yes refl = teq
        ... | no  _    = refl

    resF-eq : ∀ (cfgF : Fork → ForkPos) j {p q}
            → forkState j p ≡ forkState j q
            → forkResid allPhils (patch cfgF j p)
            ≡ forkResid allPhils (patch cfgF j q)
    resF-eq cfgF j {p}{q} teq =
      forkResid-congT allPhils
        (All.tabulate (λ {k} _ → lem k))
      where
        lem : ∀ k → forkState k (patch cfgF j p k) ≡ forkState k (patch cfgF j q k)
        lem k with j Fin.≟ k
        ... | yes refl = teq
        ... | no  _    = refl

    -- Assemble the result.  `cfg′` uses the constructor's TARGET positions (`held1`,
    -- `heldOwn`, …) at index `i`/`j`; the residual is bridged from the advance's opaque
    -- `posᵢ`/`posⱼ` via `resP-eq`/`resF-eq` (state-level), and the `⊳⟨_⟩` witness is the
    -- direct constructor, transported across the fork-index equality `f i / s i ≡ j`.
    ev-assemble : ∀ (f s : Phil → Fork) (cfgP : Phil → PhilPos) (cfgF : Fork → ForkPos)
        i j {e posᵢ posⱼ t′ P′ Q′}
      → philState f s i (cfgP i) ─[ ev (evl e) ]─► philState f s i posᵢ
      → forkState j (cfgF j) ─[ ev (evl e) ]─► forkState j posⱼ
      → P′ ≡ philResid {f}{s} allPhils (patch cfgP i posᵢ)
      → Q′ ≡ forkResid allPhils (patch cfgF j posⱼ)
      → t′ ≡ (P′ ∥⇘ syncAll ¿ syncAll-dec ⇙ Q′)
      → Σ[ cfg′ ∈ Config ]
          (t′ ≡ sysState f s cfg′ × (_⊳⟨_⟩_ {f}{s} (cfgP , cfgF) e cfg′))
    ev-assemble f s cfgP cfgF i j phStep fkStep Peq Qeq t′eq
      with cfgP i in pe
    -- think: event `picks i (f i)`, target held1; fork at `j` (= f i, free) advances own/nbr.
    ... | think
          with philStep-think {f = f} {s = s} i phStep
    ...   | refl , teqP
            with forkStep-picks j (cfgF j) fkStep
    -- own: `i ≡ j`, `f i ≡ j` ⇒ `f i ≡ i`; transport the fork patch index `f i → j`.
    ...     | inj₁ (i≡j , fi≡j , teqF) , freeF =
              (patch cfgP i held1 , patch cfgF j heldOwn)
              , trans t′eq (cong₂ (λ A B → A ∥⇘ syncAll ¿ syncAll-dec ⇙ B)
                  (trans Peq (resP-eq cfgP i teqP)) (trans Qeq (resF-eq cfgF j teqF)))
              , subst (λ x → _⊳⟨_⟩_ {f}{s} (cfgP , cfgF) (evLabel _ (picks i (f i)) tt) (patch cfgP i held1 , patch cfgF x heldOwn))
                      fi≡j (⊳pk1-own {f = f} {s = s} {i = i} pe (trans fi≡j (sym i≡j))
                        (trans (cong cfgF fi≡j) freeF))
    -- nbr: `i ≡ j ⊖1`, `f i ≡ j` ⇒ `f i ≡ i ⊕1`.
    ...     | inj₂ (i≡j⊖1 , fi≡j , teqF) , freeF =
              (patch cfgP i held1 , patch cfgF j heldNbr)
              , trans t′eq (cong₂ (λ A B → A ∥⇘ syncAll ¿ syncAll-dec ⇙ B)
                  (trans Peq (resP-eq cfgP i teqP)) (trans Qeq (resF-eq cfgF j teqF)))
              , subst (λ x → _⊳⟨_⟩_ {f}{s} (cfgP , cfgF) (evLabel _ (picks i (f i)) tt) (patch cfgP i held1 , patch cfgF x heldNbr))
                      fi≡j (⊳pk1-nbr {f = f} {s = s} {i = i} pe
                        (trans fi≡j (sym (trans (cong _⊕1 i≡j⊖1) (⊖⊕ j))))
                        (trans (cong cfgF fi≡j) freeF))
    ev-assemble f s cfgP cfgF i j phStep fkStep Peq Qeq t′eq
      | held1
          with philStep-held1 {f = f} {s = s} i phStep
    ...   | refl , teqP
            with forkStep-picks j (cfgF j) fkStep
    ...     | inj₁ (i≡j , si≡j , teqF) , freeF =
              (patch cfgP i held2 , patch cfgF j heldOwn)
              , trans t′eq (cong₂ (λ A B → A ∥⇘ syncAll ¿ syncAll-dec ⇙ B)
                  (trans Peq (resP-eq cfgP i teqP)) (trans Qeq (resF-eq cfgF j teqF)))
              , subst (λ x → _⊳⟨_⟩_ {f}{s} (cfgP , cfgF) (evLabel _ (picks i (s i)) tt) (patch cfgP i held2 , patch cfgF x heldOwn))
                      si≡j (⊳pk2-own {f = f} {s = s} {i = i} pe (trans si≡j (sym i≡j))
                        (trans (cong cfgF si≡j) freeF))
    ...     | inj₂ (i≡j⊖1 , si≡j , teqF) , freeF =
              (patch cfgP i held2 , patch cfgF j heldNbr)
              , trans t′eq (cong₂ (λ A B → A ∥⇘ syncAll ¿ syncAll-dec ⇙ B)
                  (trans Peq (resP-eq cfgP i teqP)) (trans Qeq (resF-eq cfgF j teqF)))
              , subst (λ x → _⊳⟨_⟩_ {f}{s} (cfgP , cfgF) (evLabel _ (picks i (s i)) tt) (patch cfgP i held2 , patch cfgF x heldNbr))
                      si≡j (⊳pk2-nbr {f = f} {s = s} {i = i} pe
                        (trans si≡j (sym (trans (cong _⊕1 i≡j⊖1) (⊖⊕ j))))
                        (trans (cong cfgF si≡j) freeF))
    -- held2: event `putsdown i (s i)`, target down1; fork pins `s i ≡ j` and `posⱼ ≡ reloop`.
    ev-assemble f s cfgP cfgF i j phStep fkStep Peq Qeq t′eq
      | held2
          with philStep-held2 {f = f} {s = s} i phStep
    ...   | refl , teqP
            with forkStep-putsdown j (cfgF j) fkStep
    ...     | si≡j , teqF =
              (patch cfgP i down1 , patch cfgF j reloop)
              , trans t′eq (cong₂ (λ A B → A ∥⇘ syncAll ¿ syncAll-dec ⇙ B)
                  (trans Peq (resP-eq cfgP i teqP)) (trans Qeq (resF-eq cfgF j teqF)))
              , subst (λ x → _⊳⟨_⟩_ {f}{s} (cfgP , cfgF) (evLabel _ (putsdown i (s i)) tt) (patch cfgP i down1 , patch cfgF x reloop))
                      si≡j (⊳pd-s {f = f} {s = s} {i = i} pe)
    -- down1: event `putsdown i (f i)`, target reloop; fork pins `f i ≡ j`.
    ev-assemble f s cfgP cfgF i j phStep fkStep Peq Qeq t′eq
      | down1
          with philStep-down1 {f = f} {s = s} i phStep
    ...   | refl , teqP
            with forkStep-putsdown j (cfgF j) fkStep
    ...     | fi≡j , teqF =
              (patch cfgP i reloop , patch cfgF j reloop)
              , trans t′eq (cong₂ (λ A B → A ∥⇘ syncAll ¿ syncAll-dec ⇙ B)
                  (trans Peq (resP-eq cfgP i teqP)) (trans Qeq (resF-eq cfgF j teqF)))
              , subst (λ x → _⊳⟨_⟩_ {f}{s} (cfgP , cfgF) (evLabel _ (putsdown i (f i)) tt) (patch cfgP i reloop , patch cfgF x reloop))
                      fi≡j (⊳pd-f {f = f} {s = s} {i = i} pe)
    ev-assemble f s cfgP cfgF i j phStep fkStep Peq Qeq t′eq
      | reloop = philStep-reloop-⊥ {f = f} {s = s} i phStep

  ⊳-ev-sound : ∀ {f s} {cfg : Config} {e t′}
    → sysState f s cfg ─[ ev (evl e) ]─► t′
    → Σ[ cfg′ ∈ Config ] (t′ ≡ sysState f s cfg′ × (_⊳⟨_⟩_ {f}{s} cfg e cfg′))
  ⊳-ev-sound {f}{s} {cfgP , cfgF} {e} step
    with ∥⇘-sync-inv syncAll-full step
  ... | P′ , Q′ , pStep , qStep , t′eq
        with philResid-advance allPhils allPhils-distinct cfgP pStep
           | forkResid-advance allPhils allPhils-distinct cfgF qStep
  ...     | posᵢ , phStep , i∈ , Peq | posⱼ , fkStep , j∈ , Qeq =
            ev-assemble f s cfgP cfgF (philIndex e) (forkIndex e) phStep fkStep Peq Qeq t′eq

  -------------------------------------------------------------------------------------
  -- Step 3: `⊳-τ-sound` — an internal SYSTEM′ τ realises a config τ-step `⊳τ`.
  --
  -- `∥⇘-τ-inv` (fed `philResid-NBH`/`forkResid-NBH`) splits the τ into one side's silent
  -- move.  A τ of `philResid allPhils cfg` is a `⦀`-`sSil` from the unique sil-headed
  -- component — a philosopher at `reloop` (the only sil-headed position), looping back to
  -- `think`.  `philResid-τ-advance` identifies that component `i` (`cfg i ≡ reloop`) and
  -- pins the residual `philResid allPhils (patch cfg i think)`.  Symmetric for forks
  -- (`reloop → free`).
  -------------------------------------------------------------------------------------

  private
    -- `_⦀_` force, sil clauses.
    ⦀sil-L : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {p P′ : ITree DP (ExtI DP) R} {rest : ITree DP (ExtI DP) S}
      → p .force ≡ sil P′ → (p ⦀ rest) .force ≡ sil (P′ ⦀ rest)
    ⦀sil-L eqp rewrite eqp = refl

    ⦀sil-Rret : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {p : ITree DP (ExtI DP) R} {rest Q′ : ITree DP (ExtI DP) S} {r}
      → p .force ≡ ret r → rest .force ≡ sil Q′
      → (p ⦀ rest) .force ≡ sil (p ⦀ Q′)
    ⦀sil-Rret eqp eqq rewrite eqp | eqq = refl

    ⦀sil-Rvis : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {p : ITree DP (ExtI DP) R} {rest Q′ : ITree DP (ExtI DP) S} {fp}
      → p .force ≡ vis fp → rest .force ≡ sil Q′
      → (p ⦀ rest) .force ≡ sil (p ⦀ Q′)
    ⦀sil-Rvis eqp eqq rewrite eqp | eqq = refl

    -- Both ret/vis-headed ⇒ `_⦀_` force is ret/vis (never sil/ndbr/mix).  Each takes the
    -- ret/vis witnesses (the first two `NoBranchHead` disjuncts) and refutes the bad force.
    RVH : ∀ {ℓr} {R : Set ℓr} → ITree DP (ExtI DP) R → Set _
    RVH {R = R} P = (Σ[ r ∈ R ] P .force ≡ ret r) ⊎ (Σ[ f ∈ _ ] P .force ≡ vis f)

    ⦀rv-⊥-sil : ∀ {ℓr ℓs ℓa} {R : Set ℓr} {S : Set ℓs} {A : Set ℓa}
        {p : ITree DP (ExtI DP) R} {rest : ITree DP (ExtI DP) S} {t′}
      → RVH p → RVH rest → (p ⦀ rest) .force ≡ sil t′ → A
    ⦀rv-⊥-sil (inj₁ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-sil (inj₁ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-sil (inj₂ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-sil (inj₂ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()

    ⦀rv-⊥-ndbr : ∀ {ℓr ℓs ℓa} {R : Set ℓr} {S : Set ℓs} {A : Set ℓa}
        {p : ITree DP (ExtI DP) R} {rest : ITree DP (ExtI DP) S} {g wi wa prf}
      → RVH p → RVH rest → (p ⦀ rest) .force ≡ ndbr g wi wa prf → A
    ⦀rv-⊥-ndbr (inj₁ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-ndbr (inj₁ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-ndbr (inj₂ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-ndbr (inj₂ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()

    ⦀rv-⊥-mix : ∀ {ℓr ℓs ℓa} {R : Set ℓr} {S : Set ℓs} {A : Set ℓa}
        {p : ITree DP (ExtI DP) R} {rest : ITree DP (ExtI DP) S} {g t′}
      → RVH p → RVH rest → (p ⦀ rest) .force ≡ mix g t′ → A
    ⦀rv-⊥-mix (inj₁ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-mix (inj₁ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-mix (inj₂ (_ , pe)) (inj₁ (_ , qe)) eq rewrite pe | qe = case eq of λ ()
    ⦀rv-⊥-mix (inj₂ (_ , pe)) (inj₂ (_ , qe)) eq rewrite pe | qe = case eq of λ ()

    -- A τ from a philosopher position forces `reloop → think` (only `reloop` is sil-headed).
    philState-τ-reloop : ∀ {f s} i (pos : PhilPos) {p′}
      → philState f s i pos ─[ τ ]─► p′
      → (pos ≡ reloop) × (p′ ≡ philState f s i think)
    philState-τ-reloop {f}{s} i reloop (sSil eqf) =
      refl , sil-injective (trans (sym eqf) (philState-force-reloop {f}{s} i))
    philState-τ-reloop {f}{s} i reloop (sNdbr eqf _) =
      case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i reloop (sMixSlide eqf) =
      case trans (sym eqf) (philState-force-reloop {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i think  (sSil eqf) =
      case trans (sym eqf) (philState-force-think {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i think  (sNdbr eqf _) =
      case trans (sym eqf) (philState-force-think {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i think  (sMixSlide eqf) =
      case trans (sym eqf) (philState-force-think {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i held1  (sSil eqf) =
      case trans (sym eqf) (philState-force-held1 {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i held1  (sNdbr eqf _) =
      case trans (sym eqf) (philState-force-held1 {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i held1  (sMixSlide eqf) =
      case trans (sym eqf) (philState-force-held1 {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i held2  (sSil eqf) =
      case trans (sym eqf) (philState-force-held2 {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i held2  (sNdbr eqf _) =
      case trans (sym eqf) (philState-force-held2 {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i held2  (sMixSlide eqf) =
      case trans (sym eqf) (philState-force-held2 {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i down1  (sSil eqf) =
      case trans (sym eqf) (philState-force-down1 {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i down1  (sNdbr eqf _) =
      case trans (sym eqf) (philState-force-down1 {f}{s} i) of λ ()
    philState-τ-reloop {f}{s} i down1  (sMixSlide eqf) =
      case trans (sym eqf) (philState-force-down1 {f}{s} i) of λ ()

    forkState-τ-reloop : ∀ j (pos : ForkPos) {p′}
      → forkState j pos ─[ τ ]─► p′
      → (pos ≡ reloop) × (p′ ≡ forkState j free)
    forkState-τ-reloop j reloop (sSil eqf) =
      refl , sil-injective (trans (sym eqf) (forkState-force-reloop j))
    forkState-τ-reloop j reloop (sNdbr eqf _) =
      case trans (sym eqf) (forkState-force-reloop j) of λ ()
    forkState-τ-reloop j reloop (sMixSlide eqf) =
      case trans (sym eqf) (forkState-force-reloop j) of λ ()
    forkState-τ-reloop j free    (sSil eqf) =
      case trans (sym eqf) (forkState-force-free j) of λ ()
    forkState-τ-reloop j free    (sNdbr eqf _) =
      case trans (sym eqf) (forkState-force-free j) of λ ()
    forkState-τ-reloop j free    (sMixSlide eqf) =
      case trans (sym eqf) (forkState-force-free j) of λ ()
    forkState-τ-reloop j heldOwn (sSil eqf) =
      case trans (sym eqf) (forkState-force-heldOwn j) of λ ()
    forkState-τ-reloop j heldOwn (sNdbr eqf _) =
      case trans (sym eqf) (forkState-force-heldOwn j) of λ ()
    forkState-τ-reloop j heldOwn (sMixSlide eqf) =
      case trans (sym eqf) (forkState-force-heldOwn j) of λ ()
    forkState-τ-reloop j heldNbr (sSil eqf) =
      case trans (sym eqf) (forkResNbr-force j) of λ ()
    forkState-τ-reloop j heldNbr (sNdbr eqf _) =
      case trans (sym eqf) (forkResNbr-force j) of λ ()
    forkState-τ-reloop j heldNbr (sMixSlide eqf) =
      case trans (sym eqf) (forkResNbr-force j) of λ ()

    -- A τ of `p ⦀ rest` with both operands `NoBranchHead` is one side's silent move (the
    -- `_⦀_` force of ret/vis/sil heads is ret/vis/sil, so `sNdbr`/`sMixSlide` are refuted).
    ⦀-τ-NBH-offer : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
        {p : ITree DP (ExtI DP) R} {rest : ITree DP (ExtI DP) S} {t′}
      → NoBranchHead p → NoBranchHead rest
      → (p ⦀ rest) ─[ τ ]─► t′
      → (Σ[ p′ ∈ ITree DP (ExtI DP) R ] ((p ─[ τ ]─► p′) × (t′ ≡ p′ ⦀ rest)))
      ⊎ (Σ[ r′ ∈ ITree DP (ExtI DP) S ] ((rest ─[ τ ]─► r′) × (t′ ≡ p ⦀ r′)))
    -- p sil-headed: composite slides left.
    ⦀-τ-NBH-offer {p = p} {rest = rest} (inj₂ (inj₂ (P′ , pe))) _ (sSil eqf) =
      inj₁ (P′ , sSil pe , sym (sil-injective (trans (sym (⦀sil-L pe)) eqf)))
    ⦀-τ-NBH-offer (inj₂ (inj₂ (P′ , pe))) _ (sNdbr eqf _) =
      case trans (sym eqf) (⦀sil-L pe) of λ ()
    ⦀-τ-NBH-offer (inj₂ (inj₂ (P′ , pe))) _ (sMixSlide eqf) =
      case trans (sym eqf) (⦀sil-L pe) of λ ()
    -- p ret-headed, rest sil-headed: composite slides right.
    ⦀-τ-NBH-offer {p = p} {rest = rest} (inj₁ (_ , pe)) (inj₂ (inj₂ (Q′ , qe))) (sSil eqf) =
      inj₂ (Q′ , sSil qe , sym (sil-injective (trans (sym (⦀sil-Rret pe qe)) eqf)))
    ⦀-τ-NBH-offer (inj₁ (_ , pe)) (inj₂ (inj₂ (Q′ , qe))) (sNdbr eqf _) =
      case trans (sym eqf) (⦀sil-Rret pe qe) of λ ()
    ⦀-τ-NBH-offer (inj₁ (_ , pe)) (inj₂ (inj₂ (Q′ , qe))) (sMixSlide eqf) =
      case trans (sym eqf) (⦀sil-Rret pe qe) of λ ()
    -- p vis-headed, rest sil-headed: composite slides right.
    ⦀-τ-NBH-offer {p = p} {rest = rest} (inj₂ (inj₁ (_ , pe))) (inj₂ (inj₂ (Q′ , qe))) (sSil eqf) =
      inj₂ (Q′ , sSil qe , sym (sil-injective (trans (sym (⦀sil-Rvis pe qe)) eqf)))
    ⦀-τ-NBH-offer (inj₂ (inj₁ (_ , pe))) (inj₂ (inj₂ (Q′ , qe))) (sNdbr eqf _) =
      case trans (sym eqf) (⦀sil-Rvis pe qe) of λ ()
    ⦀-τ-NBH-offer (inj₂ (inj₁ (_ , pe))) (inj₂ (inj₂ (Q′ , qe))) (sMixSlide eqf) =
      case trans (sym eqf) (⦀sil-Rvis pe qe) of λ ()
    -- both ret/vis-headed: composite ret/vis-headed, no τ-step (refute the force premises).
    ⦀-τ-NBH-offer (inj₁ p) (inj₁ q) (sSil eqf)        = ⦀rv-⊥-sil   (inj₁ p) (inj₁ q) eqf
    ⦀-τ-NBH-offer (inj₁ p) (inj₁ q) (sNdbr eqf _)     = ⦀rv-⊥-ndbr  (inj₁ p) (inj₁ q) eqf
    ⦀-τ-NBH-offer (inj₁ p) (inj₁ q) (sMixSlide eqf)   = ⦀rv-⊥-mix   (inj₁ p) (inj₁ q) eqf
    ⦀-τ-NBH-offer (inj₁ p) (inj₂ (inj₁ q)) (sSil eqf)      = ⦀rv-⊥-sil  (inj₁ p) (inj₂ q) eqf
    ⦀-τ-NBH-offer (inj₁ p) (inj₂ (inj₁ q)) (sNdbr eqf _)   = ⦀rv-⊥-ndbr (inj₁ p) (inj₂ q) eqf
    ⦀-τ-NBH-offer (inj₁ p) (inj₂ (inj₁ q)) (sMixSlide eqf) = ⦀rv-⊥-mix  (inj₁ p) (inj₂ q) eqf
    ⦀-τ-NBH-offer (inj₂ (inj₁ p)) (inj₁ q) (sSil eqf)      = ⦀rv-⊥-sil  (inj₂ p) (inj₁ q) eqf
    ⦀-τ-NBH-offer (inj₂ (inj₁ p)) (inj₁ q) (sNdbr eqf _)   = ⦀rv-⊥-ndbr (inj₂ p) (inj₁ q) eqf
    ⦀-τ-NBH-offer (inj₂ (inj₁ p)) (inj₁ q) (sMixSlide eqf) = ⦀rv-⊥-mix  (inj₂ p) (inj₁ q) eqf
    ⦀-τ-NBH-offer (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) (sSil eqf)      = ⦀rv-⊥-sil  (inj₂ p) (inj₂ q) eqf
    ⦀-τ-NBH-offer (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) (sNdbr eqf _)   = ⦀rv-⊥-ndbr (inj₂ p) (inj₂ q) eqf
    ⦀-τ-NBH-offer (inj₂ (inj₁ p)) (inj₂ (inj₁ q)) (sMixSlide eqf) = ⦀rv-⊥-mix  (inj₂ p) (inj₂ q) eqf

  -- A τ of a philosopher interleaving: the firing component `i` is at `reloop`, and the
  -- residual loops it back to `think` (the rest unchanged, via `patch`/distinctness).
  philResid-τ-advance : ∀ {f s} (S : List Phil) → Distinct S → (cfg : Phil → PhilPos) → ∀ {t′}
    → philResid {f}{s} S cfg ─[ τ ]─► t′
    → Σ[ i ∈ Phil ] ((cfg i ≡ reloop) × (i ∈ S)
        × (t′ ≡ philResid {f}{s} S (patch cfg i think)))
  philResid-τ-advance [] _ cfg (sSil eqf)      = case eqf of λ ()
  philResid-τ-advance [] _ cfg (sNdbr eqf _)   = case eqf of λ ()
  philResid-τ-advance [] _ cfg (sMixSlide eqf) = case eqf of λ ()
  philResid-τ-advance {f}{s} (i ∷ S′) dist cfg {t′} step
    with ⦀-τ-NBH-offer (philState-NBH {f}{s} i (cfg i)) (philResid-NBH {f}{s} S′ cfg) step
  -- head fired: it was sil-headed ⇒ `cfg i ≡ reloop`, loops to `think`.
  ... | inj₁ (p′ , hτ , refl)
        with philState-τ-reloop {f}{s} i (cfg i) hτ
  ...   | cfgi-rl , refl =
          i , cfgi-rl , here refl
          , cong₂ _⦀_
              (cong (philState f s i) (sym (patch-head cfg i think)))
              (philResid-cong {f}{s} S′
                 (All.map (λ {k} i≢k → sym (patch-tail cfg i think i≢k)) (proj₁ dist)))
  -- tail fired: recurse.
  philResid-τ-advance {f}{s} (i ∷ S′) dist cfg {t′} step
    | inj₂ (r′ , tτ , refl)
        with philResid-τ-advance {f}{s} S′ (proj₂ dist) cfg tτ
  ...   | i′ , cfgi′ , idx∈ , refl =
          i′ , cfgi′ , there idx∈
          , cong₂ _⦀_
              (cong (philState f s i)
                    (sym (patch-tail cfg i′ think
                            (λ eq → fresh-≢ (proj₁ dist) idx∈ (sym eq)))))
              refl

  forkResid-τ-advance : ∀ (S : List Fork) → Distinct S → (cfg : Fork → ForkPos) → ∀ {t′}
    → forkResid S cfg ─[ τ ]─► t′
    → Σ[ j ∈ Fork ] ((cfg j ≡ reloop) × (j ∈ S)
        × (t′ ≡ forkResid S (patch cfg j free)))
  forkResid-τ-advance [] _ cfg (sSil eqf)      = case eqf of λ ()
  forkResid-τ-advance [] _ cfg (sNdbr eqf _)   = case eqf of λ ()
  forkResid-τ-advance [] _ cfg (sMixSlide eqf) = case eqf of λ ()
  forkResid-τ-advance (j ∷ S′) dist cfg {t′} step
    with ⦀-τ-NBH-offer (forkState-NBH j (cfg j)) (forkResid-NBH S′ cfg) step
  ... | inj₁ (p′ , hτ , refl)
        with forkState-τ-reloop j (cfg j) hτ
  ...   | cfgj-rl , refl =
          j , cfgj-rl , here refl
          , cong₂ _⦀_
              (cong (forkState j) (sym (patch-head cfg j free)))
              (forkResid-cong S′
                 (All.map (λ {k} j≢k → sym (patch-tail cfg j free j≢k)) (proj₁ dist)))
  forkResid-τ-advance (j ∷ S′) dist cfg {t′} step
    | inj₂ (r′ , tτ , refl)
        with forkResid-τ-advance S′ (proj₂ dist) cfg tτ
  ...   | j′ , cfgj′ , idx∈ , refl =
          j′ , cfgj′ , there idx∈
          , cong₂ _⦀_
              (cong (forkState j)
                    (sym (patch-tail cfg j′ free
                            (λ eq → fresh-≢ (proj₁ dist) idx∈ (sym eq)))))
              refl

  ⊳-τ-sound : ∀ {f s} {cfg : Config} {t′}
    → sysState f s cfg ─[ τ ]─► t′
    → Σ[ cfg′ ∈ Config ] (t′ ≡ sysState f s cfg′ × cfg ⊳τ cfg′)
  ⊳-τ-sound {f}{s} {cfgP , cfgF} step
    with ∥⇘-τ-inv (philResid-NBH {f}{s} allPhils cfgP) (forkResid-NBH allPhils cfgF) step
  -- phil side: a reloop→think loop-back.
  ... | inj₁ (P′ , pτ , t′eq)
        with philResid-τ-advance {f}{s} allPhils allPhils-distinct cfgP pτ
  ...   | i , cfgPi , i∈ , refl =
          (patch cfgP i think , cfgF)
          , trans t′eq (cong (λ A → A ∥⇘ syncAll ¿ syncAll-dec ⇙ forkResid allPhils cfgF) refl)
          , ⊳τ-phil cfgPi
  -- fork side: a reloop→free loop-back.
  ⊳-τ-sound {f}{s} {cfgP , cfgF} step
    | inj₂ (Q′ , qτ , t′eq)
        with forkResid-τ-advance allPhils allPhils-distinct cfgF qτ
  ...   | j , cfgFj , j∈ , refl =
          (cfgP , patch cfgF j free)
          , trans t′eq (cong (λ B → philResid {f}{s} allPhils cfgP ∥⇘ syncAll ¿ syncAll-dec ⇙ B) refl)
          , ⊳τ-fork cfgFj

  -------------------------------------------------------------------------------------
  -- 3e′-iii-b: the validity invariant `ValidCfg` (phil↔fork consistency) + base lemmas.
  --
  -- `heldBy cfgP i x` says philosopher `i` (in position `cfgP i`) is currently holding
  -- fork `x`: in `held1`/`down1` it holds its first fork `f i`; in `held2` it holds both
  -- `f i` and `s i`; in `think`/`reloop` it holds nothing.  `ForkConsistent` ties each
  -- fork `j`'s position to the philosopher(s) that hold it (own = `j`, neighbour = `j ⊖1`),
  -- both directions.  `ValidCfg` is the pointwise invariant; `valid-init` is the start.
  -------------------------------------------------------------------------------------

  heldBy : ∀ {f s : Phil → Fork} → (Phil → PhilPos) → Phil → Fork → Set
  heldBy {f}{s} cfgP i x with cfgP i
  ... | think  = ⊥
  ... | held1  = x ≡ f i
  ... | held2  = (x ≡ f i) ⊎ (x ≡ s i)
  ... | down1  = x ≡ f i
  ... | reloop = ⊥

  ForkConsistent : ∀ {f s} → (Phil → PhilPos) → (Fork → ForkPos) → Fork → Set
  ForkConsistent {f}{s} cfgP cfgF j =
      ( cfgF j ≡ heldOwn → heldBy {f}{s} cfgP j j )
    × ( cfgF j ≡ heldNbr → heldBy {f}{s} cfgP (j ⊖1) j )
    × ( ∀ i → heldBy {f}{s} cfgP i j
            → (i ≡ j × cfgF j ≡ heldOwn) ⊎ (i ≡ (j ⊖1) × cfgF j ≡ heldNbr) )

  ValidCfg : ∀ {f s : Phil → Fork} → Config → Set
  ValidCfg {f}{s} (cfgP , cfgF) = ∀ j → ForkConsistent {f}{s} cfgP cfgF j

  valid-init : ∀ {f s} → ValidCfg {f}{s} ((λ _ → think) , (λ _ → free))
  valid-init {f}{s} j = (λ ()) , (λ ()) , (λ i h → ⊥-elim h)

  -------------------------------------------------------------------------------------
  -- 3e′-iii-b, Task 2: `ValidCfg` is preserved by every config-step.
  --
  -- `heldBy cfgP k x` only inspects `cfgP` at the queried philosopher `k`.  Each
  -- config-step touches `cfgP` at one philosopher `i` and `cfgF` at one fork `x`; we
  -- re-prove `ForkConsistent` at every fork, splitting on whether the queried holder /
  -- fork is the touched index `i` / `x` or another.  At an UNTOUCHED index `k ≢ i` the
  -- `patch`'s own `Fin.≟` reduces to `no`, so `heldBy (patch cfgP i v) k` and `heldBy
  -- cfgP k` coincide definitionally (`heldBy-tail`).  At the TOUCHED index the caller
  -- cases on `i Fin.≟ i = yes refl`, reducing `patch cfgP i v i` to the concrete `v` so
  -- `heldBy` / `cfgF` evaluate directly.  The input invariant's mutual-exclusion conjunct
  -- (3) rules out a second holder; the amended `⊳pk*` fork-prior-`free` field rules out
  -- any prior holder of a freshly-acquired fork.
  -------------------------------------------------------------------------------------

  private
    -- A `reloop`/`think` philosopher holds nothing.  `with cfgP k | eq` aligns the stuck
    -- `heldBy` scrutinee with the equation so the `⊥` clause exposes `h : ⊥`.
    heldBy-reloop-⊥ : ∀ {f s} (cfgP : Phil → PhilPos) k {x}
                    → cfgP k ≡ reloop → ¬ heldBy {f}{s} cfgP k x
    heldBy-reloop-⊥ cfgP k eq h with cfgP k | eq
    ... | reloop | refl = h

    heldBy-think-⊥ : ∀ {f s} (cfgP : Phil → PhilPos) k {x}
                   → cfgP k ≡ think → ¬ heldBy {f}{s} cfgP k x
    heldBy-think-⊥ cfgP k eq h with cfgP k | eq
    ... | think | refl = h

    -- Patching `i` (where it was `reloop`) to `think` neither adds nor removes a holding:
    -- off `i` by `heldBy-tail`; at `i` both `reloop` and `think` hold nothing.
    think-patch→ : ∀ {f s} (cfgP : Phil → PhilPos) i {k x}
                 → cfgP i ≡ reloop
                 → heldBy {f}{s} (patch cfgP i think) k x → heldBy {f}{s} cfgP k x
    think-patch→ {f}{s} cfgP i {k}{x} reloopEq h with i Fin.≟ k
    ... | yes refl = ⊥-elim h
    ... | no  i≢k  = h

    think-patch← : ∀ {f s} (cfgP : Phil → PhilPos) i {k x}
                 → cfgP i ≡ reloop
                 → heldBy {f}{s} cfgP k x → heldBy {f}{s} (patch cfgP i think) k x
    think-patch← {f}{s} cfgP i {k}{x} reloopEq h with i Fin.≟ k
    ... | yes refl = ⊥-elim (heldBy-reloop-⊥ {f}{s} cfgP i reloopEq h)
    ... | no  i≢k  = h

    -- `heldBy cfgP i j` with the old position known to be `held1` is read off
    -- (`with cfgP i | eq`).
    heldBy-old-held1→ : ∀ {f s} (cfgP : Phil → PhilPos) i {j}
                      → cfgP i ≡ held1 → heldBy {f}{s} cfgP i j → j ≡ f i
    heldBy-old-held1→ cfgP i eq h with cfgP i | eq
    ... | held1 | refl = h

    heldBy-old-held1← : ∀ {f s} (cfgP : Phil → PhilPos) i {j}
                      → cfgP i ≡ held1 → j ≡ f i → heldBy {f}{s} cfgP i j
    heldBy-old-held1← cfgP i eq jeq with cfgP i | eq
    ... | held1 | refl = jeq

    heldBy-old-held2→ : ∀ {f s} (cfgP : Phil → PhilPos) i {j}
                      → cfgP i ≡ held2 → heldBy {f}{s} cfgP i j → (j ≡ f i) ⊎ (j ≡ s i)
    heldBy-old-held2→ cfgP i eq h with cfgP i | eq
    ... | held2 | refl = h

    heldBy-old-down1→ : ∀ {f s} (cfgP : Phil → PhilPos) i {j}
                      → cfgP i ≡ down1 → heldBy {f}{s} cfgP i j → j ≡ f i
    heldBy-old-down1→ cfgP i eq h with cfgP i | eq
    ... | down1 | refl = h

    heldBy-old-held2← : ∀ {f s} (cfgP : Phil → PhilPos) i {j}
                      → cfgP i ≡ held2 → (j ≡ f i) ⊎ (j ≡ s i) → heldBy {f}{s} cfgP i j
    heldBy-old-held2← cfgP i eq d with cfgP i | eq
    ... | held2 | refl = d

    heldBy-old-down1← : ∀ {f s} (cfgP : Phil → PhilPos) i {j}
                      → cfgP i ≡ down1 → j ≡ f i → heldBy {f}{s} cfgP i j
    heldBy-old-down1← cfgP i eq jeq with cfgP i | eq
    ... | down1 | refl = jeq

    -- Two distinct holders of one fork `g` is impossible: same disjunct forces `i ≡ k`;
    -- mixed disjuncts force `cfgF g ≡ heldOwn ≡ heldNbr`.  Used by the release cases
    -- (`⊳pd-s` at `g = s i`, `⊳pd-f` at `g = f i`) to rule out a second old holder.
    mutex-distinct : ∀ {i k} (cfgF : Fork → ForkPos) (g : Fork)
                   → (i ≡ g × cfgF g ≡ heldOwn) ⊎ (i ≡ g ⊖1 × cfgF g ≡ heldNbr)
                   → (k ≡ g × cfgF g ≡ heldOwn) ⊎ (k ≡ g ⊖1 × cfgF g ≡ heldNbr)
                   → i ≢ k → ⊥
    mutex-distinct cfgF g (inj₁ (ei , _)) (inj₁ (ek , _)) i≢k = i≢k (trans ei (sym ek))
    mutex-distinct cfgF g (inj₂ (ei , _)) (inj₂ (ek , _)) i≢k = i≢k (trans ei (sym ek))
    mutex-distinct cfgF g (inj₁ (_ , o)) (inj₂ (_ , nb)) _ = case trans (sym o) nb of λ ()
    mutex-distinct cfgF g (inj₂ (_ , nb)) (inj₁ (_ , o)) _ = case trans (sym nb) o of λ ()

  valid-τ : ∀ {f s cfg cfg′} → ValidCfg {f}{s} cfg → cfg ⊳τ cfg′ → ValidCfg {f}{s} cfg′
  -- phil τ: `cfgP i : reloop → think`; `cfgF` and the holder-set are unchanged.
  valid-τ {f}{s} {cfgP , cfgF} V (⊳τ-phil {i = i} reloopEq) j =
    let (c1 , c2 , c3) = V j
    in (λ ownEq → think-patch← {f}{s} cfgP i reloopEq (c1 ownEq))
     , (λ nbrEq → think-patch← {f}{s} cfgP i reloopEq (c2 nbrEq))
     , (λ k h → c3 k (think-patch→ {f}{s} cfgP i reloopEq h))
  -- fork τ: `cfgF j : reloop → free`; `cfgP`/`heldBy` unchanged.  A reloop fork has no
  -- holder (input conjunct 3 would force `cfgF j ≡ heldOwn/heldNbr`, contradicting reloop).
  -- untouched fork `j ≢ jr`: `patch cfgF jr free j` reduces to `cfgF j` (the `patch`'s
  -- `with jr Fin.≟ j` is `no`), so the new `ForkConsistent j` is the old `V j`.
  valid-τ {f}{s} {cfgP , cfgF} V (⊳τ-fork {j = jr} reloopEq) j with jr Fin.≟ j
  ... | no  _    = V j
  ... | yes refl =
        -- the patched fork is now `free`: conjuncts 1/2 are vacuous; for conjunct 3, any
        -- holder `k` would (by input conjunct 3) force the OLD `cfgF j ≡ heldOwn/heldNbr`,
        -- contradicting the step's `cfgF j ≡ reloop`.
        let (_ , _ , c3) = V j
        in (λ ())
         , (λ ())
         , (λ k h → case c3 k h of λ
              { (inj₁ (_ , ownEq)) → case trans (sym reloopEq) ownEq of λ ()
              ; (inj₂ (_ , nbrEq)) → case trans (sym reloopEq) nbrEq of λ () })

  -- `valid-step` needs that a philosopher's two forks are distinct (`f i ≢ s i`): when a
  -- philosopher releases its SECOND fork (`⊳pd-s`, held2 → down1) it keeps the FIRST, and
  -- this only leaves the second fork free if the two are different.  This is not derivable
  -- for arbitrary `{f s}`, so it is taken as a hypothesis; it holds for the DP model's
  -- `first`/`second` (`first i ≡ i ≢ i ⊕1 ≡ second i`) and is discharged in Task 3.
  --
  -- In each case we `rewrite` the own/nbr equation (`f i ≡ i` resp. `f i ≡ i ⊕1`) so the
  -- touched fork's coordinate becomes `i` resp. `i ⊕1`, then split the queried fork `j`
  -- against the touched fork with `with i Fin.≟ j`.  At the touched fork (`yes refl`) that
  -- same `Fin.≟` reduces the `patch`es directly, so the new `cfgF`/`heldBy` goals compute to
  -- the new value (heldOwn/heldNbr/reloop) and the holder is `i` (own) / `i ⊕1`'s neighbour
  -- `i` (nbr); other holders are excluded by the prior-`free` field (acquire) or input
  -- mutual exclusion (release).  At an untouched fork (`no i≢j`) the `Fin.≟` reduces both
  -- `patch`es at `j` to the old maps, so the conjuncts reduce to the old `V j` (lifting the
  -- non-reduced neighbour/arbitrary holders by `heldBy-tail`/`heldBy-old-*` per case).
  valid-step : ∀ {f s} → (∀ i → f i ≢ s i)
             → ∀ {cfg e cfg′} → ValidCfg {f}{s} cfg → _⊳⟨_⟩_ {f}{s} cfg e cfg′ → ValidCfg {f}{s} cfg′
  ----------------------------------------------------------------------------------------
  -- ⊳pk1-own: phil `i` (own, `f i ≡ i`) takes its first fork `f i = i` (free → heldOwn).
  ----------------------------------------------------------------------------------------
  valid-step {f}{s} fs≢ V (⊳pk1-own {cfgP}{cfgF}{i} pe fi≡i freeF) j
    rewrite fi≡i with i Fin.≟ j
  -- touched fork `j = i`: now heldOwn, held by its own phil `i`.
  ... | yes refl =
        -- conjunct 1's `heldBy (patch cfgP i held1) i i` is already reduced (outer `i Fin.≟ i`
        -- = yes refl ⇒ held1) to `i ≡ f i`; witness `sym fi≡i`.
        (λ _ → sym fi≡i)
         , (λ nbrEq → case nbrEq of λ ())
         , holders
        where
          holders : ∀ k → heldBy {f}{s} (patch cfgP i held1) k i
                  → (k ≡ i × heldOwn ≡ heldOwn)
                  ⊎ (k ≡ (i ⊖1) × heldOwn ≡ heldNbr)
          holders k h with i Fin.≟ k
          ... | yes refl = inj₁ (refl , refl)
          -- (the `no i≢k` match has already reduced `patch cfgP i held1 k` to `cfgP k`, so
          -- `h : heldBy cfgP k i` directly.)
          ... | no  i≢k  with proj₂ (proj₂ (V i)) k h
          ...   | inj₁ (_ , ownEq) = case trans (sym freeF) ownEq of λ ()
          ...   | inj₂ (_ , nbrEq) = case trans (sym freeF) nbrEq of λ ()
  -- untouched fork `j ≢ i`: phil `i` (think → held1) holds only `f i = i ≠ j`, unchanged.
  ... | no i≢j =
        c1 , c2 , c3
        where
          -- conjunct 1 (holder `j`): the outer `no i≢j` reduced `patch cfgP i held1 j` to
          -- `cfgP j`, so the goal is the OLD `cfgF j ≡ heldOwn → heldBy cfgP j j` = `V j`'s.
          c1 : cfgF j ≡ heldOwn → heldBy {f}{s} cfgP j j
          c1 = proj₁ (V j)
          -- conjunct 2 (holder `j ⊖1`, NOT reduced): lift `heldBy cfgP (j⊖1) j` from `V j`.
          c2 : cfgF j ≡ heldNbr → heldBy {f}{s} (patch cfgP i held1) (j ⊖1) j
          c2 nbrEq with i Fin.≟ (j ⊖1)
          ... | no  _    = proj₁ (proj₂ (V j)) nbrEq
          ... | yes refl = ⊥-elim (heldBy-think-⊥ {f}{s} cfgP i pe (proj₁ (proj₂ (V j)) nbrEq))
          -- conjunct 3 (holder `k`): the new `i` (held1) holds only `f i = i ≠ j`.
          c3 : ∀ k → heldBy {f}{s} (patch cfgP i held1) k j
             → (k ≡ j × cfgF j ≡ heldOwn) ⊎ (k ≡ (j ⊖1) × cfgF j ≡ heldNbr)
          c3 k h with i Fin.≟ k
          ... | no  _    = proj₂ (proj₂ (V j)) k h
          ... | yes refl = ⊥-elim (i≢j (sym (trans h fi≡i)))

  ----------------------------------------------------------------------------------------
  -- ⊳pk1-nbr: phil `i` (nbr, `f i ≡ i ⊕1`) takes its first fork `f i = i ⊕1` (free → heldNbr).
  ----------------------------------------------------------------------------------------
  valid-step {f}{s} fs≢ V (⊳pk1-nbr {cfgP}{cfgF}{i} pe fi≡i⊕1 freeF) j
    rewrite fi≡i⊕1 with (i ⊕1) Fin.≟ j
  -- touched fork `j = i ⊕1`: now heldNbr, held by its neighbour `(i ⊕1) ⊖1 = i`.
  ... | yes refl =
        (λ ownEq → case ownEq of λ ())
         , (λ _ → nbr-holds)
         , holders
        where
          nb : (i ⊕1) ⊖1 ≡ i
          nb = ⊕⊖ i
          -- `i` holds its first fork `i ⊕1` (held1, `i Fin.≟ i`); transport the holder index
          -- `i → (i ⊕1) ⊖1` by `nb`.  heldBy reduces to `(i ⊕1) ≡ f i = i ⊕1` ⇒ `refl`.
          i-holds : heldBy {f}{s} (patch cfgP i held1) i (i ⊕1)
          i-holds with i Fin.≟ i
          ... | yes refl = sym fi≡i⊕1
          ... | no  ¬p   = ⊥-elim (¬p refl)
          nbr-holds : heldBy {f}{s} (patch cfgP i held1) ((i ⊕1) ⊖1) (i ⊕1)
          nbr-holds = subst (λ p → heldBy {f}{s} (patch cfgP i held1) p (i ⊕1)) (sym nb) i-holds
          holders : ∀ k → heldBy {f}{s} (patch cfgP i held1) k (i ⊕1)
                  → (k ≡ (i ⊕1) × heldNbr ≡ heldOwn)
                  ⊎ (k ≡ ((i ⊕1) ⊖1) × heldNbr ≡ heldNbr)
          holders k h with i Fin.≟ k
          ... | yes refl = inj₂ (sym (⊕⊖ i) , refl)
          ... | no  i≢k  with proj₂ (proj₂ (V (i ⊕1))) k h
          ...   | inj₁ (_ , ownEq) = case trans (sym freeF) ownEq of λ ()
          ...   | inj₂ (_ , nbrEq) = case trans (sym freeF) nbrEq of λ ()
  -- untouched fork `j ≢ i ⊕1` (note: the PHIL patch is at `i`, so the holder is lifted via
  -- `i Fin.≟ holder`, not the fork split).
  ... | no i⊕1≢j =
        c1 , c2 , c3
        where
          c1 : cfgF j ≡ heldOwn → heldBy {f}{s} (patch cfgP i held1) j j
          c1 ownEq with i Fin.≟ j
          ... | no  _    = proj₁ (V j) ownEq
          ... | yes refl = ⊥-elim (heldBy-think-⊥ {f}{s} cfgP i pe (proj₁ (V j) ownEq))
          c2 : cfgF j ≡ heldNbr → heldBy {f}{s} (patch cfgP i held1) (j ⊖1) j
          c2 nbrEq with i Fin.≟ (j ⊖1)
          ... | no  _    = proj₁ (proj₂ (V j)) nbrEq
          ... | yes refl = ⊥-elim (heldBy-think-⊥ {f}{s} cfgP i pe (proj₁ (proj₂ (V j)) nbrEq))
          c3 : ∀ k → heldBy {f}{s} (patch cfgP i held1) k j
             → (k ≡ j × cfgF j ≡ heldOwn) ⊎ (k ≡ (j ⊖1) × cfgF j ≡ heldNbr)
          c3 k h with i Fin.≟ k
          ... | no  _    = proj₂ (proj₂ (V j)) k h
          ... | yes refl = ⊥-elim (i⊕1≢j (sym (trans h fi≡i⊕1)))

  ----------------------------------------------------------------------------------------
  -- ⊳pk2-own: phil `i` (held1, own `s i ≡ i`) takes its SECOND fork `s i = i` (free → heldOwn).
  ----------------------------------------------------------------------------------------
  valid-step {f}{s} fs≢ V (⊳pk2-own {cfgP}{cfgF}{i} pe si≡i freeF) j
    rewrite si≡i with i Fin.≟ j
  -- touched fork `j = s i = i`: now heldOwn, held by its own phil `i` (via its second fork).
  ... | yes refl =
        (λ _ → inj₂ (sym si≡i))
         , (λ nbrEq → case nbrEq of λ ())
         , holders
        where
          holders : ∀ k → heldBy {f}{s} (patch cfgP i held2) k i
                  → (k ≡ i × heldOwn ≡ heldOwn) ⊎ (k ≡ (i ⊖1) × heldOwn ≡ heldNbr)
          holders k h with i Fin.≟ k
          ... | yes refl = inj₁ (refl , refl)
          ... | no  i≢k  with proj₂ (proj₂ (V i)) k h
          ...   | inj₁ (_ , ownEq) = case trans (sym freeF) ownEq of λ ()
          ...   | inj₂ (_ , nbrEq) = case trans (sym freeF) nbrEq of λ ()
  -- untouched fork `j ≢ i`: fork split reduces the held2 patch at the own holder `j`
  -- (conjunct 1 = OLD `V j`'s); the nbr holder `j ⊖1` is lifted; conjunct 3's `i` mapped.
  ... | no i≢j =
        proj₁ (V j)
         , c2
         , c3
        where
          c2 : cfgF j ≡ heldNbr → heldBy {f}{s} (patch cfgP i held2) (j ⊖1) j
          c2 nbrEq with i Fin.≟ (j ⊖1)
          ... | no  _    = proj₁ (proj₂ (V j)) nbrEq
          -- i = j ⊖1: inner `yes refl` reduced the goal to `(j ≡ f i) ⊎ (j ≡ s i)`; i held
          -- `f i = j` old (held1), so `inj₁`.
          ... | yes refl = inj₁ (heldBy-old-held1→ {f}{s} cfgP i pe (proj₁ (proj₂ (V j)) nbrEq))
          c3 : ∀ k → heldBy {f}{s} (patch cfgP i held2) k j
             → (k ≡ j × cfgF j ≡ heldOwn) ⊎ (k ≡ (j ⊖1) × cfgF j ≡ heldNbr)
          c3 k h with i Fin.≟ k
          ... | no  _    = proj₂ (proj₂ (V j)) k h
          ... | yes refl with h
          ...   | inj₁ jf = proj₂ (proj₂ (V j)) i (heldBy-old-held1← {f}{s} cfgP i pe jf)
          ...   | inj₂ jsi = ⊥-elim (i≢j (sym (trans jsi si≡i)))

  ----------------------------------------------------------------------------------------
  -- ⊳pk2-nbr: phil `i` (held1, nbr `s i ≡ i ⊕1`) takes its SECOND fork (free → heldNbr).
  ----------------------------------------------------------------------------------------
  valid-step {f}{s} fs≢ V (⊳pk2-nbr {cfgP}{cfgF}{i} pe si≡i⊕1 freeF) j
    rewrite si≡i⊕1 with (i ⊕1) Fin.≟ j
  -- touched fork `j = s i = i ⊕1`: now heldNbr, held by neighbour `(i ⊕1) ⊖1 = i` (its second).
  ... | yes refl =
        (λ ownEq → case ownEq of λ ())
         , (λ _ → nbr-holds)
         , holders
        where
          nb : (i ⊕1) ⊖1 ≡ i
          nb = ⊕⊖ i
          i-holds : heldBy {f}{s} (patch cfgP i held2) i (i ⊕1)
          i-holds with i Fin.≟ i
          ... | yes refl = inj₂ (sym si≡i⊕1)
          ... | no  ¬p   = ⊥-elim (¬p refl)
          nbr-holds : heldBy {f}{s} (patch cfgP i held2) ((i ⊕1) ⊖1) (i ⊕1)
          nbr-holds = subst (λ p → heldBy {f}{s} (patch cfgP i held2) p (i ⊕1)) (sym nb) i-holds
          holders : ∀ k → heldBy {f}{s} (patch cfgP i held2) k (i ⊕1)
                  → (k ≡ (i ⊕1) × heldNbr ≡ heldOwn) ⊎ (k ≡ ((i ⊕1) ⊖1) × heldNbr ≡ heldNbr)
          holders k h with i Fin.≟ k
          ... | yes refl = inj₂ (sym (⊕⊖ i) , refl)
          ... | no  i≢k  with proj₂ (proj₂ (V (i ⊕1))) k h
          ...   | inj₁ (_ , ownEq) = case trans (sym freeF) ownEq of λ ()
          ...   | inj₂ (_ , nbrEq) = case trans (sym freeF) nbrEq of λ ()
  ... | no i⊕1≢j =
        c1 , c2 , c3
        where
          c1 : cfgF j ≡ heldOwn → heldBy {f}{s} (patch cfgP i held2) j j
          c1 ownEq with i Fin.≟ j
          ... | no  _    = proj₁ (V j) ownEq
          ... | yes refl = inj₁ (heldBy-old-held1→ {f}{s} cfgP i pe (proj₁ (V j) ownEq))
          c2 : cfgF j ≡ heldNbr → heldBy {f}{s} (patch cfgP i held2) (j ⊖1) j
          c2 nbrEq with i Fin.≟ (j ⊖1)
          ... | no  _    = proj₁ (proj₂ (V j)) nbrEq
          ... | yes refl = inj₁ (heldBy-old-held1→ {f}{s} cfgP i pe (proj₁ (proj₂ (V j)) nbrEq))
          c3 : ∀ k → heldBy {f}{s} (patch cfgP i held2) k j
             → (k ≡ j × cfgF j ≡ heldOwn) ⊎ (k ≡ (j ⊖1) × cfgF j ≡ heldNbr)
          c3 k h with i Fin.≟ k
          ... | no  _    = proj₂ (proj₂ (V j)) k h
          ... | yes refl with h
          ...   | inj₁ jf  = proj₂ (proj₂ (V j)) i (heldBy-old-held1← {f}{s} cfgP i pe jf)
          ...   | inj₂ jsi = ⊥-elim (i⊕1≢j (sym (trans jsi si≡i⊕1)))

  ----------------------------------------------------------------------------------------
  -- ⊳pd-s: phil `i` (held2) puts down its SECOND fork `s i` (heldOwn/heldNbr → reloop).
  ----------------------------------------------------------------------------------------
  valid-step {f}{s} fs≢ V (⊳pd-s {cfgP}{cfgF}{i} pe) j
    with (s i) Fin.≟ j
  -- touched fork `j = s i` → reloop: now NO holder (i kept only `f i ≠ s i`; no second by V).
  ... | yes refl =
        (λ ownEq → case ownEq of λ ())
         , (λ nbrEq → case nbrEq of λ ())
         , holders
        where
          -- old `i` held its second fork `s i`.
          i-held-si : heldBy {f}{s} cfgP i (s i)
          i-held-si = heldBy-old-held2← {f}{s} cfgP i pe (inj₂ refl)
          holders : ∀ k → heldBy {f}{s} (patch cfgP i down1) k (s i)
                  → (k ≡ (s i) × reloop ≡ heldOwn)
                  ⊎ (k ≡ ((s i) ⊖1) × reloop ≡ heldNbr)
          holders k h with i Fin.≟ k
          -- k = i: `h` reduced to `s i ≡ f i` (down1) — impossible since `f i ≢ s i`.
          ... | yes refl = ⊥-elim (fs≢ i (sym h))
          -- k ≠ i: `h` reduced to `heldBy cfgP k (s i)`; both `i` and `k` hold `s i` old —
          -- V's mutual exclusion forbids it.
          ... | no  i≢k  =
                ⊥-elim (mutex-distinct cfgF (s i) (proj₂ (proj₂ (V (s i))) i i-held-si)
                                                  (proj₂ (proj₂ (V (s i))) k h) i≢k)
  -- untouched fork `j ≢ s i`: phil `i` still holds `f i` (kept), so its hold of `j` unchanged.
  ... | no si≢j =
        c1 , c2 , c3
        where
          -- `i`'s hold of fork `j` (≠ s i): old held2 had `(j≡f i) ⊎ (j≡s i)`; `j≠s i` leaves
          -- `j ≡ f i` (= the new down1 holding of `j`).
          jf-of : heldBy {f}{s} cfgP i j → j ≡ f i
          jf-of hold with heldBy-old-held2→ {f}{s} cfgP i pe hold
          ... | inj₁ jf  = jf
          ... | inj₂ jsi = ⊥-elim (si≢j (sym jsi))
          -- (when the inner `i Fin.≟ holder = yes refl` reduces the goal to `j ≡ f i`.)
          c1 : cfgF j ≡ heldOwn → heldBy {f}{s} (patch cfgP i down1) j j
          c1 ownEq with i Fin.≟ j
          ... | no  _    = proj₁ (V j) ownEq
          ... | yes refl = jf-of (proj₁ (V j) ownEq)
          c2 : cfgF j ≡ heldNbr → heldBy {f}{s} (patch cfgP i down1) (j ⊖1) j
          c2 nbrEq with i Fin.≟ (j ⊖1)
          ... | no  _    = proj₁ (proj₂ (V j)) nbrEq
          ... | yes refl = jf-of (proj₁ (proj₂ (V j)) nbrEq)
          c3 : ∀ k → heldBy {f}{s} (patch cfgP i down1) k j
             → (k ≡ j × cfgF j ≡ heldOwn) ⊎ (k ≡ (j ⊖1) × cfgF j ≡ heldNbr)
          c3 k h with i Fin.≟ k
          ... | no  _    = proj₂ (proj₂ (V j)) k h
          -- k = i: `h` reduced to `j ≡ f i`; i held `f i = j` old (held2 inj₁) ⇒ map via V.
          ... | yes refl = proj₂ (proj₂ (V j)) i (heldBy-old-held2← {f}{s} cfgP i pe (inj₁ h))

  ----------------------------------------------------------------------------------------
  -- ⊳pd-f: phil `i` (down1) puts down its FIRST fork `f i` (heldOwn/heldNbr → reloop).
  ----------------------------------------------------------------------------------------
  valid-step {f}{s} fs≢ V (⊳pd-f {cfgP}{cfgF}{i} pe) j
    with (f i) Fin.≟ j
  -- touched fork `j = f i` → reloop: i releases it (down1 → reloop), no other holder by V.
  ... | yes refl =
        (λ ownEq → case ownEq of λ ())
         , (λ nbrEq → case nbrEq of λ ())
         , holders
        where
          i-held-fi : heldBy {f}{s} cfgP i (f i)
          i-held-fi = heldBy-old-down1← {f}{s} cfgP i pe refl
          holders : ∀ k → heldBy {f}{s} (patch cfgP i reloop) k (f i)
                  → (k ≡ (f i) × reloop ≡ heldOwn)
                  ⊎ (k ≡ ((f i) ⊖1) × reloop ≡ heldNbr)
          holders k h with i Fin.≟ k
          -- k = i: `h` reduced (reloop) to `⊥`.
          ... | yes refl = ⊥-elim h
          -- k ≠ i: `h` reduced to `heldBy cfgP k (f i)`; both i and k hold `f i` old — mutex.
          ... | no  i≢k  =
                ⊥-elim (mutex-distinct cfgF (f i) (proj₂ (proj₂ (V (f i))) i i-held-fi)
                                                  (proj₂ (proj₂ (V (f i))) k h) i≢k)
  -- untouched fork `j ≢ f i`: i (down1) held only `f i ≠ j`, so it never held `j`.
  ... | no fi≢j =
        c1 , c2 , c3
        where
          c1 : cfgF j ≡ heldOwn → heldBy {f}{s} (patch cfgP i reloop) j j
          c1 ownEq with i Fin.≟ j
          ... | no  _    = proj₁ (V j) ownEq
          ... | yes refl = ⊥-elim (fi≢j (sym (heldBy-old-down1→ {f}{s} cfgP i pe (proj₁ (V j) ownEq))))
          c2 : cfgF j ≡ heldNbr → heldBy {f}{s} (patch cfgP i reloop) (j ⊖1) j
          c2 nbrEq with i Fin.≟ (j ⊖1)
          ... | no  _    = proj₁ (proj₂ (V j)) nbrEq
          ... | yes refl = ⊥-elim (fi≢j (sym (heldBy-old-down1→ {f}{s} cfgP i pe (proj₁ (proj₂ (V j)) nbrEq))))
          c3 : ∀ k → heldBy {f}{s} (patch cfgP i reloop) k j
             → (k ≡ j × cfgF j ≡ heldOwn) ⊎ (k ≡ (j ⊖1) × cfgF j ≡ heldNbr)
          c3 k h with i Fin.≟ k
          ... | no  _    = proj₂ (proj₂ (V j)) k h
          ... | yes refl = ⊥-elim h    -- `h` reduced to `⊥` (reloop holds nothing)

  -- The start-state characterisation, named (the anonymous `_` above proves the same).
  -- `philResid-start`/`forkResid-start` are private but in scope here (same module).
  sysState-start : ∀ {f s} → sysState f s ((λ _ → think) , (λ _ → free)) ≡ SYSTEM′ f s
  sysState-start = cong₂ (λ P Q → P ∥⇘ syncAll ¿ syncAll-dec ⇙ Q)
        (philResid-start allPhils) (forkResid-start allPhils)

  -------------------------------------------------------------------------------------
  -- 3e′-iii-b, Task 3: reachability of the validity invariant.
  --
  -- Every state reachable from `SYSTEM′` (via the big-step `═⟨_⟩═►`) is `sysState f s
  -- cfg′` for some VALID `cfg′`.  Induction on the big-step: `bNil` keeps the current
  -- config (and validity); a `bTau` is realised by `⊳-τ-sound` (preserving validity via
  -- `valid-τ`); a visible `bStep` by `⊳-ev-sound` (preserving via `valid-step`, which
  -- needs the fork-distinctness `fs≢`).  A `√`-terminating `bStep` is impossible: it
  -- forces `sysState f s cfg .force ≡ ret x`, but `sysState` is a synchronised parallel
  -- whose head residuals are non-empty interleavings, never ret-headed.
  -------------------------------------------------------------------------------------

  -- A system state is never ret-headed: its force is `force (philResid … ∥⇘ … ⇙ forkResid
  -- …)`, whose only ret-producing combo is `ret | ret`, but the head `philResid` over the
  -- non-empty `allPhils` is never ret-headed (`philResid-not-ret` via `allPhils-cons`).
  sysState-not-ret : ∀ {f s} (cfg : Config) {r}
    → (sysState f s cfg) .force ≢ ret r
  sysState-not-ret {f}{s} (cfgP , cfgF) eq with allPhils-cons
  ... | i₀ , rest , refl
        with philResid {f}{s} allPhils cfgP .force in p-eq | forkResid allPhils cfgF .force
  ...     | ret _      | ret _          = philResid-not-ret {f}{s} i₀ rest cfgP p-eq
  ...     | ret _      | sil _          = case eq of λ ()
  ...     | ret _      | vis _          = case eq of λ ()
  ...     | ret _      | ndbr _ _ _ _   = case eq of λ ()
  ...     | ret _      | mix _ _        = case eq of λ ()
  ...     | sil _      | _              = case eq of λ ()
  ...     | vis _      | ret _          = case eq of λ ()
  ...     | vis _      | sil _          = case eq of λ ()
  ...     | vis _      | vis _          = case eq of λ ()
  ...     | vis _      | ndbr _ _ _ _   = case eq of λ ()
  ...     | vis _      | mix _ _        = case eq of λ ()
  ...     | ndbr _ _ _ _ | ret _        = case eq of λ ()
  ...     | ndbr _ _ _ _ | sil _        = case eq of λ ()
  ...     | ndbr _ _ _ _ | vis _        = case eq of λ ()
  ...     | ndbr _ _ _ _ | ndbr _ _ _ _ = case eq of λ ()
  ...     | ndbr _ _ _ _ | mix _ _      = case eq of λ ()
  ...     | mix _ _    | ret _          = case eq of λ ()
  ...     | mix _ _    | sil _          = case eq of λ ()
  ...     | mix _ _    | vis _          = case eq of λ ()
  ...     | mix _ _    | ndbr _ _ _ _   = case eq of λ ()
  ...     | mix _ _    | mix _ _        = case eq of λ ()

  reach-valid : ∀ {f s} → (∀ i → f i ≢ s i) → ∀ {cfg} → ValidCfg {f}{s} cfg → ∀ {tr t′}
    → sysState f s cfg ═⟨ tr ⟩═► t′
    → Σ[ cfg′ ∈ Config ] (t′ ≡ sysState f s cfg′ × ValidCfg {f}{s} cfg′)
  reach-valid fs≢ {cfg} V bNil = cfg , refl , V
  reach-valid fs≢ V (bTau st bs) with ⊳-τ-sound st
  ... | cfg₁ , refl , ⊳w = reach-valid fs≢ (valid-τ V ⊳w) bs
  reach-valid fs≢ {cfg} V (bStep {el = evl e} st bs) with ⊳-ev-sound st
  ... | cfg₁ , refl , ⊳w = reach-valid fs≢ (valid-step fs≢ V ⊳w) bs
  reach-valid fs≢ {cfg} V (bStep {el = √ x} st bs) =
    ⊥-elim (sysState-not-ret cfg (proj₁ (√-is-ret st)))

  SYSTEM′-valid : ∀ {f s} → (∀ i → f i ≢ s i) → ∀ {tr t′} → SYSTEM′ f s ═⟨ tr ⟩═► t′
    → Σ[ cfg ∈ Config ] (t′ ≡ sysState f s cfg × ValidCfg {f}{s} cfg)
  SYSTEM′-valid {f}{s} fs≢ {tr}{t′} bs =
    reach-valid fs≢ (valid-init {f}{s})
      (subst (λ P → P ═⟨ tr ⟩═► t′) (sym sysState-start) bs)

-------------------------------------------------------------------------------------
-- m = 0 (n = 2) sanity check.
--
-- Cheap elaboration checks at the smallest instance (`open SysSt 0`, so `n = 2`,
-- `Phil = Fork = Fin 2`).  On the empty trace `[] = map evl []`, `bNil` fits the
-- `map evl s′` shape with `s′ = []`, and the n-ary state-closure corollaries
-- `PHILS-states`/`FORKS-states` return the start configuration (a `Σ` of a position
-- map and a residual-equality witness).  The empty-trace residual is the start
-- interleaving `philResid allPhils (λ _ → think)` (resp. `forkResid allPhils (λ _ →
-- free)`), built by the `[]`-base of `⦀list-reach-*` patched through the `allPhils`
-- cons fold.  We confirm the corollaries ELABORATE on `bNil`.
-------------------------------------------------------------------------------------

module Sanity where
  open M.Sys 0   -- symFirst / symSecond / Phil / Fork / allPhils at n = 2
  open St.St 0   -- PhilPos / ForkPos at n = 2
  open SysSt 0   -- PHILS-states / FORKS-states / philResid / forkResid

  -- The all-philosophers closure corollary elaborates on the empty (`bNil`) trace.
  _ : Σ[ cfg ∈ (Phil → PhilPos) ] _
  _ = PHILS-states {symFirst} {symSecond} {s′ = []} bNil

  -- The all-forks closure corollary elaborates on the empty (`bNil`) trace.
  _ : Σ[ cfg ∈ (Fork → ForkPos) ] _
  _ = FORKS-states {s′ = []} bNil

  -- The headline system state-closure elaborates on the empty (`bNil`) trace, computing a
  -- `Config` for the start state `SYSTEM′ symFirst symSecond`.
  _ : Σ[ cfg ∈ Config ] _
  _ = SYSTEM′-states {symFirst} {symSecond} bNil

  -- The config-step soundness lemmas elaborate at the smallest instance: any visible step
  -- of `sysState` realises a `⊳⟨_⟩` config-step, and any τ a `⊳τ` one.  We bind them to
  -- check the full signatures type-check at `m = 0` (no concrete composite step needed).
  ev-sound-check : ∀ {cfg : Config} {e t′}
    → sysState symFirst symSecond cfg ─[ ev (evl e) ]─► t′
    → Σ[ cfg′ ∈ Config ] (t′ ≡ sysState symFirst symSecond cfg′
        × (_⊳⟨_⟩_ {symFirst}{symSecond} cfg e cfg′))
  ev-sound-check = ⊳-ev-sound {symFirst} {symSecond}

  τ-sound-check : ∀ {cfg : Config} {t′}
    → sysState symFirst symSecond cfg ─[ τ ]─► t′
    → Σ[ cfg′ ∈ Config ] (t′ ≡ sysState symFirst symSecond cfg′ × cfg ⊳τ cfg′)
  τ-sound-check = ⊳-τ-sound {symFirst} {symSecond}

  -- The fork-distinctness witness `valid-step`/`reach-valid` require for the symmetric
  -- model: `symFirst i = i` and `symSecond i = i ⊕1`, and at `n = 2` (`Fin 2`) the two
  -- inhabitants `fzero`/`fsuc fzero` each compute a distinct `⊕1` (`fzero ⊕1 = fsuc fzero`,
  -- `fsuc fzero ⊕1 = fzero`), so `i ≢ i ⊕1` by case-analysis (both clashes are absurd).
  sym-fs≢ : ∀ i → symFirst i ≢ symSecond i
  sym-fs≢ Fin.zero            ()
  sym-fs≢ (Fin.suc Fin.zero)  ()

  -- The reachability-of-validity theorem elaborates at the smallest instance on the empty
  -- (`bNil`) trace, computing a VALID start `Config` for `SYSTEM′ symFirst symSecond`.
  _ : Σ[ cfg ∈ Config ] _
  _ = SYSTEM′-valid {symFirst} {symSecond} sym-fs≢ bNil

{-# OPTIONS --guardedness #-}

-- Part A — trace decomposition for the SYSTEM'-style dining philosophers model.
--
-- Thin wrappers over the proven `Parallel-trace` / `Interleave-trace` laws:
--   • SYSTEM′-trace : a trace of SYSTEM′ splits into a binary `SyncSplit`
--       of PHILS against FORKS at the synchronisation set `syncAll`.
--   • ⦀list-trace  : a trace of the replicated interleave `⦀list (p ∷ ps)`
--       splits, at the head layer, into a binary `InterleaveSplit` of the
--       head `p` against the tail-composite `⦀list ps`.
-- This mirrors `CSP.Laws.AlphaParallelList` (`∥list-trace` / `ListSyncSplit`)
-- but for the unalphabetised interleave `_⦀_`.

module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Traces where

open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Interaction_Trees
open ITree
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open Traces using (traces)
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP as M

module Tr (m : ℕ) where
  open M.Sys m
  import CSP.Definitions.Parallel {E = DP} as ParD
  open ParD DP-AnyTypes-≟
  import CSP.Laws.Parallel {E = DP} as ParL
  open ParL DP-AnyTypes-≟

  ---------------------------------------------------------------------------
  -- SYSTEM′-trace : SYSTEM′ first second ≡ PHILS first second ∥⇘ syncAll … ⇙ FORKS
  -- (definitionally), so `Parallel-trace` applies directly.

  SYSTEM′-trace : ∀ {first second} {s : List (Event√ DP (IProd (map (PHIL first second) allPhils)
                                                            × IProd (map FORK allPhils)))}
    → traces (SYSTEM′ first second) s
    → SyncSplit syncAll (PHILS first second) FORKS s
  SYSTEM′-trace {first} {second} =
    Parallel-trace (PHILS first second) FORKS syncAll syncAll-dec

  ---------------------------------------------------------------------------
  -- ⦀list-trace : decompose a trace of the replicated interleave.
  --
  -- DP : Set lzero → Set lzero, so all the level indices of the binary
  -- `InterleaveSplit` are concrete (lsuc lzero).

  data ListInterleaveSplit
    : (ps : List (ITree DP (ExtI DP) ⊥)) → List (Event√ DP (IProd ps)) → Set (lsuc lzero) where
    nil-split  : ∀ {s} → traces (⦀list []) s → ListInterleaveSplit [] s
    cons-split : ∀ {p ps s} → InterleaveSplit p (⦀list ps) s → ListInterleaveSplit (p ∷ ps) s

  ⦀list-trace : (ps : List (ITree DP (ExtI DP) ⊥)) {s : List (Event√ DP (IProd ps))}
              → traces (⦀list ps) s → ListInterleaveSplit ps s
  ⦀list-trace []       tr = nil-split tr
  ⦀list-trace (p ∷ ps) tr = cons-split (Interleave-trace p (⦀list ps) tr)

  ---------------------------------------------------------------------------
  -- Part B — liveness witness: a concrete reachable trace in which philosopher
  -- 0 acquires BOTH forks (its first pick `picks 0 0` then its second pick
  -- `picks 0 (0⊕1)`).  We reuse the 3c′ deadlock-proof step machinery (the
  -- per-component force/offer/refuse facts, the `⦀list`/`⦀` solo-step lemmas,
  -- the τ-free big-step `_⟹⟨_⟩_`, `lift-⦀R`, `combine-sync`, `⟹→═`, and the
  -- full-sync wrapper `∥⇘-sync-step′`).

  import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Deadlock as D
  open D.Pf m

  -- Bring the operator / iterate definitions into scope (⟶₀, >>=, loop0, …) so
  -- the new lemmas can talk about `loop0-body-tail`, `Prefix-cont`, etc.
  import CSP.Definitions.Operators {E = DP} as OpsD
  open OpsD DP-AnyTypes-≟
  import CSP.Definitions.Iterate {E = DP} as IterD
  open IterD DP-AnyTypes-≟
  import CSP.Laws.Bind {E = DP} as BindL
  open BindL DP-AnyTypes-≟ using (bind-force-vis)
  import CSP.Laws.Iterate {E = DP} as IterL
  open IterL DP-AnyTypes-≟ using (iter-bind-force-vis; iter-bind-cont-vis-just)

  open import Data.Empty using (⊥-elim)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans; cong)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Product using (proj₁)
  import Data.Fin as Fin
  open import Data.Fin using (Fin)
  open import Data.Fin.Properties using (suc-injective)
  import Data.Nat as Nat
  open import Data.Vec using (Vec; tabulate; toList)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Function using (case_of_)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)

  ---------------------------------------------------------------------------
  -- Step 1 — `loop0-tail-step`: fire the head event from a `loop0` RESIDUAL
  -- whose body offer is a prefix `ch ⟶₀ rest`.  Near-copy of 3c′'s
  -- `loop0-prefix-step`, but the SOURCE is already an `iter-bind` (a residual),
  -- whose iter loop-step is `loopStep0 body` (rather than the body's `loopStep`).
  loop0-tail-step :
    ∀ {A} (body : ITree DP (ExtI DP) (⊤ {lzero})) (ch : DP A) (a : A)
      (rest : ITree DP (ExtI DP) (⊤ {lzero}))
    → loop0-body-tail body (ch ⟶₀ rest)
        ─[ ev (evl (evLabel A ch a)) ]─►
      loop0-body-tail body rest
  loop0-tail-step {A} body ch a rest =
    sVis {at = A , ch} {a = a}
      (iter-bind-force-vis ((ch ⟶₀ rest) >>= loop-k) (loopStep0 body)
        (bind-force-vis (ch ⟶₀ rest) loop-k refl))
      (iter-bind-cont-vis-just (loopStep0 body)
        (bind-cont-vis loop-k (Prefix-cont ch (λ _ → rest))) (A , ch) a
        (bind-cont-vis-just loop-k (Prefix-cont ch (λ _ → rest)) (A , ch) a
          (Prefix-cont-just ch (λ _ → rest) a)))

  ---------------------------------------------------------------------------
  -- Local force-helper (`f⦀vv` is `private` in `D.Pf`, so we re-derive a thin
  -- copy): a vis|vis interleave composite is itself vis-headed.
  f⦀vv-loc : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
      {P : ITree DP (ExtI DP) R} {Q : ITree DP (ExtI DP) S} {fP fQ}
    → P .force ≡ vis fP → Q .force ≡ vis fQ
    → Σ[ f ∈ _ ] ((P ⦀ Q) .force ≡ vis f)
  f⦀vv-loc eqP eqQ rewrite eqP | eqQ = _ , refl

  ---------------------------------------------------------------------------
  -- Step 2 — the per-component fire steps for the two events of philosopher 0.
  --
  -- We work over the canonical decomposition of `allPhils`:
  --   allPhils = 0 ∷ (0⊕1) ∷ rest    (0⊕1 = fsuc fzero, definitionally)
  -- where `rest = toList (tabulate (λ i → fsuc (fsuc i)))` (all indices ≥ 2).

  z0 : Fin n
  z0 = Fin.zero

  s1 : Fin n
  s1 = Fin.suc Fin.zero      -- = z0 ⊕1, definitionally

  rest2L : List (Fin n)
  rest2L = toList (tabulate (λ (i : Fin m) → Fin.suc (Fin.suc i)))

  -- `0⊕1` is genuinely distinct from `0` (predecessor has no fixed point), and
  -- every index in `rest2L` is ≥ 2, hence ≢ 0 and ≢ (0⊕1).
  open import Data.Nat.Properties using (1+n≢n)

  0≢0⊕1 : z0 ≢ s1
  0≢0⊕1 ()

  -- The two-event trace philosopher 0 walks: pick own fork, then pick neighbour.
  eatTrace : List (Event DP)
  eatTrace = evLabel (⊤ {lzero}) (picks z0 z0)      tt
           ∷ evLabel (⊤ {lzero}) (picks z0 (z0 ⊕1)) tt
           ∷ []

  ---------------------------------------------------------------------------
  -- (A) PHILOSOPHER block.
  --
  -- Philosopher 0 (head of `allPhils`) fires BOTH events:
  --   • `picks 0 0`       via `loop0-body-step` on `Pbody 0` (first pick), then
  --   • `picks 0 (0⊕1)`   via `loop0-tail-step` from the residual `philRes 0`
  --     (whose body offer is `Prest 0 = picks 0 (0⊕1) ⟶₀ rest2`).
  -- All tail philosophers refuse both events (they offer only `picks k k`).

  -- `rest2` after philosopher 0's second pick.
  P0rest2 : ITree DP (ExtI DP) (⊤ {lzero})
  P0rest2 = putsdown z0 (z0 ⊕1) ⟶₀ putsdown z0 z0 ⟶₀ Skip

  phil0-eat : loop0 (Pbody z0) ⟹⟨ eatTrace ⟩ loop0-body-tail (Pbody z0) P0rest2
  phil0-eat =
    ⟹cons (PHIL-force z0) (PHIL-fires z0)
      (⟹cons (philRes-force z0)
        (loop0-offer-just (Pbody z0)
          (Prefix-cont (picks z0 (z0 ⊕1)) (λ _ → P0rest2))
          (prefix-picks-offer z0 (z0 ⊕1) (λ _ → P0rest2)))
        ⟹nil)

  -- An unadvanced philosopher `k ≢ 0` refuses `picks 0 0` (its own event is
  -- `picks k k`, which differs at the FIRST index).
  PHIL-refuses-00 : ∀ k → k ≢ z0
    → RefusesAt (loop0-fb (Pbody k) (Prefix-cont (picks k k) (λ _ → Prest k)))
                (evLabel (⊤ {lzero}) (picks z0 z0) tt)
  PHIL-refuses-00 k k≢0 = PHIL-refuses k z0 k≢0

  -- An unadvanced philosopher `k` refuses `picks 0 (0⊕1)` (its own event is
  -- `picks k k`, whose SECOND index is `k`; but `0⊕1 ≢ k` unless `k ≡ 0⊕1`, and
  -- even then the FIRST index `k ≢ 0`).  We refuse on the index mismatch.
  PHIL-refuses-0s : ∀ k → k ≢ z0
    → RefusesAt (loop0-fb (Pbody k) (Prefix-cont (picks k k) (λ _ → Prest k)))
                (evLabel (⊤ {lzero}) (picks z0 (z0 ⊕1)) tt)
  PHIL-refuses-0s k k≢0 =
    loop0-offer-nothing (Pbody k) (Prefix-cont (picks k k) (λ _ → Prest k))
      (prefix-picks-refuse k k z0 (z0 ⊕1) (λ _ → Prest k)
        (λ { (e , _) → k≢0 e }))

  ---------------------------------------------------------------------------
  -- A generic "advance the head through a STATIONARY ⦀list-tail that refuses
  -- every event of the trace" lemma.  The tail composite is either ret-headed
  -- (empty list → `Skip`) or vis-headed and refuses every event; in either case
  -- the head fires solo (`⦀-step-L-ret` / `⦀-step-L`).
  --
  -- We carry the per-event `AllRefuse`s of the tail-LIST (one `AllRefuse ps e`
  -- per event `e`), and discharge the composite's refusal via `⦀list-refuse`.

  -- All the tail components refuse a given event.
  TailRefuses : List (ITree DP (ExtI DP) ⊥) → Event DP → Set (lsuc lzero)
  TailRefuses ps (evLabel A e a) = AllRefuse ps (A , e) a

  lift-headL :
    ∀ (ps : List (ITree DP (ExtI DP) ⊥)) {p p′ : ITree DP (ExtI DP) ⊥} {els}
    → All (TailRefuses ps) els
    → p ⟹⟨ els ⟩ p′
    → (p ⦀ ⦀list ps) ⟹⟨ els ⟩ (p′ ⦀ ⦀list ps)
  lift-headL ps _ ⟹nil = ⟹nil
  lift-headL ps (tr ∷ trs) (⟹cons {A = A} {e = e} {a = a} eqp bp rest)
    with ⦀list-refuse ps {at = A , e} {a = a} tr
  ... | inj₁ (_ , retEq)
        with ⦀-step-L-ret {at = A , e} {a = a} eqp bp retEq
  ...     | sVis eqf bf   = ⟹cons eqf bf (lift-headL ps trs rest)
  ...     | sMixVis eqm _ = ⊥-elim (vis≢mix (trans (sym (proj₂ (f⦀vv-loc-r eqp retEq))) eqm))
        where
          f⦀vv-loc-r : ∀ {ℓs} {S : Set ℓs} {q : ITree DP (ExtI DP) ⊥}
                         {Q : ITree DP (ExtI DP) S} {fq} {s}
                     → q .force ≡ vis fq → Q .force ≡ ret s
                     → Σ[ f ∈ _ ] ((q ⦀ Q) .force ≡ vis f)
          f⦀vv-loc-r eqq eqQ rewrite eqq | eqQ = _ , refl
  lift-headL ps (tr ∷ trs) (⟹cons {A = A} {e = e} {a = a} eqp bp rest)
    | inj₂ (g , eqg , bg)
        with ⦀-step-L {at = A , e} {a = a} eqp bp eqg bg
  ...     | sVis eqf bf   = ⟹cons eqf bf (lift-headL ps trs rest)
  ...     | sMixVis eqm _ = ⊥-elim (vis≢mix (trans (sym (proj₂ (f⦀vv-loc eqp eqg))) eqm))

  -- The tail philosophers (all ≢ 0) refuse `picks 0 0`.
  phils-tail-refuse-00 :
    ∀ (rest : List Phil) → All (λ k → k ≢ z0) rest
    → AllRefuse (map (λ k → loop0 (Pbody k)) rest) (pAt z0 z0) tt
  phils-tail-refuse-00 []         _           = []
  phils-tail-refuse-00 (k ∷ rest) (k≢0 ∷ frs) =
    (_ , PHIL-force k , PHIL-refuses-00 k k≢0) ∷ phils-tail-refuse-00 rest frs

  -- The tail philosophers (all ≢ 0) refuse `picks 0 (0⊕1)`.
  phils-tail-refuse-0s :
    ∀ (rest : List Phil) → All (λ k → k ≢ z0) rest
    → AllRefuse (map (λ k → loop0 (Pbody k)) rest) (pAt z0 (z0 ⊕1)) tt
  phils-tail-refuse-0s []         _           = []
  phils-tail-refuse-0s (k ∷ rest) (k≢0 ∷ frs) =
    (_ , PHIL-force k , PHIL-refuses-0s k k≢0) ∷ phils-tail-refuse-0s rest frs

  -- The PHILS block walks `eatTrace`: philosopher 0 (head) eats both forks, the
  -- whole tail composite stationary (refusing both events).
  PHILS-eat :
    ∀ (rest : List Phil) → All (λ k → k ≢ z0) rest
    → ⦀list (map (λ k → loop0 (Pbody k)) (z0 ∷ rest))
        ⟹⟨ eatTrace ⟩
      (loop0-body-tail (Pbody z0) P0rest2 ⦀ ⦀list (map (λ k → loop0 (Pbody k)) rest))
  PHILS-eat rest frs =
    lift-headL (map (λ k → loop0 (Pbody k)) rest)
      (phils-tail-refuse-00 rest frs ∷ phils-tail-refuse-0s rest frs ∷ [])
      phil0-eat

  ---------------------------------------------------------------------------
  -- (B) FORK block.
  --
  -- Two DIFFERENT forks fire (at two different positions):
  --   • event 1 `picks 0 0`      : fork 0 fires its OWN branch (`FORK-fires 0`);
  --   • event 2 `picks 0 (0⊕1)`  : fork (0⊕1) fires its NEIGHBOUR branch
  --       `picks ((0⊕1)⊖1) (0⊕1) = picks 0 (0⊕1)` (since `(0⊕1)⊖1 ≡ 0`).
  -- After event 1, fork 0 is advanced (`forkRes 0`) and refuses `picks _ _`.

  -- `□`'s merged offer when the RIGHT branch offers and the LEFT refuses.
  □-offer-R :
    ∀ (at : AnyTypes DP)
      (fP fQ : (at′ : AnyTypes DP) → ContinueType at′ (Maybe (ITree DP (ExtI DP) (⊤ {lzero}))))
      (a : proj₁ at) {q}
    → fP at a ≡ nothing → fQ at a ≡ just q
    → (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just q
  □-offer-R at fP fQ a eP eQ rewrite eP | eQ = refl

  -- The neighbour residual of fork (0⊕1) after firing `picks 0 (0⊕1)`.
  F-nbr-res : ITree DP (ExtI DP) ⊥
  F-nbr-res = loop0-body-tail (Fbody (z0 ⊕1)) (putsdown ((z0 ⊕1) ⊖1) (z0 ⊕1) ⟶₀ Skip)

  -- Fork (0⊕1) fires `picks 0 (0⊕1)` via its NEIGHBOUR branch.
  FORK-fires-nbr :
    loop0-fb (Fbody (z0 ⊕1)) (FORK-fb (z0 ⊕1)) (pAt z0 (z0 ⊕1)) tt
      ≡ just F-nbr-res
  FORK-fires-nbr =
    loop0-offer-just {at = pAt z0 (z0 ⊕1)} {a = tt} (Fbody (z0 ⊕1)) (FORK-fb (z0 ⊕1))
      (□-offer-R (pAt z0 (z0 ⊕1))
                 (Prefix-cont (picks (z0 ⊕1) (z0 ⊕1))
                   (λ _ → putsdown (z0 ⊕1) (z0 ⊕1) ⟶₀ Skip))
                 (Prefix-cont (picks ((z0 ⊕1) ⊖1) (z0 ⊕1))
                   (λ _ → putsdown ((z0 ⊕1) ⊖1) (z0 ⊕1) ⟶₀ Skip))
                 tt
                 -- own branch `picks (0⊕1) (0⊕1)` refuses `picks 0 (0⊕1)`
                 -- (first index `0⊕1 ≢ 0`).
                 (prefix-picks-refuse (z0 ⊕1) (z0 ⊕1) z0 (z0 ⊕1)
                   (λ _ → putsdown (z0 ⊕1) (z0 ⊕1) ⟶₀ Skip)
                   (λ { (e , _) → 0≢0⊕1 (sym e) }))
                 -- neighbour branch `picks ((0⊕1)⊖1) (0⊕1)` = `picks 0 (0⊕1)` offers.
                 (prefix-picks-offer ((z0 ⊕1) ⊖1) (z0 ⊕1)
                   (λ _ → putsdown ((z0 ⊕1) ⊖1) (z0 ⊕1) ⟶₀ Skip)))

  -- An unadvanced fork `j` refuses `picks 0 0` when `j ≢ 0` (both its branches
  -- carry fork-index `j` in the SECOND coordinate; `0 ≢ j`).
  FORK-refuses-00 : ∀ j → j ≢ z0
    → RefusesAt (loop0-fb (Fbody j) (FORK-fb j))
                (evLabel (⊤ {lzero}) (picks z0 z0) tt)
  FORK-refuses-00 j j≢0 = FORK-refuses j z0 j≢0

  -- An unadvanced fork `j` refuses `picks 0 (0⊕1)` when `j ≢ 0⊕1` (both its
  -- branches carry fork-index `j` in the SECOND coordinate; `0⊕1 ≢ j`).
  FORK-refuses-0s : ∀ j → j ≢ (z0 ⊕1)
    → RefusesAt (loop0-fb (Fbody j) (FORK-fb j))
                (evLabel (⊤ {lzero}) (picks z0 (z0 ⊕1)) tt)
  FORK-refuses-0s j j≢s =
    loop0-offer-nothing (Fbody j) (FORK-fb j)
      (□-offer-refuse
        (Prefix-cont (picks j j)      (λ _ → putsdown j j      ⟶₀ Skip))
        (Prefix-cont (picks (j ⊖1) j) (λ _ → putsdown (j ⊖1) j ⟶₀ Skip))
        tt
        (prefix-picks-refuse j j z0 (z0 ⊕1) (λ _ → putsdown j j ⟶₀ Skip)
          (λ { (_ , e) → j≢s e }))
        (prefix-picks-refuse (j ⊖1) j z0 (z0 ⊕1) (λ _ → putsdown (j ⊖1) j ⟶₀ Skip)
          (λ { (_ , e) → j≢s e })))

  -- The `rest2L` forks (all indices ≥ 2) refuse `picks 0 0` …
  forks-rest-refuse-00 :
    ∀ (rest : List Fork) → All (λ j → j ≢ z0) rest
    → AllRefuse (map (λ j → loop0 (Fbody j)) rest) (pAt z0 z0) tt
  forks-rest-refuse-00 []         _           = []
  forks-rest-refuse-00 (j ∷ rest) (j≢0 ∷ frs) =
    (_ , FORK-force j , FORK-refuses-00 j j≢0) ∷ forks-rest-refuse-00 rest frs

  -- … and `picks 0 (0⊕1)`.
  forks-rest-refuse-0s :
    ∀ (rest : List Fork) → All (λ j → j ≢ (z0 ⊕1)) rest
    → AllRefuse (map (λ j → loop0 (Fbody j)) rest) (pAt z0 (z0 ⊕1)) tt
  forks-rest-refuse-0s []         _           = []
  forks-rest-refuse-0s (j ∷ rest) (j≢s ∷ frs) =
    (_ , FORK-force j , FORK-refuses-0s j j≢s) ∷ forks-rest-refuse-0s rest frs

  -- Local force-helper: vis|vis interleave is vis-headed, and the level-1
  -- composite `R1 = FORK (0⊕1) ⦀ TAILF` is vis-headed.
  R1-vis :
    ∀ (rest : List Fork)
    → Σ[ f ∈ _ ] ((loop0 (Fbody (z0 ⊕1)) ⦀ ⦀list (map (λ j → loop0 (Fbody j)) rest)) .force ≡ vis f)
  R1-vis rest = ⦀list-vis (loop0 (Fbody (z0 ⊕1))) (map (λ j → loop0 (Fbody j)) rest)
                  (visAllF (z0 ⊕1) rest)
    where
      VisH : ITree DP (ExtI DP) ⊥ → Set (lsuc lzero)
      VisH q = Σ[ f ∈ ((at : AnyTypes DP) → ContinueType at (Maybe (ITree DP (ExtI DP) ⊥))) ]
                 q .force ≡ vis f
      visAllF : ∀ (h : Fork) (xs : List Fork)
              → All VisH (loop0 (Fbody h) ∷ map (λ j → loop0 (Fbody j)) xs)
      visAllF h []        = (_ , FORK-force h) ∷ []
      visAllF h (x ∷ xs)  = (_ , FORK-force h) ∷ visAllF x xs

  -- The FORKS block walks `eatTrace`.
  --   FORKS = FORK 0 ⦀ R1   (R1 = FORK (0⊕1) ⦀ TAILF)
  -- event 1: fork 0 fires (R1 stationary & refuses);
  -- event 2: forkRes 0 refuses ⇒ R1 advances; inside R1, fork (0⊕1) fires
  --          its neighbour branch (TAILF stationary & refuses).
  FORKS-eat :
    ∀ (rest : List Fork)
    → All (λ j → j ≢ z0) rest → All (λ j → j ≢ (z0 ⊕1)) rest
    → ⦀list (map (λ j → loop0 (Fbody j)) (z0 ∷ (z0 ⊕1) ∷ rest))
        ⟹⟨ eatTrace ⟩
      (forkRes z0 ⦀ (F-nbr-res ⦀ ⦀list (map (λ j → loop0 (Fbody j)) rest)))
  FORKS-eat rest r0 rs
    -- event 1: fork 0 fires own branch; partner R1 vis-headed & refuses picks 0 0.
    with R1-vis rest
       | ⦀list-refuse (map (λ j → loop0 (Fbody j)) ((z0 ⊕1) ∷ rest))
           {at = pAt z0 z0} {a = tt}
           ((_ , FORK-force (z0 ⊕1) , FORK-refuses-00 (z0 ⊕1) (λ e → 0≢0⊕1 (sym e)))
             ∷ forks-rest-refuse-00 rest r0)
  ... | _ , r1eq | inj₁ (_ , retEq) = case trans (sym r1eq) retEq of λ ()
  ... | _ , r1eq | inj₂ (g , eqg , bg)
        with ⦀-step-L {at = pAt z0 z0} {a = tt}
               (FORK-force z0) (FORK-fires z0) eqg bg
  ...     | sMixVis eqm _ = ⊥-elim (vis≢mix (trans (sym (proj₂ (f⦀vv-loc (FORK-force z0) eqg))) eqm))
  ...     | sVis eqf1 bf1 =
            ⟹cons eqf1 bf1
              -- event 2: forkRes 0 refuses picks 0 (0⊕1) ⇒ advance R1 (right).
              (advanceR1)
            where
              -- R1 fires picks 0 (0⊕1): fork (0⊕1) fires neighbour, TAILF stationary.
              R1-eat :
                (loop0 (Fbody (z0 ⊕1)) ⦀ ⦀list (map (λ j → loop0 (Fbody j)) rest))
                  ⟹⟨ evLabel (⊤ {lzero}) (picks z0 (z0 ⊕1)) tt ∷ [] ⟩
                (F-nbr-res ⦀ ⦀list (map (λ j → loop0 (Fbody j)) rest))
              R1-eat
                with ⦀list-refuse (map (λ j → loop0 (Fbody j)) rest)
                       {at = pAt z0 (z0 ⊕1)} {a = tt} (forks-rest-refuse-0s rest rs)
              ... | inj₁ (_ , retEqT)
                    with ⦀-step-L-ret {at = pAt z0 (z0 ⊕1)} {a = tt}
                           (FORK-force (z0 ⊕1)) FORK-fires-nbr retEqT
              ...     | sVis eqf bf   = ⟹cons eqf bf ⟹nil
              ...     | sMixVis eqm _ = ⊥-elim (vis≢mix (trans (sym (proj₂ (f⦀vr-loc (FORK-force (z0 ⊕1)) retEqT))) eqm))
                    where
                      f⦀vr-loc : ∀ {ℓs} {S : Set ℓs} {q : ITree DP (ExtI DP) ⊥}
                                   {Q : ITree DP (ExtI DP) S} {fq} {s}
                               → q .force ≡ vis fq → Q .force ≡ ret s
                               → Σ[ f ∈ _ ] ((q ⦀ Q) .force ≡ vis f)
                      f⦀vr-loc eqq eqQ rewrite eqq | eqQ = _ , refl
              R1-eat | inj₂ (gt , eqgt , bgt)
                    with ⦀-step-L {at = pAt z0 (z0 ⊕1)} {a = tt}
                           (FORK-force (z0 ⊕1)) FORK-fires-nbr eqgt bgt
              ...     | sVis eqf bf   = ⟹cons eqf bf ⟹nil
              ...     | sMixVis eqm _ = ⊥-elim (vis≢mix (trans (sym (proj₂ (f⦀vv-loc (FORK-force (z0 ⊕1)) eqgt))) eqm))

              -- lift R1's single-event run through the refusing left head forkRes 0.
              advanceR1 :
                (forkRes z0 ⦀ (loop0 (Fbody (z0 ⊕1)) ⦀ ⦀list (map (λ j → loop0 (Fbody j)) rest)))
                  ⟹⟨ evLabel (⊤ {lzero}) (picks z0 (z0 ⊕1)) tt ∷ [] ⟩
                (forkRes z0 ⦀ (F-nbr-res ⦀ ⦀list (map (λ j → loop0 (Fbody j)) rest)))
              advanceR1 with R1-eat
              ... | ⟹cons {fQ = fQ} eqQ bQ ⟹nil
                    with ⦀-step-R {at = pAt z0 (z0 ⊕1)} {a = tt}
                           (forkRes-force z0) (forkRes-refuses-pk z0 z0 (z0 ⊕1)) eqQ bQ
              ...     | sVis eqf bf   = ⟹cons eqf bf ⟹nil
              ...     | sMixVis eqm _ = ⊥-elim (vis≢mix (trans (sym (proj₂ (f⦀vv-loc (forkRes-force z0) eqQ))) eqm))

  ---------------------------------------------------------------------------
  -- (C) Freshness of `rest2L` (indices ≥ 2): every element differs from both 0
  -- and 0⊕1 (= fsuc fzero).

  rest2L-≢0 : All (λ k → k ≢ z0) rest2L
  rest2L-≢0 = go (λ (i : Fin m) → i)
    where
      go : ∀ {l} (g : Fin l → Fin m)
         → All (λ k → k ≢ z0) (toList (tabulate (λ i → Fin.suc (Fin.suc (g i)))))
      go {Nat.zero}  g = []
      go {Nat.suc l} g = (λ ()) ∷ go (λ i → g (Fin.suc i))

  rest2L-≢s : All (λ k → k ≢ (z0 ⊕1)) rest2L
  rest2L-≢s = go (λ (i : Fin m) → i)
    where
      go : ∀ {l} (g : Fin l → Fin m)
         → All (λ k → k ≢ (z0 ⊕1)) (toList (tabulate (λ i → Fin.suc (Fin.suc (g i)))))
      go {Nat.zero}  g = []
      go {Nat.suc l} g = (λ { eq → 0≢0⊕1-suc (suc-injective eq) }) ∷ go (λ i → g (Fin.suc i))
        where
          -- `fsuc (fsuc (g zero)) ≢ fsuc fzero`  reduces (after suc-inj) to
          -- `fsuc (g zero) ≢ fzero`, which is immediate.
          0≢0⊕1-suc : Fin.suc (g Fin.zero) ≢ Fin.zero
          0≢0⊕1-suc ()

  ---------------------------------------------------------------------------
  -- (D) Assemble the liveness witness.  `combine-sync` synchronises the PHILS
  -- and FORKS eat-runs over the SAME two-event trace into one SYSTEM′sym run;
  -- `⟹→═` embeds it as a genuine `═⟨ map evl eatTrace ⟩═►`.  `SYSTEM′sym` is
  -- definitionally `PHILS sym sym ∥⇘ syncAll ¿ syncAll-dec ⇙ FORKS`, and
  -- `allPhils = 0 ∷ (0⊕1) ∷ rest2L`, `PHIL sym sym k = loop0 (Pbody k)`,
  -- `FORK j = loop0 (Fbody j)`, all definitionally.

  eat-reachable′ :
    Σ[ t′ ∈ ITree DP (ExtI DP) _ ]
      (SYSTEM′sym ═⟨ map evl ( evLabel _ (picks Fin.zero Fin.zero)           tt
                             ∷ evLabel _ (picks Fin.zero (Fin.zero ⊕1))      tt ∷ [] ) ⟩═► t′)
  eat-reachable′ =
    _ ,
    ⟹→═ (combine-sync
            (PHILS-eat ((z0 ⊕1) ∷ rest2L) ((λ e → 0≢0⊕1 (sym e)) ∷ rest2L-≢0))
            (FORKS-eat rest2L rest2L-≢0 rest2L-≢s))

-- Sanity: the decomposition wrappers elaborate at a concrete instance (n = 2).
private
  module Sanity where
    open M.Sys 0
    open Tr 0
    import CSP.Laws.Parallel {E = DP} as ParL
    open ParL DP-AnyTypes-≟ using (SyncSplit)

    -- The empty-list interleave is a leaf: its trace is carried as-is.
    _ : ∀ {s} → traces (⦀list []) s → ListInterleaveSplit [] s
    _ = λ tr → ⦀list-trace [] tr

    -- A trace of SYSTEM′ symFirst symSecond splits into PHILS/FORKS.
    _ : ∀ {s} → traces (SYSTEM′ symFirst symSecond) s
        → SyncSplit syncAll (PHILS symFirst symSecond) FORKS s
    _ = SYSTEM′-trace {symFirst} {symSecond}

    -- The Part B liveness witness elaborates at n = 2: philosopher 0 acquires
    -- BOTH forks via `picks 0 0` then `picks 0 (0⊕1)`.
    _ = eat-reachable′

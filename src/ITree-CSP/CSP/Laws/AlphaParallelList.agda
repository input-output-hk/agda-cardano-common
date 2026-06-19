{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Process_Trees
open import Semantics.LTS
open import Semantics.Failures using (_⟹⟨_⟩_; ⟹-refl; traces)
open import Semantics.Deadlock
open import Semantics.Refusals using ()  -- imported for the dependency flow; its `Refuses`
                                          -- (an event-SET refusal) is NOT the per-event
                                          -- predicate this module defines, so nothing is
                                          -- brought into scope to avoid the name clash.

module CSP.Laws.AlphaParallelList
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open PTree

import CSP.Operators {ℓ} {ℓe} {E} E-≟ as CSPOps
open CSPOps using
  ( EventSet
  ; Comp; comp; unionα; RetOf⁺; ∥ₐ⁺; ∥ₐ⁺-unfold
  ; _⟦_∥_⟧_; αpar; αpar-pTau; αpar-hTauL
  )
open EventSet
open Comp

import CSP.Laws.AlphaParallel {ℓ} {ℓe} {E} as CSPAParLaws
open CSPAParLaws E-≟ using
  ( αpar-IsStuck; Blocked
  ; AlphaSync; AlphaSyncSplit; AlphaParallel-trace; αpar-trace-intro
  ; VisDriven )

-------------------------------------------------------------------------------------
-- A tree is react-headed-and-stable ("VisHead", the react analogue of the legacy
-- `vis`-headed predicate).
--
-- The legacy hypothesis was `Σ f. force ≡ vis f`, where a `vis` node carries no τ.
-- Under the fused `react` node a node CAN offer τ even while react-headed, but the
-- binary `αpar-IsStuck` now needs each operand to be STABLE (its τ-map everywhere
-- `nothing`).  So `VisHead` bundles the react-force equality TOGETHER with stability
-- of the τ-map — exactly what `∥ₐ⁺-IsStuck` must feed to `αpar-IsStuck`.

VisHead : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        → PTree E (ExtI I) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
VisHead {I = I} {R = R} t =
  Σ[ v  ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))) ]
  Σ[ τc ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))) ]
    ((t .force ≡ react v τc) × (∀ i a → τc i a ≡ nothing))

-- The non-empty fold `∥ₐ⁺ c xs` of react-headed-and-stable components is itself
-- react-headed-and-stable.
--
--   * singleton (xs ≡ []): `∥ₐ⁺ c [] = proc c` is the BARE head process — no αpar layer
--     — so its VisHead is exactly the head component's own VisHead hypothesis.
--   * cons (xs ≡ d ∷ ds): the tail-composite `∥ₐ⁺ d ds` is react-headed-and-stable (IH),
--     so the node-pair is `react|react`, force `react (αpar-pVis …) (αpar-pTau …)`.  The
--     composite τ-map (`αpar-pTau`) only forwards `τcc`/`τct`, both everywhere `nothing`.
∥ₐ⁺-headed : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (c : Comp I R) (xs : List (Comp I R))
  → All (λ d → VisHead (Comp.proc d)) (c ∷ xs)
  → VisHead (∥ₐ⁺ c xs)
∥ₐ⁺-headed c [] (hc ∷ _) = hc
∥ₐ⁺-headed c (d ∷ ds) ((vc , τcc , eqc , stc) ∷ tl)
  with ∥ₐ⁺-headed d ds tl
... | (vt , τct , eqt , stt) rewrite eqc | eqt =
    _ , _ , refl , st
  where
    -- composite τ-map (react|react) is `αpar-pTau`, forwarding only τcc / τct.
    st : ∀ i a → αpar-pTau (Comp.alpha c) (unionα (d ∷ ds)) _,_
                    τcc τct (Comp.proc c) (∥ₐ⁺ d ds) i a ≡ nothing
    st (_ , base _)            _ = refl
    st (_ , fin)               _ = refl
    st (_ , pair (base _) _)   _ = refl
    st (_ , pair (pair _ _) _) _ = refl
    st (_ , pair fin i) (lift fzero , a)               rewrite stc (_ , i) a = refl
    st (_ , pair fin i) (lift (fsuc fzero) , a)        rewrite stt (_ , i) a = refl
    st (_ , pair fin i) (lift (fsuc (fsuc _)) , a)     = refl

-------------------------------------------------------------------------------------
-- (a) Refusal and the network-blocked predicate.
--
-- `Refuses t at a`: whenever `t` is react-headed, its offer at the event (at , a) is
-- `nothing` — the tree declines to fire that event.
Refuses : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        → PTree E (ExtI I) R → (at : AnyTypes E) → proj₁ at → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Refuses {I = I} {R = R} t at a =
  ∀ (v : (at′ : AnyTypes E) → ContinueType at′ (Maybe (PTree E (ExtI I) R)))
    (τc : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R)))
  → t .force ≡ react v τc → v at a ≡ nothing

-- The event (at , a) is network-blocked along the non-empty fold `∥ₐ⁺ c xs`: at each
-- cons layer, whichever side(s) the routing requires must decline.  This is a *product
-- of implications*, one per binary routing the head layer can take (driven by
-- `(alpha c .dec at a , unionα xs .dec at a)`):
--
--   * sync field  — when the event is in BOTH the head alphabet and the tail union
--     (the `(yes , yes)` routing) the layer is discharged by EITHER the head refusing
--     it OR the tail-composite (`∥ₐ⁺ d ds`) refusing it.  This is the strengthening:
--     the refuser may live ANYWHERE in the tail, not just at the head.
--   * solo field  — when the event is in the head alphabet ONLY (the `(yes , no)`
--     routing) only the head can carry it, so the head must refuse.
--   * tail field  — `NetBlockedAt d ds at a`, supplying the recursion that the
--     `(no , yes)` tail-solo routing needs (via `∥ₐ⁺-refuses` on the tail).
--
-- The SINGLETON base `NetBlockedAt c [] = Refuses (proc c)`: `∥ₐ⁺ c [] = proc c`, so
-- the bare head must itself refuse.
--
-- This is GENUINELY weaker than the old conjunctive `(head-refuses) × tail` shape:
-- at a synchronised event the head is now allowed to OFFER it as long as the
-- tail-composite refuses — the `inj₂` disjunct of the sync field.
NetBlockedAt : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             → (c : Comp I R) → List (Comp I R) → (at : AnyTypes E) → proj₁ at
             → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
NetBlockedAt c []       at a = Refuses (Comp.proc c) at a
NetBlockedAt c (d ∷ ds) at a =
    (Comp.alpha c .mem at a → unionα (d ∷ ds) .mem at a
       → (Refuses (Comp.proc c) at a) ⊎ (Refuses (∥ₐ⁺ d ds) at a))
  × (Comp.alpha c .mem at a → ¬ unionα (d ∷ ds) .mem at a → Refuses (Comp.proc c) at a)
  × NetBlockedAt d ds at a

NetBlocked : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           → (c : Comp I R) → List (Comp I R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
NetBlocked c xs = ∀ (at : AnyTypes E) (a : proj₁ at) → NetBlockedAt c xs at a

-- The folded composite refuses every event that the network blocks (per point).
-- Threads an `All`-VisHead hypothesis so the merged offer's shape is known at each layer.
∥ₐ⁺-refuses : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              → (c : Comp I R) (xs : List (Comp I R))
              → All (λ d → VisHead (Comp.proc d)) (c ∷ xs)
              → (at : AnyTypes E) (a : proj₁ at)
              → NetBlockedAt c xs at a
              → Refuses (∥ₐ⁺ c xs) at a
-- singleton : ∥ₐ⁺ c [] = proc c, so the network-blocked datum IS the bare head's refusal.
∥ₐ⁺-refuses c [] _ at a hr = hr
-- cons (nonempty tail) : both head and folded tail are react-headed, so the composite is
-- the react|react merged offer.  Case on (alpha c .dec at a , unionα (d∷ds) .dec at a)
-- and discharge each routing with head refusal and/or the tail's induced refusal.
∥ₐ⁺-refuses c (d ∷ ds) ((vc , τcc , eqc , _) ∷ tl) at a (sync , hsolo , tblocks) v τc feq
  with ∥ₐ⁺-headed d ds tl
... | (vt , τct , eqt , _)
  with ∥ₐ⁺-refuses d ds tl at a tblocks vt τct eqt
...   | gr rewrite eqc | eqt with feq
...     | refl with Comp.alpha c .dec at a | unionα (d ∷ ds) .dec at a
...       | yes pc | yes pt with sync pc pt
...         | inj₁ hr rewrite hr vc τcc refl = refl
...         | inj₂ tr rewrite tr vt τct refl with vc at a
...           | just _  = refl
...           | nothing = refl
∥ₐ⁺-refuses c (d ∷ ds) ((vc , τcc , eqc , _) ∷ tl) at a (sync , hsolo , tblocks) v τc feq
  | (vt , τct , eqt , _) | gr | refl | yes pc | no ¬pt rewrite hsolo pc ¬pt vc τcc refl = refl
∥ₐ⁺-refuses c (d ∷ ds) ((vc , τcc , eqc , _) ∷ tl) at a (sync , hsolo , tblocks) v τc feq
  | (vt , τct , eqt , _) | gr | refl | no _   | yes pt rewrite gr = refl
∥ₐ⁺-refuses c (d ∷ ds) ((vc , τcc , eqc , _) ∷ tl) at a (sync , hsolo , tblocks) v τc feq
  | (vt , τct , eqt , _) | gr | refl | no _   | no _   = refl

-------------------------------------------------------------------------------------
-- (b) The n-ary refusal-composition law: a network-blocked fold is IsStuck.

-- For the singleton base `∥ₐ⁺ c [] = proc c`, IsStuck is exactly the head process being
-- stuck: react-headed (`VisHead`), stable (its τ-map everywhere `nothing`) and refusing
-- every event (the `NetBlocked` datum).  sRet/sSil are refuted by the react force,
-- sVis by the everywhere-`nothing` offer, sTau by head-stability.
∥ₐ⁺-IsStuck : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (c : Comp I R) (xs : List (Comp I R))
  → All (λ d → VisHead (Comp.proc d)) (c ∷ xs)
  → NetBlocked c xs
  → IsStuck (∥ₐ⁺ c xs)
-- singleton: enumerate steps on the bare head `proc c`.
∥ₐ⁺-IsStuck c [] ((vc , τcc , eqc , stc) ∷ _) nb (sRet eq) rewrite eqc = case eq of λ ()
∥ₐ⁺-IsStuck c [] ((vc , τcc , eqc , stc) ∷ _) nb (sSil eq) rewrite eqc = case eq of λ ()
∥ₐ⁺-IsStuck c [] ((vc , τcc , eqc , stc) ∷ _) nb (sVis {at = at} {a = a} feq branch-eq)
  with nb at a
... | hr rewrite eqc with feq
...   | refl rewrite hr vc τcc refl = case branch-eq of λ ()
∥ₐ⁺-IsStuck c [] ((vc , τcc , eqc , stc) ∷ _) nb (sTau {i = i} {a = a} feq branch-eq)
  rewrite eqc with feq
... | refl rewrite stc i a = case branch-eq of λ ()
-- cons (nonempty tail): both operands react-headed-and-stable, apply the binary law,
-- feeding the head's force/stability, the tail-composite's force/stability (from
-- `∥ₐ⁺-headed`), and the per-event `Blocked` proof (from `NetBlocked` via the 4-way
-- (alpha c .dec at a, unionα (d∷ds) .dec at a) routing).
∥ₐ⁺-IsStuck c (d ∷ ds) ((vc , τcc , eqc , stc) ∷ tl) nb
  with ∥ₐ⁺-headed d ds tl
... | (vt , τct , eqt , stt) =
    αpar-IsStuck eqc eqt stc stt blocked
  where
    blocked : ∀ (at : AnyTypes E) (a : proj₁ at)
            → Blocked (Comp.alpha c) (unionα (d ∷ ds)) vc vt at a
    blocked at a with nb at a
    ... | (sync , hsolo , tblocks)
        with Comp.alpha c .dec at a | unionα (d ∷ ds) .dec at a
    ...   | yes pc | yes pt with sync pc pt
    ...     | inj₁ hr = lift (inj₁ (hr vc τcc eqc))
    ...     | inj₂ tr = lift (inj₂ (tr vt τct eqt))
    blocked at a | (sync , hsolo , tblocks) | yes pc | no ¬pt =
      lift (hsolo pc ¬pt vc τcc eqc)
    blocked at a | (sync , hsolo , tblocks) | no _ | yes pt =
      lift (∥ₐ⁺-refuses d ds tl at a tblocks vt τct eqt)
    blocked at a | (sync , hsolo , tblocks) | no _ | no _ = tt

-------------------------------------------------------------------------------------
-- (c) Sanity: a network of `Stop` components is stuck, hence has a deadlock.

private
  module Sanity where
    open CSPOps using (Stop; chanSet)

    -- The everywhere-true event-set: every event is in scope (channel-level).
    All∈ : EventSet
    All∈ = chanSet (λ _ → ⊤ {lzero}) (λ _ → yes tt)

    -- A `Stop` component (instantiated at the operator's fixed `I = E`).
    stopC : ∀ {ℓr} {R : Set ℓr} → Comp E R
    stopC = comp All∈ Stop

    -- `Stop`'s force is `react ∅v ∅t` (both maps everywhere `nothing`): react-headed,
    -- stable, and refusing every event.
    stop-head : ∀ {ℓr} {R : Set ℓr} → VisHead (Stop {R = R})
    stop-head = _ , _ , refl , (λ _ _ → refl)

    stop-refuses : ∀ {ℓr} {R : Set ℓr}
                 → (at : AnyTypes E) (a : proj₁ at) → Refuses (Stop {R = R}) at a
    stop-refuses at a v τc refl = refl

    -- Two-component network of Stops, all react-headed-and-stable, blocked at every event.
    stops-vis : ∀ {ℓr} {R : Set ℓr}
              → All (λ d → VisHead (Comp.proc d)) (stopC {R = R} ∷ stopC ∷ [])
    stops-vis = stop-head ∷ stop-head ∷ []

    stops-blocked : ∀ {ℓr} {R : Set ℓr}
                  → NetBlocked (stopC {R = R}) (stopC ∷ [])
    stops-blocked at a =
        -- sync field (yes , yes): the head Stop refuses, so take the `inj₁` disjunct.
        (λ _ _ → inj₁ (stop-refuses at a))
        -- head-solo field (yes , ¬ tail): the head Stop refuses.
      , (λ _ _ → stop-refuses at a)
        -- tail field: the inner Stop layer (a singleton), refusing directly.
      , stop-refuses at a

    stops-stuck : ∀ {ℓr} {R : Set ℓr}
                → IsStuck (∥ₐ⁺ (stopC {R = R}) (stopC ∷ []))
    stops-stuck = ∥ₐ⁺-IsStuck stopC (stopC ∷ []) stops-vis stops-blocked

    stops-deadlock : ∀ {ℓr} {R : Set ℓr}
                   → HasDeadlock (∥ₐ⁺ (stopC {R = R}) (stopC ∷ []))
    stops-deadlock = [] , _ , ⟹-refl , stops-stuck

  -------------------------------------------------------------------------------------
  -- (c′) Sanity (the strengthening): a network whose HEAD OFFERS a shared sync event
  -- but whose TAIL refuses it is STILL stuck — certified through the `inj₂`
  -- (tail-refuser) disjunct of the strengthened `NetBlockedAt`.  The OLD conjunctive
  -- `NetBlockedAt` could NOT certify this: it demanded the head refuse at every event,
  -- yet here the head offers `at₀`.
  module TailRefuserSanity where
    open CSPOps using (Stop; chanSet)

    All∈ : EventSet
    All∈ = chanSet (λ _ → ⊤ {lzero}) (λ _ → yes tt)

    -- The unit process used as the head's continuation when it fires `at₀`.
    headSkip : ∀ {ℓr} → PTree E (ExtI E) (⊤ {ℓr})
    headSkip {ℓr} = CSPOps.Skip {ℓr = ℓr}

    -- The head's offer map: it OFFERS the chosen event `at₀` (returns `just headSkip`),
    -- and declines every other event.
    offerV : ∀ {ℓr} → (at₀ : AnyTypes E)
           → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) (⊤ {ℓr})))
    offerV {ℓr} at₀ at with E-≟ at at₀
    ... | yes _ = λ _ → just (headSkip {ℓr})
    ... | no  _ = λ _ → nothing

    -- The head process: a react node offering `at₀`, with no τ (stable).
    offerP : ∀ {ℓr} (at₀ : AnyTypes E) → PTree E (ExtI E) (⊤ {ℓr})
    force (offerP {ℓr} at₀) =
      react (offerV {ℓr} at₀)
            (λ (_ : AnyTypes (ExtI E)) _ → nothing {A = PTree E (ExtI E) (⊤ {ℓr})})

    offerC : ∀ {ℓr} → (at₀ : AnyTypes E) → Comp E (⊤ {ℓr})
    offerC at₀ = comp All∈ (offerP at₀)

    -- The head is react-headed and stable.
    offer-head : ∀ {ℓr} (at₀ : AnyTypes E) → VisHead (offerP {ℓr} at₀)
    offer-head at₀ = _ , _ , refl , (λ _ _ → refl)

    -- The head genuinely OFFERS `at₀` (it does NOT refuse it) — so the old head-only
    -- predicate is inapplicable at `at₀`.
    offer-offers : ∀ {ℓr} (at₀ : AnyTypes E) (a₀ : proj₁ at₀)
                 → offerV {ℓr} at₀ at₀ a₀ ≡ just (headSkip {ℓr})
    offer-offers at₀ a₀ with E-≟ at₀ at₀
    ... | yes _ = refl
    ... | no ¬p = case ¬p refl of λ ()

    stopC : ∀ {ℓr} → Comp E (⊤ {ℓr})
    stopC = comp All∈ Stop

    stop-head : ∀ {ℓr} → VisHead (Stop {R = ⊤ {ℓr}})
    stop-head = _ , _ , refl , (λ _ _ → refl)

    stop-refuses : ∀ {ℓr} (at : AnyTypes E) (a : proj₁ at) → Refuses (Stop {R = ⊤ {ℓr}}) at a
    stop-refuses at a v τc refl = refl

    -- The whole network is react-headed-and-stable.
    net-vis : ∀ {ℓr} (at₀ : AnyTypes E)
            → All (λ d → VisHead (Comp.proc d)) (offerC {ℓr} at₀ ∷ stopC ∷ [])
    net-vis at₀ = offer-head at₀ ∷ stop-head ∷ []

    -- The tail-composite `∥ₐ⁺ stopC []` (≡ `Stop`) refuses EVERY event.  Built via the
    -- strengthened `∥ₐ⁺-refuses` over the singleton tail.
    tail-blocked : ∀ {ℓr} (at : AnyTypes E) (a : proj₁ at)
                 → NetBlockedAt (stopC {ℓr}) [] at a
    tail-blocked at a = stop-refuses at a
    tail-refuses : ∀ {ℓr} (at : AnyTypes E) (a : proj₁ at)
                 → Refuses (∥ₐ⁺ (stopC {ℓr}) []) at a
    tail-refuses at a = ∥ₐ⁺-refuses stopC [] (stop-head ∷ []) at a (tail-blocked at a)

    -- The network is blocked at every event — discharged entirely through `inj₂`
    -- (the TAIL-composite refuses) even though the HEAD offers `at₀`.
    net-blocked : ∀ {ℓr} (at₀ : AnyTypes E) → NetBlocked (offerC {ℓr} at₀) (stopC ∷ [])
    net-blocked at₀ at a =
        -- sync field (yes , yes): the HEAD may offer `at` (e.g. at₀), so we take the
        -- `inj₂` disjunct — the TAIL-composite refuses it.  THIS is the new capability.
        (λ _ _ → inj₂ (tail-refuses at a))
        -- head-solo field (yes , ¬ tail): vacuous — the tail union is All∈ (inhabited),
        -- so `¬ unionα` is uninhabited.
      , (λ _ ¬u → case ¬u (inj₁ tt) of λ ())
        -- tail field: the inner Stop layer (a singleton), refusing directly.
      , tail-blocked at a

    net-stuck : ∀ {ℓr} (at₀ : AnyTypes E)
              → IsStuck (∥ₐ⁺ (offerC {ℓr} at₀) (stopC ∷ []))
    net-stuck at₀ = ∥ₐ⁺-IsStuck (offerC at₀) (stopC ∷ []) (net-vis at₀) (net-blocked at₀)

    net-deadlock : ∀ {ℓr} (at₀ : AnyTypes E)
                 → HasDeadlock (∥ₐ⁺ (offerC {ℓr} at₀) (stopC ∷ []))
    net-deadlock at₀ = [] , _ , ⟹-refl , net-stuck at₀

-------------------------------------------------------------------------------------
-- (d) n-ary trace-decomposition (elimination) law for the replicated parallel.
--
-- A trace of `∥ₐ⁺ c xs` splits, at the head layer, into a binary `AlphaSyncSplit` of
-- the head component (`Comp.proc c`) against the tail-composite (`∥ₐ⁺ d ds`).  The
-- singleton (xs ≡ []) is a leaf (`∥ₐ⁺ c [] = proc c`): there is nothing to split, so
-- the trace is carried as-is on the bare head.  The cons case carries the binary
-- head/tail split; the tail-composite's trace lives inside that `AlphaSyncSplit` and can
-- be recursively decomposed by applying `∥ₐ⁺-trace` to it for full flattening.
--
-- react port (T1–T5): `ITree`→`PTree`, `═⟨ ⟩═►`→`⟹⟨ ⟩` (the `traces` weak-reach);
-- the binary `AlphaParallel-trace` (already react-ported in `CSP.Laws.AlphaParallel`)
-- does all the node-shape work, so this n-ary wrapper is unchanged in structure.

data ListSyncSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  : (c : Comp I R) (xs : List (Comp I R))
  → List (Event√ {ℓ = ℓ} {ℓe = ℓe} {ℓi = lsuc ℓ ⊔ ℓi} {E = E} {I = ExtI I} (RetOf⁺ c xs))
  → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr) where
  nil-split  : ∀ {c s} → traces {E = E} {I = ExtI I} (∥ₐ⁺ {I = I} {R = R} c []) s
                       → ListSyncSplit c [] s
  cons-split : ∀ {c d ds s}
             → AlphaSyncSplit (Comp.alpha c) (unionα (d ∷ ds)) (Comp.proc c) (∥ₐ⁺ d ds) s
             → ListSyncSplit c (d ∷ ds) s

∥ₐ⁺-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (c : Comp I R) (xs : List (Comp I R))
    {s : List (Event√ {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I} (RetOf⁺ c xs))}
  → traces (∥ₐ⁺ c xs) s → ListSyncSplit c xs s
∥ₐ⁺-trace c []       tr = nil-split tr
∥ₐ⁺-trace c (d ∷ ds) tr =
  cons-split (AlphaParallel-trace (Comp.proc c) (∥ₐ⁺ d ds)
                                  (Comp.alpha c) (unionα (d ∷ ds)) tr)

-------------------------------------------------------------------------------------
-- (e) n-ary trace-introduction law for the replicated parallel.
--
-- The dual of `∥ₐ⁺-trace`: given a (vis-driven, head-stable) trace `bc` of the head
-- component and a trace `bxs` of the tail-composite that synchronise per `AlphaSync`,
-- the folded composite `∥ₐ⁺ c (d ∷ ds)` performs the merged trace `map evl s`.  Since
-- `∥ₐ⁺ c (d ∷ ds)` is *definitionally* the binary parallel of the head against the
-- tail-composite (`∥ₐ⁺-unfold`), this is exactly the binary introduction law
-- `αpar-trace-intro` instantiated at the head layer; the caller iterates it down the
-- list (supplying the tail's trace `bxs`, itself built by a recursive application).
--
-- react port: `VisDriven` + `isStable` endpoints replace the legacy bare vis-headed
-- hypotheses; the call is otherwise the verbatim binary `αpar-trace-intro`.

∥ₐ⁺-trace-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    (c : Comp I R) (d : Comp I R) (ds : List (Comp I R))
    {sc sxs s : List (Event {ℓi = lsuc ℓ ⊔ ℓi} {I = ExtI I})}
    {c′ : PTree E (ExtI I) R} {xs′ : PTree E (ExtI I) (RetOf⁺ d ds)}
    {bc : Comp.proc c ⟹⟨ map evl sc ⟩ c′}
    {bxs : ∥ₐ⁺ d ds ⟹⟨ map evl sxs ⟩ xs′}
  → AlphaSync (Comp.alpha c) (unionα (d ∷ ds)) sc sxs s
  → VisDriven bc → VisDriven bxs
  → isStable c′ → isStable xs′
  → (∥ₐ⁺ c (d ∷ ds)) ⟹⟨ map evl s ⟩
      (c′ ⟦ Comp.alpha c ∥ unionα (d ∷ ds) ⟧ xs′)
∥ₐ⁺-trace-intro c d ds {bc = bc} {bxs = bxs} asy vdc vdxs stc stxs =
  αpar-trace-intro asy bc vdc bxs vdxs stc stxs

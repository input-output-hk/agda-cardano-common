{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; _×_; Σ-syntax)
open import Data.Sum using (inj₁)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS

module CSP.Laws.AlphaParallelList
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Traces

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟
import CSP.Definitions.AlphaParallel {ℓ} {ℓe} {E} as CSPAPar
open CSPAPar E-≟
import CSP.Laws.AlphaParallel {ℓ} {ℓe} {E} as CSPAParLaws
open CSPAParLaws E-≟

-------------------------------------------------------------------------------------
-- A tree is vis-headed when its force is a `vis` node.

VisHead : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} → ITree E (ExtI I) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
VisHead {I = I} {R = R} t =
  Σ[ f ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))) ] (t .force ≡ vis f)

-- The fold of a non-empty list of vis-headed components is itself vis-headed.
∥list-headed : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (c : Comp I R) (xs : List (Comp I R))
  → All (λ d → VisHead (Comp.proc d)) (c ∷ xs)
  → VisHead (∥list (c ∷ xs))
∥list-headed c [] ((fc , eqc) ∷ tl) rewrite eqc = _ , refl
∥list-headed c (c′ ∷ xs′) ((fc , eqc) ∷ tl)
  with ∥list-headed c′ xs′ tl
... | (ftail , eqtail) rewrite eqc | eqtail = _ , refl

-------------------------------------------------------------------------------------
-- (a) Refusal and the network-blocked predicate.
--
-- `Refuses t at a`: whenever `t` is vis-headed, its offer at the event (at , a) is
-- `nothing` — the tree declines to fire that event.
Refuses : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        → ITree E (ExtI I) R → (at : AnyTypes E) → proj₁ at → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Refuses {I = I} {R = R} t at a =
  ∀ (f : (at′ : AnyTypes E) → ContinueType at′ (Maybe (ITree E (ExtI I) R)))
  → t .force ≡ vis f → f at a ≡ nothing

-- The event (at , a) is network-blocked along the list `xs`: at each cons layer,
-- whichever side(s) the routing requires must decline.  Concretely, *if* the head owns
-- the event it must refuse it, *and* *if* the tail's union owns it the tail must block
-- it.  This conjunctive shape feeds the binary `Blocked` exactly: it supplies head
-- refusal for the `(yes , _)` routings and tail blocking for the `(_ , yes)` routings.
-- The empty list is vacuously blocked (its union is ⊥, so nothing can fire there).
NetBlockedAt : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             → List (Comp I R) → (at : AnyTypes E) → proj₁ at → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
NetBlockedAt []       at a = ⊤
NetBlockedAt (c ∷ xs) at a =
    (Comp.alpha c at → Refuses (Comp.proc c) at a)
  × NetBlockedAt xs at a

NetBlocked : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           → List (Comp I R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
NetBlocked xs = ∀ (at : AnyTypes E) (a : proj₁ at) → NetBlockedAt xs at a

-- The folded composite refuses every event that the network blocks (per point).
-- Threads an `All`-vis hypothesis so the merged offer's shape is known at each layer.
∥list-refuses : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              → (xs : List (Comp I R))
              → All (λ d → VisHead (Comp.proc d)) xs
              → (at : AnyTypes E) (a : proj₁ at)
              → NetBlockedAt xs at a
              → Refuses (∥list xs) at a
-- [] : ∥list [] = Skip, force = ret tt ≠ vis f, so the Refuses premise is absurd.
∥list-refuses [] _ at a _ f ()
-- singleton : ∥list (c ∷ []) is the vis|ret composite against Skip.  unionDec [] is
-- always `no`, so only the (yes , no) routing can fire, requiring the head to offer
-- `just`; the head refusal (from `hrefuses`) makes the merged offer `nothing`.
∥list-refuses (c ∷ []) ((fc , eqc) ∷ _) at a (hrefuses , tt) f feq
  with (λ pc → hrefuses pc fc eqc)
... | mkhr rewrite eqc with feq
...   | refl with Comp.adec c at
...     | yes pc rewrite mkhr pc = refl
...     | no _ = refl
-- cons (nonempty tail) : both head and folded tail are vis-headed, so the composite is
-- the vis|vis merged offer.  Case on (adec c at , unionDec (c′∷xs′) at) and discharge
-- each routing with head refusal and/or the tail's induced refusal.
∥list-refuses (c ∷ c′ ∷ xs′) ((fc , eqc) ∷ tl) at a (hrefuses , tblocks) f feq
  with ∥list-headed c′ xs′ tl
... | (g , eqtail)
  with (λ pc → hrefuses pc fc eqc)
     | ∥list-refuses (c′ ∷ xs′) tl at a tblocks g eqtail
...   | mkhr | gr rewrite eqc | eqtail with feq
...     | refl with Comp.adec c at | unionDec (c′ ∷ xs′) at
...       | yes pc | yes pt rewrite mkhr pc = refl
...       | yes pc | no _   rewrite mkhr pc = refl
...       | no _   | yes pt rewrite gr = refl
...       | no _   | no _   = refl

-------------------------------------------------------------------------------------
-- (b) The n-ary refusal-composition law: a network-blocked fold is IsStuck.

-- For the singleton base case ∥list (c ∷ []) is the vis|ret composite against Skip.
-- Its force is a `vis` node, so the only step shape is `sVis`; the merged offer is
-- `nothing` everywhere (unionDec [] is always `no`, so only the (yes , no) routing can
-- fire, and the head refuses there), contradicting the branch-eq.
∥list-IsStuck : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (c : Comp I R) (xs : List (Comp I R))
  → All (λ d → VisHead (Comp.proc d)) (c ∷ xs)
  → NetBlocked (c ∷ xs)
  → IsStuck (∥list (c ∷ xs))
-- singleton: only `sVis` is shape-compatible; merged offer is `nothing` everywhere.
∥list-IsStuck c [] ((fc , eqc) ∷ _) nb (sVis {at = at} {a = a} feq branch-eq)
  with nb at a
... | (hrefuses , tt)
    with (λ pc → hrefuses pc fc eqc)
...   | mkhr rewrite eqc with feq
...     | refl with Comp.adec c at
...       | yes pc rewrite mkhr pc = case branch-eq of λ ()
...       | no _                   = case branch-eq of λ ()
∥list-IsStuck c [] ((fc , eqc) ∷ _) nb (sMixVis eq-mix _) rewrite eqc = case eq-mix of λ ()
∥list-IsStuck c [] ((fc , eqc) ∷ _) nb (sRet eq)          rewrite eqc = case eq of λ ()
∥list-IsStuck c [] ((fc , eqc) ∷ _) nb (sSil eq)          rewrite eqc = case eq of λ ()
∥list-IsStuck c [] ((fc , eqc) ∷ _) nb (sNdbr eq _)       rewrite eqc = case eq of λ ()
∥list-IsStuck c [] ((fc , eqc) ∷ _) nb (sMixSlide eq)     rewrite eqc = case eq of λ ()
-- cons (nonempty tail): both operands vis-headed, apply the binary law.
∥list-IsStuck c (c′ ∷ xs′) ((fc , eqc) ∷ tl) nb
  with ∥list-headed c′ xs′ tl
... | (g , eqtail) =
    αpar-IsStuck eqc eqtail blocked
  where
    blocked : ∀ (at : AnyTypes E) (a : proj₁ at)
            → Blocked (Comp.alpha c) (unionα (c′ ∷ xs′))
                      (Comp.adec c) (unionDec (c′ ∷ xs′)) fc g at a
    blocked at a with nb at a
    ... | (hrefuses , tblocks)
        with Comp.adec c at | unionDec (c′ ∷ xs′) at
    ...   | yes pc | yes pt = lift (inj₁ (hrefuses pc fc eqc))
    ...   | yes pc | no _   = lift (hrefuses pc fc eqc)
    ...   | no _   | yes pt = lift (∥list-refuses (c′ ∷ xs′) tl at a tblocks g eqtail)
    ...   | no _   | no _   = tt

-------------------------------------------------------------------------------------
-- (c) Sanity: a network of `Stop` components is stuck, hence has a deadlock.

private
  module Sanity where
    open import ITree_Relations.Deadlock using (HasDeadlock)

    All∈ : Alpha
    All∈ _ = ⊤ {lzero}
    All-dec : Dec-Alpha All∈
    All-dec _ = yes tt

    stopC : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} → Comp I R
    stopC = comp All∈ All-dec Stop

    -- Stop = deadlock has force `vis (λ _ _ → nothing)`, so it is vis-headed and its
    -- offer is `nothing` everywhere: it refuses every event.
    stop-refuses : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 → (at : AnyTypes E) (a : proj₁ at) → Refuses (Stop {E = E} {I = ExtI I} {R = R}) at a
    stop-refuses at a f refl = refl

    -- Two-component network of Stops, blocked at every event.
    stops-blocked : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                  → NetBlocked (stopC {I = I} {R = R} ∷ stopC ∷ [])
    stops-blocked at a =
      (λ _ → stop-refuses at a) , (λ _ → stop-refuses at a) , tt

    stops-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              → All (λ d → VisHead (Comp.proc d)) (stopC {I = I} {R = R} ∷ stopC ∷ [])
    stops-vis = (_ , refl) ∷ (_ , refl) ∷ []

    stops-stuck : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                → IsStuck (∥list (stopC {I = I} {R = R} ∷ stopC ∷ []))
    stops-stuck = ∥list-IsStuck stopC (stopC ∷ []) stops-vis stops-blocked

    stops-deadlock : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                   → HasDeadlock (∥list (stopC {I = I} {R = R} ∷ stopC ∷ []))
    stops-deadlock = [] , _ , bNil , stops-stuck

-------------------------------------------------------------------------------------
-- (d) n-ary trace-decomposition (elimination) law for the replicated parallel.
--
-- A trace of `∥list xs` splits, at the head layer, into a binary `AlphaSyncSplit` of
-- the head component (`Comp.proc c`) against the tail-composite (`∥list xs`).  The
-- empty list is a leaf (`∥list [] = Skip`): there is nothing to split, so the trace is
-- carried as-is.  The cons case carries the binary head/tail split; the tail-composite's
-- trace lives inside that `AlphaSyncSplit` and can be recursively decomposed by applying
-- `∥list-trace` to it for full flattening.

data ListSyncSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  : (xs : List (Comp I R)) → List (Event√ E (RetOf xs)) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr) where
  nil-split  : ∀ {s} → traces (∥list {I = I} {R = R} []) s → ListSyncSplit [] s
  cons-split : ∀ {c xs s}
             → AlphaSyncSplit (Comp.alpha c) (unionα xs) (Comp.proc c) (∥list xs) s
             → ListSyncSplit (c ∷ xs) s

∥list-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (xs : List (Comp I R)) {s : List (Event√ E (RetOf xs))}
  → traces (∥list xs) s → ListSyncSplit xs s
∥list-trace []       tr = nil-split tr
∥list-trace (c ∷ xs) tr =
  cons-split (AlphaParallel-trace (Comp.proc c) (∥list xs)
                                  (Comp.alpha c) (Comp.adec c)
                                  (unionα xs) (unionDec xs) tr)

-------------------------------------------------------------------------------------
-- (e) n-ary trace-introduction law for the replicated parallel.
--
-- The dual of `∥list-trace`: given a (vis-driven, head-stable) trace `bc` of the head
-- component and a trace `bxs` of the tail-composite that synchronise per `AlphaSync`,
-- the folded composite `∥list (c ∷ xs)` performs the merged trace `s`.  Since
-- `∥list (c ∷ xs)` is *definitionally* the binary parallel of the head against the
-- tail-composite, this is exactly the binary introduction law `αpar-trace-intro`
-- instantiated at the head layer; the caller iterates it down the list (supplying the
-- tail's trace `bxs`, itself built by a recursive application of this lemma).

∥list-trace-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    (c : Comp I R) (xs : List (Comp I R))
    {sc sxs s : List (Event E)}
    {c′ : ITree E (ExtI I) R} {xs′ : ITree E (ExtI I) (RetOf xs)}
    {bc : Comp.proc c ═⟨ map evl sc ⟩═► c′}
    {bxs : ∥list xs ═⟨ map evl sxs ⟩═► xs′}
  → AlphaSync (Comp.alpha c) (unionα xs) sc sxs s
  → VisDriven bc → VisDriven bxs
  → isStable c′ → isStable xs′
  → (∥list (c ∷ xs)) ═⟨ map evl s ⟩═►
      (c′ ⟦ Comp.alpha c ¿ Comp.adec c ∥ unionα xs ¿ unionDec xs ⟧ xs′)
∥list-trace-intro c xs {bc = bc} {bxs = bxs} asy vdc vdxs stc stxs =
  αpar-trace-intro asy bc vdc bxs vdxs stc stxs

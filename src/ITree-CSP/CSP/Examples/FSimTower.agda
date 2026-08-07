{-# OPTIONS --guardedness #-}

-- WORKED EXAMPLE: an FSim tower assembled from component FSims.
--
-- This is the smoke test the FSim layer previously lacked.  `CSP.Laws.FSim.*` supplies
-- five operator congruences.  Before this campaign no FSim CONGRUENCE had an external
-- consumer: `CSP.Laws.Stability.Closure` already imported an FSim HELPER
-- (`CSP.Laws.FSim.HideCong.hide-stable-noOffA`, not a congruence), and the only
-- compositional FD proof anywhere in the repo was the 3-state vending machine
-- (`CSP.Examples.VendingMachine.VendingMachine`, via `loop0-mono-⊑FD`).  The two existing
-- FSim consumers (`CSP.Examples.UCS.Ch6.BuffersFSim`, `…Liveness.PipePairFlipBFsFSim`)
-- each build ONE `FSim` by hand via `FSimFromRel` — the monolithic route again, just
-- one-directional.  This campaign's own `CSP.Laws.FD.Congruences` now imports/re-exports
-- the FSim congruences as well.  (It used to name `CSP.Laws.FD.LoopMonoFD` here too; that
-- module has since been deleted outright, its four surviving `FSim → ⊑FD` loop wrappers
-- superseded by the fact-shaped `CSP.Laws.FD.IterMonoFD`.)
--
-- Here the refinement is instead ASSEMBLED:
--
--     per-leaf `⊓-refine-fsim`   (2 leaves, strict one-way refinements)
--   → `⦀Fin-fsim`               (fold, Sep discharged from disjoint alphabets)
--   → `Hide-fsim`               (unconditional — the operator where ⊑FD-mono is FALSE)
--   → `fsim→⊑FD`                (cash out ONCE, at the top)
--
-- The shape `(⦀Fin n leaf) ∖ msgs` is the shape of every real target in this repo, and
-- hiding appears on BOTH sides as it does in the BlockFetch abstract refinement.
--
-- WHY THIS MATTERS: unconditional `Hide-mono-⊑FD` is FALSE (`CSP.Laws.FD.HideMonoFD`),
-- so a composite built from bare `⊑FD` facts cannot cross a hide. What crosses instead
-- is a WITNESS — here, `Hide-fsim` (unconditional) then `fsim→⊑FD`; `⊑FD → FSim`
-- completeness is out of scope, so a `⊑FD` fact can never be substituted for one. See
-- `CSP.Laws.FD.Congruences`'s "WHY HIDING IS THE CRUX" note for the full statement,
-- including the strictly-stronger `cong-∖`/`hide-cong-FD` route and what the weaker
-- orders do and do NOT give: `⊑T` is unconditionally hide-monotone (`Hide-mono-⊑ᵀ`), but
-- `⊑F⊥` is NOT — `Hide-mono-fail` is the unconditional stable-FAILURE transfer
-- (`failures` in, `failures⊥` out), not `⊑F⊥` monotonicity, and unconditional `⊑F⊥`
-- monotonicity through hiding fails by the same divergence-chaos mechanism as `⊑FD`.
-- This module demonstrates the FSim route.
--
-- POSTULATES: none local.  Inherited: `Diverges-LEM` + `¬DivModA→MAcc` via `Hide-fsim`,
-- `Par-Diverges→` via `Par-fsim` (through `⦀Fin-fsim`); all three are certified from the
-- single `dne` of `CSP.Laws.ClassicalFromLEM`.  `Semantics.DRImpliesFD` IS reached
-- transitively (`Hide-fsim` → `CSP.Laws.FD.FDTransfer`), but nothing here uses its
-- `¬-divergent→normal` or `drbisim→≈FD`: the whole tower goes through `FSim` only.

module CSP.Examples.FSimTower where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _F≟_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤poly)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; sym; trans)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. The event type: two channels, each indexed by the leaf that owns it.
--   `mid i` — leaf i's INTERNAL channel (the one hidden at the top of the tower)
--   `out i` — leaf i's EXTERNAL channel (survives the hide)
-- Both carry `⊤`, which is inhabited, so both can actually fire (an event over an
-- uninhabited carrier is unobservable).
data TEv : Set → Set where
  mid : Fin 2 → TEv ⊤
  out : Fin 2 → TEv ⊤

-- decidable equality on the event family: channel tag first, then the leaf index
TEv-≟ : (x y : AnyTypes TEv) → Dec (x ≡ y)
TEv-≟ (_ , mid i) (_ , mid j) with i F≟ j
... | yes refl = yes refl
... | no  i≢j  = no (λ { refl → i≢j refl })
TEv-≟ (_ , out i) (_ , out j) with i F≟ j
... | yes refl = yes refl
... | no  i≢j  = no (λ { refl → i≢j refl })
TEv-≟ (_ , mid _) (_ , out _) = no (λ ())
TEv-≟ (_ , out _) (_ , mid _) = no (λ ())

open import CSP.Operators TEv-≟
open EventSet

-- the process type of this example: ⊤-returning trees over `TEv`
TProc : Set₁
TProc = PTree TEv (ExtI TEv) (⊤poly {lzero})

-- ONE IMPORT for the whole suite.  Everything the tower below needs — the two semantic
-- relations (`FSim`, `_⊑FD_`) and the cash-out (`fsim→⊑FD`), the three component
-- congruences (`⊓-refine-fsim`, `⦀Fin-fsim`, `Hide-fsim`), and the premise vocabulary
-- with its introduction forms (`Alpha`, `Disj`, `OffersOnly`, `OffersOnly-Prefix₀`,
-- `OffersOnly-Skip`) — comes through the index module `CSP.Laws.FD.Congruences`, which
-- re-exports them from `Semantics.FailureSim` / `.FailuresDivergences`,
-- `CSP.Laws.FSim.IChoiceCong` / `.ParCongRep` / `.HideCong` and
-- `CSP.Laws.Bisim.DRCongruenceRep` respectively.  This module is deliberately the index's
-- REGRESSION TEST: it is what turns the index's "downstream users need one import" from
-- an untested assertion into something the build checks.  The proof bodies below are
-- unchanged by the reroute — every repointed name resolves to the same definition.
-- Only `Process_Trees` and `CSP.Operators` (process SYNTAX, not congruence results) plus
-- the stdlib remain direct imports.
open import CSP.Laws.FD.Congruences TEv-≟
  using (FSim; fsim→⊑FD; _⊑FD_; ⊓-refine-fsim; Hide-fsim; ⦀Fin-fsim;
         Alpha; Disj; OffersOnly; OffersOnly-Prefix₀; OffersOnly-Skip)

------------------------------------------------------------------------------------
-- §2. The two leaves.  Each leaf spec is STRICTLY more nondeterministic than its
-- impl, so every leaf refinement is a genuine one-way `⊑FD` and not a disguised
-- bisimulation.
------------------------------------------------------------------------------------

-- leaf impl i: emit on the internal channel, then on the external one, then stop
implLeaf : ∀ (i : Fin 2) → TProc
implLeaf i = mid i ⟶₀ (out i ⟶₀ Skip)

-- an alternative branch, used only to make each leaf spec strictly more
-- nondeterministic than its impl: it skips the internal step and emits on the
-- external channel TWICE.  Emitting twice is deliberate — it keeps the refinement
-- strict AFTER the hide as well: `⟨out i, out i⟩` is a trace of the hidden spec and
-- of no state of the hidden impl (each impl leaf emits `out i` once, and the other
-- leaf owns a different channel), whereas the mere absence of the internal step is
-- invisible once `mid` is hidden.  (Argued informally here — as in the
-- `Pinf ⊑FD Qh` half of `CSP.Laws.FD.HideMonoFD`'s header — not formalised:
-- `¬ ((⦀Fin 2 specLeaf ∖ msgs) ⊑FD (⦀Fin 2 implLeaf ∖ msgs))` has no Agda proof in
-- this module.)
altLeaf : ∀ (i : Fin 2) → TProc
altLeaf i = out i ⟶₀ (out i ⟶₀ Skip)

-- leaf spec i: the impl OR the alternative — a genuine one-way refinement, since
-- `(P ⊓ Q) ⊑FD P` but not conversely
specLeaf : ∀ (i : Fin 2) → TProc
specLeaf i = implLeaf i ⊓ altLeaf i

-- each leaf spec failure-simulates its impl, by resolving the internal choice left
leaf-fsim : ∀ (i : Fin 2) → FSim (⊤poly {lzero}) (implLeaf i) (specLeaf i)
leaf-fsim i = ⊓-refine-fsim (implLeaf i) (altLeaf i)

------------------------------------------------------------------------------------
-- §3. Per-leaf alphabets: confinement of the impl family and pairwise disjointness,
-- the two hypotheses `⦀Fin-fsim` needs.
------------------------------------------------------------------------------------

-- the leaf that owns a channel: both `mid i` and `out i` belong to leaf `i`
ChanOf : AnyTypes TEv → Fin 2
ChanOf (_ , mid i) = i
ChanOf (_ , out i) = i

-- leaf i's alphabet: exactly the two channels carrying index i
leafAlpha : Fin 2 → Alpha
leafAlpha i at a = ChanOf at ≡ i

-- distinct leaves have disjoint alphabets (a channel has exactly one owner)
leafDisj : ∀ i j → i ≢ j → Disj (leafAlpha i) (leafAlpha j)
leafDisj i j i≢j at a p q = i≢j (trans (sym p) q)

-- each impl leaf offers only within its own alphabet: two nested prefixes on
-- channels owned by leaf i, then `Skip` (which offers nothing visible)
leafOO : ∀ i → OffersOnly (leafAlpha i) (implLeaf i)
leafOO i = OffersOnly-Prefix₀ (λ _ → refl)
             (OffersOnly-Prefix₀ (λ _ → refl) OffersOnly-Skip)

------------------------------------------------------------------------------------
-- §4. The tower.
------------------------------------------------------------------------------------

-- membership in the internal channel family (value-independent, so decidable
-- by inspecting the channel tag alone)
IsMid : AnyTypes TEv → Set
IsMid (_ , mid _) = ⊤
IsMid (_ , out _) = ⊥

-- decision procedure for `IsMid`
IsMid? : (at : AnyTypes TEv) → Dec (IsMid at)
IsMid? (_ , mid _) = yes tt
IsMid? (_ , out _) = no (λ z → z)

-- the hidden internal channel family: every `mid i`, at every value
msgs : EventSet
msgs = chanSet IsMid IsMid?

-- THE TOWER: fold the two leaves, then hide the internal channel on BOTH sides
tower-fsim : FSim (⊤poly {lzero})
                  ((⦀Fin 2 implLeaf) ∖ msgs)
                  ((⦀Fin 2 specLeaf) ∖ msgs)
tower-fsim = Hide-fsim msgs (⦀Fin-fsim leafAlpha leafDisj leafOO leaf-fsim)

-- THE HEADLINE: a compositional FD refinement, assembled rather than hand-built
tower⊑FD : ((⦀Fin 2 specLeaf) ∖ msgs) ⊑FD ((⦀Fin 2 implLeaf) ∖ msgs)
tower⊑FD = fsim→⊑FD tower-fsim

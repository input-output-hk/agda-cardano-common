# Four-node diamond over breakable links — LTL liveness specification

This module *states* (does not prove) the block-liveness property of the
broken four-node diamond `systemBroken`
(`FourNodeDiamondBroken.lagda.md`): **a block produced by NodeA eventually
reaches NodeD, provided all `break` events are confined to at most one path
group** — G1 = {AB, BD} or G2 = {AC, CD}. ("No link broken" is subsumed:
breaks confined to one group ⟺ the other path stays whole.) Node A is no
longer hardwired to the block `b1`: `systemBroken` now takes A's produced
block `blkA : Block₃` as an argument, and every statement below quantifies
over it, so the property is asserted for *every* configuration of A. The
statements keep the payload quantifier `b` **separate** from `blkA` —
`producedA b` already pins the observed payload, and no `b ≡ blkA` fact is
needed (or available). The property is
phrased in the trace-based LTL layer `Semantics.LTL.Traces_Based`, first two
ways — as a formula-level satisfaction statement (`BlockLiveness`) and as a
positive, proof-friendly dual (`BlockLiveness⁺`). On this branch's model
(`examples/praos_liveness`: `apiES` now gates **all** api channels — see
`docs/superpowers/specs/2026-07-22-praos-liveness-model-change-design.md`) the
non-Praos peers (KeepAlive, TxSubmission, Leios) cannot free-run, so
**`BlockLiveness⁺` (no fairness antecedent) is the honest, provable headline
target here** — it is no longer refuted by an unfair KA-starvation trace. A
third, fairness-qualified target `BlockLiveness⁺ᶠ`, from an earlier fairness
spike (milestone F3) against the free-running, api-narrow model
(`examples/four_node_liveness`), is retained below for reference but is
**superseded for this model** (see the *Fairness amendment* section). All
three are `Set`s — deliberately unproved and NOT postulated; the only proofs
here are sanity tests for the four atomic frame predicates and the two
fairness classes. Design doc:
`docs/superpowers/specs/2026-07-14-fournode-liveness-ltl-spec-design.md`;
fairness spike report:
`docs/superpowers/specs/2026-07-19-ltl-fairness-spike-report.md`;
Praos model-change design:
`docs/superpowers/specs/2026-07-22-praos-liveness-model-change-design.md`.

```agda
{-# OPTIONS --guardedness #-}
```

```agda
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Level using (0ℓ)
open import Process_Trees using (PTree; ExtI)

module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec where
```

The healthy diamond supplies the shared `Params` `p`, the four link
identifiers, and the block domain `Block₃` (`p`'s `Block` field — the type
the BF `sendBFBlock`/`recvBFBlock` API events carry); the broken diamond
supplies the system under specification:

```agda
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD; Block₃; b1; b2 )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using ( systemBroken )
```

The alphabet: directions from `Base`; the `apiBF`/`break` channels, the
BlockFetch API tags, and decidable equality from `Net p`; the `Payload` data
domain from `Data p`:

```agda
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; apiBF; apiKA; break
        ; sendBFBlock; recvBFBlock; sendBFStartBatch; sendKADone; sendKAMsg )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
```

`Op.Skip` fills the (never-forced) state slot of hand-built test frames;
`evl`/`evLabel` from the LTS build visible-event observations; the LTL layer
is instantiated at the same alphabet as `systemBroken` itself:

```agda
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; evl; evLabel )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}

-- visible-class weak fairness (milestone F1), instantiated at this alphabet;
-- `Fair C tr` is the F3 antecedent that excludes the KA-starvation trace
open import Semantics.LTL.Fairness
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Fair )
```

## Atoms

Four frame predicates, each a dependent pattern match on the visible-step
frame shape; every non-matching frame (wrong channel/tag, `√`-events, `done`,
`stuck`, `div`) falls to the catch-all clause and denotes `⊥`. Matching the
BF tag (`sendBFBlock`/`recvBFBlock`) refines the event's carrier to `Block₃`
(= `Params.Block p`), so equating the carried value with `b` is well-typed.

```agda
-- A hands block b to a BF server peer: apiBF sendBFBlock at hi on AB or AC
producedA : Block₃ → FramePred 0ℓ (⊤ {0ℓ})
producedA b (step _ (evl (evLabel _ (apiBF l d sendBFBlock) a))) =
  ((l ≡ linkAB) ⊎ (l ≡ linkAC)) × (d ≡ hi) × (a ≡ b)
producedA _ _ = ⊥

-- D's BF client receives block b: apiBF recvBFBlock at hi on BD or CD, carrying
-- EXACTLY b.  The payload conjunct `a ≡ b` mirrors `producedA`'s, so the headline
-- reads "the block A produced is the block D receives", not merely "some block
-- arrives".  (SESSION-51: restored.  It is discharged by the per-leg block-VALUE
-- invariant `Praos.PipeValInv.PipeVal` — folded from `rinit` to the delivering
-- frame by `Praos.PipeValWalk` — together with `Praos.PipeValRecv.recvFire-blkA-*`
-- (the delivered value IS D's BF client's held block) and
-- `Praos.PipeValWalk.prodBlkA` (`b ≡ blkA`).  The payload-AGNOSTIC predicate the
-- delivery walk itself produces is `arrivedD⁻` below; `Praos.PipeValArrive`
-- upgrades one to the other.)
arrivedD : Block₃ → FramePred 0ℓ (⊤ {0ℓ})
arrivedD b (step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))) =
  ((l ≡ linkBD) ⊎ (l ≡ linkCD)) × (d ≡ hi) × (a ≡ b)
arrivedD _ _ = ⊥

-- the payload-AGNOSTIC delivery observation: ANY D-`recvBFBlock@hi` on BD or CD.
-- This is what the delivery walk establishes directly (it is block-blind — the
-- pending invariant `Pr` does not read the block); `arrivedD` is recovered from
-- it by the value layer, so the walk never has to carry a value.
arrivedD⁻ : FramePred 0ℓ (⊤ {0ℓ})
arrivedD⁻ (step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))) =
  ((l ≡ linkBD) ⊎ (l ≡ linkCD)) × (d ≡ hi)
arrivedD⁻ _ = ⊥

-- a break event on path group 1 = {AB, BD}
brkG1 : FramePred 0ℓ (⊤ {0ℓ})
brkG1 (step _ (evl (evLabel _ (break l) _))) = (l ≡ linkAB) ⊎ (l ≡ linkBD)
brkG1 _ = ⊥

-- a break event on path group 2 = {AC, CD}
brkG2 : FramePred 0ℓ (⊤ {0ℓ})
brkG2 (step _ (evl (evLabel _ (break l) _))) = (l ≡ linkAC) ⊎ (l ≡ linkCD)
brkG2 _ = ⊥
```

## Formulas

```agda
-- breaks confined to one group: the other path's links never break
confined : LTLᵗ 0ℓ (⊤ {0ℓ})
confined = (G (¬ atom brkG1)) ∨ (G (¬ atom brkG2))

-- response: whenever A produces b, D eventually receives b
respondsAtoD : Block₃ → LTLᵗ 0ℓ (⊤ {0ℓ})
respondsAtoD b = confined ⇒ (G ((atom (producedA b)) ⇒ (F (atom (arrivedD b)))))
```

## The specification

```agda
-- THE SPECIFICATION (a Set: stated, deliberately unproved, NOT postulated); A may produce ANY block `blkA`
BlockLiveness : Set _
BlockLiveness = ∀ (blkA : Block₃) (b : Block₃) → systemBroken blkA ⊨ respondsAtoD b
```

## Positive dual

The future constructive proof's target. `G`/`F` above are the classical
`¬`-encodings; `□ᵗ`/`◇ᵗ` are the library's positive coinductive/inductive
forms, bridged by the `F⇒◇ᵗ`/`◇ᵗ⇒F` and `□ᵗ⇒⟦G⟧⁺`/`⟦G⟧⁺⇒□ᵗ`/`⟦G⟧⁺⇒⟦G⟧`
equivalences of `Traces_Based` §6.1. Suffixes are quantified by the library's
`drop n` idiom (`drop n tr : Trace _ (dropIdx n tr)`), as in the VM `⊨`
proofs.

```agda
-- positive dual of BlockLiveness for a FIXED produced block `blkA`: □ᵗ confinement hypothesis, ◇ᵗ response at every suffix
BlockLiveness⁺At : Block₃ → Set _
BlockLiveness⁺At blkA = ∀ (b : Block₃) (tr : Trace (⊤ {0ℓ}) (systemBroken blkA))
                      → (□ᵗ (¬ atom brkG1) tr ⊎ □ᵗ (¬ atom brkG2) tr)
                      → ∀ (n : ℕ) → ⟦ atom (producedA b) ⟧ (drop n tr)
                      → ◇ᵗ (atom (arrivedD b)) (drop n tr)

-- positive dual of BlockLiveness at an arbitrary produced block: the ∀-closure of `BlockLiveness⁺At`
BlockLiveness⁺ : Set _
BlockLiveness⁺ = ∀ (blkA : Block₃) → BlockLiveness⁺At blkA
```

## Fairness amendment (F3) — superseded on this model

**The unfairness caveat — updated for `examples/praos_liveness`.** The
original caveat below applied to the **free-running, api-narrow** model
(`examples/four_node_liveness`, `apiES = {apiCS, apiBF}`): the KeepAlive
**client** is an autonomous, perpetual **visible** loop whose
`apiKA … sendKAMsg` events lay **outside** that narrower sync alphabet, so
`∥⇘apiES⇙` interleaved them freely — they could fire forever with no
partner required, and a maximal trace could schedule the KA loop
*exclusively* after a `producedA b` frame, starving the fetch pipeline and
refuting `BlockLiveness⁺` (informally, per the M1 finding
(`.superpowers/sdd/m1-report.md`) — no formal counterexample trace is
constructed here). **On this branch, `apiES` gates ALL api channels**
(`apiCS`/`apiBF`/`apiKA`/`apiTS`/`apiLN`/`apiLF` — see
`docs/superpowers/specs/2026-07-22-praos-liveness-model-change-design.md`), so
the KeepAlive/TxSubmission/Leios peers must rendezvous with the (Praos-only)
node drivers on every api event; drivers never offer those non-Praos api
events, so those peers cannot fire at all — they go inert rather than
free-running, and the KA-starvation counterexample no longer applies.
`BlockLiveness⁺` is therefore the honest, fairness-free target on this
model. The fairness spike
(`docs/superpowers/specs/2026-07-19-ltl-fairness-spike-report.md`) that
introduced a **weak-fairness hypothesis on a visible event class** `C`
(`Semantics.LTL.Fairness.Fair`) to rescue the free-running model is
**superseded for this model** — `BlockLiveness⁺ᶠ` and the two fairness
classes below are kept, unmodified, for reference and for the free-running
variant only; they are not this branch's proof target.

### The intact-path fetch-driver classes

`C` must make the *intact* path's fetch progress. Under `□ᵗ (¬ atom brkG1)`
the group {AB, BD} never breaks, so the whole route is A→B→D and the
fetch-relevant driver events are that route's BlockFetch api events — the
wildcard tag match captures **all** `apiBF` tags on links AB/BD at the driver
direction `hi` (requests, hand-off/server-side tags like `reqBFRange`/
`sendBFStartBatch`/`sendBFBatchDone`, and the `recvBFBlock` delivery — spike
§Q1 refinement); symmetrically under `□ᵗ (¬ atom brkG2)`
for A→C→D on AC/CD. We therefore define **two** classes, one per candidate
intact path, mirroring the atom-definition style (`apiBF` refines the
carrier; every non-`apiBF` event — crucially `apiKA`, and any other-path or
wrong-direction `apiBF` — falls to the catch-all `⊥`). These classes exclude
`apiKA` **by construction**, which is exactly what defeats the KA
counterexample.

```agda
-- superseded on the all-api-synced Praos model (kept for the free-running variant)
-- intact-path A→B→D fetch driver: apiBF on {AB, BD} at hi — the wildcard tag
-- captures ALL apiBF tags (requests, hand-off/server-side tags like
-- reqBFRange/sendBFStartBatch/sendBFBatchDone, and recvBFBlock)
C-ABD : Event → Set
C-ABD (evLabel _ (apiBF l d _) _) = ((l ≡ linkAB) ⊎ (l ≡ linkBD)) × (d ≡ hi)
C-ABD _ = ⊥

-- superseded on the all-api-synced Praos model (kept for the free-running variant)
-- intact-path A→C→D fetch driver: apiBF on {AC, CD} at hi — the wildcard tag
-- captures ALL apiBF tags (requests, hand-off/server-side tags like
-- reqBFRange/sendBFStartBatch/sendBFBatchDone, and recvBFBlock)
C-ACD : Event → Set
C-ACD (evLabel _ (apiBF l d _) _) = ((l ≡ linkAC) ⊎ (l ≡ linkCD)) × (d ≡ hi)
C-ACD _ = ⊥
```

### `BlockLiveness⁺ᶠ` — the M5 target

The design choice (this module records the reasoning): **option (i) — pair
each confinement disjunct with its own path-matched `Fair` class** — rather
than a single `Fair` over the union class (option (ii)). Justification: (a)
this is the **weakest** hypothesis that plausibly suffices, hence the
**strongest** theorem. A caller who has G1-confinement and fairness on the
ABD driver (but not on the ACD driver, nor on the union) satisfies option (i)
but *not* option (ii), so option (i) is satisfiable by strictly more traces.
(b) `Fair` is mixed-variance in `C` (its class occurs positively in the
`Fires` consequent and negatively in the `enabledAt` antecedent), so a single
union `Fair (C-ABD ∪ C-ACD)` does **not** even imply the per-path `Fair`
the walk consumes — union-firing need not be intact-path firing — making
option (ii) both heavier *and* insufficient. (c) The abstract-liveness walk
needs fairness precisely on the driver of *whichever* path confinement leaves
intact; pairing supplies exactly that and no more. This refines the spike
§Q3 sketch (a single `Fair C` printed outside the `⊎`), which under-specifies
the class and cannot path-match once the disjunct is only known dynamically.

```agda
-- superseded on the all-api-synced Praos model (kept for the free-running variant)
-- fairness-qualified positive dual: each confinement disjunct is paired with
-- weak fairness on that intact path's BF fetch driver (the honest M5 target)
BlockLiveness⁺ᶠ : Set _
BlockLiveness⁺ᶠ = ∀ (blkA : Block₃) (b : Block₃) (tr : Trace (⊤ {0ℓ}) (systemBroken blkA))
                → ( (□ᵗ (¬ atom brkG1) tr × Fair C-ABD tr)
                  ⊎ (□ᵗ (¬ atom brkG2) tr × Fair C-ACD tr) )
                → ∀ (n : ℕ) → ⟦ atom (producedA b) ⟧ (drop n tr)
                → ◇ᵗ (atom (arrivedD b)) (drop n tr)
```

## Atom sanity tests

The only proofs in this module. `Frame` values are plain data, so matching
and near-miss frames are hand-built with `Op.Skip` in the (never-forced)
state slot — we never construct a `Trace` of `systemBroken` or take an LTS
step of it (a single step of the composite costs ≈2.5 min / ≈20 GB, as
documented in `FourNodeDiamond.lagda.md`).

```agda
-- a hand-built visible frame (state slot never forced)
mkVis : ∀ {B : Set} → Net_Api Payload B → B → Frame (⊤ {0ℓ})
mkVis e a = step Op.Skip (evl (evLabel _ e a))
```

`producedA` holds on A's `sendBFBlock` at `hi`, on AB and on AC, carrying `b1`:

```agda
-- producedA holds on A's sendBFBlock at hi on AB carrying b1
_ : producedA b1 (mkVis (apiBF linkAB hi sendBFBlock) b1)
_ = inj₁ refl , refl , refl

-- and on AC
_ : producedA b1 (mkVis (apiBF linkAC hi sendBFBlock) b1)
_ = inj₂ refl , refl , refl
```

`producedA` rejects each near-miss: wrong payload (`b2`), wrong direction
(`lo`), wrong link (BD), wrong channel tag (`sendBFStartBatch`):

```agda
-- rejects: wrong payload (b2 ≢ b1)
_ : producedA b1 (mkVis (apiBF linkAB hi sendBFBlock) b2) → ⊥
_ = λ { (_ , _ , ()) }

-- rejects: wrong direction (lo ≢ hi)
_ : producedA b1 (mkVis (apiBF linkAB lo sendBFBlock) b1) → ⊥
_ = λ { (_ , () , _) }

-- rejects: wrong link (linkBD ≢ linkAB, ≢ linkAC — distinct Fin 4 literals)
_ : producedA b1 (mkVis (apiBF linkBD hi sendBFBlock) b1) → ⊥
_ = λ { (inj₁ () , _) ; (inj₂ () , _) }

-- rejects: wrong channel tag (sendBFStartBatch — atom reduces to ⊥)
_ : producedA b1 (mkVis (apiBF linkAB hi sendBFStartBatch) U.tt) → ⊥
_ = λ ()
```

`arrivedD` holds on D's `recvBFBlock` at `hi` on BD and on CD, and rejects
each near-miss: wrong payload (`b2`), wrong direction (`lo`), wrong link
(AB), wrong channel tag (`sendBFBlock`, the send-side):

```agda
-- arrivedD holds on D's recvBFBlock at hi on BD carrying b1
_ : arrivedD b1 (mkVis (apiBF linkBD hi recvBFBlock) b1)
_ = inj₁ refl , refl , refl

-- and on CD
_ : arrivedD b1 (mkVis (apiBF linkCD hi recvBFBlock) b1)
_ = inj₂ refl , refl , refl

-- SESSION-51: the payload conjunct is BACK, so a wrong payload is REJECTED
_ : arrivedD b1 (mkVis (apiBF linkBD hi recvBFBlock) b2) → ⊥
_ = λ { (_ , _ , ()) }

-- the payload-AGNOSTIC companion (what the delivery walk itself establishes)
-- still fires on any payload
_ : arrivedD⁻ (mkVis (apiBF linkBD hi recvBFBlock) b2)
_ = inj₁ refl , refl

-- rejects: wrong direction (lo ≢ hi)
_ : arrivedD b1 (mkVis (apiBF linkBD lo recvBFBlock) b1) → ⊥
_ = λ { (_ , ()) }

-- rejects: wrong link (linkAB ≢ linkBD, ≢ linkCD — distinct Fin 4 literals)
_ : arrivedD b1 (mkVis (apiBF linkAB hi recvBFBlock) b1) → ⊥
_ = λ { (inj₁ () , _) ; (inj₂ () , _) }

-- rejects: wrong channel tag (sendBFBlock is A's side, not D's receive)
_ : arrivedD b1 (mkVis (apiBF linkBD hi sendBFBlock) b1) → ⊥
_ = λ ()
```

`brkG1`/`brkG2` hold on their own links' breaks and reject the other group's:

```agda
-- brkG1 holds on break linkAB
_ : brkG1 (mkVis (break linkAB) U.tt)
_ = inj₁ refl

-- and on break linkBD
_ : brkG1 (mkVis (break linkBD) U.tt)
_ = inj₂ refl

-- brkG1 rejects group-2 breaks (linkAC ≢ linkAB, ≢ linkBD)
_ : brkG1 (mkVis (break linkAC) U.tt) → ⊥
_ = λ { (inj₁ ()) ; (inj₂ ()) }

-- brkG2 holds on break linkAC
_ : brkG2 (mkVis (break linkAC) U.tt)
_ = inj₁ refl

-- and on break linkCD
_ : brkG2 (mkVis (break linkCD) U.tt)
_ = inj₂ refl

-- brkG2 rejects group-1 breaks (linkBD ≢ linkAC, ≢ linkCD)
_ : brkG2 (mkVis (break linkBD) U.tt) → ⊥
_ = λ { (inj₁ ()) ; (inj₂ ()) }
```

Non-visible frames reject everything:

```agda
-- stuck frame rejects producedA
_ : producedA b1 (stuck Op.Skip) → ⊥
_ = λ ()

-- done frame rejects producedA
_ : producedA b1 (done Op.Skip tt) → ⊥
_ = λ ()

-- div frame rejects brkG1
_ : brkG1 (div Op.Skip) → ⊥
_ = λ ()
```

## Fairness-class sanity tests

The fairness classes are `Event → Set` predicates (not `Frame` predicates),
so they are probed on hand-built `Event`s. `mkEv` pairs a `Net_Api` event
with a carrier value (never a real LTS step of `systemBroken`):

```agda
-- a hand-built visible event (carrier value supplied, no state/step)
mkEv : ∀ {B : Set} → Net_Api Payload B → B → Event
mkEv e a = evLabel _ e a
```

`C-ABD` holds on the ABD path's BF driver: A's `sendBFBlock` at hi on AB
(the produce side), D's `recvBFBlock` at hi on BD (the target), and any BF
request on the path (e.g. `sendBFStartBatch`, ⊤-carried):

```agda
-- C-ABD holds on producedA's event (apiBF sendBFBlock at hi on AB)
_ : C-ABD (mkEv (apiBF linkAB hi sendBFBlock) b1)
_ = inj₁ refl , refl

-- C-ABD holds on arrivedD's event (apiBF recvBFBlock at hi on BD)
_ : C-ABD (mkEv (apiBF linkBD hi recvBFBlock) b1)
_ = inj₂ refl , refl

-- C-ABD holds on a BF request on the path (any apiBF tag, e.g. startBatch)
_ : C-ABD (mkEv (apiBF linkAB hi sendBFStartBatch) U.tt)
_ = inj₁ refl , refl
```

`C-ABD` rejects the KA-starvation source (`apiKA`), the other path's events
(AC/CD), and the wrong direction (lo):

```agda
-- C-ABD rejects apiKA (sendKADone witness) — excluded from the class by construction
_ : C-ABD (mkEv (apiKA linkAB hi sendKADone) U.tt) → ⊥
_ = λ ()

-- C-ABD rejects apiKA sendKAMsg — the actual repeating KA-loop tag (M1 finding)
-- that starves the fetch (∉ class)
_ : C-ABD (mkEv (apiKA linkAB hi sendKAMsg) U.tt) → ⊥
_ = λ ()

-- C-ABD rejects the other path's send (linkAC ∉ {AB, BD})
_ : C-ABD (mkEv (apiBF linkAC hi sendBFBlock) b1) → ⊥
_ = λ { (inj₁ () , _) ; (inj₂ () , _) }

-- C-ABD rejects the other path's receive (linkCD ∉ {AB, BD})
_ : C-ABD (mkEv (apiBF linkCD hi recvBFBlock) b1) → ⊥
_ = λ { (inj₁ () , _) ; (inj₂ () , _) }

-- C-ABD rejects the wrong direction (lo ≢ hi)
_ : C-ABD (mkEv (apiBF linkAB lo sendBFBlock) b1) → ⊥
_ = λ { (_ , ()) }

-- C-ABD rejects a non-api event (break is not apiBF)
_ : C-ABD (mkEv (break linkAB) U.tt) → ⊥
_ = λ ()
```

`C-ACD` is symmetric: holds on the ACD path's BF driver (AC/CD at hi, plus any
BF request on the path), rejects `apiKA`, rejects the ABD path's events
(AB/BD), rejects the wrong direction (lo), and rejects a non-api event
(break):

```agda
-- C-ACD holds on producedA's event on the AC leg (apiBF sendBFBlock at hi on AC)
_ : C-ACD (mkEv (apiBF linkAC hi sendBFBlock) b1)
_ = inj₁ refl , refl

-- C-ACD holds on arrivedD's event on the CD leg (apiBF recvBFBlock at hi on CD)
_ : C-ACD (mkEv (apiBF linkCD hi recvBFBlock) b1)
_ = inj₂ refl , refl

-- C-ACD holds on a BF request on the path (any apiBF tag, e.g. startBatch)
_ : C-ACD (mkEv (apiBF linkAC hi sendBFStartBatch) U.tt)
_ = inj₁ refl , refl

-- C-ACD rejects apiKA (sendKADone witness) — excluded from the class by construction
_ : C-ACD (mkEv (apiKA linkAC hi sendKADone) U.tt) → ⊥
_ = λ ()

-- C-ACD rejects apiKA sendKAMsg — the actual repeating KA-loop tag (M1 finding)
-- that starves the fetch (∉ class)
_ : C-ACD (mkEv (apiKA linkAC hi sendKAMsg) U.tt) → ⊥
_ = λ ()

-- C-ACD rejects the ABD path's send (linkAB ∉ {AC, CD})
_ : C-ACD (mkEv (apiBF linkAB hi sendBFBlock) b1) → ⊥
_ = λ { (inj₁ () , _) ; (inj₂ () , _) }

-- C-ACD rejects the ABD path's receive (linkBD ∉ {AC, CD})
_ : C-ACD (mkEv (apiBF linkBD hi recvBFBlock) b1) → ⊥
_ = λ { (inj₁ () , _) ; (inj₂ () , _) }

-- C-ACD rejects the wrong direction (lo ≢ hi)
_ : C-ACD (mkEv (apiBF linkAC lo sendBFBlock) b1) → ⊥
_ = λ { (_ , ()) }

-- C-ACD rejects a non-api event (break is not apiBF)
_ : C-ACD (mkEv (break linkAC) U.tt) → ⊥
_ = λ ()
```

## Truth analysis (documentation for the future proof — no code)

Summarised from the design doc
`docs/superpowers/specs/2026-07-14-fournode-liveness-ltl-spec-design.md`:

1. **Quiescence risk.** Maximal traces may end in a `stuck` frame — the
   2026-07-07 done-quiescence deadlock finding for `System_CopySpec`-family
   systems. The theorem's content is exactly that no maximal trace of
   `systemBroken` gets stuck or diverges *between* a `producedA b` frame and
   its matching `arrivedD b` frame, under the confinement hypothesis.

2. **Why the property is plausible.** Both A and D interleave (`⦀`) their two
   per-link drivers, so a broken-path driver stalling mid-protocol cannot
   block the intact path's driver; B and C are pass-throughs on distinct
   paths; confinement guarantees one complete path A→X→D never breaks.

3. **Boundary cases the proof must confront.** (a) `break` may fire *after*
   the block is already in flight on that link — the breakable medium kills
   the link mid-delivery (`△ break → Skip` discards the cell's state);
   confinement only promises the *other* path is whole, so delivery must be
   argued via the intact path's copy of `blkA`. (b) A's `produce` on the broken
   path may never emit its `sendBFBlock` — `producedA b` then holds only via
   the intact link's event; this is fine for the response shape. (c) `G` in
   `respondsAtoD` is the classical `¬F¬` encoding — the constructive proof
   should target `BlockLiveness⁺` and transfer via the §6.1 equivalences.

4. **Proof route (future).** Direct trace reasoning is intractable on the
   composite (the documented ≈2.5 min / ≈20 GB single-step cost). The route
   is: a spec-equivalence for the breakable medium (currently deferred —
   likely a `CopySpecBreakableA ≈DR`-style result against an abstract
   broken-copy spec), an abstract-system liveness argument, then transfer
   via `Semantics.LTL.WBisimInvariant`. Sizing that campaign is future work.

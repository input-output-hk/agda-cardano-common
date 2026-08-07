{-# OPTIONS --guardedness #-}

-- ONE-WAY coinductive characterisation of failures-divergences refinement.
--
-- `FSim R t₁ t₂` reads "the SPECIFICATION t₂ failure-simulates the IMPLEMENTATION t₁",
-- following the orientation of `Semantics.WeakSim`'s `WSim` (every t₁ step is matched
-- by a weak t₂ step), so the headline theorem is `fsim→⊑FD : FSim R Q P → P ⊑FD Q`.
--
-- Compared with `Semantics.DRImpliesFD.drbisim→⊑FD`, which consumes all four `DRbisim`
-- fields, this needs only the FORWARD simulation, ONE divergence direction, and a
-- per-state stability condition.  The `bwd` / `div←` halves of a `DRbisim` are dead
-- weight for a refinement, and providing them forces the abstract side of a proof to
-- be reflected back through the whole operator stack.
--
-- The module is POSTULATE-FREE.  In particular it does NOT go through
-- `¬-divergent→normal` (the single classical postulate of `Semantics.DRImpliesFD`):
-- the `stab` field *produces* a stable specification witness rather than merely
-- asserting the specification converges, which is exactly what removes the need to
-- classically normalise.  As a consequence this module must not — and does not —
-- import `Semantics.DRImpliesFD` or anything supplying `dne`.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module Semantics.FailureSim {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS                 {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakBisim           {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakSim             {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Stability           {ℓ} {ℓe} {ℓi} {E} {I} using (stable-not-sil)
open import Semantics.Refusals            {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Failures            {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.FailuresDivergences {ℓ} {ℓe} {ℓi} {E} {I}
  using (IsDivergence; divergences; failures⊥; _⊑F⊥_; _⊑D_; _⊑FD_)

-------------------------------------------------------------------------------------
-- The record.
-------------------------------------------------------------------------------------

-- t₂ (the spec) failure-simulates t₁ (the impl)
record FSim {ℓr} (R : Set ℓr) (t₁ t₂ : PTree E I R)
          : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    fwd  : WSimF (FSim R) t₁ t₂

    -- whenever the impl is stable, the spec can silently settle into a stable
    -- state whose offers are contained in the impl's offers.  The inclusion runs
    -- spec-offers ⊆ impl-offers (NOT the reverse): to carry a refusal from the impl
    -- to the spec one must refute `Offers t₂′ e`, and semantically the spec is the
    -- more nondeterministic process, so once settled it offers no more than the impl.
    stab : isStable t₁
         → Σ[ t₂′ ∈ PTree E I R ]
             ( t₂ ─[τ*]─► t₂′
             × isStable t₂′
             × (∀ (e : Event√ R) → Offers t₂′ e → Offers t₁ e) )

    -- only the impl→spec divergence direction is needed; that is what ⊑D consumes
    div→ : Diverges t₁ → Diverges t₂
open FSim public

-------------------------------------------------------------------------------------
-- FSimF: a `div→`-FREE failure simulation.
--
-- `_⊑F_` (`Semantics.Failures`) is divergence-BLIND — a `⊑F` fact is a statement about
-- STABLE failures only, and `fsim→⊑F` below (read it) never once projects `.FSim.div→`.
-- So a caller who only wants a `⊑F` consequence is nonetheless forced, by `FSim`'s
-- type, to discharge `div→ : Diverges t₁ → Diverges t₂` — and when `t₁` is a large
-- composite (e.g. a hidden multi-node network), that is a WHOLE-COMPOSITE divergence
-- obligation, exactly the cost a `⊑F`-only campaign is trying to avoid.
--
-- `FSimF` is `FSim` with `div→` simply removed: same `fwd`/`stab` fields, same types.
-- `fsim→fsimF` forgets the (unused) field so every existing `FSim` witness still
-- yields a `⊑F` fact via `fsimF→⊑F`, and no existing `FSim`-producing proof is disturbed.
-------------------------------------------------------------------------------------

-- t₂ (the spec) failure-simulates t₁ (the impl), WITHOUT a divergence obligation
record FSimF {ℓr} (R : Set ℓr) (t₁ t₂ : PTree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    fwd  : WSimF (FSimF R) t₁ t₂

    -- identical to `FSim.stab` (see above for the direction-of-inclusion rationale)
    stab : isStable t₁
         → Σ[ t₂′ ∈ PTree E I R ]
             ( t₂ ─[τ*]─► t₂′
             × isStable t₂′
             × (∀ (e : Event√ R) → Offers t₂′ e → Offers t₁ e) )
open FSimF public

-- the forgetful map: every `FSim` witness is in particular an `FSimF` witness once
-- `div→` is dropped, so no existing `FSim`-producing proof needs to change
fsim→fsimF : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → FSim R t₁ t₂ → FSimF R t₁ t₂
fsim→fsimF sim .FSimF.fwd .WSimF.on-ev  step with sim .FSim.fwd .WSimF.on-ev  step
... | Y , w , rel = Y , w , fsim→fsimF rel
fsim→fsimF sim .FSimF.fwd .WSimF.on-tau step with sim .FSim.fwd .WSimF.on-tau step
... | Y , w , rel = Y , w , fsim→fsimF rel
fsim→fsimF sim .FSimF.stab st = sim .FSim.stab st

-------------------------------------------------------------------------------------
-- Big-step replay (the FSim/FSimF analogue of `wsim-trace-sim` / `dr-trace-sim`).
-------------------------------------------------------------------------------------

-- a failure-simulated process's big-step trace is replayed move-by-move
fsim-trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s}
               → FSim R P Q → P ⟹⟨ s ⟩ P′
               → Σ[ Q′ ∈ PTree E I R ] (Q ⟹⟨ s ⟩ Q′ × FSim R P′ Q′)
fsim-trace-sim p≲q ⟹-refl = _ , ⟹-refl , p≲q
fsim-trace-sim p≲q (⟹-τ pτ rest)  with p≲q .FSim.fwd .WSimF.on-tau pτ
... | _ , qτ , p₁≲q₁ with fsim-trace-sim p₁≲q₁ rest
...   | Q′ , q⟹ , p′≲q′ = Q′ , weaken-τ qτ q⟹ , p′≲q′
fsim-trace-sim p≲q (⟹-ev pev rest) with p≲q .FSim.fwd .WSimF.on-ev pev
... | _ , qev , p₁≲q₁ with fsim-trace-sim p₁≲q₁ rest
...   | Q′ , q⟹ , p′≲q′ = Q′ , weaken-ev qev q⟹ , p′≲q′

-- the FSimF analogue of `fsim-trace-sim`: a div→-free failure-simulated process's
-- big-step trace is replayed move-by-move (only `fwd` is ever consulted)
fsimF-trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s}
               → FSimF R P Q → P ⟹⟨ s ⟩ P′
               → Σ[ Q′ ∈ PTree E I R ] (Q ⟹⟨ s ⟩ Q′ × FSimF R P′ Q′)
fsimF-trace-sim p≲q ⟹-refl = _ , ⟹-refl , p≲q
fsimF-trace-sim p≲q (⟹-τ pτ rest)  with p≲q .FSimF.fwd .WSimF.on-tau pτ
... | _ , qτ , p₁≲q₁ with fsimF-trace-sim p₁≲q₁ rest
...   | Q′ , q⟹ , p′≲q′ = Q′ , weaken-τ qτ q⟹ , p′≲q′
fsimF-trace-sim p≲q (⟹-ev pev rest) with p≲q .FSimF.fwd .WSimF.on-ev pev
... | _ , qev , p₁≲q₁ with fsimF-trace-sim p₁≲q₁ rest
...   | Q′ , q⟹ , p′≲q′ = Q′ , weaken-ev qev q⟹ , p′≲q′

-------------------------------------------------------------------------------------
-- Forgetting the failure data leaves a plain weak simulation, hence trace refinement.
-------------------------------------------------------------------------------------

-- drop `stab` and `div→`: a failure simulation is in particular a weak simulation
fsim→wsim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → FSim R t₁ t₂ → WSim R t₁ t₂
fsim→wsim sim .WSim.fwd .WSimF.on-ev  s with sim .FSim.fwd .WSimF.on-ev  s
... | _ , w , rel = _ , w , fsim→wsim rel
fsim→wsim sim .WSim.fwd .WSimF.on-tau s with sim .FSim.fwd .WSimF.on-tau s
... | _ , w , rel = _ , w , fsim→wsim rel

-- trace refinement, via the weak simulation
fsim→⊑T : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑T Q
fsim→⊑T sim = wsim→⊑T (fsim→wsim sim)

-------------------------------------------------------------------------------------
-- The bridge to the FD model.  Unlike `drbisim→⊑F⊥` this uses no classical principle:
-- no `¬-divergent→normal`, no `stable-≉-ret` case, no `dr-absorb-τ*`, no `⊥-elim`.
-- The `ret` case simply cannot arise, because `stab` hands back a STABLE witness and
-- a `ret` state is never stable.  (If a spec must terminate where the impl stalls,
-- `stab` is unprovable — that is the correct outcome, not a gap.)
-------------------------------------------------------------------------------------

-- divergences are respected: replay the divergence prefix, then apply div→
fsim→⊑D : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑D Q
fsim→⊑D sim d with fsim-trace-sim sim (d .IsDivergence.reach)
... | Pw , p⟹ , simw = record
        { prefix  = d .IsDivergence.prefix
        ; suffix  = d .IsDivergence.suffix
        ; split   = d .IsDivergence.split
        ; witness = Pw
        ; reach   = p⟹
        ; divwit  = simw .FSim.div→ (d .IsDivergence.divwit)
        }

-- stable (divergence-FREE) failures are respected by an FSimF: replay the spec's
-- failing trace against the impl, settle the impl with `stab`, and compose the offer
-- inclusion with the spec's refusal.  No `div→` obligation is ever consulted here —
-- this is exactly `fsim→⊑F`'s ORIGINAL proof, now stated over the smaller record.
fsimF→⊑F : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSimF R Q P → P ⊑F Q
fsimF→⊑F sim s X (Qw , q⟹ , stQw , norefuse)
  with fsimF-trace-sim sim q⟹
... | Pw , p⟹ , simw with simw .FSimF.stab stQw
...   | Pw′ , pw→pw′ , stPw′ , incl =
        Pw′ , ⟹-then-τ* p⟹ pw→pw′ , stPw′ , λ e Be off → norefuse e Be (incl e off)

-- stable (divergence-FREE) failures are respected: this is the `inj₁` branch of
-- `fsim→⊑F⊥` below, extracted so a caller with no divergence-strictness need (e.g. a
-- plain `⊑F` fact) does not have to go through the `⊎` wrapper of `⊑F⊥`.  Derived from
-- `fsimF→⊑F` by forgetting the (unused) `div→` field first — `fsim→⊑F` never touches
-- `div→`, so this is a pure transcription, not a new proof.
fsim→⊑F : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑F Q
fsim→⊑F sim = fsimF→⊑F (fsim→fsimF sim)

-- divergence-strict failures are respected: the `inj₂` disjunct is `fsim→⊑D`, the
-- `inj₁` disjunct is exactly `fsim→⊑F` above
fsim→⊑F⊥ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑F⊥ Q
fsim→⊑F⊥ sim (inj₂ dQ) = inj₂ (fsim→⊑D sim dQ)
fsim→⊑F⊥ sim (inj₁ f)  = inj₁ (fsim→⊑F sim _ _ f)

-- the headline theorem: a one-way failure simulation gives ⊑FD
fsim→⊑FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑FD Q
fsim→⊑FD sim = fsim→⊑F⊥ sim , fsim→⊑D sim

-------------------------------------------------------------------------------------
-- FSim is a preorder.  Reflexivity is immediate; transitivity needs FSim-specific
-- weak-step lifting lemmas (`fsim-τ*-sim` / `fsim-wev-sim`) because `τ*-sim`,
-- `wev-sim` and `w-sim-trans` in `Semantics.WeakBisim` are hard-coded to `Wbisim`
-- (they project `.Wbisim.fwd`) and `Semantics.WeakSim` has no `wsim-trans` to borrow.
-------------------------------------------------------------------------------------

-- reflexivity: each step is matched by itself, and a stable state settles at itself
f-sim-refl : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → WSimF (FSim R) t t
fsim-refl  : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → FSim R t t
f-sim-refl t .WSimF.on-ev  step = _ , wev τ*-refl step τ*-refl , fsim-refl _
f-sim-refl t .WSimF.on-tau step = _ , wτ (τ*-step step τ*-refl) , fsim-refl _
fsim-refl t .FSim.fwd      = f-sim-refl t
fsim-refl t .FSim.stab  st = t , τ*-refl , st , λ _ off → off
fsim-refl t .FSim.div→  d  = d

-- a τ* run of Q is matched by a τ* run of any S that failure-simulates Q
fsim-τ*-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R}
            → Q ─[τ*]─► Q′ → FSim R Q S
            → Σ[ S′ ∈ PTree E I R ] (S ─[τ*]─► S′ × FSim R Q′ S′)
fsim-τ*-sim τ*-refl           q≲s = _ , τ*-refl , q≲s
fsim-τ*-sim (τ*-step qτ rest) q≲s with q≲s .FSim.fwd .WSimF.on-tau qτ
... | _ , wτ s→s₁ , q₁≲s₁ with fsim-τ*-sim rest q₁≲s₁
...   | S′ , s₁→s′ , q′≲s′ = S′ , τ*-trans s→s₁ s₁→s′ , q′≲s′

-- a weak visible run of Q is matched by a weak visible run of S
fsim-wev-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R} {l : Event√ R}
             → Q ═[ ev l ]═► Q′ → FSim R Q S
             → Σ[ S′ ∈ PTree E I R ] (S ═[ ev l ]═► S′ × FSim R Q′ S′)
fsim-wev-sim (wev q→q₁ q₁ev q₂→q′) q≲s with fsim-τ*-sim q→q₁ q≲s
... | _ , s→s₁ , q₁≲s₁ with q₁≲s₁ .FSim.fwd .WSimF.on-ev q₁ev
...   | _ , wev s₁→m mev n→s₂ , q₂≲s₂ with fsim-τ*-sim q₂→q′ q₂≲s₂
...     | S′ , s₂→s′ , q′≲s′ =
          S′ , wev (τ*-trans s→s₁ s₁→m) mev (τ*-trans n→s₂ s₂→s′) , q′≲s′

-- composing a single-step simulation P→Q with a failure simulation Q≲S.  Stated as a
-- transformation on `WSimF`s (mirroring `w-sim-trans`) via forward declarations rather
-- than a mutual block, so the corecursive `fsim-trans` sits under the Σ-result of the
-- simulation and stays guarded.
f-sim-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
            → WSimF (FSim R) P Q → FSim R Q S → WSimF (FSim R) P S
fsim-trans  : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ t₃ : PTree E I R}
            → FSim R t₁ t₂ → FSim R t₂ t₃ → FSim R t₁ t₃

f-sim-trans p→q q≲s .WSimF.on-ev pev with p→q .WSimF.on-ev pev
... | _ , q-weak , p′≲q′ with fsim-wev-sim q-weak q≲s
...   | S′ , s-weak , q′≲s′ = S′ , s-weak , fsim-trans p′≲q′ q′≲s′
f-sim-trans p→q q≲s .WSimF.on-tau pτ with p→q .WSimF.on-tau pτ
... | _ , wτ q→q′ , p′≲q′ with fsim-τ*-sim q→q′ q≲s
...   | S′ , s→s′ , q′≲s′ = S′ , wτ s→s′ , fsim-trans p′≲q′ q′≲s′

fsim-trans p≲q q≲s .FSim.fwd = f-sim-trans (p≲q .FSim.fwd) q≲s
-- settle t₂ with the first sim, push the second sim along that τ*-run, settle t₃ with
-- it, then compose the two τ*-runs and the two offer inclusions
fsim-trans p≲q q≲s .FSim.stab st₁ with p≲q .FSim.stab st₁
... | t₂′ , t₂→t₂′ , st₂′ , incl₂ with fsim-τ*-sim t₂→t₂′ q≲s
...   | t₃′ , t₃→t₃′ , q′≲s′ with q′≲s′ .FSim.stab st₂′
...     | t₃″ , t₃′→t₃″ , st₃″ , incl₃ =
          t₃″ , τ*-trans t₃→t₃′ t₃′→t₃″ , st₃″ , λ e off → incl₂ e (incl₃ e off)
fsim-trans p≲q q≲s .FSim.div→ d = q≲s .FSim.div→ (p≲q .FSim.div→ d)

-------------------------------------------------------------------------------------
-- "The spec may be lazy": a failure simulation survives PREPENDING τ-steps to the
-- SPEC side.  Every field is closed under prepending because each one only ever
-- *produces* a τ*-run out of the spec (or a divergence of it), never consumes one.
-------------------------------------------------------------------------------------

-- prefixing finitely many τ's to an infinite τ-chain leaves it infinite.  Stated
-- generically here (the CSP-layer copies `CSP.Laws.FSim.BindCong.div-prepend-τ*` and
-- `CSP.Laws.FD.InterruptFD.τ*-Diverges` sit downstream and cannot be imported).
div-prepend-τ* : ∀ {ℓr} {R : Set ℓr} {t u : PTree E I R}
               → t ─[τ*]─► u → Diverges u → Diverges t
div-prepend-τ* τ*-refl           d = d
div-prepend-τ* (τ*-step st rest) d .Diverges.next = _
div-prepend-τ* (τ*-step st rest) d .Diverges.step = st
div-prepend-τ* (τ*-step st rest) d .Diverges.rest = div-prepend-τ* rest d

-- if the spec can silently reach t₂′ and t₂′ failure-simulates t₁, then t₂ already
-- does: glue the given run in front of every weak run / stability run the simulation
-- at t₂′ hands back (same residuals, so no corecursion is needed), and prepend it to
-- the divergence with `div-prepend-τ*`
fsim-τ*-prepend : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ t₂′ : PTree E I R}
                → t₂ ─[τ*]─► t₂′ → FSim R t₁ t₂′ → FSim R t₁ t₂
fsim-τ*-prepend run sim .FSim.fwd .WSimF.on-ev  s with sim .FSim.fwd .WSimF.on-ev s
... | Y , wev pre stp post , rel = Y , wev (τ*-trans run pre) stp post , rel
fsim-τ*-prepend run sim .FSim.fwd .WSimF.on-tau s with sim .FSim.fwd .WSimF.on-tau s
... | Y , wτ run′ , rel = Y , wτ (τ*-trans run run′) , rel
fsim-τ*-prepend run sim .FSim.stab st with sim .FSim.stab st
... | t₂″ , run′ , st″ , incl = t₂″ , τ*-trans run run′ , st″ , incl
fsim-τ*-prepend run sim .FSim.div→ d = div-prepend-τ* run (sim .FSim.div→ d)

-------------------------------------------------------------------------------------
-- The converse direction for a SINGLE `sil` node: a simulation by a `sil`-headed spec
-- FACTORS THROUGH that node's unique τ-successor.  Where `fsim-τ*-prepend` makes the
-- spec lazier, this makes it eager: every matching run the spec can offer out of a
-- `sil` node must take that node's only τ first, so nothing is lost by starting at the
-- successor.  Together the two say a spec's leading `sil` is FSim-invisible.
--
-- The one delicate case is `fwd.on-tau` when the spec matched with the EMPTY τ-run
-- (the spec stood still at the `sil` node): there is no run to peel, so the residual
-- obligation is the lemma itself at the same spec state.  It is discharged by guarded
-- CORECURSION — the call sits under the coinductive `FSim.fwd` projection, exactly as
-- `f-sim-trans`/`fsim-trans` do — with the empty run `τ*-refl` out of the successor.
-------------------------------------------------------------------------------------

-- a `sil` node performs no VISIBLE step (`sRet`/`sVis` both contradict the force eq)
sil-no-ev : ∀ {ℓr} {R : Set ℓr} {t u t′ : PTree E I R} {l : Event√ R}
          → PTree.force t ≡ sil u → t ─[ ev l ]─► t′ → ⊥
sil-no-ev eq (sRet req)    with trans (sym req) eq
... | ()
sil-no-ev eq (sVis reqf _) with trans (sym reqf) eq
... | ()

-- a τ*-run out of a `sil` node either stands still or factors through the unique
-- successor: the first τ, if any, can only be the `sil` step itself
sil-τ*-split : ∀ {ℓr} {R : Set ℓr} {t u m : PTree E I R}
             → PTree.force t ≡ sil u → t ─[τ*]─► m → (t ≡ m) ⊎ (u ─[τ*]─► m)
sil-τ*-split eq τ*-refl                = inj₁ refl
sil-τ*-split eq (τ*-step (sSil sileq)  rest) with trans (sym sileq) eq
... | refl = inj₂ rest
sil-τ*-split eq (τ*-step (sTau reqf _) rest) with trans (sym reqf) eq
... | ()

-- an infinite τ-run out of a `sil` node continues out of its unique successor
sil-div-factor : ∀ {ℓr} {R : Set ℓr} {t u : PTree E I R}
               → PTree.force t ≡ sil u → Diverges t → Diverges u
sil-div-factor {t = t} {u = u} eq d = go (d .Diverges.step) (d .Diverges.rest)
  where
    -- the diverging first step lands on `u`, so its tail is already a `Diverges u`
    go : ∀ {w} → t ─[ τ ]─► w → Diverges w → Diverges u
    go (sSil sileq)  r with trans (sym sileq) eq
    ... | refl = r
    go (sTau reqf _) r with trans (sym reqf) eq
    ... | ()

-- the factoring lemma, split into its `WSimF` half and the record half (forward
-- declarations rather than a `mutual` block, matching `f-sim-trans`/`fsim-trans`)
f-sim-sil-factor : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ t₂′ : PTree E I R}
                 → PTree.force t₂ ≡ sil t₂′ → FSim R t₁ t₂ → WSimF (FSim R) t₁ t₂′
fsim-sil-factor  : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ t₂′ : PTree E I R}
                 → PTree.force t₂ ≡ sil t₂′ → FSim R t₁ t₂ → FSim R t₁ t₂′

-- a visible match cannot have an empty leading τ-run (a `sil` node offers no event),
-- so the run's tail already starts at the successor
f-sim-sil-factor eq sim .WSimF.on-ev step with sim .FSim.fwd .WSimF.on-ev step
... | Y , wev pre stp post , rel with sil-τ*-split eq pre
...   | inj₁ refl = ⊥-elim (sil-no-ev eq stp)
...   | inj₂ pre′ = Y , wev pre′ stp post , rel
-- a τ-match either already passed the `sil` (peel it) or stood still (corecurse)
f-sim-sil-factor {t₂′ = t₂′} eq sim .WSimF.on-tau step
  with sim .FSim.fwd .WSimF.on-tau step
... | Y , wτ run , rel with sil-τ*-split eq run
...   | inj₁ refl = t₂′ , wτ τ*-refl , fsim-sil-factor eq rel
...   | inj₂ run′ = Y , wτ run′ , rel

fsim-sil-factor eq sim .FSim.fwd = f-sim-sil-factor eq sim
-- the settling run cannot be empty either: a `sil` node is not stable
fsim-sil-factor {t₂ = t₂} eq sim .FSim.stab st with sim .FSim.stab st
... | w , run , stw , incl with sil-τ*-split eq run
...   | inj₁ refl = ⊥-elim (stable-not-sil {t = t₂} stw eq)
...   | inj₂ run′ = w , run′ , stw , incl
fsim-sil-factor eq sim .FSim.div→ d = sil-div-factor eq (sim .FSim.div→ d)

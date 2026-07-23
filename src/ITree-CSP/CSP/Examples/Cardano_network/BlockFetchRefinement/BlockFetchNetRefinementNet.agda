{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Task 4 (network), part 2: `net-noDiv` — the hidden network process
-- `networkBF ∖ ioBF` is divergence-free.  This module adds the 106-node
-- coinductive `Good` graph over the reachable joint configs (the τ-inversion
-- `net*-τ` and `nd-*` convergence layer live in `BlockFetchNetRefinement`),
-- the initial node `gNetInit`, and `net-noDiv = go-reach gNetInit`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.BlockFetchRefinement.BlockFetchNetRefinementNet (p : Params) where

open import Level using (lift) renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Maybe using (Maybe; just; nothing)

open import Process_Trees

open import CSP.Examples.Cardano_network.BlockFetch p

-- API tags + carried payload types, needed for the JN-gevA result and the
-- impossible-jeBoth refuter.
open import CSP.Examples.Cardano_network.Net p
  using ( ApiBFTag; ApiBFCar; recvBFBlock )

open import Semantics.LTS {E = BFNetEv} {I = ExtI BFNetEv} hiding (Diverges)
open import Semantics.DRBisim {E = BFNetEv} {I = ExtI BFNetEv} using (Diverges)
open import Semantics.Failures {E = BFNetEv} {I = ExtI BFNetEv}
  using (_⟹⟨_⟩_)

open NetOps using (_∖_; Par; iter; _⦀_; _∥⇘_⇙_; ∅ES; EventSet)

-- everything from part 1: JN / Inner / the peer-state terms / the decomposers
-- (JN-τ-cases, JN-gev, JN-gev-none), the net*-τ inversions, and the nd-* layer.
open import CSP.Examples.Cardano_network.BlockFetchRefinement.BlockFetchNetRefinement p

-- bring the coinductive `Good` projections (gnd / gτ / gev) into scope for copatterns.
open Good

-- the hide / parallel single-step inversions, at the network alphabet (same as part 1).
open import CSP.Laws.Traces.TraceLawsHide BFNetEv-≟
  using (Hide-ev-elim; heV; he√)
open import CSP.Laws.Traces.TraceLawsParallelElim BFNetEv-≟
  using (Par-ev-elim; evSync; evL; evR; evBoth)

-- a generic-event JN visible router: a surviving visible step at ANY label `e`
-- is in fact a peer-solo apiBF (the copy's events ∈ ioBF are hidden; peers offer
-- no bfMsg; bfIn/bfOut are hidden).  Returns the `JNev` classification so each
-- apiBF-offering node can route on it.  (`JN-gev` of part 1 needs the apiBF label
-- up front; `Good.gev` only gives a generic `e`, so we invert the hide here.)
JN-gevA : ∀ {cl sv cp} {W″ : PTree BFNetEv (ExtI BFNetEv) Rr} {e : Event√ Rr}
        → (∀ {X} {ee : BFNetEv X} {a Q'} → cp ─[ ev (evl (record { A = X ; e = ee ; a = a })) ]─► Q' → ioBF .EventSet.mem (X , ee) a)
        → (∀ {a P'} → cl ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥)
        → (∀ {a Q'} → sv ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥)
        → (∀ {a Q'} → cp ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥)
        → (∀ {r} → PTree.force (NetOps.Par ioBF mrg2 (Inner cl sv) cp) ≡ ret r → ⊥)
        → JN (Inner cl sv) cp ─[ ev e ]─► W″
        → Σ[ m ∈ ApiBFTag ] Σ[ a ∈ ApiBFCar m ] JNev cl sv cp a (apiBF m) W″
JN-gevA {cl} {sv} {cp} cpMem clNoM svNoM cpNoM noRet st
  with Hide-ev-elim ioBF (NetOps.Par ioBF mrg2 (Inner cl sv) cp) st
... | he√ eqf = ⊥-elim (noRet eqf)
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg clNoM svNoM cpNoM pev)
... | heV {e = bfIn}  P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} {a = a} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner cl sv) cp pev
...   | evSync mm cstp sstp = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (¬m (cpMem cst))
...   | evBoth ¬m2 ist cst = ⊥-elim (¬m (cpMem cst))
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg cl sv ist
...     | evL ¬m3 clst = m , a , jeClL clst
...     | evR ¬m3 svst = m , a , jeSvR svst
...     | evBoth ¬m3 clst svst = m , a , jeBoth clst svst

-- ISn stStreaming offers no recvBFBlock apiBF (used to refute the impossible
-- jeBoth branch where client and server would fire the same apiBF).
ISstr-no-recv : ∀ {a Q''} → ISn stStreaming ─[ ev (evl (record { A = ApiBFCar recvBFBlock ; e = apiBF recvBFBlock ; a = a })) ]─► Q'' → ⊥
ISstr-no-recv (sVis refl ())

-- forward declarations of all 106 Good nodes (mutually corecursive).

gA : Good (JN (Inner (ICn stIdle) (ISn stIdle)) Cidle)
gB : ∀ {r} → Good (JN (Inner (CB-req r) (ISn stIdle)) Cidle)
gB2 : ∀ {r} → Good (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)))
gB3 : ∀ {r} → Good (JN (Inner (CB-loop stBusy) (SB-req r)) Cret)
gB3a : ∀ {r} → Good (JN (Inner (ICn stBusy) (SB-req r)) Cret)
gB4 : ∀ {r} → Good (JN (Inner (ICn stBusy) (SB-req r)) Cidle)
gB5 : ∀ {r} → Good (JN (Inner (CB-loop stBusy) (SB-req r)) Cidle)
gBD0a : Good (JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone))
gBD0e : Good (JN (Inner (ICn stStreaming) SB-bdone) Cidle)
gBD0h : Good (JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone))
gBD1a : ∀ {b₀} → Good (JN (Inner (CB-blk b₀) (ISn stIdle)) (Chold mBatchDone))
gBD1d : Good (JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone))
gBD1e : ∀ {b₀} → Good (JN (Inner (CB-blk b₀) SB-bdone) Cidle)
gBD1h : ∀ {b₀} → Good (JN (Inner (CB-blk b₀) (SB-loop stIdle)) (Chold mBatchDone))
gBD2a : ∀ {b₁} → Good (JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b₁)))
gBD2b : ∀ {b₁} → Good (JN (Inner (CB-blk b₁) SB-bdone) Cret)
gBD2d : ∀ {b₁} → Good (JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b₁)))
gBD2e : ∀ {b₀ b₁} → Good (JN (Inner (CB-blk b₀) SB-bdone) (Chold (mBlock b₁)))
gBX1 : Good (JN (Inner (CB-loop stStreaming) SB-bdone) Cidle)
gBX2 : Good (JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone))
gBX3 : Good (JN (Inner (CB-loop stStreaming) SB-bdone) Cret)
gBX3a : Good (JN (Inner (ICn stStreaming) SB-bdone) Cret)
gBh : ∀ {r} → Good (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)))
gCd2 : Good (JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone))
gCd3 : Good (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret)
gCd4 : Good (JN (Inner (ICn stDone) (SB-loop stDone)) Cret)
gCd5 : Good (JN (Inner (CB-loop stDone) (ISn stDone)) Cret)
gCd6 : Good (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle)
gCd7 : Good (JN (Inner (ICn stDone) (ISn stDone)) Cret)
gCd8 : Good (JN (Inner (ICn stDone) (SB-loop stDone)) Cidle)
gCd9 : Good (JN (Inner (CB-loop stDone) (ISn stDone)) Cidle)
gCdR : Good (JN (Inner CB-cdone (ISn stIdle)) Cret)
gCdSi : Good (JN (Inner CB-cdone (SB-loop stIdle)) Cidle)
gCdSr : Good (JN (Inner CB-cdone (SB-loop stIdle)) Cret)
gCdh : Good (JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone))
gCdone : Good (JN (Inner CB-cdone (ISn stIdle)) Cidle)
gFl : Good (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle)
gG3 : Good (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret)
gG3a : Good (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret)
gG5 : Good (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret)
gG6 : Good (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle)
gG7 : Good (JN (Inner (ICn stBusy) (ISn stBusy)) Cret)
gI : Good (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle)
gIBMr : Good (JN (Inner (ICn stBusy) SB-sbatch) Cret)
gIBNr : Good (JN (Inner (ICn stBusy) SB-noblk) Cret)
gIBSirr : ∀ {r} → Good (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)))
gIBbdsb : Good (JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch))
gIBblksb : ∀ {b} → Good (JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch))
gIDScd : Good (JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone))
gJ : Good (JN (Inner (ICn stBusy) (ISn stBusy)) Cidle)
gLbBDsb : Good (JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch))
gLbBLKsb : ∀ {b} → Good (JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch))
gLbBh : ∀ {r} → Good (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)))
gLbM2 : Good (JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch))
gLbMh : Good (JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch))
gLbMi : Good (JN (Inner (CB-loop stBusy) SB-sbatch) Cidle)
gLbMr : Good (JN (Inner (CB-loop stBusy) SB-sbatch) Cret)
gLbN2 : Good (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks))
gLbNh : Good (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks))
gLbNi : Good (JN (Inner (CB-loop stBusy) SB-noblk) Cidle)
gLbNr : Good (JN (Inner (CB-loop stBusy) SB-noblk) Cret)
gLdCdh : Good (JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone))
gM : Good (JN (Inner (ICn stBusy) SB-sbatch) Cidle)
gM2 : Good (JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch))
gM3 : Good (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret)
gM4 : Good (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret)
gM5 : Good (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret)
gM6 : Good (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle)
gM7 : Good (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret)
gM8 : Good (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle)
gM9 : Good (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle)
gMh : Good (JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch))
gN : Good (JN (Inner (ICn stBusy) SB-noblk) Cidle)
gN2 : Good (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks))
gN3 : Good (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret)
gN4 : Good (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret)
gN5 : Good (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret)
gN6 : Good (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle)
gN7 : Good (JN (Inner (ICn stIdle) (ISn stIdle)) Cret)
gN8 : Good (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle)
gN9 : Good (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle)
gNh : Good (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks))
gReqR : ∀ {r} → Good (JN (Inner (CB-req r) (ISn stIdle)) Cret)
gReqSi : ∀ {r} → Good (JN (Inner (CB-req r) (SB-loop stIdle)) Cidle)
gReqSr : ∀ {r} → Good (JN (Inner (CB-req r) (SB-loop stIdle)) Cret)
gV0 : Good (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle)
gVocc1 : ∀ {b} → Good (JN (Inner (CB-blk b) (ISn stStreaming)) Cidle)
gW : ∀ {b} → Good (JN (Inner (ICn stStreaming) (SB-blk b)) Cidle)
gW2 : ∀ {b} → Good (JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)))
gW2a : ∀ {b₀ b₁} → Good (JN (Inner (CB-blk b₀) (ISn stStreaming)) (Chold (mBlock b₁)))
gW2d : ∀ {b₁} → Good (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b₁)))
gW2e : ∀ {b₀ b₁} → Good (JN (Inner (CB-blk b₀) (SB-blk b₁)) Cidle)
gW2h : ∀ {b₀ b₁} → Good (JN (Inner (CB-blk b₀) (SB-loop stStreaming)) (Chold (mBlock b₁)))
gW3 : ∀ {b} → Good (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret)
gW3a : ∀ {b₁ b₂} → Good (JN (Inner (ICn stStreaming) (SB-blk b₂)) (Chold (mBlock b₁)))
gW3b : ∀ {b₁ b₂} → Good (JN (Inner (CB-blk b₁) (SB-blk b₂)) Cret)
gW3d : ∀ {b₁ b₂} → Good (JN (Inner (CB-loop stStreaming) (SB-blk b₂)) (Chold (mBlock b₁)))
gW3e : ∀ {b₀ b₁ b₂} → Good (JN (Inner (CB-blk b₀) (SB-blk b₂)) (Chold (mBlock b₁)))
gW4 : ∀ {b} → Good (JN (Inner (CB-blk b) (ISn stStreaming)) Cret)
gW5 : ∀ {b} → Good (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle)
gWX1 : ∀ {b₁} → Good (JN (Inner (CB-loop stStreaming) (SB-blk b₁)) Cidle)
gWX2 : ∀ {b₁} → Good (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b₁)))
gWX3 : ∀ {b₂} → Good (JN (Inner (CB-loop stStreaming) (SB-blk b₂)) Cret)
gWX3a : ∀ {b₂} → Good (JN (Inner (ICn stStreaming) (SB-blk b₂)) Cret)
gWh : ∀ {b} → Good (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)))
gZ : Good (JN (Inner (ICn stDone) (ISn stDone)) Cidle)

-- node definitions.

gA .gnd = nd-A
gA .gτ st = ⊥-elim (netA-noτ st)
gA .gev st with JN-gevA Cidle-mem ICn-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with ICidle-api clst
...     | inj₁ (r , refl , refl) = gB
...     | inj₂ (refl , refl) = gCdone
gA .gev st | _ , _ , jeSvR svst = ⊥-elim (ISidle-no-api svst)
gA .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ISidle-no-api svst)

gB .gnd = nd-B
gB {r} .gτ st with netB-τ st
... | refl = gBh
gB {r} .gev st = ⊥-elim (JN-gev-none CBreq-no-api ISidle-no-api CBreq-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gB2 .gnd = nd-B2
gB2 {r} .gτ st with netB2-τ st
... | refl = gB3a
gB2 {r} .gev st = ⊥-elim (JN-gev-none ICbusy-no-api ISidle-no-api ICn-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gB3 .gnd = nd-B3
gB3 {r} .gτ st with netB3-τ st
... | inj₁ eq = subst Good (sym eq) gB3a
... | inj₂ eq = subst Good (sym eq) gB5
gB3 {r} .gev st with JN-gevA Cret-mem CBloop-no-bfMsg SBreq-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (CBloop-no-ev clst)
gB3 {r} .gev st | _ , _ , jeSvR svst with SBreq-api svst
...     | (refl , refl) = gG3
gB3 {r} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (CBloop-no-ev clst)

gB3a .gnd = nd-B3a
gB3a {r} .gτ st with netB3a-τ st
... | refl = gB4
gB3a {r} .gev st with JN-gevA Cret-mem ICn-no-bfMsg SBreq-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (ICbusy-no-api clst)
gB3a {r} .gev st | _ , _ , jeSvR svst with SBreq-api svst
...     | (refl , refl) = gG3a
gB3a {r} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ICbusy-no-api clst)

gB4 .gnd = nd-B4
gB4 {r} .gτ st = ⊥-elim (netB4-noτ st)
gB4 {r} .gev st with JN-gevA Cidle-mem ICn-no-bfMsg SBreq-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (ICbusy-no-api clst)
gB4 {r} .gev st | _ , _ , jeSvR svst with SBreq-api svst
...     | (refl , refl) = gFl
gB4 {r} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ICbusy-no-api clst)

gB5 .gnd = nd-B5
gB5 {r} .gτ st with netB5-τ st
... | refl = gB4
gB5 {r} .gev st with JN-gevA Cidle-mem CBloop-no-bfMsg SBreq-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (CBloop-no-ev clst)
gB5 {r} .gev st | _ , _ , jeSvR svst with SBreq-api svst
...     | (refl , refl) = gG6
gB5 {r} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (CBloop-no-ev clst)

gBD0a .gnd = nd-BD0a
gBD0a .gτ st with netBD0a-τ st
... | refl = gN5
gBD0a .gev st = ⊥-elim (JN-gev-none ICstr-no-api ISidle-no-api ICn-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gBD0e .gnd = nd-BD0e
gBD0e .gτ st with netBD0e-τ st
... | refl = gBD0h
gBD0e .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBbdone-no-api ICn-no-bfMsg SBbdone-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gBD0h .gnd = nd-BD0h
gBD0h .gτ st with netBD0h-τ st
... | inj₁ eq = subst Good (sym eq) gBD0a
... | inj₂ eq = subst Good (sym eq) gN3
gBD0h .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gBD1a .gnd = nd-BD1a
gBD1a {b₀} .gτ st = ⊥-elim (netBD1a-noτ st)
gBD1a {b₀} .gev st with JN-gevA Chold-mem CBblk-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gBD1d
gBD1a {b₀} .gev st | _ , _ , jeSvR svst = ⊥-elim (ISidle-no-api svst)
gBD1a {b₀} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ISidle-no-api svst)

gBD1d .gnd = nd-BD1d
gBD1d .gτ st with netBD1d-τ st
... | refl = gBD0a
gBD1d .gev st = ⊥-elim (JN-gev-none CBloop-no-ev ISidle-no-api CBloop-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gBD1e .gnd = nd-BD1e
gBD1e {b₀} .gτ st with netBD1e-τ st
... | refl = gBD1h
gBD1e {b₀} .gev st with JN-gevA Cidle-mem CBblk-no-bfMsg SBbdone-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gBX1
gBD1e {b₀} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBbdone-no-api svst)
gBD1e {b₀} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBbdone-no-api svst)

gBD1h .gnd = nd-BD1h
gBD1h {b₀} .gτ st with netBD1h-τ st
... | refl = gBD1a
gBD1h {b₀} .gev st with JN-gevA Chold-mem CBblk-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gBX2
gBD1h {b₀} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBloop-no-ev svst)
gBD1h {b₀} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBloop-no-ev svst)

gBD2a .gnd = nd-BD2a
gBD2a {b₁} .gτ st with netBD2a-τ st
... | refl = gBD2b
gBD2a {b₁} .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBbdone-no-api ICn-no-bfMsg SBbdone-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gBD2b .gnd = nd-BD2b
gBD2b {b₁} .gτ st with netBD2b-τ st
... | refl = gBD1e
gBD2b {b₁} .gev st with JN-gevA Cret-mem CBblk-no-bfMsg SBbdone-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gBX3
gBD2b {b₁} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBbdone-no-api svst)
gBD2b {b₁} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBbdone-no-api svst)

gBD2d .gnd = nd-BD2d
gBD2d {b₁} .gτ st with netBD2d-τ st
... | refl = gBD2a
gBD2d {b₁} .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBbdone-no-api CBloop-no-bfMsg SBbdone-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gBD2e .gnd = nd-BD2e
gBD2e {b₀} {b₁} .gτ st = ⊥-elim (netBD2e-noτ st)
gBD2e {b₀} {b₁} .gev st with JN-gevA Chold-mem CBblk-no-bfMsg SBbdone-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gBD2d
gBD2e {b₀} {b₁} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBbdone-no-api svst)
gBD2e {b₀} {b₁} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBbdone-no-api svst)

gBX1 .gnd = nd-BX1
gBX1 .gτ st with netBX1-τ st
... | inj₁ eq = subst Good (sym eq) gBD0e
... | inj₂ eq = subst Good (sym eq) gBX2
gBX1 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBbdone-no-api CBloop-no-bfMsg SBbdone-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gBX2 .gnd = nd-BX2
gBX2 .gτ st with netBX2-τ st
... | inj₁ eq = subst Good (sym eq) gBD0h
... | inj₂ eq = subst Good (sym eq) gBD1d
gBX2 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gBX3 .gnd = nd-BX3
gBX3 .gτ st with netBX3-τ st
... | inj₁ eq = subst Good (sym eq) gBX3a
... | inj₂ eq = subst Good (sym eq) gBX1
gBX3 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBbdone-no-api CBloop-no-bfMsg SBbdone-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gBX3a .gnd = nd-BX3a
gBX3a .gτ st with netBX3a-τ st
... | refl = gBD0e
gBX3a .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBbdone-no-api ICn-no-bfMsg SBbdone-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gBh .gnd = nd-Bh
gBh {r} .gτ st with netBh-τ st
... | inj₁ eq = subst Good (sym eq) gB2
... | inj₂ eq = subst Good (sym eq) gB3
gBh {r} .gev st = ⊥-elim (JN-gev-none CBloop-no-ev ISidle-no-api CBloop-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gCd2 .gnd = nd-Cd2
gCd2 .gτ st with netCd2-τ st
... | refl = gCd4
gCd2 .gev st = ⊥-elim (JN-gev-none ICdone-no-api ISidle-no-api ICn-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gCd3 .gnd = nd-Cd3
gCd3 .gτ st with netCd3-τ st
... | inj₁ eq = subst Good (sym eq) gCd4
... | inj₂ (inj₁ eq) = subst Good (sym eq) gCd5
... | inj₂ (inj₂ eq) = subst Good (sym eq) gCd6
gCd3 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gCd4 .gnd = nd-Cd4
gCd4 .gτ st with netCd4-τ st
... | inj₁ eq = subst Good (sym eq) gCd7
... | inj₂ eq = subst Good (sym eq) gCd8
gCd4 .gev st = ⊥-elim (JN-gev-none ICdone-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gCd5 .gnd = nd-Cd5
gCd5 .gτ st with netCd5-τ st
... | inj₁ eq = subst Good (sym eq) gCd7
... | inj₂ eq = subst Good (sym eq) gCd9
gCd5 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev ISdone-no-api CBloop-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gCd6 .gnd = nd-Cd6
gCd6 .gτ st with netCd6-τ st
... | inj₁ eq = subst Good (sym eq) gCd8
... | inj₂ eq = subst Good (sym eq) gCd9
gCd6 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gCd7 .gnd = nd-Cd7
gCd7 .gτ st with netCd7-τ st
... | refl = gZ
gCd7 .gev st = ⊥-elim (JN-gev-none ICdone-no-api ISdone-no-api ICn-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gCd8 .gnd = nd-Cd8
gCd8 .gτ st with netCd8-τ st
... | refl = gZ
gCd8 .gev st = ⊥-elim (JN-gev-none ICdone-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gCd9 .gnd = nd-Cd9
gCd9 .gτ st with netCd9-τ st
... | refl = gZ
gCd9 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev ISdone-no-api CBloop-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gCdR .gnd = nd-CdR
gCdR .gτ st with netCdR-τ st
... | refl = gCdone
gCdR .gev st = ⊥-elim (JN-gev-none CBcdone-no-api ISidle-no-api CBcdone-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gCdSi .gnd = nd-CdSi
gCdSi .gτ st with netCdSi-τ st
... | inj₁ eq = subst Good (sym eq) gCdone
... | inj₂ eq = subst Good (sym eq) gLdCdh
gCdSi .gev st = ⊥-elim (JN-gev-none CBcdone-no-api SBloop-no-ev CBcdone-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gCdSr .gnd = nd-CdSr
gCdSr .gτ st with netCdSr-τ st
... | inj₁ eq = subst Good (sym eq) gCdR
... | inj₂ eq = subst Good (sym eq) gCdSi
gCdSr .gev st = ⊥-elim (JN-gev-none CBcdone-no-api SBloop-no-ev CBcdone-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gCdh .gnd = nd-Cdh
gCdh .gτ st with netCdh-τ st
... | inj₁ eq = subst Good (sym eq) gCd2
... | inj₂ eq = subst Good (sym eq) gCd3
gCdh .gev st = ⊥-elim (JN-gev-none CBloop-no-ev ISidle-no-api CBloop-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gCdone .gnd = nd-Cdone
gCdone .gτ st with netCdone-τ st
... | refl = gCdh
gCdone .gev st = ⊥-elim (JN-gev-none CBcdone-no-api ISidle-no-api CBcdone-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gFl .gnd = nd-Fl
gFl .gτ st with netFl-τ st
... | refl = gJ
gFl .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gG3 .gnd = nd-G3
gG3 .gτ st with netG3-τ st
... | inj₁ eq = subst Good (sym eq) gG3a
... | inj₂ (inj₁ eq) = subst Good (sym eq) gG5
... | inj₂ (inj₂ eq) = subst Good (sym eq) gG6
gG3 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gG3a .gnd = nd-G3a
gG3a .gτ st with netG3a-τ st
... | inj₁ eq = subst Good (sym eq) gG7
... | inj₂ eq = subst Good (sym eq) gFl
gG3a .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gG5 .gnd = nd-G5
gG5 .gτ st with netG5-τ st
... | inj₁ eq = subst Good (sym eq) gG7
... | inj₂ eq = subst Good (sym eq) gI
gG5 .gev st with JN-gevA Cret-mem CBloop-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (CBloop-no-ev clst)
gG5 .gev st | _ , _ , jeSvR svst with ISbusy-api svst
...     | inj₁ (refl , refl) = gLbMr
...     | inj₂ (refl , refl) = gLbNr
gG5 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (CBloop-no-ev clst)

gG6 .gnd = nd-G6
gG6 .gτ st with netG6-τ st
... | inj₁ eq = subst Good (sym eq) gFl
... | inj₂ eq = subst Good (sym eq) gI
gG6 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gG7 .gnd = nd-G7
gG7 .gτ st with netG7-τ st
... | refl = gJ
gG7 .gev st with JN-gevA Cret-mem ICn-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (ICbusy-no-api clst)
gG7 .gev st | _ , _ , jeSvR svst with ISbusy-api svst
...     | inj₁ (refl , refl) = gIBMr
...     | inj₂ (refl , refl) = gIBNr
gG7 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ICbusy-no-api clst)

gI .gnd = nd-I
gI .gτ st with netI-τ st
... | refl = gJ
gI .gev st with JN-gevA Cidle-mem CBloop-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (CBloop-no-ev clst)
gI .gev st | _ , _ , jeSvR svst with ISbusy-api svst
...     | inj₁ (refl , refl) = gLbMi
...     | inj₂ (refl , refl) = gLbNi
gI .gev st | _ , _ , jeBoth clst svst = ⊥-elim (CBloop-no-ev clst)

gIBMr .gnd = nd-IBMr
gIBMr .gτ st with netIBMr-τ st
... | refl = gM
gIBMr .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBsbatch-no-api ICn-no-bfMsg SBsbatch-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gIBNr .gnd = nd-IBNr
gIBNr .gτ st with netIBNr-τ st
... | refl = gN
gIBNr .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBnoblk-no-api ICn-no-bfMsg SBnoblk-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gIBSirr .gnd = nd-IBSirr
gIBSirr {r} .gτ st with netIBSirr-τ st
... | refl = gB2
gIBSirr {r} .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gIBbdsb .gnd = nd-IBbdsb
gIBbdsb .gτ st with netIBbdsb-τ st
... | refl = gBX3
gIBbdsb .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBbdone-no-api ICn-no-bfMsg SBbdone-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gIBblksb .gnd = nd-IBblksb
gIBblksb {b} .gτ st with netIBblksb-τ st
... | refl = gWX3
gIBblksb {b} .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBblk-no-api ICn-no-bfMsg SBblk-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gIDScd .gnd = nd-IDScd
gIDScd .gτ st with netIDScd-τ st
... | refl = gCd2
gIDScd .gev st = ⊥-elim (JN-gev-none ICdone-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gJ .gnd = nd-J
gJ .gτ st = ⊥-elim (netJ-noτ st)
gJ .gev st with JN-gevA Cidle-mem ICn-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (ICbusy-no-api clst)
gJ .gev st | _ , _ , jeSvR svst with ISbusy-api svst
...     | inj₁ (refl , refl) = gM
...     | inj₂ (refl , refl) = gN
gJ .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ICbusy-no-api clst)

gLbBDsb .gnd = nd-LbBDsb
gLbBDsb .gτ st with netLbBDsb-τ st
... | refl = gIBbdsb
gLbBDsb .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBbdone-no-api CBloop-no-bfMsg SBbdone-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gLbBLKsb .gnd = nd-LbBLKsb
gLbBLKsb {b} .gτ st with netLbBLKsb-τ st
... | refl = gIBblksb
gLbBLKsb {b} .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBblk-no-api CBloop-no-bfMsg SBblk-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gLbBh .gnd = nd-LbBh
gLbBh {r} .gτ st with netLbBh-τ st
... | inj₁ eq = subst Good (sym eq) gIBSirr
... | inj₂ eq = subst Good (sym eq) gBh
gLbBh {r} .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gLbM2 .gnd = nd-LbM2
gLbM2 .gτ st with netLbM2-τ st
... | refl = gM2
gLbM2 .gev st with JN-gevA Chold-mem CBloop-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (CBloop-no-ev clst)
gLbM2 .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gLbBLKsb
...     | inj₂ (refl , refl) = gLbBDsb
gLbM2 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (CBloop-no-ev clst)

gLbMh .gnd = nd-LbMh
gLbMh .gτ st with netLbMh-τ st
... | inj₁ eq = subst Good (sym eq) gMh
... | inj₂ eq = subst Good (sym eq) gLbM2
gLbMh .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gLbMi .gnd = nd-LbMi
gLbMi .gτ st with netLbMi-τ st
... | inj₁ eq = subst Good (sym eq) gM
... | inj₂ eq = subst Good (sym eq) gLbMh
gLbMi .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBsbatch-no-api CBloop-no-bfMsg SBsbatch-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gLbMr .gnd = nd-LbMr
gLbMr .gτ st with netLbMr-τ st
... | inj₁ eq = subst Good (sym eq) gIBMr
... | inj₂ eq = subst Good (sym eq) gLbMi
gLbMr .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBsbatch-no-api CBloop-no-bfMsg SBsbatch-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gLbN2 .gnd = nd-LbN2
gLbN2 .gτ st with netLbN2-τ st
... | refl = gN2
gLbN2 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev ISidle-no-api CBloop-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gLbNh .gnd = nd-LbNh
gLbNh .gτ st with netLbNh-τ st
... | inj₁ eq = subst Good (sym eq) gNh
... | inj₂ eq = subst Good (sym eq) gLbN2
gLbNh .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gLbNi .gnd = nd-LbNi
gLbNi .gτ st with netLbNi-τ st
... | inj₁ eq = subst Good (sym eq) gN
... | inj₂ eq = subst Good (sym eq) gLbNh
gLbNi .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBnoblk-no-api CBloop-no-bfMsg SBnoblk-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gLbNr .gnd = nd-LbNr
gLbNr .gτ st with netLbNr-τ st
... | inj₁ eq = subst Good (sym eq) gIBNr
... | inj₂ eq = subst Good (sym eq) gLbNi
gLbNr .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBnoblk-no-api CBloop-no-bfMsg SBnoblk-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gLdCdh .gnd = nd-LdCdh
gLdCdh .gτ st with netLdCdh-τ st
... | inj₁ eq = subst Good (sym eq) gIDScd
... | inj₂ eq = subst Good (sym eq) gCdh
gLdCdh .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gM .gnd = nd-M
gM .gτ st with netM-τ st
... | refl = gMh
gM .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBsbatch-no-api ICn-no-bfMsg SBsbatch-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gM2 .gnd = nd-M2
gM2 .gτ st with netM2-τ st
... | refl = gM5
gM2 .gev st with JN-gevA Chold-mem ICn-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (ICbusy-no-api clst)
gM2 .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gIBblksb
...     | inj₂ (refl , refl) = gIBbdsb
gM2 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ICbusy-no-api clst)

gM3 .gnd = nd-M3
gM3 .gτ st with netM3-τ st
... | inj₁ eq = subst Good (sym eq) gM4
... | inj₂ (inj₁ eq) = subst Good (sym eq) gM5
... | inj₂ (inj₂ eq) = subst Good (sym eq) gM6
gM3 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gM4 .gnd = nd-M4
gM4 .gτ st with netM4-τ st
... | inj₁ eq = subst Good (sym eq) gM7
... | inj₂ eq = subst Good (sym eq) gM8
gM4 .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gM5 .gnd = nd-M5
gM5 .gτ st with netM5-τ st
... | inj₁ eq = subst Good (sym eq) gM7
... | inj₂ eq = subst Good (sym eq) gM9
gM5 .gev st with JN-gevA Cret-mem CBloop-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (CBloop-no-ev clst)
gM5 .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gWX3
...     | inj₂ (refl , refl) = gBX3
gM5 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (CBloop-no-ev clst)

gM6 .gnd = nd-M6
gM6 .gτ st with netM6-τ st
... | inj₁ eq = subst Good (sym eq) gM8
... | inj₂ eq = subst Good (sym eq) gM9
gM6 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gM7 .gnd = nd-M7
gM7 .gτ st with netM7-τ st
... | refl = gV0
gM7 .gev st with JN-gevA Cret-mem ICn-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (ICstr-no-api clst)
gM7 .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gWX3a
...     | inj₂ (refl , refl) = gBX3a
gM7 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ICstr-no-api clst)

gM8 .gnd = nd-M8
gM8 .gτ st with netM8-τ st
... | refl = gV0
gM8 .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gM9 .gnd = nd-M9
gM9 .gτ st with netM9-τ st
... | refl = gV0
gM9 .gev st with JN-gevA Cidle-mem CBloop-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (CBloop-no-ev clst)
gM9 .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gWX1
...     | inj₂ (refl , refl) = gBX1
gM9 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (CBloop-no-ev clst)

gMh .gnd = nd-Mh
gMh .gτ st with netMh-τ st
... | inj₁ eq = subst Good (sym eq) gM2
... | inj₂ eq = subst Good (sym eq) gM3
gMh .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gN .gnd = nd-N
gN .gτ st with netN-τ st
... | refl = gNh
gN .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBnoblk-no-api ICn-no-bfMsg SBnoblk-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gN2 .gnd = nd-N2
gN2 .gτ st with netN2-τ st
... | refl = gN5
gN2 .gev st = ⊥-elim (JN-gev-none ICbusy-no-api ISidle-no-api ICn-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gN3 .gnd = nd-N3
gN3 .gτ st with netN3-τ st
... | inj₁ eq = subst Good (sym eq) gN4
... | inj₂ (inj₁ eq) = subst Good (sym eq) gN5
... | inj₂ (inj₂ eq) = subst Good (sym eq) gN6
gN3 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gN4 .gnd = nd-N4
gN4 .gτ st with netN4-τ st
... | inj₁ eq = subst Good (sym eq) gN7
... | inj₂ eq = subst Good (sym eq) gN8
gN4 .gev st with JN-gevA Cret-mem ICn-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with ICidle-api clst
...     | inj₁ (r , refl , refl) = gReqSr
...     | inj₂ (refl , refl) = gCdSr
gN4 .gev st | _ , _ , jeSvR svst = ⊥-elim (SBloop-no-ev svst)
gN4 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBloop-no-ev svst)

gN5 .gnd = nd-N5
gN5 .gτ st with netN5-τ st
... | inj₁ eq = subst Good (sym eq) gN7
... | inj₂ eq = subst Good (sym eq) gN9
gN5 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev ISidle-no-api CBloop-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gN6 .gnd = nd-N6
gN6 .gτ st with netN6-τ st
... | inj₁ eq = subst Good (sym eq) gN8
... | inj₂ eq = subst Good (sym eq) gN9
gN6 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gN7 .gnd = nd-N7
gN7 .gτ st with netN7-τ st
... | refl = gA
gN7 .gev st with JN-gevA Cret-mem ICn-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with ICidle-api clst
...     | inj₁ (r , refl , refl) = gReqR
...     | inj₂ (refl , refl) = gCdR
gN7 .gev st | _ , _ , jeSvR svst = ⊥-elim (ISidle-no-api svst)
gN7 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ISidle-no-api svst)

gN8 .gnd = nd-N8
gN8 .gτ st with netN8-τ st
... | refl = gA
gN8 .gev st with JN-gevA Cidle-mem ICn-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with ICidle-api clst
...     | inj₁ (r , refl , refl) = gReqSi
...     | inj₂ (refl , refl) = gCdSi
gN8 .gev st | _ , _ , jeSvR svst = ⊥-elim (SBloop-no-ev svst)
gN8 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBloop-no-ev svst)

gN9 .gnd = nd-N9
gN9 .gτ st with netN9-τ st
... | refl = gA
gN9 .gev st = ⊥-elim (JN-gev-none CBloop-no-ev ISidle-no-api CBloop-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gNh .gnd = nd-Nh
gNh .gτ st with netNh-τ st
... | inj₁ eq = subst Good (sym eq) gN2
... | inj₂ eq = subst Good (sym eq) gN3
gNh .gev st = ⊥-elim (JN-gev-none ICbusy-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gReqR .gnd = nd-ReqR
gReqR {r} .gτ st with netReqR-τ st
... | refl = gB
gReqR {r} .gev st = ⊥-elim (JN-gev-none CBreq-no-api ISidle-no-api CBreq-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gReqSi .gnd = nd-ReqSi
gReqSi {r} .gτ st with netReqSi-τ st
... | inj₁ eq = subst Good (sym eq) gB
... | inj₂ eq = subst Good (sym eq) gLbBh
gReqSi {r} .gev st = ⊥-elim (JN-gev-none CBreq-no-api SBloop-no-ev CBreq-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gReqSr .gnd = nd-ReqSr
gReqSr {r} .gτ st with netReqSr-τ st
... | inj₁ eq = subst Good (sym eq) gReqR
... | inj₂ eq = subst Good (sym eq) gReqSi
gReqSr {r} .gev st = ⊥-elim (JN-gev-none CBreq-no-api SBloop-no-ev CBreq-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gV0 .gnd = nd-V0
gV0 .gτ st = ⊥-elim (netV0-noτ st)
gV0 .gev st with JN-gevA Cidle-mem ICn-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (ICstr-no-api clst)
gV0 .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gW
...     | inj₂ (refl , refl) = gBD0e
gV0 .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ICstr-no-api clst)

gVocc1 .gnd = nd-Vocc1
gVocc1 {b} .gτ st = ⊥-elim (netVocc1-noτ st)
gVocc1 {b} .gev st with JN-gevA Cidle-mem CBblk-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gM9
gVocc1 {b} .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gW2e
...     | inj₂ (refl , refl) = gBD1e
gVocc1 {b} .gev st | _ , _ , jeBoth clst svst with CBblk-api clst
...     | (refl , refl) = ⊥-elim (ISstr-no-recv svst)

gW .gnd = nd-W
gW {b} .gτ st with netW-τ st
... | refl = gWh
gW {b} .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBblk-no-api ICn-no-bfMsg SBblk-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gW2 .gnd = nd-W2
gW2 {b} .gτ st with netW2-τ st
... | refl = gW4
gW2 {b} .gev st with JN-gevA Chold-mem ICn-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (ICstr-no-api clst)
gW2 {b} .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gW3a
...     | inj₂ (refl , refl) = gBD2a
gW2 {b} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (ICstr-no-api clst)

gW2a .gnd = nd-W2a
gW2a {b₀} {b₁} .gτ st = ⊥-elim (netW2a-noτ st)
gW2a {b₀} {b₁} .gev st with JN-gevA Chold-mem CBblk-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gW2d
gW2a {b₀} {b₁} .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gW3e
...     | inj₂ (refl , refl) = gBD2e
gW2a {b₀} {b₁} .gev st | _ , _ , jeBoth clst svst with CBblk-api clst
...     | (refl , refl) = ⊥-elim (ISstr-no-recv svst)

gW2d .gnd = nd-W2d
gW2d {b₁} .gτ st with netW2d-τ st
... | refl = gW2
gW2d {b₁} .gev st with JN-gevA Chold-mem CBloop-no-bfMsg ISn-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst = ⊥-elim (CBloop-no-ev clst)
gW2d {b₁} .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gW3d
...     | inj₂ (refl , refl) = gBD2d
gW2d {b₁} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (CBloop-no-ev clst)

gW2e .gnd = nd-W2e
gW2e {b₀} {b₁} .gτ st with netW2e-τ st
... | refl = gW2h
gW2e {b₀} {b₁} .gev st with JN-gevA Cidle-mem CBblk-no-bfMsg SBblk-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gWX1
gW2e {b₀} {b₁} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBblk-no-api svst)
gW2e {b₀} {b₁} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBblk-no-api svst)

gW2h .gnd = nd-W2h
gW2h {b₀} {b₁} .gτ st with netW2h-τ st
... | refl = gW2a
gW2h {b₀} {b₁} .gev st with JN-gevA Chold-mem CBblk-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gWX2
gW2h {b₀} {b₁} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBloop-no-ev svst)
gW2h {b₀} {b₁} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBloop-no-ev svst)

gW3 .gnd = nd-W3
gW3 {b} .gτ st with netW3-τ st
... | inj₁ eq = subst Good (sym eq) gW4
... | inj₂ eq = subst Good (sym eq) gW5
gW3 {b} .gev st with JN-gevA Cret-mem CBblk-no-bfMsg SBloop-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gM3
gW3 {b} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBloop-no-ev svst)
gW3 {b} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBloop-no-ev svst)

gW3a .gnd = nd-W3a
gW3a {b₁} {b₂} .gτ st with netW3a-τ st
... | refl = gW3b
gW3a {b₁} {b₂} .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBblk-no-api ICn-no-bfMsg SBblk-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gW3b .gnd = nd-W3b
gW3b {b₁} {b₂} .gτ st with netW3b-τ st
... | refl = gW2e
gW3b {b₁} {b₂} .gev st with JN-gevA Cret-mem CBblk-no-bfMsg SBblk-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gWX3
gW3b {b₁} {b₂} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBblk-no-api svst)
gW3b {b₁} {b₂} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBblk-no-api svst)

gW3d .gnd = nd-W3d
gW3d {b₁} {b₂} .gτ st with netW3d-τ st
... | refl = gW3a
gW3d {b₁} {b₂} .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBblk-no-api CBloop-no-bfMsg SBblk-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gW3e .gnd = nd-W3e
gW3e {b₀} {b₁} {b₂} .gτ st = ⊥-elim (netW3e-noτ st)
gW3e {b₀} {b₁} {b₂} .gev st with JN-gevA Chold-mem CBblk-no-bfMsg SBblk-no-bfMsg Chold-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gW3d
gW3e {b₀} {b₁} {b₂} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBblk-no-api svst)
gW3e {b₀} {b₁} {b₂} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBblk-no-api svst)

gW4 .gnd = nd-W4
gW4 {b} .gτ st with netW4-τ st
... | refl = gVocc1
gW4 {b} .gev st with JN-gevA Cret-mem CBblk-no-bfMsg ISn-no-bfMsg Cret-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gM5
gW4 {b} .gev st | _ , _ , jeSvR svst with ISstr-api svst
...     | inj₁ (b′ , refl , refl) = gW3b
...     | inj₂ (refl , refl) = gBD2b
gW4 {b} .gev st | _ , _ , jeBoth clst svst with CBblk-api clst
...     | (refl , refl) = ⊥-elim (ISstr-no-recv svst)

gW5 .gnd = nd-W5
gW5 {b} .gτ st with netW5-τ st
... | refl = gVocc1
gW5 {b} .gev st with JN-gevA Cidle-mem CBblk-no-bfMsg SBloop-no-bfMsg Cidle-no-bfMsg (λ ()) st
...   | _ , _ , jeClL clst with CBblk-api clst
...     | (refl , refl) = gM6
gW5 {b} .gev st | _ , _ , jeSvR svst = ⊥-elim (SBloop-no-ev svst)
gW5 {b} .gev st | _ , _ , jeBoth clst svst = ⊥-elim (SBloop-no-ev svst)

gWX1 .gnd = nd-WX1
gWX1 {b₁} .gτ st with netWX1-τ st
... | inj₁ eq = subst Good (sym eq) gW
... | inj₂ eq = subst Good (sym eq) gWX2
gWX1 {b₁} .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBblk-no-api CBloop-no-bfMsg SBblk-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

gWX2 .gnd = nd-WX2
gWX2 {b₁} .gτ st with netWX2-τ st
... | inj₁ eq = subst Good (sym eq) gWh
... | inj₂ eq = subst Good (sym eq) gW2d
gWX2 {b₁} .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBloop-no-ev CBloop-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gWX3 .gnd = nd-WX3
gWX3 {b₂} .gτ st with netWX3-τ st
... | inj₁ eq = subst Good (sym eq) gWX3a
... | inj₂ eq = subst Good (sym eq) gWX1
gWX3 {b₂} .gev st = ⊥-elim (JN-gev-none CBloop-no-ev SBblk-no-api CBloop-no-bfMsg SBblk-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gWX3a .gnd = nd-WX3a
gWX3a {b₂} .gτ st with netWX3a-τ st
... | refl = gW
gWX3a {b₂} .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBblk-no-api ICn-no-bfMsg SBblk-no-bfMsg Cret-no-bfMsg Cret-no-api (λ ()) st)

gWh .gnd = nd-Wh
gWh {b} .gτ st with netWh-τ st
... | inj₁ eq = subst Good (sym eq) gW2
... | inj₂ eq = subst Good (sym eq) gW3
gWh {b} .gev st = ⊥-elim (JN-gev-none ICstr-no-api SBloop-no-ev ICn-no-bfMsg SBloop-no-bfMsg Chold-no-bfMsg Chold-no-api (λ ()) st)

gZ .gnd = nd-Z
gZ .gτ st = ⊥-elim (netZ-noτ st)
gZ .gev st = ⊥-elim (JN-gev-none ICdone-no-api ISdone-no-api ICn-no-bfMsg ISn-no-bfMsg Cidle-no-bfMsg Cidle-no-api (λ ()) st)

-- the network's initial hidden state reduces to the idle/idle/idle joint config.
gNetInit : Good (networkBF NetOps.∖ ioBF)
gNetInit = gA

-- `networkBF ∖ ioBF` is divergence-free at every weakly-reachable state.
net-noDiv : ∀ {s W} → (networkBF NetOps.∖ ioBF) ⟹⟨ s ⟩ W → ¬ Diverges W
net-noDiv = go-reach gNetInit

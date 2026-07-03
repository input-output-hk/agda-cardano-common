{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Task 2 (network): divergence-freedom of the hidden BlockFetch network
-- processes.  Both `BFnetSpec ∖ bfMsgES` (cap-3 sequential spec) and
-- `networkBF ∖ ioBF` (interleaved peers routed through a copy medium) are
-- divergence-free: every hidden message-τ is bracketed by an observable API
-- event, so no infinite τ-run exists.  Mirrors `BlockFetchAbsRefinement`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.BlockFetchNetRefinement (p : Params) where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

open import CSP.Examples.Cardano_network.BlockFetch p

-- API tags + carried payload types, needed to name the transient states.
open import CSP.Examples.Cardano_network.Net p
  using ( ApiBFTag; ApiBFCar
        ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch
        ; sendBFNoBlocks; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange )
open import CSP.Examples.Cardano_network.Data p using (ChainRange; DecEq-ChainRange)
-- full open brings the Params instance fields (decBlock, …) into instance scope.
open Params p

-- the semantics at the network BlockFetch alphabet
open import Semantics.LTS {E = BFNetEv} {I = ExtI BFNetEv}
open import Semantics.DRBisim {E = BFNetEv} {I = ExtI BFNetEv}
  using (Diverges; deadlock-converges; deadlock-no-τ)
open import Semantics.Failures {E = BFNetEv} {I = ExtI BFNetEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)

-- the hide / parallel trace-law single-step inversions, at the network alphabet
open import CSP.Laws.Traces.TraceLawsHide BFNetEv-≟
  using (Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√)
open import CSP.Laws.Traces.TraceLawsParallelElim BFNetEv-≟
  using (Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)

open NetOps using (_∖_; Par⊤; Par; iter; iter-bind; Ret; Output; Prefix; Prefix₀; pchoice; Skip; loop0; loop; _⦀_; _∥⇘_⇙_; _>>=_; ∅ES; viewV; EventSet)

------------------------------------------------------------------------
-- The coinductive divergence-freedom invariant (mirrors `Good`).
------------------------------------------------------------------------

-- `Good W` certifies that the hidden state `W` is divergence-free and that
-- this property is preserved by every τ- and visible-step out of `W`.
record Good (W : PTree BFNetEv (ExtI BFNetEv) Rr) : Set₁ where
  coinductive
  field
    gnd : ¬ Diverges W
    gτ  : ∀ {W′} → W ─[ τ ]─► W′ → Good W′
    gev : ∀ {W′} {e : Event√ Rr} → W ─[ ev e ]─► W′ → Good W′
open Good

-- the weak-reach walk: a `Good` invariant rules out divergence at any
-- weakly-reachable state.
go-reach : ∀ {s W W′} → Good W → W ⟹⟨ s ⟩ W′ → ¬ Diverges W′
go-reach g ⟹-refl         = g .gnd
go-reach g (⟹-τ  st rest) = go-reach (g .gτ  st) rest
go-reach g (⟹-ev st rest) = go-reach (g .gev st) rest

-- deadlock is Good: it has no τ-, visible- or √-successor at all.
good-deadlock : Good deadlock
good-deadlock .gnd = deadlock-converges
good-deadlock .gτ (sSil ())
good-deadlock .gτ (sTau refl ())
good-deadlock .gev (sRet ())
good-deadlock .gev (sVis refl ())

------------------------------------------------------------------------
-- SPEC side: BFnetSpec ∖ bfMsgES.  Sequential cap-3 iteration.
------------------------------------------------------------------------

-- abbreviation: the SPEC iteration at a state
IT : BFNetState → PTree BFNetEv (ExtI BFNetEv) Rr
IT s = NetOps.iter bfnetStep s

-- a `Stable` SPEC state offers only apiBF events (∉ bfMsgES) with an empty
-- τ-part, so it has no hidden τ.  `nStrD0` is excluded (it is an iter loop-back).
data StableN : BFNetState → Set where
  sIdle  : StableN nIdle
  sBusy  : StableN nBusy
  sStr0  : StableN nStr0
  sStr1  : ∀ {b} → StableN (nStr1 b)
  sStr2  : ∀ {b b′} → StableN (nStr2 b b′)
  sStr3  : ∀ {b b′ b″} → StableN (nStr3 b b′ b″)
  sStrD1 : ∀ {b} → StableN (nStrD1 b)
  sStrD2 : ∀ {b b′} → StableN (nStrD2 b b′)
  sDone  : StableN nDone

-- a stable pchoice SPEC state (it offers only apiBF events ∉ bfMsgES) has no
-- hidden τ.  Probed per-state; nDone is the terminal deadlock state (empty react).
spec-noτ : ∀ {W′} {s : BFNetState} → StableN s → ¬ ((IT s NetOps.∖ bfMsgES) ─[ τ ]─► W′)
spec-noτ {s = s} _ st with Hide-τ-elim bfMsgES (IT s) st
spec-noτ sIdle _ | hτP P' (sSil ()) refl
spec-noτ sIdle _ | hτP P' (sTau refl ()) refl
spec-noτ sIdle _ | hτH {e = bfMsg}    P' mem (sVis {at = (_ , bfMsg)}    refl ()) refl
spec-noτ sIdle _ | hτH {e = bfIn}     P' mem (sVis {at = (_ , bfIn)}     refl ()) refl
spec-noτ sIdle _ | hτH {e = bfOut}    P' mem (sVis {at = (_ , bfOut)}    refl ()) refl
spec-noτ sIdle _ | hτH {e = apiBF m}  P' mem stp refl = mem
spec-noτ sBusy _ | hτP P' (sSil ()) refl
spec-noτ sBusy _ | hτP P' (sTau refl ()) refl
spec-noτ sBusy _ | hτH {e = bfMsg}    P' mem (sVis {at = (_ , bfMsg)}    refl ()) refl
spec-noτ sBusy _ | hτH {e = bfIn}     P' mem (sVis {at = (_ , bfIn)}     refl ()) refl
spec-noτ sBusy _ | hτH {e = bfOut}    P' mem (sVis {at = (_ , bfOut)}    refl ()) refl
spec-noτ sBusy _ | hτH {e = apiBF m}  P' mem stp refl = mem
spec-noτ sStr0 _ | hτP P' (sSil ()) refl
spec-noτ sStr0 _ | hτP P' (sTau refl ()) refl
spec-noτ sStr0 _ | hτH {e = bfMsg}    P' mem (sVis {at = (_ , bfMsg)}    refl ()) refl
spec-noτ sStr0 _ | hτH {e = bfIn}     P' mem (sVis {at = (_ , bfIn)}     refl ()) refl
spec-noτ sStr0 _ | hτH {e = bfOut}    P' mem (sVis {at = (_ , bfOut)}    refl ()) refl
spec-noτ sStr0 _ | hτH {e = apiBF m}  P' mem stp refl = mem
spec-noτ sStr1 _ | hτP P' (sSil ()) refl
spec-noτ sStr1 _ | hτP P' (sTau refl ()) refl
spec-noτ sStr1 _ | hτH {e = bfMsg}    P' mem (sVis {at = (_ , bfMsg)}    refl ()) refl
spec-noτ sStr1 _ | hτH {e = bfIn}     P' mem (sVis {at = (_ , bfIn)}     refl ()) refl
spec-noτ sStr1 _ | hτH {e = bfOut}    P' mem (sVis {at = (_ , bfOut)}    refl ()) refl
spec-noτ sStr1 _ | hτH {e = apiBF m}  P' mem stp refl = mem
spec-noτ sStr2 _ | hτP P' (sSil ()) refl
spec-noτ sStr2 _ | hτP P' (sTau refl ()) refl
spec-noτ sStr2 _ | hτH {e = bfMsg}    P' mem (sVis {at = (_ , bfMsg)}    refl ()) refl
spec-noτ sStr2 _ | hτH {e = bfIn}     P' mem (sVis {at = (_ , bfIn)}     refl ()) refl
spec-noτ sStr2 _ | hτH {e = bfOut}    P' mem (sVis {at = (_ , bfOut)}    refl ()) refl
spec-noτ sStr2 _ | hτH {e = apiBF m}  P' mem stp refl = mem
spec-noτ sStr3 _ | hτP P' (sSil ()) refl
spec-noτ sStr3 _ | hτP P' (sTau refl ()) refl
spec-noτ sStr3 _ | hτH {e = bfMsg}    P' mem (sVis {at = (_ , bfMsg)}    refl ()) refl
spec-noτ sStr3 _ | hτH {e = bfIn}     P' mem (sVis {at = (_ , bfIn)}     refl ()) refl
spec-noτ sStr3 _ | hτH {e = bfOut}    P' mem (sVis {at = (_ , bfOut)}    refl ()) refl
spec-noτ sStr3 _ | hτH {e = apiBF m}  P' mem stp refl = mem
spec-noτ sStrD1 _ | hτP P' (sSil ()) refl
spec-noτ sStrD1 _ | hτP P' (sTau refl ()) refl
spec-noτ sStrD1 _ | hτH {e = bfMsg}    P' mem (sVis {at = (_ , bfMsg)}    refl ()) refl
spec-noτ sStrD1 _ | hτH {e = bfIn}     P' mem (sVis {at = (_ , bfIn)}     refl ()) refl
spec-noτ sStrD1 _ | hτH {e = bfOut}    P' mem (sVis {at = (_ , bfOut)}    refl ()) refl
spec-noτ sStrD1 _ | hτH {e = apiBF m}  P' mem stp refl = mem
spec-noτ sStrD2 _ | hτP P' (sSil ()) refl
spec-noτ sStrD2 _ | hτP P' (sTau refl ()) refl
spec-noτ sStrD2 _ | hτH {e = bfMsg}    P' mem (sVis {at = (_ , bfMsg)}    refl ()) refl
spec-noτ sStrD2 _ | hτH {e = bfIn}     P' mem (sVis {at = (_ , bfIn)}     refl ()) refl
spec-noτ sStrD2 _ | hτH {e = bfOut}    P' mem (sVis {at = (_ , bfOut)}    refl ()) refl
spec-noτ sStrD2 _ | hτH {e = apiBF m}  P' mem stp refl = mem
spec-noτ sDone _ | hτP P' (sSil ()) refl
spec-noτ sDone _ | hτP P' (sTau refl ()) refl
spec-noτ sDone _ | hτH P' mem (sVis refl ()) refl

------------------------------------------------------------------------
-- SPEC transient states (just past a hidden bfMsg send / iter loop-back).
------------------------------------------------------------------------

-- transient: an iter loop-back point (ret (inj₁ s) ⇒ sil (IT s)).
S-loop : BFNetState → PTree BFNetEv (ExtI BFNetEv) Rr
S-loop s = NetOps.iter-bind (NetOps.Ret (inj₁ s)) bfnetStep

-- transient: nIdle/request, the bfMsg(mRequestRange) hop then the reqBFRange api.
S-req : ChainRange → PTree BFNetEv (ExtI BFNetEv) Rr
S-req range = NetOps.iter-bind
  (NetOps.Output bfMsg (mRequestRange range)
     (NetOps.Output (apiBF reqBFRange) range (NetOps.Ret (inj₁ nBusy)))) bfnetStep

-- transient: nIdle/request, after the bfMsg hidden — offering the reqBFRange api.
S-req2 : ChainRange → PTree BFNetEv (ExtI BFNetEv) Rr
S-req2 range = NetOps.iter-bind
  (NetOps.Output (apiBF reqBFRange) range (NetOps.Ret (inj₁ nBusy))) bfnetStep

-- transient: nIdle/client-done, the bfMsg(mClientDone) hop (→ nDone).
S-cdone : PTree BFNetEv (ExtI BFNetEv) Rr
S-cdone = NetOps.iter-bind
  (NetOps.Output bfMsg mClientDone (NetOps.Ret (inj₁ nDone))) bfnetStep

-- transient: nBusy/start-batch, the bfMsg(mStartBatch) hop (→ nStr0).
S-sbatch : PTree BFNetEv (ExtI BFNetEv) Rr
S-sbatch = NetOps.iter-bind
  (NetOps.Output bfMsg mStartBatch (NetOps.Ret (inj₁ nStr0))) bfnetStep

-- transient: nBusy/no-blocks, the bfMsg(mNoBlocks) hop (→ nIdle).
S-noblk : PTree BFNetEv (ExtI BFNetEv) Rr
S-noblk = NetOps.iter-bind
  (NetOps.Output bfMsg mNoBlocks (NetOps.Ret (inj₁ nIdle))) bfnetStep

-- transient: nStr0/send-block b, the bfMsg(mBlock b) hop (→ nStr1 b).
S-blk0 : Block → PTree BFNetEv (ExtI BFNetEv) Rr
S-blk0 b = NetOps.iter-bind
  (NetOps.Output bfMsg (mBlock b) (NetOps.Ret (inj₁ (nStr1 b)))) bfnetStep

-- transient: nStr1 b/send-block b′, the bfMsg(mBlock b′) hop (→ nStr2 b b′).
S-blk1 : Block → Block → PTree BFNetEv (ExtI BFNetEv) Rr
S-blk1 b b′ = NetOps.iter-bind
  (NetOps.Output bfMsg (mBlock b′) (NetOps.Ret (inj₁ (nStr2 b b′)))) bfnetStep

-- transient: nStr2 b b′/send-block b″, the bfMsg(mBlock b″) hop (→ nStr3 b b′ b″).
S-blk2 : Block → Block → Block → PTree BFNetEv (ExtI BFNetEv) Rr
S-blk2 b b′ b″ = NetOps.iter-bind
  (NetOps.Output bfMsg (mBlock b″) (NetOps.Ret (inj₁ (nStr3 b b′ b″)))) bfnetStep

-- transient: nStr0/batch-done, the bfMsg(mBatchDone) hop (→ nStrD0).
S-bd0 : PTree BFNetEv (ExtI BFNetEv) Rr
S-bd0 = NetOps.iter-bind
  (NetOps.Output bfMsg mBatchDone (NetOps.Ret (inj₁ nStrD0))) bfnetStep

-- transient: nStr1 b/batch-done, the bfMsg(mBatchDone) hop (→ nStrD1 b).
S-bd1 : Block → PTree BFNetEv (ExtI BFNetEv) Rr
S-bd1 b = NetOps.iter-bind
  (NetOps.Output bfMsg mBatchDone (NetOps.Ret (inj₁ (nStrD1 b)))) bfnetStep

-- transient: nStr2 b b′/batch-done, the bfMsg(mBatchDone) hop (→ nStrD2 b b′).
S-bd2 : Block → Block → PTree BFNetEv (ExtI BFNetEv) Rr
S-bd2 b b′ = NetOps.iter-bind
  (NetOps.Output bfMsg mBatchDone (NetOps.Ret (inj₁ (nStrD2 b b′)))) bfnetStep

-- the only τ out of S-loop s lands on IT s (the iter loop-back sil).
S-loop-τ : ∀ {s W″} → (S-loop s NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (IT s NetOps.∖ bfMsgES)
S-loop-τ {s} st with Hide-τ-elim bfMsgES (S-loop s) st
... | hτP P' (sSil refl) refl = refl
... | hτP P' (sTau () _) refl
... | hτH P' mem (sVis () _) refl

-- IT nStrD0 is itself a loop-back transient: its only τ lands on IT nIdle.
S-strD0-τ : ∀ {W″} → (IT nStrD0 NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (IT nIdle NetOps.∖ bfMsgES)
S-strD0-τ st with Hide-τ-elim bfMsgES (IT nStrD0) st
... | hτP P' (sSil refl) refl = refl
... | hτP P' (sTau () _) refl
... | hτH P' mem (sVis () _) refl

-- the only τ out of S-req lands on S-req2 (the hidden bfMsg(mRequestRange)).
S-req-τ : ∀ {range W″} → (S-req range NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-req2 range NetOps.∖ bfMsgES)
S-req-τ {range} st with Hide-τ-elim bfMsgES (S-req range) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl breq) refl with r ≟ range
...   | yes refl with breq
...     | refl = refl
S-req-τ {range} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl | no _
S-req-τ {range} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
S-req-τ {range} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
S-req-τ {range} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
S-req-τ {range} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock b}        refl ()) refl
S-req-τ {range} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl ()) refl
S-req-τ {range} st | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
S-req-τ {range} st | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
S-req-τ {range} st | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- generic single-hop bfMsg-send τ-lemma factored out: a value-free `Prefix₀`-style
-- bfMsg(mX) prefix has its sole τ landing on the loop-back of its target state.
-- (Each concrete sender is proved below by matching its specific BFMsg value.)

-- the only τ out of S-cdone lands on S-loop nDone (hidden bfMsg(mClientDone)).
S-cdone-τ : ∀ {W″} → (S-cdone NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop nDone NetOps.∖ bfMsgES)
S-cdone-τ st with Hide-τ-elim bfMsgES S-cdone st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl refl) refl = refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock b}        refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl ()) refl
... | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
... | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
... | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- the only τ out of S-sbatch lands on S-loop nStr0 (hidden bfMsg(mStartBatch)).
S-sbatch-τ : ∀ {W″} → (S-sbatch NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop nStr0 NetOps.∖ bfMsgES)
S-sbatch-τ st with Hide-τ-elim bfMsgES S-sbatch st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl refl) refl = refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock b}        refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl ()) refl
... | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
... | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
... | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- the only τ out of S-noblk lands on S-loop nIdle (hidden bfMsg(mNoBlocks)).
S-noblk-τ : ∀ {W″} → (S-noblk NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop nIdle NetOps.∖ bfMsgES)
S-noblk-τ st with Hide-τ-elim bfMsgES S-noblk st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl refl) refl = refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock b}        refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl ()) refl
... | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
... | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
... | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- the only τ out of S-blk0 lands on S-loop (nStr1 b) (hidden bfMsg(mBlock b)).
S-blk0-τ : ∀ {b W″} → (S-blk0 b NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop (nStr1 b) NetOps.∖ bfMsgES)
S-blk0-τ {b} st with Hide-τ-elim bfMsgES (S-blk0 b) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock x} refl breq) refl with x ≟ b
...   | yes refl with breq
...     | refl = refl
S-blk0-τ {b} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock x}        refl ()) refl | no _
S-blk0-τ {b} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
S-blk0-τ {b} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
S-blk0-τ {b} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
S-blk0-τ {b} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
S-blk0-τ {b} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl ()) refl
S-blk0-τ {b} st | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
S-blk0-τ {b} st | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
S-blk0-τ {b} st | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- the only τ out of S-blk1 lands on S-loop (nStr2 b b′) (hidden bfMsg(mBlock b′)).
S-blk1-τ : ∀ {b b′ W″} → (S-blk1 b b′ NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop (nStr2 b b′) NetOps.∖ bfMsgES)
S-blk1-τ {b} {b′} st with Hide-τ-elim bfMsgES (S-blk1 b b′) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock x} refl breq) refl with x ≟ b′
...   | yes refl with breq
...     | refl = refl
S-blk1-τ {b} {b′} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock x}        refl ()) refl | no _
S-blk1-τ {b} {b′} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
S-blk1-τ {b} {b′} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
S-blk1-τ {b} {b′} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
S-blk1-τ {b} {b′} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
S-blk1-τ {b} {b′} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl ()) refl
S-blk1-τ {b} {b′} st | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
S-blk1-τ {b} {b′} st | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
S-blk1-τ {b} {b′} st | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- the only τ out of S-blk2 lands on S-loop (nStr3 b b′ b″) (hidden bfMsg(mBlock b″)).
S-blk2-τ : ∀ {b b′ b″ W″} → (S-blk2 b b′ b″ NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop (nStr3 b b′ b″) NetOps.∖ bfMsgES)
S-blk2-τ {b} {b′} {b″} st with Hide-τ-elim bfMsgES (S-blk2 b b′ b″) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock x} refl breq) refl with x ≟ b″
...   | yes refl with breq
...     | refl = refl
S-blk2-τ {b} {b′} {b″} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock x}        refl ()) refl | no _
S-blk2-τ {b} {b′} {b″} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
S-blk2-τ {b} {b′} {b″} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
S-blk2-τ {b} {b′} {b″} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
S-blk2-τ {b} {b′} {b″} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
S-blk2-τ {b} {b′} {b″} st | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl ()) refl
S-blk2-τ {b} {b′} {b″} st | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
S-blk2-τ {b} {b′} {b″} st | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
S-blk2-τ {b} {b′} {b″} st | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- the only τ out of S-bd0 lands on S-loop nStrD0 (hidden bfMsg(mBatchDone)).
S-bd0-τ : ∀ {W″} → (S-bd0 NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop nStrD0 NetOps.∖ bfMsgES)
S-bd0-τ st with Hide-τ-elim bfMsgES S-bd0 st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl refl) refl = refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock b}        refl ()) refl
... | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
... | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
... | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- the only τ out of S-bd1 lands on S-loop (nStrD1 b) (hidden bfMsg(mBatchDone)).
S-bd1-τ : ∀ {b W″} → (S-bd1 b NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop (nStrD1 b) NetOps.∖ bfMsgES)
S-bd1-τ {b} st with Hide-τ-elim bfMsgES (S-bd1 b) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl refl) refl = refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock c}        refl ()) refl
... | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
... | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
... | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- the only τ out of S-bd2 lands on S-loop (nStrD2 b b′) (hidden bfMsg(mBatchDone)).
S-bd2-τ : ∀ {b b′ W″} → (S-bd2 b b′ NetOps.∖ bfMsgES) ─[ τ ]─► W″ → W″ ≡ (S-loop (nStrD2 b b′) NetOps.∖ bfMsgES)
S-bd2-τ {b} {b′} st with Hide-τ-elim bfMsgES (S-bd2 b b′) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBatchDone}      refl refl) refl = refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mRequestRange r} refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mClientDone}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mStartBatch}     refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mNoBlocks}       refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} {a = mBlock c}        refl ()) refl
... | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
... | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
... | hτH {e = apiBF m} P' mem stp refl = ⊥-elim mem

-- S-req2 is stable: it offers only the reqBFRange api (∉ bfMsgES), empty τ-part.
S-req2-noτ : ∀ {range W″} → ¬ ((S-req2 range NetOps.∖ bfMsgES) ─[ τ ]─► W″)
S-req2-noτ {range} st with Hide-τ-elim bfMsgES (S-req2 range) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = bfMsg} P' mem (sVis {at = (_ , bfMsg)} refl ()) refl
... | hτH {e = bfIn}  P' mem (sVis {at = (_ , bfIn)}  refl ()) refl
... | hτH {e = bfOut} P' mem (sVis {at = (_ , bfOut)} refl ()) refl
... | hτH {e = apiBF m} P' mem stp refl = mem

------------------------------------------------------------------------
-- ¬ Diverges at each SPEC state (a finite, acyclic τ-DAG toward stable states).
------------------------------------------------------------------------

-- stable pchoice states never diverge (no τ at all).
spec-nd-IT : ∀ {s} → StableN s → ¬ Diverges (IT s NetOps.∖ bfMsgES)
spec-nd-IT stbl d = spec-noτ stbl (d .Diverges.step)

-- S-req2 is stable.
spec-nd-req2 : ∀ {range} → ¬ Diverges (S-req2 range NetOps.∖ bfMsgES)
spec-nd-req2 d = S-req2-noτ (d .Diverges.step)

-- transient states: a single τ leads to an already-converging state.
spec-nd-loop : ∀ {s} → StableN s → ¬ Diverges (S-loop s NetOps.∖ bfMsgES)
spec-nd-loop stbl d = spec-nd-IT stbl (subst Diverges (S-loop-τ (d .Diverges.step)) (d .Diverges.rest))

-- nStrD0 is an iter loop-back transient: τ to IT nIdle (stable).
spec-nd-strD0 : ¬ Diverges (IT nStrD0 NetOps.∖ bfMsgES)
spec-nd-strD0 d = spec-nd-IT sIdle (subst Diverges (S-strD0-τ (d .Diverges.step)) (d .Diverges.rest))

-- S-loop nStrD0 → IT nStrD0 → IT nIdle.
spec-nd-loop-strD0 : ¬ Diverges (S-loop nStrD0 NetOps.∖ bfMsgES)
spec-nd-loop-strD0 d = spec-nd-strD0 (subst Diverges (S-loop-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-req : ∀ {range} → ¬ Diverges (S-req range NetOps.∖ bfMsgES)
spec-nd-req d = spec-nd-req2 (subst Diverges (S-req-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-cdone : ¬ Diverges (S-cdone NetOps.∖ bfMsgES)
spec-nd-cdone d = spec-nd-loop sDone (subst Diverges (S-cdone-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-sbatch : ¬ Diverges (S-sbatch NetOps.∖ bfMsgES)
spec-nd-sbatch d = spec-nd-loop sStr0 (subst Diverges (S-sbatch-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-noblk : ¬ Diverges (S-noblk NetOps.∖ bfMsgES)
spec-nd-noblk d = spec-nd-loop sIdle (subst Diverges (S-noblk-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-blk0 : ∀ {b} → ¬ Diverges (S-blk0 b NetOps.∖ bfMsgES)
spec-nd-blk0 d = spec-nd-loop sStr1 (subst Diverges (S-blk0-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-blk1 : ∀ {b b′} → ¬ Diverges (S-blk1 b b′ NetOps.∖ bfMsgES)
spec-nd-blk1 d = spec-nd-loop sStr2 (subst Diverges (S-blk1-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-blk2 : ∀ {b b′ b″} → ¬ Diverges (S-blk2 b b′ b″ NetOps.∖ bfMsgES)
spec-nd-blk2 d = spec-nd-loop sStr3 (subst Diverges (S-blk2-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-bd0 : ¬ Diverges (S-bd0 NetOps.∖ bfMsgES)
spec-nd-bd0 d = spec-nd-loop-strD0 (subst Diverges (S-bd0-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-bd1 : ∀ {b} → ¬ Diverges (S-bd1 b NetOps.∖ bfMsgES)
spec-nd-bd1 d = spec-nd-loop sStrD1 (subst Diverges (S-bd1-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-bd2 : ∀ {b b′} → ¬ Diverges (S-bd2 b b′ NetOps.∖ bfMsgES)
spec-nd-bd2 d = spec-nd-loop sStrD2 (subst Diverges (S-bd2-τ (d .Diverges.step)) (d .Diverges.rest))

------------------------------------------------------------------------
-- The coinductive `Good` invariant at every reachable hidden SPEC state.
------------------------------------------------------------------------

-- forward declarations of the per-state invariants.
good-IT     : (s : BFNetState) → Good (IT s NetOps.∖ bfMsgES)
good-loop   : ∀ {s} → StableN s → Good (S-loop s NetOps.∖ bfMsgES)
good-loop-strD0 : Good (S-loop nStrD0 NetOps.∖ bfMsgES)
good-req    : ∀ (range : ChainRange) → Good (S-req range NetOps.∖ bfMsgES)
good-req2   : ∀ (range : ChainRange) → Good (S-req2 range NetOps.∖ bfMsgES)
good-cdone  : Good (S-cdone NetOps.∖ bfMsgES)
good-sbatch : Good (S-sbatch NetOps.∖ bfMsgES)
good-noblk  : Good (S-noblk NetOps.∖ bfMsgES)
good-blk0   : ∀ (b : Block) → Good (S-blk0 b NetOps.∖ bfMsgES)
good-blk1   : ∀ (b b′ : Block) → Good (S-blk1 b b′ NetOps.∖ bfMsgES)
good-blk2   : ∀ (b b′ b″ : Block) → Good (S-blk2 b b′ b″ NetOps.∖ bfMsgES)
good-bd0    : Good (S-bd0 NetOps.∖ bfMsgES)
good-bd1    : ∀ (b : Block) → Good (S-bd1 b NetOps.∖ bfMsgES)
good-bd2    : ∀ (b b′ : Block) → Good (S-bd2 b b′ NetOps.∖ bfMsgES)

-- IT nIdle: stable; offers sendBFRequestRange (→ S-req) and sendBFClientDone (→ S-cdone).
good-IT nIdle .gnd = spec-nd-IT sIdle
good-IT nIdle .gτ st = ⊥-elim (spec-noτ sIdle st)
good-IT nIdle .gev st with Hide-ev-elim bfMsgES (IT nIdle) st
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = r} refl refl) = good-req r
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl refl) = good-cdone
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
... | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
... | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
... | he√ ()
-- IT nBusy: stable; offers sendBFStartBatch (→ S-sbatch) and sendBFNoBlocks (→ S-noblk).
good-IT nBusy .gnd = spec-nd-IT sBusy
good-IT nBusy .gτ st = ⊥-elim (spec-noτ sBusy st)
good-IT nBusy .gev st with Hide-ev-elim bfMsgES (IT nBusy) st
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = good-sbatch
... | heV {e = apiBF sendBFNoBlocks}   P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}   refl refl) = good-noblk
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
... | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
... | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
... | he√ ()
-- IT nStr0: stable; offers sendBFBlock (→ S-blk0) and sendBFBatchDone (→ S-bd0).
good-IT nStr0 .gnd = spec-nd-IT sStr0
good-IT nStr0 .gτ st = ⊥-elim (spec-noτ sStr0 st)
good-IT nStr0 .gev st with Hide-ev-elim bfMsgES (IT nStr0) st
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = good-blk0 b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = good-bd0
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
... | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
... | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
... | he√ ()
-- IT (nStr1 b): stable, mixed; recvBFBlock!b (→ S-loop nStr0), sendBFBlock b′ (→ S-blk1),
-- sendBFBatchDone (→ S-bd1 b).
good-IT (nStr1 b) .gnd = spec-nd-IT sStr1
good-IT (nStr1 b) .gτ st = ⊥-elim (spec-noτ sStr1 st)
good-IT (nStr1 b) .gev st with Hide-ev-elim bfMsgES (IT (nStr1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = good-loop sStr0
good-IT (nStr1 b) .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
good-IT (nStr1 b) .gev st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b′} refl refl) = good-blk1 b b′
good-IT (nStr1 b) .gev st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = good-bd1 b
good-IT (nStr1 b) .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
good-IT (nStr1 b) .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
good-IT (nStr1 b) .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
good-IT (nStr1 b) .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
good-IT (nStr1 b) .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
good-IT (nStr1 b) .gev st | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
good-IT (nStr1 b) .gev st | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
good-IT (nStr1 b) .gev st | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
good-IT (nStr1 b) .gev st | he√ ()
-- IT (nStr2 b b′): stable, mixed; recvBFBlock!b (→ S-loop (nStr1 b′)), sendBFBlock b″ (→ S-blk2),
-- sendBFBatchDone (→ S-bd2 b b′).
good-IT (nStr2 b b′) .gnd = spec-nd-IT sStr2
good-IT (nStr2 b b′) .gτ st = ⊥-elim (spec-noτ sStr2 st)
good-IT (nStr2 b b′) .gev st with Hide-ev-elim bfMsgES (IT (nStr2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = good-loop sStr1
good-IT (nStr2 b b′) .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
good-IT (nStr2 b b′) .gev st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b″} refl refl) = good-blk2 b b′ b″
good-IT (nStr2 b b′) .gev st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = good-bd2 b b′
good-IT (nStr2 b b′) .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
good-IT (nStr2 b b′) .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
good-IT (nStr2 b b′) .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
good-IT (nStr2 b b′) .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
good-IT (nStr2 b b′) .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
good-IT (nStr2 b b′) .gev st | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
good-IT (nStr2 b b′) .gev st | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
good-IT (nStr2 b b′) .gev st | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
good-IT (nStr2 b b′) .gev st | he√ ()
-- IT (nStr3 b b′ b″): saturated; ONLY recvBFBlock!b (→ S-loop (nStr2 b′ b″)).
good-IT (nStr3 b b′ b″) .gnd = spec-nd-IT sStr3
good-IT (nStr3 b b′ b″) .gτ st = ⊥-elim (spec-noτ sStr3 st)
good-IT (nStr3 b b′ b″) .gev st with Hide-ev-elim bfMsgES (IT (nStr3 b b′ b″)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = good-loop sStr2
good-IT (nStr3 b b′ b″) .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
good-IT (nStr3 b b′ b″) .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
good-IT (nStr3 b b′ b″) .gev st | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
good-IT (nStr3 b b′ b″) .gev st | he√ ()
-- IT nStrD0: iter loop-back transient; a single τ to IT nIdle, no visible event.
good-IT nStrD0 .gnd = spec-nd-strD0
good-IT nStrD0 .gτ st with S-strD0-τ st
... | refl = good-IT nIdle
good-IT nStrD0 .gev st with Hide-ev-elim bfMsgES (IT nStrD0) st
... | heV P' ¬m (sVis () _)
... | he√ ()
-- IT (nStrD1 b): stable; ONLY recvBFBlock!b (→ S-loop nStrD0).
good-IT (nStrD1 b) .gnd = spec-nd-IT sStrD1
good-IT (nStrD1 b) .gτ st = ⊥-elim (spec-noτ sStrD1 st)
good-IT (nStrD1 b) .gev st with Hide-ev-elim bfMsgES (IT (nStrD1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = good-loop-strD0
good-IT (nStrD1 b) .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
good-IT (nStrD1 b) .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
good-IT (nStrD1 b) .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
good-IT (nStrD1 b) .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
good-IT (nStrD1 b) .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
good-IT (nStrD1 b) .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
good-IT (nStrD1 b) .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
good-IT (nStrD1 b) .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
good-IT (nStrD1 b) .gev st | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
good-IT (nStrD1 b) .gev st | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
good-IT (nStrD1 b) .gev st | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
good-IT (nStrD1 b) .gev st | he√ ()
-- IT (nStrD2 b b′): stable; ONLY recvBFBlock!b (→ S-loop (nStrD1 b′)).
good-IT (nStrD2 b b′) .gnd = spec-nd-IT sStrD2
good-IT (nStrD2 b b′) .gτ st = ⊥-elim (spec-noτ sStrD2 st)
good-IT (nStrD2 b b′) .gev st with Hide-ev-elim bfMsgES (IT (nStrD2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = good-loop sStrD1
good-IT (nStrD2 b b′) .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
good-IT (nStrD2 b b′) .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
good-IT (nStrD2 b b′) .gev st | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
good-IT (nStrD2 b b′) .gev st | he√ ()
-- IT nDone: deadlock (empty react); stable, non-divergent, no visible event and no √.
good-IT nDone .gnd = spec-nd-IT sDone
good-IT nDone .gτ st = ⊥-elim (spec-noτ sDone st)
good-IT nDone .gev st with Hide-ev-elim bfMsgES (IT nDone) st
... | heV P' ¬m (sVis refl ())
... | he√ ()

-- S-req: one hidden τ (bfMsg(mRequestRange)) to S-req2; no surviving visible event.
good-req range .gnd = spec-nd-req
good-req range .gτ st with S-req-τ st
... | refl = good-req2 range
good-req range .gev st with Hide-ev-elim bfMsgES (S-req range) st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-req2: stable; the reqBFRange api (value = range) survives to S-loop nBusy.
good-req2 range .gnd = spec-nd-req2
good-req2 range .gτ st = ⊥-elim (S-req2-noτ st)
good-req2 range .gev st with Hide-ev-elim bfMsgES (S-req2 range) st
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl breq) with a ≟ range
...   | yes refl with breq
...     | refl = good-loop sBusy
good-req2 range .gev st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
good-req2 range .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
good-req2 range .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
good-req2 range .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
good-req2 range .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
good-req2 range .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
good-req2 range .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
good-req2 range .gev st | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
good-req2 range .gev st | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
good-req2 range .gev st | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
good-req2 range .gev st | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())
good-req2 range .gev st | he√ ()

-- S-cdone: one hidden τ (bfMsg(mClientDone)) to S-loop nDone; no surviving visible event.
good-cdone .gnd = spec-nd-cdone
good-cdone .gτ st with S-cdone-τ st
... | refl = good-loop sDone
good-cdone .gev st with Hide-ev-elim bfMsgES S-cdone st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-sbatch: one hidden τ (bfMsg(mStartBatch)) to S-loop nStr0; no surviving visible event.
good-sbatch .gnd = spec-nd-sbatch
good-sbatch .gτ st with S-sbatch-τ st
... | refl = good-loop sStr0
good-sbatch .gev st with Hide-ev-elim bfMsgES S-sbatch st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-noblk: one hidden τ (bfMsg(mNoBlocks)) to S-loop nIdle; no surviving visible event.
good-noblk .gnd = spec-nd-noblk
good-noblk .gτ st with S-noblk-τ st
... | refl = good-loop sIdle
good-noblk .gev st with Hide-ev-elim bfMsgES S-noblk st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-blk0: one hidden τ (bfMsg(mBlock b)) to S-loop (nStr1 b); no surviving visible event.
good-blk0 b .gnd = spec-nd-blk0
good-blk0 b .gτ st with S-blk0-τ st
... | refl = good-loop sStr1
good-blk0 b .gev st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-blk1: one hidden τ (bfMsg(mBlock b′)) to S-loop (nStr2 b b′); no surviving visible event.
good-blk1 b b′ .gnd = spec-nd-blk1
good-blk1 b b′ .gτ st with S-blk1-τ st
... | refl = good-loop sStr2
good-blk1 b b′ .gev st with Hide-ev-elim bfMsgES (S-blk1 b b′) st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-blk2: one hidden τ (bfMsg(mBlock b″)) to S-loop (nStr3 b b′ b″); no surviving visible event.
good-blk2 b b′ b″ .gnd = spec-nd-blk2
good-blk2 b b′ b″ .gτ st with S-blk2-τ st
... | refl = good-loop sStr3
good-blk2 b b′ b″ .gev st with Hide-ev-elim bfMsgES (S-blk2 b b′ b″) st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-bd0: one hidden τ (bfMsg(mBatchDone)) to S-loop nStrD0; no surviving visible event.
good-bd0 .gnd = spec-nd-bd0
good-bd0 .gτ st with S-bd0-τ st
... | refl = good-loop-strD0
good-bd0 .gev st with Hide-ev-elim bfMsgES S-bd0 st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-bd1: one hidden τ (bfMsg(mBatchDone)) to S-loop (nStrD1 b); no surviving visible event.
good-bd1 b .gnd = spec-nd-bd1
good-bd1 b .gτ st with S-bd1-τ st
... | refl = good-loop sStrD1
good-bd1 b .gev st with Hide-ev-elim bfMsgES (S-bd1 b) st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-bd2: one hidden τ (bfMsg(mBatchDone)) to S-loop (nStrD2 b b′); no surviving visible event.
good-bd2 b b′ .gnd = spec-nd-bd2
good-bd2 b b′ .gτ st with S-bd2-τ st
... | refl = good-loop sStrD2
good-bd2 b b′ .gev st with Hide-ev-elim bfMsgES (S-bd2 b b′) st
... | heV {e = bfMsg}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn}     P' ¬m (sVis {at = (_ , bfIn)}     refl ())
... | heV {e = bfOut}    P' ¬m (sVis {at = (_ , bfOut)}    refl ())
... | heV {e = apiBF m}  P' ¬m (sVis {at = (_ , apiBF m)}  refl ())
... | he√ ()

-- S-loop s: a single iter loop-back τ to IT s; force is a `sil`, no visible event.
good-loop {s} stbl .gnd = spec-nd-loop stbl
good-loop {s} stbl .gτ st with S-loop-τ st
... | refl = good-IT s
good-loop {s} stbl .gev st with Hide-ev-elim bfMsgES (S-loop s) st
... | heV P' ¬m (sVis () _)
... | he√ ()

-- S-loop nStrD0: a single iter loop-back τ to IT nStrD0; force is a `sil`, no visible event.
good-loop-strD0 .gnd = spec-nd-loop-strD0
good-loop-strD0 .gτ st with S-loop-τ {nStrD0} st
... | refl = good-IT nStrD0
good-loop-strD0 .gev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | heV P' ¬m (sVis () _)
... | he√ ()

-- the SPEC's initial hidden state is `IT nIdle ∖ bfMsgES = BFnetSpec ∖ bfMsgES`.
good-spec-init : Good (BFnetSpec NetOps.∖ bfMsgES)
good-spec-init = good-IT nIdle

-- no weakly-reachable state of the hidden SPEC diverges.
spec3-noDiv : ∀ {s W} → (BFnetSpec NetOps.∖ bfMsgES) ⟹⟨ s ⟩ W → ¬ Diverges W
spec3-noDiv = go-reach good-spec-init

------------------------------------------------------------------------
-- NETWORK side: networkBF ∖ ioBF.  Nested parallel + hide.
--   networkBF = Par ioBF mrg2 (Par ∅ES mrg cl sv) copyL ∖ ioBF
-- inner `⦀` (∅ES) never syncs; outer `∥⇘ ioBF ⇙` syncs on bfIn/bfOut with copy.
------------------------------------------------------------------------

-- the constant merge used by Par⊤ / ⦀.
mrg : Rr → Rr → Rr
mrg _ _ = Poly.tt
mrg2 : Rr → Rr → Rr
mrg2 _ _ = Poly.tt

-- client / server iteration at a state.
ICn : BFState → PTree BFNetEv (ExtI BFNetEv) Rr
ICn s = NetOps.iter netClient s
ISn : BFState → PTree BFNetEv (ExtI BFNetEv) Rr
ISn s = NetOps.iter netServer s

-- one step of the copy's `loop0` body (so we can name the copy states).
copyStep : Poly.⊤ {lzero} → PTree BFNetEv (ExtI BFNetEv) (Poly.⊤ {lzero} ⊎ Rr)
copyStep _ = NetOps.pchoice copyMenuL NetOps.>>= λ a′ → NetOps.Ret (inj₁ a′)

-- the copy idle state (≡ copyL = loop0 (pchoice copyMenuL)).
Cidle : PTree BFNetEv (ExtI BFNetEv) Rr
Cidle = NetOps.iter copyStep Poly.tt



-- copy-hold transient: after `bfIn?m`, the copy owes `bfOut\!m` then loops back.
Chold : BFMsg → PTree BFNetEv (ExtI BFNetEv) Rr
Chold m = NetOps.iter-bind
  (NetOps.Output bfOut m NetOps.Skip NetOps.>>= λ a′ → NetOps.Ret (inj₁ a′)) copyStep

-- inner = client ⦀ server (∅ES, never syncs).
Inner : PTree BFNetEv (ExtI BFNetEv) Rr → PTree BFNetEv (ExtI BFNetEv) Rr → PTree BFNetEv (ExtI BFNetEv) Rr
Inner cl sv = NetOps.Par ∅ES mrg cl sv

-- joint network state: (inner ∥⇘ ioBF ⇙ copy) ∖ ioBF.
JN : PTree BFNetEv (ExtI BFNetEv) Rr → PTree BFNetEv (ExtI BFNetEv) Rr → PTree BFNetEv (ExtI BFNetEv) Rr
JN inner cp = NetOps.Par ioBF mrg2 inner cp NetOps.∖ ioBF


-- the inner idle/idle peers offer no bfIn event (client sends bfIn only after an
-- apiBF; server receives on bfOut, not bfIn).
innerII-no-bfin : ∀ {a P'} → Inner (ICn stIdle) (ISn stIdle) ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► P' → ⊥
innerII-no-bfin ist with Par-ev-elim ∅ES mrg (ICn stIdle) (ISn stIdle) ist
... | evL ¬m2 (sVis {at = (_ , bfIn)} refl ())
... | evR ¬m2 (sVis {at = (_ , bfIn)} refl ())
... | evBoth ¬m2 (sVis {at = (_ , bfIn)} refl ()) cst2

-- the copy idle offers only bfIn? (not bfOut).
Cidle-no-bfout : ∀ {a Q'} → Cidle ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q' → ⊥
Cidle-no-bfout (sVis refl ())

-- A=(idle,idle,idle,copy idle): stable (all peers offer only apiBF; copy
-- offers bfIn? but no peer offers bfIn now, so no sync).
netA-noτ : ∀ {W″} → ¬ (JN (Inner (ICn stIdle) (ISn stIdle)) Cidle ─[ τ ]─► W″)
netA-noτ st with Hide-τ-elim ioBF (NetOps.Par ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle) st
... | hτP P' pst refl with Par-τ-elim ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle pst
...   | τL P'' ist refl with Par-τ-elim ∅ES mrg (ICn stIdle) (ISn stIdle) ist
...     | τL P3 (sSil ()) refl
...     | τL P3 (sTau refl ()) refl
...     | τR Q3 (sSil ()) refl
...     | τR Q3 (sTau refl ()) refl
netA-noτ st | hτP P' pst refl | τR Q'' (sSil ()) refl
netA-noτ st | hτP P' pst refl | τR Q'' (sTau refl ()) refl
netA-noτ st | hτH P' mem pev refl with Par-ev-elim ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle pev
...   | evL ¬m ist = ¬m mem
...   | evR ¬m cst = ¬m mem
...   | evBoth ¬m ist cst = ¬m mem
...   | evSync {e = bfMsg} m ist cst = ⊥-elim m
...   | evSync {e = apiBF mm} m ist cst = ⊥-elim m
...   | evSync {e = bfIn}  m ist cst = innerII-no-bfin ist
...   | evSync {e = bfOut} m ist cst = Cidle-no-bfout cst

------------------------------------------------------------------------
-- NETWORK transient terms: peer send-holds, recv-deliveries, notifies,
-- loop-backs, and the copy-hold.
------------------------------------------------------------------------

-- client send-hold (idle → busy): owes bfIn!(mRequestRange range), then loops to stBusy.
CB-req : ChainRange → PTree BFNetEv (ExtI BFNetEv) Rr
CB-req range = NetOps.iter-bind (NetOps.Output bfIn (mRequestRange range) (NetOps.Ret (inj₁ stBusy))) netClient

-- client send-hold (idle → done): owes bfIn!mClientDone, then loops to stDone.
CB-cdone : PTree BFNetEv (ExtI BFNetEv) Rr
CB-cdone = NetOps.iter-bind (NetOps.Output bfIn mClientDone (NetOps.Ret (inj₁ stDone))) netClient

-- client recv-deliver (streaming, owes recvBFBlock b): owes apiBF recvBFBlock!b, loops to stStreaming.
CB-blk : Block → PTree BFNetEv (ExtI BFNetEv) Rr
CB-blk b = NetOps.iter-bind (NetOps.Output (apiBF recvBFBlock) b (NetOps.Ret (inj₁ stStreaming))) netClient

-- client loop-back point (ret (inj₁ s) ⇒ sil (ICn s)).
CB-loop : BFState → PTree BFNetEv (ExtI BFNetEv) Rr
CB-loop s = NetOps.iter-bind (NetOps.Ret (inj₁ s)) netClient

-- server notify (idle → busy): owes apiBF reqBFRange!range, then loops to stBusy.
SB-req : ChainRange → PTree BFNetEv (ExtI BFNetEv) Rr
SB-req range = NetOps.iter-bind (NetOps.Output (apiBF reqBFRange) range (NetOps.Ret (inj₁ stBusy))) netServer

-- server send-hold (busy → streaming): owes bfIn!mStartBatch, then loops to stStreaming.
SB-sbatch : PTree BFNetEv (ExtI BFNetEv) Rr
SB-sbatch = NetOps.iter-bind (NetOps.Output bfIn mStartBatch (NetOps.Ret (inj₁ stStreaming))) netServer

-- server send-hold (busy → idle): owes bfIn!mNoBlocks, then loops to stIdle.
SB-noblk : PTree BFNetEv (ExtI BFNetEv) Rr
SB-noblk = NetOps.iter-bind (NetOps.Output bfIn mNoBlocks (NetOps.Ret (inj₁ stIdle))) netServer

-- server send-hold (streaming, send block b): owes bfIn!(mBlock b), loops to stStreaming.
SB-blk : Block → PTree BFNetEv (ExtI BFNetEv) Rr
SB-blk b = NetOps.iter-bind (NetOps.Output bfIn (mBlock b) (NetOps.Ret (inj₁ stStreaming))) netServer

-- server send-hold (streaming → idle, batch done): owes bfIn!mBatchDone, loops to stIdle.
SB-bdone : PTree BFNetEv (ExtI BFNetEv) Rr
SB-bdone = NetOps.iter-bind (NetOps.Output bfIn mBatchDone (NetOps.Ret (inj₁ stIdle))) netServer

-- server loop-back point (ret (inj₁ s) ⇒ sil (ISn s)).
SB-loop : BFState → PTree BFNetEv (ExtI BFNetEv) Rr
SB-loop s = NetOps.iter-bind (NetOps.Ret (inj₁ s)) netServer

------------------------------------------------------------------------
-- Copy medium step lemmas (reused at every message hop).
------------------------------------------------------------------------

-- copy loop-back transient: after bfOut\!m fires, Skip >>= loops back via iter-bind.
Cret : PTree BFNetEv (ExtI BFNetEv) Rr
Cret = NetOps.iter-bind (NetOps.Skip NetOps.>>= λ a′ → NetOps.Ret (inj₁ a′)) copyStep

-- copy idle has no τ.
Cidle-noτ : ∀ {Q'} → ¬ (Cidle ─[ τ ]─► Q')
Cidle-noτ (sSil ())
Cidle-noτ (sTau refl ())

-- copy idle receives bfIn?a, landing on Chold a.
Cidle-bfin : ∀ {a Q'} → Cidle ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q' → Q' ≡ Chold a
Cidle-bfin (sVis refl cstp) with cstp
... | refl = refl

-- copy idle offers no bfOut.
Cidle-no-bfout′ : ∀ {a Q'} → Cidle ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q' → ⊥
Cidle-no-bfout′ (sVis refl ())

-- copy-hold emits bfOut\!m (value forced to m), landing on Cret.
Chold-bfout : ∀ {m a Q'} → Chold m ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q' → (a ≡ m) × (Q' ≡ Cret)
Chold-bfout {m} {a} (sVis refl cstp) with a ≟ m
... | no _ with cstp
...   | ()
Chold-bfout {m} {a} (sVis refl cstp) | yes refl with cstp
...   | refl = refl , refl

-- copy-hold offers no bfIn.
Chold-no-bfin : ∀ {m a Q'} → Chold m ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q' → ⊥
Chold-no-bfin (sVis refl ())

-- copy-hold has no τ (it is a stable visible-only bfOut\! offer).
Chold-noτ : ∀ {m W″} → ¬ (Chold m ─[ τ ]─► W″)
Chold-noτ (sSil ())
Chold-noτ (sTau refl ())

-- Cret's only τ is the iter loop-back (sil) to Cidle.
Cret-τ : ∀ {W″} → Cret ─[ τ ]─► W″ → W″ ≡ Cidle
Cret-τ (sSil refl) = refl

-- Cret offers no visible event (its force is a sil).
Cret-no-ev : ∀ {e Q'} → Cret ─[ ev e ]─► Q' → ⊥
Cret-no-ev (sRet ())
Cret-no-ev (sVis () _)

------------------------------------------------------------------------
-- Inner-peer step lemmas: the inner Par ∅ES never syncs, so every inner
-- step is a solo evL (client) / evR (server).
------------------------------------------------------------------------

-- ICn stBusy / ICn stStreaming / ISn stIdle / ISn stStreaming RECEIVE on bfOut;
-- ICn stIdle / ISn stBusy / ISn stStreaming SEND on bfIn after an apiBF.

-- CB-loop s makes a single iter loop-back τ (sil) to ICn s; no other τ.
CBloop-τ : ∀ {s P''} → CB-loop s ─[ τ ]─► P'' → P'' ≡ ICn s
CBloop-τ (sSil refl) = refl

-- SB-loop s makes a single iter loop-back τ (sil) to ISn s; no other τ.
SBloop-τ : ∀ {s Q''} → SB-loop s ─[ τ ]─► Q'' → Q'' ≡ ISn s
SBloop-τ (sSil refl) = refl

-- CB-loop / SB-loop offer no visible event (force is a sil).
CBloop-no-ev : ∀ {s e P''} → CB-loop s ─[ ev e ]─► P'' → ⊥
CBloop-no-ev (sRet ())
CBloop-no-ev (sVis () _)
SBloop-no-ev : ∀ {s e Q''} → SB-loop s ─[ ev e ]─► Q'' → ⊥
SBloop-no-ev (sRet ())
SBloop-no-ev (sVis () _)

------------------------------------------------------------------------
-- Generic JN τ-decomposition: a τ of `JN (Inner cl sv) cp` is one of
--   • an inner client τ      (cl ─[τ]─► cl′),
--   • an inner server τ      (sv ─[τ]─► sv′),
--   • a copy τ               (cp ─[τ]─► cp′),
--   • a bfIn sync            (some peer sends bfIn\!a, copy receives), or
--   • a bfOut sync           (copy sends bfOut\!a, some peer receives).
-- Each carries the surviving sub-steps so per-config lemmas just pattern match.
------------------------------------------------------------------------

-- the decomposition result of a JN τ-step.
data JNτ (cl sv cp : PTree BFNetEv (ExtI BFNetEv) Rr) : PTree BFNetEv (ExtI BFNetEv) Rr → Set₁ where
  jClτ  : ∀ {cl′} → cl ─[ τ ]─► cl′ → JNτ cl sv cp (JN (Inner cl′ sv) cp)
  jSvτ  : ∀ {sv′} → sv ─[ τ ]─► sv′ → JNτ cl sv cp (JN (Inner cl sv′) cp)
  jCpτ  : ∀ {cp′} → cp ─[ τ ]─► cp′ → JNτ cl sv cp (JN (Inner cl sv) cp′)
  jInL  : ∀ {a cl′ cp′} → cl ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► cl′
        → cp ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► cp′
        → JNτ cl sv cp (JN (Inner cl′ sv) cp′)
  jInR  : ∀ {a sv′ cp′} → sv ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► sv′
        → cp ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► cp′
        → JNτ cl sv cp (JN (Inner cl sv′) cp′)
  -- both peers fire bfIn at once (refuted per-config); successor left opaque.
  jInB  : ∀ {a cl′ sv′ W} → cl ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► cl′
        → sv ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► sv′
        → JNτ cl sv cp W
  jOutL : ∀ {a cl′ cp′} → cp ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► cp′
        → cl ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► cl′
        → JNτ cl sv cp (JN (Inner cl′ sv) cp′)
  jOutR : ∀ {a sv′ cp′} → cp ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► cp′
        → sv ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► sv′
        → JNτ cl sv cp (JN (Inner cl sv′) cp′)
  -- both peers receive bfOut at once (refuted per-config); successor left opaque.
  jOutB : ∀ {a cl′ sv′ W} → cl ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► cl′
        → sv ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► sv′
        → JNτ cl sv cp W

-- the decomposition itself: invert the hide, the outer Par, and (for an inner τ
-- or an inner sync side) the inner Par.
JN-τ-cases : ∀ {cl sv cp W″} → JN (Inner cl sv) cp ─[ τ ]─► W″ → JNτ cl sv cp W″
JN-τ-cases {cl} {sv} {cp} st with Hide-τ-elim ioBF (NetOps.Par ioBF mrg2 (Inner cl sv) cp) st
... | hτP P' pst refl with Par-τ-elim ioBF mrg2 (Inner cl sv) cp pst
...   | τR Q'' cpst refl = jCpτ cpst
...   | τL P'' ist refl with Par-τ-elim ∅ES mrg cl sv ist
...     | τL P3 clst refl = jClτ clst
...     | τR Q3 svst refl = jSvτ svst
JN-τ-cases {cl} {sv} {cp} st | hτH P' mem pev refl with Par-ev-elim ioBF mrg2 (Inner cl sv) cp pev
...   | evL ¬m ist = ⊥-elim (¬m mem)
...   | evR ¬m cst = ⊥-elim (¬m mem)
...   | evBoth ¬m ist cst = ⊥-elim (¬m mem)
...   | evSync {e = bfMsg} m ist cst = ⊥-elim m
...   | evSync {e = apiBF mm} m ist cst = ⊥-elim m
...   | evSync {e = bfIn} {a = a} m ist cst with Par-ev-elim ∅ES mrg cl sv ist
...     | evL ¬m2 clst = jInL clst cst
...     | evR ¬m2 svst = jInR svst cst
...     | evBoth ¬m2 clst svst = jInB clst svst
JN-τ-cases {cl} {sv} {cp} st | hτH P' mem pev refl | evSync {e = bfOut} {a = a} m ist cst with Par-ev-elim ∅ES mrg cl sv ist
...     | evL ¬m2 clst = jOutL cst clst
...     | evR ¬m2 svst = jOutR cst svst
...     | evBoth ¬m2 clst svst = jOutB clst svst

------------------------------------------------------------------------
-- Generic JN visible-event decomposition.  A surviving visible event of
-- `JN (Inner cl sv) cp` is an apiBF (∉ ioBF), fired solo by the client or
-- the server inside the inner Par (copy offers only hidden bfIn/bfOut, and
-- apiBF cannot sync).  √ is impossible (the copy never returns).
------------------------------------------------------------------------

-- the decomposition result of a JN visible step (only apiBF survives hiding).
data JNev (cl sv cp : PTree BFNetEv (ExtI BFNetEv) Rr)
          : ∀ {X} → X → BFNetEv X → PTree BFNetEv (ExtI BFNetEv) Rr → Set₁ where
  jeClL : ∀ {m a cl′} → cl ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► cl′
        → JNev cl sv cp a (apiBF m) (JN (Inner cl′ sv) cp)
  jeSvR : ∀ {m a sv′} → sv ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► sv′
        → JNev cl sv cp a (apiBF m) (JN (Inner cl sv′) cp)
  -- both peers fire the same apiBF (refuted per-config; successor opaque).
  jeBoth : ∀ {m a cl′ sv′ W} → cl ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► cl′
        → sv ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► sv′
        → JNev cl sv cp a (apiBF m) W

-- a JN visible apiBF step decomposes to a client-solo / server-solo inner step;
-- the copy never offers apiBF (caller supplies `cpNoApi`).
JN-ev-apiBF : ∀ {cl sv cp m a W″}
            → (∀ {Q'} → cp ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q' → ⊥)
            → JN (Inner cl sv) cp ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► W″
            → JNev cl sv cp a (apiBF m) W″
JN-ev-apiBF {cl} {sv} {cp} {m} {a} cpNoApi st
  with Hide-ev-elim ioBF (NetOps.Par ioBF mrg2 (Inner cl sv) cp) st
... | heV P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner cl sv) cp pev
...   | evSync mm cstp sstp = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (cpNoApi cst)
...   | evBoth ¬m2 ist cst = ⊥-elim (cpNoApi cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg cl sv ist
...     | evL ¬m3 clst = jeClL clst
...     | evR ¬m3 svst = jeSvR svst
...     | evBoth ¬m3 clst svst = jeBoth clst svst

-- the copy states never offer an apiBF event.
Cidle-no-api : ∀ {m a Q'} → Cidle ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q' → ⊥
Cidle-no-api (sVis refl ())
Chold-no-api : ∀ {mm m a Q'} → Chold mm ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q' → ⊥
Chold-no-api (sVis refl ())
Cret-no-api : ∀ {m a Q'} → Cret ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q' → ⊥
Cret-no-api (sVis () _)

------------------------------------------------------------------------
-- Peer (client / server) iter-state step classifications.  Each peer state
-- offers exactly the events its protocol prescribes; these lemmas record the
-- successor term and refute the impossible offers.  Reused across configs.
------------------------------------------------------------------------

-- ICn stIdle: no τ; offers apiBF sendBFRequestRange\!r (→ CB-req r) / sendBFClientDone (→ CB-cdone);
-- no bfIn, no bfOut.
ICidle-noτ : ∀ {P''} → ¬ (ICn stIdle ─[ τ ]─► P'')
ICidle-noτ (sSil ())
ICidle-noτ (sTau refl ())
ICidle-no-bfin : ∀ {a P''} → ICn stIdle ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► P'' → ⊥
ICidle-no-bfin (sVis refl ())
ICidle-no-bfout : ∀ {a P''} → ICn stIdle ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► P'' → ⊥
ICidle-no-bfout (sVis refl ())

-- ISn stIdle: no τ; RECEIVES bfOut (mRequestRange r → SB-req r, mClientDone → SB-loop stDone);
-- no bfIn, no apiBF.
ISidle-noτ : ∀ {Q''} → ¬ (ISn stIdle ─[ τ ]─► Q'')
ISidle-noτ (sSil ())
ISidle-noτ (sTau refl ())
ISidle-no-bfin : ∀ {a Q''} → ISn stIdle ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → ⊥
ISidle-no-bfin (sVis refl ())
ISidle-no-api : ∀ {m a Q''} → ISn stIdle ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q'' → ⊥
ISidle-no-api (sVis refl ())

-- ISn stIdle receiving bfOut: mRequestRange r → SB-req r; mClientDone → SB-loop stDone; others refuted.
ISidle-bfout : ∀ {a Q''} → ISn stIdle ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q''
             → (Σ[ r ∈ ChainRange ] (a ≡ mRequestRange r) × (Q'' ≡ SB-req r))
             ⊎ ((a ≡ mClientDone) × (Q'' ≡ SB-loop stDone))
ISidle-bfout {mRequestRange r} (sVis refl q) with q
... | refl = inj₁ (r , refl , refl)
ISidle-bfout {mClientDone} (sVis refl q) with q
... | refl = inj₂ (refl , refl)
ISidle-bfout {mStartBatch} (sVis refl ())
ISidle-bfout {mNoBlocks} (sVis refl ())
ISidle-bfout {mBlock b} (sVis refl ())
ISidle-bfout {mBatchDone} (sVis refl ())

-- ICn stIdle apiBF classification: sendBFRequestRange\!r → CB-req r; sendBFClientDone → CB-cdone; others refuted.
ICidle-api : ∀ {m a P''} → ICn stIdle ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► P''
           → (Σ[ r ∈ ChainRange ] (m ≡ sendBFRequestRange) × (P'' ≡ CB-req r))
           ⊎ ((m ≡ sendBFClientDone) × (P'' ≡ CB-cdone))
ICidle-api {sendBFRequestRange} {a} (sVis refl p) with p
... | refl = inj₁ (a , refl , refl)
ICidle-api {sendBFClientDone} (sVis refl p) with p
... | refl = inj₂ (refl , refl)
ICidle-api {sendBFStartBatch} (sVis refl ())
ICidle-api {sendBFNoBlocks} (sVis refl ())
ICidle-api {sendBFBlock} (sVis refl ())
ICidle-api {sendBFBatchDone} (sVis refl ())
ICidle-api {recvBFBlock} (sVis refl ())
ICidle-api {reqBFRange} (sVis refl ())

------------------------------------------------------------------------
-- Send-hold / recv-deliver / notify peer step lemmas.
------------------------------------------------------------------------

-- CB-req r: send-hold; only bfIn\!(mRequestRange r) (→ CB-loop stBusy); no τ, no bfOut, no apiBF.
CBreq-noτ : ∀ {r P''} → ¬ (CB-req r ─[ τ ]─► P'')
CBreq-noτ (sSil ())
CBreq-noτ (sTau refl ())
CBreq-bfin : ∀ {r a P''} → CB-req r ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► P'' → (a ≡ mRequestRange r) × (P'' ≡ CB-loop stBusy)
CBreq-bfin {r} {a} (sVis refl p) with a ≟ mRequestRange r
... | no _ with p
...   | ()
CBreq-bfin {r} {a} (sVis refl p) | yes refl with p
...   | refl = refl , refl
CBreq-no-bfout : ∀ {r a P''} → CB-req r ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► P'' → ⊥
CBreq-no-bfout (sVis refl ())
CBreq-no-api : ∀ {r m a P''} → CB-req r ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► P'' → ⊥
CBreq-no-api (sVis refl ())

-- CB-cdone: send-hold; only bfIn\!mClientDone (→ CB-loop stDone); no τ, no bfOut, no apiBF.
CBcdone-noτ : ∀ {P''} → ¬ (CB-cdone ─[ τ ]─► P'')
CBcdone-noτ (sSil ())
CBcdone-noτ (sTau refl ())
CBcdone-bfin : ∀ {a P''} → CB-cdone ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► P'' → (a ≡ mClientDone) × (P'' ≡ CB-loop stDone)
CBcdone-bfin {a} (sVis refl p) with a ≟ mClientDone
... | no _ with p
...   | ()
CBcdone-bfin {a} (sVis refl p) | yes refl with p
...   | refl = refl , refl
CBcdone-no-bfout : ∀ {a P''} → CB-cdone ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► P'' → ⊥
CBcdone-no-bfout (sVis refl ())
CBcdone-no-api : ∀ {m a P''} → CB-cdone ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► P'' → ⊥
CBcdone-no-api (sVis refl ())

-- SB-req r: notify; only apiBF reqBFRange\!r (→ SB-loop stBusy); no τ, no bfIn, no bfOut.
SBreq-noτ : ∀ {r Q''} → ¬ (SB-req r ─[ τ ]─► Q'')
SBreq-noτ (sSil ())
SBreq-noτ (sTau refl ())
SBreq-api : ∀ {r m a Q''} → SB-req r ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q'' → (m ≡ reqBFRange) × (Q'' ≡ SB-loop stBusy)
SBreq-api {r} {reqBFRange} {a} (sVis refl q) with a ≟ r
... | no _ with q
...   | ()
SBreq-api {r} {reqBFRange} {a} (sVis refl q) | yes refl with q
...   | refl = refl , refl
SBreq-api {r} {sendBFRequestRange} (sVis refl ())
SBreq-api {r} {sendBFClientDone} (sVis refl ())
SBreq-api {r} {sendBFStartBatch} (sVis refl ())
SBreq-api {r} {sendBFNoBlocks} (sVis refl ())
SBreq-api {r} {sendBFBlock} (sVis refl ())
SBreq-api {r} {sendBFBatchDone} (sVis refl ())
SBreq-api {r} {recvBFBlock} (sVis refl ())
SBreq-no-bfin : ∀ {r a Q''} → SB-req r ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → ⊥
SBreq-no-bfin (sVis refl ())
SBreq-no-bfout : ∀ {r a Q''} → SB-req r ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q'' → ⊥
SBreq-no-bfout (sVis refl ())

------------------------------------------------------------------------
-- Request-routing configs: client sends mRequestRange, server gets notify.
--   B  = (CB-req r,        ISn stIdle, Cidle)              -- client send-hold
--   Bh = (CB-loop stBusy,  ISn stIdle, Chold(mReqRange r)) -- copy holds the request
--   B2 = (ICn stBusy,      ISn stIdle, Chold(mReqRange r)) -- client looped back
--   B3 = (CB-loop stBusy,  SB-req r,   Cret)                -- server got notify, copy draining
--   B4 = (ICn stBusy,      SB-req r,   Cret)                -- client looped back too
--   B5 = (CB-loop stBusy,  SB-req r,   Cidle)               -- copy drained
--   B6 = (ICn stBusy,      SB-req r,   Cidle)               -- client looped back
--   F  = (ICn stBusy,      SB-loop stBusy, Cidle)           -- after notify api fires
--   then both busy → J.
------------------------------------------------------------------------

-- B → Bh by the bfIn sync (client send-hold drains into the copy).
netB-τ : ∀ {r W″} → JN (Inner (CB-req r) (ISn stIdle)) Cidle ─[ τ ]─► W″
       → W″ ≡ JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r))
netB-τ {r} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBreq-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst = ⊥-elim (λ-Cidle cpst)
      where λ-Cidle : ∀ {Q'} → Cidle ─[ τ ]─► Q' → ⊥
            λ-Cidle (sSil ())
            λ-Cidle (sTau refl ())
... | jInL clst cst with CBreq-bfin clst | Cidle-bfin cst
...   | (refl , refl) | refl = refl
netB-τ {r} st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netB-τ {r} st | jInB clst svst = ⊥-elim (ISidle-no-bfin svst)
netB-τ {r} st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netB-τ {r} st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netB-τ {r} st | jOutB clst svst = ⊥-elim (CBreq-no-bfout clst)

-- ICn stBusy: no τ; RECEIVES bfOut (mStartBatch → CB-loop stStreaming, mNoBlocks → CB-loop stIdle);
-- no bfIn, no apiBF.
ICbusy-noτ : ∀ {P''} → ¬ (ICn stBusy ─[ τ ]─► P'')
ICbusy-noτ (sSil ())
ICbusy-noτ (sTau refl ())
ICbusy-no-bfin : ∀ {a P''} → ICn stBusy ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► P'' → ⊥
ICbusy-no-bfin (sVis refl ())
ICbusy-no-api : ∀ {m a P''} → ICn stBusy ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► P'' → ⊥
ICbusy-no-api (sVis refl ())
ICbusy-bfout : ∀ {a P''} → ICn stBusy ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► P''
             → ((a ≡ mStartBatch) × (P'' ≡ CB-loop stStreaming)) ⊎ ((a ≡ mNoBlocks) × (P'' ≡ CB-loop stIdle))
ICbusy-bfout {mStartBatch} (sVis refl p) with p
... | refl = inj₁ (refl , refl)
ICbusy-bfout {mNoBlocks} (sVis refl p) with p
... | refl = inj₂ (refl , refl)
ICbusy-bfout {mRequestRange r} (sVis refl ())
ICbusy-bfout {mClientDone} (sVis refl ())
ICbusy-bfout {mBlock b} (sVis refl ())
ICbusy-bfout {mBatchDone} (sVis refl ())

-- ISn stBusy: no τ; offers apiBF sendBFStartBatch (→ SB-sbatch) / sendBFNoBlocks (→ SB-noblk);
-- no bfIn, no bfOut.
ISbusy-noτ : ∀ {Q''} → ¬ (ISn stBusy ─[ τ ]─► Q'')
ISbusy-noτ (sSil ())
ISbusy-noτ (sTau refl ())
ISbusy-no-bfin : ∀ {a Q''} → ISn stBusy ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → ⊥
ISbusy-no-bfin (sVis refl ())
ISbusy-no-bfout : ∀ {a Q''} → ISn stBusy ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q'' → ⊥
ISbusy-no-bfout (sVis refl ())
ISbusy-api : ∀ {m a Q''} → ISn stBusy ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q''
           → ((m ≡ sendBFStartBatch) × (Q'' ≡ SB-sbatch)) ⊎ ((m ≡ sendBFNoBlocks) × (Q'' ≡ SB-noblk))
ISbusy-api {sendBFStartBatch} (sVis refl q) with q
... | refl = inj₁ (refl , refl)
ISbusy-api {sendBFNoBlocks} (sVis refl q) with q
... | refl = inj₂ (refl , refl)
ISbusy-api {sendBFRequestRange} (sVis refl ())
ISbusy-api {sendBFClientDone} (sVis refl ())
ISbusy-api {sendBFBlock} (sVis refl ())
ISbusy-api {sendBFBatchDone} (sVis refl ())
ISbusy-api {recvBFBlock} (sVis refl ())
ISbusy-api {reqBFRange} (sVis refl ())

-- ICn stDone / ISn stDone: terminal; force is `ret`, so a √ but no τ / visible apiBF / bfIn / bfOut.
ICdone-noτ : ∀ {P''} → ¬ (ICn stDone ─[ τ ]─► P'')
ICdone-noτ (sSil ())
ICdone-noτ (sTau () _)
ISdone-noτ : ∀ {Q''} → ¬ (ISn stDone ─[ τ ]─► Q'')
ISdone-noτ (sSil ())
ISdone-noτ (sTau () _)
ICdone-no-bfin : ∀ {a P''} → ICn stDone ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► P'' → ⊥
ICdone-no-bfin (sVis () _)
ICdone-no-bfout : ∀ {a P''} → ICn stDone ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► P'' → ⊥
ICdone-no-bfout (sVis () _)
ICdone-no-api : ∀ {m a P''} → ICn stDone ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► P'' → ⊥
ICdone-no-api (sVis () _)
ISdone-no-bfin : ∀ {a Q''} → ISn stDone ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → ⊥
ISdone-no-bfin (sVis () _)
ISdone-no-bfout : ∀ {a Q''} → ISn stDone ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q'' → ⊥
ISdone-no-bfout (sVis () _)
ISdone-no-api : ∀ {m a Q''} → ISn stDone ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q'' → ⊥
ISdone-no-api (sVis () _)

-- Bh = (CB-loop stBusy, ISn stIdle, Chold(mReqRange r)): two τ's — client loop-back (→ B2)
-- and the bfOut sync draining the copy into the server's notify (→ B3).
netBh-τ : ∀ {r W″} → JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)))
        ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (SB-req r)) Cret)
netBh-τ {r} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netBh-τ {r} st | jSvτ svst = ⊥-elim (ISidle-noτ svst)
netBh-τ {r} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netBh-τ {r} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netBh-τ {r} st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netBh-τ {r} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netBh-τ {r} st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netBh-τ {r} st | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (r2 , refl , refl) = inj₂ refl
...     | inj₂ (() , _)
netBh-τ {r} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- B2 = (ICn stBusy, ISn stIdle, Chold(mReqRange r)): one τ — bfOut sync (→ B4).
netB2-τ : ∀ {r W″} → JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) (SB-req r)) Cret
netB2-τ {r} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
... | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
... | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICbusy-bfout clst
...     | inj₁ (() , _)
...     | inj₂ (() , _)
netB2-τ {r} st | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (r2 , refl , refl) = refl
...     | inj₂ (() , _)
netB2-τ {r} st | jOutB clst svst with ICbusy-bfout clst
...   | inj₁ (refl , _) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)
netB2-τ {r} st | jOutB clst svst | inj₂ (refl , _) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)

-- B3 = (CB-loop stBusy, SB-req r, Cret): two τ's — client loop-back (→ B3a) and copy loop-back (→ B5).
netB3-τ : ∀ {r W″} → JN (Inner (CB-loop stBusy) (SB-req r)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stBusy) (SB-req r)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (SB-req r)) Cidle)
netB3-τ {r} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netB3-τ {r} st | jSvτ svst = ⊥-elim (SBreq-noτ svst)
netB3-τ {r} st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netB3-τ {r} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netB3-τ {r} st | jInR svst cst = ⊥-elim (SBreq-no-bfin svst)
netB3-τ {r} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netB3-τ {r} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netB3-τ {r} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netB3-τ {r} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- B3a = (ICn stBusy, SB-req r, Cret): one τ — copy loop-back (→ B4').
netB3a-τ : ∀ {r W″} → JN (Inner (ICn stBusy) (SB-req r)) Cret ─[ τ ]─► W″
         → W″ ≡ JN (Inner (ICn stBusy) (SB-req r)) Cidle
netB3a-τ {r} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (SBreq-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netB3a-τ {r} st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netB3a-τ {r} st | jInR svst cst = ⊥-elim (SBreq-no-bfin svst)
netB3a-τ {r} st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netB3a-τ {r} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netB3a-τ {r} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netB3a-τ {r} st | jOutB clst svst = ⊥-elim (SBreq-no-bfout svst)

-- B5 = (CB-loop stBusy, SB-req r, Cidle): one τ — client loop-back (→ B4').
netB5-τ : ∀ {r W″} → JN (Inner (CB-loop stBusy) (SB-req r)) Cidle ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) (SB-req r)) Cidle
netB5-τ {r} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netB5-τ {r} st | jSvτ svst = ⊥-elim (SBreq-noτ svst)
netB5-τ {r} st | jCpτ cpst = ⊥-elim (Cidle-noτ′ cpst)
      where Cidle-noτ′ : ∀ {Q'} → Cidle ─[ τ ]─► Q' → ⊥
            Cidle-noτ′ (sSil ())
            Cidle-noτ′ (sTau refl ())
netB5-τ {r} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netB5-τ {r} st | jInR svst cst = ⊥-elim (SBreq-no-bfin svst)
netB5-τ {r} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netB5-τ {r} st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netB5-τ {r} st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netB5-τ {r} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- B4 = (ICn stBusy, SB-req r, Cidle): STABLE; server offers reqBFRange api (solo), client awaits bfOut (none).
netB4-noτ : ∀ {r W″} → ¬ (JN (Inner (ICn stBusy) (SB-req r)) Cidle ─[ τ ]─► W″)
netB4-noτ {r} st with JN-τ-cases st
... | jClτ clst = ICbusy-noτ clst
... | jSvτ svst = SBreq-noτ svst
... | jCpτ cpst = Cidle-noτ cpst
... | jInL clst cst = ICbusy-no-bfin clst
... | jInR svst cst = SBreq-no-bfin svst
... | jInB clst svst = ICbusy-no-bfin clst
... | jOutL cst clst = Cidle-no-bfout′ cst
... | jOutR cst svst = Cidle-no-bfout′ cst
... | jOutB clst svst = SBreq-no-bfout svst

-- Fl = (ICn stBusy, SB-loop stBusy, Cidle): one τ — server loop-back (→ Jbusy).
netFl-τ : ∀ {W″} → JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) (ISn stBusy)) Cidle
netFl-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netFl-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netFl-τ st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netFl-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netFl-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netFl-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netFl-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netFl-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- Jbusy = (ICn stBusy, ISn stBusy, Cidle): STABLE; server offers sbatch/noblk apis (solo).
netJ-noτ : ∀ {W″} → ¬ (JN (Inner (ICn stBusy) (ISn stBusy)) Cidle ─[ τ ]─► W″)
netJ-noτ st with JN-τ-cases st
... | jClτ clst = ICbusy-noτ clst
... | jSvτ svst = ISbusy-noτ svst
... | jCpτ cpst = Cidle-noτ cpst
... | jInL clst cst = ICbusy-no-bfin clst
... | jInR svst cst = ISbusy-no-bfin svst
... | jInB clst svst = ICbusy-no-bfin clst
... | jOutL cst clst = Cidle-no-bfout′ cst
... | jOutR cst svst = Cidle-no-bfout′ cst
... | jOutB clst svst = ISbusy-no-bfout svst

------------------------------------------------------------------------
-- Done-routing configs: client sends mClientDone, server goes to stDone.
------------------------------------------------------------------------

-- Cdone = (CB-cdone, ISn stIdle, Cidle): one τ — bfIn sync (→ Cdh).
netCdone-τ : ∀ {W″} → JN (Inner CB-cdone (ISn stIdle)) Cidle ─[ τ ]─► W″
           → W″ ≡ JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone)
netCdone-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBcdone-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
... | jInL clst cst with CBcdone-bfin clst | Cidle-bfin cst
...   | (refl , refl) | refl = refl
netCdone-τ st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netCdone-τ st | jInB clst svst = ⊥-elim (ISidle-no-bfin svst)
netCdone-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netCdone-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netCdone-τ st | jOutB clst svst = ⊥-elim (CBcdone-no-bfout clst)

-- Cdh = (CB-loop stDone, ISn stIdle, Chold mClientDone): two τ's — client loop-back (→ Cd2),
-- bfOut sync (→ Cd3).
netCdh-τ : ∀ {W″} → JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone) ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone))
         ⊎ (W″ ≡ JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret)
netCdh-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netCdh-τ st | jSvτ svst = ⊥-elim (ISidle-noτ svst)
netCdh-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netCdh-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netCdh-τ st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netCdh-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netCdh-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netCdh-τ st | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (refl , refl) = inj₂ refl
netCdh-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- Cd2 = (ICn stDone, ISn stIdle, Chold mClientDone): one τ — bfOut sync (→ Cd4).
netCd2-τ : ∀ {W″} → JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone) ─[ τ ]─► W″
         → W″ ≡ JN (Inner (ICn stDone) (SB-loop stDone)) Cret
netCd2-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICdone-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICdone-no-bfin clst)
... | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
... | jInB clst svst = ⊥-elim (ICdone-no-bfin clst)
... | jOutL cst clst = ⊥-elim (ICdone-no-bfout clst)
... | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (refl , refl) = refl
netCd2-τ st | jOutB clst svst = ⊥-elim (ICdone-no-bfout clst)

-- Cd3 = (CB-loop stDone, SB-loop stDone, Cret): three τ's — client loop (→ Cd4), server loop (→ Cd5),
-- copy loop (→ Cd6).
netCd3-τ : ∀ {W″} → JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stDone) (SB-loop stDone)) Cret)
         ⊎ (W″ ≡ JN (Inner (CB-loop stDone) (ISn stDone)) Cret)
         ⊎ (W″ ≡ JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle)
netCd3-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netCd3-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ (inj₁ refl)
netCd3-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ (inj₂ refl)
netCd3-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netCd3-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netCd3-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netCd3-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netCd3-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netCd3-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- Cd4 = (ICn stDone, SB-loop stDone, Cret): server loop (→ Cd7) / copy loop (→ Cd8).
netCd4-τ : ∀ {W″} → JN (Inner (ICn stDone) (SB-loop stDone)) Cret ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stDone) (ISn stDone)) Cret)
         ⊎ (W″ ≡ JN (Inner (ICn stDone) (SB-loop stDone)) Cidle)
netCd4-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICdone-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netCd4-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netCd4-τ st | jInL clst cst = ⊥-elim (ICdone-no-bfin clst)
netCd4-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netCd4-τ st | jInB clst svst = ⊥-elim (ICdone-no-bfin clst)
netCd4-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netCd4-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netCd4-τ st | jOutB clst svst = ⊥-elim (ICdone-no-bfout clst)

-- Cd5 = (CB-loop stDone, ISn stDone, Cret): client loop (→ Cd7) / copy loop (→ Cd9).
netCd5-τ : ∀ {W″} → JN (Inner (CB-loop stDone) (ISn stDone)) Cret ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stDone) (ISn stDone)) Cret)
         ⊎ (W″ ≡ JN (Inner (CB-loop stDone) (ISn stDone)) Cidle)
netCd5-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netCd5-τ st | jSvτ svst = ⊥-elim (ISdone-noτ svst)
netCd5-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netCd5-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netCd5-τ st | jInR svst cst = ⊥-elim (ISdone-no-bfin svst)
netCd5-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netCd5-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netCd5-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netCd5-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- Cd6 = (CB-loop stDone, SB-loop stDone, Cidle): client loop (→ Cd8) / server loop (→ Cd9).
netCd6-τ : ∀ {W″} → JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stDone) (SB-loop stDone)) Cidle)
         ⊎ (W″ ≡ JN (Inner (CB-loop stDone) (ISn stDone)) Cidle)
netCd6-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netCd6-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netCd6-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netCd6-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netCd6-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netCd6-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netCd6-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netCd6-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netCd6-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- Cd7 = (ICn stDone, ISn stDone, Cret): one τ — copy loop (→ Zdone).
netCd7-τ : ∀ {W″} → JN (Inner (ICn stDone) (ISn stDone)) Cret ─[ τ ]─► W″
         → W″ ≡ JN (Inner (ICn stDone) (ISn stDone)) Cidle
netCd7-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICdone-noτ clst)
... | jSvτ svst = ⊥-elim (ISdone-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netCd7-τ st | jInL clst cst = ⊥-elim (ICdone-no-bfin clst)
netCd7-τ st | jInR svst cst = ⊥-elim (ISdone-no-bfin svst)
netCd7-τ st | jInB clst svst = ⊥-elim (ICdone-no-bfin clst)
netCd7-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netCd7-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netCd7-τ st | jOutB clst svst = ⊥-elim (ICdone-no-bfout clst)

-- Cd8 = (ICn stDone, SB-loop stDone, Cidle): one τ — server loop (→ Zdone).
netCd8-τ : ∀ {W″} → JN (Inner (ICn stDone) (SB-loop stDone)) Cidle ─[ τ ]─► W″
         → W″ ≡ JN (Inner (ICn stDone) (ISn stDone)) Cidle
netCd8-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICdone-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netCd8-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netCd8-τ st | jInL clst cst = ⊥-elim (ICdone-no-bfin clst)
netCd8-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netCd8-τ st | jInB clst svst = ⊥-elim (ICdone-no-bfin clst)
netCd8-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netCd8-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netCd8-τ st | jOutB clst svst = ⊥-elim (ICdone-no-bfout clst)

-- Cd9 = (CB-loop stDone, ISn stDone, Cidle): one τ — client loop (→ Zdone).
netCd9-τ : ∀ {W″} → JN (Inner (CB-loop stDone) (ISn stDone)) Cidle ─[ τ ]─► W″
         → W″ ≡ JN (Inner (ICn stDone) (ISn stDone)) Cidle
netCd9-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netCd9-τ st | jSvτ svst = ⊥-elim (ISdone-noτ svst)
netCd9-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netCd9-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netCd9-τ st | jInR svst cst = ⊥-elim (ISdone-no-bfin svst)
netCd9-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netCd9-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netCd9-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netCd9-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- Zdone = (ICn stDone, ISn stDone, Cidle): terminal stable — no τ at all (copy idle blocks √).
netZ-noτ : ∀ {W″} → ¬ (JN (Inner (ICn stDone) (ISn stDone)) Cidle ─[ τ ]─► W″)
netZ-noτ st with JN-τ-cases st
... | jClτ clst = ICdone-noτ clst
... | jSvτ svst = ISdone-noτ svst
... | jCpτ cpst = Cidle-noτ cpst
... | jInL clst cst = ICdone-no-bfin clst
... | jInR svst cst = ISdone-no-bfin svst
... | jInB clst svst = ICdone-no-bfin clst
... | jOutL cst clst = Cidle-no-bfout′ cst
... | jOutR cst svst = Cidle-no-bfout′ cst
... | jOutB clst svst = ICdone-no-bfout clst

-- SB-sbatch: send-hold; only bfIn\!mStartBatch (→ SB-loop stStreaming); no τ, no bfOut, no apiBF.
SBsbatch-noτ : ∀ {Q''} → ¬ (SB-sbatch ─[ τ ]─► Q'')
SBsbatch-noτ (sSil ())
SBsbatch-noτ (sTau refl ())
SBsbatch-bfin : ∀ {a Q''} → SB-sbatch ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → (a ≡ mStartBatch) × (Q'' ≡ SB-loop stStreaming)
SBsbatch-bfin {a} (sVis refl q) with a ≟ mStartBatch
... | no _ with q
...   | ()
SBsbatch-bfin {a} (sVis refl q) | yes refl with q
...   | refl = refl , refl
SBsbatch-no-bfout : ∀ {a Q''} → SB-sbatch ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q'' → ⊥
SBsbatch-no-bfout (sVis refl ())
SBsbatch-no-api : ∀ {m a Q''} → SB-sbatch ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q'' → ⊥
SBsbatch-no-api (sVis refl ())

-- SB-noblk: send-hold; only bfIn\!mNoBlocks (→ SB-loop stIdle); no τ, no bfOut, no apiBF.
SBnoblk-noτ : ∀ {Q''} → ¬ (SB-noblk ─[ τ ]─► Q'')
SBnoblk-noτ (sSil ())
SBnoblk-noτ (sTau refl ())
SBnoblk-bfin : ∀ {a Q''} → SB-noblk ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → (a ≡ mNoBlocks) × (Q'' ≡ SB-loop stIdle)
SBnoblk-bfin {a} (sVis refl q) with a ≟ mNoBlocks
... | no _ with q
...   | ()
SBnoblk-bfin {a} (sVis refl q) | yes refl with q
...   | refl = refl , refl
SBnoblk-no-bfout : ∀ {a Q''} → SB-noblk ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q'' → ⊥
SBnoblk-no-bfout (sVis refl ())
SBnoblk-no-api : ∀ {m a Q''} → SB-noblk ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q'' → ⊥
SBnoblk-no-api (sVis refl ())

-- ISn stStreaming: no τ; offers apiBF sendBFBlock\!b (→ SB-blk b) / sendBFBatchDone (→ SB-bdone);
-- no bfIn, no bfOut.
ISstr-noτ : ∀ {Q''} → ¬ (ISn stStreaming ─[ τ ]─► Q'')
ISstr-noτ (sSil ())
ISstr-noτ (sTau refl ())
ISstr-no-bfin : ∀ {a Q''} → ISn stStreaming ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → ⊥
ISstr-no-bfin (sVis refl ())
ISstr-no-bfout : ∀ {a Q''} → ISn stStreaming ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q'' → ⊥
ISstr-no-bfout (sVis refl ())
ISstr-api : ∀ {m a Q''} → ISn stStreaming ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q''
          → (Σ[ b ∈ Block ] (m ≡ sendBFBlock) × (Q'' ≡ SB-blk b)) ⊎ ((m ≡ sendBFBatchDone) × (Q'' ≡ SB-bdone))
ISstr-api {sendBFBlock} {a} (sVis refl q) with q
... | refl = inj₁ (a , refl , refl)
ISstr-api {sendBFBatchDone} (sVis refl q) with q
... | refl = inj₂ (refl , refl)
ISstr-api {sendBFRequestRange} (sVis refl ())
ISstr-api {sendBFClientDone} (sVis refl ())
ISstr-api {sendBFStartBatch} (sVis refl ())
ISstr-api {sendBFNoBlocks} (sVis refl ())
ISstr-api {recvBFBlock} (sVis refl ())
ISstr-api {reqBFRange} (sVis refl ())

-- ICn stStreaming: no τ; RECEIVES bfOut (mBlock b → CB-blk b, mBatchDone → CB-loop stIdle);
-- no bfIn, no apiBF.
ICstr-noτ : ∀ {P''} → ¬ (ICn stStreaming ─[ τ ]─► P'')
ICstr-noτ (sSil ())
ICstr-noτ (sTau refl ())
ICstr-no-bfin : ∀ {a P''} → ICn stStreaming ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► P'' → ⊥
ICstr-no-bfin (sVis refl ())
ICstr-no-api : ∀ {m a P''} → ICn stStreaming ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► P'' → ⊥
ICstr-no-api (sVis refl ())
ICstr-bfout : ∀ {a P''} → ICn stStreaming ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► P''
            → (Σ[ b ∈ Block ] (a ≡ mBlock b) × (P'' ≡ CB-blk b)) ⊎ ((a ≡ mBatchDone) × (P'' ≡ CB-loop stIdle))
ICstr-bfout {mBlock b} (sVis refl p) with p
... | refl = inj₁ (b , refl , refl)
ICstr-bfout {mBatchDone} (sVis refl p) with p
... | refl = inj₂ (refl , refl)
ICstr-bfout {mRequestRange r} (sVis refl ())
ICstr-bfout {mClientDone} (sVis refl ())
ICstr-bfout {mStartBatch} (sVis refl ())
ICstr-bfout {mNoBlocks} (sVis refl ())

------------------------------------------------------------------------
-- Busy→streaming (sbatch) and busy→idle (noblk) routing.
------------------------------------------------------------------------

-- M = (ICn stBusy, SB-sbatch, Cidle): one τ — bfIn sync (→ Mh).
netM-τ : ∀ {W″} → JN (Inner (ICn stBusy) SB-sbatch) Cidle ─[ τ ]─► W″
       → W″ ≡ JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch)
netM-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (SBsbatch-noτ svst)
... | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
... | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
... | jInR svst cst with SBsbatch-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = refl
netM-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netM-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netM-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netM-τ st | jOutB clst svst = ⊥-elim (SBsbatch-no-bfout svst)

-- Mh = (ICn stBusy, SB-loop stStreaming, Chold mStartBatch): server loop (→ M2) / bfOut sync (→ M3).
netMh-τ : ∀ {W″} → JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch))
        ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret)
netMh-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netMh-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netMh-τ st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netMh-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netMh-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netMh-τ st | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICbusy-bfout clst
...     | inj₁ (refl , refl) = inj₂ refl
...     | inj₂ (() , _)
netMh-τ st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netMh-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- M2 = (ICn stBusy, ISn stStreaming, Chold mStartBatch): one τ — bfOut sync (→ M4).
netM2-τ : ∀ {W″} → JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret
netM2-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (ISstr-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
... | jInR svst cst = ⊥-elim (ISstr-no-bfin svst)
... | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICbusy-bfout clst
...     | inj₁ (refl , refl) = refl
...     | inj₂ (() , _)
netM2-τ st | jOutR cst svst = ⊥-elim (ISstr-no-bfout svst)
netM2-τ st | jOutB clst svst = ⊥-elim (ISstr-no-bfout svst)

-- M3 = (CB-loop stStreaming, SB-loop stStreaming, Cret): client/server/copy loops → M4 / M5 / M6.
netM3-τ : ∀ {W″} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle)
netM3-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netM3-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ (inj₁ refl)
netM3-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ (inj₂ refl)
netM3-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netM3-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netM3-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netM3-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netM3-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netM3-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- M4 = (ICn stStreaming, SB-loop stStreaming, Cret): server loop (→ M7) / copy loop (→ M8).
netM4-τ : ∀ {W″} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret)
        ⊎ (W″ ≡ JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle)
netM4-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netM4-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netM4-τ st | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
netM4-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netM4-τ st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netM4-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netM4-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netM4-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- M5 = (CB-loop stStreaming, ISn stStreaming, Cret): client loop (→ M7) / copy loop (→ M9).
netM5-τ : ∀ {W″} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle)
netM5-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netM5-τ st | jSvτ svst = ⊥-elim (ISstr-noτ svst)
netM5-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netM5-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netM5-τ st | jInR svst cst = ⊥-elim (ISstr-no-bfin svst)
netM5-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netM5-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netM5-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netM5-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- M6 = (CB-loop stStreaming, SB-loop stStreaming, Cidle): client loop (→ M8) / server loop (→ M9).
netM6-τ : ∀ {W″} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle)
        ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle)
netM6-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netM6-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netM6-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netM6-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netM6-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netM6-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netM6-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netM6-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netM6-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- M7 = (ICn stStreaming, ISn stStreaming, Cret): copy loop (→ V0).
netM7-τ : ∀ {W″} → JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle
netM7-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (ISstr-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netM7-τ st | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
netM7-τ st | jInR svst cst = ⊥-elim (ISstr-no-bfin svst)
netM7-τ st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netM7-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netM7-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netM7-τ st | jOutB clst svst = ⊥-elim (ISstr-no-bfout svst)

-- M8 = (ICn stStreaming, SB-loop stStreaming, Cidle): server loop (→ V0).
netM8-τ : ∀ {W″} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle
netM8-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netM8-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netM8-τ st | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
netM8-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netM8-τ st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netM8-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netM8-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netM8-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- M9 = (CB-loop stStreaming, ISn stStreaming, Cidle): client loop (→ V0).
netM9-τ : ∀ {W″} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle
netM9-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netM9-τ st | jSvτ svst = ⊥-elim (ISstr-noτ svst)
netM9-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netM9-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netM9-τ st | jInR svst cst = ⊥-elim (ISstr-no-bfin svst)
netM9-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netM9-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netM9-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netM9-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

------------------------------------------------------------------------
-- Busy→idle (noblk) routing: both peers return to stIdle (config A).
--   N  = (ICn stBusy, SB-noblk, Cidle)                          bfIn sync → Nh
--   Nh = (ICn stBusy, SB-loop stIdle, Chold mNoBlocks)          srv loop / bfOut sync → N2 / N3
--   N2 = (ICn stBusy, ISn stIdle, Chold mNoBlocks)              bfOut sync → N4
--   N3 = (CB-loop stIdle, SB-loop stIdle, Cret)                 3 loops → N4 / N5 / N6
--   N4 = (ICn stIdle, SB-loop stIdle, Cret)                     srv/copy loop → N7 / N8
--   N5 = (CB-loop stIdle, ISn stIdle, Cret)                     cl/copy loop → N7 / N9
--   N6 = (CB-loop stIdle, SB-loop stIdle, Cidle)                cl/srv loop → N8 / N9
--   N7 = (ICn stIdle, ISn stIdle, Cret)                         copy loop → A
--   N8 = (ICn stIdle, SB-loop stIdle, Cidle)                    srv loop → A
--   N9 = (CB-loop stIdle, ISn stIdle, Cidle)                    cl loop → A
------------------------------------------------------------------------

-- N → Nh by bfIn sync.
netN-τ : ∀ {W″} → JN (Inner (ICn stBusy) SB-noblk) Cidle ─[ τ ]─► W″
       → W″ ≡ JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks)
netN-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (SBnoblk-noτ svst)
... | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
... | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
... | jInR svst cst with SBnoblk-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = refl
netN-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netN-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netN-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netN-τ st | jOutB clst svst = ⊥-elim (SBnoblk-no-bfout svst)

-- Nh: server loop (→ N2) / bfOut sync (→ N3).
netNh-τ : ∀ {W″} → JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks))
        ⊎ (W″ ≡ JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret)
netNh-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netNh-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netNh-τ st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netNh-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netNh-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netNh-τ st | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICbusy-bfout clst
...     | inj₁ (() , _)
...     | inj₂ (refl , refl) = inj₂ refl
netNh-τ st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netNh-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- N2: bfOut sync (→ N4).
netN2-τ : ∀ {W″} → JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret
netN2-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
... | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
... | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICbusy-bfout clst
...     | inj₁ (() , _)
...     | inj₂ (refl , refl) = refl
netN2-τ st | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)
netN2-τ st | jOutB clst svst with ICbusy-bfout clst
...   | inj₁ (refl , _) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)
netN2-τ st | jOutB clst svst | inj₂ (refl , _) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)

-- N3: client/server/copy loops → N4 / N5 / N6.
netN3-τ : ∀ {W″} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle)
netN3-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netN3-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ (inj₁ refl)
netN3-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ (inj₂ refl)
netN3-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netN3-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netN3-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netN3-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netN3-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netN3-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- N4: server loop (→ N7) / copy loop (→ N8).
netN4-τ : ∀ {W″} → JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stIdle) (ISn stIdle)) Cret)
        ⊎ (W″ ≡ JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle)
netN4-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICidle-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netN4-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netN4-τ st | jInL clst cst = ⊥-elim (ICidle-no-bfin clst)
netN4-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netN4-τ st | jInB clst svst = ⊥-elim (ICidle-no-bfin clst)
netN4-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netN4-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netN4-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- N5: client loop (→ N7) / copy loop (→ N9).
netN5-τ : ∀ {W″} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stIdle) (ISn stIdle)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle)
netN5-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netN5-τ st | jSvτ svst = ⊥-elim (ISidle-noτ svst)
netN5-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netN5-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netN5-τ st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netN5-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netN5-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netN5-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netN5-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- N6: client loop (→ N8) / server loop (→ N9).
netN6-τ : ∀ {W″} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle)
        ⊎ (W″ ≡ JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle)
netN6-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netN6-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netN6-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netN6-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netN6-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netN6-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netN6-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netN6-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netN6-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- N7: copy loop (→ A).
netN7-τ : ∀ {W″} → JN (Inner (ICn stIdle) (ISn stIdle)) Cret ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stIdle) (ISn stIdle)) Cidle
netN7-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICidle-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netN7-τ st | jInL clst cst = ⊥-elim (ICidle-no-bfin clst)
netN7-τ st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netN7-τ st | jInB clst svst = ⊥-elim (ICidle-no-bfin clst)
netN7-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netN7-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netN7-τ st | jOutB clst svst = ⊥-elim (ICidle-no-bfout clst)

-- N8: server loop (→ A).
netN8-τ : ∀ {W″} → JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stIdle) (ISn stIdle)) Cidle
netN8-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICidle-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netN8-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netN8-τ st | jInL clst cst = ⊥-elim (ICidle-no-bfin clst)
netN8-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netN8-τ st | jInB clst svst = ⊥-elim (ICidle-no-bfin clst)
netN8-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netN8-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netN8-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- N9: client loop (→ A).
netN9-τ : ∀ {W″} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stIdle) (ISn stIdle)) Cidle
netN9-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netN9-τ st | jSvτ svst = ⊥-elim (ISidle-noτ svst)
netN9-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netN9-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netN9-τ st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netN9-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netN9-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netN9-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netN9-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- SB-blk b: send-hold; only bfIn\!(mBlock b) (→ SB-loop stStreaming); no τ, no bfOut, no apiBF.
SBblk-noτ : ∀ {b Q''} → ¬ (SB-blk b ─[ τ ]─► Q'')
SBblk-noτ (sSil ())
SBblk-noτ (sTau refl ())
SBblk-bfin : ∀ {b a Q''} → SB-blk b ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → (a ≡ mBlock b) × (Q'' ≡ SB-loop stStreaming)
SBblk-bfin {b} {a} (sVis refl q) with a ≟ mBlock b
... | no _ with q
...   | ()
SBblk-bfin {b} {a} (sVis refl q) | yes refl with q
...   | refl = refl , refl
SBblk-no-bfout : ∀ {b a Q''} → SB-blk b ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q'' → ⊥
SBblk-no-bfout (sVis refl ())
SBblk-no-api : ∀ {b m a Q''} → SB-blk b ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q'' → ⊥
SBblk-no-api (sVis refl ())

-- SB-bdone: send-hold; only bfIn\!mBatchDone (→ SB-loop stIdle); no τ, no bfOut, no apiBF.
SBbdone-noτ : ∀ {Q''} → ¬ (SB-bdone ─[ τ ]─► Q'')
SBbdone-noτ (sSil ())
SBbdone-noτ (sTau refl ())
SBbdone-bfin : ∀ {a Q''} → SB-bdone ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► Q'' → (a ≡ mBatchDone) × (Q'' ≡ SB-loop stIdle)
SBbdone-bfin {a} (sVis refl q) with a ≟ mBatchDone
... | no _ with q
...   | ()
SBbdone-bfin {a} (sVis refl q) | yes refl with q
...   | refl = refl , refl
SBbdone-no-bfout : ∀ {a Q''} → SB-bdone ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► Q'' → ⊥
SBbdone-no-bfout (sVis refl ())
SBbdone-no-api : ∀ {m a Q''} → SB-bdone ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q'' → ⊥
SBbdone-no-api (sVis refl ())

-- CB-blk b: recv-deliver; only apiBF recvBFBlock\!b (→ CB-loop stStreaming); no τ, no bfIn, no bfOut.
CBblk-noτ : ∀ {b P''} → ¬ (CB-blk b ─[ τ ]─► P'')
CBblk-noτ (sSil ())
CBblk-noτ (sTau refl ())
CBblk-api : ∀ {b m a P''} → CB-blk b ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► P'' → (m ≡ recvBFBlock) × (P'' ≡ CB-loop stStreaming)
CBblk-api {b} {recvBFBlock} {a} (sVis refl p) with a ≟ b
... | no _ with p
...   | ()
CBblk-api {b} {recvBFBlock} {a} (sVis refl p) | yes refl with p
...   | refl = refl , refl
CBblk-api {b} {sendBFRequestRange} (sVis refl ())
CBblk-api {b} {sendBFClientDone} (sVis refl ())
CBblk-api {b} {sendBFStartBatch} (sVis refl ())
CBblk-api {b} {sendBFNoBlocks} (sVis refl ())
CBblk-api {b} {sendBFBlock} (sVis refl ())
CBblk-api {b} {sendBFBatchDone} (sVis refl ())
CBblk-api {b} {reqBFRange} (sVis refl ())
CBblk-no-bfin : ∀ {b a P''} → CB-blk b ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = a })) ]─► P'' → ⊥
CBblk-no-bfin (sVis refl ())
CBblk-no-bfout : ∀ {b a P''} → CB-blk b ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = a })) ]─► P'' → ⊥
CBblk-no-bfout (sVis refl ())

------------------------------------------------------------------------
-- Streaming subsystem.  The resident-block slots are: client = CB-blk b
-- (owes recvBFBlock b), copy = Chold (mBlock b), server send-hold = SB-blk b.
-- Occupancy 0..3.  A bfIn sync drains a server-hold into the copy; a bfOut sync
-- drains the copy into the client delivery; server loop-backs re-offer.
-- Each `bfMsg`-style hop is bracketed by an observable apiBF.
------------------------------------------------------------------------

-- W b = (ICn stStreaming, SB-blk b, Cidle): one τ — bfIn sync (→ Wh b).
netW-τ : ∀ {b W″} → JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ─[ τ ]─► W″
       → W″ ≡ JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))
netW-τ {b} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (SBblk-noτ svst)
... | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
... | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
... | jInR svst cst with SBblk-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = refl
netW-τ {b} st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netW-τ {b} st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netW-τ {b} st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netW-τ {b} st | jOutB clst svst = ⊥-elim (SBblk-no-bfout svst)

-- Wh b = (ICn stStreaming, SB-loop stStreaming, Chold(mBlock b)): server loop (→ W2 b) / bfOut sync (→ W3 b).
netWh-τ : ∀ {b W″} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)))
        ⊎ (W″ ≡ JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret)
netWh-τ {b} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netWh-τ {b} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netWh-τ {b} st | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
netWh-τ {b} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netWh-τ {b} st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netWh-τ {b} st | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICstr-bfout clst
...     | inj₁ (b2 , refl , refl) = inj₂ refl
...     | inj₂ (() , _)
netWh-τ {b} st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netWh-τ {b} st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- W2 b = (ICn stStreaming, ISn stStreaming, Chold(mBlock b)): one τ — bfOut sync (→ W4 b).
netW2-τ : ∀ {b W″} → JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (CB-blk b) (ISn stStreaming)) Cret
netW2-τ {b} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (ISstr-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
... | jInR svst cst = ⊥-elim (ISstr-no-bfin svst)
... | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICstr-bfout clst
...     | inj₁ (b2 , refl , refl) = refl
...     | inj₂ (() , _)
netW2-τ {b} st | jOutR cst svst = ⊥-elim (ISstr-no-bfout svst)
netW2-τ {b} st | jOutB clst svst = ⊥-elim (ISstr-no-bfout svst)

-- W3 b = (CB-blk b, SB-loop stStreaming, Cret): server loop (→ W4 b) / copy loop (→ W5 b).
netW3-τ : ∀ {b W″} → JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (CB-blk b) (ISn stStreaming)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle)
netW3-τ {b} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netW3-τ {b} st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netW3-τ {b} st | jInL clst cst = ⊥-elim (CBblk-no-bfin clst)
netW3-τ {b} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netW3-τ {b} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)
netW3-τ {b} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netW3-τ {b} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netW3-τ {b} st | jOutB clst svst = ⊥-elim (CBblk-no-bfout clst)

-- W4 b = (CB-blk b, ISn stStreaming, Cret): one τ — copy loop (→ Vocc1 b).
netW4-τ : ∀ {b W″} → JN (Inner (CB-blk b) (ISn stStreaming)) Cret ─[ τ ]─► W″
        → W″ ≡ JN (Inner (CB-blk b) (ISn stStreaming)) Cidle
netW4-τ {b} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst = ⊥-elim (ISstr-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netW4-τ {b} st | jInL clst cst = ⊥-elim (CBblk-no-bfin clst)
netW4-τ {b} st | jInR svst cst = ⊥-elim (ISstr-no-bfin svst)
netW4-τ {b} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)
netW4-τ {b} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netW4-τ {b} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netW4-τ {b} st | jOutB clst svst = ⊥-elim (CBblk-no-bfout clst)

-- W5 b = (CB-blk b, SB-loop stStreaming, Cidle): one τ — server loop (→ Vocc1 b).
netW5-τ : ∀ {b W″} → JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle ─[ τ ]─► W″
        → W″ ≡ JN (Inner (CB-blk b) (ISn stStreaming)) Cidle
netW5-τ {b} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netW5-τ {b} st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netW5-τ {b} st | jInL clst cst = ⊥-elim (CBblk-no-bfin clst)
netW5-τ {b} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netW5-τ {b} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)
netW5-τ {b} st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netW5-τ {b} st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netW5-τ {b} st | jOutB clst svst = ⊥-elim (CBblk-no-bfout clst)

-- Vocc1 b = (CB-blk b, ISn stStreaming, Cidle): STABLE occupancy-1; client owes recvBFBlock\!b,
-- server offers sendBFBlock / sendBFBatchDone.
netVocc1-noτ : ∀ {b W″} → ¬ (JN (Inner (CB-blk b) (ISn stStreaming)) Cidle ─[ τ ]─► W″)
netVocc1-noτ {b} st with JN-τ-cases st
... | jClτ clst = CBblk-noτ clst
... | jSvτ svst = ISstr-noτ svst
... | jCpτ cpst = Cidle-noτ cpst
... | jInL clst cst = CBblk-no-bfin clst
... | jInR svst cst = ISstr-no-bfin svst
... | jInB clst svst = CBblk-no-bfin clst
... | jOutL cst clst = Cidle-no-bfout′ cst
... | jOutR cst svst = Cidle-no-bfout′ cst
... | jOutB clst svst = CBblk-no-bfout clst

------------------------------------------------------------------------
-- Occupancy 2: a second block b₁ in flight while the client still owes b₀.
--   W2e = (CB-blk b₀, SB-blk b₁, Cidle)                 bfIn sync → W2h
--   W2h = (CB-blk b₀, SB-loop stStreaming, Chold(mBlock b₁))  srv loop → W2a (client owes b₀, can't recv bfOut)
--   W2a = (CB-blk b₀, ISn stStreaming, Chold(mBlock b₁))      STABLE occ-2
------------------------------------------------------------------------

-- W2e = (CB-blk b₀, SB-blk b₁, Cidle): one τ — bfIn sync (→ W2h).
netW2e-τ : ∀ {b₀ b₁ W″} → JN (Inner (CB-blk b₀) (SB-blk b₁)) Cidle ─[ τ ]─► W″
         → W″ ≡ JN (Inner (CB-blk b₀) (SB-loop stStreaming)) (Chold (mBlock b₁))
netW2e-τ {b₀} {b₁} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst = ⊥-elim (SBblk-noτ svst)
... | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
... | jInL clst cst = ⊥-elim (CBblk-no-bfin clst)
... | jInR svst cst with SBblk-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = refl
netW2e-τ {b₀} {b₁} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)
netW2e-τ {b₀} {b₁} st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netW2e-τ {b₀} {b₁} st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netW2e-τ {b₀} {b₁} st | jOutB clst svst = ⊥-elim (SBblk-no-bfout svst)

-- W2h = (CB-blk b₀, SB-loop stStreaming, Chold(mBlock b₁)): one τ — server loop (→ W2a).
-- (The client owes recvBFBlock b₀, so it cannot consume the held block on bfOut → no bfOut sync.)
netW2h-τ : ∀ {b₀ b₁ W″} → JN (Inner (CB-blk b₀) (SB-loop stStreaming)) (Chold (mBlock b₁)) ─[ τ ]─► W″
         → W″ ≡ JN (Inner (CB-blk b₀) (ISn stStreaming)) (Chold (mBlock b₁))
netW2h-τ {b₀} {b₁} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netW2h-τ {b₀} {b₁} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netW2h-τ {b₀} {b₁} st | jInL clst cst = ⊥-elim (CBblk-no-bfin clst)
netW2h-τ {b₀} {b₁} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netW2h-τ {b₀} {b₁} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)
netW2h-τ {b₀} {b₁} st | jOutL cst clst = ⊥-elim (CBblk-no-bfout clst)
netW2h-τ {b₀} {b₁} st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netW2h-τ {b₀} {b₁} st | jOutB clst svst = ⊥-elim (CBblk-no-bfout clst)

-- W2a = (CB-blk b₀, ISn stStreaming, Chold(mBlock b₁)): STABLE occupancy 2.
netW2a-noτ : ∀ {b₀ b₁ W″} → ¬ (JN (Inner (CB-blk b₀) (ISn stStreaming)) (Chold (mBlock b₁)) ─[ τ ]─► W″)
netW2a-noτ {b₀} {b₁} st with JN-τ-cases st
... | jClτ clst = CBblk-noτ clst
... | jSvτ svst = ISstr-noτ svst
... | jCpτ cpst = Chold-noτ cpst
... | jInL clst cst = CBblk-no-bfin clst
... | jInR svst cst = ISstr-no-bfin svst
... | jInB clst svst = CBblk-no-bfin clst
... | jOutL cst clst = CBblk-no-bfout clst
... | jOutR cst svst = ISstr-no-bfout svst
... | jOutB clst svst = CBblk-no-bfout clst

-- W2d = (CB-loop stStreaming, ISn stStreaming, Chold(mBlock b₁)): one τ — client loop (→ W2 b₁, the occ-1 deliver transient).
netW2d-τ : ∀ {b₁ W″} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b₁)) ─[ τ ]─► W″
         → W″ ≡ JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b₁))
netW2d-τ {b₁} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netW2d-τ {b₁} st | jSvτ svst = ⊥-elim (ISstr-noτ svst)
netW2d-τ {b₁} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netW2d-τ {b₁} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netW2d-τ {b₁} st | jInR svst cst = ⊥-elim (ISstr-no-bfin svst)
netW2d-τ {b₁} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netW2d-τ {b₁} st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netW2d-τ {b₁} st | jOutR cst svst = ⊥-elim (ISstr-no-bfout svst)
netW2d-τ {b₁} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

------------------------------------------------------------------------
-- Occupancy 3 (saturated): client owes b₀, copy holds b₁, server send-holds b₂.
--   W3e = (CB-blk b₀, SB-blk b₂, Chold(mBlock b₁))        STABLE — only recvBFBlock b₀ enabled
--   W3d = (CB-loop stStreaming, SB-blk b₂, Chold(mBlock b₁))  client loop → W3a
--   W3a = (ICn stStreaming, SB-blk b₂, Chold(mBlock b₁))      bfOut sync → W3b
--   W3b = (CB-blk b₁, SB-blk b₂, Cret)                        copy loop → W2e(b₁,b₂) (occ-2 entry)
------------------------------------------------------------------------

-- W3e: STABLE occupancy 3 (server blocked on bfIn since copy is full; client owes a delivery).
netW3e-noτ : ∀ {b₀ b₁ b₂ W″} → ¬ (JN (Inner (CB-blk b₀) (SB-blk b₂)) (Chold (mBlock b₁)) ─[ τ ]─► W″)
netW3e-noτ {b₀} {b₁} {b₂} st with JN-τ-cases st
... | jClτ clst = CBblk-noτ clst
... | jSvτ svst = SBblk-noτ svst
... | jCpτ cpst = Chold-noτ cpst
... | jInL clst cst = CBblk-no-bfin clst
... | jInR svst cst = Chold-no-bfin cst
... | jInB clst svst = CBblk-no-bfin clst
... | jOutL cst clst = CBblk-no-bfout clst
... | jOutR cst svst = SBblk-no-bfout svst
... | jOutB clst svst = CBblk-no-bfout clst

-- W3d: one τ — client loop (→ W3a).
netW3d-τ : ∀ {b₁ b₂ W″} → JN (Inner (CB-loop stStreaming) (SB-blk b₂)) (Chold (mBlock b₁)) ─[ τ ]─► W″
         → W″ ≡ JN (Inner (ICn stStreaming) (SB-blk b₂)) (Chold (mBlock b₁))
netW3d-τ {b₁} {b₂} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netW3d-τ {b₁} {b₂} st | jSvτ svst = ⊥-elim (SBblk-noτ svst)
netW3d-τ {b₁} {b₂} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netW3d-τ {b₁} {b₂} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netW3d-τ {b₁} {b₂} st | jInR svst cst = ⊥-elim (Chold-no-bfin cst)
netW3d-τ {b₁} {b₂} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netW3d-τ {b₁} {b₂} st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netW3d-τ {b₁} {b₂} st | jOutR cst svst = ⊥-elim (SBblk-no-bfout svst)
netW3d-τ {b₁} {b₂} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- W3a: one τ — bfOut sync delivers b₁ to the client (→ W3b). (Server still blocked on bfIn: copy full.)
netW3a-τ : ∀ {b₁ b₂ W″} → JN (Inner (ICn stStreaming) (SB-blk b₂)) (Chold (mBlock b₁)) ─[ τ ]─► W″
         → W″ ≡ JN (Inner (CB-blk b₁) (SB-blk b₂)) Cret
netW3a-τ {b₁} {b₂} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (SBblk-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
... | jInR svst cst = ⊥-elim (Chold-no-bfin cst)
... | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICstr-bfout clst
...     | inj₁ (b , refl , refl) = refl
...     | inj₂ (() , _)
netW3a-τ {b₁} {b₂} st | jOutR cst svst = ⊥-elim (SBblk-no-bfout svst)
netW3a-τ {b₁} {b₂} st | jOutB clst svst = ⊥-elim (SBblk-no-bfout svst)

-- W3b: one τ — copy loop (→ W2e(b₁,b₂), the occ-2 entry).
netW3b-τ : ∀ {b₁ b₂ W″} → JN (Inner (CB-blk b₁) (SB-blk b₂)) Cret ─[ τ ]─► W″
         → W″ ≡ JN (Inner (CB-blk b₁) (SB-blk b₂)) Cidle
netW3b-τ {b₁} {b₂} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst = ⊥-elim (SBblk-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netW3b-τ {b₁} {b₂} st | jInL clst cst = ⊥-elim (Cret-no-ev cst)
netW3b-τ {b₁} {b₂} st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netW3b-τ {b₁} {b₂} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)  -- copy step refuted below via Cret
netW3b-τ {b₁} {b₂} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netW3b-τ {b₁} {b₂} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netW3b-τ {b₁} {b₂} st | jOutB clst svst = ⊥-elim (CBblk-no-bfout clst)

------------------------------------------------------------------------
-- Batch-done draining.  Server fires sendBFBatchDone (→ SB-bdone), the
-- mBatchDone hop routes through the copy; the client (once it has delivered
-- all owed blocks) consumes mBatchDone on bfOut and returns to stIdle.
------------------------------------------------------------------------

-- BD0e = (ICn stStreaming, SB-bdone, Cidle): one τ — bfIn sync (→ BD0h).
netBD0e-τ : ∀ {W″} → JN (Inner (ICn stStreaming) SB-bdone) Cidle ─[ τ ]─► W″
          → W″ ≡ JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone)
netBD0e-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
... | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
... | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
... | jInR svst cst with SBbdone-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = refl
netBD0e-τ st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netBD0e-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netBD0e-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netBD0e-τ st | jOutB clst svst = ⊥-elim (SBbdone-no-bfout svst)

-- BD0h = (ICn stStreaming, SB-loop stIdle, Chold mBatchDone): server loop (→ BD0a) / bfOut sync (→ N3).
netBD0h-τ : ∀ {W″} → JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► W″
          → (W″ ≡ JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone))
          ⊎ (W″ ≡ JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret)
netBD0h-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netBD0h-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netBD0h-τ st | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
netBD0h-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netBD0h-τ st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netBD0h-τ st | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICstr-bfout clst
...     | inj₁ (_ , () , _)
...     | inj₂ (refl , refl) = inj₂ refl
netBD0h-τ st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netBD0h-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- BD0a = (ICn stStreaming, ISn stIdle, Chold mBatchDone): one τ — bfOut sync (→ BD1c).
netBD0a-τ : ∀ {W″} → JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► W″
          → W″ ≡ JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret
netBD0a-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
... | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
... | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICstr-bfout clst
...     | inj₁ (_ , () , _)
...     | inj₂ (refl , refl) = refl
netBD0a-τ st | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)
netBD0a-τ st | jOutB clst svst with ICstr-bfout clst
...   | inj₁ (b , refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)
netBD0a-τ st | jOutB clst svst | inj₂ (refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)

-- BD1e = (CB-blk b₀, SB-bdone, Cidle): one τ — bfIn sync (→ BD1h).
netBD1e-τ : ∀ {b₀ W″} → JN (Inner (CB-blk b₀) SB-bdone) Cidle ─[ τ ]─► W″
          → W″ ≡ JN (Inner (CB-blk b₀) (SB-loop stIdle)) (Chold mBatchDone)
netBD1e-τ {b₀} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
... | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
... | jInL clst cst = ⊥-elim (CBblk-no-bfin clst)
... | jInR svst cst with SBbdone-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = refl
netBD1e-τ {b₀} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)
netBD1e-τ {b₀} st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netBD1e-τ {b₀} st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netBD1e-τ {b₀} st | jOutB clst svst = ⊥-elim (SBbdone-no-bfout svst)

-- BD1h = (CB-blk b₀, SB-loop stIdle, Chold mBatchDone): one τ — server loop (→ BD1a).
-- (Client owes b₀, so it can't consume mBatchDone on bfOut yet.)
netBD1h-τ : ∀ {b₀ W″} → JN (Inner (CB-blk b₀) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► W″
          → W″ ≡ JN (Inner (CB-blk b₀) (ISn stIdle)) (Chold mBatchDone)
netBD1h-τ {b₀} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netBD1h-τ {b₀} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netBD1h-τ {b₀} st | jInL clst cst = ⊥-elim (CBblk-no-bfin clst)
netBD1h-τ {b₀} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netBD1h-τ {b₀} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)
netBD1h-τ {b₀} st | jOutL cst clst = ⊥-elim (CBblk-no-bfout clst)
netBD1h-τ {b₀} st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netBD1h-τ {b₀} st | jOutB clst svst = ⊥-elim (CBblk-no-bfout clst)

-- BD1a = (CB-blk b₀, ISn stIdle, Chold mBatchDone): STABLE; only client recvBFBlock\!b₀ enabled.
netBD1a-noτ : ∀ {b₀ W″} → ¬ (JN (Inner (CB-blk b₀) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► W″)
netBD1a-noτ {b₀} st with JN-τ-cases st
... | jClτ clst = CBblk-noτ clst
... | jSvτ svst = ISidle-noτ svst
... | jCpτ cpst = Chold-noτ cpst
... | jInL clst cst = CBblk-no-bfin clst
... | jInR svst cst = ISidle-no-bfin svst
... | jInB clst svst = CBblk-no-bfin clst
... | jOutL cst clst = CBblk-no-bfout clst
... | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)
netBD1a-noτ {b₀} st | jOutB clst svst = CBblk-no-bfout clst

-- BD1d = (CB-loop stStreaming, ISn stIdle, Chold mBatchDone): one τ — client loop (→ BD1b).
netBD1d-τ : ∀ {W″} → JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► W″
          → W″ ≡ JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone)
netBD1d-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netBD1d-τ st | jSvτ svst = ⊥-elim (ISidle-noτ svst)
netBD1d-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netBD1d-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netBD1d-τ st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netBD1d-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netBD1d-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netBD1d-τ st | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)
netBD1d-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- BD2e = (CB-blk b₀, SB-bdone, Chold(mBlock b₁)): STABLE occ-2 batch-done; only recvBFBlock\!b₀ enabled.
netBD2e-noτ : ∀ {b₀ b₁ W″} → ¬ (JN (Inner (CB-blk b₀) SB-bdone) (Chold (mBlock b₁)) ─[ τ ]─► W″)
netBD2e-noτ {b₀} {b₁} st with JN-τ-cases st
... | jClτ clst = CBblk-noτ clst
... | jSvτ svst = SBbdone-noτ svst
... | jCpτ cpst = Chold-noτ cpst
... | jInL clst cst = CBblk-no-bfin clst
... | jInR svst cst = Chold-no-bfin cst
... | jInB clst svst = CBblk-no-bfin clst
... | jOutL cst clst = CBblk-no-bfout clst
... | jOutR cst svst = SBbdone-no-bfout svst
... | jOutB clst svst = CBblk-no-bfout clst

-- BD2d = (CB-loop stStreaming, SB-bdone, Chold(mBlock b₁)): one τ — client loop (→ BD2a).
netBD2d-τ : ∀ {b₁ W″} → JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b₁)) ─[ τ ]─► W″
          → W″ ≡ JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b₁))
netBD2d-τ {b₁} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netBD2d-τ {b₁} st | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
netBD2d-τ {b₁} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netBD2d-τ {b₁} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netBD2d-τ {b₁} st | jInR svst cst = ⊥-elim (Chold-no-bfin cst)
netBD2d-τ {b₁} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netBD2d-τ {b₁} st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netBD2d-τ {b₁} st | jOutR cst svst = ⊥-elim (SBbdone-no-bfout svst)
netBD2d-τ {b₁} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- BD2a = (ICn stStreaming, SB-bdone, Chold(mBlock b₁)): one τ — bfOut sync delivers b₁ (→ BD2b).
netBD2a-τ : ∀ {b₁ W″} → JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b₁)) ─[ τ ]─► W″
          → W″ ≡ JN (Inner (CB-blk b₁) SB-bdone) Cret
netBD2a-τ {b₁} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
... | jInR svst cst = ⊥-elim (Chold-no-bfin cst)
... | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICstr-bfout clst
...     | inj₁ (b , refl , refl) = refl
...     | inj₂ (() , _)
netBD2a-τ {b₁} st | jOutR cst svst = ⊥-elim (SBbdone-no-bfout svst)
netBD2a-τ {b₁} st | jOutB clst svst = ⊥-elim (SBbdone-no-bfout svst)

-- BD2b = (CB-blk b₁, SB-bdone, Cret): one τ — copy loop (→ BD1e b₁, occ-1 batch-done entry).
netBD2b-τ : ∀ {b₁ W″} → JN (Inner (CB-blk b₁) SB-bdone) Cret ─[ τ ]─► W″
          → W″ ≡ JN (Inner (CB-blk b₁) SB-bdone) Cidle
netBD2b-τ {b₁} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBblk-noτ clst)
... | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netBD2b-τ {b₁} st | jInL clst cst = ⊥-elim (Cret-no-ev cst)
netBD2b-τ {b₁} st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netBD2b-τ {b₁} st | jInB clst svst = ⊥-elim (CBblk-no-bfin clst)
netBD2b-τ {b₁} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netBD2b-τ {b₁} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netBD2b-τ {b₁} st | jOutB clst svst = ⊥-elim (CBblk-no-bfout clst)

-- V0 = (ICn stStreaming, ISn stStreaming, Cidle): STABLE occupancy-0 streaming; server offers block/bdone.
netV0-noτ : ∀ {W″} → ¬ (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle ─[ τ ]─► W″)
netV0-noτ st with JN-τ-cases st
... | jClτ clst = ICstr-noτ clst
... | jSvτ svst = ISstr-noτ svst
... | jCpτ cpst = Cidle-noτ cpst
... | jInL clst cst = ICstr-no-bfin clst
... | jInR svst cst = ISstr-no-bfin svst
... | jInB clst svst = ICstr-no-bfin clst
... | jOutL cst clst = Cidle-no-bfout′ cst
... | jOutR cst svst = Cidle-no-bfout′ cst
... | jOutB clst svst = ISstr-no-bfout svst

------------------------------------------------------------------------
-- Mixed-state visible-apiBF successors (busy-loop and streaming/bdone-loop
-- families): a notify (SB-req) / delivery (CB-blk) fires its visible apiBF
-- concurrently with the surrounding loop/sync τ's; the peer advances to its
-- loop-back, yielding these loop-back configs (all converge to stable states).
------------------------------------------------------------------------

-- G3 = (CB-loop stBusy, SB-loop stBusy, Cret): client/server/copy loops → G3a / G5 / G6.
netG3-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle)
netG3-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netG3-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ (inj₁ refl)
netG3-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ (inj₂ refl)
netG3-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netG3-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netG3-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netG3-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netG3-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netG3-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- G3a = (ICn stBusy, SB-loop stBusy, Cret): server loop (→ G7) / copy loop (→ Fl).
netG3a-τ : ∀ {W″} → JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stBusy) (ISn stBusy)) Cret)
         ⊎ (W″ ≡ JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle)
netG3a-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netG3a-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netG3a-τ st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netG3a-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netG3a-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netG3a-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netG3a-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netG3a-τ st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

-- G5 = (CB-loop stBusy, ISn stBusy, Cret): client loop (→ G7) / copy loop (→ I).
netG5-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stBusy) (ISn stBusy)) Cret)
        ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle)
netG5-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netG5-τ st | jSvτ svst = ⊥-elim (ISbusy-noτ svst)
netG5-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netG5-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netG5-τ st | jInR svst cst = ⊥-elim (ISbusy-no-bfin svst)
netG5-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netG5-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netG5-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netG5-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- G6 = (CB-loop stBusy, SB-loop stBusy, Cidle): client loop (→ Fl) / server loop (→ I).
netG6-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle ─[ τ ]─► W″
        → (W″ ≡ JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle)
        ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle)
netG6-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netG6-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netG6-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netG6-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netG6-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netG6-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netG6-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netG6-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netG6-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- G7 = (ICn stBusy, ISn stBusy, Cret): copy loop (→ J).
netG7-τ : ∀ {W″} → JN (Inner (ICn stBusy) (ISn stBusy)) Cret ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) (ISn stBusy)) Cidle
netG7-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (ISbusy-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netG7-τ st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netG7-τ st | jInR svst cst = ⊥-elim (ISbusy-no-bfin svst)
netG7-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netG7-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netG7-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netG7-τ st | jOutB clst svst = ⊥-elim (ISbusy-no-bfout svst)

-- I = (CB-loop stBusy, ISn stBusy, Cidle): client loop (→ J).
netI-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle ─[ τ ]─► W″
       → W″ ≡ JN (Inner (ICn stBusy) (ISn stBusy)) Cidle
netI-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netI-τ st | jSvτ svst = ⊥-elim (ISbusy-noτ svst)
netI-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netI-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netI-τ st | jInR svst cst = ⊥-elim (ISbusy-no-bfin svst)
netI-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netI-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netI-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netI-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- WX1 = (CB-loop stStreaming, SB-blk b₁, Cidle): client loop (→ W b₁) / bfIn sync (→ WX2).
netWX1-τ : ∀ {b₁ W″} → JN (Inner (CB-loop stStreaming) (SB-blk b₁)) Cidle ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stStreaming) (SB-blk b₁)) Cidle)
         ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b₁)))
netWX1-τ {b₁} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netWX1-τ {b₁} st | jSvτ svst = ⊥-elim (SBblk-noτ svst)
netWX1-τ {b₁} st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netWX1-τ {b₁} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netWX1-τ {b₁} st | jInR svst cst with SBblk-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = inj₂ refl
netWX1-τ {b₁} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netWX1-τ {b₁} st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netWX1-τ {b₁} st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netWX1-τ {b₁} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- WX2 = (CB-loop stStreaming, SB-loop stStreaming, Chold(mBlock b₁)): client loop (→ Wh b₁) / server loop (→ W2d b₁).
netWX2-τ : ∀ {b₁ W″} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b₁)) ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b₁)))
         ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b₁)))
netWX2-τ {b₁} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netWX2-τ {b₁} st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netWX2-τ {b₁} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netWX2-τ {b₁} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netWX2-τ {b₁} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netWX2-τ {b₁} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netWX2-τ {b₁} st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netWX2-τ {b₁} st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netWX2-τ {b₁} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- WX3 = (CB-loop stStreaming, SB-blk b₂, Cret): client loop (→ WX3a) / copy loop (→ WX1 b₂).
netWX3-τ : ∀ {b₂ W″} → JN (Inner (CB-loop stStreaming) (SB-blk b₂)) Cret ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stStreaming) (SB-blk b₂)) Cret)
         ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (SB-blk b₂)) Cidle)
netWX3-τ {b₂} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netWX3-τ {b₂} st | jSvτ svst = ⊥-elim (SBblk-noτ svst)
netWX3-τ {b₂} st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netWX3-τ {b₂} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netWX3-τ {b₂} st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netWX3-τ {b₂} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netWX3-τ {b₂} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netWX3-τ {b₂} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netWX3-τ {b₂} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- WX3a = (ICn stStreaming, SB-blk b₂, Cret): copy loop (→ W b₂).
netWX3a-τ : ∀ {b₂ W″} → JN (Inner (ICn stStreaming) (SB-blk b₂)) Cret ─[ τ ]─► W″
          → W″ ≡ JN (Inner (ICn stStreaming) (SB-blk b₂)) Cidle
netWX3a-τ {b₂} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (SBblk-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netWX3a-τ {b₂} st | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
netWX3a-τ {b₂} st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netWX3a-τ {b₂} st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netWX3a-τ {b₂} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netWX3a-τ {b₂} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netWX3a-τ {b₂} st | jOutB clst svst = ⊥-elim (SBblk-no-bfout svst)

-- BX1 = (CB-loop stStreaming, SB-bdone, Cidle): client loop (→ BD0e) / bfIn sync (→ BX2).
netBX1-τ : ∀ {W″} → JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stStreaming) SB-bdone) Cidle)
         ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone))
netBX1-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netBX1-τ st | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
netBX1-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netBX1-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netBX1-τ st | jInR svst cst with SBbdone-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = inj₂ refl
netBX1-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netBX1-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netBX1-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netBX1-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- BX2 = (CB-loop stStreaming, SB-loop stIdle, Chold mBatchDone): client loop (→ BD0h) / server loop (→ BD1d).
netBX2-τ : ∀ {W″} → JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone))
         ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone))
netBX2-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netBX2-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netBX2-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netBX2-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netBX2-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netBX2-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netBX2-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netBX2-τ st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netBX2-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- BX3 = (CB-loop stStreaming, SB-bdone, Cret): client loop (→ BX3a) / copy loop (→ BX1).
netBX3-τ : ∀ {W″} → JN (Inner (CB-loop stStreaming) SB-bdone) Cret ─[ τ ]─► W″
         → (W″ ≡ JN (Inner (ICn stStreaming) SB-bdone) Cret)
         ⊎ (W″ ≡ JN (Inner (CB-loop stStreaming) SB-bdone) Cidle)
netBX3-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netBX3-τ st | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
netBX3-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netBX3-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netBX3-τ st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netBX3-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netBX3-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netBX3-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netBX3-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

-- BX3a = (ICn stStreaming, SB-bdone, Cret): copy loop (→ BD0e).
netBX3a-τ : ∀ {W″} → JN (Inner (ICn stStreaming) SB-bdone) Cret ─[ τ ]─► W″
          → W″ ≡ JN (Inner (ICn stStreaming) SB-bdone) Cidle
netBX3a-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICstr-noτ clst)
... | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netBX3a-τ st | jInL clst cst = ⊥-elim (ICstr-no-bfin clst)
netBX3a-τ st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netBX3a-τ st | jInB clst svst = ⊥-elim (ICstr-no-bfin clst)
netBX3a-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netBX3a-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netBX3a-τ st | jOutB clst svst = ⊥-elim (SBbdone-no-bfout svst)

------------------------------------------------------------------------
-- ¬ Diverges at every reachable joint NETWORK config (acyclic τ-DAG).
------------------------------------------------------------------------

-- forward declarations of the per-config convergence lemmas.
nd-A : ¬ Diverges (JN (Inner (ICn stIdle) (ISn stIdle)) Cidle)
nd-B : ∀ {r} → ¬ Diverges (JN (Inner (CB-req r) (ISn stIdle)) Cidle)
nd-Bh : ∀ {r} → ¬ Diverges (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)))
nd-B2 : ∀ {r} → ¬ Diverges (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)))
nd-B3 : ∀ {r} → ¬ Diverges (JN (Inner (CB-loop stBusy) (SB-req r)) Cret)
nd-B3a : ∀ {r} → ¬ Diverges (JN (Inner (ICn stBusy) (SB-req r)) Cret)
nd-B5 : ∀ {r} → ¬ Diverges (JN (Inner (CB-loop stBusy) (SB-req r)) Cidle)
nd-B4 : ∀ {r} → ¬ Diverges (JN (Inner (ICn stBusy) (SB-req r)) Cidle)
nd-Fl : ¬ Diverges (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle)
nd-J : ¬ Diverges (JN (Inner (ICn stBusy) (ISn stBusy)) Cidle)
nd-Cdone : ¬ Diverges (JN (Inner CB-cdone (ISn stIdle)) Cidle)
nd-Cdh : ¬ Diverges (JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone))
nd-Cd2 : ¬ Diverges (JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone))
nd-Cd3 : ¬ Diverges (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret)
nd-Cd4 : ¬ Diverges (JN (Inner (ICn stDone) (SB-loop stDone)) Cret)
nd-Cd5 : ¬ Diverges (JN (Inner (CB-loop stDone) (ISn stDone)) Cret)
nd-Cd6 : ¬ Diverges (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle)
nd-Cd7 : ¬ Diverges (JN (Inner (ICn stDone) (ISn stDone)) Cret)
nd-Cd8 : ¬ Diverges (JN (Inner (ICn stDone) (SB-loop stDone)) Cidle)
nd-Cd9 : ¬ Diverges (JN (Inner (CB-loop stDone) (ISn stDone)) Cidle)
nd-Z : ¬ Diverges (JN (Inner (ICn stDone) (ISn stDone)) Cidle)
nd-M : ¬ Diverges (JN (Inner (ICn stBusy) SB-sbatch) Cidle)
nd-Mh : ¬ Diverges (JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch))
nd-M2 : ¬ Diverges (JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch))
nd-M3 : ¬ Diverges (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret)
nd-M4 : ¬ Diverges (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret)
nd-M5 : ¬ Diverges (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret)
nd-M6 : ¬ Diverges (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle)
nd-M7 : ¬ Diverges (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret)
nd-M8 : ¬ Diverges (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle)
nd-M9 : ¬ Diverges (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle)
nd-N : ¬ Diverges (JN (Inner (ICn stBusy) SB-noblk) Cidle)
nd-Nh : ¬ Diverges (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks))
nd-N2 : ¬ Diverges (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks))
nd-N3 : ¬ Diverges (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret)
nd-N4 : ¬ Diverges (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret)
nd-N5 : ¬ Diverges (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret)
nd-N6 : ¬ Diverges (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle)
nd-N7 : ¬ Diverges (JN (Inner (ICn stIdle) (ISn stIdle)) Cret)
nd-N8 : ¬ Diverges (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle)
nd-N9 : ¬ Diverges (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle)
nd-W : ∀ {b} → ¬ Diverges (JN (Inner (ICn stStreaming) (SB-blk b)) Cidle)
nd-Wh : ∀ {b} → ¬ Diverges (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)))
nd-W2 : ∀ {b} → ¬ Diverges (JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)))
nd-W3 : ∀ {b} → ¬ Diverges (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret)
nd-W4 : ∀ {b} → ¬ Diverges (JN (Inner (CB-blk b) (ISn stStreaming)) Cret)
nd-W5 : ∀ {b} → ¬ Diverges (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle)
nd-V0 : ¬ Diverges (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle)
nd-Vocc1 : ∀ {b} → ¬ Diverges (JN (Inner (CB-blk b) (ISn stStreaming)) Cidle)
nd-W2e : ∀ {b₀ b₁} → ¬ Diverges (JN (Inner (CB-blk b₀) (SB-blk b₁)) Cidle)
nd-W2h : ∀ {b₀ b₁} → ¬ Diverges (JN (Inner (CB-blk b₀) (SB-loop stStreaming)) (Chold (mBlock b₁)))
nd-W2a : ∀ {b₀ b₁} → ¬ Diverges (JN (Inner (CB-blk b₀) (ISn stStreaming)) (Chold (mBlock b₁)))
nd-W2d : ∀ {b₁} → ¬ Diverges (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b₁)))
nd-W3e : ∀ {b₀ b₁ b₂} → ¬ Diverges (JN (Inner (CB-blk b₀) (SB-blk b₂)) (Chold (mBlock b₁)))
nd-W3d : ∀ {b₁ b₂} → ¬ Diverges (JN (Inner (CB-loop stStreaming) (SB-blk b₂)) (Chold (mBlock b₁)))
nd-W3a : ∀ {b₁ b₂} → ¬ Diverges (JN (Inner (ICn stStreaming) (SB-blk b₂)) (Chold (mBlock b₁)))
nd-W3b : ∀ {b₁ b₂} → ¬ Diverges (JN (Inner (CB-blk b₁) (SB-blk b₂)) Cret)
nd-BD0e : ¬ Diverges (JN (Inner (ICn stStreaming) SB-bdone) Cidle)
nd-BD0h : ¬ Diverges (JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone))
nd-BD0a : ¬ Diverges (JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone))
nd-BD1e : ∀ {b₀} → ¬ Diverges (JN (Inner (CB-blk b₀) SB-bdone) Cidle)
nd-BD1h : ∀ {b₀} → ¬ Diverges (JN (Inner (CB-blk b₀) (SB-loop stIdle)) (Chold mBatchDone))
nd-BD1a : ∀ {b₀} → ¬ Diverges (JN (Inner (CB-blk b₀) (ISn stIdle)) (Chold mBatchDone))
nd-BD1d : ¬ Diverges (JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone))
nd-BD2e : ∀ {b₀ b₁} → ¬ Diverges (JN (Inner (CB-blk b₀) SB-bdone) (Chold (mBlock b₁)))
nd-BD2d : ∀ {b₁} → ¬ Diverges (JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b₁)))
nd-BD2a : ∀ {b₁} → ¬ Diverges (JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b₁)))
nd-BD2b : ∀ {b₁} → ¬ Diverges (JN (Inner (CB-blk b₁) SB-bdone) Cret)
nd-G3 : ¬ Diverges (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret)
nd-G3a : ¬ Diverges (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret)
nd-G5 : ¬ Diverges (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret)
nd-G6 : ¬ Diverges (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle)
nd-G7 : ¬ Diverges (JN (Inner (ICn stBusy) (ISn stBusy)) Cret)
nd-I : ¬ Diverges (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle)
nd-WX1 : ∀ {b₁} → ¬ Diverges (JN (Inner (CB-loop stStreaming) (SB-blk b₁)) Cidle)
nd-WX2 : ∀ {b₁} → ¬ Diverges (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b₁)))
nd-WX3 : ∀ {b₂} → ¬ Diverges (JN (Inner (CB-loop stStreaming) (SB-blk b₂)) Cret)
nd-WX3a : ∀ {b₂} → ¬ Diverges (JN (Inner (ICn stStreaming) (SB-blk b₂)) Cret)
nd-BX1 : ¬ Diverges (JN (Inner (CB-loop stStreaming) SB-bdone) Cidle)
nd-BX2 : ¬ Diverges (JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone))
nd-BX3 : ¬ Diverges (JN (Inner (CB-loop stStreaming) SB-bdone) Cret)
nd-BX3a : ¬ Diverges (JN (Inner (ICn stStreaming) SB-bdone) Cret)

nd-A d = netA-noτ (d .Diverges.step)
nd-B d = nd-Bh (subst Diverges (netB-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Bh d with netBh-τ (d .Diverges.step)
... | inj₁ eq = nd-B2 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-B3 (subst Diverges eq (d .Diverges.rest))
nd-B2 d = nd-B3a (subst Diverges (netB2-τ (d .Diverges.step)) (d .Diverges.rest))
nd-B3 d with netB3-τ (d .Diverges.step)
... | inj₁ eq = nd-B3a (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-B5 (subst Diverges eq (d .Diverges.rest))
nd-B3a d = nd-B4 (subst Diverges (netB3a-τ (d .Diverges.step)) (d .Diverges.rest))
nd-B5 d = nd-B4 (subst Diverges (netB5-τ (d .Diverges.step)) (d .Diverges.rest))
nd-B4 d = netB4-noτ (d .Diverges.step)
nd-Fl d = nd-J (subst Diverges (netFl-τ (d .Diverges.step)) (d .Diverges.rest))
nd-J d = netJ-noτ (d .Diverges.step)
nd-Cdone d = nd-Cdh (subst Diverges (netCdone-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Cdh d with netCdh-τ (d .Diverges.step)
... | inj₁ eq = nd-Cd2 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-Cd3 (subst Diverges eq (d .Diverges.rest))
nd-Cd2 d = nd-Cd4 (subst Diverges (netCd2-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Cd3 d with netCd3-τ (d .Diverges.step)
... | inj₁ eq = nd-Cd4 (subst Diverges eq (d .Diverges.rest))
... | inj₂ (inj₁ eq) = nd-Cd5 (subst Diverges eq (d .Diverges.rest))
... | inj₂ (inj₂ eq) = nd-Cd6 (subst Diverges eq (d .Diverges.rest))
nd-Cd4 d with netCd4-τ (d .Diverges.step)
... | inj₁ eq = nd-Cd7 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-Cd8 (subst Diverges eq (d .Diverges.rest))
nd-Cd5 d with netCd5-τ (d .Diverges.step)
... | inj₁ eq = nd-Cd7 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-Cd9 (subst Diverges eq (d .Diverges.rest))
nd-Cd6 d with netCd6-τ (d .Diverges.step)
... | inj₁ eq = nd-Cd8 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-Cd9 (subst Diverges eq (d .Diverges.rest))
nd-Cd7 d = nd-Z (subst Diverges (netCd7-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Cd8 d = nd-Z (subst Diverges (netCd8-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Cd9 d = nd-Z (subst Diverges (netCd9-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Z d = netZ-noτ (d .Diverges.step)
nd-M d = nd-Mh (subst Diverges (netM-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Mh d with netMh-τ (d .Diverges.step)
... | inj₁ eq = nd-M2 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-M3 (subst Diverges eq (d .Diverges.rest))
nd-M2 d = nd-M5 (subst Diverges (netM2-τ (d .Diverges.step)) (d .Diverges.rest))
nd-M3 d with netM3-τ (d .Diverges.step)
... | inj₁ eq = nd-M4 (subst Diverges eq (d .Diverges.rest))
... | inj₂ (inj₁ eq) = nd-M5 (subst Diverges eq (d .Diverges.rest))
... | inj₂ (inj₂ eq) = nd-M6 (subst Diverges eq (d .Diverges.rest))
nd-M4 d with netM4-τ (d .Diverges.step)
... | inj₁ eq = nd-M7 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-M8 (subst Diverges eq (d .Diverges.rest))
nd-M5 d with netM5-τ (d .Diverges.step)
... | inj₁ eq = nd-M7 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-M9 (subst Diverges eq (d .Diverges.rest))
nd-M6 d with netM6-τ (d .Diverges.step)
... | inj₁ eq = nd-M8 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-M9 (subst Diverges eq (d .Diverges.rest))
nd-M7 d = nd-V0 (subst Diverges (netM7-τ (d .Diverges.step)) (d .Diverges.rest))
nd-M8 d = nd-V0 (subst Diverges (netM8-τ (d .Diverges.step)) (d .Diverges.rest))
nd-M9 d = nd-V0 (subst Diverges (netM9-τ (d .Diverges.step)) (d .Diverges.rest))
nd-N d = nd-Nh (subst Diverges (netN-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Nh d with netNh-τ (d .Diverges.step)
... | inj₁ eq = nd-N2 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-N3 (subst Diverges eq (d .Diverges.rest))
nd-N2 d = nd-N5 (subst Diverges (netN2-τ (d .Diverges.step)) (d .Diverges.rest))
nd-N3 d with netN3-τ (d .Diverges.step)
... | inj₁ eq = nd-N4 (subst Diverges eq (d .Diverges.rest))
... | inj₂ (inj₁ eq) = nd-N5 (subst Diverges eq (d .Diverges.rest))
... | inj₂ (inj₂ eq) = nd-N6 (subst Diverges eq (d .Diverges.rest))
nd-N4 d with netN4-τ (d .Diverges.step)
... | inj₁ eq = nd-N7 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-N8 (subst Diverges eq (d .Diverges.rest))
nd-N5 d with netN5-τ (d .Diverges.step)
... | inj₁ eq = nd-N7 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-N9 (subst Diverges eq (d .Diverges.rest))
nd-N6 d with netN6-τ (d .Diverges.step)
... | inj₁ eq = nd-N8 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-N9 (subst Diverges eq (d .Diverges.rest))
nd-N7 d = nd-A (subst Diverges (netN7-τ (d .Diverges.step)) (d .Diverges.rest))
nd-N8 d = nd-A (subst Diverges (netN8-τ (d .Diverges.step)) (d .Diverges.rest))
nd-N9 d = nd-A (subst Diverges (netN9-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W d = nd-Wh (subst Diverges (netW-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Wh d with netWh-τ (d .Diverges.step)
... | inj₁ eq = nd-W2 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-W3 (subst Diverges eq (d .Diverges.rest))
nd-W2 d = nd-W4 (subst Diverges (netW2-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W3 d with netW3-τ (d .Diverges.step)
... | inj₁ eq = nd-W4 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-W5 (subst Diverges eq (d .Diverges.rest))
nd-W4 d = nd-Vocc1 (subst Diverges (netW4-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W5 d = nd-Vocc1 (subst Diverges (netW5-τ (d .Diverges.step)) (d .Diverges.rest))
nd-V0 d = netV0-noτ (d .Diverges.step)
nd-Vocc1 d = netVocc1-noτ (d .Diverges.step)
nd-W2e d = nd-W2h (subst Diverges (netW2e-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W2h d = nd-W2a (subst Diverges (netW2h-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W2a d = netW2a-noτ (d .Diverges.step)
nd-W2d d = nd-W2 (subst Diverges (netW2d-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W3e d = netW3e-noτ (d .Diverges.step)
nd-W3d d = nd-W3a (subst Diverges (netW3d-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W3a d = nd-W3b (subst Diverges (netW3a-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W3b d = nd-W2e (subst Diverges (netW3b-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BD0e d = nd-BD0h (subst Diverges (netBD0e-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BD0h d with netBD0h-τ (d .Diverges.step)
... | inj₁ eq = nd-BD0a (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-N3 (subst Diverges eq (d .Diverges.rest))
nd-BD0a d = nd-N5 (subst Diverges (netBD0a-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BD1e d = nd-BD1h (subst Diverges (netBD1e-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BD1h d = nd-BD1a (subst Diverges (netBD1h-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BD1a d = netBD1a-noτ (d .Diverges.step)
nd-BD1d d = nd-BD0a (subst Diverges (netBD1d-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BD2e d = netBD2e-noτ (d .Diverges.step)
nd-BD2d d = nd-BD2a (subst Diverges (netBD2d-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BD2a d = nd-BD2b (subst Diverges (netBD2a-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BD2b d = nd-BD1e (subst Diverges (netBD2b-τ (d .Diverges.step)) (d .Diverges.rest))
nd-G3 d with netG3-τ (d .Diverges.step)
... | inj₁ eq = nd-G3a (subst Diverges eq (d .Diverges.rest))
... | inj₂ (inj₁ eq) = nd-G5 (subst Diverges eq (d .Diverges.rest))
... | inj₂ (inj₂ eq) = nd-G6 (subst Diverges eq (d .Diverges.rest))
nd-G3a d with netG3a-τ (d .Diverges.step)
... | inj₁ eq = nd-G7 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-Fl (subst Diverges eq (d .Diverges.rest))
nd-G5 d with netG5-τ (d .Diverges.step)
... | inj₁ eq = nd-G7 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-I (subst Diverges eq (d .Diverges.rest))
nd-G6 d with netG6-τ (d .Diverges.step)
... | inj₁ eq = nd-Fl (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-I (subst Diverges eq (d .Diverges.rest))
nd-G7 d = nd-J (subst Diverges (netG7-τ (d .Diverges.step)) (d .Diverges.rest))
nd-I d = nd-J (subst Diverges (netI-τ (d .Diverges.step)) (d .Diverges.rest))
nd-WX1 d with netWX1-τ (d .Diverges.step)
... | inj₁ eq = nd-W (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-WX2 (subst Diverges eq (d .Diverges.rest))
nd-WX2 d with netWX2-τ (d .Diverges.step)
... | inj₁ eq = nd-Wh (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-W2d (subst Diverges eq (d .Diverges.rest))
nd-WX3 d with netWX3-τ (d .Diverges.step)
... | inj₁ eq = nd-WX3a (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-WX1 (subst Diverges eq (d .Diverges.rest))
nd-WX3a d = nd-W (subst Diverges (netWX3a-τ (d .Diverges.step)) (d .Diverges.rest))
nd-BX1 d with netBX1-τ (d .Diverges.step)
... | inj₁ eq = nd-BD0e (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-BX2 (subst Diverges eq (d .Diverges.rest))
nd-BX2 d with netBX2-τ (d .Diverges.step)
... | inj₁ eq = nd-BD0h (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-BD1d (subst Diverges eq (d .Diverges.rest))
nd-BX3 d with netBX3-τ (d .Diverges.step)
... | inj₁ eq = nd-BX3a (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-BX1 (subst Diverges eq (d .Diverges.rest))
nd-BX3a d = nd-BD0e (subst Diverges (netBX3a-τ (d .Diverges.step)) (d .Diverges.rest))

------------------------------------------------------------------------
-- Good-graph visible-event router.  A surviving JN visible step is a
-- peer-solo apiBF; bfIn/bfOut are hidden, the copy offers no surviving event,
-- and there is no √ (the copy never returns).
------------------------------------------------------------------------

-- the copy states never exhibit a surviving (non-ioBF) visible event.
Cidle-mem : ∀ {X} {ee : BFNetEv X} {a Q'} → Cidle ─[ ev (evl (record { A = X ; e = ee ; a = a })) ]─► Q' → ioBF .EventSet.mem (X , ee) a
Cidle-mem {ee = bfIn} (sVis refl q) = Poly.tt
Cidle-mem {ee = bfMsg} (sVis refl ())
Cidle-mem {ee = bfOut} (sVis refl ())
Cidle-mem {ee = apiBF m} (sVis refl ())
Chold-mem : ∀ {m X} {ee : BFNetEv X} {a Q'} → Chold m ─[ ev (evl (record { A = X ; e = ee ; a = a })) ]─► Q' → ioBF .EventSet.mem (X , ee) a
Chold-mem {ee = bfOut} (sVis refl q) = Poly.tt
Chold-mem {ee = bfMsg} (sVis refl ())
Chold-mem {ee = bfIn} (sVis refl ())
Chold-mem {ee = apiBF m} (sVis refl ())
Cret-mem : ∀ {X} {ee : BFNetEv X} {a Q'} → Cret ─[ ev (evl (record { A = X ; e = ee ; a = a })) ]─► Q' → ioBF .EventSet.mem (X , ee) a
Cret-mem (sVis () _)

-- the generic JN visible-event router: classify a surviving visible step into a
-- peer-solo apiBF (jeClL / jeSvR / jeBoth).  The copy contributes no surviving
-- event (its events ∈ ioBF), and bfIn/bfOut/bfMsg from peers are hidden/absent.
JN-gev : ∀ {cl sv cp m a W″}
       → (∀ {X} {ee : BFNetEv X} {a Q'} → cp ─[ ev (evl (record { A = X ; e = ee ; a = a })) ]─► Q' → ioBF .EventSet.mem (X , ee) a)
       → JN (Inner cl sv) cp ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► W″
       → JNev cl sv cp a (apiBF m) W″
JN-gev {cl} {sv} {cp} {m} {a} cpMem st
  with Hide-ev-elim ioBF (NetOps.Par ioBF mrg2 (Inner cl sv) cp) st
... | heV P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner cl sv) cp pev
...   | evSync mm cstp sstp = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (¬m (cpMem cst))
...   | evBoth ¬m2 ist cst = ⊥-elim (¬m (cpMem cst))
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg cl sv ist
...     | evL ¬m3 clst = jeClL clst
...     | evR ¬m3 svst = jeSvR svst
...     | evBoth ¬m3 clst svst = jeBoth clst svst

------------------------------------------------------------------------
-- Peers never offer the direct-rendezvous event bfMsg (network peers use
-- bfIn/bfOut/apiBF only); needed to refute the bfMsg branch of Good.gev.
------------------------------------------------------------------------

-- client iter states offer no bfMsg.
ICn-no-bfMsg : ∀ {s a P'} → ICn s ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥
ICn-no-bfMsg {stIdle} (sVis refl ())
ICn-no-bfMsg {stBusy} (sVis refl ())
ICn-no-bfMsg {stStreaming} (sVis refl ())
ICn-no-bfMsg {stDone} (sVis () _)
-- server iter states offer no bfMsg.
ISn-no-bfMsg : ∀ {s a Q'} → ISn s ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
ISn-no-bfMsg {stIdle} (sVis refl ())
ISn-no-bfMsg {stBusy} (sVis refl ())
ISn-no-bfMsg {stStreaming} (sVis refl ())
ISn-no-bfMsg {stDone} (sVis () _)
-- client transients offer no bfMsg.
CBreq-no-bfMsg : ∀ {r a P'} → CB-req r ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥
CBreq-no-bfMsg (sVis refl ())
CBcdone-no-bfMsg : ∀ {a P'} → CB-cdone ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥
CBcdone-no-bfMsg (sVis refl ())
CBblk-no-bfMsg : ∀ {b a P'} → CB-blk b ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥
CBblk-no-bfMsg (sVis refl ())
CBloop-no-bfMsg : ∀ {s a P'} → CB-loop s ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥
CBloop-no-bfMsg (sVis () _)
-- server transients offer no bfMsg.
SBreq-no-bfMsg : ∀ {r a Q'} → SB-req r ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
SBreq-no-bfMsg (sVis refl ())
SBsbatch-no-bfMsg : ∀ {a Q'} → SB-sbatch ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
SBsbatch-no-bfMsg (sVis refl ())
SBnoblk-no-bfMsg : ∀ {a Q'} → SB-noblk ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
SBnoblk-no-bfMsg (sVis refl ())
SBblk-no-bfMsg : ∀ {b a Q'} → SB-blk b ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
SBblk-no-bfMsg (sVis refl ())
SBbdone-no-bfMsg : ∀ {a Q'} → SB-bdone ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
SBbdone-no-bfMsg (sVis refl ())
SBloop-no-bfMsg : ∀ {s a Q'} → SB-loop s ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
SBloop-no-bfMsg (sVis () _)

-- copy states offer no bfMsg.
Cidle-no-bfMsg : ∀ {a Q'} → Cidle ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
Cidle-no-bfMsg (sVis refl ())
Chold-no-bfMsg : ∀ {m a Q'} → Chold m ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
Chold-no-bfMsg (sVis refl ())
Cret-no-bfMsg : ∀ {a Q'} → Cret ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥
Cret-no-bfMsg (sVis () _)

-- a JN bfMsg-labelled visible step is impossible (no component offers bfMsg).
JN-no-bfMsg : ∀ {cl sv cp a P'}
            → (∀ {a P'} → cl ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥)
            → (∀ {a Q'} → sv ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥)
            → (∀ {a Q'} → cp ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥)
            → NetOps.Par ioBF mrg2 (Inner cl sv) cp ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥
JN-no-bfMsg {cl} {sv} {cp} clNo svNo cpNo pev with Par-ev-elim ioBF mrg2 (Inner cl sv) cp pev
... | evSync mm cstp sstp = mm
... | evR ¬m2 cst = cpNo cst
... | evBoth ¬m2 ist cst = cpNo cst
... | evL ¬m2 ist with Par-ev-elim ∅ES mrg cl sv ist
...   | evL ¬m3 clst = clNo clst
...   | evR ¬m3 svst = svNo svst
...   | evBoth ¬m3 clst svst = clNo clst

-- a JN visible step is impossible when NEITHER peer offers any apiBF (and the
-- copy offers none); used for the gev of pure-transient configs.
JN-gev-none : ∀ {cl sv cp} {W″ : PTree BFNetEv (ExtI BFNetEv) Rr} {e : Event√ Rr}
            → (∀ {m a P'} → cl ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► P' → ⊥)
            → (∀ {m a Q'} → sv ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q' → ⊥)
            → (∀ {a P'} → cl ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► P' → ⊥)
            → (∀ {a Q'} → sv ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥)
            → (∀ {a Q'} → cp ─[ ev (evl (record { A = BFMsg ; e = bfMsg ; a = a })) ]─► Q' → ⊥)
            → (∀ {m a Q'} → cp ─[ ev (evl (record { A = ApiBFCar m ; e = apiBF m ; a = a })) ]─► Q' → ⊥)
            → (∀ {r} → PTree.force (NetOps.Par ioBF mrg2 (Inner cl sv) cp) ≡ ret r → ⊥)
            → JN (Inner cl sv) cp ─[ ev e ]─► W″ → ⊥
JN-gev-none {cl} {sv} {cp} clNoA svNoA clNoM svNoM cpNoM cpNoA noRet st
  with Hide-ev-elim ioBF (NetOps.Par ioBF mrg2 (Inner cl sv) cp) st
... | he√ eqf = noRet eqf
... | heV {e = bfMsg} P' ¬m pev = JN-no-bfMsg clNoM svNoM cpNoM pev
... | heV {e = bfIn} P' ¬m pev = ¬m Poly.tt
... | heV {e = bfOut} P' ¬m pev = ¬m Poly.tt
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner cl sv) cp pev
...   | evSync mm cstp sstp = mm
...   | evR ¬m2 cst = cpNoA cst
...   | evBoth ¬m2 ist cst = cpNoA cst
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg cl sv ist
...     | evL ¬m3 clst = clNoA clst
...     | evR ¬m3 svst = svNoA svst
...     | evBoth ¬m3 clst svst = clNoA clst

-- 24 new mixed-pipelining configs: τ-inversion lemmas.

netCdR-τ : ∀ {W″} → JN (Inner CB-cdone (ISn stIdle)) Cret ─[ τ ]─► W″
        → W″ ≡ JN (Inner CB-cdone (ISn stIdle)) Cidle
netCdR-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBcdone-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netCdR-τ st | jInL clst cst = ⊥-elim (Cret-no-ev cst)
netCdR-τ st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netCdR-τ st | jInB clst svst = ⊥-elim (ISidle-no-bfin svst)
netCdR-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netCdR-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netCdR-τ st | jOutB clst svst = ⊥-elim (CBcdone-no-bfout clst)

netCdSi-τ : ∀ {W″} → JN (Inner CB-cdone (SB-loop stIdle)) Cidle ─[ τ ]─► W″
       → (W″ ≡ JN (Inner CB-cdone (ISn stIdle)) Cidle)
       ⊎ (W″ ≡ JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone))
netCdSi-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBcdone-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netCdSi-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netCdSi-τ st | jInL clst cst with CBcdone-bfin clst | Cidle-bfin cst
...   | (refl , refl) | refl = inj₂ refl
netCdSi-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netCdSi-τ st | jInB clst svst = ⊥-elim (SBloop-no-ev svst)
netCdSi-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netCdSi-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netCdSi-τ st | jOutB clst svst = ⊥-elim (CBcdone-no-bfout clst)

netCdSr-τ : ∀ {W″} → JN (Inner CB-cdone (SB-loop stIdle)) Cret ─[ τ ]─► W″
       → (W″ ≡ JN (Inner CB-cdone (ISn stIdle)) Cret)
       ⊎ (W″ ≡ JN (Inner CB-cdone (SB-loop stIdle)) Cidle)
netCdSr-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBcdone-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netCdSr-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netCdSr-τ st | jInL clst cst = ⊥-elim (Cret-no-ev cst)
netCdSr-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netCdSr-τ st | jInB clst svst = ⊥-elim (SBloop-no-ev svst)
netCdSr-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netCdSr-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netCdSr-τ st | jOutB clst svst = ⊥-elim (CBcdone-no-bfout clst)

netLbN2-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks)
netLbN2-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netLbN2-τ st | jSvτ svst = ⊥-elim (ISidle-noτ svst)
netLbN2-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netLbN2-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbN2-τ st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netLbN2-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbN2-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netLbN2-τ st | jOutR cst svst with Chold-bfout cst
...   | (refl , refl) with ISidle-bfout svst
...     | inj₁ (_ , () , _)
...     | inj₂ (() , _)
netLbN2-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbM2-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch)
netLbM2-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netLbM2-τ st | jSvτ svst = ⊥-elim (ISstr-noτ svst)
netLbM2-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netLbM2-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbM2-τ st | jInR svst cst = ⊥-elim (ISstr-no-bfin svst)
netLbM2-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbM2-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netLbM2-τ st | jOutR cst svst = ⊥-elim (ISstr-no-bfout svst)
netLbM2-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbBDsb-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch)
netLbBDsb-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netLbBDsb-τ st | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
netLbBDsb-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netLbBDsb-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbBDsb-τ st | jInR svst cst = ⊥-elim (Chold-no-bfin cst)
netLbBDsb-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbBDsb-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netLbBDsb-τ st | jOutR cst svst = ⊥-elim (SBbdone-no-bfout svst)
netLbBDsb-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbBLKsb-τ : ∀ {b W″} → JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch)
netLbBLKsb-τ {b} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = refl
netLbBLKsb-τ {b} st | jSvτ svst = ⊥-elim (SBblk-noτ svst)
netLbBLKsb-τ {b} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netLbBLKsb-τ {b} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbBLKsb-τ {b} st | jInR svst cst = ⊥-elim (Chold-no-bfin cst)
netLbBLKsb-τ {b} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbBLKsb-τ {b} st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netLbBLKsb-τ {b} st | jOutR cst svst = ⊥-elim (SBblk-no-bfout svst)
netLbBLKsb-τ {b} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbNh-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks))
       ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks))
netLbNh-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netLbNh-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netLbNh-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netLbNh-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbNh-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netLbNh-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbNh-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netLbNh-τ st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netLbNh-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbBh-τ : ∀ {r W″} → JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)))
       ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)))
netLbBh-τ {r} st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netLbBh-τ {r} st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netLbBh-τ {r} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netLbBh-τ {r} st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbBh-τ {r} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netLbBh-τ {r} st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbBh-τ {r} st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netLbBh-τ {r} st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netLbBh-τ {r} st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbMh-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch))
       ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch))
netLbMh-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netLbMh-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netLbMh-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netLbMh-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbMh-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netLbMh-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbMh-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netLbMh-τ st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netLbMh-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbNi-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) SB-noblk) Cidle ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (ICn stBusy) SB-noblk) Cidle)
       ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks))
netLbNi-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netLbNi-τ st | jSvτ svst = ⊥-elim (SBnoblk-noτ svst)
netLbNi-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netLbNi-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbNi-τ st | jInR svst cst with SBnoblk-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = inj₂ refl
netLbNi-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbNi-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netLbNi-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netLbNi-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbNr-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) SB-noblk) Cret ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (ICn stBusy) SB-noblk) Cret)
       ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) SB-noblk) Cidle)
netLbNr-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netLbNr-τ st | jSvτ svst = ⊥-elim (SBnoblk-noτ svst)
netLbNr-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netLbNr-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbNr-τ st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netLbNr-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbNr-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netLbNr-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netLbNr-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbMi-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) SB-sbatch) Cidle ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (ICn stBusy) SB-sbatch) Cidle)
       ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch))
netLbMi-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netLbMi-τ st | jSvτ svst = ⊥-elim (SBsbatch-noτ svst)
netLbMi-τ st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netLbMi-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbMi-τ st | jInR svst cst with SBsbatch-bfin svst | Cidle-bfin cst
...   | (refl , refl) | refl = inj₂ refl
netLbMi-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbMi-τ st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netLbMi-τ st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netLbMi-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLbMr-τ : ∀ {W″} → JN (Inner (CB-loop stBusy) SB-sbatch) Cret ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (ICn stBusy) SB-sbatch) Cret)
       ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) SB-sbatch) Cidle)
netLbMr-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netLbMr-τ st | jSvτ svst = ⊥-elim (SBsbatch-noτ svst)
netLbMr-τ st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netLbMr-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLbMr-τ st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netLbMr-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLbMr-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netLbMr-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netLbMr-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netLdCdh-τ : ∀ {W″} → JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone) ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone))
       ⊎ (W″ ≡ JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone))
netLdCdh-τ st with JN-τ-cases st
... | jClτ clst with CBloop-τ clst
...   | refl = inj₁ refl
netLdCdh-τ st | jSvτ svst with SBloop-τ svst
...   | refl = inj₂ refl
netLdCdh-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netLdCdh-τ st | jInL clst cst = ⊥-elim (CBloop-no-ev clst)
netLdCdh-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netLdCdh-τ st | jInB clst svst = ⊥-elim (CBloop-no-ev clst)
netLdCdh-τ st | jOutL cst clst = ⊥-elim (CBloop-no-ev clst)
netLdCdh-τ st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netLdCdh-τ st | jOutB clst svst = ⊥-elim (CBloop-no-ev clst)

netReqR-τ : ∀ {r W″} → JN (Inner (CB-req r) (ISn stIdle)) Cret ─[ τ ]─► W″
        → W″ ≡ JN (Inner (CB-req r) (ISn stIdle)) Cidle
netReqR-τ {r} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBreq-noτ clst)
... | jSvτ svst = ⊥-elim (ISidle-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netReqR-τ {r} st | jInL clst cst = ⊥-elim (Cret-no-ev cst)
netReqR-τ {r} st | jInR svst cst = ⊥-elim (ISidle-no-bfin svst)
netReqR-τ {r} st | jInB clst svst = ⊥-elim (ISidle-no-bfin svst)
netReqR-τ {r} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netReqR-τ {r} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netReqR-τ {r} st | jOutB clst svst = ⊥-elim (CBreq-no-bfout clst)

netReqSi-τ : ∀ {r W″} → JN (Inner (CB-req r) (SB-loop stIdle)) Cidle ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (CB-req r) (ISn stIdle)) Cidle)
       ⊎ (W″ ≡ JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)))
netReqSi-τ {r} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBreq-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netReqSi-τ {r} st | jCpτ cpst = ⊥-elim (Cidle-noτ cpst)
netReqSi-τ {r} st | jInL clst cst with CBreq-bfin clst | Cidle-bfin cst
...   | (refl , refl) | refl = inj₂ refl
netReqSi-τ {r} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netReqSi-τ {r} st | jInB clst svst = ⊥-elim (SBloop-no-ev svst)
netReqSi-τ {r} st | jOutL cst clst = ⊥-elim (Cidle-no-bfout′ cst)
netReqSi-τ {r} st | jOutR cst svst = ⊥-elim (Cidle-no-bfout′ cst)
netReqSi-τ {r} st | jOutB clst svst = ⊥-elim (CBreq-no-bfout clst)

netReqSr-τ : ∀ {r W″} → JN (Inner (CB-req r) (SB-loop stIdle)) Cret ─[ τ ]─► W″
       → (W″ ≡ JN (Inner (CB-req r) (ISn stIdle)) Cret)
       ⊎ (W″ ≡ JN (Inner (CB-req r) (SB-loop stIdle)) Cidle)
netReqSr-τ {r} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (CBreq-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = inj₁ refl
netReqSr-τ {r} st | jCpτ cpst with Cret-τ cpst
...   | refl = inj₂ refl
netReqSr-τ {r} st | jInL clst cst = ⊥-elim (Cret-no-ev cst)
netReqSr-τ {r} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netReqSr-τ {r} st | jInB clst svst = ⊥-elim (SBloop-no-ev svst)
netReqSr-τ {r} st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netReqSr-τ {r} st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netReqSr-τ {r} st | jOutB clst svst = ⊥-elim (CBreq-no-bfout clst)

netIBbdsb-τ : ∀ {W″} → JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (CB-loop stStreaming) SB-bdone) Cret
netIBbdsb-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (SBbdone-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
... | jInR svst cst = ⊥-elim (Chold-no-bfin cst)
... | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICbusy-bfout clst
...     | inj₁ (refl , refl) = refl
...     | inj₂ (() , _)
netIBbdsb-τ st | jOutR cst svst = ⊥-elim (SBbdone-no-bfout svst)
netIBbdsb-τ st | jOutB clst svst = ⊥-elim (SBbdone-no-bfout svst)

netIBblksb-τ : ∀ {b W″} → JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret
netIBblksb-τ {b} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (SBblk-noτ svst)
... | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
... | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
... | jInR svst cst = ⊥-elim (Chold-no-bfin cst)
... | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
... | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICbusy-bfout clst
...     | inj₁ (refl , refl) = refl
...     | inj₂ (() , _)
netIBblksb-τ {b} st | jOutR cst svst = ⊥-elim (SBblk-no-bfout svst)
netIBblksb-τ {b} st | jOutB clst svst = ⊥-elim (SBblk-no-bfout svst)

netIBSirr-τ : ∀ {r W″} → JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r))
netIBSirr-τ {r} st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netIBSirr-τ {r} st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netIBSirr-τ {r} st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netIBSirr-τ {r} st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netIBSirr-τ {r} st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netIBSirr-τ {r} st | jOutL cst clst with Chold-bfout cst
...   | (refl , refl) with ICbusy-bfout clst
...     | inj₁ (() , _)
...     | inj₂ (() , _)
netIBSirr-τ {r} st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netIBSirr-τ {r} st | jOutB clst svst = ⊥-elim (SBloop-no-ev svst)

netIBNr-τ : ∀ {W″} → JN (Inner (ICn stBusy) SB-noblk) Cret ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) SB-noblk) Cidle
netIBNr-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (SBnoblk-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netIBNr-τ st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netIBNr-τ st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netIBNr-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netIBNr-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netIBNr-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netIBNr-τ st | jOutB clst svst = ⊥-elim (SBnoblk-no-bfout svst)

netIBMr-τ : ∀ {W″} → JN (Inner (ICn stBusy) SB-sbatch) Cret ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stBusy) SB-sbatch) Cidle
netIBMr-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICbusy-noτ clst)
... | jSvτ svst = ⊥-elim (SBsbatch-noτ svst)
... | jCpτ cpst with Cret-τ cpst
...   | refl = refl
netIBMr-τ st | jInL clst cst = ⊥-elim (ICbusy-no-bfin clst)
netIBMr-τ st | jInR svst cst = ⊥-elim (Cret-no-ev cst)
netIBMr-τ st | jInB clst svst = ⊥-elim (ICbusy-no-bfin clst)
netIBMr-τ st | jOutL cst clst = ⊥-elim (Cret-no-ev cst)
netIBMr-τ st | jOutR cst svst = ⊥-elim (Cret-no-ev cst)
netIBMr-τ st | jOutB clst svst = ⊥-elim (SBsbatch-no-bfout svst)

netIDScd-τ : ∀ {W″} → JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone) ─[ τ ]─► W″
        → W″ ≡ JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone)
netIDScd-τ st with JN-τ-cases st
... | jClτ clst = ⊥-elim (ICdone-noτ clst)
... | jSvτ svst with SBloop-τ svst
...   | refl = refl
netIDScd-τ st | jCpτ cpst = ⊥-elim (Chold-noτ cpst)
netIDScd-τ st | jInL clst cst = ⊥-elim (ICdone-no-bfin clst)
netIDScd-τ st | jInR svst cst = ⊥-elim (SBloop-no-ev svst)
netIDScd-τ st | jInB clst svst = ⊥-elim (ICdone-no-bfin clst)
netIDScd-τ st | jOutL cst clst = ⊥-elim (ICdone-no-bfout clst)
netIDScd-τ st | jOutR cst svst = ⊥-elim (SBloop-no-ev svst)
netIDScd-τ st | jOutB clst svst = ⊥-elim (ICdone-no-bfout clst)

-- 24 new configs: ¬ Diverges.

nd-CdR : ¬ Diverges (JN (Inner CB-cdone (ISn stIdle)) Cret)
nd-CdSi : ¬ Diverges (JN (Inner CB-cdone (SB-loop stIdle)) Cidle)
nd-CdSr : ¬ Diverges (JN (Inner CB-cdone (SB-loop stIdle)) Cret)
nd-LbN2 : ¬ Diverges (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks))
nd-LbM2 : ¬ Diverges (JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch))
nd-LbBDsb : ¬ Diverges (JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch))
nd-LbBLKsb : ∀ {b} → ¬ Diverges (JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch))
nd-LbNh : ¬ Diverges (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks))
nd-LbBh : ∀ {r} → ¬ Diverges (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)))
nd-LbMh : ¬ Diverges (JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch))
nd-LbNi : ¬ Diverges (JN (Inner (CB-loop stBusy) SB-noblk) Cidle)
nd-LbNr : ¬ Diverges (JN (Inner (CB-loop stBusy) SB-noblk) Cret)
nd-LbMi : ¬ Diverges (JN (Inner (CB-loop stBusy) SB-sbatch) Cidle)
nd-LbMr : ¬ Diverges (JN (Inner (CB-loop stBusy) SB-sbatch) Cret)
nd-LdCdh : ¬ Diverges (JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone))
nd-ReqR : ∀ {r} → ¬ Diverges (JN (Inner (CB-req r) (ISn stIdle)) Cret)
nd-ReqSi : ∀ {r} → ¬ Diverges (JN (Inner (CB-req r) (SB-loop stIdle)) Cidle)
nd-ReqSr : ∀ {r} → ¬ Diverges (JN (Inner (CB-req r) (SB-loop stIdle)) Cret)
nd-IBbdsb : ¬ Diverges (JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch))
nd-IBblksb : ∀ {b} → ¬ Diverges (JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch))
nd-IBSirr : ∀ {r} → ¬ Diverges (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)))
nd-IBNr : ¬ Diverges (JN (Inner (ICn stBusy) SB-noblk) Cret)
nd-IBMr : ¬ Diverges (JN (Inner (ICn stBusy) SB-sbatch) Cret)
nd-IDScd : ¬ Diverges (JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone))

nd-CdR d = nd-Cdone (subst Diverges (netCdR-τ (d .Diverges.step)) (d .Diverges.rest))
nd-CdSi d with netCdSi-τ (d .Diverges.step)
... | inj₁ eq = nd-Cdone (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-LdCdh (subst Diverges eq (d .Diverges.rest))
nd-CdSr d with netCdSr-τ (d .Diverges.step)
... | inj₁ eq = nd-CdR (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-CdSi (subst Diverges eq (d .Diverges.rest))
nd-LbN2 d = nd-N2 (subst Diverges (netLbN2-τ (d .Diverges.step)) (d .Diverges.rest))
nd-LbM2 d = nd-M2 (subst Diverges (netLbM2-τ (d .Diverges.step)) (d .Diverges.rest))
nd-LbBDsb d = nd-IBbdsb (subst Diverges (netLbBDsb-τ (d .Diverges.step)) (d .Diverges.rest))
nd-LbBLKsb {b} d = nd-IBblksb (subst Diverges (netLbBLKsb-τ (d .Diverges.step)) (d .Diverges.rest))
nd-LbNh d with netLbNh-τ (d .Diverges.step)
... | inj₁ eq = nd-Nh (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-LbN2 (subst Diverges eq (d .Diverges.rest))
nd-LbBh {r} d with netLbBh-τ (d .Diverges.step)
... | inj₁ eq = nd-IBSirr (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-Bh (subst Diverges eq (d .Diverges.rest))
nd-LbMh d with netLbMh-τ (d .Diverges.step)
... | inj₁ eq = nd-Mh (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-LbM2 (subst Diverges eq (d .Diverges.rest))
nd-LbNi d with netLbNi-τ (d .Diverges.step)
... | inj₁ eq = nd-N (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-LbNh (subst Diverges eq (d .Diverges.rest))
nd-LbNr d with netLbNr-τ (d .Diverges.step)
... | inj₁ eq = nd-IBNr (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-LbNi (subst Diverges eq (d .Diverges.rest))
nd-LbMi d with netLbMi-τ (d .Diverges.step)
... | inj₁ eq = nd-M (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-LbMh (subst Diverges eq (d .Diverges.rest))
nd-LbMr d with netLbMr-τ (d .Diverges.step)
... | inj₁ eq = nd-IBMr (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-LbMi (subst Diverges eq (d .Diverges.rest))
nd-LdCdh d with netLdCdh-τ (d .Diverges.step)
... | inj₁ eq = nd-IDScd (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-Cdh (subst Diverges eq (d .Diverges.rest))
nd-ReqR {r} d = nd-B (subst Diverges (netReqR-τ (d .Diverges.step)) (d .Diverges.rest))
nd-ReqSi {r} d with netReqSi-τ (d .Diverges.step)
... | inj₁ eq = nd-B (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-LbBh (subst Diverges eq (d .Diverges.rest))
nd-ReqSr {r} d with netReqSr-τ (d .Diverges.step)
... | inj₁ eq = nd-ReqR (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-ReqSi (subst Diverges eq (d .Diverges.rest))
nd-IBbdsb d = nd-BX3 (subst Diverges (netIBbdsb-τ (d .Diverges.step)) (d .Diverges.rest))
nd-IBblksb {b} d = nd-WX3 (subst Diverges (netIBblksb-τ (d .Diverges.step)) (d .Diverges.rest))
nd-IBSirr {r} d = nd-B2 (subst Diverges (netIBSirr-τ (d .Diverges.step)) (d .Diverges.rest))
nd-IBNr d = nd-N (subst Diverges (netIBNr-τ (d .Diverges.step)) (d .Diverges.rest))
nd-IBMr d = nd-M (subst Diverges (netIBMr-τ (d .Diverges.step)) (d .Diverges.rest))
nd-IDScd d = nd-Cd2 (subst Diverges (netIDScd-τ (d .Diverges.step)) (d .Diverges.rest))

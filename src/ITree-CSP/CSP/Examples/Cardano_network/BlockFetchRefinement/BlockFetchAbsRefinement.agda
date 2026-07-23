{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Task 2: divergence-freedom of the hidden BlockFetch processes ⇒ ⊑D.
--
-- The two hidden BlockFetch processes `clientServerBF ∖ msgBF` (impl) and
-- `BFabstract ∖ msgBF` (spec) are divergence-free: every hidden message-τ
-- is bracketed by an observable API event, so no infinite τ-run exists.
-- This yields the ⊑D half of `(BFabstract ∖ msgBF) ⊑FD (clientServerBF ∖ msgBF)`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.BlockFetchRefinement.BlockFetchAbsRefinement (p : Params) where

open import Level using (lift)
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

-- the semantics at the abstract BlockFetch alphabet
open import Semantics.LTS {E = BFAbsEv} {I = ExtI BFAbsEv} hiding (Diverges)
open import Semantics.DRBisim {E = BFAbsEv} {I = ExtI BFAbsEv}
  using (Diverges; deadlock-converges; deadlock-no-τ)
open import Semantics.Failures {E = BFAbsEv} {I = ExtI BFAbsEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.FailuresDivergences {E = BFAbsEv} {I = ExtI BFAbsEv}
  using (_⊑D_; divergences; IsDivergence)

-- the hide / parallel trace-law single-step inversions, at the abstract alphabet
open import CSP.Laws.Traces.TraceLawsHide BFAbsEv-≟
  using (Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√)
open import CSP.Laws.Traces.TraceLawsParallelElim BFAbsEv-≟
  using (Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)

open AbsOps using (_∖_; Par⊤; Par; iter; Ret; Output; Prefix; Prefix₀; pchoice; viewV; EventSet)

------------------------------------------------------------------------
-- The coinductive divergence-freedom invariant (mirrors `GoodC`).
------------------------------------------------------------------------

-- `Good W` certifies that the hidden state `W` is divergence-free and that
-- this property is preserved by every τ- and visible-step out of `W`.
record Good (W : PTree BFAbsEv (ExtI BFAbsEv) Rr) : Set₁ where
  coinductive
  field
    gnd : ¬ Diverges W
    gτ  : ∀ {W′} → W ─[ τ ]─► W′ → Good W′
    gev : ∀ {W′} {e : Event√ Rr} → W ─[ ev e ]─► W′ → Good W′
open Good

-- the weak-reach walk: a `Good` invariant rules out divergence at any
-- weakly-reachable state (identical to `copy-reach-noDiv`'s `go`).
go-reach : ∀ {s W W′} → Good W → W ⟹⟨ s ⟩ W′ → ¬ Diverges W′
go-reach g ⟹-refl         = g .gnd
go-reach g (⟹-τ  st rest) = go-reach (g .gτ  st) rest
go-reach g (⟹-ev st rest) = go-reach (g .gev st) rest

-- abbreviation: the SPEC iteration at a state
IT : BFState → PTree BFAbsEv (ExtI BFAbsEv) Rr
IT s = AbsOps.iter absStep s

-- a pchoice SPEC state (stIdle/stBusy/stStreaming) has no hidden τ: its τ-part is
-- empty and every offered visible event is an apiBF (∉ msgBF), so no message hides.
spec-noτ : ∀ {W′} (s : BFState) → ¬ ((IT s AbsOps.∖ msgBF) ─[ τ ]─► W′)
spec-noτ s st with Hide-τ-elim msgBF (IT s) st
spec-noτ stIdle _ | hτP P' (sSil ()) refl
spec-noτ stIdle _ | hτP P' (sTau refl ()) refl
spec-noτ stIdle _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
spec-noτ stIdle _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
spec-noτ stIdle _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
spec-noτ stIdle _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
spec-noτ stIdle _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
spec-noτ stIdle _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
spec-noτ stIdle _ | hτH {e = apiBF m}         P' mem stp refl = mem
spec-noτ stBusy _ | hτP P' (sSil ()) refl
spec-noτ stBusy _ | hτP P' (sTau refl ()) refl
spec-noτ stBusy _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
spec-noτ stBusy _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
spec-noτ stBusy _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
spec-noτ stBusy _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
spec-noτ stBusy _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
spec-noτ stBusy _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
spec-noτ stBusy _ | hτH {e = apiBF m}         P' mem stp refl = mem
spec-noτ stStreaming _ | hτP P' (sSil ()) refl
spec-noτ stStreaming _ | hτP P' (sTau refl ()) refl
spec-noτ stStreaming _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
spec-noτ stStreaming _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
spec-noτ stStreaming _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
spec-noτ stStreaming _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
spec-noτ stStreaming _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
spec-noτ stStreaming _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
spec-noτ stStreaming _ | hτH {e = apiBF m}         P' mem stp refl = mem
spec-noτ stDone _ | hτP P' (sSil ()) refl
spec-noτ stDone _ | hτP P' (sTau () _) refl
spec-noτ stDone _ | hτH P' mem (sVis () _) refl

-- transient: just past the stIdle/request apiBF — Output Msg\!range (a hidden τ).
S-req : ChainRange → PTree BFAbsEv (ExtI BFAbsEv) Rr
S-req range = AbsOps.iter-bind
  (AbsOps.Output MsgRequestRange range
     (AbsOps.Output (apiBF reqBFRange) range (AbsOps.Ret (inj₁ stBusy)))) absStep

-- transient: stIdle/request, after the Msg hidden — offering the reqBFRange api.
S-req2 : ChainRange → PTree BFAbsEv (ExtI BFAbsEv) Rr
S-req2 range = AbsOps.iter-bind
  (AbsOps.Output (apiBF reqBFRange) range (AbsOps.Ret (inj₁ stBusy))) absStep

-- transient: an iter loop-back point (ret (inj₁ s) ⇒ sil (IT s)).
S-loop : BFState → PTree BFAbsEv (ExtI BFAbsEv) Rr
S-loop s = AbsOps.iter-bind (AbsOps.Ret (inj₁ s)) absStep

-- transient: stIdle/client-done, the MsgClientDone prefix (hidden τ).
S-cdone : PTree BFAbsEv (ExtI BFAbsEv) Rr
S-cdone = AbsOps.iter-bind
  (AbsOps.Prefix₀ MsgClientDone (AbsOps.Ret (inj₁ stDone))) absStep

-- transient: stBusy/start-batch, the MsgStartBatch prefix (hidden τ).
S-sbatch : PTree BFAbsEv (ExtI BFAbsEv) Rr
S-sbatch = AbsOps.iter-bind
  (AbsOps.Prefix₀ MsgStartBatch (AbsOps.Ret (inj₁ stStreaming))) absStep

-- transient: stBusy/no-blocks, the MsgNoBlocks prefix (hidden τ).
S-noblk : PTree BFAbsEv (ExtI BFAbsEv) Rr
S-noblk = AbsOps.iter-bind
  (AbsOps.Prefix₀ MsgNoBlocks (AbsOps.Ret (inj₁ stIdle))) absStep

-- transient: stStreaming/block, the MsgBlock\!b offer (hidden τ).
S-blk : Block → PTree BFAbsEv (ExtI BFAbsEv) Rr
S-blk b = AbsOps.iter-bind
  (AbsOps.Output MsgBlock b
     (AbsOps.Output (apiBF recvBFBlock) b (AbsOps.Ret (inj₁ stStreaming)))) absStep

-- transient: stStreaming/block, after Msg hidden — offering the recvBFBlock api.
S-blk2 : Block → PTree BFAbsEv (ExtI BFAbsEv) Rr
S-blk2 b = AbsOps.iter-bind
  (AbsOps.Output (apiBF recvBFBlock) b (AbsOps.Ret (inj₁ stStreaming))) absStep

-- transient: stStreaming/batch-done, the MsgBatchDone prefix (hidden τ).
S-bdone : PTree BFAbsEv (ExtI BFAbsEv) Rr
S-bdone = AbsOps.iter-bind
  (AbsOps.Prefix₀ MsgBatchDone (AbsOps.Ret (inj₁ stIdle))) absStep

-- the only τ out of S-loop s lands on IT s (the iter loop-back sil).
S-loop-τ : ∀ {s W″} → (S-loop s AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (IT s AbsOps.∖ msgBF)
S-loop-τ {s} st with Hide-τ-elim msgBF (S-loop s) st
... | hτP P' (sSil refl) refl = refl
... | hτP P' (sTau () _) refl
... | hτH P' mem (sVis () _) refl

-- the only τ out of S-req lands on S-req2 (the hidden MsgRequestRange).
S-req-τ : ∀ {range W″} → (S-req range AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (S-req2 range AbsOps.∖ msgBF)
S-req-τ {range} st with Hide-τ-elim msgBF (S-req range) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} {a = a} refl breq) refl with a ≟ range
...   | yes refl with breq
...     | refl = refl
S-req-τ {range} st | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} {a = a} refl ()) refl | no _
S-req-τ {range} st | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
S-req-τ {range} st | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
S-req-τ {range} st | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
S-req-τ {range} st | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
S-req-τ {range} st | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
S-req-τ {range} st | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of S-blk lands on S-blk2 (the hidden MsgBlock).
S-blk-τ : ∀ {b W″} → (S-blk b AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (S-blk2 b AbsOps.∖ msgBF)
S-blk-τ {b} st with Hide-τ-elim msgBF (S-blk b) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgBlock} P' mem (sVis {at = (_ , MsgBlock)} {a = a} refl breq) refl with a ≟ b
...   | yes refl with breq
...     | refl = refl
S-blk-τ {b} st | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)} {a = a} refl ()) refl | no _
S-blk-τ {b} st | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
S-blk-τ {b} st | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
S-blk-τ {b} st | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
S-blk-τ {b} st | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
S-blk-τ {b} st | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
S-blk-τ {b} st | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of S-cdone lands on S-loop stDone (hidden MsgClientDone).
S-cdone-τ : ∀ {W″} → (S-cdone AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (S-loop stDone AbsOps.∖ msgBF)
S-cdone-τ st with Hide-τ-elim msgBF S-cdone st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl refl) refl = refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of S-sbatch lands on S-loop stStreaming (hidden MsgStartBatch).
S-sbatch-τ : ∀ {W″} → (S-sbatch AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (S-loop stStreaming AbsOps.∖ msgBF)
S-sbatch-τ st with Hide-τ-elim msgBF S-sbatch st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl refl) refl = refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of S-noblk lands on S-loop stIdle (hidden MsgNoBlocks).
S-noblk-τ : ∀ {W″} → (S-noblk AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (S-loop stIdle AbsOps.∖ msgBF)
S-noblk-τ st with Hide-τ-elim msgBF S-noblk st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl refl) refl = refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of S-bdone lands on S-loop stIdle (hidden MsgBatchDone).
S-bdone-τ : ∀ {W″} → (S-bdone AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (S-loop stIdle AbsOps.∖ msgBF)
S-bdone-τ st with Hide-τ-elim msgBF S-bdone st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl refl) refl = refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- S-req2 is stable: it offers only the reqBFRange api (∉ msgBF), empty τ-part.
S-req2-noτ : ∀ {range W″} → ¬ ((S-req2 range AbsOps.∖ msgBF) ─[ τ ]─► W″)
S-req2-noτ {range} st with Hide-τ-elim msgBF (S-req2 range) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = mem

-- S-blk2 is stable: it offers only the recvBFBlock api (∉ msgBF), empty τ-part.
S-blk2-noτ : ∀ {b W″} → ¬ ((S-blk2 b AbsOps.∖ msgBF) ─[ τ ]─► W″)
S-blk2-noτ {b} st with Hide-τ-elim msgBF (S-blk2 b) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = mem

------------------------------------------------------------------------
-- ¬ Diverges at each SPEC state (a finite, acyclic τ-DAG toward stable states).
------------------------------------------------------------------------

-- stable pchoice states never diverge (no τ at all).
spec-nd-IT : ∀ (s : BFState) → ¬ Diverges (IT s AbsOps.∖ msgBF)
spec-nd-IT s d = spec-noτ s (d .Diverges.step)

-- S-req2 / S-blk2 are stable.
spec-nd-req2 : ∀ {range} → ¬ Diverges (S-req2 range AbsOps.∖ msgBF)
spec-nd-req2 d = S-req2-noτ (d .Diverges.step)

spec-nd-blk2 : ∀ {b} → ¬ Diverges (S-blk2 b AbsOps.∖ msgBF)
spec-nd-blk2 d = S-blk2-noτ (d .Diverges.step)

-- transient states: a single τ leads to an already-converging state.
spec-nd-loop : ∀ (s : BFState) → ¬ Diverges (S-loop s AbsOps.∖ msgBF)
spec-nd-loop s d = spec-nd-IT s (subst Diverges (S-loop-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-req : ∀ {range} → ¬ Diverges (S-req range AbsOps.∖ msgBF)
spec-nd-req d = spec-nd-req2 (subst Diverges (S-req-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-blk : ∀ {b} → ¬ Diverges (S-blk b AbsOps.∖ msgBF)
spec-nd-blk d = spec-nd-blk2 (subst Diverges (S-blk-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-cdone : ¬ Diverges (S-cdone AbsOps.∖ msgBF)
spec-nd-cdone d = spec-nd-loop stDone (subst Diverges (S-cdone-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-sbatch : ¬ Diverges (S-sbatch AbsOps.∖ msgBF)
spec-nd-sbatch d = spec-nd-loop stStreaming (subst Diverges (S-sbatch-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-noblk : ¬ Diverges (S-noblk AbsOps.∖ msgBF)
spec-nd-noblk d = spec-nd-loop stIdle (subst Diverges (S-noblk-τ (d .Diverges.step)) (d .Diverges.rest))

spec-nd-bdone : ¬ Diverges (S-bdone AbsOps.∖ msgBF)
spec-nd-bdone d = spec-nd-loop stIdle (subst Diverges (S-bdone-τ (d .Diverges.step)) (d .Diverges.rest))

------------------------------------------------------------------------
-- The coinductive `Good` invariant at every reachable hidden SPEC state.
------------------------------------------------------------------------

-- deadlock is Good: it has no τ-, visible- or √-successor at all.
good-deadlock : Good deadlock
good-deadlock .gnd = deadlock-converges
good-deadlock .gτ (sSil ())
good-deadlock .gτ (sTau refl ())
good-deadlock .gev (sRet ())
good-deadlock .gev (sVis refl ())

-- forward declarations of the per-state invariants.
good-IT     : (s : BFState) → Good (IT s AbsOps.∖ msgBF)
good-req    : ∀ (range : ChainRange) → Good (S-req range AbsOps.∖ msgBF)
good-req2   : ∀ (range : ChainRange) → Good (S-req2 range AbsOps.∖ msgBF)
good-cdone  : Good (S-cdone AbsOps.∖ msgBF)
good-sbatch : Good (S-sbatch AbsOps.∖ msgBF)
good-noblk  : Good (S-noblk AbsOps.∖ msgBF)
good-blk    : ∀ (b : Block) → Good (S-blk b AbsOps.∖ msgBF)
good-blk2   : ∀ (b : Block) → Good (S-blk2 b AbsOps.∖ msgBF)
good-bdone  : Good (S-bdone AbsOps.∖ msgBF)
good-loop   : (s : BFState) → Good (S-loop s AbsOps.∖ msgBF)

-- IT stIdle: stable; offers sendBFRequestRange (→ S-req) and sendBFClientDone (→ S-cdone).
good-IT stIdle .gnd = spec-nd-IT stIdle
good-IT stIdle .gτ st = ⊥-elim (spec-noτ stIdle st)
good-IT stIdle .gev st with Hide-ev-elim msgBF (IT stIdle) st
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = r} refl refl) = good-req r
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl refl) = good-cdone
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()
-- IT stBusy: stable; offers sendBFStartBatch (→ S-sbatch) and sendBFNoBlocks (→ S-noblk).
good-IT stBusy .gnd = spec-nd-IT stBusy
good-IT stBusy .gτ st = ⊥-elim (spec-noτ stBusy st)
good-IT stBusy .gev st with Hide-ev-elim msgBF (IT stBusy) st
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = good-sbatch
... | heV {e = apiBF sendBFNoBlocks}   P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}   refl refl) = good-noblk
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()
-- IT stStreaming: stable; offers sendBFBlock (→ S-blk) and sendBFBatchDone (→ S-bdone).
good-IT stStreaming .gnd = spec-nd-IT stStreaming
good-IT stStreaming .gτ st = ⊥-elim (spec-noτ stStreaming st)
good-IT stStreaming .gev st with Hide-ev-elim msgBF (IT stStreaming) st
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = good-blk b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = good-bdone
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()
-- IT stDone: terminal √ to deadlock; no visible/τ steps.
good-IT stDone .gnd = spec-nd-IT stDone
good-IT stDone .gτ st = ⊥-elim (spec-noτ stDone st)
good-IT stDone .gev st with Hide-ev-elim msgBF (IT stDone) st
... | heV P' ¬m (sVis () _)
... | he√ refl = good-deadlock

-- S-req: one hidden τ (the MsgRequestRange) to S-req2; no surviving visible event.
good-req range .gnd = spec-nd-req
good-req range .gτ st with S-req-τ st
... | refl = good-req2 range
good-req range .gev st with Hide-ev-elim msgBF (S-req range) st
... | heV {e = MsgRequestRange}          P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- S-req2: stable; the reqBFRange api (value = range) survives to S-loop stBusy.
good-req2 range .gnd = spec-nd-req2
good-req2 range .gτ st = ⊥-elim (S-req2-noτ st)
good-req2 range .gev st with Hide-ev-elim msgBF (S-req2 range) st
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl breq) with a ≟ range
...   | yes refl with breq
...     | refl = good-loop stBusy
good-req2 range .gev st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
good-req2 range .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
good-req2 range .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
good-req2 range .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
good-req2 range .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
good-req2 range .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
good-req2 range .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
good-req2 range .gev st | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
good-req2 range .gev st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
good-req2 range .gev st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
good-req2 range .gev st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
good-req2 range .gev st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
good-req2 range .gev st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
good-req2 range .gev st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
good-req2 range .gev st | he√ ()

-- S-blk: one hidden τ (the MsgBlock) to S-blk2; no surviving visible event.
good-blk b .gnd = spec-nd-blk
good-blk b .gτ st with S-blk-τ st
... | refl = good-blk2 b
good-blk b .gev st with Hide-ev-elim msgBF (S-blk b) st
... | heV {e = MsgBlock}                 P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- S-blk2: stable; the recvBFBlock api (value = b) survives to S-loop stStreaming.
good-blk2 b .gnd = spec-nd-blk2
good-blk2 b .gτ st = ⊥-elim (S-blk2-noτ st)
good-blk2 b .gev st with Hide-ev-elim msgBF (S-blk2 b) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl breq) with a ≟ b
...   | yes refl with breq
...     | refl = good-loop stStreaming
good-blk2 b .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl ()) | no _
good-blk2 b .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
good-blk2 b .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
good-blk2 b .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
good-blk2 b .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
good-blk2 b .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
good-blk2 b .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
good-blk2 b .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
good-blk2 b .gev st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
good-blk2 b .gev st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
good-blk2 b .gev st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
good-blk2 b .gev st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
good-blk2 b .gev st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
good-blk2 b .gev st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
good-blk2 b .gev st | he√ ()

-- S-cdone: one hidden τ (MsgClientDone) to S-loop stDone; no surviving visible event.
good-cdone .gnd = spec-nd-cdone
good-cdone .gτ st with S-cdone-τ st
... | refl = good-loop stDone
good-cdone .gev st with Hide-ev-elim msgBF S-cdone st
... | heV {e = MsgClientDone}   P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- S-sbatch: one hidden τ (MsgStartBatch) to S-loop stStreaming; no surviving visible event.
good-sbatch .gnd = spec-nd-sbatch
good-sbatch .gτ st with S-sbatch-τ st
... | refl = good-loop stStreaming
good-sbatch .gev st with Hide-ev-elim msgBF S-sbatch st
... | heV {e = MsgStartBatch}   P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- S-noblk: one hidden τ (MsgNoBlocks) to S-loop stIdle; no surviving visible event.
good-noblk .gnd = spec-nd-noblk
good-noblk .gτ st with S-noblk-τ st
... | refl = good-loop stIdle
good-noblk .gev st with Hide-ev-elim msgBF S-noblk st
... | heV {e = MsgNoBlocks}     P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- S-bdone: one hidden τ (MsgBatchDone) to S-loop stIdle; no surviving visible event.
good-bdone .gnd = spec-nd-bdone
good-bdone .gτ st with S-bdone-τ st
... | refl = good-loop stIdle
good-bdone .gev st with Hide-ev-elim msgBF S-bdone st
... | heV {e = MsgBatchDone}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- S-loop s: a single iter loop-back τ to IT s; force is a `sil`, so no visible event.
good-loop s .gnd = spec-nd-loop s
good-loop s .gτ st with S-loop-τ st
... | refl = good-IT s
good-loop s .gev st with Hide-ev-elim msgBF (S-loop s) st
... | heV P' ¬m (sVis () _)
... | he√ ()

-- the SPEC's initial hidden state is `IT stIdle ∖ msgBF = BFabstract ∖ msgBF`.
good-spec-init : Good (BFabstract AbsOps.∖ msgBF)
good-spec-init = good-IT stIdle

-- no weakly-reachable state of the hidden SPEC diverges.
spec-noDiv : ∀ {s W} → (BFabstract AbsOps.∖ msgBF) ⟹⟨ s ⟩ W → ¬ Diverges W
spec-noDiv = go-reach good-spec-init

------------------------------------------------------------------------
-- PIPELINED SPEC: BFabstractP ∖ msgBF.  Same shape as the serial SPEC,
-- with the extra streaming states `pStr1 b`/`pStr2 b b′`/`pStrD b`.
------------------------------------------------------------------------

-- abbreviation: the PIPELINED iteration at a state.
ITP : BFSpecState → PTree BFAbsEv (ExtI BFAbsEv) Rr
ITP s = AbsOps.iter absStepP s

-- a pchoice / direct-api PIPELINED state has no hidden τ: its τ-part is empty
-- and every offered visible event is an apiBF (∉ msgBF), so no message hides.
specP-noτ : ∀ {W′} (s : BFSpecState) → ¬ ((ITP s AbsOps.∖ msgBF) ─[ τ ]─► W′)
specP-noτ s st with Hide-τ-elim msgBF (ITP s) st
specP-noτ pIdle _ | hτP P' (sSil ()) refl
specP-noτ pIdle _ | hτP P' (sTau refl ()) refl
specP-noτ pIdle _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
specP-noτ pIdle _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
specP-noτ pIdle _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
specP-noτ pIdle _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
specP-noτ pIdle _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
specP-noτ pIdle _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
specP-noτ pIdle _ | hτH {e = apiBF m}         P' mem stp refl = mem
specP-noτ pBusy _ | hτP P' (sSil ()) refl
specP-noτ pBusy _ | hτP P' (sTau refl ()) refl
specP-noτ pBusy _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
specP-noτ pBusy _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
specP-noτ pBusy _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
specP-noτ pBusy _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
specP-noτ pBusy _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
specP-noτ pBusy _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
specP-noτ pBusy _ | hτH {e = apiBF m}         P' mem stp refl = mem
specP-noτ pStr0 _ | hτP P' (sSil ()) refl
specP-noτ pStr0 _ | hτP P' (sTau refl ()) refl
specP-noτ pStr0 _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
specP-noτ pStr0 _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
specP-noτ pStr0 _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
specP-noτ pStr0 _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
specP-noτ pStr0 _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
specP-noτ pStr0 _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
specP-noτ pStr0 _ | hτH {e = apiBF m}         P' mem stp refl = mem
specP-noτ (pStr1 b) _ | hτP P' (sSil ()) refl
specP-noτ (pStr1 b) _ | hτP P' (sTau refl ()) refl
specP-noτ (pStr1 b) _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
specP-noτ (pStr1 b) _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
specP-noτ (pStr1 b) _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
specP-noτ (pStr1 b) _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
specP-noτ (pStr1 b) _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
specP-noτ (pStr1 b) _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
specP-noτ (pStr1 b) _ | hτH {e = apiBF m}         P' mem stp refl = mem
specP-noτ (pStr2 b b′) _ | hτP P' (sSil ()) refl
specP-noτ (pStr2 b b′) _ | hτP P' (sTau refl ()) refl
specP-noτ (pStr2 b b′) _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
specP-noτ (pStr2 b b′) _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
specP-noτ (pStr2 b b′) _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
specP-noτ (pStr2 b b′) _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
specP-noτ (pStr2 b b′) _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
specP-noτ (pStr2 b b′) _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
specP-noτ (pStr2 b b′) _ | hτH {e = apiBF m}         P' mem stp refl = mem
specP-noτ (pStrD b) _ | hτP P' (sSil ()) refl
specP-noτ (pStrD b) _ | hτP P' (sTau refl ()) refl
specP-noτ (pStrD b) _ | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
specP-noτ (pStrD b) _ | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
specP-noτ (pStrD b) _ | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
specP-noτ (pStrD b) _ | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
specP-noτ (pStrD b) _ | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
specP-noτ (pStrD b) _ | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
specP-noτ (pStrD b) _ | hτH {e = apiBF m}         P' mem stp refl = mem
specP-noτ pDone _ | hτP P' (sSil ()) refl
specP-noτ pDone _ | hτP P' (sTau () _) refl
specP-noτ pDone _ | hτH P' mem (sVis () _) refl

-- transient: just past the pIdle/request apiBF — Output Msg!range (a hidden τ).
P-req : ChainRange → PTree BFAbsEv (ExtI BFAbsEv) Rr
P-req range = AbsOps.iter-bind
  (AbsOps.Output MsgRequestRange range
     (AbsOps.Output (apiBF reqBFRange) range (AbsOps.Ret (inj₁ pBusy)))) absStepP

-- transient: pIdle/request, after the Msg hidden — offering the reqBFRange api.
P-req2 : ChainRange → PTree BFAbsEv (ExtI BFAbsEv) Rr
P-req2 range = AbsOps.iter-bind
  (AbsOps.Output (apiBF reqBFRange) range (AbsOps.Ret (inj₁ pBusy))) absStepP

-- transient: an iter loop-back point (ret (inj₁ s) ⇒ sil (ITP s)).
P-loop : BFSpecState → PTree BFAbsEv (ExtI BFAbsEv) Rr
P-loop s = AbsOps.iter-bind (AbsOps.Ret (inj₁ s)) absStepP

-- transient: pIdle/client-done, the MsgClientDone prefix (hidden τ).
P-cdone : PTree BFAbsEv (ExtI BFAbsEv) Rr
P-cdone = AbsOps.iter-bind
  (AbsOps.Prefix₀ MsgClientDone (AbsOps.Ret (inj₁ pDone))) absStepP

-- transient: pBusy/start-batch, the MsgStartBatch prefix (hidden τ).
P-sbatch : PTree BFAbsEv (ExtI BFAbsEv) Rr
P-sbatch = AbsOps.iter-bind
  (AbsOps.Prefix₀ MsgStartBatch (AbsOps.Ret (inj₁ pStr0))) absStepP

-- transient: pBusy/no-blocks, the MsgNoBlocks prefix (hidden τ).
P-noblk : PTree BFAbsEv (ExtI BFAbsEv) Rr
P-noblk = AbsOps.iter-bind
  (AbsOps.Prefix₀ MsgNoBlocks (AbsOps.Ret (inj₁ pIdle))) absStepP

-- transient: pStr0/block, the MsgBlock!b offer (hidden τ) → pStr1 b.
P-blk0 : Block → PTree BFAbsEv (ExtI BFAbsEv) Rr
P-blk0 b = AbsOps.iter-bind
  (AbsOps.Output MsgBlock b (AbsOps.Ret (inj₁ (pStr1 b)))) absStepP

-- transient: pStr0/batch-done (and pStrD-deliver tail), the MsgBatchDone prefix (hidden τ).
P-bdone : PTree BFAbsEv (ExtI BFAbsEv) Rr
P-bdone = AbsOps.iter-bind
  (AbsOps.Prefix₀ MsgBatchDone (AbsOps.Ret (inj₁ pIdle))) absStepP

-- transient: pStr1 b/send-block b′, the pipeline MsgBlock!b′ offer (hidden τ) → pStr2 b b′.
P-blkP : Block → Block → PTree BFAbsEv (ExtI BFAbsEv) Rr
P-blkP b b′ = AbsOps.iter-bind
  (AbsOps.Output MsgBlock b′ (AbsOps.Ret (inj₁ (pStr2 b b′)))) absStepP

-- transient: pStr2-deliver tail, the in-flight MsgBlock!b′ offer (hidden τ) → pStr1 b′.
P-blkD : Block → PTree BFAbsEv (ExtI BFAbsEv) Rr
P-blkD b′ = AbsOps.iter-bind
  (AbsOps.Output MsgBlock b′ (AbsOps.Ret (inj₁ (pStr1 b′)))) absStepP

-- the only τ out of P-loop s lands on ITP s (the iter loop-back sil).
P-loop-τ : ∀ {s W″} → (P-loop s AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (ITP s AbsOps.∖ msgBF)
P-loop-τ {s} st with Hide-τ-elim msgBF (P-loop s) st
... | hτP P' (sSil refl) refl = refl
... | hτP P' (sTau () _) refl
... | hτH P' mem (sVis () _) refl

-- the only τ out of P-req lands on P-req2 (the hidden MsgRequestRange).
P-req-τ : ∀ {range W″} → (P-req range AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (P-req2 range AbsOps.∖ msgBF)
P-req-τ {range} st with Hide-τ-elim msgBF (P-req range) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} {a = a} refl breq) refl with a ≟ range
...   | yes refl with breq
...     | refl = refl
P-req-τ {range} st | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} {a = a} refl ()) refl | no _
P-req-τ {range} st | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
P-req-τ {range} st | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
P-req-τ {range} st | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
P-req-τ {range} st | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
P-req-τ {range} st | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
P-req-τ {range} st | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of P-blk0 lands on P-loop (pStr1 b) (the hidden MsgBlock).
P-blk0-τ : ∀ {b W″} → (P-blk0 b AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (P-loop (pStr1 b) AbsOps.∖ msgBF)
P-blk0-τ {b} st with Hide-τ-elim msgBF (P-blk0 b) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgBlock} P' mem (sVis {at = (_ , MsgBlock)} {a = a} refl breq) refl with a ≟ b
...   | yes refl with breq
...     | refl = refl
P-blk0-τ {b} st | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)} {a = a} refl ()) refl | no _
P-blk0-τ {b} st | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
P-blk0-τ {b} st | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
P-blk0-τ {b} st | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
P-blk0-τ {b} st | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
P-blk0-τ {b} st | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
P-blk0-τ {b} st | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of P-blkP lands on P-loop (pStr2 b b′) (the hidden MsgBlock!b′).
P-blkP-τ : ∀ {b b′ W″} → (P-blkP b b′ AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (P-loop (pStr2 b b′) AbsOps.∖ msgBF)
P-blkP-τ {b} {b′} st with Hide-τ-elim msgBF (P-blkP b b′) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgBlock} P' mem (sVis {at = (_ , MsgBlock)} {a = a} refl breq) refl with a ≟ b′
...   | yes refl with breq
...     | refl = refl
P-blkP-τ {b} {b′} st | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)} {a = a} refl ()) refl | no _
P-blkP-τ {b} {b′} st | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
P-blkP-τ {b} {b′} st | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
P-blkP-τ {b} {b′} st | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
P-blkP-τ {b} {b′} st | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
P-blkP-τ {b} {b′} st | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
P-blkP-τ {b} {b′} st | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of P-blkD lands on P-loop (pStr1 b′) (the hidden MsgBlock!b′).
P-blkD-τ : ∀ {b′ W″} → (P-blkD b′ AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (P-loop (pStr1 b′) AbsOps.∖ msgBF)
P-blkD-τ {b′} st with Hide-τ-elim msgBF (P-blkD b′) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgBlock} P' mem (sVis {at = (_ , MsgBlock)} {a = a} refl breq) refl with a ≟ b′
...   | yes refl with breq
...     | refl = refl
P-blkD-τ {b′} st | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)} {a = a} refl ()) refl | no _
P-blkD-τ {b′} st | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
P-blkD-τ {b′} st | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
P-blkD-τ {b′} st | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
P-blkD-τ {b′} st | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
P-blkD-τ {b′} st | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
P-blkD-τ {b′} st | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of P-cdone lands on P-loop pDone (hidden MsgClientDone).
P-cdone-τ : ∀ {W″} → (P-cdone AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (P-loop pDone AbsOps.∖ msgBF)
P-cdone-τ st with Hide-τ-elim msgBF P-cdone st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl refl) refl = refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of P-sbatch lands on P-loop pStr0 (hidden MsgStartBatch).
P-sbatch-τ : ∀ {W″} → (P-sbatch AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (P-loop pStr0 AbsOps.∖ msgBF)
P-sbatch-τ st with Hide-τ-elim msgBF P-sbatch st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl refl) refl = refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of P-noblk lands on P-loop pIdle (hidden MsgNoBlocks).
P-noblk-τ : ∀ {W″} → (P-noblk AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (P-loop pIdle AbsOps.∖ msgBF)
P-noblk-τ st with Hide-τ-elim msgBF P-noblk st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl refl) refl = refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- the only τ out of P-bdone lands on P-loop pIdle (hidden MsgBatchDone).
P-bdone-τ : ∀ {W″} → (P-bdone AbsOps.∖ msgBF) ─[ τ ]─► W″ → W″ ≡ (P-loop pIdle AbsOps.∖ msgBF)
P-bdone-τ st with Hide-τ-elim msgBF P-bdone st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl refl) refl = refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = ⊥-elim mem

-- P-req2 is stable: it offers only the reqBFRange api (∉ msgBF), empty τ-part.
P-req2-noτ : ∀ {range W″} → ¬ ((P-req2 range AbsOps.∖ msgBF) ─[ τ ]─► W″)
P-req2-noτ {range} st with Hide-τ-elim msgBF (P-req2 range) st
... | hτP P' (sSil ()) refl
... | hτP P' (sTau refl ()) refl
... | hτH {e = MsgRequestRange} P' mem (sVis {at = (_ , MsgRequestRange)} refl ()) refl
... | hτH {e = MsgStartBatch}   P' mem (sVis {at = (_ , MsgStartBatch)}   refl ()) refl
... | hτH {e = MsgNoBlocks}     P' mem (sVis {at = (_ , MsgNoBlocks)}     refl ()) refl
... | hτH {e = MsgBlock}        P' mem (sVis {at = (_ , MsgBlock)}        refl ()) refl
... | hτH {e = MsgBatchDone}    P' mem (sVis {at = (_ , MsgBatchDone)}    refl ()) refl
... | hτH {e = MsgClientDone}   P' mem (sVis {at = (_ , MsgClientDone)}   refl ()) refl
... | hτH {e = apiBF m}         P' mem stp refl = mem

------------------------------------------------------------------------
-- ¬ Diverges at each PIPELINED-SPEC state (a finite, acyclic τ-DAG).
------------------------------------------------------------------------

-- stable states never diverge (no τ at all).
specP-nd-IT : ∀ (s : BFSpecState) → ¬ Diverges (ITP s AbsOps.∖ msgBF)
specP-nd-IT s d = specP-noτ s (d .Diverges.step)

-- P-req2 is stable.
specP-nd-req2 : ∀ {range} → ¬ Diverges (P-req2 range AbsOps.∖ msgBF)
specP-nd-req2 d = P-req2-noτ (d .Diverges.step)

-- transient states: a single τ leads to an already-converging state.
specP-nd-loop : ∀ (s : BFSpecState) → ¬ Diverges (P-loop s AbsOps.∖ msgBF)
specP-nd-loop s d = specP-nd-IT s (subst Diverges (P-loop-τ (d .Diverges.step)) (d .Diverges.rest))

specP-nd-req : ∀ {range} → ¬ Diverges (P-req range AbsOps.∖ msgBF)
specP-nd-req d = specP-nd-req2 (subst Diverges (P-req-τ (d .Diverges.step)) (d .Diverges.rest))

specP-nd-blk0 : ∀ {b} → ¬ Diverges (P-blk0 b AbsOps.∖ msgBF)
specP-nd-blk0 {b} d = specP-nd-loop (pStr1 b) (subst Diverges (P-blk0-τ (d .Diverges.step)) (d .Diverges.rest))

specP-nd-blkP : ∀ {b b′} → ¬ Diverges (P-blkP b b′ AbsOps.∖ msgBF)
specP-nd-blkP {b} {b′} d = specP-nd-loop (pStr2 b b′) (subst Diverges (P-blkP-τ (d .Diverges.step)) (d .Diverges.rest))

specP-nd-blkD : ∀ {b′} → ¬ Diverges (P-blkD b′ AbsOps.∖ msgBF)
specP-nd-blkD {b′} d = specP-nd-loop (pStr1 b′) (subst Diverges (P-blkD-τ (d .Diverges.step)) (d .Diverges.rest))

specP-nd-cdone : ¬ Diverges (P-cdone AbsOps.∖ msgBF)
specP-nd-cdone d = specP-nd-loop pDone (subst Diverges (P-cdone-τ (d .Diverges.step)) (d .Diverges.rest))

specP-nd-sbatch : ¬ Diverges (P-sbatch AbsOps.∖ msgBF)
specP-nd-sbatch d = specP-nd-loop pStr0 (subst Diverges (P-sbatch-τ (d .Diverges.step)) (d .Diverges.rest))

specP-nd-noblk : ¬ Diverges (P-noblk AbsOps.∖ msgBF)
specP-nd-noblk d = specP-nd-loop pIdle (subst Diverges (P-noblk-τ (d .Diverges.step)) (d .Diverges.rest))

specP-nd-bdone : ¬ Diverges (P-bdone AbsOps.∖ msgBF)
specP-nd-bdone d = specP-nd-loop pIdle (subst Diverges (P-bdone-τ (d .Diverges.step)) (d .Diverges.rest))

------------------------------------------------------------------------
-- The coinductive `Good` invariant at every reachable PIPELINED-SPEC state.
------------------------------------------------------------------------

-- forward declarations of the per-state invariants.
goodP-IT     : (s : BFSpecState) → Good (ITP s AbsOps.∖ msgBF)
goodP-req    : ∀ (range : ChainRange) → Good (P-req range AbsOps.∖ msgBF)
goodP-req2   : ∀ (range : ChainRange) → Good (P-req2 range AbsOps.∖ msgBF)
goodP-cdone  : Good (P-cdone AbsOps.∖ msgBF)
goodP-sbatch : Good (P-sbatch AbsOps.∖ msgBF)
goodP-noblk  : Good (P-noblk AbsOps.∖ msgBF)
goodP-blk0   : ∀ (b : Block) → Good (P-blk0 b AbsOps.∖ msgBF)
goodP-blkP   : ∀ (b b′ : Block) → Good (P-blkP b b′ AbsOps.∖ msgBF)
goodP-blkD   : ∀ (b′ : Block) → Good (P-blkD b′ AbsOps.∖ msgBF)
goodP-bdone  : Good (P-bdone AbsOps.∖ msgBF)
goodP-loop   : (s : BFSpecState) → Good (P-loop s AbsOps.∖ msgBF)

-- ITP pIdle: stable; offers sendBFRequestRange (→ P-req) and sendBFClientDone (→ P-cdone).
goodP-IT pIdle .gnd = specP-nd-IT pIdle
goodP-IT pIdle .gτ st = ⊥-elim (specP-noτ pIdle st)
goodP-IT pIdle .gev st with Hide-ev-elim msgBF (ITP pIdle) st
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = r} refl refl) = goodP-req r
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl refl) = goodP-cdone
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()
-- ITP pBusy: stable; offers sendBFStartBatch (→ P-sbatch) and sendBFNoBlocks (→ P-noblk).
goodP-IT pBusy .gnd = specP-nd-IT pBusy
goodP-IT pBusy .gτ st = ⊥-elim (specP-noτ pBusy st)
goodP-IT pBusy .gev st with Hide-ev-elim msgBF (ITP pBusy) st
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = goodP-sbatch
... | heV {e = apiBF sendBFNoBlocks}   P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}   refl refl) = goodP-noblk
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()
-- ITP pStr0: stable; offers sendBFBlock (→ P-blk0) and sendBFBatchDone (→ P-bdone).
goodP-IT pStr0 .gnd = specP-nd-IT pStr0
goodP-IT pStr0 .gτ st = ⊥-elim (specP-noτ pStr0 st)
goodP-IT pStr0 .gev st with Hide-ev-elim msgBF (ITP pStr0) st
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = goodP-blk0 b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = goodP-bdone
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()
-- ITP (pStr1 b): stable, mixed menu; recvBFBlock!b (→ P-loop pStr0), sendBFBlock b′ (→ P-blkP),
-- sendBFBatchDone (→ P-loop (pStrD b)).
goodP-IT (pStr1 b) .gnd = specP-nd-IT (pStr1 b)
goodP-IT (pStr1 b) .gτ st = ⊥-elim (specP-noτ (pStr1 b) st)
goodP-IT (pStr1 b) .gev st with Hide-ev-elim msgBF (ITP (pStr1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = goodP-loop pStr0
goodP-IT (pStr1 b) .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
goodP-IT (pStr1 b) .gev st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b′} refl refl) = goodP-blkP b b′
goodP-IT (pStr1 b) .gev st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = goodP-loop (pStrD b)
goodP-IT (pStr1 b) .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
goodP-IT (pStr1 b) .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
goodP-IT (pStr1 b) .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
goodP-IT (pStr1 b) .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
goodP-IT (pStr1 b) .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
goodP-IT (pStr1 b) .gev st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
goodP-IT (pStr1 b) .gev st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
goodP-IT (pStr1 b) .gev st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
goodP-IT (pStr1 b) .gev st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
goodP-IT (pStr1 b) .gev st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
goodP-IT (pStr1 b) .gev st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
goodP-IT (pStr1 b) .gev st | he√ ()
-- ITP (pStr2 b b′): stable; the recvBFBlock!b api survives to P-blkD b′ (deliver head, then absorb in-flight).
goodP-IT (pStr2 b b′) .gnd = specP-nd-IT (pStr2 b b′)
goodP-IT (pStr2 b b′) .gτ st = ⊥-elim (specP-noτ (pStr2 b b′) st)
goodP-IT (pStr2 b b′) .gev st with Hide-ev-elim msgBF (ITP (pStr2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl breq) with a ≟ b
...   | yes refl with breq
...     | refl = goodP-blkD b′
goodP-IT (pStr2 b b′) .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl ()) | no _
goodP-IT (pStr2 b b′) .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
goodP-IT (pStr2 b b′) .gev st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
goodP-IT (pStr2 b b′) .gev st | he√ ()
-- ITP (pStrD b): stable; the recvBFBlock!b api survives to P-bdone (deliver head, then absorb batch-done).
goodP-IT (pStrD b) .gnd = specP-nd-IT (pStrD b)
goodP-IT (pStrD b) .gτ st = ⊥-elim (specP-noτ (pStrD b) st)
goodP-IT (pStrD b) .gev st with Hide-ev-elim msgBF (ITP (pStrD b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl breq) with a ≟ b
...   | yes refl with breq
...     | refl = goodP-bdone
goodP-IT (pStrD b) .gev st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl ()) | no _
goodP-IT (pStrD b) .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
goodP-IT (pStrD b) .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
goodP-IT (pStrD b) .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
goodP-IT (pStrD b) .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
goodP-IT (pStrD b) .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
goodP-IT (pStrD b) .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
goodP-IT (pStrD b) .gev st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
goodP-IT (pStrD b) .gev st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
goodP-IT (pStrD b) .gev st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
goodP-IT (pStrD b) .gev st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
goodP-IT (pStrD b) .gev st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
goodP-IT (pStrD b) .gev st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
goodP-IT (pStrD b) .gev st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
goodP-IT (pStrD b) .gev st | he√ ()
-- ITP pDone: terminal √ to deadlock; no visible/τ steps.
goodP-IT pDone .gnd = specP-nd-IT pDone
goodP-IT pDone .gτ st = ⊥-elim (specP-noτ pDone st)
goodP-IT pDone .gev st with Hide-ev-elim msgBF (ITP pDone) st
... | heV P' ¬m (sVis () _)
... | he√ refl = good-deadlock

-- P-req: one hidden τ (the MsgRequestRange) to P-req2; no surviving visible event.
goodP-req range .gnd = specP-nd-req
goodP-req range .gτ st with P-req-τ st
... | refl = goodP-req2 range
goodP-req range .gev st with Hide-ev-elim msgBF (P-req range) st
... | heV {e = MsgRequestRange}          P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- P-req2: stable; the reqBFRange api (value = range) survives to P-loop pBusy.
goodP-req2 range .gnd = specP-nd-req2
goodP-req2 range .gτ st = ⊥-elim (P-req2-noτ st)
goodP-req2 range .gev st with Hide-ev-elim msgBF (P-req2 range) st
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl breq) with a ≟ range
...   | yes refl with breq
...     | refl = goodP-loop pBusy
goodP-req2 range .gev st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
goodP-req2 range .gev st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
goodP-req2 range .gev st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
goodP-req2 range .gev st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
goodP-req2 range .gev st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
goodP-req2 range .gev st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
goodP-req2 range .gev st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
goodP-req2 range .gev st | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
goodP-req2 range .gev st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
goodP-req2 range .gev st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
goodP-req2 range .gev st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
goodP-req2 range .gev st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
goodP-req2 range .gev st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
goodP-req2 range .gev st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
goodP-req2 range .gev st | he√ ()

-- P-blk0: one hidden τ (the MsgBlock) to P-loop (pStr1 b); no surviving visible event.
goodP-blk0 b .gnd = specP-nd-blk0
goodP-blk0 b .gτ st with P-blk0-τ st
... | refl = goodP-loop (pStr1 b)
goodP-blk0 b .gev st with Hide-ev-elim msgBF (P-blk0 b) st
... | heV {e = MsgBlock}                 P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- P-blkP: one hidden τ (the pipeline MsgBlock!b′) to P-loop (pStr2 b b′); no surviving visible event.
goodP-blkP b b′ .gnd = specP-nd-blkP
goodP-blkP b b′ .gτ st with P-blkP-τ st
... | refl = goodP-loop (pStr2 b b′)
goodP-blkP b b′ .gev st with Hide-ev-elim msgBF (P-blkP b b′) st
... | heV {e = MsgBlock}                 P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- P-blkD: one hidden τ (the in-flight MsgBlock!b′) to P-loop (pStr1 b′); no surviving visible event.
goodP-blkD b′ .gnd = specP-nd-blkD
goodP-blkD b′ .gτ st with P-blkD-τ st
... | refl = goodP-loop (pStr1 b′)
goodP-blkD b′ .gev st with Hide-ev-elim msgBF (P-blkD b′) st
... | heV {e = MsgBlock}                 P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- P-cdone: one hidden τ (MsgClientDone) to P-loop pDone; no surviving visible event.
goodP-cdone .gnd = specP-nd-cdone
goodP-cdone .gτ st with P-cdone-τ st
... | refl = goodP-loop pDone
goodP-cdone .gev st with Hide-ev-elim msgBF P-cdone st
... | heV {e = MsgClientDone}   P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- P-sbatch: one hidden τ (MsgStartBatch) to P-loop pStr0; no surviving visible event.
goodP-sbatch .gnd = specP-nd-sbatch
goodP-sbatch .gτ st with P-sbatch-τ st
... | refl = goodP-loop pStr0
goodP-sbatch .gev st with Hide-ev-elim msgBF P-sbatch st
... | heV {e = MsgStartBatch}   P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- P-noblk: one hidden τ (MsgNoBlocks) to P-loop pIdle; no surviving visible event.
goodP-noblk .gnd = specP-nd-noblk
goodP-noblk .gτ st with P-noblk-τ st
... | refl = goodP-loop pIdle
goodP-noblk .gev st with Hide-ev-elim msgBF P-noblk st
... | heV {e = MsgNoBlocks}     P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- P-bdone: one hidden τ (MsgBatchDone) to P-loop pIdle; no surviving visible event.
goodP-bdone .gnd = specP-nd-bdone
goodP-bdone .gτ st with P-bdone-τ st
... | refl = goodP-loop pIdle
goodP-bdone .gev st with Hide-ev-elim msgBF P-bdone st
... | heV {e = MsgBatchDone}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

-- P-loop s: a single iter loop-back τ to ITP s; force is a `sil`, so no visible event.
goodP-loop s .gnd = specP-nd-loop s
goodP-loop s .gτ st with P-loop-τ st
... | refl = goodP-IT s
goodP-loop s .gev st with Hide-ev-elim msgBF (P-loop s) st
... | heV P' ¬m (sVis () _)
... | he√ ()

-- the PIPELINED SPEC's initial hidden state is `ITP pIdle ∖ msgBF = BFabstractP ∖ msgBF`.
goodP-spec-init : Good (BFabstractP AbsOps.∖ msgBF)
goodP-spec-init = goodP-IT pIdle

-- no weakly-reachable state of the hidden PIPELINED SPEC diverges.
specP-noDiv : ∀ {s W} → (BFabstractP AbsOps.∖ msgBF) ⟹⟨ s ⟩ W → ¬ Diverges W
specP-noDiv = go-reach goodP-spec-init

------------------------------------------------------------------------
-- IMPL: clientServerBF ∖ msgBF.  Joint states `Par msgBF merge cP sP`.
------------------------------------------------------------------------

-- the constant merge used by Par⊤.
mrg : Rr → Rr → Rr
mrg _ _ = Poly.tt

-- a joint hidden state.
JP : PTree BFAbsEv (ExtI BFAbsEv) Rr → PTree BFAbsEv (ExtI BFAbsEv) Rr
   → PTree BFAbsEv (ExtI BFAbsEv) Rr
JP cP sP = AbsOps.Par msgBF mrg cP sP AbsOps.∖ msgBF

-- client iteration at a state.
IC : BFState → PTree BFAbsEv (ExtI BFAbsEv) Rr
IC s = AbsOps.iter clientAbsStep s

-- server iteration at a state.
IS : BFState → PTree BFAbsEv (ExtI BFAbsEv) Rr
IS s = AbsOps.iter serverAbsStep s

-- client mid-message continuations.
CB-req : ChainRange → PTree BFAbsEv (ExtI BFAbsEv) Rr
CB-req range = AbsOps.iter-bind (AbsOps.Output MsgRequestRange range (AbsOps.Ret (inj₁ stBusy))) clientAbsStep

CB-cdone : PTree BFAbsEv (ExtI BFAbsEv) Rr
CB-cdone = AbsOps.iter-bind (AbsOps.Prefix₀ MsgClientDone (AbsOps.Ret (inj₁ stDone))) clientAbsStep

CB-blk : Block → PTree BFAbsEv (ExtI BFAbsEv) Rr
CB-blk b = AbsOps.iter-bind (AbsOps.Output (apiBF recvBFBlock) b (AbsOps.Ret (inj₁ stStreaming))) clientAbsStep

CB-loop : BFState → PTree BFAbsEv (ExtI BFAbsEv) Rr
CB-loop s = AbsOps.iter-bind (AbsOps.Ret (inj₁ s)) clientAbsStep

-- server mid-message continuations.
SB-req : ChainRange → PTree BFAbsEv (ExtI BFAbsEv) Rr
SB-req range = AbsOps.iter-bind (AbsOps.Output (apiBF reqBFRange) range (AbsOps.Ret (inj₁ stBusy))) serverAbsStep

SB-sbatch : PTree BFAbsEv (ExtI BFAbsEv) Rr
SB-sbatch = AbsOps.iter-bind (AbsOps.Prefix₀ MsgStartBatch (AbsOps.Ret (inj₁ stStreaming))) serverAbsStep

SB-noblk : PTree BFAbsEv (ExtI BFAbsEv) Rr
SB-noblk = AbsOps.iter-bind (AbsOps.Prefix₀ MsgNoBlocks (AbsOps.Ret (inj₁ stIdle))) serverAbsStep

SB-blk : Block → PTree BFAbsEv (ExtI BFAbsEv) Rr
SB-blk b = AbsOps.iter-bind (AbsOps.Output MsgBlock b (AbsOps.Ret (inj₁ stStreaming))) serverAbsStep

SB-bdone : PTree BFAbsEv (ExtI BFAbsEv) Rr
SB-bdone = AbsOps.iter-bind (AbsOps.Prefix₀ MsgBatchDone (AbsOps.Ret (inj₁ stIdle))) serverAbsStep

SB-loop : BFState → PTree BFAbsEv (ExtI BFAbsEv) Rr
SB-loop s = AbsOps.iter-bind (AbsOps.Ret (inj₁ s)) serverAbsStep

-- B=(CB-req r, IS stIdle): the only τ is the MsgRequestRange sync → (CB-loop stBusy, SB-req r).
B-τ : ∀ {r W″} → (JP (CB-req r) (IS stIdle)) ─[ τ ]─► W″ → W″ ≡ JP (CB-loop stBusy) (SB-req r)
B-τ {r} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-req r) (IS stIdle)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-req r) (IS stIdle) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
B-τ {r} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-req r) (IS stIdle) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} {a = a} refl cbreq) (sVis {at = (_ , MsgRequestRange)} refl sbreq) with a ≟ r
...     | yes refl with cbreq | sbreq
...       | refl | refl = refl
B-τ {r} st | hτH P' mem pev refl | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} {a = a} refl ()) (sVis {at = (_ , MsgRequestRange)} refl sbreq) | no _
B-τ {r} st | hτH P' mem pev refl | evSync {e = MsgStartBatch}  m (sVis {at = (_ , MsgStartBatch)}  refl ()) sstp
B-τ {r} st | hτH P' mem pev refl | evSync {e = MsgNoBlocks}    m (sVis {at = (_ , MsgNoBlocks)}    refl ()) sstp
B-τ {r} st | hτH P' mem pev refl | evSync {e = MsgBlock}       m (sVis {at = (_ , MsgBlock)}       refl ()) sstp
B-τ {r} st | hτH P' mem pev refl | evSync {e = MsgBatchDone}   m (sVis {at = (_ , MsgBatchDone)}   refl ()) sstp
B-τ {r} st | hτH P' mem pev refl | evSync {e = MsgClientDone}  m (sVis {at = (_ , MsgClientDone)}  refl ()) sstp
B-τ {r} st | hτH P' mem pev refl | evSync {e = apiBF mm}       m cstp sstp = ⊥-elim m

-- D=(CB-loop stBusy, SB-req r): the only τ is the client loop-back → (IC stBusy, SB-req r).
D-τ : ∀ {r W″} → (JP (CB-loop stBusy) (SB-req r)) ─[ τ ]─► W″ → W″ ≡ JP (IC stBusy) (SB-req r)
D-τ {r} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-req r)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stBusy) (SB-req r) pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
D-τ {r} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-req r) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch}   m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis () _) sstp
...   | evSync {e = MsgBlock}        m (sVis () _) sstp
...   | evSync {e = MsgBatchDone}    m (sVis () _) sstp
...   | evSync {e = MsgClientDone}   m (sVis () _) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- F=(IC stBusy, SB-req r): stable; client awaits a Msg, server offers reqBFRange api (solo).
F-noτ : ∀ {r W″} → ¬ ((JP (IC stBusy) (SB-req r)) ─[ τ ]─► W″)
F-noτ {r} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-req r)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stBusy) (SB-req r) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
F-noτ {r} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stBusy) (SB-req r) pev
...   | evL ¬m cstp = ¬m mem
...   | evR ¬m sstp = ¬m mem
...   | evBoth ¬m cstp sstp = ¬m mem
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m cstp (sVis {at = (_ , MsgStartBatch)}   refl ())
...   | evSync {e = MsgNoBlocks}     m cstp (sVis {at = (_ , MsgNoBlocks)}     refl ())
...   | evSync {e = MsgBlock}        m cstp (sVis {at = (_ , MsgBlock)}        refl ())
...   | evSync {e = MsgBatchDone}    m cstp (sVis {at = (_ , MsgBatchDone)}    refl ())
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)} refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = m

-- J=(IC stBusy, IS stBusy): stable; client awaits Msg, server offers sbatch/noblk apis (solo).
J-noτ : ∀ {W″} → ¬ ((JP (IC stBusy) (IS stBusy)) ─[ τ ]─► W″)
J-noτ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (IS stBusy)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stBusy) (IS stBusy) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
J-noτ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stBusy) (IS stBusy) pev
...   | evL ¬m cstp = ¬m mem
...   | evR ¬m sstp = ¬m mem
...   | evBoth ¬m cstp sstp = ¬m mem
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m cstp (sVis {at = (_ , MsgStartBatch)}   refl ())
...   | evSync {e = MsgNoBlocks}     m cstp (sVis {at = (_ , MsgNoBlocks)}     refl ())
...   | evSync {e = MsgBlock}        m cstp (sVis {at = (_ , MsgBlock)}        refl ())
...   | evSync {e = MsgBatchDone}    m cstp (sVis {at = (_ , MsgBatchDone)}    refl ())
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)} refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = m

-- V=(IC stStreaming, IS stStreaming): stable; client awaits Msg, server offers block/bdone apis.
V-noτ : ∀ {W″} → ¬ ((JP (IC stStreaming) (IS stStreaming)) ─[ τ ]─► W″)
V-noτ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (IS stStreaming)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stStreaming) (IS stStreaming) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
V-noτ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stStreaming) (IS stStreaming) pev
...   | evL ¬m cstp = ¬m mem
...   | evR ¬m sstp = ¬m mem
...   | evBoth ¬m cstp sstp = ¬m mem
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)}   refl ()) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)}     refl ()) sstp
...   | evSync {e = MsgBlock}        m cstp (sVis {at = (_ , MsgBlock)}        refl ())
...   | evSync {e = MsgBatchDone}    m cstp (sVis {at = (_ , MsgBatchDone)}    refl ())
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)} refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = m

-- C=(CB-cdone, IS stIdle): the only τ is the MsgClientDone sync → (CB-loop stDone, SB-loop stDone).
C-τ : ∀ {W″} → (JP CB-cdone (IS stIdle)) ─[ τ ]─► W″ → W″ ≡ JP (CB-loop stDone) (SB-loop stDone)
C-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg CB-cdone (IS stIdle)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg CB-cdone (IS stIdle) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
C-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg CB-cdone (IS stIdle) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)} refl refl) (sVis {at = (_ , MsgClientDone)} refl refl) = refl
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)}   refl ()) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)}     refl ()) sstp
...   | evSync {e = MsgBlock}        m (sVis {at = (_ , MsgBlock)}        refl ()) sstp
...   | evSync {e = MsgBatchDone}    m (sVis {at = (_ , MsgBatchDone)}    refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- M=(IC stBusy, SB-sbatch): the only τ is the MsgStartBatch sync → (CB-loop stStreaming, SB-loop stStreaming).
M-τ : ∀ {W″} → (JP (IC stBusy) SB-sbatch) ─[ τ ]─► W″ → W″ ≡ JP (CB-loop stStreaming) (SB-loop stStreaming)
M-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) SB-sbatch) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stBusy) SB-sbatch pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
M-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stBusy) SB-sbatch pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)} refl refl) (sVis {at = (_ , MsgStartBatch)} refl refl) = refl
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgNoBlocks}     m cstp (sVis {at = (_ , MsgNoBlocks)} refl ())
...   | evSync {e = MsgBlock}        m (sVis {at = (_ , MsgBlock)}        refl ()) sstp
...   | evSync {e = MsgBatchDone}    m (sVis {at = (_ , MsgBatchDone)}    refl ()) sstp
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)}   refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- N=(IC stBusy, SB-noblk): the only τ is the MsgNoBlocks sync → (CB-loop stIdle, SB-loop stIdle).
N-τ : ∀ {W″} → (JP (IC stBusy) SB-noblk) ─[ τ ]─► W″ → W″ ≡ JP (CB-loop stIdle) (SB-loop stIdle)
N-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) SB-noblk) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stBusy) SB-noblk pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
N-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stBusy) SB-noblk pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)} refl refl) (sVis {at = (_ , MsgNoBlocks)} refl refl) = refl
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m cstp (sVis {at = (_ , MsgStartBatch)} refl ())
...   | evSync {e = MsgBlock}        m (sVis {at = (_ , MsgBlock)}        refl ()) sstp
...   | evSync {e = MsgBatchDone}    m (sVis {at = (_ , MsgBatchDone)}    refl ()) sstp
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)}   refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- W=(IC stStreaming, SB-blk b): the only τ is the MsgBlock\!b sync → (CB-blk b, SB-loop stStreaming).
W-τ : ∀ {b W″} → (JP (IC stStreaming) (SB-blk b)) ─[ τ ]─► W″ → W″ ≡ JP (CB-blk b) (SB-loop stStreaming)
W-τ {b} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-blk b)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stStreaming) (SB-blk b) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
W-τ {b} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stStreaming) (SB-blk b) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgBlock} m (sVis {at = (_ , MsgBlock)} refl cbreq) (sVis {at = (_ , MsgBlock)} {a = a} refl sbreq) with a ≟ b
...     | yes refl with cbreq | sbreq
...       | refl | refl = refl
W-τ {b} st | hτH P' mem pev refl | evSync {e = MsgBlock} m (sVis {at = (_ , MsgBlock)} refl cbreq) (sVis {at = (_ , MsgBlock)} {a = a} refl ()) | no _
W-τ {b} st | hτH P' mem pev refl | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
W-τ {b} st | hτH P' mem pev refl | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)}   refl ()) sstp
W-τ {b} st | hτH P' mem pev refl | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)}     refl ()) sstp
W-τ {b} st | hτH P' mem pev refl | evSync {e = MsgBatchDone}    m cstp (sVis {at = (_ , MsgBatchDone)} refl ())
W-τ {b} st | hτH P' mem pev refl | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)}   refl ()) sstp
W-τ {b} st | hτH P' mem pev refl | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- Y=(IC stStreaming, SB-bdone): the only τ is the MsgBatchDone sync → (CB-loop stIdle, SB-loop stIdle).
Y-τ : ∀ {W″} → (JP (IC stStreaming) SB-bdone) ─[ τ ]─► W″ → W″ ≡ JP (CB-loop stIdle) (SB-loop stIdle)
Y-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) SB-bdone) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stStreaming) SB-bdone pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
Y-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stStreaming) SB-bdone pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgBatchDone}    m (sVis {at = (_ , MsgBatchDone)} refl refl) (sVis {at = (_ , MsgBatchDone)} refl refl) = refl
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)}   refl ()) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)}     refl ()) sstp
...   | evSync {e = MsgBlock}        m cstp (sVis {at = (_ , MsgBlock)} refl ())
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)}   refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- H=(IC stBusy, SB-loop stBusy): the only τ is the server loop-back → (IC stBusy, IS stBusy).
H-τ : ∀ {W″} → (JP (IC stBusy) (SB-loop stBusy)) ─[ τ ]─► W″ → W″ ≡ JP (IC stBusy) (IS stBusy)
H-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-loop stBusy)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stBusy) (SB-loop stBusy) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil refl) refl = refl
...   | τR Q'' (sTau () _) refl
H-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stBusy) (SB-loop stBusy) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m cstp (sVis () _)
...   | evSync {e = MsgStartBatch} m cstp (sVis () _)
...   | evSync {e = MsgNoBlocks} m cstp (sVis () _)
...   | evSync {e = MsgBlock} m cstp (sVis () _)
...   | evSync {e = MsgBatchDone} m cstp (sVis () _)
...   | evSync {e = MsgClientDone} m cstp (sVis () _)
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- R=(IC stStreaming, SB-loop stStreaming): server loop-back → (IC stStreaming, IS stStreaming).
R-τ : ∀ {W″} → (JP (IC stStreaming) (SB-loop stStreaming)) ─[ τ ]─► W″ → W″ ≡ JP (IC stStreaming) (IS stStreaming)
R-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-loop stStreaming)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stStreaming) (SB-loop stStreaming) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil refl) refl = refl
...   | τR Q'' (sTau () _) refl
R-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stStreaming) (SB-loop stStreaming) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m cstp (sVis () _)
...   | evSync {e = MsgStartBatch} m cstp (sVis () _)
...   | evSync {e = MsgNoBlocks} m cstp (sVis () _)
...   | evSync {e = MsgBlock} m cstp (sVis () _)
...   | evSync {e = MsgBatchDone} m cstp (sVis () _)
...   | evSync {e = MsgClientDone} m cstp (sVis () _)
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- T=(IC stIdle, SB-loop stIdle): server loop-back → (IC stIdle, IS stIdle).
T-τ : ∀ {W″} → (JP (IC stIdle) (SB-loop stIdle)) ─[ τ ]─► W″ → W″ ≡ JP (IC stIdle) (IS stIdle)
T-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stIdle) (SB-loop stIdle)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stIdle) (SB-loop stIdle) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil refl) refl = refl
...   | τR Q'' (sTau () _) refl
T-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stIdle) (SB-loop stIdle) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m cstp (sVis () _)
...   | evSync {e = MsgStartBatch} m cstp (sVis () _)
...   | evSync {e = MsgNoBlocks} m cstp (sVis () _)
...   | evSync {e = MsgBlock} m cstp (sVis () _)
...   | evSync {e = MsgBatchDone} m cstp (sVis () _)
...   | evSync {e = MsgClientDone} m cstp (sVis () _)
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- U=(CB-loop stIdle, IS stIdle): client loop-back → (IC stIdle, IS stIdle).
U-τ : ∀ {W″} → (JP (CB-loop stIdle) (IS stIdle)) ─[ τ ]─► W″ → W″ ≡ JP (IC stIdle) (IS stIdle)
U-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stIdle) (IS stIdle)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stIdle) (IS stIdle) pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
U-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stIdle) (IS stIdle) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- I=(CB-loop stBusy, IS stBusy): client loop-back → (IC stBusy, IS stBusy).
I-τ : ∀ {W″} → (JP (CB-loop stBusy) (IS stBusy)) ─[ τ ]─► W″ → W″ ≡ JP (IC stBusy) (IS stBusy)
I-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (IS stBusy)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stBusy) (IS stBusy) pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
I-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stBusy) (IS stBusy) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- S=(CB-loop stStreaming, IS stStreaming): client loop-back → (IC stStreaming, IS stStreaming).
S-τ : ∀ {W″} → (JP (CB-loop stStreaming) (IS stStreaming)) ─[ τ ]─► W″ → W″ ≡ JP (IC stStreaming) (IS stStreaming)
S-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (IS stStreaming)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stStreaming) (IS stStreaming) pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
S-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stStreaming) (IS stStreaming) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- E1=(IC stDone, SB-loop stDone): server loop-back → (IC stDone, IS stDone).
E1-τ : ∀ {W″} → (JP (IC stDone) (SB-loop stDone)) ─[ τ ]─► W″ → W″ ≡ JP (IC stDone) (IS stDone)
E1-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stDone) (SB-loop stDone)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stDone) (SB-loop stDone) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil refl) refl = refl
...   | τR Q'' (sTau () _) refl
E1-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stDone) (SB-loop stDone) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- E2=(CB-loop stDone, IS stDone): client loop-back → (IC stDone, IS stDone).
E2-τ : ∀ {W″} → (JP (CB-loop stDone) (IS stDone)) ─[ τ ]─► W″ → W″ ≡ JP (IC stDone) (IS stDone)
E2-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stDone) (IS stDone)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stDone) (IS stDone) pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau () _) refl
E2-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stDone) (IS stDone) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- W2=(CB-blk b, SB-loop stStreaming): server loop-back → (CB-blk b, IS stStreaming).
W2-τ : ∀ {b W″} → (JP (CB-blk b) (SB-loop stStreaming)) ─[ τ ]─► W″ → W″ ≡ JP (CB-blk b) (IS stStreaming)
W2-τ {b} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-loop stStreaming)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-blk b) (SB-loop stStreaming) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil refl) refl = refl
...   | τR Q'' (sTau () _) refl
W2-τ {b} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-blk b) (SB-loop stStreaming) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m cstp (sVis () _)
...   | evSync {e = MsgStartBatch} m cstp (sVis () _)
...   | evSync {e = MsgNoBlocks} m cstp (sVis () _)
...   | evSync {e = MsgBlock} m cstp (sVis () _)
...   | evSync {e = MsgBatchDone} m cstp (sVis () _)
...   | evSync {e = MsgClientDone} m cstp (sVis () _)
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- W6=(CB-loop stStreaming, SB-blk b): client loop-back → (IC stStreaming, SB-blk b).
W6-τ : ∀ {b W″} → (JP (CB-loop stStreaming) (SB-blk b)) ─[ τ ]─► W″ → W″ ≡ JP (IC stStreaming) (SB-blk b)
W6-τ {b} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-blk b)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stStreaming) (SB-blk b) pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
W6-τ {b} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-blk b) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- W7=(CB-loop stStreaming, SB-bdone): client loop-back → (IC stStreaming, SB-bdone).
W7-τ : ∀ {W″} → (JP (CB-loop stStreaming) SB-bdone) ─[ τ ]─► W″ → W″ ≡ JP (IC stStreaming) SB-bdone
W7-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-bdone)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stStreaming) (SB-bdone) pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
W7-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-bdone) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m


-- E=(CB-loop stDone, SB-loop stDone): two loop τ's, to E1 or E2.
E-τ : ∀ {W″} → (JP (CB-loop stDone) (SB-loop stDone)) ─[ τ ]─► W″ → (W″ ≡ JP (IC stDone) (SB-loop stDone)) ⊎ (W″ ≡ JP (CB-loop stDone) (IS stDone))
E-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stDone) (SB-loop stDone)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stDone) (SB-loop stDone) pst
...   | τL P'' (sSil refl) refl = inj₁ refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil refl) refl = inj₂ refl
...   | τR Q'' (sTau () _) refl
E-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stDone) (SB-loop stDone) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- G=(CB-loop stBusy, SB-loop stBusy): two loop τ's, to H or I.
G-τ : ∀ {W″} → (JP (CB-loop stBusy) (SB-loop stBusy)) ─[ τ ]─► W″ → (W″ ≡ JP (IC stBusy) (SB-loop stBusy)) ⊎ (W″ ≡ JP (CB-loop stBusy) (IS stBusy))
G-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-loop stBusy)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stBusy) (SB-loop stBusy) pst
...   | τL P'' (sSil refl) refl = inj₁ refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil refl) refl = inj₂ refl
...   | τR Q'' (sTau () _) refl
G-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-loop stBusy) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- P=(CB-loop stStreaming, SB-loop stStreaming): two loop τ's, to R or S.
P-τ : ∀ {W″} → (JP (CB-loop stStreaming) (SB-loop stStreaming)) ─[ τ ]─► W″ → (W″ ≡ JP (IC stStreaming) (SB-loop stStreaming)) ⊎ (W″ ≡ JP (CB-loop stStreaming) (IS stStreaming))
P-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming) pst
...   | τL P'' (sSil refl) refl = inj₁ refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil refl) refl = inj₂ refl
...   | τR Q'' (sTau () _) refl
P-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m

-- Q=(CB-loop stIdle, SB-loop stIdle): two loop τ's, to T or U.
Q-τ : ∀ {W″} → (JP (CB-loop stIdle) (SB-loop stIdle)) ─[ τ ]─► W″ → (W″ ≡ JP (IC stIdle) (SB-loop stIdle)) ⊎ (W″ ≡ JP (CB-loop stIdle) (IS stIdle))
Q-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stIdle) (SB-loop stIdle)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stIdle) (SB-loop stIdle) pst
...   | τL P'' (sSil refl) refl = inj₁ refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil refl) refl = inj₂ refl
...   | τR Q'' (sTau () _) refl
Q-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stIdle) (SB-loop stIdle) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch} m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks} m (sVis () _) sstp
...   | evSync {e = MsgBlock} m (sVis () _) sstp
...   | evSync {e = MsgBatchDone} m (sVis () _) sstp
...   | evSync {e = MsgClientDone} m (sVis () _) sstp
...   | evSync {e = apiBF mm} m cstp sstp = ⊥-elim m


-- W3=(CB-blk b, IS stStreaming): stable; client delivers recvBFBlock (solo), server offers block/bdone apis (solo).
W3-noτ : ∀ {b W″} → ¬ ((JP (CB-blk b) (IS stStreaming)) ─[ τ ]─► W″)
W3-noτ {b} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (IS stStreaming)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-blk b) (IS stStreaming) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
W3-noτ {b} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-blk b) (IS stStreaming) pev
...   | evL ¬m cstp = ¬m mem
...   | evR ¬m sstp = ¬m mem
...   | evBoth ¬m cstp sstp = ¬m mem
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)}   refl ()) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)}     refl ()) sstp
...   | evSync {e = MsgBlock}        m (sVis {at = (_ , MsgBlock)}        refl ()) sstp
...   | evSync {e = MsgBatchDone}    m (sVis {at = (_ , MsgBatchDone)}    refl ()) sstp
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)}   refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = m

-- Z=(IC stDone, IS stDone): terminal; both peers return, no τ at all.
Z-noτ : ∀ {W″} → ¬ ((JP (IC stDone) (IS stDone)) ─[ τ ]─► W″)
Z-noτ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stDone) (IS stDone)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stDone) (IS stDone) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau () _) refl
Z-noτ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stDone) (IS stDone) pev
...   | evL ¬m cstp = ¬m mem
...   | evR ¬m sstp = ¬m mem
...   | evBoth ¬m cstp sstp = ¬m mem
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch}   m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis () _) sstp
...   | evSync {e = MsgBlock}        m (sVis () _) sstp
...   | evSync {e = MsgBatchDone}    m (sVis () _) sstp
...   | evSync {e = MsgClientDone}   m (sVis () _) sstp
...   | evSync {e = apiBF mm}        m (sVis () _) sstp

-- W4=(CB-blk b, SB-blk b′): stable; client delivers recvBFBlock, server's MsgBlock awaits a sync.
W4-noτ : ∀ {b b′ W″} → ¬ ((JP (CB-blk b) (SB-blk b′)) ─[ τ ]─► W″)
W4-noτ {b} {b′} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-blk b′)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-blk b) (SB-blk b′) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
W4-noτ {b} {b′} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-blk b) (SB-blk b′) pev
...   | evL ¬m cstp = ¬m mem
...   | evR ¬m sstp = ¬m mem
...   | evBoth ¬m cstp sstp = ¬m mem
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)}   refl ()) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)}     refl ()) sstp
...   | evSync {e = MsgBlock}        m (sVis {at = (_ , MsgBlock)}        refl ()) sstp
...   | evSync {e = MsgBatchDone}    m (sVis {at = (_ , MsgBatchDone)}    refl ()) sstp
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)}   refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = m

-- W5=(CB-blk b, SB-bdone): stable; client delivers recvBFBlock, server's MsgBatchDone awaits a sync.
W5-noτ : ∀ {b W″} → ¬ ((JP (CB-blk b) SB-bdone) ─[ τ ]─► W″)
W5-noτ {b} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) SB-bdone) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-blk b) SB-bdone pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
W5-noτ {b} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-blk b) SB-bdone pev
...   | evL ¬m cstp = ¬m mem
...   | evR ¬m sstp = ¬m mem
...   | evBoth ¬m cstp sstp = ¬m mem
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)}   refl ()) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)}     refl ()) sstp
...   | evSync {e = MsgBlock}        m (sVis {at = (_ , MsgBlock)}        refl ()) sstp
...   | evSync {e = MsgBatchDone}    m (sVis {at = (_ , MsgBatchDone)}    refl ()) sstp
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)}   refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = m

-- A=(IC stIdle, IS stIdle): stable; client offers only apiBF (no message sync possible).
A-noτ : ∀ {W″} → ¬ (JP (IC stIdle) (IS stIdle) ─[ τ ]─► W″)
A-noτ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (IC stIdle) (IS stIdle)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (IC stIdle) (IS stIdle) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
A-noτ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (IC stIdle) (IS stIdle) pev
...   | evL ¬m cstp = ¬m mem
...   | evR ¬m sstp = ¬m mem
...   | evBoth ¬m cstp sstp = ¬m mem
...   | evSync {e = MsgRequestRange} m (sVis {at = (_ , MsgRequestRange)} refl ()) sstp
...   | evSync {e = MsgStartBatch}   m (sVis {at = (_ , MsgStartBatch)}   refl ()) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis {at = (_ , MsgNoBlocks)}     refl ()) sstp
...   | evSync {e = MsgBlock}        m (sVis {at = (_ , MsgBlock)}        refl ()) sstp
...   | evSync {e = MsgBatchDone}    m (sVis {at = (_ , MsgBatchDone)}    refl ()) sstp
...   | evSync {e = MsgClientDone}   m (sVis {at = (_ , MsgClientDone)}   refl ()) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = m

------------------------------------------------------------------------
-- ¬ Diverges at each IMPL joint state (a finite, acyclic τ-DAG).
------------------------------------------------------------------------

-- stable joint states never diverge.
nd-A : ¬ Diverges (JP (IC stIdle) (IS stIdle))
nd-A d = A-noτ (d .Diverges.step)
nd-F : ∀ {r} → ¬ Diverges (JP (IC stBusy) (SB-req r))
nd-F d = F-noτ (d .Diverges.step)
nd-J : ¬ Diverges (JP (IC stBusy) (IS stBusy))
nd-J d = J-noτ (d .Diverges.step)
nd-V : ¬ Diverges (JP (IC stStreaming) (IS stStreaming))
nd-V d = V-noτ (d .Diverges.step)
nd-W3 : ∀ {b} → ¬ Diverges (JP (CB-blk b) (IS stStreaming))
nd-W3 d = W3-noτ (d .Diverges.step)
nd-W4 : ∀ {b b′} → ¬ Diverges (JP (CB-blk b) (SB-blk b′))
nd-W4 d = W4-noτ (d .Diverges.step)
nd-W5 : ∀ {b} → ¬ Diverges (JP (CB-blk b) SB-bdone)
nd-W5 d = W5-noτ (d .Diverges.step)
nd-Z : ¬ Diverges (JP (IC stDone) (IS stDone))
nd-Z d = Z-noτ (d .Diverges.step)

-- single-loop transients converge to an already-converging successor.
nd-D : ∀ {r} → ¬ Diverges (JP (CB-loop stBusy) (SB-req r))
nd-D d = nd-F (subst Diverges (D-τ (d .Diverges.step)) (d .Diverges.rest))
nd-H : ¬ Diverges (JP (IC stBusy) (SB-loop stBusy))
nd-H d = nd-J (subst Diverges (H-τ (d .Diverges.step)) (d .Diverges.rest))
nd-I : ¬ Diverges (JP (CB-loop stBusy) (IS stBusy))
nd-I d = nd-J (subst Diverges (I-τ (d .Diverges.step)) (d .Diverges.rest))
nd-R : ¬ Diverges (JP (IC stStreaming) (SB-loop stStreaming))
nd-R d = nd-V (subst Diverges (R-τ (d .Diverges.step)) (d .Diverges.rest))
nd-S : ¬ Diverges (JP (CB-loop stStreaming) (IS stStreaming))
nd-S d = nd-V (subst Diverges (S-τ (d .Diverges.step)) (d .Diverges.rest))
nd-T : ¬ Diverges (JP (IC stIdle) (SB-loop stIdle))
nd-T d = nd-A (subst Diverges (T-τ (d .Diverges.step)) (d .Diverges.rest))
nd-U : ¬ Diverges (JP (CB-loop stIdle) (IS stIdle))
nd-U d = nd-A (subst Diverges (U-τ (d .Diverges.step)) (d .Diverges.rest))
nd-E1 : ¬ Diverges (JP (IC stDone) (SB-loop stDone))
nd-E1 d = nd-Z (subst Diverges (E1-τ (d .Diverges.step)) (d .Diverges.rest))
nd-E2 : ¬ Diverges (JP (CB-loop stDone) (IS stDone))
nd-E2 d = nd-Z (subst Diverges (E2-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W2 : ∀ {b} → ¬ Diverges (JP (CB-blk b) (SB-loop stStreaming))
nd-W2 d = nd-W3 (subst Diverges (W2-τ (d .Diverges.step)) (d .Diverges.rest))

-- sync transients converge to their (converging) post-sync successor.
nd-B : ∀ {r} → ¬ Diverges (JP (CB-req r) (IS stIdle))
nd-B d = nd-D (subst Diverges (B-τ (d .Diverges.step)) (d .Diverges.rest))
nd-C : ¬ Diverges (JP CB-cdone (IS stIdle))
nd-C d = nd-E (subst Diverges (C-τ (d .Diverges.step)) (d .Diverges.rest))
  where
  -- E=(CB-loop stDone, SB-loop stDone): both loops converge (to E1 / E2).
  nd-E : ¬ Diverges (JP (CB-loop stDone) (SB-loop stDone))
  nd-E d′ with E-τ (d′ .Diverges.step)
  ... | inj₁ eq = nd-E1 (subst Diverges eq (d′ .Diverges.rest))
  ... | inj₂ eq = nd-E2 (subst Diverges eq (d′ .Diverges.rest))
nd-M : ¬ Diverges (JP (IC stBusy) SB-sbatch)
nd-M d = nd-P (subst Diverges (M-τ (d .Diverges.step)) (d .Diverges.rest))
  where
  -- P=(CB-loop stStreaming, SB-loop stStreaming): both loops converge (to R / S).
  nd-P : ¬ Diverges (JP (CB-loop stStreaming) (SB-loop stStreaming))
  nd-P d′ with P-τ (d′ .Diverges.step)
  ... | inj₁ eq = nd-R (subst Diverges eq (d′ .Diverges.rest))
  ... | inj₂ eq = nd-S (subst Diverges eq (d′ .Diverges.rest))
nd-N : ¬ Diverges (JP (IC stBusy) SB-noblk)
nd-N d = nd-Q (subst Diverges (N-τ (d .Diverges.step)) (d .Diverges.rest))
  where
  -- Q=(CB-loop stIdle, SB-loop stIdle): both loops converge (to T / U).
  nd-Q : ¬ Diverges (JP (CB-loop stIdle) (SB-loop stIdle))
  nd-Q d′ with Q-τ (d′ .Diverges.step)
  ... | inj₁ eq = nd-T (subst Diverges eq (d′ .Diverges.rest))
  ... | inj₂ eq = nd-U (subst Diverges eq (d′ .Diverges.rest))
nd-W : ∀ {b} → ¬ Diverges (JP (IC stStreaming) (SB-blk b))
nd-W d = nd-W2 (subst Diverges (W-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Y : ¬ Diverges (JP (IC stStreaming) SB-bdone)
nd-Y d = nd-Q (subst Diverges (Y-τ (d .Diverges.step)) (d .Diverges.rest))
  where
  nd-Q : ¬ Diverges (JP (CB-loop stIdle) (SB-loop stIdle))
  nd-Q d′ with Q-τ (d′ .Diverges.step)
  ... | inj₁ eq = nd-T (subst Diverges eq (d′ .Diverges.rest))
  ... | inj₂ eq = nd-U (subst Diverges eq (d′ .Diverges.rest))
nd-W6 : ∀ {b} → ¬ Diverges (JP (CB-loop stStreaming) (SB-blk b))
nd-W6 d = nd-W (subst Diverges (W6-τ (d .Diverges.step)) (d .Diverges.rest))
nd-W7 : ¬ Diverges (JP (CB-loop stStreaming) SB-bdone)
nd-W7 d = nd-Y (subst Diverges (W7-τ (d .Diverges.step)) (d .Diverges.rest))

-- K=(CB-loop stBusy, SB-sbatch): the only τ is the client loop-back → (IC stBusy, SB-sbatch).
K-τ : ∀ {W″} → (JP (CB-loop stBusy) SB-sbatch) ─[ τ ]─► W″ → W″ ≡ JP (IC stBusy) SB-sbatch
K-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) SB-sbatch) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stBusy) SB-sbatch pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
K-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stBusy) SB-sbatch pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch}   m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis () _) sstp
...   | evSync {e = MsgBlock}        m (sVis () _) sstp
...   | evSync {e = MsgBatchDone}    m (sVis () _) sstp
...   | evSync {e = MsgClientDone}   m (sVis () _) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- L=(CB-loop stBusy, SB-noblk): the only τ is the client loop-back → (IC stBusy, SB-noblk).
L-τ : ∀ {W″} → (JP (CB-loop stBusy) SB-noblk) ─[ τ ]─► W″ → W″ ≡ JP (IC stBusy) SB-noblk
L-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) SB-noblk) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-loop stBusy) SB-noblk pst
...   | τL P'' (sSil refl) refl = refl
...   | τL P'' (sTau () _) refl
...   | τR Q'' (sSil ()) refl
...   | τR Q'' (sTau refl ()) refl
L-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-loop stBusy) SB-noblk pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m (sVis () _) sstp
...   | evSync {e = MsgStartBatch}   m (sVis () _) sstp
...   | evSync {e = MsgNoBlocks}     m (sVis () _) sstp
...   | evSync {e = MsgBlock}        m (sVis () _) sstp
...   | evSync {e = MsgBatchDone}    m (sVis () _) sstp
...   | evSync {e = MsgClientDone}   m (sVis () _) sstp
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- K / L converge to M / N respectively.
nd-K : ¬ Diverges (JP (CB-loop stBusy) SB-sbatch)
nd-K d = nd-M (subst Diverges (K-τ (d .Diverges.step)) (d .Diverges.rest))
nd-L : ¬ Diverges (JP (CB-loop stBusy) SB-noblk)
nd-L d = nd-N (subst Diverges (L-τ (d .Diverges.step)) (d .Diverges.rest))

-- Ta=(CB-req r, SB-loop stIdle): the only τ is the server loop-back → (CB-req r, IS stIdle).
Ta-τ : ∀ {r W″} → (JP (CB-req r) (SB-loop stIdle)) ─[ τ ]─► W″ → W″ ≡ JP (CB-req r) (IS stIdle)
Ta-τ {r} st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg (CB-req r) (SB-loop stIdle)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg (CB-req r) (SB-loop stIdle) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil refl) refl = refl
...   | τR Q'' (sTau () _) refl
Ta-τ {r} st | hτH P' mem pev refl with Par-ev-elim msgBF mrg (CB-req r) (SB-loop stIdle) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m cstp (sVis () _)
...   | evSync {e = MsgStartBatch}   m cstp (sVis () _)
...   | evSync {e = MsgNoBlocks}     m cstp (sVis () _)
...   | evSync {e = MsgBlock}        m cstp (sVis () _)
...   | evSync {e = MsgBatchDone}    m cstp (sVis () _)
...   | evSync {e = MsgClientDone}   m cstp (sVis () _)
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- Tb=(CB-cdone, SB-loop stIdle): the only τ is the server loop-back → (CB-cdone, IS stIdle).
Tb-τ : ∀ {W″} → (JP CB-cdone (SB-loop stIdle)) ─[ τ ]─► W″ → W″ ≡ JP CB-cdone (IS stIdle)
Tb-τ st with Hide-τ-elim msgBF (AbsOps.Par msgBF mrg CB-cdone (SB-loop stIdle)) st
... | hτP P' pst refl with Par-τ-elim msgBF mrg CB-cdone (SB-loop stIdle) pst
...   | τL P'' (sSil ()) refl
...   | τL P'' (sTau refl ()) refl
...   | τR Q'' (sSil refl) refl = refl
...   | τR Q'' (sTau () _) refl
Tb-τ st | hτH P' mem pev refl with Par-ev-elim msgBF mrg CB-cdone (SB-loop stIdle) pev
...   | evL ¬m cstp = ⊥-elim (¬m mem)
...   | evR ¬m sstp = ⊥-elim (¬m mem)
...   | evBoth ¬m cstp sstp = ⊥-elim (¬m mem)
...   | evSync {e = MsgRequestRange} m cstp (sVis () _)
...   | evSync {e = MsgStartBatch}   m cstp (sVis () _)
...   | evSync {e = MsgNoBlocks}     m cstp (sVis () _)
...   | evSync {e = MsgBlock}        m cstp (sVis () _)
...   | evSync {e = MsgBatchDone}    m cstp (sVis () _)
...   | evSync {e = MsgClientDone}   m cstp (sVis () _)
...   | evSync {e = apiBF mm}        m cstp sstp = ⊥-elim m

-- Ta / Tb converge (to B / C).
nd-Ta : ∀ {r} → ¬ Diverges (JP (CB-req r) (SB-loop stIdle))
nd-Ta d = nd-B (subst Diverges (Ta-τ (d .Diverges.step)) (d .Diverges.rest))
nd-Tb : ¬ Diverges (JP CB-cdone (SB-loop stIdle))
nd-Tb d = nd-C (subst Diverges (Tb-τ (d .Diverges.step)) (d .Diverges.rest))

-- standalone convergence for the double-loop states (used as gnd in the Good graph).
nd-E : ¬ Diverges (JP (CB-loop stDone) (SB-loop stDone))
nd-E d with E-τ (d .Diverges.step)
... | inj₁ eq = nd-E1 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-E2 (subst Diverges eq (d .Diverges.rest))
nd-G : ¬ Diverges (JP (CB-loop stBusy) (SB-loop stBusy))
nd-G d with G-τ (d .Diverges.step)
... | inj₁ eq = nd-H (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-I (subst Diverges eq (d .Diverges.rest))
nd-P : ¬ Diverges (JP (CB-loop stStreaming) (SB-loop stStreaming))
nd-P d with P-τ (d .Diverges.step)
... | inj₁ eq = nd-R (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-S (subst Diverges eq (d .Diverges.rest))
nd-Q : ¬ Diverges (JP (CB-loop stIdle) (SB-loop stIdle))
nd-Q d with Q-τ (d .Diverges.step)
... | inj₁ eq = nd-T (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nd-U (subst Diverges eq (d .Diverges.rest))

------------------------------------------------------------------------
-- The coinductive `Good` invariant at every reachable IMPL joint state.
------------------------------------------------------------------------

-- forward declarations.
gA  : Good (JP (IC stIdle) (IS stIdle))
gB  : ∀ r → Good (JP (CB-req r) (IS stIdle))
gC  : Good (JP CB-cdone (IS stIdle))
gD  : ∀ r → Good (JP (CB-loop stBusy) (SB-req r))
gE  : Good (JP (CB-loop stDone) (SB-loop stDone))
gE1 : Good (JP (IC stDone) (SB-loop stDone))
gE2 : Good (JP (CB-loop stDone) (IS stDone))
gF  : ∀ r → Good (JP (IC stBusy) (SB-req r))
gG  : Good (JP (CB-loop stBusy) (SB-loop stBusy))
gH  : Good (JP (IC stBusy) (SB-loop stBusy))
gI  : Good (JP (CB-loop stBusy) (IS stBusy))
gJ  : Good (JP (IC stBusy) (IS stBusy))
gK  : Good (JP (CB-loop stBusy) SB-sbatch)
gL  : Good (JP (CB-loop stBusy) SB-noblk)
gM  : Good (JP (IC stBusy) SB-sbatch)
gN  : Good (JP (IC stBusy) SB-noblk)
gP  : Good (JP (CB-loop stStreaming) (SB-loop stStreaming))
gQ  : Good (JP (CB-loop stIdle) (SB-loop stIdle))
gR  : Good (JP (IC stStreaming) (SB-loop stStreaming))
gS  : Good (JP (CB-loop stStreaming) (IS stStreaming))
gT  : Good (JP (IC stIdle) (SB-loop stIdle))
gU  : Good (JP (CB-loop stIdle) (IS stIdle))
gV  : Good (JP (IC stStreaming) (IS stStreaming))
gW  : ∀ b → Good (JP (IC stStreaming) (SB-blk b))
gW2 : ∀ b → Good (JP (CB-blk b) (SB-loop stStreaming))
gW3 : ∀ b → Good (JP (CB-blk b) (IS stStreaming))
gW4 : ∀ b b′ → Good (JP (CB-blk b) (SB-blk b′))
gW5 : ∀ b → Good (JP (CB-blk b) SB-bdone)
gW6 : ∀ b → Good (JP (CB-loop stStreaming) (SB-blk b))
gW7 : Good (JP (CB-loop stStreaming) SB-bdone)
gY  : Good (JP (IC stStreaming) SB-bdone)
gZ  : Good (JP (IC stDone) (IS stDone))
gTa : ∀ r → Good (JP (CB-req r) (SB-loop stIdle))
gTb : Good (JP CB-cdone (SB-loop stIdle))

-- gA = (IC stIdle, IS stIdle).
gA .gnd = nd-A
gA .gτ st = ⊥-elim (A-noτ st)
gA .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stIdle) (IS stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stIdle) (IS stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 cstp (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 cstp (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) = gB aa
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = gC
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gB = (CB-req r, IS stIdle).
gB r .gnd = nd-B
gB r .gτ st with B-τ st
... | refl = gD r
gB r .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-req r) (IS stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-req r) (IS stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gC = (CB-cdone, IS stIdle).
gC .gnd = nd-C
gC .gτ st with C-τ st
... | refl = gE
gC .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-cdone) (IS stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-cdone) (IS stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gD = (CB-loop stBusy, SB-req r).
gD r .gnd = nd-D
gD r .gτ st with D-τ st
... | refl = gF r
gD r .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-req r)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-req r) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
gD r .gev st | heV P' ¬m pev | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl sbreq) with aa ≟ r
... | yes refl with sbreq
...   | refl = gG
gD r .gev st | heV P' ¬m pev | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl ()) | no _
-- gE = (CB-loop stDone, SB-loop stDone).
gE .gnd = nd-E
gE .gτ st with E-τ st
... | inj₁ refl = gE1
... | inj₂ refl = gE2
gE .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stDone) (SB-loop stDone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stDone) (SB-loop stDone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gE1 = (IC stDone, SB-loop stDone).
gE1 .gnd = nd-E1
gE1 .gτ st with E1-τ st
... | refl = gZ
gE1 .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stDone) (SB-loop stDone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stDone) (SB-loop stDone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gE2 = (CB-loop stDone, IS stDone).
gE2 .gnd = nd-E2
gE2 .gτ st with E2-τ st
... | refl = gZ
gE2 .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stDone) (IS stDone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stDone) (IS stDone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gF = (IC stBusy, SB-req r).
gF r .gnd = nd-F
gF r .gτ st = ⊥-elim (F-noτ st)
gF r .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-req r)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-req r) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
gF r .gev st | heV P' ¬m pev | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl sbreq) with aa ≟ r
... | yes refl with sbreq
...   | refl = gH
gF r .gev st | heV P' ¬m pev | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl ()) | no _
-- gG = (CB-loop stBusy, SB-loop stBusy).
gG .gnd = nd-G
gG .gτ st with G-τ st
... | inj₁ refl = gH
... | inj₂ refl = gI
gG .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-loop stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-loop stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gH = (IC stBusy, SB-loop stBusy).
gH .gnd = nd-H
gH .gτ st with H-τ st
... | refl = gJ
gH .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-loop stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-loop stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gI = (CB-loop stBusy, IS stBusy).
gI .gnd = nd-I
gI .gτ st with I-τ st
... | refl = gJ
gI .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (IS stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (IS stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = gK
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl refl) = gL
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gJ = (IC stBusy, IS stBusy).
gJ .gnd = nd-J
gJ .gτ st = ⊥-elim (J-noτ st)
gJ .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (IS stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (IS stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = gM
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl refl) = gN
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gK = (CB-loop stBusy, SB-sbatch).
gK .gnd = nd-K
gK .gτ st with K-τ st
... | refl = gM
gK .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-sbatch)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-sbatch) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gL = (CB-loop stBusy, SB-noblk).
gL .gnd = nd-L
gL .gτ st with L-τ st
... | refl = gN
gL .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-noblk)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-noblk) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gM = (IC stBusy, SB-sbatch).
gM .gnd = nd-M
gM .gτ st with M-τ st
... | refl = gP
gM .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-sbatch)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-sbatch) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gN = (IC stBusy, SB-noblk).
gN .gnd = nd-N
gN .gτ st with N-τ st
... | refl = gQ
gN .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-noblk)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-noblk) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gP = (CB-loop stStreaming, SB-loop stStreaming).
gP .gnd = nd-P
gP .gτ st with P-τ st
... | inj₁ refl = gR
... | inj₂ refl = gS
gP .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gQ = (CB-loop stIdle, SB-loop stIdle).
gQ .gnd = nd-Q
gQ .gτ st with Q-τ st
... | inj₁ refl = gT
... | inj₂ refl = gU
gQ .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stIdle) (SB-loop stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stIdle) (SB-loop stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gR = (IC stStreaming, SB-loop stStreaming).
gR .gnd = nd-R
gR .gτ st with R-τ st
... | refl = gV
gR .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-loop stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (SB-loop stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gS = (CB-loop stStreaming, IS stStreaming).
gS .gnd = nd-S
gS .gτ st with S-τ st
... | refl = gV
gS .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (IS stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (IS stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} {a = aa} refl refl) = gW6 aa
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = gW7
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gT = (IC stIdle, SB-loop stIdle).
gT .gnd = nd-T
gT .gτ st with T-τ st
... | refl = gA
gT .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stIdle) (SB-loop stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stIdle) (SB-loop stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 cstp (sVis () _)
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 cstp (sVis () _)
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) = gTa aa
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = gTb
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gU = (CB-loop stIdle, IS stIdle).
gU .gnd = nd-U
gU .gτ st with U-τ st
... | refl = gA
gU .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stIdle) (IS stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stIdle) (IS stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gV = (IC stStreaming, IS stStreaming).
gV .gnd = nd-V
gV .gτ st = ⊥-elim (V-noτ st)
gV .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (IS stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (IS stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} {a = aa} refl refl) = gW aa
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = gY
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gW = (IC stStreaming, SB-blk b).
gW b .gnd = nd-W
gW b .gτ st with W-τ st
... | refl = gW2 b
gW b .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-blk b)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (SB-blk b) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gW2 = (CB-blk b, SB-loop stStreaming).
gW2 b .gnd = nd-W2
gW2 b .gτ st with W2-τ st
... | refl = gW3 b
gW2 b .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-loop stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-loop stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis () _)
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
gW2 b .gev st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = gP
gW2 b .gev st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
-- gW3 = (CB-blk b, IS stStreaming).
gW3 b .gnd = nd-W3
gW3 b .gτ st = ⊥-elim (W3-noτ st)
gW3 b .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (IS stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (IS stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} {a = aa} refl refl) = gW4 b aa
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = gW5 b
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
gW3 b .gev st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = gS
gW3 b .gev st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
-- gW4 = (CB-blk b, SB-blk b′).
gW4 b b′ .gnd = nd-W4
gW4 b b′ .gτ st = ⊥-elim (W4-noτ st)
gW4 b b′ .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-blk b′)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-blk b′) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
gW4 b b′ .gev st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = gW6 b′
gW4 b b′ .gev st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
-- gW5 = (CB-blk b, SB-bdone).
gW5 b .gnd = nd-W5
gW5 b .gτ st = ⊥-elim (W5-noτ st)
gW5 b .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-bdone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-bdone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
gW5 b .gev st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = gW7
gW5 b .gev st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
-- gW6 = (CB-loop stStreaming, SB-blk b).
gW6 b .gnd = nd-W6
gW6 b .gτ st with W6-τ st
... | refl = gW b
gW6 b .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-blk b)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-blk b) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gW7 = (CB-loop stStreaming, SB-bdone).
gW7 .gnd = nd-W7
gW7 .gτ st with W7-τ st
... | refl = gY
gW7 .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-bdone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-bdone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gY = (IC stStreaming, SB-bdone).
gY .gnd = nd-Y
gY .gτ st with Y-τ st
... | refl = gQ
gY .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-bdone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (SB-bdone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gZ = (IC stDone, IS stDone).
gZ .gnd = nd-Z
gZ .gτ st = ⊥-elim (Z-noτ st)
gZ .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stDone) (IS stDone)) st
... | he√ refl = good-deadlock
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stDone) (IS stDone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gTa = (CB-req r, SB-loop stIdle).
gTa r .gnd = nd-Ta
gTa r .gτ st with Ta-τ st
... | refl = gB r
gTa r .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-req r) (SB-loop stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-req r) (SB-loop stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
-- gTb = (CB-cdone, SB-loop stIdle).
gTb .gnd = nd-Tb
gTb .gτ st with Tb-τ st
... | refl = gC
gTb .gev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-cdone) (SB-loop stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-cdone) (SB-loop stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

-- the IMPL's initial hidden state is `clientServerBF ∖ msgBF = JP (IC stIdle) (IS stIdle)`.
good-impl-init : Good (clientServerBF AbsOps.∖ msgBF)
good-impl-init = gA

-- no weakly-reachable state of the hidden IMPL diverges.
impl-noDiv : ∀ {s W} → (clientServerBF AbsOps.∖ msgBF) ⟹⟨ s ⟩ W → ¬ Diverges W
impl-noDiv = go-reach good-impl-init

-- THE REVERSE DIVERGENCE REFINEMENT: divergences of the IMPL are empty, so the
-- inclusion `divergences (clientServerBF ∖ msgBF) ⊆ divergences (BFabstract ∖ msgBF)` is vacuous.
BFabs-⊑D : (BFabstract AbsOps.∖ msgBF) ⊑D (clientServerBF AbsOps.∖ msgBF)
BFabs-⊑D div = ⊥-elim (impl-noDiv (IsDivergence.reach div) (IsDivergence.divwit div))

-- THE PIPELINED REVERSE DIVERGENCE REFINEMENT: divergences of the IMPL are empty,
-- so the inclusion into `divergences (BFabstractP ∖ msgBF)` is vacuous (same refuted impl antecedent).
BFabsP-⊑D : (BFabstractP AbsOps.∖ msgBF) ⊑D (clientServerBF AbsOps.∖ msgBF)
BFabsP-⊑D div = ⊥-elim (impl-noDiv (IsDivergence.reach div) (IsDivergence.divwit div))

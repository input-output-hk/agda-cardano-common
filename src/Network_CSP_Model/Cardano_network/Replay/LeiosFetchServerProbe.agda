{-# OPTIONS --guardedness #-}

-- INFEASIBILITY PROBE for server soundness (trace-replay Phase 5, Increment 0):
-- the full first-step inversion of `serverModel bs`, for EVERY body store `bs`.
-- It goes through all four layers Increment 1 must handle at every reachable
-- state: the outer `∥⇘ storeES ⇙`, the inner `∥⇘ apiES ⇙`, the renamed
-- producer and the `⦀` of the two serving threads, plus the store's `□` menu.
-- Result: the only first moves are the producer's wire receives (one per
-- `SIdleV` view: BlockRequest, BlockTxsRequest, Done), each leaving threads and
-- store untouched; no τ and no √ is possible.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchServerProbe where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
import Data.Unit.Polymorphic as PU
open import Function using (case_of_)
open import Level using (lift)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Process_Trees using (PTree; ExtI; AnyTypes; react; ret; sil; base; pair; fin; isStable)
open import Cardano_network.Base using (N2N_LeiosFetch)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Params using (module Params)
open import Class.DecEq using (DecEq)
open import Class.DecEq.Instances using (DecEq-List)
open import Cardano_network.Net replayParams using (Net_Api; Net_Api-≟; output)
open import Cardano_network.Data replayParams using (Payload)
open import Cardano_network.LeiosFetchP replayParams
  using (LFPEv; LFPEv-≟; receiveLFP; serverStepP; stIdle; LFPserverStClient)
open import Cardano_network.Parametric.Leios.PeersP replayParams using (ιLFP; ιLFP⁻¹; ιLFP-linv)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP replayParams
  using (ιLFP-rinv; Rd; SIdleV; siBlk; siTxs; siDone; sIdleV)
open import Cardano_network.Replay.LeiosFetchServerModel
open import Cardano_network.Replay.LeiosFetchServerParts
  using (decEBR; renE; peerAfter; ivi-elim; SE; bodyAll; store-ev; store-stable)
open import Cardano_network.ApiAlphabet replayParams using (apiES)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (EventSet; ∅ES; _□_; □-mt; mergeVis; _>>=_; iter-bind; _∥⇘_⇙_)
import CSP.Operators {E = LFPEv} LFPEv-≟ as LOp
import CSP.Rename {E₁ = LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RenLFP
import CSP.Laws.Traces.RenameDeadlock {E₁ = LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RD
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Event; evLabel; _─[_]─►_; ev; evl; √; τ; sVis; sSil; sTau)
import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} as F
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (⟹-refl; ⟹-ev)
open import Semantics.Stability {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (mk-stable; stable→react; stable-no-τ; stable-not-ret)
open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
  using (Par-τ-elim; ParτR; τL; τR; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload})
  using (loop-pfx-ev-inv; loop-pfx-no-τ)
open import CSP.Laws.DivFree.Loop LFPEv-≟ using (iter-ev-elim)
import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) as LoopN
open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) using (fBind-react)
open import CSP.Laws.Bisim.IterCong (Net_Api-≟ {Payload}) using (fIter-react)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
  using (AllT; AllL; _∷_; AllT-□; AllT-⟶; AllT-Output; AllT-Ret; AllT-Stop; AllT->>=)

------------------------------------------------------------------------
-- Vocabulary
------------------------------------------------------------------------

-- every Idle move of the producer is a wire receive on its own cell
sidle-wire : ∀ {x t′} → SIdleV lS dS x t′ → Σ[ p ∈ Payload ] x ≡ F.evLabel Payload (receiveLFP lS dS) p
sidle-wire (siBlk _)    = _ , refl
sidle-wire (siTxs _ _)  = _ , refl
sidle-wire siDone       = _ , refl

------------------------------------------------------------------------
-- The producer at Idle
------------------------------------------------------------------------

-- the producer's first move: one of its three Idle receives, renamed
peer-ev : ∀ {e′ W} → peerS ─[ ev e′ ]─► W
        → Σ[ x ∈ F.Event ] Σ[ t′ ∈ Rd ] (SIdleV lS dS x t′ × e′ ≡ evl (renE x) × W ≡ peerAfter t′)
peer-ev st with RD.ren-ev-inv {inv = RenLFP.ι-vis-inv} {P = LFPserverStClient lS dS} st
... | inj₂ (_ , _ , () , _)
... | inj₁ ((A₁ , e₁′) , a , (A , e₂) , b , P₁ , stP , inv≡ , refl , refl)
  with iter-ev-elim (serverStepP lS dS stIdle) (serverStepP lS dS) stP
...   | t′ , st₂ , refl with ivi-elim inv≡
...     | e₁ , refl , refl = F.evLabel A e₁ b , t′ , sIdleV st₂ , refl , refl

-- the producer has no silent move at Idle
peer-no-τ : ∀ {W} → ¬ (peerS ─[ τ ]─► W)
peer-no-τ st with RD.ren-τ-inv {inv = RenLFP.ι-vis-inv} {P = LFPserverStClient lS dS} st
... | _ , F.sSil () , _
... | _ , F.sTau refl () , _

------------------------------------------------------------------------
-- The two serving threads at their loop heads
------------------------------------------------------------------------

-- every first move of the threads is an api report, hence in `apiES`
threads-ev : ∀ {X e a M} → threadsS ─[ ev (evl (evLabel X e a)) ]─► M → EventSet.mem apiES (X , e) a
threads-ev st with Par-ev-elim ∅ES _ _ _ st
... | evSync () _ _
... | evL _ st₁ with loop-pfx-ev-inv _ _ _ st₁
...   | _ , refl , _ = ptt
threads-ev st | evR _ st₂ with loop-pfx-ev-inv _ _ _ st₂
...   | _ , refl , _ = ptt
threads-ev st | evBoth _ st₁ _ with loop-pfx-ev-inv _ _ _ st₁
...   | _ , refl , _ = ptt

-- the threads have no silent move at their loop heads
threads-no-τ : ∀ {M} → ¬ (threadsS ─[ τ ]─► M)
threads-no-τ st with Par-τ-elim ∅ES _ _ _ st
... | τL _ st₁ _ = loop-pfx-no-τ _ _ _ st₁
... | τR _ st₂ _ = loop-pfx-no-τ _ _ _ st₂

------------------------------------------------------------------------
-- The body store, for any `bs`: `store-ev`, `store-stable` (now in `LeiosFetchServerParts`)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The inner composite (producer ∥ threads) and the whole model
------------------------------------------------------------------------

-- no Idle move of the producer is an api event
peer-not-api : ∀ {X e a W} → peerS ─[ ev (evl (evLabel X e a)) ]─► W → ¬ EventSet.mem apiES (X , e) a
peer-not-api st m with peer-ev st
... | x , t′ , sv , eq , _ with sidle-wire sv
...   | p , refl with eq
...     | refl = m

-- the inner composite at its initial state
inner : Proc
inner = peerS ∥⇘ apiES ⇙ threadsS

-- the inner composite's first move is the producer's receive, alone
inner-ev : ∀ {e M} → inner ─[ ev (evl e) ]─► M
         → Σ[ x ∈ F.Event ] Σ[ t′ ∈ Rd ]
             (SIdleV lS dS x t′ × e ≡ renE x × M ≡ (peerAfter t′ ∥⇘ apiES ⇙ threadsS))
inner-ev st with Par-ev-elim apiES _ peerS threadsS st
... | evSync m stP _ = ⊥-elim (peer-not-api stP m)
... | evL _ stP with peer-ev stP
...   | x , t′ , sv , refl , refl = x , t′ , sv , refl , refl
inner-ev st | evR ¬m stT     = ⊥-elim (¬m (threads-ev stT))
inner-ev st | evBoth ¬m _ stT = ⊥-elim (¬m (threads-ev stT))

-- a producer Idle move is a wire event: neither in `apiES` nor in `storeES`
wire-out : ∀ {x t′ X e a} → SIdleV lS dS x t′ → evLabel X e a ≡ renE x
         → ¬ EventSet.mem apiES (X , e) a × ¬ EventSet.mem storeES (X , e) a
wire-out (siBlk _)   refl = (λ ()) , (λ ())
wire-out (siTxs _ _) refl = (λ ()) , (λ ())
wire-out siDone      refl = (λ ()) , (λ ())

-- no first move of the inner composite is a store event
inner-not-store : ∀ {X e a M} → inner ─[ ev (evl (evLabel X e a)) ]─► M → ¬ EventSet.mem storeES (X , e) a
inner-not-store st =
  let (_ , _ , sv , eq , _) = inner-ev st in Σ.proj₂ (wire-out sv eq)

-- PROBE (visible): every first visible move of `serverModel bs` is one of the
-- producer's three Idle receives, leaving threads and store where they were
init-ev : ∀ {bs e M} → serverModel bs ─[ ev (evl e) ]─► M
        → Σ[ x ∈ F.Event ] Σ[ t′ ∈ Rd ]
            (SIdleV lS dS x t′ × e ≡ renE x × M ≡ srvAt (peerAfter t′) threadsS bs)
init-ev {bs} st = go (Par-ev-elim storeES _ inner (bodyStore nS bs) st)
  where
    -- the outer parallel's five cases
    go : ∀ {e M} → ParevR storeES (λ _ _ → ptt) inner (bodyStore nS bs) M (evl e)
       → Σ[ x ∈ F.Event ] Σ[ t′ ∈ Rd ]
           (SIdleV lS dS x t′ × e ≡ renE x × M ≡ srvAt (peerAfter t′) threadsS bs)
    go (evSync m stI _)   = ⊥-elim (inner-not-store stI m)
    go (evL _ stI)        = let (x , t′ , sv , eq , eqM) = inner-ev stI in
                            x , t′ , sv , eq , cong (λ I → I ∥⇘ storeES ⇙ bodyStore nS bs) eqM
    go (evR ¬m stS)       = ⊥-elim (¬m (store-ev {bs = bs} stS))
    go (evBoth ¬m _ stS)  = ⊥-elim (¬m (store-ev {bs = bs} stS))

-- PROBE (silent): `serverModel bs` has no τ at its initial state
init-no-τ : ∀ {bs M} → ¬ (serverModel bs ─[ τ ]─► M)
init-no-τ {bs} st = outer (Par-τ-elim storeES _ inner (bodyStore nS bs) st)
  where
    -- the inner parallel's two τ cases
    innerτ : ∀ {M} → ParτR apiES (λ _ _ → ptt) peerS threadsS M → ⊥
    innerτ (τL _ stP _) = peer-no-τ stP
    innerτ (τR _ stT _) = threads-no-τ stT

    -- the outer parallel's two τ cases
    outer : ∀ {M} → ParτR storeES (λ _ _ → ptt) inner (bodyStore nS bs) M → ⊥
    outer (τL _ stI _) = innerτ (Par-τ-elim apiES _ peerS threadsS stI)
    outer (τR _ stS _) = stable-no-τ (store-stable bs) stS

-- a parallel whose right operand is stable cannot terminate
par-no-√ : ∀ {A : EventSet} {P Q : Proc} {r M} → isStable Q
         → ¬ ((P ∥⇘ A ⇙ Q) ─[ ev (√ r) ]─► M)
par-no-√ {A} {P} {Q} sQ st with Par-ev-elim A _ P Q st
... | ev√ _ eqS = stable-not-ret {t = Q} sQ eqS

-- PROBE (termination): `serverModel bs` cannot terminate at its initial state
init-no-√ : ∀ {bs r M} → ¬ (serverModel bs ─[ ev (√ r) ]─► M)
init-no-√ {bs} = par-no-√ (store-stable bs)

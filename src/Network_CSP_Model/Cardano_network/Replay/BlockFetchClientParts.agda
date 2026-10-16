{-# OPTIONS --guardedness #-}

-- Structural inversion and forward steps for the existing pipelined PTree.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.BlockFetchClientParts (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (_<?_)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)
open import Process_Trees using (PTree; ExtI; react; base)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p
open Params p
open import Cardano_network.BlockFetch p
  using (BFEv; sendBF; receiveBF; apiBFev; doneBF; BFEv-≟; Rr)
open import Cardano_network.BlockFetchPipe p
open import CSP.Operators BFEv-≟ using (Ret; Output; ∅t; iter-bind)
open import Semantics.LTS {E = BFEv} {I = ExtI BFEv}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil; sTau)
open import CSP.Laws.DivFree.Loop BFEv-≟ using (iter-τ-elim; iter-ev-elim; itτ; itBack)
open import CSP.Laws.Bisim.IterCong BFEv-≟ using (iter-bind-ev; iter-bind-τ)
open import Cardano_network.Replay.LeiosFetchServerParts using (module OutInv)
open OutInv BFEv-≟ using (out-ev)

-- The pipelined client's process carrier.
Proc : Set₁
Proc = PTree BFEv (ExtI BFEv) Rr

module _ (k : ℕ) (l : Link) (d : Dir) where
  -- Keep the original iteration body around a residual round.
  It : Body → Proc
  It t = iter-bind t (step k l d)

  -- Application observation at this endpoint.
  apiE : (m : ApiBFTag) → ApiBFCar m → Event
  apiE m v = evLabel _ (apiBFev l d m) v

  -- Wire reception at this endpoint.
  rcvE : Payload → Event
  rcvE a = evLabel _ (receiveBF l d) a

  -- Deliver a received block before returning to the loop.
  deliver : Block → State → Body
  deliver b s = Output (apiBFev l d recvBFBlock) b (Ret (inj₁ s))

  -- Exact visible successor shapes of the original PTree menu.
  data HeadV (s : State) : Event → Body → Set₁ where
    hReq : ∀ r → occupancy s < k → HeadV s (apiE sendBFRequestRange r)
      (send l d (MsgRequestRange r) (inj₁ (pending (ranges s ∷ʳ r) (phase s) (completed s))))
    hDone : ∀ {u} → s ≡ initial → HeadV s (apiE sendBFClientDone u)
      (send l d MsgClientDone (inj₂ _))
    hStart : ∀ {r rs c tm ln} → s ≡ pending (r ∷ rs) waiting c →
      HeadV s (rcvE (tm , FromResponder , ln , blockFetch MsgStartBatch))
      (Ret (inj₁ (pending (r ∷ rs) streaming c)))
    hNone : ∀ {r rs c tm ln} → s ≡ pending (r ∷ rs) waiting c →
      HeadV s (rcvE (tm , FromResponder , ln , blockFetch MsgNoBlocks))
      (Ret (inj₁ (pending rs waiting (suc c))))
    hBlock : ∀ {r rs c tm ln} b → s ≡ pending (r ∷ rs) streaming c →
      HeadV s (rcvE (tm , FromResponder , ln , blockFetch (MsgBlock b)))
      (deliver b (pending (r ∷ rs) streaming c))
    hEnd : ∀ {r rs c tm ln} → s ≡ pending (r ∷ rs) streaming c →
      HeadV s (rcvE (tm , FromResponder , ln , blockFetch MsgBatchDone))
      (Ret (inj₁ (pending rs waiting (suc c))))

  -- Invert each menu case, retaining the successful guards.
  headV : ∀ {s x t} → step k l d s ─[ ev (evl x) ]─► t → HeadV s x t
  headV {s} (sVis {at = _ , apiBFev l′ d′ sendBFRequestRange} {a = r} refl br)
    with l′ ≟ l | d′ ≟ d | occupancy s <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV s _) (just-injective br) (hReq r lt)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  headV {pending [] waiting zero} (sVis {at = _ , apiBFev l′ d′ sendBFClientDone} refl br)
    with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hDone refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending [] waiting (suc c)} (sVis {at = _ , apiBFev _ _ sendBFClientDone} refl ())
  headV {pending [] streaming c} (sVis {at = _ , apiBFev _ _ sendBFClientDone} refl ())
  headV {pending (r ∷ rs) ph c} (sVis {at = _ , apiBFev _ _ sendBFClientDone} refl ())
  headV {pending (r ∷ rs) waiting c} (sVis {at = _ , receiveBF l′ d′}
    {a = _ , FromResponder , _ , blockFetch (MsgStartBatch)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hStart refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (r ∷ rs) waiting c} (sVis {at = _ , receiveBF l′ d′}
    {a = _ , FromResponder , _ , blockFetch (MsgNoBlocks)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hNone refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (r ∷ rs) streaming c} (sVis {at = _ , receiveBF l′ d′}
    {a = _ , FromResponder , _ , blockFetch (MsgBlock b)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBlock b refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (r ∷ rs) streaming c} (sVis {at = _ , receiveBF l′ d′}
    {a = _ , FromResponder , _ , blockFetch (MsgBatchDone)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hEnd refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending [] ph c} (sVis {at = _ , receiveBF _ _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromInitiator , _ , _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , keepAlive _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , chainSync _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , txSubmission _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , leiosNotify _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , leiosFetch _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , leiosNotifyP _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , leiosFetchP _} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , blockFetch (MsgRequestRange _)} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , blockFetch (MsgClientDone)} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , blockFetch (MsgBlock _)} refl ())
  headV {pending (_ ∷ _) waiting c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , blockFetch (MsgBatchDone)} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromInitiator , _ , _} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , keepAlive _} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , chainSync _} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , txSubmission _} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , leiosNotify _} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , leiosFetch _} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , leiosNotifyP _} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , leiosFetchP _} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , blockFetch (MsgRequestRange _)} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , blockFetch (MsgClientDone)} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , blockFetch (MsgStartBatch)} refl ())
  headV {pending (_ ∷ _) streaming c} (sVis {at = _ , receiveBF _ _} {a = _ , FromResponder , _ , blockFetch (MsgNoBlocks)} refl ())
  headV (sVis {at = _ , apiBFev _ _ sendBFStartBatch} refl ())
  headV (sVis {at = _ , apiBFev _ _ sendBFNoBlocks} refl ())
  headV (sVis {at = _ , apiBFev _ _ sendBFBlock} refl ())
  headV (sVis {at = _ , apiBFev _ _ sendBFBatchDone} refl ())
  headV (sVis {at = _ , apiBFev _ _ recvBFBlock} refl ())
  headV (sVis {at = _ , apiBFev _ _ reqBFRange} refl ())
  headV (sVis {at = _ , sendBF _ _} refl ())
  headV (sVis {at = _ , doneBF _ _} refl ())

  -- Lift head inversion through the iteration wrapper.
  head-inv : ∀ {s x M} → It (step k l d s) ─[ ev (evl x) ]─► M →
    Σ[ t ∈ Body ] (HeadV s x t × M ≡ It t)
  head-inv {s} st with iter-ev-elim (step k l d s) (step k l d) st
  ... | t , st′ , refl = t , headV st′ , refl

  -- Output residuals expose exactly their selected value.
  out-inv : ∀ {B} {dd : DecEq B} {ch : BFEv B} {v a x M} →
    It (Output ⦃ dd ⦄ ch v (Ret a)) ─[ ev (evl x) ]─► M →
    x ≡ evLabel B ch v × M ≡ It (Ret a)
  out-inv {dd = dd} {ch} {v} {a} st
    with iter-ev-elim (Output ⦃ dd ⦄ ch v (Ret a)) (step k l d) st
  ... | _ , st′ , refl with out-ev ⦃ dd ⦄ st′
  ... | refl , refl = refl , refl

  -- Return residuals cannot produce visible events.
  ret-noev : ∀ {a x M} → ¬ (It (Ret a) ─[ ev (evl x) ]─► M)
  ret-noev {a} st with iter-ev-elim (Ret a) (step k l d) st
  ... | _ , sVis () _ , _

  -- Output continuations are stable until their visible event fires.
  noτ : ∀ {t v M} → PTree.force t ≡ react v ∅t → ¬ (It t ─[ τ ]─► M)
  noτ {t} eq st with iter-τ-elim t (step k l d) st
  ... | itτ _ (sSil eq′) _ = case trans (sym eq) eq′ of λ ()
  ... | itBack _ eq′ _ = case trans (sym eq) eq′ of λ ()
  ... | itτ _ (sTau eq′ br) _ with trans (sym eq) eq′
  ... | refl = case br of λ ()

  -- A returned next state silently re-enters its loop head.
  back-inv : ∀ {s M} → It (Ret (inj₁ s)) ─[ τ ]─► M → M ≡ It (step k l d s)
  back-inv {s} st with iter-τ-elim (Ret (inj₁ s)) (step k l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ refl refl = refl

  -- A final return has no silent successor.
  end-noτ : ∀ {u M} → ¬ (It (Ret (inj₂ u)) ─[ τ ]─► M)
  end-noτ {u} st with iter-τ-elim (Ret (inj₂ u)) (step k l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ () _

  -- The only silent head transition collects one completed receiver result.
  collect-inv : ∀ {rs ph c M} → It (step k l d (pending rs ph c)) ─[ τ ]─► M →
    Σ[ c′ ∈ ℕ ] (c ≡ suc c′ × M ≡ It (Ret (inj₁ (pending rs ph c′))))
  collect-inv {rs} {ph} {c} st with iter-τ-elim (step k l d (pending rs ph c)) (step k l d) st
  ... | itBack _ () _
  ... | itτ _ (sSil ()) _
  collect-inv {rs} {ph} {zero} st | itτ _ (sTau refl ()) _
  collect-inv {rs} {ph} {suc c} st | itτ _ (sTau refl br) refl
    with refl ← just-injective br = c , refl , refl

  -- Lift a visible round transition through iteration.
  fire : ∀ {t t′ x} → t ─[ ev (evl x) ]─► t′ → It t ─[ ev (evl x) ]─► It t′
  fire {t} = iter-bind-ev (step k l d) t

  -- The loop-back is a single silent step.
  back : ∀ {s} → It (Ret (inj₁ s)) ─[ τ ]─► It (step k l d s)
  back = sSil refl

  -- Collection is available at every head with a completed result.
  collect-fire : ∀ {rs ph c} → It (step k l d (pending rs ph (suc c))) ─[ τ ]─►
    It (Ret (inj₁ (pending rs ph c)))
  collect-fire {rs} {ph} {c} = iter-bind-τ (step k l d) _
    (sTau {i = _ , base (sendBF l d)} {a = time₀ , FromInitiator , length₀ , blockFetch MsgClientDone} refl refl)

  -- Request admission holds whenever the original occupancy guard is true.
  fire-req : ∀ {s} r → occupancy s < k → step k l d s ─[ ev (evl (apiE sendBFRequestRange r)) ]─►
    send l d (MsgRequestRange r) (inj₁ (pending (ranges s ∷ʳ r) (phase s) (completed s)))
  fire-req {s} r lt = sVis refl br
    where
    -- Discharge link/direction reflexivity and the supplied bound.
    br : menu k l d s (_ , apiBFev l d sendBFRequestRange) r ≡ just (send l d (MsgRequestRange r) (inj₁ (pending (ranges s ∷ʳ r) (phase s) (completed s))))
    br with l ≟ l | d ≟ d | occupancy s <? k
    ... | yes refl | yes refl | yes _ = refl
    ... | no bad | _ | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | yes refl | no bad = ⊥-elim (bad lt)

  -- Fire the done branch at the selected endpoint.
  fire-done : ∀ {u} → step k l d (initial) ─[ ev (evl (apiE sendBFClientDone u)) ]─► (send l d MsgClientDone (inj₂ _))
  fire-done {u} = sVis refl br
    where
    -- Both endpoint equality decisions are reflexive.
    br : menu k l d (initial) (_ , apiBFev l d sendBFClientDone) u ≡ just (send l d MsgClientDone (inj₂ _))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Fire the start branch at the selected endpoint.
  fire-start : ∀ {r rs c} → step k l d (pending (r ∷ rs) waiting c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch))) ]─► (Ret (inj₁ (pending (r ∷ rs) streaming c)))
  fire-start {r} {rs} {c} = sVis refl br
    where
    -- Both endpoint equality decisions are reflexive.
    br : menu k l d (pending (r ∷ rs) waiting c) (_ , receiveBF l d) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (Ret (inj₁ (pending (r ∷ rs) streaming c)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Fire the none branch at the selected endpoint.
  fire-none : ∀ {r rs c} → step k l d (pending (r ∷ rs) waiting c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks))) ]─► (Ret (inj₁ (pending rs waiting (suc c))))
  fire-none {r} {rs} {c} = sVis refl br
    where
    -- Both endpoint equality decisions are reflexive.
    br : menu k l d (pending (r ∷ rs) waiting c) (_ , receiveBF l d) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (Ret (inj₁ (pending rs waiting (suc c))))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Fire the block branch at the selected endpoint.
  fire-block : ∀ {r rs c} b → step k l d (pending (r ∷ rs) streaming c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)))) ]─► (deliver b (pending (r ∷ rs) streaming c))
  fire-block {r} {rs} {c} b = sVis refl br
    where
    -- Both endpoint equality decisions are reflexive.
    br : menu k l d (pending (r ∷ rs) streaming c) (_ , receiveBF l d) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (deliver b (pending (r ∷ rs) streaming c))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Fire the end branch at the selected endpoint.
  fire-end : ∀ {r rs c} → step k l d (pending (r ∷ rs) streaming c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone))) ]─► (Ret (inj₁ (pending rs waiting (suc c))))
  fire-end {r} {rs} {c} = sVis refl br
    where
    -- Both endpoint equality decisions are reflexive.
    br : menu k l d (pending (r ∷ rs) streaming c) (_ , receiveBF l d) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (Ret (inj₁ (pending rs waiting (suc c))))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

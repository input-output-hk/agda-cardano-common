{-# OPTIONS --guardedness #-}

-- Structural inversion and forward steps for the existing pipelined PTree.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.ChainSyncClientParts (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _<_; _+_)
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
open import Cardano_network.ChainSync p
  using (CSEv; sendCS; receiveCS; apiCSev; doneCS; CSEv-≟; Rr; DecEq-Header×Tip; DecEq-Point×Tip)
open import Cardano_network.ChainSyncPipe p
open import CSP.Operators CSEv-≟ using (Ret; Output; ∅t; iter-bind)
open import Semantics.LTS {E = CSEv} {I = ExtI CSEv}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil; sTau)
open import CSP.Laws.DivFree.Loop CSEv-≟ using (iter-τ-elim; iter-ev-elim; itτ; itBack)
open import CSP.Laws.Bisim.IterCong CSEv-≟ using (iter-bind-ev; iter-bind-τ)
open import Cardano_network.Replay.LeiosFetchServerParts using (module OutInv)
open OutInv CSEv-≟ using (out-ev)

-- The pipelined client's process carrier.
Proc : Set₁
Proc = PTree CSEv (ExtI CSEv) Rr

module _ (k : ℕ) (l : Link) (d : Dir) where
  -- Keep the original iteration body around a residual round.
  It : Body → Proc
  It t = iter-bind t (step k l d)

  -- Application observation at this endpoint.
  apiE : (m : ApiCSTag) → ApiCSCar m → Event
  apiE m v = evLabel _ (apiCSev l d m) v

  -- Wire reception at this endpoint.
  rcvE : Payload → Event
  rcvE a = evLabel _ (receiveCS l d) a

  -- Preserve the concrete application handoff for each response.
  forward : Header → Tip → State → Body
  forward h t s = Output ⦃ DecEq-Header×Tip ⦄ (apiCSev l d recvCSRollforward) (h , t) (Ret (inj₁ s))

  -- Rollback returns its point and tip to the application.
  backward : Point → Tip → State → Body
  backward pt t s = Output ⦃ DecEq-Point×Tip ⦄ (apiCSev l d recvCSRollback) (pt , t) (Ret (inj₁ s))

  -- Intersection success hands over its selected point.
  found : Point → Tip → Body
  found pt t = Output ⦃ DecEq-Point×Tip ⦄ (apiCSev l d recvCSIntersectFound) (pt , t) (Ret (inj₁ initial))

  -- Intersection failure hands over the tip alone.
  notFound : Tip → Body
  notFound t = Output (apiCSev l d recvCSIntersectNotFound) t (Ret (inj₁ initial))

  -- Exact successful offers, including the original occupancy guard.
  data HeadV (s : State) : Event → Body → Set₁ where
    hReq : ∀ {n ph c u} → s ≡ pending n ph c → n + c < k → HeadV s (apiE sendCSRequestNext u) (send l d MsgCSRequestNext (inj₁ (pending (suc n) ph c)))
    hFind : ∀ pts → s ≡ pending zero canAwait zero → HeadV s (apiE sendCSFindIntersect pts) (send l d (MsgCSFindIntersect pts) (inj₁ intersect))
    hDone : ∀ {u} → s ≡ pending zero canAwait zero → HeadV s (apiE sendCSDone u) (send l d MsgCSDone (inj₂ _))
    hAwait : ∀ {n c tm ln} → s ≡ pending (suc n) canAwait c → HeadV s (rcvE (tm , FromResponder , ln , chainSync (MsgCSAwaitReply))) (Ret (inj₁ (pending (suc n) mustReply c)))
    hFound : ∀ {tm ln} pt t → s ≡ intersect → HeadV s (rcvE (tm , FromResponder , ln , chainSync (MsgCSIntersectFound pt t))) (found pt t)
    hNotFound : ∀ {tm ln} t → s ≡ intersect → HeadV s (rcvE (tm , FromResponder , ln , chainSync (MsgCSIntersectNotFound t))) (notFound t)
    hForwardCan : ∀ {n c tm ln} h t → s ≡ pending (suc n) canAwait c → HeadV s (rcvE (tm , FromResponder , ln , chainSync (MsgCSRollForward h t))) (forward h t (pending n canAwait (suc c)))
    hForwardMust : ∀ {n c tm ln} h t → s ≡ pending (suc n) mustReply c → HeadV s (rcvE (tm , FromResponder , ln , chainSync (MsgCSRollForward h t))) (forward h t (pending n canAwait (suc c)))
    hBackwardCan : ∀ {n c tm ln} pt t → s ≡ pending (suc n) canAwait c → HeadV s (rcvE (tm , FromResponder , ln , chainSync (MsgCSRollBackward pt t))) (backward pt t (pending n canAwait (suc c)))
    hBackwardMust : ∀ {n c tm ln} pt t → s ≡ pending (suc n) mustReply c → HeadV s (rcvE (tm , FromResponder , ln , chainSync (MsgCSRollBackward pt t))) (backward pt t (pending n canAwait (suc c)))

  -- Invert the actual menu, retaining endpoint and guard evidence.
  headV : ∀ {s x t} → step k l d s ─[ ev (evl x) ]─► t → HeadV s x t
  headV {pending n ph c} (sVis {at = _ , apiCSev l′ d′ sendCSRequestNext} {a = u} refl br) with l′ ≟ l | d′ ≟ d | (n + c) <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV _ _) (just-injective br) (hReq  refl lt)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  headV {pending zero canAwait zero} (sVis {at = _ , apiCSev l′ d′ sendCSFindIntersect} {a = pts} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hFind pts refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending zero canAwait zero} (sVis {at = _ , apiCSev l′ d′ sendCSDone} {a = u} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hDone  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS l′ d′ } {a = _ , FromResponder , _ , chainSync (MsgCSAwaitReply)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hAwait  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {intersect} (sVis {at = _ , receiveCS l′ d′ } {a = _ , FromResponder , _ , chainSync (MsgCSIntersectFound pt t)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hFound pt t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {intersect} (sVis {at = _ , receiveCS l′ d′ } {a = _ , FromResponder , _ , chainSync (MsgCSIntersectNotFound t)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hNotFound t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS l′ d′ } {a = _ , FromResponder , _ , chainSync (MsgCSRollForward h t)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hForwardCan h t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS l′ d′ } {a = _ , FromResponder , _ , chainSync (MsgCSRollForward h t)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hForwardMust h t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS l′ d′ } {a = _ , FromResponder , _ , chainSync (MsgCSRollBackward pt t)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBackwardCan pt t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS l′ d′ } {a = _ , FromResponder , _ , chainSync (MsgCSRollBackward pt t)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBackwardMust pt t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {intersect} (sVis {at = _ , apiCSev _ _ sendCSRequestNext} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
  headV {pending zero canAwait (suc c)} (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
  headV {pending zero mustReply c} (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
  headV {pending (suc n) ph c} (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
  headV {pending zero canAwait (suc c)} (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
  headV {pending zero mustReply c} (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
  headV {pending (suc n) ph c} (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ sendCSRollForward} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ sendCSRollForward} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ sendCSRollBackward} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ sendCSRollBackward} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ sendCSAwaitReply} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ sendCSAwaitReply} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ sendCSIntersectFound} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ sendCSIntersectFound} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ sendCSIntersectNotFound} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ sendCSIntersectNotFound} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
  headV {pending n ph c} (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
  headV {intersect} (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
  headV {pending n ph c} (sVis {at = _ , sendCS _ _} refl ())
  headV {intersect} (sVis {at = _ , sendCS _ _} refl ())
  headV {pending n ph c} (sVis {at = _ , doneCS _ _} refl ())
  headV {intersect} (sVis {at = _ , doneCS _ _} refl ())
  headV {pending zero ph c} (sVis {at = _ , receiveCS _ _} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromInitiator , _ , _} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSRequestNext)} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSFindIntersect _)} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSIntersectFound _ _)} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSIntersectNotFound _)} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSDone)} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , keepAlive _} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , blockFetch _} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , txSubmission _} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosNotify _} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosFetch _} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosNotifyP _} refl ())
  headV {pending (suc n) canAwait c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosFetchP _} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromInitiator , _ , _} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSRequestNext)} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSAwaitReply)} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSFindIntersect _)} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSIntersectFound _ _)} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSIntersectNotFound _)} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSDone)} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , keepAlive _} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , blockFetch _} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , txSubmission _} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosNotify _} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosFetch _} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosNotifyP _} refl ())
  headV {pending (suc n) mustReply c} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosFetchP _} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromInitiator , _ , _} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSRequestNext)} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSAwaitReply)} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSRollForward _ _)} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSRollBackward _ _)} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSFindIntersect _)} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , chainSync (MsgCSDone)} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , keepAlive _} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , blockFetch _} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , txSubmission _} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosNotify _} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosFetch _} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosNotifyP _} refl ())
  headV {intersect} (sVis {at = _ , receiveCS _ _} {a = _ , FromResponder , _ , leiosFetchP _} refl ())

  -- Lift head inversion through the iteration wrapper.
  head-inv : ∀ {s x M} → It (step k l d s) ─[ ev (evl x) ]─► M →
    Σ[ t ∈ Body ] (HeadV s x t × M ≡ It t)
  head-inv {s} st with iter-ev-elim (step k l d s) (step k l d) st
  ... | t , st′ , refl = t , headV st′ , refl

  -- Output residuals expose exactly their selected value.
  out-inv : ∀ {B} {dd : DecEq B} {ch : CSEv B} {v a x M} →
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
    (sTau {i = _ , base (sendCS l d)} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSDone} refl refl)

  -- Intersection has no completed result to collect.
  intersect-noτ : ∀ {M} → ¬ (It (step k l d intersect) ─[ τ ]─► M)
  intersect-noτ = noτ refl

  -- Construct the Req branch at this endpoint.
  fire-Req : ∀ {n ph c u} → n + c < k → step k l d (pending n ph c) ─[ ev (evl (apiE sendCSRequestNext u)) ]─► (send l d MsgCSRequestNext (inj₁ (pending (suc n) ph c)))
  fire-Req {n} {ph} {c} {u}  lt = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (pending n ph c) (_ , apiCSev l d sendCSRequestNext) (u) ≡ just (send l d MsgCSRequestNext (inj₁ (pending (suc n) ph c)))
    br with l ≟ l | d ≟ d | (n + c) <? k
    ... | yes refl | yes refl | yes _ = refl
    ... | no bad | _ | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | yes refl | no bad = ⊥-elim (bad lt)

  -- Construct the Find branch at this endpoint.
  fire-Find : ∀ pts → step k l d (pending zero canAwait zero) ─[ ev (evl (apiE sendCSFindIntersect pts)) ]─► (send l d (MsgCSFindIntersect pts) (inj₁ intersect))
  fire-Find pts = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (pending zero canAwait zero) (_ , apiCSev l d sendCSFindIntersect) (pts) ≡ just (send l d (MsgCSFindIntersect pts) (inj₁ intersect))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Done branch at this endpoint.
  fire-Done : ∀ {u} → step k l d (pending zero canAwait zero) ─[ ev (evl (apiE sendCSDone u)) ]─► (send l d MsgCSDone (inj₂ _))
  fire-Done {u}  = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (pending zero canAwait zero) (_ , apiCSev l d sendCSDone) (u) ≡ just (send l d MsgCSDone (inj₂ _))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Await branch at this endpoint.
  fire-Await : ∀ {n c} → step k l d (pending (suc n) canAwait c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , chainSync (MsgCSAwaitReply)))) ]─► (Ret (inj₁ (pending (suc n) mustReply c)))
  fire-Await {n} {c}  = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (pending (suc n) canAwait c) (_ , receiveCS l d ) (time₀ , FromResponder , length₀ , chainSync (MsgCSAwaitReply)) ≡ just (Ret (inj₁ (pending (suc n) mustReply c)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Found branch at this endpoint.
  fire-Found : ∀ pt t → step k l d (intersect) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt t)))) ]─► (found pt t)
  fire-Found pt t = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (intersect) (_ , receiveCS l d ) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt t)) ≡ just (found pt t)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the NotFound branch at this endpoint.
  fire-NotFound : ∀ t → step k l d (intersect) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound t)))) ]─► (notFound t)
  fire-NotFound t = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (intersect) (_ , receiveCS l d ) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound t)) ≡ just (notFound t)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the ForwardCan branch at this endpoint.
  fire-ForwardCan : ∀ {n c} h t → step k l d (pending (suc n) canAwait c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)))) ]─► (forward h t (pending n canAwait (suc c)))
  fire-ForwardCan {n} {c} h t = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (pending (suc n) canAwait c) (_ , receiveCS l d ) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (forward h t (pending n canAwait (suc c)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the ForwardMust branch at this endpoint.
  fire-ForwardMust : ∀ {n c} h t → step k l d (pending (suc n) mustReply c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)))) ]─► (forward h t (pending n canAwait (suc c)))
  fire-ForwardMust {n} {c} h t = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (pending (suc n) mustReply c) (_ , receiveCS l d ) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (forward h t (pending n canAwait (suc c)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the BackwardCan branch at this endpoint.
  fire-BackwardCan : ∀ {n c} pt t → step k l d (pending (suc n) canAwait c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt t)))) ]─► (backward pt t (pending n canAwait (suc c)))
  fire-BackwardCan {n} {c} pt t = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (pending (suc n) canAwait c) (_ , receiveCS l d ) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt t)) ≡ just (backward pt t (pending n canAwait (suc c)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the BackwardMust branch at this endpoint.
  fire-BackwardMust : ∀ {n c} pt t → step k l d (pending (suc n) mustReply c) ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt t)))) ]─► (backward pt t (pending n canAwait (suc c)))
  fire-BackwardMust {n} {c} pt t = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this offer.
    br : menu k l d (pending (suc n) mustReply c) (_ , receiveCS l d ) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt t)) ≡ just (backward pt t (pending n canAwait (suc c)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

{-# OPTIONS --guardedness #-}

-- Bidirectional wire-control correspondence with the existing sequential server.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.ChainSyncServerBridge (p : Params) where

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (map-id)
open import Data.List.Relation.Unary.All using (universal)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (id; case_of_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)
open import Process_Trees using (PTree; ExtI; react; ret; sil; AnyTypes; ContinueType)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p
open Params p
open import Cardano_network.ChainSync p
  using (CSEv; sendCS; receiveCS; apiCSev; doneCS; CSEv-≟; Rr;
         CSState; stIdle; stCanAwait; stMustReply; stIntersect; stDone; serverStep; CSserverStClient; DecEq-ListPoint)
open import CSP.Operators CSEv-≟ using (Ret; Output; Prefix₀; ∅t; iter-bind)
open import CSP.Laws.DivFree.Loop CSEv-≟ using (iter-τ-elim; iter-ev-elim; itτ; itBack)
open import CSP.Laws.Bisim.IterCong CSEv-≟ using (iter-bind-ev)
open import CSP.Laws.Traces.PrefixInversion CSEv-≟ using (⟶₀-ev-inv)
open import Cardano_network.Replay.LeiosFetchServerParts using (module OutInv)
open OutInv CSEv-≟ using (out-ev)
open import Cardano_network.Replay.LeiosFetchServerForward using (module Fire)
open Fire CSEv-≟ using (out-fire; pfx-fire)
open import Semantics.LTS {E = CSEv} {I = ExtI CSEv}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil; sTau)
open import Semantics.Deadlock {E = CSEv} {I = ExtI CSEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = CSEv} {I = ExtI CSEv} as Br
open import Semantics.Replay using (Replay)
open import Data.Nat using (ℕ)
open import Cardano_network.Replay.ChainSyncSession


-- The existing server's loop-body carrier.
Body : Set₁
Body = PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)

-- The existing server's whole-process carrier.
Proc : Set₁
Proc = PTree CSEv (ExtI CSEv) Rr

-- Preserve all wire-control distinctions while erasing payloads.
kind : MessageChainSync → Kind
kind MsgCSRequestNext = requestNext
kind MsgCSAwaitReply = awaitReply
kind (MsgCSRollForward _ _) = rollForward
kind (MsgCSRollBackward _ _) = rollBackward
kind (MsgCSFindIntersect _) = findIntersect
kind (MsgCSIntersectFound _ _) = intersectFound
kind (MsgCSIntersectNotFound _) = intersectNotFound
kind MsgCSDone = doneK

-- Application and completion notifications are absent from the wire log.
cls : Event → Maybe E
cls (evLabel _ (sendCS _ _) (_ , _ , _ , chainSync m)) = just (Send , kind m)
cls (evLabel _ (receiveCS _ _) (_ , _ , _ , chainSync m)) = just (Recv , kind m)
cls _ = nothing

-- Compare projected finite traces without observing semantic termination.
Obs : List Event → List E → Set
Obs = Br.Obs cls id

-- The sequential producer has at most one unanswered request.
ctl : CSState → St
ctl stIdle = initial
ctl stCanAwait = pending 1 canAwait
ctl stMustReply = pending 1 mustReply
ctl stIntersect = intersect
ctl stDone = closed

module _ (k : ℕ) (l : Link) (d : Dir) where
  open Spec k server

  -- Retain the original server iteration and its actual residual bodies.
  It : Body → Proc
  It t = iter-bind t (serverStep l d)

  -- The original producer's wire output.
  send : MessageChainSync → CSState → Body
  send m a = Output (sendCS l d) (time₀ , FromResponder , length₀ , chainSync m) (Ret (inj₁ a))

  -- A request is handed to the producer application before responding.
  requestAPI : Body
  requestAPI = Prefix₀ (apiCSev l d reqCSRequestNext) (Ret (inj₁ stCanAwait))

  -- Intersection points are handed to the producer unchanged.
  intersectAPI : List Point → Body
  intersectAPI pts = Output ⦃ DecEq-ListPoint ⦄ (apiCSev l d reqCSFindIntersect) pts (Ret (inj₁ stIntersect))

  -- Completion notification precedes the final loop iteration.
  notice : Body
  notice = Prefix₀ (doneCS l d) (Ret (inj₁ stDone))

  -- A local application event.
  apiE : (tag : ApiCSTag) → ApiCSCar tag → Event
  apiE tag v = evLabel _ (apiCSev l d tag) v

  -- A local received payload.
  rcvE : Payload → Event
  rcvE v = evLabel _ (receiveCS l d) v

  -- Exhaustive successful branches of the existing server.
  data HeadV (a : CSState) : Event → Body → Set₁ where
    hReq : ∀ {tm md ln}  → a ≡ stIdle → HeadV a (rcvE (tm , md , ln , chainSync MsgCSRequestNext)) requestAPI
    hFind : ∀ {tm md ln} pts → a ≡ stIdle → HeadV a (rcvE (tm , md , ln , chainSync (MsgCSFindIntersect pts))) (intersectAPI pts)
    hDone : ∀ {tm md ln}  → a ≡ stIdle → HeadV a (rcvE (tm , md , ln , chainSync MsgCSDone)) notice
    hForwardstCanAwait : ∀ h t → a ≡ stCanAwait → HeadV a (apiE sendCSRollForward (h , t)) (send (MsgCSRollForward h t) stIdle)
    hBackwardstCanAwait : ∀ pt t → a ≡ stCanAwait → HeadV a (apiE sendCSRollBackward (pt , t)) (send (MsgCSRollBackward pt t) stIdle)
    hForwardstMustReply : ∀ h t → a ≡ stMustReply → HeadV a (apiE sendCSRollForward (h , t)) (send (MsgCSRollForward h t) stIdle)
    hBackwardstMustReply : ∀ pt t → a ≡ stMustReply → HeadV a (apiE sendCSRollBackward (pt , t)) (send (MsgCSRollBackward pt t) stIdle)
    hAwait : ∀ {u} → a ≡ stCanAwait → HeadV a (apiE sendCSAwaitReply (u)) (send MsgCSAwaitReply stMustReply)
    hFound : ∀ pt t → a ≡ stIntersect → HeadV a (apiE sendCSIntersectFound (pt , t)) (send (MsgCSIntersectFound pt t) stIdle)
    hNotFound : ∀ t → a ≡ stIntersect → HeadV a (apiE sendCSIntersectNotFound (t)) (send (MsgCSIntersectNotFound t) stIdle)

  -- Invert menu decisions without abstracting away disabled offers.
  headV : ∀ {a x t} → serverStep l d a ─[ ev (evl x) ]─► t → HeadV a x t
  headV {stIdle} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync MsgCSRequestNext} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hReq  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIdle} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync (MsgCSFindIntersect pts)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hFind pts refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIdle} (sVis {at = _ , receiveCS l′ d′} {a = _ , _ , _ , chainSync MsgCSDone} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hDone  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stCanAwait} (sVis {at = _ , apiCSev l′ d′ sendCSRollForward} {a = h , t} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hForwardstCanAwait h t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stCanAwait} (sVis {at = _ , apiCSev l′ d′ sendCSRollBackward} {a = pt , t} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBackwardstCanAwait pt t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stMustReply} (sVis {at = _ , apiCSev l′ d′ sendCSRollForward} {a = h , t} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hForwardstMustReply h t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stMustReply} (sVis {at = _ , apiCSev l′ d′ sendCSRollBackward} {a = pt , t} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBackwardstMustReply pt t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stCanAwait} (sVis {at = _ , apiCSev l′ d′ sendCSAwaitReply} {a = u} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hAwait  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIntersect} (sVis {at = _ , apiCSev l′ d′ sendCSIntersectFound} {a = pt , t} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hFound pt t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIntersect} (sVis {at = _ , apiCSev l′ d′ sendCSIntersectNotFound} {a = t} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hNotFound t refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIdle} (sVis {at = _ , apiCSev _ _ sendCSRequestNext} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ sendCSRollForward} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ sendCSRollBackward} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ sendCSAwaitReply} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ sendCSIntersectFound} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ sendCSIntersectNotFound} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
  headV {stIdle} (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
  headV {stIdle} (sVis {at = _ , sendCS _ _} refl ())
  headV {stIdle} (sVis {at = _ , doneCS _ _} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ sendCSRequestNext} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ sendCSIntersectFound} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ sendCSIntersectNotFound} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
  headV {stCanAwait} (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
  headV {stCanAwait} (sVis {at = _ , sendCS _ _} refl ())
  headV {stCanAwait} (sVis {at = _ , doneCS _ _} refl ())
  headV {stCanAwait} (sVis {at = _ , receiveCS _ _} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ sendCSRequestNext} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ sendCSAwaitReply} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ sendCSIntersectFound} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ sendCSIntersectNotFound} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
  headV {stMustReply} (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
  headV {stMustReply} (sVis {at = _ , sendCS _ _} refl ())
  headV {stMustReply} (sVis {at = _ , doneCS _ _} refl ())
  headV {stMustReply} (sVis {at = _ , receiveCS _ _} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ sendCSRequestNext} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ sendCSFindIntersect} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ sendCSDone} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ recvCSRollforward} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ recvCSRollback} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ recvCSIntersectFound} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ recvCSIntersectNotFound} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ sendCSRollForward} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ sendCSRollBackward} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ sendCSAwaitReply} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ reqCSRequestNext} refl ())
  headV {stIntersect} (sVis {at = _ , apiCSev _ _ reqCSFindIntersect} refl ())
  headV {stIntersect} (sVis {at = _ , sendCS _ _} refl ())
  headV {stIntersect} (sVis {at = _ , doneCS _ _} refl ())
  headV {stIntersect} (sVis {at = _ , receiveCS _ _} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSAwaitReply)} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , keepAlive _} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , blockFetch _} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , txSubmission _} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
  headV {stIdle} (sVis {at = _ , receiveCS _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
  headV {stDone} (sVis () _)

  -- Lift a visible transition through the original iteration wrapper.
  fire : ∀ {t t′ x} → t ─[ ev (evl x) ]─► t′ → It t ─[ ev (evl x) ]─► It t′
  fire {t} = iter-bind-ev (serverStep l d) t

  -- Loop-back is the existing iter silent step.
  back : ∀ {a} → It (Ret (inj₁ a)) ─[ τ ]─► It (serverStep l d a)
  back = sSil refl

  -- Output and live menu residuals have no silent moves.
  noτ : ∀ {t v M} → PTree.force t ≡ react v ∅t → ¬ (It t ─[ τ ]─► M)
  noτ {t} eq st with iter-τ-elim t (serverStep l d) st
  ... | itτ _ (sSil eq′) _ = case trans (sym eq) eq′ of λ ()
  ... | itBack _ eq′ _ = case trans (sym eq) eq′ of λ ()
  ... | itτ _ (sTau eq′ br) _ with trans (sym eq) eq′
  ... | refl = case br of λ ()

  -- Finished server residuals have no silent successor.
  end-noτ : ∀ {u M} → ¬ (It (Ret (inj₂ u)) ─[ τ ]─► M)
  end-noτ {u} st with iter-τ-elim (Ret (inj₂ u)) (serverStep l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ () _

  -- A return residual exposes no wire or application event.
  ret-noev : ∀ {a x M} → ¬ (It (Ret a) ─[ ev (evl x) ]─► M)
  ret-noev {a} st with iter-ev-elim (Ret a) (serverStep l d) st
  ... | _ , sVis () _ , _

  -- The only silent loop-back resumes the corresponding server state.
  back-inv : ∀ {a M} → It (Ret (inj₁ a)) ─[ τ ]─► M → M ≡ It (serverStep l d a)
  back-inv {a} st with iter-τ-elim (Ret (inj₁ a)) (serverStep l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ refl refl = refl

  -- Output inversion retains the precise emitted value and continuation.
  out-inv : ∀ {B} {dd : DecEq B} {ch : CSEv B} {v a x M} →
    It (Output ⦃ dd ⦄ ch v (Ret a)) ─[ ev (evl x) ]─► M →
    x ≡ evLabel B ch v × M ≡ It (Ret a)
  out-inv {dd = dd} {ch} {v} {a} st with iter-ev-elim (Output ⦃ dd ⦄ ch v (Ret a)) (serverStep l d) st
  ... | _ , st′ , refl with out-ev ⦃ dd ⦄ st′
  ... | refl , refl = refl , refl

  -- Relate heads and all intermediate application/wire residuals.
  data Rel : Proc → St → Set₁ where
    head : ∀ {a} → Rel (It (serverStep l d a)) (ctl a)
    loopBack : ∀ {a} → Rel (It (Ret (inj₁ a))) (ctl a)
    sending : ∀ {m a s} → Step s (Send , kind m) (ctl a) → Rel (It (send m a)) s
    requesting : Rel (It requestAPI) (pending 1 canAwait)
    finding : ∀ pts → Rel (It (intersectAPI pts)) intersect
    doneNotice : Rel (It notice) closed

  -- Loop-back is silent at the wire-control abstraction.
  sim-τ : ∀ {T T′ s} → Rel T s → T ─[ τ ]─► T′ →
    Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel T′ s′)
  sim-τ (head {stIdle}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stCanAwait}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stMustReply}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stIntersect}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stDone}) st = ⊥-elim (end-noτ st)
  sim-τ loopBack st with back-inv st
  ... | refl = _ , done , head
  sim-τ (sending _) st = ⊥-elim (noτ refl st)
  sim-τ requesting st = ⊥-elim (noτ refl st)
  sim-τ (finding _) st = ⊥-elim (noτ refl st)
  sim-τ doneNotice st = ⊥-elim (noτ refl st)

  -- Match observed wire steps and erase application-only events.
  sim-ev : ∀ {T T′ s e} → Rel T s → T ─[ ev (evl e) ]─► T′ →
    Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (Obs (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel T′ s′)
  sim-ev (head {a}) st with iter-ev-elim (serverStep l d a) (serverStep l d) st
  ... | _ , st′ , refl with headV {a = a} st′
  ... | hReq  refl = (Recv , requestNext) ∷ [] , _ , refl , vis refl done , requesting
  ... | hFind pts refl = (Recv , findIntersect) ∷ [] , _ , refl , vis refl done , finding pts
  ... | hDone  refl = (Recv , doneK) ∷ [] , _ , refl , vis refl done , doneNotice
  ... | hForwardstCanAwait h t refl = [] , _ , refl , done , sending refl
  ... | hBackwardstCanAwait pt t refl = [] , _ , refl , done , sending refl
  ... | hForwardstMustReply h t refl = [] , _ , refl , done , sending refl
  ... | hBackwardstMustReply pt t refl = [] , _ , refl , done , sending refl
  ... | hAwait  refl = [] , _ , refl , done , sending refl
  ... | hFound pt t refl = [] , _ , refl , done , sending refl
  ... | hNotFound t refl = [] , _ , refl , done , sending refl
  sim-ev loopBack st = ⊥-elim (ret-noev st)
  sim-ev (sending {m} pr) st with out-inv st
  ... | refl , refl = (Send , kind m) ∷ [] , _ , refl , vis pr done , loopBack
  sim-ev (finding pts) st with out-inv st
  ... | refl , refl = [] , _ , refl , done , loopBack
  sim-ev requesting st with iter-ev-elim requestAPI (serverStep l d) st
  ... | _ , st′ , refl with ⟶₀-ev-inv st′
  ... | _ , refl , refl = [] , _ , refl , done , loopBack
  sim-ev doneNotice st with iter-ev-elim notice (serverStep l d) st
  ... | _ , st′ , refl with ⟶₀-ev-inv st′
  ... | _ , refl , refl = [] , _ , refl , done , loopBack

  -- Every concrete residual is simulated by the certified replay machine.
  simulation : Br.Sim model cls id Rel
  simulation = record { sim-τ = sim-τ ; sim-ev = sim-ev }

  -- Every observed original server trace belongs to the replay language.
  sound : ∀ {t M es} → CSserverStClient l d ⟹∖√⟨ t ⟩ M → Obs t es → HasTrace initial es
  sound {es = es} run o with Br.sound model cls id simulation (head {stIdle}) run
  ... | es′ , s′ , o′ , r , _ = s′ , subst (λ xs → initial ⇒⟨ xs ⟩ s′)
    (trans (sym (map-id es′)) (trans (sym o′) (trans o (map-id es)))) r

  -- Expose the original offer map for constructive transition witnesses.
  offers : CSState → (at : AnyTypes CSEv) → ContinueType at (Maybe Body)
  offers a with PTree.force (serverStep l d a)
  ... | react v _ = v
  ... | ret _ = λ _ _ → nothing
  ... | sil _ = λ _ _ → nothing

  -- Realise the Req offer at the selected endpoint.
  fire-Req : serverStep l d stIdle ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext))) ]─► requestAPI
  fire-Req  = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stIdle (_ , receiveCS l d) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just requestAPI
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the Find offer at the selected endpoint.
  fire-Find : ∀ pts → serverStep l d stIdle ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect pts)))) ]─► (intersectAPI pts)
  fire-Find pts = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stIdle (_ , receiveCS l d) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect pts)) ≡ just (intersectAPI pts)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the Done offer at the selected endpoint.
  fire-Done : serverStep l d stIdle ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , chainSync MsgCSDone))) ]─► notice
  fire-Done  = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stIdle (_ , receiveCS l d) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just notice
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the ForwardstCanAwait offer at the selected endpoint.
  fire-ForwardstCanAwait : ∀ h t → serverStep l d stCanAwait ─[ ev (evl (apiE sendCSRollForward (h , t))) ]─► (send (MsgCSRollForward h t) stIdle)
  fire-ForwardstCanAwait h t = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stCanAwait (_ , apiCSev l d sendCSRollForward) (h , t) ≡ just (send (MsgCSRollForward h t) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the BackwardstCanAwait offer at the selected endpoint.
  fire-BackwardstCanAwait : ∀ pt t → serverStep l d stCanAwait ─[ ev (evl (apiE sendCSRollBackward (pt , t))) ]─► (send (MsgCSRollBackward pt t) stIdle)
  fire-BackwardstCanAwait pt t = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stCanAwait (_ , apiCSev l d sendCSRollBackward) (pt , t) ≡ just (send (MsgCSRollBackward pt t) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the ForwardstMustReply offer at the selected endpoint.
  fire-ForwardstMustReply : ∀ h t → serverStep l d stMustReply ─[ ev (evl (apiE sendCSRollForward (h , t))) ]─► (send (MsgCSRollForward h t) stIdle)
  fire-ForwardstMustReply h t = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stMustReply (_ , apiCSev l d sendCSRollForward) (h , t) ≡ just (send (MsgCSRollForward h t) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the BackwardstMustReply offer at the selected endpoint.
  fire-BackwardstMustReply : ∀ pt t → serverStep l d stMustReply ─[ ev (evl (apiE sendCSRollBackward (pt , t))) ]─► (send (MsgCSRollBackward pt t) stIdle)
  fire-BackwardstMustReply pt t = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stMustReply (_ , apiCSev l d sendCSRollBackward) (pt , t) ≡ just (send (MsgCSRollBackward pt t) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the Await offer at the selected endpoint.
  fire-Await : serverStep l d stCanAwait ─[ ev (evl (apiE sendCSAwaitReply (tt))) ]─► (send MsgCSAwaitReply stMustReply)
  fire-Await  = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stCanAwait (_ , apiCSev l d sendCSAwaitReply) (tt) ≡ just (send MsgCSAwaitReply stMustReply)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the Found offer at the selected endpoint.
  fire-Found : ∀ pt t → serverStep l d stIntersect ─[ ev (evl (apiE sendCSIntersectFound (pt , t))) ]─► (send (MsgCSIntersectFound pt t) stIdle)
  fire-Found pt t = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stIntersect (_ , apiCSev l d sendCSIntersectFound) (pt , t) ≡ just (send (MsgCSIntersectFound pt t) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Realise the NotFound offer at the selected endpoint.
  fire-NotFound : ∀ t → serverStep l d stIntersect ─[ ev (evl (apiE sendCSIntersectNotFound (t))) ]─► (send (MsgCSIntersectNotFound t) stIdle)
  fire-NotFound t = sVis refl br
    where
    -- Both endpoint comparisons hold reflexively.
    br : offers stIntersect (_ , apiCSev l d sendCSIntersectNotFound) (t) ≡ just (send (MsgCSIntersectNotFound t) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Completeness uses only reachable sequential control states.
  data RelC : Proc → St → Set₁ where
    cstIdle : RelC (It (serverStep l d stIdle)) (ctl stIdle)
    cstCanAwait : RelC (It (serverStep l d stCanAwait)) (ctl stCanAwait)
    cstMustReply : RelC (It (serverStep l d stMustReply)) (ctl stMustReply)
    cstIntersect : RelC (It (serverStep l d stIntersect)) (ctl stIntersect)
    cstDone : RelC (It (serverStep l d stDone)) (ctl stDone)

  -- One block supplies the erased point, header and tip payloads.
  module _ (b₀ : Block) where
    -- Replay has no silent transitions.
    co-τ : ∀ {T s s′} → RelC T s → Replay._-τ→_ model s s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t [] × RelC T′ s′)
    co-τ _ ()

    -- Each accepted transition has a concrete original PTree execution.
    co-ev : ∀ {T s s′ e} → RelC T s → ⊤ → Step s e s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
    co-ev {e = Send , requestNext} cstIdle _ ()
    co-ev {e = Send , awaitReply} cstIdle _ ()
    co-ev {e = Send , rollForward} cstIdle _ ()
    co-ev {e = Send , rollBackward} cstIdle _ ()
    co-ev {e = Send , findIntersect} cstIdle _ ()
    co-ev {e = Send , intersectFound} cstIdle _ ()
    co-ev {e = Send , intersectNotFound} cstIdle _ ()
    co-ev {e = Send , doneK} cstIdle _ ()
    co-ev {e = Recv , requestNext} cstIdle _ refl = _ , _ ,
      ∖√-ev (fire (fire-Req ))
      (∖√-ev (fire pfx-fire) (∖√-τ back ∖√-refl)) , refl , cstCanAwait
    co-ev {e = Recv , awaitReply} cstIdle _ ()
    co-ev {e = Recv , rollForward} cstIdle _ ()
    co-ev {e = Recv , rollBackward} cstIdle _ ()
    co-ev {e = Recv , findIntersect} cstIdle _ refl = _ , _ ,
      ∖√-ev (fire (fire-Find []))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIntersect
    co-ev {e = Recv , intersectFound} cstIdle _ ()
    co-ev {e = Recv , intersectNotFound} cstIdle _ ()
    co-ev {e = Recv , doneK} cstIdle _ refl = _ , _ ,
      ∖√-ev (fire (fire-Done ))
      (∖√-ev (fire pfx-fire) (∖√-τ back ∖√-refl)) , refl , cstDone
    co-ev {e = Send , requestNext} cstCanAwait _ ()
    co-ev {e = Send , awaitReply} cstCanAwait _ refl = _ , _ ,
      ∖√-ev (fire (fire-Await ))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstMustReply
    co-ev {e = Send , rollForward} cstCanAwait _ refl = _ , _ ,
      ∖√-ev (fire (fire-ForwardstCanAwait (header b₀) (tip b₀)))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , rollBackward} cstCanAwait _ refl = _ , _ ,
      ∖√-ev (fire (fire-BackwardstCanAwait (point b₀) (tip b₀)))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , findIntersect} cstCanAwait _ ()
    co-ev {e = Send , intersectFound} cstCanAwait _ ()
    co-ev {e = Send , intersectNotFound} cstCanAwait _ ()
    co-ev {e = Send , doneK} cstCanAwait _ ()
    co-ev {e = Recv , requestNext} cstCanAwait _ ()
    co-ev {e = Recv , awaitReply} cstCanAwait _ ()
    co-ev {e = Recv , rollForward} cstCanAwait _ ()
    co-ev {e = Recv , rollBackward} cstCanAwait _ ()
    co-ev {e = Recv , findIntersect} cstCanAwait _ ()
    co-ev {e = Recv , intersectFound} cstCanAwait _ ()
    co-ev {e = Recv , intersectNotFound} cstCanAwait _ ()
    co-ev {e = Recv , doneK} cstCanAwait _ ()
    co-ev {e = Send , requestNext} cstMustReply _ ()
    co-ev {e = Send , awaitReply} cstMustReply _ ()
    co-ev {e = Send , rollForward} cstMustReply _ refl = _ , _ ,
      ∖√-ev (fire (fire-ForwardstMustReply (header b₀) (tip b₀)))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , rollBackward} cstMustReply _ refl = _ , _ ,
      ∖√-ev (fire (fire-BackwardstMustReply (point b₀) (tip b₀)))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , findIntersect} cstMustReply _ ()
    co-ev {e = Send , intersectFound} cstMustReply _ ()
    co-ev {e = Send , intersectNotFound} cstMustReply _ ()
    co-ev {e = Send , doneK} cstMustReply _ ()
    co-ev {e = Recv , requestNext} cstMustReply _ ()
    co-ev {e = Recv , awaitReply} cstMustReply _ ()
    co-ev {e = Recv , rollForward} cstMustReply _ ()
    co-ev {e = Recv , rollBackward} cstMustReply _ ()
    co-ev {e = Recv , findIntersect} cstMustReply _ ()
    co-ev {e = Recv , intersectFound} cstMustReply _ ()
    co-ev {e = Recv , intersectNotFound} cstMustReply _ ()
    co-ev {e = Recv , doneK} cstMustReply _ ()
    co-ev {e = Send , requestNext} cstIntersect _ ()
    co-ev {e = Send , awaitReply} cstIntersect _ ()
    co-ev {e = Send , rollForward} cstIntersect _ ()
    co-ev {e = Send , rollBackward} cstIntersect _ ()
    co-ev {e = Send , findIntersect} cstIntersect _ ()
    co-ev {e = Send , intersectFound} cstIntersect _ refl = _ , _ ,
      ∖√-ev (fire (fire-Found (point b₀) (tip b₀)))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , intersectNotFound} cstIntersect _ refl = _ , _ ,
      ∖√-ev (fire (fire-NotFound (tip b₀)))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , doneK} cstIntersect _ ()
    co-ev {e = Recv , requestNext} cstIntersect _ ()
    co-ev {e = Recv , awaitReply} cstIntersect _ ()
    co-ev {e = Recv , rollForward} cstIntersect _ ()
    co-ev {e = Recv , rollBackward} cstIntersect _ ()
    co-ev {e = Recv , findIntersect} cstIntersect _ ()
    co-ev {e = Recv , intersectFound} cstIntersect _ ()
    co-ev {e = Recv , intersectNotFound} cstIntersect _ ()
    co-ev {e = Recv , doneK} cstIntersect _ ()
    co-ev {e = Send , requestNext} cstDone _ ()
    co-ev {e = Send , awaitReply} cstDone _ ()
    co-ev {e = Send , rollForward} cstDone _ ()
    co-ev {e = Send , rollBackward} cstDone _ ()
    co-ev {e = Send , findIntersect} cstDone _ ()
    co-ev {e = Send , intersectFound} cstDone _ ()
    co-ev {e = Send , intersectNotFound} cstDone _ ()
    co-ev {e = Send , doneK} cstDone _ ()
    co-ev {e = Recv , requestNext} cstDone _ ()
    co-ev {e = Recv , awaitReply} cstDone _ ()
    co-ev {e = Recv , rollForward} cstDone _ ()
    co-ev {e = Recv , rollBackward} cstDone _ ()
    co-ev {e = Recv , findIntersect} cstDone _ ()
    co-ev {e = Recv , intersectFound} cstDone _ ()
    co-ev {e = Recv , intersectNotFound} cstDone _ ()
    co-ev {e = Recv , doneK} cstDone _ ()

    -- The original peer realises all replay transitions.
    cosimulation : Br.CoSim model cls id RelC (λ _ → ⊤)
    cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

    -- Every accepted finite control trace has an original server run.
    complete : ∀ {es} → HasTrace initial es →
      ∃[ t ] ∃[ M ] (CSserverStClient l d ⟹∖√⟨ t ⟩ M × Obs t es)
    complete {es} (_ , r) with Br.complete model cls id cosimulation
      cstIdle (universal (λ _ → tt) es) r
    ... | M , t , run , o , _ = t , M , run , o

    -- Exact correspondence, for arbitrary parameters and endpoints.
    bridge : ∀ {es} → HasTrace initial es ⇔
      (∃[ t ] ∃[ M ] (CSserverStClient l d ⟹∖√⟨ t ⟩ M × Obs t es))
    bridge = mk⇔ complete (λ { (t , M , run , o) → sound run o })

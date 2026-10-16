{-# OPTIONS --guardedness #-}

-- Bidirectional wire-control correspondence with the strict sequential submitter.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.TxSubmission2ClientBridge (p : Params) where

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
open import Cardano_network.TxSubmission p
  using (TSEv; sendTS; receiveTS; apiTSev; doneTS; TSEv-≟; Rr;
         TSState; stInit; stIdle; stTxIdsBlocking; stTxIdsNonBlocking; stTxs; stDone; DecEq-ListTxHash; DecEq-BS×ℕ×ℕ)
import Cardano_network.TxSubmission2Pipe p as P
open P using (submitterStep)
open import CSP.Operators TSEv-≟ using (Ret; Output; Prefix₀; ∅t; iter-bind)
open import CSP.Laws.DivFree.Loop TSEv-≟ using (iter-τ-elim; iter-ev-elim; itτ; itBack)
open import CSP.Laws.Bisim.IterCong TSEv-≟ using (iter-bind-ev)
open import CSP.Laws.Traces.PrefixInversion TSEv-≟ using (⟶₀-ev-inv)
open import Cardano_network.Replay.LeiosFetchServerParts using (module OutInv)
open OutInv TSEv-≟ using (out-ev)
open import Cardano_network.Replay.LeiosFetchServerForward using (module Fire)
open Fire TSEv-≟ using (out-fire; pfx-fire)
open import Semantics.LTS {E = TSEv} {I = ExtI TSEv}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil; sTau)
open import Semantics.Deadlock {E = TSEv} {I = ExtI TSEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = TSEv} {I = ExtI TSEv} as Br
open import Semantics.Replay using (Replay)
open import Data.Nat using (ℕ)
open import Cardano_network.Replay.TxSubmission2Session


-- The strict submitter's loop-body carrier.
Body : Set₁
Body = PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)

-- The strict submitter's whole-process carrier.
Proc : Set₁
Proc = PTree TSEv (ExtI TSEv) Rr

-- Retain the blocking mode and empty/nonempty ID-reply distinction.
kind : MessageTxSubmission2 → Kind
kind MsgTSInit = init
kind (MsgTSRequestTxIds Blocking _ _) = requestBlocking
kind (MsgTSRequestTxIds NonBlocking _ _) = requestNonBlocking
kind (MsgTSReplyTxIds []) = replyIdsEmpty
kind (MsgTSReplyTxIds (_ ∷ _)) = replyIdsNonEmpty
kind (MsgTSRequestTxs _) = requestTxs
kind (MsgTSReplyTxs _) = replyTxs
kind MsgTSDone = doneK

-- Observe wire messages, erasing application events and payload contents.
cls : Event → Maybe E
cls (evLabel _ (sendTS _ _) (_ , _ , _ , txSubmission m)) = just (Send , kind m)
cls (evLabel _ (receiveTS _ _) (_ , _ , _ , txSubmission m)) = just (Recv , kind m)
cls _ = nothing

-- Exact equality of projected finite wire-control traces.
Obs : List Event → List E → Set
Obs = Br.Obs cls id

-- The submitter processes one request at a time after Init.
ctl : TSState → St
ctl stInit = awaitingInit
ctl stIdle = pending []
ctl stTxIdsBlocking = blocking
ctl stTxIdsNonBlocking = pending (ids ∷ [])
ctl stTxs = pending (txs ∷ [])
ctl stDone = closed

module _ (k : ℕ) (l : Link) (d : Dir) where
  open Spec k client

  -- Use the strict submitter, which rejects empty blocking replies.
  It : Body → Proc
  It t = iter-bind t (submitterStep l d)

  -- Concrete submitter wire output followed by loop-back.
  send : MessageTxSubmission2 → TSState → Body
  send m a = Output (sendTS l d) (time₀ , FromInitiator , length₀ , txSubmission m) (Ret (inj₁ a))

  -- Deliver a blocking ID request to the application.
  blockingAPI : ℕ → ℕ → Body
  blockingAPI a r = Output ⦃ DecEq-BS×ℕ×ℕ ⦄ (apiTSev l d recvTSRequestTxIds) (Blocking , a , r) (Ret (inj₁ stTxIdsBlocking))

  -- Deliver a nonblocking ID request to the application.
  nonblockingAPI : ℕ → ℕ → Body
  nonblockingAPI a r = Output ⦃ DecEq-BS×ℕ×ℕ ⦄ (apiTSev l d recvTSRequestTxIds) (NonBlocking , a , r) (Ret (inj₁ stTxIdsNonBlocking))

  -- Deliver the requested transaction IDs unchanged.
  txsAPI : List TxHash → Body
  txsAPI xs = Output ⦃ DecEq-ListTxHash ⦄ (apiTSev l d recvTSRequestTxs) xs (Ret (inj₁ stTxs))

  -- A local application event.
  apiE : (tag : ApiTSTag) → ApiTSCar tag → Event
  apiE tag v = evLabel _ (apiTSev l d tag) v

  -- A local received payload.
  rcvE : Payload → Event
  rcvE v = evLabel _ (receiveTS l d) v

  -- Exhaustive successful branches of the strict submitter.
  data HeadV (s : TSState) : Event → Body → Set₁ where
    hInit : s ≡ stInit → HeadV s
      (evLabel _ (sendTS l d) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)) (Ret (inj₁ stIdle))
    hBlock : ∀ {tm md ln} a r → s ≡ stIdle → HeadV s (rcvE (tm , md , ln , txSubmission (MsgTSRequestTxIds Blocking a r))) (blockingAPI a r)
    hNonblock : ∀ {tm md ln} a r → s ≡ stIdle → HeadV s (rcvE (tm , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking a r))) (nonblockingAPI a r)
    hTxs : ∀ {tm md ln} xs → s ≡ stIdle → HeadV s (rcvE (tm , md , ln , txSubmission (MsgTSRequestTxs xs))) (txsAPI xs)
    hBIds : ∀ x xs → s ≡ stTxIdsBlocking → HeadV s (apiE sendTSReplyTxIds (x ∷ xs)) (send (MsgTSReplyTxIds (x ∷ xs)) stIdle)
    hNEmpty : s ≡ stTxIdsNonBlocking → HeadV s (apiE sendTSReplyTxIds ([])) (send (MsgTSReplyTxIds ([])) stIdle)
    hNIds : ∀ x xs → s ≡ stTxIdsNonBlocking → HeadV s (apiE sendTSReplyTxIds (x ∷ xs)) (send (MsgTSReplyTxIds (x ∷ xs)) stIdle)
    hDone : ∀ {u}  → s ≡ stTxIdsBlocking → HeadV s (apiE sendTSDone (u)) (send MsgTSDone stDone)
    hReplyTxs : ∀ xs → s ≡ stTxs → HeadV s (apiE sendTSReplyTxs (xs)) (send (MsgTSReplyTxs xs) stIdle)

  -- Invert the actual peer; the Init case is its automatic output.
  headV : ∀ {a x t} → submitterStep l d a ─[ ev (evl x) ]─► t → HeadV a x t
  headV {stInit} st with out-ev st
  ... | refl , refl = hInit refl
  headV {stIdle} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds Blocking a r)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBlock a r refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIdle} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds NonBlocking a r)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hNonblock a r refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIdle} (sVis {at = _ , receiveTS l′ d′} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs xs)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hTxs xs refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev l′ d′ sendTSReplyTxIds} {a = x ∷ xs} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBIds x xs refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev l′ d′ sendTSReplyTxIds} {a = []} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hNEmpty  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev l′ d′ sendTSReplyTxIds} {a = x ∷ xs} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hNIds x xs refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev l′ d′ sendTSDone} {a = u} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hDone  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stTxs} (sVis {at = _ , apiTSev l′ d′ sendTSReplyTxs} {a = xs} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hReplyTxs xs refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} {a = []} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {stIdle} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {stIdle} (sVis {at = _ , sendTS _ _} refl ())
  headV {stIdle} (sVis {at = _ , doneTS _ _} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , sendTS _ _} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , doneTS _ _} refl ())
  headV {stTxIdsBlocking} (sVis {at = _ , receiveTS _ _} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , sendTS _ _} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , doneTS _ _} refl ())
  headV {stTxIdsNonBlocking} (sVis {at = _ , receiveTS _ _} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {stTxs} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {stTxs} (sVis {at = _ , sendTS _ _} refl ())
  headV {stTxs} (sVis {at = _ , doneTS _ _} refl ())
  headV {stTxs} (sVis {at = _ , receiveTS _ _} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSInit)} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , txSubmission (MsgTSDone)} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , keepAlive _} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , blockFetch _} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , chainSync _} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
  headV {stIdle} (sVis {at = _ , receiveTS _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
  headV {stDone} (sVis () _)

  -- Lift a visible transition through the original iteration wrapper.
  fire : ∀ {t t′ x} → t ─[ ev (evl x) ]─► t′ → It t ─[ ev (evl x) ]─► It t′
  fire {t} = iter-bind-ev (submitterStep l d) t

  -- Loop-back is the existing iter silent step.
  back : ∀ {a} → It (Ret (inj₁ a)) ─[ τ ]─► It (submitterStep l d a)
  back = sSil refl

  -- Output and live menu residuals have no silent moves.
  noτ : ∀ {t v M} → PTree.force t ≡ react v ∅t → ¬ (It t ─[ τ ]─► M)
  noτ {t} eq st with iter-τ-elim t (submitterStep l d) st
  ... | itτ _ (sSil eq′) _ = case trans (sym eq) eq′ of λ ()
  ... | itBack _ eq′ _ = case trans (sym eq) eq′ of λ ()
  ... | itτ _ (sTau eq′ br) _ with trans (sym eq) eq′
  ... | refl = case br of λ ()

  -- Finished submitter residuals have no silent successor.
  end-noτ : ∀ {u M} → ¬ (It (Ret (inj₂ u)) ─[ τ ]─► M)
  end-noτ {u} st with iter-τ-elim (Ret (inj₂ u)) (submitterStep l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ () _

  -- A return residual exposes no wire or application event.
  ret-noev : ∀ {a x M} → ¬ (It (Ret a) ─[ ev (evl x) ]─► M)
  ret-noev {a} st with iter-ev-elim (Ret a) (submitterStep l d) st
  ... | _ , sVis () _ , _

  -- The only silent loop-back resumes the corresponding submitter state.
  back-inv : ∀ {a M} → It (Ret (inj₁ a)) ─[ τ ]─► M → M ≡ It (submitterStep l d a)
  back-inv {a} st with iter-τ-elim (Ret (inj₁ a)) (submitterStep l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ refl refl = refl

  -- Output inversion retains the precise emitted value and continuation.
  out-inv : ∀ {B} {dd : DecEq B} {ch : TSEv B} {v a x M} →
    It (Output ⦃ dd ⦄ ch v (Ret a)) ─[ ev (evl x) ]─► M →
    x ≡ evLabel B ch v × M ≡ It (Ret a)
  out-inv {dd = dd} {ch} {v} {a} st with iter-ev-elim (Output ⦃ dd ⦄ ch v (Ret a)) (submitterStep l d) st
  ... | _ , st′ , refl with out-ev ⦃ dd ⦄ st′
  ... | refl , refl = refl , refl

  -- Include API deliveries and pending wire replies, not only loop heads.
  data Rel : Proc → St → Set₁ where
    head : ∀ {a} → Rel (It (submitterStep l d a)) (ctl a)
    loopBack : ∀ {a} → Rel (It (Ret (inj₁ a))) (ctl a)
    sending : ∀ {m a s} → Step s (Send , kind m) (ctl a) → Rel (It (send m a)) s
    blockingR : ∀ a r → Rel (It (blockingAPI a r)) blocking
    nonblockingR : ∀ a r → Rel (It (nonblockingAPI a r)) (pending (ids ∷ []))
    txsR : ∀ xs → Rel (It (txsAPI xs)) (pending (txs ∷ []))

  -- Loop-back is silent at the wire abstraction.
  sim-τ : ∀ {T T′ s} → Rel T s → T ─[ τ ]─► T′ →
    Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel T′ s′)
  sim-τ (head {stInit}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stIdle}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stTxIdsBlocking}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stTxIdsNonBlocking}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stTxs}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stDone}) st = ⊥-elim (end-noτ st)
  sim-τ loopBack st with back-inv st
  ... | refl = _ , done , head
  sim-τ (sending _) st = ⊥-elim (noτ refl st)
  sim-τ (blockingR _ _) st = ⊥-elim (noτ refl st)
  sim-τ (nonblockingR _ _) st = ⊥-elim (noτ refl st)
  sim-τ (txsR _) st = ⊥-elim (noτ refl st)

  -- Match each visible event against the unchanged control checker.
  sim-ev : ∀ {T T′ s e} → Rel T s → T ─[ ev (evl e) ]─► T′ →
    Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (Obs (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel T′ s′)
  sim-ev (head {a}) st with iter-ev-elim (submitterStep l d a) (submitterStep l d) st
  ... | _ , st′ , refl with headV {a = a} st′
  ... | hInit refl = (Send , init) ∷ [] , _ , refl , vis refl done , loopBack
  ... | hBlock a r refl = (Recv , requestBlocking) ∷ [] , _ , refl , vis refl done , blockingR a r
  ... | hNonblock a r refl = (Recv , requestNonBlocking) ∷ [] , _ , refl , vis refl done , nonblockingR a r
  ... | hTxs xs refl = (Recv , requestTxs) ∷ [] , _ , refl , vis refl done , txsR xs
  ... | hBIds x xs refl = [] , _ , refl , done , sending refl
  ... | hNEmpty  refl = [] , _ , refl , done , sending refl
  ... | hNIds x xs refl = [] , _ , refl , done , sending refl
  ... | hDone  refl = [] , _ , refl , done , sending refl
  ... | hReplyTxs xs refl = [] , _ , refl , done , sending refl
  sim-ev loopBack st = ⊥-elim (ret-noev st)
  sim-ev (sending {m} pr) st with out-inv st
  ... | refl , refl = (Send , kind m) ∷ [] , _ , refl , vis pr done , loopBack
  sim-ev (blockingR a r) st with out-inv st
  ... | refl , refl = [] , _ , refl , done , loopBack
  sim-ev (nonblockingR a r) st with out-inv st
  ... | refl , refl = [] , _ , refl , done , loopBack
  sim-ev (txsR xs) st with out-inv st
  ... | refl , refl = [] , _ , refl , done , loopBack

  -- The strict client is simulated by the certified replay language.
  simulation : Br.Sim model cls id Rel
  simulation = record { sim-τ = sim-τ ; sim-ev = sim-ev }

  -- Soundness needs no transaction or transaction-ID inhabitant.
  sound : ∀ {t M es} → P.client l d ⟹∖√⟨ t ⟩ M → Obs t es → HasTrace initial es
  sound {es = es} run o with Br.sound model cls id simulation (head {stInit}) run
  ... | es′ , s′ , o′ , r , _ = s′ , subst (λ xs → initial ⇒⟨ xs ⟩ s′)
    (trans (sym (map-id es′)) (trans (sym o′) (trans o (map-id es)))) r

  -- Expose the actual menu for concrete forward-step witnesses.
  offers : TSState → (at : AnyTypes TSEv) → ContinueType at (Maybe Body)
  offers a with PTree.force (submitterStep l d a)
  ... | react v _ = v
  ... | ret _ = λ _ _ → nothing
  ... | sil _ = λ _ _ → nothing

  -- Construct the Block branch of the actual peer.
  fire-Block : ∀ a r → submitterStep l d stIdle ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)))) ]─► (blockingAPI a r)
  fire-Block a r = sVis refl br
    where
    -- Both endpoint comparisons succeed reflexively.
    br : offers stIdle (_ , receiveTS l d) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (blockingAPI a r)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Nonblock branch of the actual peer.
  fire-Nonblock : ∀ a r → submitterStep l d stIdle ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)))) ]─► (nonblockingAPI a r)
  fire-Nonblock a r = sVis refl br
    where
    -- Both endpoint comparisons succeed reflexively.
    br : offers stIdle (_ , receiveTS l d) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (nonblockingAPI a r)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Txs branch of the actual peer.
  fire-Txs : ∀ xs → submitterStep l d stIdle ─[ ev (evl (rcvE (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs xs)))) ]─► (txsAPI xs)
  fire-Txs xs = sVis refl br
    where
    -- Both endpoint comparisons succeed reflexively.
    br : offers stIdle (_ , receiveTS l d) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs xs)) ≡ just (txsAPI xs)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the BIds branch of the actual peer.
  fire-BIds : ∀ x xs → submitterStep l d stTxIdsBlocking ─[ ev (evl (apiE sendTSReplyTxIds (x ∷ xs))) ]─► (send (MsgTSReplyTxIds (x ∷ xs)) stIdle)
  fire-BIds x xs = sVis refl br
    where
    -- Both endpoint comparisons succeed reflexively.
    br : offers stTxIdsBlocking (_ , apiTSev l d sendTSReplyTxIds) (x ∷ xs) ≡ just (send (MsgTSReplyTxIds (x ∷ xs)) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the NEmpty branch of the actual peer.
  fire-NEmpty : submitterStep l d stTxIdsNonBlocking ─[ ev (evl (apiE sendTSReplyTxIds ([]))) ]─► (send (MsgTSReplyTxIds ([])) stIdle)
  fire-NEmpty  = sVis refl br
    where
    -- Both endpoint comparisons succeed reflexively.
    br : offers stTxIdsNonBlocking (_ , apiTSev l d sendTSReplyTxIds) ([]) ≡ just (send (MsgTSReplyTxIds ([])) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the NIds branch of the actual peer.
  fire-NIds : ∀ x xs → submitterStep l d stTxIdsNonBlocking ─[ ev (evl (apiE sendTSReplyTxIds (x ∷ xs))) ]─► (send (MsgTSReplyTxIds (x ∷ xs)) stIdle)
  fire-NIds x xs = sVis refl br
    where
    -- Both endpoint comparisons succeed reflexively.
    br : offers stTxIdsNonBlocking (_ , apiTSev l d sendTSReplyTxIds) (x ∷ xs) ≡ just (send (MsgTSReplyTxIds (x ∷ xs)) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Done branch of the actual peer.
  fire-Done : submitterStep l d stTxIdsBlocking ─[ ev (evl (apiE sendTSDone (tt))) ]─► (send MsgTSDone stDone)
  fire-Done  = sVis refl br
    where
    -- Both endpoint comparisons succeed reflexively.
    br : offers stTxIdsBlocking (_ , apiTSev l d sendTSDone) (tt) ≡ just (send MsgTSDone stDone)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the ReplyTxs branch of the actual peer.
  fire-ReplyTxs : ∀ xs → submitterStep l d stTxs ─[ ev (evl (apiE sendTSReplyTxs (xs))) ]─► (send (MsgTSReplyTxs xs) stIdle)
  fire-ReplyTxs xs = sVis refl br
    where
    -- Both endpoint comparisons succeed reflexively.
    br : offers stTxs (_ , apiTSev l d sendTSReplyTxs) (xs) ≡ just (send (MsgTSReplyTxs xs) stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Canonical representatives are the six reachable submitter states.
  data RelC : Proc → St → Set₁ where
    cstInit : RelC (It (submitterStep l d stInit)) (ctl stInit)
    cstIdle : RelC (It (submitterStep l d stIdle)) (ctl stIdle)
    cstTxIdsBlocking : RelC (It (submitterStep l d stTxIdsBlocking)) (ctl stTxIdsBlocking)
    cstTxIdsNonBlocking : RelC (It (submitterStep l d stTxIdsNonBlocking)) (ctl stTxIdsNonBlocking)
    cstTxs : RelC (It (submitterStep l d stTxs)) (ctl stTxs)
    cstDone : RelC (It (submitterStep l d stDone)) (ctl stDone)

  -- A single transaction ID realises nonempty replies; no Tx is required.
  module _ (h₀ : TxHash) where
    -- There are no replay tau transitions.
    co-τ : ∀ {T s s′} → RelC T s → Replay._-τ→_ model s s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t [] × RelC T′ s′)
    co-τ _ ()

    -- Realise every accepted sequential control step with original API events.
    co-ev : ∀ {T s s′ e} → RelC T s → ⊤ → Step s e s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
    co-ev {e = Send , init} cstInit _ refl = _ , _ ,
      ∖√-ev (fire out-fire) (∖√-τ back ∖√-refl) , refl , cstIdle
    co-ev {e = Send , requestBlocking} cstInit _ ()
    co-ev {e = Send , requestNonBlocking} cstInit _ ()
    co-ev {e = Send , replyIdsEmpty} cstInit _ ()
    co-ev {e = Send , replyIdsNonEmpty} cstInit _ ()
    co-ev {e = Send , requestTxs} cstInit _ ()
    co-ev {e = Send , replyTxs} cstInit _ ()
    co-ev {e = Send , doneK} cstInit _ ()
    co-ev {e = Recv , init} cstInit _ ()
    co-ev {e = Recv , requestBlocking} cstInit _ ()
    co-ev {e = Recv , requestNonBlocking} cstInit _ ()
    co-ev {e = Recv , replyIdsEmpty} cstInit _ ()
    co-ev {e = Recv , replyIdsNonEmpty} cstInit _ ()
    co-ev {e = Recv , requestTxs} cstInit _ ()
    co-ev {e = Recv , replyTxs} cstInit _ ()
    co-ev {e = Recv , doneK} cstInit _ ()
    co-ev {e = Send , init} cstIdle _ ()
    co-ev {e = Send , requestBlocking} cstIdle _ ()
    co-ev {e = Send , requestNonBlocking} cstIdle _ ()
    co-ev {e = Send , replyIdsEmpty} cstIdle _ ()
    co-ev {e = Send , replyIdsNonEmpty} cstIdle _ ()
    co-ev {e = Send , requestTxs} cstIdle _ ()
    co-ev {e = Send , replyTxs} cstIdle _ ()
    co-ev {e = Send , doneK} cstIdle _ ()
    co-ev {e = Recv , init} cstIdle _ ()
    co-ev {e = Recv , requestBlocking} cstIdle _ refl = _ , _ ,
      ∖√-ev (fire (fire-Block 0 1))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstTxIdsBlocking
    co-ev {e = Recv , requestNonBlocking} cstIdle _ refl = _ , _ ,
      ∖√-ev (fire (fire-Nonblock 0 1))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstTxIdsNonBlocking
    co-ev {e = Recv , replyIdsEmpty} cstIdle _ ()
    co-ev {e = Recv , replyIdsNonEmpty} cstIdle _ ()
    co-ev {e = Recv , requestTxs} cstIdle _ refl = _ , _ ,
      ∖√-ev (fire (fire-Txs []))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstTxs
    co-ev {e = Recv , replyTxs} cstIdle _ ()
    co-ev {e = Recv , doneK} cstIdle _ ()
    co-ev {e = Send , init} cstTxIdsBlocking _ ()
    co-ev {e = Send , requestBlocking} cstTxIdsBlocking _ ()
    co-ev {e = Send , requestNonBlocking} cstTxIdsBlocking _ ()
    co-ev {e = Send , replyIdsEmpty} cstTxIdsBlocking _ ()
    co-ev {e = Send , replyIdsNonEmpty} cstTxIdsBlocking _ refl = _ , _ ,
      ∖√-ev (fire (fire-BIds h₀ []))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , requestTxs} cstTxIdsBlocking _ ()
    co-ev {e = Send , replyTxs} cstTxIdsBlocking _ ()
    co-ev {e = Send , doneK} cstTxIdsBlocking _ refl = _ , _ ,
      ∖√-ev (fire (fire-Done ))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstDone
    co-ev {e = Recv , init} cstTxIdsBlocking _ ()
    co-ev {e = Recv , requestBlocking} cstTxIdsBlocking _ ()
    co-ev {e = Recv , requestNonBlocking} cstTxIdsBlocking _ ()
    co-ev {e = Recv , replyIdsEmpty} cstTxIdsBlocking _ ()
    co-ev {e = Recv , replyIdsNonEmpty} cstTxIdsBlocking _ ()
    co-ev {e = Recv , requestTxs} cstTxIdsBlocking _ ()
    co-ev {e = Recv , replyTxs} cstTxIdsBlocking _ ()
    co-ev {e = Recv , doneK} cstTxIdsBlocking _ ()
    co-ev {e = Send , init} cstTxIdsNonBlocking _ ()
    co-ev {e = Send , requestBlocking} cstTxIdsNonBlocking _ ()
    co-ev {e = Send , requestNonBlocking} cstTxIdsNonBlocking _ ()
    co-ev {e = Send , replyIdsEmpty} cstTxIdsNonBlocking _ refl = _ , _ ,
      ∖√-ev (fire (fire-NEmpty ))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , replyIdsNonEmpty} cstTxIdsNonBlocking _ refl = _ , _ ,
      ∖√-ev (fire (fire-NIds h₀ []))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , requestTxs} cstTxIdsNonBlocking _ ()
    co-ev {e = Send , replyTxs} cstTxIdsNonBlocking _ ()
    co-ev {e = Send , doneK} cstTxIdsNonBlocking _ ()
    co-ev {e = Recv , init} cstTxIdsNonBlocking _ ()
    co-ev {e = Recv , requestBlocking} cstTxIdsNonBlocking _ ()
    co-ev {e = Recv , requestNonBlocking} cstTxIdsNonBlocking _ ()
    co-ev {e = Recv , replyIdsEmpty} cstTxIdsNonBlocking _ ()
    co-ev {e = Recv , replyIdsNonEmpty} cstTxIdsNonBlocking _ ()
    co-ev {e = Recv , requestTxs} cstTxIdsNonBlocking _ ()
    co-ev {e = Recv , replyTxs} cstTxIdsNonBlocking _ ()
    co-ev {e = Recv , doneK} cstTxIdsNonBlocking _ ()
    co-ev {e = Send , init} cstTxs _ ()
    co-ev {e = Send , requestBlocking} cstTxs _ ()
    co-ev {e = Send , requestNonBlocking} cstTxs _ ()
    co-ev {e = Send , replyIdsEmpty} cstTxs _ ()
    co-ev {e = Send , replyIdsNonEmpty} cstTxs _ ()
    co-ev {e = Send , requestTxs} cstTxs _ ()
    co-ev {e = Send , replyTxs} cstTxs _ refl = _ , _ ,
      ∖√-ev (fire (fire-ReplyTxs []))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cstIdle
    co-ev {e = Send , doneK} cstTxs _ ()
    co-ev {e = Recv , init} cstTxs _ ()
    co-ev {e = Recv , requestBlocking} cstTxs _ ()
    co-ev {e = Recv , requestNonBlocking} cstTxs _ ()
    co-ev {e = Recv , replyIdsEmpty} cstTxs _ ()
    co-ev {e = Recv , replyIdsNonEmpty} cstTxs _ ()
    co-ev {e = Recv , requestTxs} cstTxs _ ()
    co-ev {e = Recv , replyTxs} cstTxs _ ()
    co-ev {e = Recv , doneK} cstTxs _ ()
    co-ev {e = Send , init} cstDone _ ()
    co-ev {e = Send , requestBlocking} cstDone _ ()
    co-ev {e = Send , requestNonBlocking} cstDone _ ()
    co-ev {e = Send , replyIdsEmpty} cstDone _ ()
    co-ev {e = Send , replyIdsNonEmpty} cstDone _ ()
    co-ev {e = Send , requestTxs} cstDone _ ()
    co-ev {e = Send , replyTxs} cstDone _ ()
    co-ev {e = Send , doneK} cstDone _ ()
    co-ev {e = Recv , init} cstDone _ ()
    co-ev {e = Recv , requestBlocking} cstDone _ ()
    co-ev {e = Recv , requestNonBlocking} cstDone _ ()
    co-ev {e = Recv , replyIdsEmpty} cstDone _ ()
    co-ev {e = Recv , replyIdsNonEmpty} cstDone _ ()
    co-ev {e = Recv , requestTxs} cstDone _ ()
    co-ev {e = Recv , replyTxs} cstDone _ ()
    co-ev {e = Recv , doneK} cstDone _ ()

    -- The strict submitter co-simulates its replay specification.
    cosimulation : Br.CoSim model cls id RelC (λ _ → ⊤)
    cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

    -- Each accepted trace has an execution in TxSubmission2Pipe.client.
    complete : ∀ {es} → HasTrace initial es →
      ∃[ t ] ∃[ M ] (P.client l d ⟹∖√⟨ t ⟩ M × Obs t es)
    complete {es} (_ , r) with Br.complete model cls id cosimulation
      cstInit (universal (λ _ → tt) es) r
    ... | M , t , run , o , _ = t , M , run , o

    -- Exact control-trace correspondence, independent of the server bound.
    bridge : ∀ {es} → HasTrace initial es ⇔
      (∃[ t ] ∃[ M ] (P.client l d ⟹∖√⟨ t ⟩ M × Obs t es))
    bridge = mk⇔ complete (λ { (t , M , run , o) → sound run o })

{-# OPTIONS --guardedness #-}

-- Bidirectional wire-control correspondence with the existing sequential server.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.BlockFetchServerBridge (p : Params) where

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
open import Cardano_network.BlockFetch p
  using (BFEv; sendBF; receiveBF; apiBFev; doneBF; BFEv-≟; Rr;
         BFState; stIdle; stBusy; stStreaming; stDone; serverStep; BFserverStClient)
open import CSP.Operators BFEv-≟ using (Ret; Output; Prefix₀; ∅t; iter-bind)
open import CSP.Laws.DivFree.Loop BFEv-≟ using (iter-τ-elim; iter-ev-elim; itτ; itBack)
open import CSP.Laws.Bisim.IterCong BFEv-≟ using (iter-bind-ev)
open import CSP.Laws.Traces.PrefixInversion BFEv-≟ using (⟶₀-ev-inv)
open import Cardano_network.Replay.LeiosFetchServerParts using (module OutInv)
open OutInv BFEv-≟ using (out-ev)
open import Cardano_network.Replay.LeiosFetchServerForward using (module Fire)
open Fire BFEv-≟ using (out-fire; pfx-fire)
open import Semantics.LTS {E = BFEv} {I = ExtI BFEv}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil; sTau)
open import Semantics.Deadlock {E = BFEv} {I = ExtI BFEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = BFEv} {I = ExtI BFEv} as Br
open import Semantics.Replay using (Replay)
open import Cardano_network.Replay.BlockFetchServerSession
open import Cardano_network.Replay.BlockFetchClientBridge p using (kind; cls; Obs) public

-- The existing server's loop-body carrier.
Body : Set₁
Body = PTree BFEv (ExtI BFEv) (BFState ⊎ Rr)

-- The existing server's whole-process carrier.
Proc : Set₁
Proc = PTree BFEv (ExtI BFEv) Rr

-- Translate the existing four control states exactly.
ctl : BFState → St
ctl stIdle = idle
ctl stBusy = busy
ctl stStreaming = streaming
ctl stDone = closed

module _ (l : Link) (d : Dir) where
  -- Wrap residuals in the existing server iteration, without replacing it.
  It : Body → Proc
  It t = iter-bind t (serverStep l d)

  -- A server wire output followed by its loop-back.
  send : MessageBlockFetch → BFState → Body
  send m a = Output (sendBF l d) (time₀ , FromResponder , length₀ , blockFetch m) (Ret (inj₁ a))

  -- Deliver the received range to the application before it selects a response.
  deliver : ChainRange → Body
  deliver r = Output (apiBFev l d reqBFRange) r (Ret (inj₁ stBusy))

  -- The local Done notification is visible to the application, not the log.
  notice : Body
  notice = Prefix₀ (doneBF l d) (Ret (inj₁ stDone))

  -- A local application command at this endpoint.
  apiE : (tag : ApiBFTag) → ApiBFCar tag → Event
  apiE tag v = evLabel _ (apiBFev l d tag) v

  -- A received wire message; metadata is retained until observation erases it.
  rcvE : Payload → Event
  rcvE v = evLabel _ (receiveBF l d) v

  -- Exact visible cases of the existing server's step function.
  data HeadV (a : BFState) : Event → Body → Set₁ where
    hReq : ∀ {tm md ln} r → a ≡ stIdle →
      HeadV a (rcvE (tm , md , ln , blockFetch (MsgRequestRange r))) (deliver r)
    hDone : ∀ {tm md ln} → a ≡ stIdle →
      HeadV a (rcvE (tm , md , ln , blockFetch MsgClientDone)) notice
    hStart : ∀ {u} → a ≡ stBusy → HeadV a (apiE sendBFStartBatch u) (send MsgStartBatch stStreaming)
    hNone : ∀ {u} → a ≡ stBusy → HeadV a (apiE sendBFNoBlocks u) (send MsgNoBlocks stIdle)
    hBlock : ∀ b → a ≡ stStreaming → HeadV a (apiE sendBFBlock b) (send (MsgBlock b) stStreaming)
    hEnd : ∀ {u} → a ≡ stStreaming → HeadV a (apiE sendBFBatchDone u) (send MsgBatchDone stIdle)

  -- Invert the actual PTree menu decisions and reject every disabled branch.
  headV : ∀ {a x t} → serverStep l d a ─[ ev (evl x) ]─► t → HeadV a x t
  headV {stIdle} (sVis {at = _ , receiveBF l′ d′} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hReq r refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIdle} (sVis {at = _ , receiveBF l′ d′} {a = _ , _ , _ , blockFetch MsgClientDone} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hDone refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stBusy} (sVis {at = _ , apiBFev l′ d′ sendBFStartBatch} {a = u} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hStart refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stBusy} (sVis {at = _ , apiBFev l′ d′ sendBFNoBlocks} {a = u} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hNone refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stStreaming} (sVis {at = _ , apiBFev l′ d′ sendBFBlock} {a = b} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBlock b refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stStreaming} (sVis {at = _ , apiBFev l′ d′ sendBFBatchDone} {a = u} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hEnd refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {stIdle} (sVis {at = _ , apiBFev _ _ sendBFRequestRange} refl ())
  headV {stIdle} (sVis {at = _ , apiBFev _ _ sendBFClientDone} refl ())
  headV {stIdle} (sVis {at = _ , apiBFev _ _ sendBFStartBatch} refl ())
  headV {stIdle} (sVis {at = _ , apiBFev _ _ sendBFNoBlocks} refl ())
  headV {stIdle} (sVis {at = _ , apiBFev _ _ sendBFBlock} refl ())
  headV {stIdle} (sVis {at = _ , apiBFev _ _ sendBFBatchDone} refl ())
  headV {stIdle} (sVis {at = _ , apiBFev _ _ recvBFBlock} refl ())
  headV {stIdle} (sVis {at = _ , apiBFev _ _ reqBFRange} refl ())
  headV {stIdle} (sVis {at = _ , sendBF _ _} refl ())
  headV {stIdle} (sVis {at = _ , doneBF _ _} refl ())
  headV {stBusy} (sVis {at = _ , apiBFev _ _ sendBFRequestRange} refl ())
  headV {stBusy} (sVis {at = _ , apiBFev _ _ sendBFClientDone} refl ())
  headV {stBusy} (sVis {at = _ , apiBFev _ _ sendBFBlock} refl ())
  headV {stBusy} (sVis {at = _ , apiBFev _ _ sendBFBatchDone} refl ())
  headV {stBusy} (sVis {at = _ , apiBFev _ _ recvBFBlock} refl ())
  headV {stBusy} (sVis {at = _ , apiBFev _ _ reqBFRange} refl ())
  headV {stBusy} (sVis {at = _ , sendBF _ _} refl ())
  headV {stBusy} (sVis {at = _ , doneBF _ _} refl ())
  headV {stBusy} (sVis {at = _ , receiveBF _ _} refl ())
  headV {stStreaming} (sVis {at = _ , apiBFev _ _ sendBFRequestRange} refl ())
  headV {stStreaming} (sVis {at = _ , apiBFev _ _ sendBFClientDone} refl ())
  headV {stStreaming} (sVis {at = _ , apiBFev _ _ sendBFStartBatch} refl ())
  headV {stStreaming} (sVis {at = _ , apiBFev _ _ sendBFNoBlocks} refl ())
  headV {stStreaming} (sVis {at = _ , apiBFev _ _ recvBFBlock} refl ())
  headV {stStreaming} (sVis {at = _ , apiBFev _ _ reqBFRange} refl ())
  headV {stStreaming} (sVis {at = _ , sendBF _ _} refl ())
  headV {stStreaming} (sVis {at = _ , doneBF _ _} refl ())
  headV {stStreaming} (sVis {at = _ , receiveBF _ _} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch (MsgStartBatch)} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch (MsgNoBlocks)} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch (MsgBlock _)} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , blockFetch (MsgBatchDone)} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , keepAlive _} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , chainSync _} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , txSubmission _} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
  headV {stIdle} (sVis {at = _ , receiveBF _ _} {a = _ , _ , _ , leiosFetchP _} refl ())
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
  out-inv : ∀ {B} {dd : DecEq B} {ch : BFEv B} {v a x M} →
    It (Output ⦃ dd ⦄ ch v (Ret a)) ─[ ev (evl x) ]─► M →
    x ≡ evLabel B ch v × M ≡ It (Ret a)
  out-inv {dd = dd} {ch} {v} {a} st with iter-ev-elim (Output ⦃ dd ⦄ ch v (Ret a)) (serverStep l d) st
  ... | _ , st′ , refl with out-ev ⦃ dd ⦄ st′
  ... | refl , refl = refl , refl

  -- Relate each reachable residual, including unlogged application handoffs.
  data Rel : Proc → St → Set₁ where
    head : ∀ {a} → Rel (It (serverStep l d a)) (ctl a)
    loopBack : ∀ {a} → Rel (It (Ret (inj₁ a))) (ctl a)
    sending : ∀ {m a s} → Step s (Send , kind m) (ctl a) → Rel (It (send m a)) s
    delivering : ∀ r → Rel (It (deliver r)) busy
    doneNotice : Rel (It notice) closed

  -- Silent iteration steps do not change the observed control state.
  sim-τ : ∀ {T T′ s} → Rel T s → T ─[ τ ]─► T′ →
    Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel T′ s′)
  sim-τ (head {stIdle}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stBusy}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stStreaming}) st = ⊥-elim (noτ refl st)
  sim-τ (head {stDone}) st = ⊥-elim (end-noτ st)
  sim-τ loopBack st with back-inv st
  ... | refl = _ , done , head
  sim-τ (sending _) st = ⊥-elim (noτ refl st)
  sim-τ (delivering _) st = ⊥-elim (noτ refl st)
  sim-τ doneNotice st = ⊥-elim (noτ refl st)

  -- Match each visible PTree step with zero or one wire-control transitions.
  sim-ev : ∀ {T T′ s e} → Rel T s → T ─[ ev (evl e) ]─► T′ →
    Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (Obs (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel T′ s′)
  sim-ev (head {a}) st with iter-ev-elim (serverStep l d a) (serverStep l d) st
  ... | _ , st′ , refl with headV {a = a} st′
  ... | hReq r refl = (Recv , request) ∷ [] , _ , refl , vis receive done , delivering r
  ... | hDone refl = (Recv , clientDone) ∷ [] , _ , refl , vis close done , doneNotice
  ... | hStart refl = [] , _ , refl , done , sending start
  ... | hNone refl = [] , _ , refl , done , sending none
  ... | hBlock b refl = [] , _ , refl , done , sending body
  ... | hEnd refl = [] , _ , refl , done , sending end
  sim-ev loopBack st = ⊥-elim (ret-noev st)
  sim-ev (sending {m} pr) st with out-inv st
  ... | refl , refl = (Send , kind m) ∷ [] , _ , refl , vis pr done , loopBack
  sim-ev (delivering r) st with out-inv st
  ... | refl , refl = [] , _ , refl , done , loopBack
  sim-ev doneNotice st with iter-ev-elim notice (serverStep l d) st
  ... | _ , st′ , refl with ⟶₀-ev-inv st′
  ... | _ , refl , refl = [] , _ , refl , done , loopBack

  -- The sequential control checker simulates the existing server PTree.
  simulation : Br.Sim model cls id Rel
  simulation = record { sim-τ = sim-τ ; sim-ev = sim-ev }

  -- Every observed finite server run is accepted by the control specification.
  sound : ∀ {t M es} → BFserverStClient l d ⟹∖√⟨ t ⟩ M → Obs t es → HasTrace idle es
  sound {es = es} run o with Br.sound model cls id simulation head run
  ... | es′ , s′ , o′ , r , _ = s′ , subst (λ xs → idle ⇒⟨ xs ⟩ s′)
    (trans (sym (map-id es′)) (trans (sym o′) (trans o (map-id es)))) r

  -- Expose the original step's offer map solely for forward-step proofs.
  offers : BFState → (at : AnyTypes BFEv) → ContinueType at (Maybe Body)
  offers a with PTree.force (serverStep l d a)
  ... | react v _ = v
  ... | ret _ = λ _ _ → nothing
  ... | sil _ = λ _ _ → nothing

  -- Witness the existing server's req branch.
  fire-req : ∀ r → serverStep l d stIdle ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)))) ]─► (deliver r)
  fire-req r = sVis refl br
    where
    -- Endpoint decisions succeed reflexively.
    br : offers stIdle (_ , receiveBF l d) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (deliver r)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Witness the existing server's done branch.
  fire-done : serverStep l d stIdle ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone))) ]─► (notice)
  fire-done  = sVis refl br
    where
    -- Endpoint decisions succeed reflexively.
    br : offers stIdle (_ , receiveBF l d) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (notice)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Witness the existing server's start branch.
  fire-start : serverStep l d stBusy ─[ ev (evl (apiE sendBFStartBatch tt)) ]─► (send MsgStartBatch stStreaming)
  fire-start  = sVis refl br
    where
    -- Endpoint decisions succeed reflexively.
    br : offers stBusy (_ , apiBFev l d sendBFStartBatch) (tt) ≡ just (send MsgStartBatch stStreaming)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Witness the existing server's none branch.
  fire-none : serverStep l d stBusy ─[ ev (evl (apiE sendBFNoBlocks tt)) ]─► (send MsgNoBlocks stIdle)
  fire-none  = sVis refl br
    where
    -- Endpoint decisions succeed reflexively.
    br : offers stBusy (_ , apiBFev l d sendBFNoBlocks) (tt) ≡ just (send MsgNoBlocks stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Witness the existing server's block branch.
  fire-block : ∀ b → serverStep l d stStreaming ─[ ev (evl (apiE sendBFBlock b)) ]─► (send (MsgBlock b) stStreaming)
  fire-block b = sVis refl br
    where
    -- Endpoint decisions succeed reflexively.
    br : offers stStreaming (_ , apiBFev l d sendBFBlock) (b) ≡ just (send (MsgBlock b) stStreaming)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Witness the existing server's end branch.
  fire-end : serverStep l d stStreaming ─[ ev (evl (apiE sendBFBatchDone tt)) ]─► (send MsgBatchDone stIdle)
  fire-end  = sVis refl br
    where
    -- Endpoint decisions succeed reflexively.
    br : offers stStreaming (_ , apiBFev l d sendBFBatchDone) (tt) ≡ just (send MsgBatchDone stIdle)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Canonical representatives are loop heads in the existing server.
  data RelC : Proc → St → Set₁ where
    cIdle : RelC (It (serverStep l d stIdle)) idle
    cBusy : RelC (It (serverStep l d stBusy)) busy
    cStreaming : RelC (It (serverStep l d stStreaming)) streaming
    cClosed : RelC (It (serverStep l d stDone)) closed

  -- Erased request/block payloads need one explicit inhabitant for completeness.
  module _ (b₀ : Block) where
    -- Canonical range for a control-only request observation.
    range₀ : ChainRange
    range₀ = chainRange (point b₀) (point b₀)

    -- No wire-specification silent transition needs realising.
    co-τ : ∀ {T s s′} → RelC T s → Replay._-τ→_ model s s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t [] × RelC T′ s′)
    co-τ _ ()

    -- Construct each response/request trace including its unlogged handoff.
    co-ev : ∀ {T s s′ e} → RelC T s → ⊤ → Step s e s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
    co-ev cIdle _ receive = _ , _ ,
      ∖√-ev (fire (fire-req range₀))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cBusy
    co-ev cIdle _ close = _ , _ ,
      ∖√-ev (fire fire-done)
      (∖√-ev (fire pfx-fire) (∖√-τ back ∖√-refl)) , refl , cClosed
    co-ev cBusy _ start = _ , _ ,
      ∖√-ev (fire fire-start)
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cStreaming
    co-ev cBusy _ none = _ , _ ,
      ∖√-ev (fire fire-none)
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cIdle
    co-ev cStreaming _ body = _ , _ ,
      ∖√-ev (fire (fire-block b₀))
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cStreaming
    co-ev cStreaming _ end = _ , _ ,
      ∖√-ev (fire fire-end)
      (∖√-ev (fire out-fire) (∖√-τ back ∖√-refl)) , refl , cIdle
    co-ev cClosed _ ()

    -- The original server co-simulates the control specification.
    cosimulation : Br.CoSim model cls id RelC (λ _ → ⊤)
    cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

    -- Every permitted control trace has an existing server PTree execution.
    complete : ∀ {es} → HasTrace idle es →
      ∃[ t ] ∃[ M ] (BFserverStClient l d ⟹∖√⟨ t ⟩ M × Obs t es)
    complete {es} (_ , r) with Br.complete model cls id cosimulation
      cIdle (universal (λ _ → tt) es) r
    ... | M , t , run , o , _ = t , M , run , o

    -- Exact finite control-trace correspondence at each endpoint.
    bridge : ∀ {es} → HasTrace idle es ⇔
      (∃[ t ] ∃[ M ] (BFserverStClient l d ⟹∖√⟨ t ⟩ M × Obs t es))
    bridge = mk⇔ complete (λ { (t , M , run , o) → sound run o })

{-# OPTIONS --guardedness #-}

-- Step views and forward moves of the depth-k pipelined client
-- (`LeiosFetchPipe.pipe`) for the CLIENT BRIDGE (trace-replay Phase 5,
-- Increment 3).  Generic in `Params`, the bound `k`, the link and the
-- direction, so every decision `pipeV` takes (`l′ ≟ l`, `d′ ≟ d`,
-- `length q <? k`, `ebHash eb ≟ h`, `length es ≟ length bm`) is on a neutral term and
-- `with` can abstract it.
--   * `headV`: every visible step at a loop head, by inverting `pipeV`;
--   * `it-…`: the loop wrapper `It t = iter-bind t (pipeStep k l d)` around a
--     round residual: head steps, output steps, loop-back and silent stop;
--   * `drainV`: discarded replies by kind and final Done, with no callbacks;
--   * `fire-…`: the head steps at symbolic values (the inverse direction).
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
open import Cardano_network.Params using (Params)

module Cardano_network.Replay.LeiosFetchClientParts (p : Params) where

open import Level using (lift)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (_<?_; _≤?_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Data.Bool using (T)
open import Relation.Nullary.Decidable using (T?)
open import Cardano_network.Replay.LeiosFetchWords using (canonical)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs)
open import Process_Trees using (PTree; ExtI; react; ret; sil; base; pair; fin)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p
open Params p
open import Cardano_network.LeiosFetchP p
  using (LFPEv; sendLFP; receiveLFP; apiLPev; doneLFP; LFPEv-≟; Rr)
open import Cardano_network.LeiosFetchPipe p
open import CSP.Operators LFPEv-≟ using (Ret; Output; ∅t)
open import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil; sTau)
open import CSP.Laws.DivFree.Loop LFPEv-≟ using (iter-τ-elim; iter-ev-elim; itτ; itBack)
open import CSP.Laws.Bisim.IterCong LFPEv-≟ using (iter-bind-ev; iter-bind-τ)
import CSP.Operators LFPEv-≟ as Op

open import Cardano_network.Replay.LeiosFetchOutParts using (module OutInv; module Fire)
open OutInv LFPEv-≟ public using (out-ev)
open Fire LFPEv-≟ public using (out-fire)

-- the client process type
Proc : Set₁
Proc = PTree LFPEv (ExtI LFPEv) Rr

module _ (k : ℕ) (l : Link) (d : Dir) where

  -- the loop around a round residual `t`
  It : PipeT → Proc
  It t = Op.iter-bind t (pipeStep k l d)

  -- the session's api label of command `m` with value `v`
  apiE : (m : ApiLPTag) → ApiLPCar m → Event
  apiE m v = evLabel (ApiLPCar m) (apiLPev l d m) v

  -- a wire receive with payload `a`
  rcvE : Payload → Event
  rcvE a = evLabel Payload (receiveLFP l d) a

  ----------------------------------------------------------------------
  -- Inverting a loop head
  ----------------------------------------------------------------------

  -- the visible steps of `pipeStep k l d q`
  data HeadV (q : List Pend) : Event → PipeT → Set₁ where
    -- the application asks for a body, fewer than k pending: the request goes out next
    hReqB : ∀ pt → length q < k
          → HeadV q (apiE lfpSendBlockRequest pt) (sendM l d (MsgLFPBlockRequest pt) (inj₁ (q ∷ʳ blk pt)))
    -- the application asks for a tx closure, fewer than k pending
    hReqT : ∀ pt bm → length q < k → T (canonical bm)
          → HeadV q (apiE lfpSendBlockTxsRequest (pt , bm))
              (sendM l d (MsgLFPBlockTxsRequest pt bm) (inj₁ (q ∷ʳ txs pt bm)))
    -- the application ends the session, nothing pending
    hDone : ∀ {u} → q ≡ [] → HeadV q (apiE lfpSendDone u) (sendM l d MsgLFPDone (inj₂ _))
    -- a Block for the head BlockRequest's hash arrives
    hBlk  : ∀ {h s q′ tm md ln} eb → q ≡ blk (h , s) ∷ q′ → ebHash eb ≡ h
          → HeadV q (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlock eb))) (delB l d eb q′)
    -- A positional reply matches the head bitmap's count.
    hTxs  : ∀ {pt bm q′ tm md ln} es → q ≡ txs pt bm ∷ q′ → length es ≡ length bm
          → HeadV q (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlockTxs es))) (delT l d pt bm es q′)

  -- the loop-head inversion (one clause per case of `pipeV`)
  headV : ∀ {q x t′} → pipeStep k l d q ─[ ev (evl x) ]─► t′ → HeadV q x t′
  headV {q} (sVis {at = _ , apiLPev l′ d′ lfpSendBlockRequest} {a = pt} refl br)
    with l′ ≟ l | d′ ≟ d | length q <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV q _) (just-injective br) (hReqB pt lt)
  ... | no _     | _        | _      with () ← br
  ... | yes refl | no _     | _      with () ← br
  ... | yes refl | yes refl | no _   with () ← br
  headV {q} (sVis {at = _ , apiLPev l′ d′ lfpSendBlockTxsRequest} {a = pt , bm} refl br)
    with l′ ≟ l | d′ ≟ d | length q <? k | T? (canonical bm)
  ... | yes refl | yes refl | yes lt | yes can = subst (HeadV q _) (just-injective br) (hReqT pt bm lt can)
  ... | no _     | _        | _      | _ with () ← br
  ... | yes refl | no _     | _      | _ with () ← br
  ... | yes refl | yes refl | no _   | _ with () ← br
  ... | yes refl | yes refl | yes _  | no _ with () ← br
  headV {[]} (sVis {at = _ , apiLPev l′ d′ lfpSendDone} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV [] _) (just-injective br) (hDone refl)
  ... | no _     | _        with () ← br
  ... | yes refl | no _     with () ← br
  headV {_ ∷ _} (sVis {at = _ , apiLPev _ _ lfpSendDone} refl ())
  headV {blk (h , s) ∷ q} (sVis {at = _ , receiveLFP l′ d′} {a = _ , _ , _ , leiosFetchP (MsgLFPBlock eb)} refl br)
    with l′ ≟ l | d′ ≟ d | ebHash eb ≟ h
  ... | yes refl | yes refl | yes e = subst (HeadV _ _) (just-injective br) (hBlk eb refl e)
  ... | no _     | _        | _     with () ← br
  ... | yes refl | no _     | _     with () ← br
  ... | yes refl | yes refl | no _  with () ← br
  headV {txs pt bm ∷ q} (sVis {at = _ , receiveLFP l′ d′} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs es)} refl br)
    with l′ ≟ l | d′ ≟ d | length es ≟ length bm
  ... | yes refl | yes refl | yes eq = subst (HeadV _ _) (just-injective br) (hTxs es refl eq)
  ... | no _     | _        | _        with () ← br
  ... | yes refl | no _     | _        with () ← br
  ... | yes refl | yes refl | no _     with () ← br
  headV {[]} (sVis {at = _ , receiveLFP _ _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest _)} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest _ _)} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs _)} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP MsgLFPDone} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest _)} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlock _)} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest _ _)} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP MsgLFPDone} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  headV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
  headV (sVis {at = _ , sendLFP _ _} refl ())
  headV (sVis {at = _ , doneLFP _ _} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpSendRequestNext} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpSendDone} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpSendBlockAnnouncement} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpSendBlockOffer} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpSendBlockTxsOffer} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpSendVotes} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpRecvBlockAnnouncement} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpRecvBlockOffer} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpRecvBlockTxsOffer} refl ())
  headV (sVis {at = _ , apiLPev _ _ lnpRecvVotes} refl ())
  headV (sVis {at = _ , apiLPev _ _ lfpSendBlock} refl ())
  headV (sVis {at = _ , apiLPev _ _ lfpSendBlockTxs} refl ())
  headV (sVis {at = _ , apiLPev _ _ lfpRecvBlock} refl ())
  headV (sVis {at = _ , apiLPev _ _ lfpRecvBlockTxs} refl ())
  headV (sVis {at = _ , apiLPev _ _ lfpReqBlockRequest} refl ())
  headV (sVis {at = _ , apiLPev _ _ lfpReqBlockTxsRequest} refl ())

  ----------------------------------------------------------------------
  -- The loop wrapper, backwards
  ----------------------------------------------------------------------

  -- a visible step at a loop head is a `HeadV` step of the round
  it-head-ev : ∀ {q x M} → It (pipeStep k l d q) ─[ ev (evl x) ]─► M
             → Σ[ t′ ∈ PipeT ] (HeadV q x t′ × M ≡ It t′)
  it-head-ev {q} st with iter-ev-elim (pipeStep k l d q) (pipeStep k l d) st
  ... | t′ , st′ , refl = t′ , headV st′ , refl

  -- an output residual fires only its value, then the loop-back is pending
  it-out-ev : ∀ {B} {dd : DecEq B} {c : LFPEv B} {v : B} {r x M}
            → It (Output ⦃ dd ⦄ c v (Ret r)) ─[ ev (evl x) ]─► M
            → x ≡ evLabel B c v × M ≡ It (Ret r)
  it-out-ev {dd = dd} {c} {v} {r} st with iter-ev-elim (Output ⦃ dd ⦄ c v (Ret r)) (pipeStep k l d) st
  ... | t′ , st′ , refl with out-ev ⦃ dd ⦄ st′
  ...   | refl , refl = refl , refl

  -- a returned residual has no visible move
  it-ret-no-ev : ∀ {r x M} → ¬ (It (Ret r) ─[ ev (evl x) ]─► M)
  it-ret-no-ev {r} st with iter-ev-elim (Ret r) (pipeStep k l d) st
  ... | _ , sVis () _ , _

  -- a τ-free menu residual has no silent move
  it-stable-noτ : ∀ {t v M} → PTree.force t ≡ react v ∅t → ¬ (It t ─[ τ ]─► M)
  it-stable-noτ {t} eqt st with iter-τ-elim t (pipeStep k l d) st
  ... | itτ _ (sSil eq) _    = case trans (sym eqt) eq of λ ()
  ... | itBack _ eq _        = case trans (sym eqt) eq of λ ()
  ... | itτ _ (sTau eq br) _ with trans (sym eqt) eq
  ...   | refl = case br of λ ()

  -- the only silent move of a pending loop-back is the loop-back itself
  it-back-τ : ∀ {q M} → It (Ret (inj₁ q)) ─[ τ ]─► M → M ≡ It (pipeStep k l d q)
  it-back-τ {q} st with iter-τ-elim (Ret (inj₁ q)) (pipeStep k l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ refl refl = refl

  -- a finished client has no silent move
  it-end-noτ : ∀ {u M} → ¬ (It (Ret (inj₂ u)) ─[ τ ]─► M)
  it-end-noτ {u} st with iter-τ-elim (Ret (inj₂ u)) (pipeStep k l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ () _

  ----------------------------------------------------------------------
  -- Forward moves
  ----------------------------------------------------------------------

  -- a round step lifts through the loop
  it-ev : ∀ {t t′ B} {c : LFPEv B} {a : B}
        → t ─[ ev (evl (evLabel B c a)) ]─► t′ → It t ─[ ev (evl (evLabel B c a)) ]─► It t′
  it-ev {t} = iter-bind-ev (pipeStep k l d) t

  -- the loop-back fires
  it-back : ∀ {q} → It (Ret (inj₁ q)) ─[ τ ]─► It (pipeStep k l d q)
  it-back = sSil refl

  -- the application's body request fires below the bound
  fire-reqB : ∀ {q} pt → length q < k
            → pipeStep k l d q ─[ ev (evl (apiE lfpSendBlockRequest pt)) ]─►
              sendM l d (MsgLFPBlockRequest pt) (inj₁ (q ∷ʳ blk pt))
  fire-reqB {q} pt lt = sVis refl br
    where
      -- the offer map's decisions all say yes
      br : pipeV k l d q (_ , apiLPev l d lfpSendBlockRequest) pt
         ≡ just (sendM l d (MsgLFPBlockRequest pt) (inj₁ (q ∷ʳ blk pt)))
      br with l ≟ l | d ≟ d | length q <? k
      ... | yes refl | yes refl | yes _ = refl
      ... | no ¬p    | _        | _     = ⊥-elim (¬p refl)
      ... | yes refl | no ¬p    | _     = ⊥-elim (¬p refl)
      ... | yes refl | yes refl | no ¬p = ⊥-elim (¬p lt)

  -- the application's tx-closure request fires below the bound
  fire-reqT : ∀ {q} pt bm → length q < k → T (canonical bm)
            → pipeStep k l d q ─[ ev (evl (apiE lfpSendBlockTxsRequest (pt , bm))) ]─►
              sendM l d (MsgLFPBlockTxsRequest pt bm) (inj₁ (q ∷ʳ txs pt bm))
  fire-reqT {q} pt bm lt can = sVis refl br
    where
      -- the offer map's decisions all say yes
      br : pipeV k l d q (_ , apiLPev l d lfpSendBlockTxsRequest) (pt , bm)
         ≡ just (sendM l d (MsgLFPBlockTxsRequest pt bm) (inj₁ (q ∷ʳ txs pt bm)))
      br with l ≟ l | d ≟ d | length q <? k | T? (canonical bm)
      ... | yes refl | yes refl | yes _ | yes _ = refl
      ... | no ¬p    | _        | _     | _ = ⊥-elim (¬p refl)
      ... | yes refl | no ¬p    | _     | _ = ⊥-elim (¬p refl)
      ... | yes refl | yes refl | no ¬p | _ = ⊥-elim (¬p lt)
      ... | yes refl | yes refl | yes _ | no ne = ⊥-elim (ne can)

  -- the application's Done fires with nothing pending
  fire-done : ∀ {u} → pipeStep k l d [] ─[ ev (evl (apiE lfpSendDone u)) ]─► sendM l d MsgLFPDone (inj₂ _)
  fire-done {u} = sVis refl br
    where
      -- the offer map's decisions all say yes
      br : pipeV k l d [] (_ , apiLPev l d lfpSendDone) u ≡ just (sendM l d MsgLFPDone (inj₂ _))
      br with l ≟ l | d ≟ d
      ... | yes refl | yes refl = refl
      ... | no ¬p    | _        = ⊥-elim (¬p refl)
      ... | yes refl | no ¬p    = ⊥-elim (¬p refl)

  -- a Block with the head request's hash fires
  fire-blk : ∀ {h s q tm md ln} eb → ebHash eb ≡ h
           → pipeStep k l d (blk (h , s) ∷ q) ─[ ev (evl (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlock eb)))) ]─►
             delB l d eb q
  fire-blk {h} {s} {q} {tm} {md} {ln} eb e = sVis refl br
    where
      -- the offer map's decisions all say yes
      br : pipeV k l d (blk (h , s) ∷ q) (_ , receiveLFP l d) (tm , md , ln , leiosFetchP (MsgLFPBlock eb))
         ≡ just (delB l d eb q)
      br with l ≟ l | d ≟ d | ebHash eb ≟ h
      ... | yes refl | yes refl | yes _ = refl
      ... | no ¬p    | _        | _     = ⊥-elim (¬p refl)
      ... | yes refl | no ¬p    | _     = ⊥-elim (¬p refl)
      ... | yes refl | yes refl | no ¬p = ⊥-elim (¬p e)

  -- A positional reply with the head bitmap's count fires.
  fire-txs : ∀ {pt bm q tm md ln} es → length es ≡ length bm
           → pipeStep k l d (txs pt bm ∷ q) ─[ ev (evl (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlockTxs es)))) ]─►
             delT l d pt bm es q
  fire-txs {pt} {bm} {q} {tm} {md} {ln} es eq = sVis refl br
    where
      -- The routing and count decisions all say yes.
      br : pipeV k l d (txs pt bm ∷ q) (_ , receiveLFP l d) (tm , md , ln , leiosFetchP (MsgLFPBlockTxs es))
         ≡ just (delT l d pt bm es q)
      br with l ≟ l | d ≟ d | length es ≟ length bm
      ... | yes refl | yes refl | yes _ = refl
      ... | no ¬p    | _        | _     = ⊥-elim (¬p refl)
      ... | yes refl | no ¬p    | _     = ⊥-elim (¬p refl)
      ... | yes refl | yes refl | no ¬p = ⊥-elim (¬p eq)

  -- A checking head has exactly one silent action: stop and begin draining.
  stop-inv : ∀ {q M} → pipeStep k l d q ─[ τ ]─► M → M ≡ drainStep l d q
  stop-inv (sTau {i = _ , base _} refl ())
  stop-inv (sTau {i = _ , pair _ _} refl ())
  stop-inv (sTau {i = _ , fin} {a = lift fzero} refl br) = sym (just-injective br)
  stop-inv (sTau {i = _ , fin} {a = lift (fsuc _)} refl ())

  -- Stopping under the iteration wrapper preserves the chosen draining residual.
  it-head-τ : ∀ {q M} → It (pipeStep k l d q) ─[ τ ]─► M → M ≡ It (drainStep l d q)
  it-head-τ {q} st with iter-τ-elim (pipeStep k l d q) (pipeStep k l d) st
  ... | itτ _ st′ refl = cong It (stop-inv st′)
  ... | itBack _ () _

  -- The canonical silent stop is available at every checking head.
  it-stop : ∀ {q} → It (pipeStep k l d q) ─[ τ ]─► It (drainStep l d q)
  it-stop = iter-bind-τ (pipeStep k l d) _
    (sTau {i = _ , fin {n = 1}} {a = lift fzero} refl refl)

  -- Draining has no silent moves, including its final wire-Done residual.
  drain-noτ : ∀ {q M} → ¬ (It (drainStep l d q) ─[ τ ]─► M)
  drain-noτ {[]} = it-stable-noτ refl
  drain-noτ {blk _ ∷ _} = it-stable-noτ refl
  drain-noτ {txs _ _ ∷ _} = it-stable-noτ refl

  -- Drain events consume only the head's message kind, or send Done when empty.
  data DrainV : List Pend → Event → PipeT → Set₁ where
    -- A Block is discarded, even when its hash differs from the request.
    dBlk : ∀ {pt q tm md ln} eb
         → DrainV (blk pt ∷ q) (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlock eb))) (drainStep l d q)
    -- Decoder-admissible transactions are discarded without an API callback.
    dTxs : ∀ {pt bm q tm md ln} es → length es ≤ maxTxs
         → DrainV (txs pt bm ∷ q) (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlockTxs es))) (drainStep l d q)
    -- No application callback is run before the drain's final Done.
    dDone : DrainV [] (evLabel Payload (sendLFP l d)
              (time₀ , FromInitiator , length₀ , leiosFetchP MsgLFPDone)) (Ret (inj₂ _))

  -- Invert one drain event before applying the iteration wrapper.
  drainV : ∀ {q x M} → drainStep l d q ─[ ev (evl x) ]─► M → DrainV q x M
  drainV {[]} st with out-ev st
  ... | refl , refl = dDone
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP l′ d′}
    {a = _ , _ , _ , leiosFetchP (MsgLFPBlock eb)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (DrainV _ _) (just-injective br) (dBlk eb)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP l′ d′}
    {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs es)} refl br) with l′ ≟ l | d′ ≟ d | length es ≤? maxTxs
  ... | yes refl | yes refl | yes cap = subst (DrainV _ _) (just-injective br) (dTxs es cap)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  drainV {blk _ ∷ _} (sVis {at = _ , sendLFP _ _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , doneLFP _ _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , apiLPev _ _ _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest _)} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest _ _)} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPDone)} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs _)} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  drainV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , sendLFP _ _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , doneLFP _ _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , apiLPev _ _ _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest _)} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest _ _)} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPDone)} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlock _)} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  drainV {txs _ _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())

  -- Lift drain inversion through iteration.
  it-drain-ev : ∀ {q x M} → It (drainStep l d q) ─[ ev (evl x) ]─► M
              → Σ[ t′ ∈ PipeT ] (DrainV q x t′ × M ≡ It t′)
  it-drain-ev {q} st with iter-ev-elim (drainStep l d q) (pipeStep k l d) st
  ... | t′ , st′ , refl = t′ , drainV st′ , refl

  -- Any Block can discharge a draining Block request on this link and direction.
  fire-drainB : ∀ {pt q tm md ln} eb
              → drainStep l d (blk pt ∷ q) ─[ ev (evl (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlock eb)))) ]─► drainStep l d q
  fire-drainB {q = q} {tm} {md} {ln} eb = sVis refl br
    where
      -- Both routing comparisons are reflexive.
      br : drainBlockV l d (drainStep l d q) (_ , receiveLFP l d)
             (tm , md , ln , leiosFetchP (MsgLFPBlock eb)) ≡ just (drainStep l d q)
      br with l ≟ l | d ≟ d
      ... | yes refl | yes refl = refl
      ... | no ne | _ = ⊥-elim (ne refl)
      ... | yes refl | no ne = ⊥-elim (ne refl)

  -- A decoder-admissible transaction reply can discharge a draining request.
  fire-drainT : ∀ {pt bm q tm md ln} es → length es ≤ maxTxs
              → drainStep l d (txs pt bm ∷ q) ─[ ev (evl (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlockTxs es)))) ]─► drainStep l d q
  fire-drainT {q = q} {tm} {md} {ln} es cap = sVis refl br
    where
      -- Both routing comparisons are reflexive.
      br : drainTxsV l d (drainStep l d q) (_ , receiveLFP l d)
             (tm , md , ln , leiosFetchP (MsgLFPBlockTxs es)) ≡ just (drainStep l d q)
      br with l ≟ l | d ≟ d | length es ≤? maxTxs
      ... | yes refl | yes refl | yes _ = refl
      ... | no ne | _ | _ = ⊥-elim (ne refl)
      ... | yes refl | no ne | _ = ⊥-elim (ne refl)
      ... | yes refl | yes refl | no ne = ⊥-elim (ne cap)

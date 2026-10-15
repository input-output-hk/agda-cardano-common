{-# OPTIONS --guardedness #-}

-- Step views and forward moves of the depth-k pipelined client
-- (`LeiosFetchPipe.pipe`) for the CLIENT BRIDGE (trace-replay Phase 5,
-- Increment 3).  Generic in `Params`, the bound `k`, the link and the
-- direction, so every decision `pipeV` takes (`l′ ≟ l`, `d′ ≟ d`,
-- `length q <? k`, `ebHash eb ≟ h`, `pt′ ≟ pt`) is on a neutral term and
-- `with` can abstract it.
--   * `headV`: every visible step at a loop head, by inverting `pipeV`;
--   * `it-…`: the loop wrapper `It t = iter-bind t (pipeStep k l d)` around a
--     round residual: head steps, output steps, the loop-back, no τ elsewhere;
--   * `fire-…`: the head steps at symbolic values (the inverse direction).
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
open import Cardano_network.Params using (Params)

module Cardano_network.Replay.ClientParts (p : Params) where

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (_<?_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; ExtI; react; ret; sil)
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
open import CSP.Laws.Bisim.IterCong LFPEv-≟ using (iter-bind-ev)
import CSP.Operators LFPEv-≟ as Op
open import Cardano_network.Replay.ServerParts using (module OutInv)
open OutInv LFPEv-≟ using (out-ev)

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
    hReqT : ∀ pt bm → length q < k
          → HeadV q (apiE lfpSendBlockTxsRequest (pt , bm))
              (sendM l d (MsgLFPBlockTxsRequest pt bm) (inj₁ (q ∷ʳ txs pt)))
    -- the application ends the session, nothing pending
    hDone : ∀ {u} → q ≡ [] → HeadV q (apiE lfpSendDone u) (sendM l d MsgLFPDone (inj₂ _))
    -- a Block for the head BlockRequest's hash arrives
    hBlk  : ∀ {h s q′ tm md ln} eb → q ≡ blk (h , s) ∷ q′ → ebHash eb ≡ h
          → HeadV q (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlock eb))) (delB l d eb q′)
    -- a BlockTxs for the head BlockTxsRequest's point arrives
    hTxs  : ∀ {pt q′ tm md ln} es → q ≡ txs pt ∷ q′
          → HeadV q (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlockTxs pt es))) (delT l d pt es q′)

  -- the loop-head inversion (one clause per case of `pipeV`)
  headV : ∀ {q x t′} → pipeStep k l d q ─[ ev (evl x) ]─► t′ → HeadV q x t′
  headV {q} (sVis {at = _ , apiLPev l′ d′ lfpSendBlockRequest} {a = pt} refl br)
    with l′ ≟ l | d′ ≟ d | length q <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV q _) (just-injective br) (hReqB pt lt)
  ... | no _     | _        | _      with () ← br
  ... | yes refl | no _     | _      with () ← br
  ... | yes refl | yes refl | no _   with () ← br
  headV {q} (sVis {at = _ , apiLPev l′ d′ lfpSendBlockTxsRequest} {a = pt , bm} refl br)
    with l′ ≟ l | d′ ≟ d | length q <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV q _) (just-injective br) (hReqT pt bm lt)
  ... | no _     | _        | _      with () ← br
  ... | yes refl | no _     | _      with () ← br
  ... | yes refl | yes refl | no _   with () ← br
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
  headV {txs pt ∷ q} (sVis {at = _ , receiveLFP l′ d′} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs pt′ es)} refl br)
    with l′ ≟ l | d′ ≟ d | _≟_ ⦃ DecEq-EBPoint ⦄ pt′ pt
  ... | yes refl | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hTxs es refl)
  ... | no _     | _        | _        with () ← br
  ... | yes refl | no _     | _        with () ← br
  ... | yes refl | yes refl | no _     with () ← br
  headV {[]} (sVis {at = _ , receiveLFP _ _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest _)} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest _ _)} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxs _ _)} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP MsgLFPDone} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  headV {blk _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockRequest _)} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlock _)} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP (MsgLFPBlockTxsRequest _ _)} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetchP MsgLFPDone} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , keepAlive _} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , blockFetch _} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , chainSync _} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , txSubmission _} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotify _} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosFetch _} refl ())
  headV {txs _ ∷ _} (sVis {at = _ , receiveLFP _ _} {a = _ , _ , _ , leiosNotifyP _} refl ())
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
  fire-reqT : ∀ {q} pt bm → length q < k
            → pipeStep k l d q ─[ ev (evl (apiE lfpSendBlockTxsRequest (pt , bm))) ]─►
              sendM l d (MsgLFPBlockTxsRequest pt bm) (inj₁ (q ∷ʳ txs pt))
  fire-reqT {q} pt bm lt = sVis refl br
    where
      -- the offer map's decisions all say yes
      br : pipeV k l d q (_ , apiLPev l d lfpSendBlockTxsRequest) (pt , bm)
         ≡ just (sendM l d (MsgLFPBlockTxsRequest pt bm) (inj₁ (q ∷ʳ txs pt)))
      br with l ≟ l | d ≟ d | length q <? k
      ... | yes refl | yes refl | yes _ = refl
      ... | no ¬p    | _        | _     = ⊥-elim (¬p refl)
      ... | yes refl | no ¬p    | _     = ⊥-elim (¬p refl)
      ... | yes refl | yes refl | no ¬p = ⊥-elim (¬p lt)

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

  -- a BlockTxs echoing the head request's point fires
  fire-txs : ∀ {pt q tm md ln} es
           → pipeStep k l d (txs pt ∷ q) ─[ ev (evl (rcvE (tm , md , ln , leiosFetchP (MsgLFPBlockTxs pt es)))) ]─►
             delT l d pt es q
  fire-txs {pt} {q} {tm} {md} {ln} es = sVis refl br
    where
      -- the offer map's decisions all say yes
      br : pipeV k l d (txs pt ∷ q) (_ , receiveLFP l d) (tm , md , ln , leiosFetchP (MsgLFPBlockTxs pt es))
         ≡ just (delT l d pt es q)
      br with l ≟ l | d ≟ d | _≟_ ⦃ DecEq-EBPoint ⦄ pt pt
      ... | yes refl | yes refl | yes _ = refl
      ... | no ¬p    | _        | _     = ⊥-elim (¬p refl)
      ... | yes refl | no ¬p    | _     = ⊥-elim (¬p refl)
      ... | yes refl | yes refl | no ¬p = ⊥-elim (¬p refl)

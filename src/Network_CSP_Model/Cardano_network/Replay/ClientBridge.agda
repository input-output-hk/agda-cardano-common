{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Link)

-- The CLIENT BRIDGE (trace-replay Phase 5, Increment 3; amendment B2, no
-- premise), for every bound `k`, link `l` and direction `d`:
--   * `client-sound`: what the log sees (`clsC`/`forget`) of any √-free run
--     of the depth-k pipelined client `pipe k l d` is a client-spec trace;
--   * `client-complete`: every client-spec trace is seen on some run;
--   * `client-bridge`: the two together.
-- Both directions use the generic `Bridge.sound`/`Bridge.complete`
-- unchanged.  The model's FIFO `List Pend` and the spec's `List Req` are
-- related by `Tr` (same kinds and points, in order).
-- Soundness: `Rel` pairs each reachable loop state (head, the request or
-- reply hand-off after an api or wire event, the pending loop-back, the end)
-- with the spec queue; api events and τ are matched by no spec step, wire
-- events by exactly one.
-- Completeness: `RelC` keeps the client at its loop head (or finished); each
-- spec event is one fixed run (api, wire, loop-back, or wire, api,
-- loop-back), with canonical values for what the log forgets (bitmap `[]`,
-- tx list `[]`, Block body = its hash since `ebHash = id`).
-- CAVEAT (B2): `pipe` was written from the spec, so this bridge mainly
-- certifies that transcription; `server-bridge` is the result about the
-- pre-existing model.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.ClientBridge (k : ℕ) (l : Link) (d : Dir) where

open import Data.Nat using (_<_; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.List.Relation.Unary.All using (universal)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees using (ExtI)
open import Cardano_network.Base using (FromResponder)
open import Cardano_network.Net replayParams using (lfpSendBlockRequest; lfpSendBlockTxsRequest)
open import Cardano_network.Data replayParams
  using (MsgLFPBlockRequest; MsgLFPBlockTxsRequest; MsgLFPDone)
open import Cardano_network.LeiosFetchP replayParams using (LFPEv; LFPEv-≟)
open import Cardano_network.LeiosFetchPipe replayParams using (Pend; blk; txs; pipe; pipeStep; sendM; delB; delT)
open import Cardano_network.Replay.ClientParts replayParams
open import Cardano_network.Replay.ServerForward using (module Fire)
open Fire LFPEv-≟ using (out-fire)
open import Cardano_network.Replay.ServerSound k using (trace-forget)
open import Cardano_network.Replay.Obs using (ObsC; clsC; forget)
open import CSP.Operators LFPEv-≟ using (Ret)
open import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} using (Event; _─[_]─►_; ev; evl; τ)
open import Semantics.Deadlock {E = LFPEv} {I = ExtI LFPEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = LFPEv} {I = ExtI LFPEv} as BrC

open import Cardano_network.Replay.LeiosFetchSession
  using ( St; E; Req; cOpen; cClosed; client₀; blockReq; blockTxsReq; Send; Recv
        ; MsgLeiosBlockRequest; MsgLeiosBlock; MsgLeiosBlockTxsRequest; MsgLeiosBlockTxs
        ; MsgLeiosDone; module Spec )
open Spec k
  using (leiosFetch; _-[_]→_; _-τ→_; cSendBlockReq; cSendTxsReq; cRecvBlock; cRecvTxs; cSendDone)
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (_⇒⟨_⟩_; done; vis; HasTrace)

------------------------------------------------------------------------
-- Model queue versus spec queue
------------------------------------------------------------------------

-- the model's pending queue lists the spec's outstanding requests, in order
data Tr : List Pend → List Req → Set where
  -- both empty
  []  : Tr [] []
  -- a BlockRequest for (h , s) at the head of both
  bk  : ∀ {h s q rq} → Tr q rq → Tr (blk (h , s) ∷ q) (blockReq h s ∷ rq)
  -- a BlockTxsRequest for (h , s) at the head of both
  tx  : ∀ {h s q rq} → Tr q rq → Tr (txs (h , s) ∷ q) (blockTxsReq h s ∷ rq)

-- related queues have the same length
Tr-len : ∀ {q rq} → Tr q rq → length q ≡ length rq
Tr-len []       = refl
Tr-len (bk tr) = cong suc (Tr-len tr)
Tr-len (tx tr) = cong suc (Tr-len tr)

-- enqueueing related requests at the tail keeps the queues related
Tr-snoc : ∀ {q rq x y} → Tr q rq → Tr (x ∷ []) (y ∷ []) → Tr (q ∷ʳ x) (rq ∷ʳ y)
Tr-snoc []       t = t
Tr-snoc (bk tr) t = bk (Tr-snoc tr t)
Tr-snoc (tx tr) t = tx (Tr-snoc tr t)

-- the loop around a round residual, at this bound, link and direction
It′ : _ → Proc
It′ = It k l d

------------------------------------------------------------------------
-- Soundness
------------------------------------------------------------------------

-- every reachable client state, with the spec state that simulates it
data Rel : Proc → St → Set₁ where
  -- loop head at queue q
  rHead : ∀ {q rq} → Tr q rq → Rel (It′ (pipeStep k l d q)) (cOpen rq)
  -- loop-back to queue q pending
  rBack : ∀ {q rq} → Tr q rq → Rel (It′ (Ret (inj₁ q))) (cOpen rq)
  -- the BlockRequest for (h , s) is about to go out (below the bound)
  rReqB : ∀ {q rq h s} → Tr q rq → length q < k
        → Rel (It′ (sendM l d (MsgLFPBlockRequest (h , s)) (inj₁ (q ∷ʳ blk (h , s))))) (cOpen rq)
  -- the BlockTxsRequest for (h , s) is about to go out (below the bound)
  rReqT : ∀ {q rq h s bm} → Tr q rq → length q < k
        → Rel (It′ (sendM l d (MsgLFPBlockTxsRequest (h , s) bm) (inj₁ (q ∷ʳ txs (h , s))))) (cOpen rq)
  -- Done is about to go out
  rDone : Rel (It′ (sendM l d MsgLFPDone (inj₂ _))) (cOpen [])
  -- a received Block is about to be handed over
  rDelB : ∀ {q rq eb} → Tr q rq → Rel (It′ (delB l d eb q)) (cOpen rq)
  -- a received BlockTxs is about to be handed over
  rDelT : ∀ {q rq pt es} → Tr q rq → Rel (It′ (delT l d pt es q)) (cOpen rq)
  -- the session is over
  rEnd  : Rel (It′ (Ret (inj₂ _))) cClosed

-- a model τ is the loop-back; the spec stands still
sim-τ : ∀ {P P′ s} → Rel P s → P ─[ τ ]─► P′ → Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel P′ s′)
sim-τ (rHead _)   st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ (rBack tr)  st with it-back-τ k l d st
... | refl = _ , done , rHead tr
sim-τ (rReqB _ _) st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ (rReqT _ _) st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ rDone       st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ (rDelB _)   st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ (rDelT _)   st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ rEnd        st = ⊥-elim (it-end-noτ k l d st)

-- a model event: api events match no spec step, wire events exactly one
sim-ev : ∀ {P P′ s e} → Rel P s → P ─[ ev (evl e) ]─► P′
       → Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (ObsC (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel P′ s′)
sim-ev (rHead tr) st with it-head-ev k l d st
... | _ , hReqB _ lt , refl   = [] , _ , refl , done , rReqB tr lt
... | _ , hReqT _ _ lt , refl = [] , _ , refl , done , rReqT tr lt
... | _ , hDone refl , refl with tr
...   | [] = [] , _ , refl , done , rDone
sim-ev (rHead tr) st | _ , hBlk eb refl refl , refl with tr
...   | bk tr′ = (Recv , MsgLeiosBlock eb 0) ∷ [] , _ , refl , vis cRecvBlock done , rDelB tr′
sim-ev (rHead tr) st | _ , hTxs es refl , refl with tr
...   | tx {h = h} {s} tr′ = (Recv , MsgLeiosBlockTxs h s 0 0 []) ∷ [] , _ , refl , vis cRecvTxs done , rDelT tr′
sim-ev (rReqB {h = h} {s} tr lt) st with it-out-ev k l d st
... | refl , refl =
  (Send , MsgLeiosBlockRequest h s) ∷ [] , _ , refl
  , vis (cSendBlockReq (subst (_< k) (Tr-len tr) lt)) done , rBack (Tr-snoc tr (bk []))
sim-ev (rReqT {h = h} {s} tr lt) st with it-out-ev k l d st
... | refl , refl =
  (Send , MsgLeiosBlockTxsRequest h s 0 []) ∷ [] , _ , refl
  , vis (cSendTxsReq (subst (_< k) (Tr-len tr) lt)) done , rBack (Tr-snoc tr (tx []))
sim-ev rDone st with it-out-ev k l d st
... | refl , refl = (Send , MsgLeiosDone) ∷ [] , _ , refl , vis cSendDone done , rEnd
sim-ev (rDelB tr) st with it-out-ev k l d st
... | refl , refl = [] , _ , refl , done , rBack tr
sim-ev (rDelT tr) st with it-out-ev k l d st
... | refl , refl = [] , _ , refl , done , rBack tr
sim-ev (rBack _) st = ⊥-elim (it-ret-no-ev k l d st)
sim-ev rEnd      st = ⊥-elim (it-ret-no-ev k l d st)

-- the client spec simulates the pipelined client
clientSim : BrC.Sim leiosFetch clsC forget Rel
clientSim = record { sim-τ = sim-τ ; sim-ev = sim-ev }

-- CLIENT SOUNDNESS: what the log can see of any run of `pipe k l d` is a client-spec trace
client-sound : ∀ {t M es} → pipe k l d ⟹∖√⟨ t ⟩ M → ObsC t es → HasTrace client₀ es
client-sound run o with BrC.sound leiosFetch clsC forget clientSim (rHead []) run
... | _ , s′ , o′ , r , _ = s′ , trace-forget (trans (sym o) o′) r

------------------------------------------------------------------------
-- Completeness
------------------------------------------------------------------------

-- the client state chosen for each spec state
data RelC : Proc → St → Set₁ where
  -- the loop head at the related queue
  cHead : ∀ {q rq} → Tr q rq → RelC (It′ (pipeStep k l d q)) (cOpen rq)
  -- finished
  cEnd  : RelC (It′ (Ret (inj₂ _))) cClosed

-- the client spec has no τ
co-τ : ∀ {P s s′} → RelC P s → s -τ→ s′
     → Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × ObsC t [] × RelC P′ s′)
co-τ (cHead _) ()
co-τ cEnd      ()

-- each spec event is one fixed client run
co-ev : ∀ {P s s′ e} → RelC P s → ⊤ → s -[ e ]→ s′
      → Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × ObsC t (e ∷ []) × RelC P′ s′)
co-ev (cHead tr) _ (cSendBlockReq {h = h} {s} lt) =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-reqB k l d (h , s) (subst (_< k) (sym (Tr-len tr)) lt)))
  (∖√-ev (it-ev k l d out-fire)
  (∖√-τ (it-back k l d) ∖√-refl))
  , refl , cHead (Tr-snoc tr (bk []))
co-ev (cHead tr) _ (cSendTxsReq {h = h} {s} lt) =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-reqT k l d (h , s) [] (subst (_< k) (sym (Tr-len tr)) lt)))
  (∖√-ev (it-ev k l d out-fire)
  (∖√-τ (it-back k l d) ∖√-refl))
  , refl , cHead (Tr-snoc tr (tx []))
co-ev (cHead (bk {h = h} tr)) _ cRecvBlock =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-blk k l d {tm = tt} {md = FromResponder} {ln = tt} h refl))
  (∖√-ev (it-ev k l d out-fire)
  (∖√-τ (it-back k l d) ∖√-refl))
  , refl , cHead tr
co-ev (cHead (tx tr)) _ cRecvTxs =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-txs k l d {tm = tt} {md = FromResponder} {ln = tt} []))
  (∖√-ev (it-ev k l d out-fire)
  (∖√-τ (it-back k l d) ∖√-refl))
  , refl , cHead tr
co-ev (cHead []) _ cSendDone =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-done k l d {u = tt}))
  (∖√-ev (it-ev k l d out-fire)
   ∖√-refl)
  , refl , cEnd
co-ev cEnd _ ()

-- the pipelined client co-simulates the client spec (no premise)
clientCoSim : BrC.CoSim leiosFetch clsC forget RelC (λ _ → ⊤)
clientCoSim = record { co-τ = co-τ ; co-ev = co-ev }

-- CLIENT COMPLETENESS: every client-spec trace is observed on a run of `pipe k l d`
client-complete : ∀ {es} → HasTrace client₀ es → ∃[ t ] ∃[ M ] (pipe k l d ⟹∖√⟨ t ⟩ M × ObsC t es)
client-complete {es} (_ , r) with BrC.complete leiosFetch clsC forget clientCoSim (cHead []) (universal (λ _ → tt) es) r
... | M , t , run , o , _ = t , M , run , o

-- CLIENT BRIDGE (B2): a log trace is a client-spec trace iff the pipelined client shows it
client-bridge : ∀ {es} → HasTrace client₀ es ⇔ (∃[ t ] ∃[ M ] (pipe k l d ⟹∖√⟨ t ⟩ M × ObsC t es))
client-bridge = mk⇔ client-complete (λ { (t , M , run , o) → client-sound run o })

------------------------------------------------------------------------
-- WHY THE EXISTING CLIENT DOES NOT BRIDGE (B2), comment only
------------------------------------------------------------------------
-- `LeiosFetchP.LFPclientStClient` (depth-1, alternating) fails both ways:
--   * model ⊄ spec: after `Send BlockRequest 5 0` it accepts ANY Block, so
--     `[Send BlockRequest 5 0 , Recv Block 6 z]` is observed on a run but is
--     not a client-spec trace (`cRecvBlock` needs the head's hash 5);
--   * spec ⊄ model: `[Send BlockRequest 1 0 , Send BlockRequest 2 0]` is a
--     client-spec trace for every k ≥ 2, but the depth-1 client cannot send a
--     second request before the first reply.
-- Not mechanised.

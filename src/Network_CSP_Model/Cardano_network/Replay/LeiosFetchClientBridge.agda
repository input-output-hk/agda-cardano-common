{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Link)

-- Counted bridge for the spec-written depth-k FIFO client, for every link and
-- direction. Honest sends are canonical; checking retains positional counts;
-- silent stop-and-drain ignores handler count matching but keeps decoder caps.
-- Soundness consumes WireOK for forgotten sizes and bitmap validity. The bridge
-- certifies this pipe transcription, not the pre-existing depth-1 client.
-- Checked with --safe on the command line (B7a).
module Cardano_network.Replay.LeiosFetchClientBridge (k : ℕ) (l : Link) (d : Dir) where

open import Data.Nat using (_<_; _≤_; suc; z≤n)
open import Data.List using (List; []; _∷_; _∷ʳ_; length; map; upTo; replicate)
import Data.List.Properties as L
import Data.Nat.Properties as N
open import Data.Bool using (T)
open import Cardano_network.Replay.LeiosFetchWords using (canonical; canonical-count; canonical-upTo; canonical-decodable; toWords; toWords-valid; toWords-popcount)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs)
open import Cardano_network.Replay.LeiosFetchWireOK using (WireOK; accepted-wire)
open import Cardano_network.Replay.LeiosFetchObservationTransport k using (accepted-transport)
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
  using (MsgLFPBlockRequest; MsgLFPBlockTxsRequest; MsgLFPDone; MsgLFPBlockTxs; leiosFetchP)
open import Cardano_network.LeiosFetchP replayParams using (LFPEv; LFPEv-≟)
open import Cardano_network.LeiosFetchPipe replayParams using (Pend; blk; txs; pipe; pipeStep; sendM; delB; delT; drainStep)
open import Cardano_network.Replay.LeiosFetchClientParts replayParams
open import Cardano_network.Replay.LeiosFetchObs using (ObsC; clsC; forget; _≈♭_; recv-reply; txs♭; txsReq♭)
open import CSP.Operators LFPEv-≟ using (Ret)
open import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} using (Event; _─[_]─►_; ev; evl; τ)
open import Semantics.Deadlock {E = LFPEv} {I = ExtI LFPEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = LFPEv} {I = ExtI LFPEv} as BrC

open import Cardano_network.Replay.LeiosFetchSession
  using ( St; E; Req; cOpen; cDrain; cClosed; client₀; blockReq; blockTxsReq; Send; Recv
        ; MsgLeiosBlockRequest; MsgLeiosBlock; MsgLeiosBlockTxsRequest; MsgLeiosBlockTxs
        ; MsgLeiosDone; module Spec )
open Spec k
  using (leiosFetch; _-[_]→_; _-τ→_; cSendBlockReq; cSendTxsReq; cRecvBlock; cRecvTxs; cSendDone; cStop; cDrainBlock; cDrainTxs; cDrainDone)
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (_⇒⟨_⟩_; done; tau; vis; HasTrace)

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
  tx  : ∀ {h s bm q rq} → T (canonical bm) → Tr q rq → Tr (txs (h , s) bm ∷ q) (blockTxsReq h s (length bm) ∷ rq)

-- related queues have the same length
Tr-len : ∀ {q rq} → Tr q rq → length q ≡ length rq
Tr-len []       = refl
Tr-len (bk tr) = cong suc (Tr-len tr)
Tr-len (tx can tr) = cong suc (Tr-len tr)

-- enqueueing related requests at the tail keeps the queues related
Tr-snoc : ∀ {q rq x y} → Tr q rq → Tr (x ∷ []) (y ∷ []) → Tr (q ∷ʳ x) (rq ∷ʳ y)
Tr-snoc []       t = t
Tr-snoc (bk tr) t = bk (Tr-snoc tr t)
Tr-snoc (tx can tr) t = tx can (Tr-snoc tr t)

-- Completeness and soundness retain the same counted FIFO invariant.
TrC : List Pend → List Req → Set
TrC = Tr

-- The shared FIFO relation preserves queue length.
TrC-len : ∀ {q rq} → TrC q rq → length q ≡ length rq
TrC-len = Tr-len

-- Appending counted requests preserves the shared relation.
TrC-snoc : ∀ {q rq x y} → TrC q rq → TrC (x ∷ []) (y ∷ []) → TrC (q ∷ʳ x) (rq ∷ʳ y)
TrC-snoc = Tr-snoc

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
  rReqT : ∀ {q rq h s bm} → Tr q rq → length q < k → T (canonical bm)
        → Rel (It′ (sendM l d (MsgLFPBlockTxsRequest (h , s) bm) (inj₁ (q ∷ʳ txs (h , s) bm)))) (cOpen rq)
  -- Done is about to go out
  rDone : Rel (It′ (sendM l d MsgLFPDone (inj₂ _))) (cOpen [])
  -- a received Block is about to be handed over
  rDelB : ∀ {q rq eb} → Tr q rq → Rel (It′ (delB l d eb q)) (cOpen rq)
  -- a received BlockTxs is about to be handed over
  rDelT : ∀ {q rq pt bm es} → Tr q rq → Rel (It′ (delT l d pt bm es q)) (cOpen rq)
  -- A stopped client drains by kind, with no application callbacks.
  rDraining : ∀ {q rq} → Tr q rq → Rel (It′ (drainStep l d q)) (cDrain rq)
  -- the session is over
  rEnd  : Rel (It′ (Ret (inj₂ _))) cClosed

-- A loop-back leaves the spec unchanged; a silent stop matches cStop.
sim-τ : ∀ {P P′ s} → Rel P s → P ─[ τ ]─► P′ → Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel P′ s′)
sim-τ (rHead tr) st with it-head-τ k l d st
... | refl = _ , tau cStop done , rDraining tr
sim-τ (rBack tr)  st with it-back-τ k l d st
... | refl = _ , done , rHead tr
sim-τ (rReqB _ _) st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ (rReqT _ _ _) st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ rDone       st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ (rDelB _)   st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ (rDelT _)   st = ⊥-elim (it-stable-noτ k l d refl st)
sim-τ (rDraining {q} _) st = ⊥-elim (drain-noτ k l d {q = q} st)
sim-τ rEnd        st = ⊥-elim (it-end-noτ k l d st)

-- Decoder-successful transaction receives retain their count in the observation.
reply-obs : ∀ {tm md ln} ts → length ts ≤ maxTxs →
  ObsC (rcvE k l d (tm , md , ln , leiosFetchP
    (MsgLFPBlockTxs ts)) ∷ [])
    ((Recv , MsgLeiosBlockTxs (length ts) 0) ∷ [])
reply-obs {tm} {md} {ln} ts cap rewrite recv-reply tm md ln ts cap = refl

-- a model event: api events match no spec step, wire events exactly one
sim-ev : ∀ {P P′ s e} → Rel P s → P ─[ ev (evl e) ]─► P′
       → Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (ObsC (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel P′ s′)
sim-ev (rHead tr) st with it-head-ev k l d st
... | _ , hReqB _ lt , refl   = [] , _ , refl , done , rReqB tr lt
... | _ , hReqT _ _ lt can , refl = [] , _ , refl , done , rReqT tr lt can
... | _ , hDone refl , refl with tr
...   | [] = [] , _ , refl , done , rDone
sim-ev (rHead tr) st | _ , hBlk eb refl refl , refl with tr
...   | bk tr′ = (Recv , MsgLeiosBlock eb 0) ∷ [] , _ , refl , vis (cRecvBlock z≤n) done , rDelB tr′
sim-ev (rHead tr) st | _ , hTxs {tm = tm} {md} {ln} es refl count , refl with tr
... | tx {h = h} {s} {bm} can tr′ =
  (Recv , MsgLeiosBlockTxs (length bm) 0) ∷ [] , _ ,
  trans (reply-obs {tm} {md} {ln} es (subst (_≤ maxTxs) (sym count) (canonical-count {os = bm} can)))
    (cong (λ n → (Recv , txs♭ n) ∷ []) count) ,
  vis (cRecvTxs (canonical-count {os = bm} can) z≤n) done , rDelT tr′
sim-ev (rReqB {h = h} {s} tr lt) st with it-out-ev k l d st
... | refl , refl =
  (Send , MsgLeiosBlockRequest h s) ∷ [] , _ , refl
  , vis (cSendBlockReq (subst (_< k) (Tr-len tr) lt)) done , rBack (Tr-snoc tr (bk []))
sim-ev (rReqT {h = h} {s} {bm} tr lt can) st with it-out-ev k l d st
... | refl , refl =
  (Send , MsgLeiosBlockTxsRequest h s (length bm) (toWords bm)) ∷ [] , _ , refl ,
  vis (cSendTxsReq (subst (_< k) (Tr-len tr) lt) (toWords-valid {os = bm} (canonical-decodable {os = bm} can))
    (sym (toWords-popcount {os = bm} (canonical-decodable {os = bm} can))) (canonical-count {os = bm} can)) done ,
  rBack (Tr-snoc tr (tx can []))
sim-ev rDone st with it-out-ev k l d st
... | refl , refl = (Send , MsgLeiosDone) ∷ [] , _ , refl , vis cSendDone done , rEnd
sim-ev (rDelB tr) st with it-out-ev k l d st
... | refl , refl = [] , _ , refl , done , rBack tr
sim-ev (rDelT tr) st with it-out-ev k l d st
... | refl , refl = [] , _ , refl , done , rBack tr
sim-ev (rDraining {q} tr) st with it-drain-ev k l d {q = q} st
... | _ , dBlk eb , refl with tr
...   | bk tr′ = (Recv , MsgLeiosBlock eb 0) ∷ [] , _ , refl
              , vis (cDrainBlock z≤n) done , rDraining tr′
sim-ev (rDraining tr) st | _ , dTxs {tm = tm} {md} {ln} ts cap , refl with tr
... | tx can tr′ = (Recv , MsgLeiosBlockTxs (length ts) 0) ∷ [] , _ , reply-obs {tm} {md} {ln} ts cap ,
  vis (cDrainTxs cap z≤n) done , rDraining tr′
sim-ev (rDraining tr) st | _ , dDone , refl with tr
...   | [] = (Send , MsgLeiosDone) ∷ [] , _ , refl , vis cDrainDone done , rEnd
sim-ev (rBack _) st = ⊥-elim (it-ret-no-ev k l d st)
sim-ev rEnd      st = ⊥-elim (it-ret-no-ev k l d st)

-- the client spec simulates the pipelined client
clientSim : BrC.Sim leiosFetch clsC forget Rel
clientSim = record { sim-τ = sim-τ ; sim-ev = sim-ev }

-- Every counted observation of a client run is accepted under its wire premise.
client-sound : ∀ {t M es} → pipe k l d ⟹∖√⟨ t ⟩ M → ObsC t es → WireOK es → HasTrace client₀ es
client-sound run obs wire with BrC.sound leiosFetch clsC forget clientSim (rHead []) run
... | es′ , s′ , same , trace , related = accepted-transport (s′ , trace) (trans (sym same) obs) wire

------------------------------------------------------------------------
-- Completeness
------------------------------------------------------------------------

-- the client state chosen for each spec state
data RelC : Proc → St → Set₁ where
  -- the loop head at the related queue
  cHead : ∀ {q rq} → TrC q rq → RelC (It′ (pipeStep k l d q)) (cOpen rq)
  -- A stopped client drains the corresponding queue.
  cDraining : ∀ {q rq} → TrC q rq → RelC (It′ (drainStep l d q)) (cDrain rq)
  -- finished
  cEnd  : RelC (It′ (Ret (inj₂ _))) cClosed

-- A silent spec stop selects the model stop branch.
co-τ : ∀ {P s s′} → RelC P s → s -τ→ s′
     → Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × ObsC t [] × RelC P′ s′)
co-τ (cHead tr) cStop = _ , [] , ∖√-τ (it-stop k l d) ∖√-refl , refl , cDraining tr
co-τ (cDraining _) ()
co-τ cEnd      ()

-- each spec event is one fixed client run
co-ev : ∀ {P s s′ e} → RelC P s → ⊤ → s -[ e ]→ s′
      → Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × ObsC t (e ∷ []) × RelC P′ s′)
co-ev (cHead tr) _ (cSendBlockReq {h = h} {s} lt) =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-reqB k l d (h , s) (subst (_< k) (sym (TrC-len tr)) lt)))
  (∖√-ev (it-ev k l d out-fire)
  (∖√-τ (it-back k l d) ∖√-refl))
  , refl , cHead (TrC-snoc tr (bk []))
co-ev (cHead tr) _ (cSendTxsReq {h = h} {s} {n} lt _ _ cap) =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-reqT k l d (h , s) (upTo n) (subst (_< k) (sym (TrC-len tr)) lt) (canonical-upTo n cap)))
  (∖√-ev (it-ev k l d out-fire) (∖√-τ (it-back k l d) ∖√-refl)) ,
  cong (λ m → (Send , txsReq♭ h s m) ∷ []) (L.length-upTo n) ,
  cHead (TrC-snoc tr (subst (λ m → TrC (txs (h , s) (upTo n) ∷ []) (blockTxsReq h s m ∷ []))
    (L.length-upTo n) (tx (canonical-upTo n cap) [])))
co-ev (cHead (bk {h = h} tr)) _ (cRecvBlock _) =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-blk k l d {tm = tt} {md = FromResponder} {ln = tt} h refl))
  (∖√-ev (it-ev k l d out-fire)
  (∖√-τ (it-back k l d) ∖√-refl))
  , refl , cHead tr
co-ev (cHead (tx {bm = bm} can tr)) _ (cRecvTxs cap _) =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-txs k l d {tm = tt} {md = FromResponder} {ln = tt}
    (replicate (length bm) tt) (L.length-replicate (length bm))))
  (∖√-ev (it-ev k l d out-fire) (∖√-τ (it-back k l d) ∖√-refl)) ,
  trans (reply-obs {tm = tt} {md = FromResponder} {ln = tt} (replicate (length bm) tt) (subst (_≤ maxTxs) (sym (L.length-replicate (length bm))) cap))
    (cong (λ n → (Recv , txs♭ n) ∷ []) (L.length-replicate (length bm))) , cHead tr
co-ev (cHead []) _ cSendDone =
  _ , _ ,
  ∖√-ev (it-ev k l d (fire-done k l d {u = tt}))
  (∖√-ev (it-ev k l d out-fire)
   ∖√-refl)
  , refl , cEnd
co-ev (cDraining (bk {h = h₀} {s} {q} tr)) _ (cDrainBlock {h′ = h} _) =
  _ , _ , ∖√-ev (it-ev k l d (fire-drainB k l d {pt = h₀ , s} {q = q} {tm = tt} {md = FromResponder} {ln = tt} h)) ∖√-refl
  , refl , cDraining tr
co-ev (cDraining (tx {h = h} {s} {bm} {q} can tr)) _ (cDrainTxs {n′ = n} cap _) =
  _ , _ , ∖√-ev (it-ev k l d (fire-drainT k l d {pt = h , s} {bm = bm} {q = q}
    {tm = tt} {md = FromResponder} {ln = tt} (replicate n tt)
    (subst (_≤ maxTxs) (sym (L.length-replicate n)) cap))) ∖√-refl ,
  trans (reply-obs {tm = tt} {md = FromResponder} {ln = tt} (replicate n tt) (subst (_≤ maxTxs) (sym (L.length-replicate n)) cap))
    (cong (λ m → (Recv , txs♭ m) ∷ []) (L.length-replicate n)) , cDraining tr
co-ev (cDraining []) _ cDrainDone =
  _ , _ , ∖√-ev (it-ev k l d out-fire) ∖√-refl , refl , cEnd
co-ev cEnd _ ()

-- the pipelined client co-simulates the client spec (no premise)
clientCoSim : BrC.CoSim leiosFetch clsC forget RelC (λ _ → ⊤)
clientCoSim = record { co-τ = co-τ ; co-ev = co-ev }

-- CLIENT COMPLETENESS: every client-spec trace is observed on a run of `pipe k l d`
client-complete : ∀ {es} → HasTrace client₀ es → ∃[ t ] ∃[ M ] (pipe k l d ⟹∖√⟨ t ⟩ M × ObsC t es)
client-complete {es} (_ , r) with BrC.complete leiosFetch clsC forget clientCoSim (cHead []) (universal (λ _ → tt) es) r
... | M , t , run , o , _ = t , M , run , o

-- Exact counted client bridge; forgotten wire fields are constrained explicitly.
client-bridge : ∀ {es} → HasTrace client₀ es ⇔
  (WireOK es × ∃[ t ] ∃[ M ] (pipe k l d ⟹∖√⟨ t ⟩ M × ObsC t es))
client-bridge = mk⇔ forward backward
  where
  -- Completeness realizes every accepted client log, which is wire-admissible.
  forward : ∀ {es} → HasTrace client₀ es → WireOK es × ∃[ t ] ∃[ M ] (pipe k l d ⟹∖√⟨ t ⟩ M × ObsC t es)
  forward accepted = accepted-wire k accepted , client-complete accepted

  -- Universal soundness consumes the matching run, observation and wire checks.
  backward : ∀ {es} → (WireOK es × ∃[ t ] ∃[ M ] (pipe k l d ⟹∖√⟨ t ⟩ M × ObsC t es)) → HasTrace client₀ es
  backward (wire , t , M , run , obs) = client-sound run obs wire

------------------------------------------------------------------------
-- WHY THE EXISTING CLIENT DOES NOT BRIDGE (B2), comment only
------------------------------------------------------------------------
-- `LeiosFetchP.LFPclientStClient` (depth-1, alternating) fails both ways:
--   * model ⊄ spec: it accepts ANY Block and can then send another request.
--     `[Send BlockRequest 5 0 , Recv Block 6 0 , Send BlockRequest 7 0]`
--     is not a client-spec trace: checking requires hash 5; draining admits
--     the mismatch but forbids the later request. The two-event prefix alone
--     is now accepted by stopping and draining.
--   * spec ⊄ model: `[Send BlockRequest 1 0 , Send BlockRequest 2 0]` is a
--     client-spec trace for every k ≥ 2, but the depth-1 client cannot send a
--     second request before the first reply.
-- Not mechanised.

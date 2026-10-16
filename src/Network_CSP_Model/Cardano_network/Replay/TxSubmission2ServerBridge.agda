{-# OPTIONS --guardedness #-}

-- Exact control-trace correspondence for the original pipelined PTree.
-- Payload contents beyond control distinctions, API events, collection and √ are erased.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.TxSubmission2ServerBridge (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.List using (List; []; _∷_; _∷ʳ_; length; map)
open import Data.List.Properties using (map-id)
open import Data.List.Relation.Unary.All using (universal)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p
open Params p
open import Cardano_network.TxSubmission p using (TSEv; sendTS; receiveTS; TSEv-≟; Rr)
import Cardano_network.TxSubmission2Pipe p as P
open P using (send; step)
open import Cardano_network.Replay.TxSubmission2ServerParts p
open import CSP.Operators TSEv-≟ using (Ret)
open import Semantics.LTS {E = TSEv} {I = ExtI TSEv} using (Event; evLabel; _─[_]─►_; ev; evl; τ)
open import Semantics.Deadlock {E = TSEv} {I = ExtI TSEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Cardano_network.Replay.LeiosFetchServerForward using (module Fire)
open Fire TSEv-≟ using (out-fire)
import Semantics.Replay.Bridge {E = TSEv} {I = ExtI TSEv} as Br
open import Semantics.Replay using (Replay)
open import Cardano_network.Replay.TxSubmission2Session
import Cardano_network.Replay.TxSubmission2StepView as V
open import Cardano_network.Replay.TxSubmission2ClientBridge p using (kind; cls; Obs) public
open import Cardano_network.Replay.PipelineBounds using (wire-bound)

-- Translate FIFO tags without erasing the expected response family.
reply : P.Reply → Reply
reply P.ids = ids
reply P.txs = txs

-- Preserve the entire unanswered FIFO in the replay state.
queue : List P.Reply → List Reply
queue = map reply

-- Completed results occupy sender credit but are invisible on the wire.
ctl : P.State → St
ctl P.awaitingInit = awaitingInit
ctl P.blocking = blocking
ctl (P.pending q c) = pending (queue q)

-- FIFO conversion preserves the number of pending requests.
queue-length : ∀ q → length (queue q) ≡ length q
queue-length [] = refl
queue-length (_ ∷ q) = cong suc (queue-length q)

-- FIFO conversion commutes with enqueueing one response family.
queue-snoc : ∀ q r → queue (q ∷ʳ r) ≡ queue q ∷ʳ reply r
queue-snoc [] r = refl
queue-snoc (x ∷ q) r = cong (reply x ∷_) (queue-snoc q r)

module _ (k : ℕ) (l : Link) (d : Dir) where
  open Spec k server

  -- Retain the actual requester iteration around every residual.
  It′ : P.Body → Proc
  It′ = It k l d

  -- A concrete occupancy guard implies admission of the projected FIFO.
  admit : ∀ q c r → length q + c < k →
    issue k (queue q) (reply r) ≡ just (pending (queue (q ∷ʳ r)))
  admit q c r lt = trans (V.issue-ok (subst (_< k) (sym (queue-length q)) (wire-bound lt)))
    (cong (λ qs → just (pending qs)) (sym (queue-snoc q r)))

  -- ID request admission has the same target FIFO as the original PTree.
  ids-ok : ∀ q c → length q + c < k →
    Step (ctl (P.pending q c)) (Send , requestNonBlocking) (ctl (P.pending (q ∷ʳ P.ids) c))
  ids-ok [] c lt = admit [] c P.ids lt
  ids-ok (P.ids ∷ q) c lt = admit (P.ids ∷ q) c P.ids lt
  ids-ok (P.txs ∷ q) c lt = admit (P.txs ∷ q) c P.ids lt

  -- Transaction request admission preserves its distinct FIFO tag.
  txs-ok : ∀ q c → length q + c < k →
    Step (ctl (P.pending q c)) (Send , requestTxs) (ctl (P.pending (q ∷ʳ P.txs) c))
  txs-ok [] c lt = admit [] c P.txs lt
  txs-ok (P.ids ∷ q) c lt = admit (P.ids ∷ q) c P.txs lt
  txs-ok (P.txs ∷ q) c lt = admit (P.txs ∷ q) c P.txs lt

  -- Account for wire sends, API deliveries, collection and final return.
  data Rel : Proc → St → Set₁ where
    head : ∀ s → Rel (It′ (step k l d s)) (ctl s)
    backR : ∀ s → Rel (It′ (Ret (inj₁ s))) (ctl s)
    sendR : ∀ {m s a} → Step s (Send , kind m) (ctl a) → Rel (It′ (send l d m a)) s
    idsR : ∀ s xs → Rel (It′ (deliverIds k l d xs s)) (ctl s)
    txsR : ∀ s xs → Rel (It′ (deliverTxs k l d xs s)) (ctl s)
    endR : Rel (It′ (Ret (inj₂ _))) closed

  -- Internal result collection leaves the unanswered FIFO unchanged.
  sim-τ : ∀ {T T′ s} → Rel T s → T ─[ τ ]─► T′ →
    Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel T′ s′)
  sim-τ (head (P.pending q c)) st with collect-inv k l d st
  ... | c′ , refl , refl = _ , done , backR (P.pending q c′)
  sim-τ (head P.awaitingInit) st = ⊥-elim (init-noτ k l d st)
  sim-τ (head P.blocking) st = ⊥-elim (blocking-noτ k l d st)
  sim-τ (backR s) st with back-inv k l d st
  ... | refl = _ , done , head s
  sim-τ (sendR _) st = ⊥-elim (noτ k l d refl st)
  sim-τ (idsR _ _) st = ⊥-elim (noτ k l d refl st)
  sim-τ (txsR _ _) st = ⊥-elim (noτ k l d refl st)
  sim-τ endR st = ⊥-elim (end-noτ k l d st)

  -- Wire transitions preserve FIFO order and the blocking reply constraint.
  sim-ev : ∀ {T T′ s e} → Rel T s → T ─[ ev (evl e) ]─► T′ →
    Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (Obs (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel T′ s′)
  sim-ev (head s) st with head-inv k l d st
  ... | _ , hInit refl , refl = (Recv , init) ∷ [] , _ , refl , vis refl done , backR _
  ... | _ , hBlock a r refl , refl = [] , _ , refl , done , sendR refl
  ... | _ , hIds a r refl lt , refl = [] , _ , refl , done , sendR (ids-ok _ _ lt)
  ... | _ , hTxs xs refl lt , refl = [] , _ , refl , done , sendR (txs-ok _ _ lt)
  ... | _ , hReplyIds [] refl , refl = (Recv , replyIdsEmpty) ∷ [] , _ , refl , vis refl done , idsR _ []
  ... | _ , hReplyIds (x ∷ xs) refl , refl = (Recv , replyIdsNonEmpty) ∷ [] , _ , refl , vis refl done , idsR _ (x ∷ xs)
  ... | _ , hReplyTxs xs refl , refl = (Recv , replyTxs) ∷ [] , _ , refl , vis refl done , txsR _ xs
  ... | _ , hUnblock x xs refl , refl = (Recv , replyIdsNonEmpty) ∷ [] , _ , refl , vis refl done , idsR _ (x ∷ xs)
  ... | _ , hDone refl , refl = (Recv , doneK) ∷ [] , _ , refl , vis refl done , endR
  sim-ev (sendR {m} pr) st with out-inv k l d st
  ... | refl , refl = (Send , kind m) ∷ [] , _ , refl , vis pr done , backR _
  sim-ev (idsR s xs) st with out-inv k l d st
  ... | refl , refl = [] , _ , refl , done , backR s
  sim-ev (txsR s xs) st with out-inv k l d st
  ... | refl , refl = [] , _ , refl , done , backR s
  sim-ev (backR _) st = ⊥-elim (ret-noev k l d st)
  sim-ev endR st = ⊥-elim (ret-noev k l d st)

  -- The original requester is simulated by the certified wire machine.
  simulation : Br.Sim model cls id Rel
  simulation = record { sim-τ = sim-τ ; sim-ev = sim-ev }

  -- All finite original requester traces project to accepted control traces.
  sound : ∀ {t M es} → P.server k l d ⟹∖√⟨ t ⟩ M → Obs t es → HasTrace initial es
  sound {es = es} run o with Br.sound model cls id simulation (head P.awaitingInit) run
  ... | es′ , s′ , o′ , r , _ = s′ , subst (λ xs → initial ⇒⟨ xs ⟩ s′)
    (trans (sym (map-id es′)) (trans (sym o′) (trans o (map-id es)))) r

  -- An indexed FIFO makes both response-family heads available to inversion.
  data Queue : List P.Reply → List Reply → Set where
    emptyQ : Queue [] []
    idsQ : ∀ {q rs} → Queue q rs → Queue (P.ids ∷ q) (ids ∷ rs)
    txsQ : ∀ {q rs} → Queue q rs → Queue (P.txs ∷ q) (txs ∷ rs)

  -- Corresponding queues have equal occupancy.
  lengthQ : ∀ {q rs} → Queue q rs → length q ≡ length rs
  lengthQ emptyQ = refl
  lengthQ (idsQ qs) = cong suc (lengthQ qs)
  lengthQ (txsQ qs) = cong suc (lengthQ qs)

  -- Enqueueing an ID response preserves FIFO correspondence.
  snocIds : ∀ {q rs} → Queue q rs → Queue (q ∷ʳ P.ids) (rs ∷ʳ ids)
  snocIds emptyQ = idsQ emptyQ
  snocIds (idsQ qs) = idsQ (snocIds qs)
  snocIds (txsQ qs) = txsQ (snocIds qs)

  -- Enqueueing a transaction response preserves FIFO correspondence.
  snocTxs : ∀ {q rs} → Queue q rs → Queue (q ∷ʳ P.txs) (rs ∷ʳ txs)
  snocTxs emptyQ = txsQ emptyQ
  snocTxs (idsQ qs) = idsQ (snocTxs qs)
  snocTxs (txsQ qs) = txsQ (snocTxs qs)

  -- Canonical witnesses collect every completed reply immediately.
  data RelC : Proc → St → Set₁ where
    cInit : RelC (It′ (step k l d P.awaitingInit)) awaitingInit
    cHead : ∀ {q rs} → Queue q rs → RelC (It′ (step k l d (P.pending q 0))) (pending rs)
    cBlock : RelC (It′ (step k l d P.blocking)) blocking
    cEnd : RelC (It′ (Ret (inj₂ _))) closed

  -- A transaction ID is needed only to witness nonempty ID replies.
  module _ (h₀ : TxHash) where
    -- Replay contains no internal transitions.
    co-τ : ∀ {T s s′} → RelC T s → Replay._-τ→_ model s s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t [] × RelC T′ s′)
    co-τ _ ()

    -- Construct every control step using the original peer and its API.
    co-view : ∀ {T s s′ e} → RelC T s → V.View k s e s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
    co-view cInit V.start = _ , _ ,
      ∖√-ev (fire k l d (fire-Init k l d))
      (∖√-τ (back k l d) ∖√-refl) , refl , cHead emptyQ
    co-view (cHead emptyQ) V.block = _ , _ ,
      ∖√-ev (fire k l d (fire-Block k l d 0 1))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cBlock
    co-view (cHead {q} qs) (V.askIds lt) = _ , _ ,
      ∖√-ev (fire k l d (fire-Ids k l d {q = q} {c = 0} 0 1
        (subst (_< k) (sym (trans (+-identityʳ (length q)) (lengthQ qs))) lt)))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cHead (snocIds qs)
    co-view (cHead {q} qs) (V.askTxs lt) = _ , _ ,
      ∖√-ev (fire k l d (fire-Txs k l d {q = q} {c = 0} []
        (subst (_< k) (sym (trans (+-identityʳ (length q)) (lengthQ qs))) lt)))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cHead (snocTxs qs)
    co-view (cHead (idsQ qs)) V.emptyIds = _ , _ ,
      ∖√-ev (fire k l d (fire-ReplyIds k l d []))
      (∖√-ev (fire k l d out-fire)
      (∖√-τ (back k l d) (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl)))) , refl , cHead qs
    co-view (cHead (idsQ qs)) V.nonemptyIds = _ , _ ,
      ∖√-ev (fire k l d (fire-ReplyIds k l d (h₀ ∷ [])))
      (∖√-ev (fire k l d out-fire)
      (∖√-τ (back k l d) (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl)))) , refl , cHead qs
    co-view (cHead (txsQ qs)) V.transactions = _ , _ ,
      ∖√-ev (fire k l d (fire-ReplyTxs k l d []))
      (∖√-ev (fire k l d out-fire)
      (∖√-τ (back k l d) (∖√-τ (collect-fire k l d)
      (∖√-τ (back k l d) ∖√-refl)))) , refl , cHead qs
    co-view cBlock V.unblock = _ , _ ,
      ∖√-ev (fire k l d (fire-Unblock k l d h₀ []))
      (∖√-ev (fire k l d out-fire) (∖√-τ (back k l d) ∖√-refl)) , refl , cHead emptyQ
    co-view cBlock V.close = _ , _ ,
      ∖√-ev (fire k l d (fire-Done k l d)) ∖√-refl , refl , cEnd
    co-view cEnd ()

    -- The view is obtained from the existing function's successful update.
    co-ev : ∀ {T s s′ e} → RelC T s → ⊤ → Step s e s′ →
      Σ[ T′ ∈ Proc ] Σ[ t ∈ List Event ] (T ⟹∖√⟨ t ⟩ T′ × Obs t (e ∷ []) × RelC T′ s′)
    co-ev r _ pr = co-view r (V.view pr)

    -- Constructive co-simulation for every pipeline depth.
    cosimulation : Br.CoSim model cls id RelC (λ _ → ⊤)
    cosimulation = record { co-τ = co-τ ; co-ev = co-ev }

    -- Every accepted control trace has an original requester execution.
    complete : ∀ {es} → HasTrace initial es →
      ∃[ t ] ∃[ M ] (P.server k l d ⟹∖√⟨ t ⟩ M × Obs t es)
    complete {es} (_ , r) with Br.complete model cls id cosimulation
      cInit (universal (λ _ → tt) es) r
    ... | M , t , run , o , _ = t , M , run , o

    -- Exact finite control-trace correspondence, including k=0.
    bridge : ∀ {es} → HasTrace initial es ⇔
      (∃[ t ] ∃[ M ] (P.server k l d ⟹∖√⟨ t ⟩ M × Obs t es))
    bridge = mk⇔ complete (λ { (t , M , run , o) → sound run o })

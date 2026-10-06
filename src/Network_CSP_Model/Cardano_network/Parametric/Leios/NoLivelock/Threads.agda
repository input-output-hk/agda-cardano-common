{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C, premise (a): the THREAD summaries.  Each
-- read-pointer thread does a bounded number of events per round and reads
-- index k in round k, so it does at most D·B + D events on any trace whose
-- reads are all below B (`ptrLoop`).  Each TRIGGERED thread does at most
-- D events per trigger plus D (and plus the list weights its reports carry)
-- (`trigLoop`).  The EMISSION summaries bound the list weights and command
-- counts a thread puts on the api, for the far side's relays.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.Threads
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
open Topology tP using (Node)


open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; m≤m+n; m≤n+m; +-mono-≤; +-monoʳ-≤; +-identityʳ; +-assoc; n≤1+n)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ; length-++)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Class.DecEq using (DecEq; _≟_)
open import Class.DecEq.Instances using (DecEq-List)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Process_Trees using (ExtI; PTree)
open import Cardano_network.Base
open import Cardano_network.Parametric.Topology using (opposite)
open import Cardano_network.Net pP
open import Cardano_network.Data pP using (Payload; header; DecEq-TxsReply; DecEq-TxsRequest; DecEq-Offer; DecEq-EBPoint; DecEq-Header; DecEq-ChainRange)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import Cardano_network.Params using (module Params)
open Params pP using (decBlock; decVoteBlob; decTx; decEB; decTxHash; decEBHash; VoteBlob; Tx; TxHash; txHash; ebHash)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel; Event√; evl; √)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) using (loopStep)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload})
  using (DpW; Dp→DpW; DpW-mono; DpW-Ret; DpW-⟶; DpW-Output; DpW->>=; DpW-□; DpW-if; Dp-if; Dp-maybe′
        ; Ends-maybe′; AllT-if; AllT-maybe′; trigLoop; Σc-0; PfxW; Back; RoundPot; potIter; slack0
        ; labels-√; +-swap; ≤-≡)
open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) using (bind-elim-aux; bs-live; bs-term)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (loop; Prefix; Output; Ret; _>>=_)
open import Cardano_network.Parametric.Leios.NoLivelock.Weights pP using (cRep; cCmd; ℓRep; ℓCmd)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
open LeiosP pP using (allOffsets; DecEq-LeiosPoint)
open LeiosP.LeiosParams lpP using (ebTxs; rbCert)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic pP tP apiES using (serverBody-k; DecEq-Header×Tip; clientBody; clientBody-k; clientLoop; forgeEv; putEv)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic pP lpP tP apiES vo using ( serverBodyL; serverLoopL; lnServerBodyL; lnServerLoopL; ebIndexBody; ebIndex; voterBody; voter
        ; bodyOfferBody; bodyOfferLoop; awaitTxs; voteOfferBody; voteOfferLoop; tsServeBody; tsServe
        ; forgeL; forgeBodyL; forgeCertL; submit; certSink; lnClientBodyL; lnClientLoopL; fetchBody
        ; fetchTxs; putChecked; putAllVotes; ebServeBody; ebServeLoop; serveTxs; ebTxsServeBody
        ; ebTxsServeLoop; putAllTx; tsPullBody; tsPull; at?; getTxEv; putTxEv; putVoteEv; submitEv; certEv; memberOf; forgeOK; DecEq-⊤poly; DecEq-ℕ×ℕ )

------------------------------------------------------------------------
-- the thread
------------------------------------------------------------------------

-- the label is a read of the j-th oldest block … with j = k
IsGetAt : ℕ → Event → Set
IsGetAt k (evLabel _ (store _ _ (stGetAt j)) _) = j ≡ k
IsGetAt k _                                     = ⊥

-- the served round's tail has six events
sk-Dp : ∀ n l d b → Dp 6 (serverBody-k n l d b)
sk-Dp n l d b =
  Dp-⟶ _ (λ _ → Dp-Output _ _ (Dp-⟶ _ (λ _ → Dp-⟶ _ (λ _ → Dp-Output _ _ (Dp-⟶ _ (λ _ → Dp-Ret))))))

-- a whole round has eight
sb-Dp : ∀ n l d k → Dp 8 (loopStep {R = ⊤ {0ℓ}} (serverBodyL n l d) k)
sb-Dp n l d k =
  Dp->>= {m = 8} {n = 0} (Dp-⟶ _ (λ _ → Dp-⟶ _ (λ b → Dp->>= {m = 6} {n = 0} (sk-Dp n l d b) (λ _ → Dp-Ret))))
         (λ _ → Dp-Ret)

-- a completed round from pointer k read index k and advanced to k+1
sb-Cm : ∀ n l d k → Cm (IsGetAt k) (inj₁ (suc k)) (loopStep {R = ⊤ {0ℓ}} (serverBodyL n l d) k)
sb-Cm n l d k =
  Cm->>= {P = serverBodyL n l d k} (Cm-⟶ _ (λ _ → Cm-⟶-rd _ (λ _ → refl) (λ b → Ends->>= (λ _ → Ends-Ret)))) Ends-Ret

-- THE THREAD COUNT: at most 8·B + 8 events while every read is below B
serverLoopL-count : ∀ n l d B {s W} → serverLoopL n (l , d) ⟹⟨ s ⟩ W
                  → (∀ j → AnyE (IsGetAt j) s → j < B) → #e s ≤ 8 * B + 8
serverLoopL-count n l d B tr rb =
  ptrLoop {idx = λ k → k} {nxt = suc} (λ _ → refl) (sb-Dp n l (opposite d)) (sb-Cm n l (opposite d)) 0 tr rb

------------------------------------------------------------------------
-- the other read predicates and the trigger weights
------------------------------------------------------------------------

-- the label is a read of the k-th oldest vote blob
IsGetVoteAt : ℕ → Event → Set
IsGetVoteAt k (evLabel _ (store _ _ (stGetVoteAt j)) _) = j ≡ k
IsGetVoteAt k _                                         = ⊥

-- the label is a read of the k-th oldest mempool transaction
IsGetTxAt : ℕ → Event → Set
IsGetTxAt k (evLabel _ (store _ _ (stGetTxAt j)) _) = j ≡ k
IsGetTxAt k _                                       = ⊥

-- 1 on a forge (`envForge`, the trigger of `forgeL`)
cForge : Event → ℕ
cForge (evLabel _ (env _ _ envForge) _) = 1
cForge _                                = 0

-- 1 on a submission (`envSubmit`, the trigger of `submit`)
cSubmit : Event → ℕ
cSubmit (evLabel _ (env _ _ envSubmit) _) = 1
cSubmit _                                 = 0

-- 1 on a certificate (`stCert`, the trigger of `certSink`)
cCert : Event → ℕ
cCert (evLabel _ (store _ _ stCert) _) = 1
cCert _                                = 0

-- 1 on any of the four Notify reports (the triggers of the LN client)
cLnRep : Event → ℕ
cLnRep e = cRep lnpRecvBlockAnnouncement e + (cRep lnpRecvBlockOffer e + (cRep lnpRecvBlockTxsOffer e + cRep lnpRecvVotes e))

-- the lists the LN client's reports carry: tx-closure entries and vote blobs
ℓLnRep : Event → ℕ
ℓLnRep e = ℓRep lfpRecvBlockTxs e + ℓRep lnpRecvVotes e

------------------------------------------------------------------------
-- generic helpers (every thread is a `loop` at result `⊤`)
------------------------------------------------------------------------

-- a process tree over the node alphabet
Tr : Set → Set₁
Tr R = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R

-- the list instances the api outputs of `NodeLogicL` use (vote blobs, tx hashes, txs)
iVs : DecEq (List VoteBlob)
iVs = DecEq-List ⦃ decVoteBlob ⦄

-- … tx hashes
iHs : DecEq (List TxHash)
iHs = DecEq-List ⦃ decTxHash ⦄

-- … transactions
iTs : DecEq (List Tx)
iTs = DecEq-List ⦃ decTx ⦄

-- a per-label fact of every round holds along every loop trace
loopAll : ∀ {P : Event → Set} {A : Set} {body : A → Tr A}
        → (∀ a → AllT P (body a)) → ∀ a {s W} → loop {R = ⊤ {0ℓ}} body a ⟹⟨ s ⟩ W → AllL P (labels s)
loopAll {P} {body = body} ap a tr =
  invLoop (λ _ _ → ⊤ {0ℓ}) (λ _ → 0) (λ _ → P) (λ _ p → p) (λ {a} _ → AllT->>= (ap a) (λ _ → AllT-Ret))
          (λ {a} _ → Post->>= {Q₁ = λ _ _ → ⊤ {0ℓ}} {P = body a} (post λ _ → tt) (λ _ → Post-Ret tt)) {m = 0} tt tr

-- a label-wise bound adds up
Σc-≤ : ∀ {c d : Event → ℕ} {ls} → AllL (λ e → c e ≤ d e) ls → Σc c ls ≤ Σc d ls
Σc-≤ []      = z≤n
Σc-≤ (p ∷ a) = +-mono-≤ p (Σc-≤ a)

-- a weight that is at most one on every label is at most the event count
Σc1≤#e : ∀ {c : Event → ℕ} {R : Set} (s : List (Event√ R)) → AllL (λ e → c e ≤ 1) (labels s) → Σc c (labels s) ≤ #e s
Σc1≤#e []          []      = z≤n
Σc1≤#e (evl _ ∷ s) (p ∷ a) = +-mono-≤ p (Σc1≤#e s a)
Σc1≤#e (√ _ ∷ s)   a       = Σc1≤#e s a

-- a triggered loop whose rounds have plain depth D
trig0 : ∀ {A : Set} {body : A → Tr A} {D : ℕ} {cT : Event → ℕ}
      → (∀ a → Dp D (loopStep {R = ⊤ {0ℓ}} body a))
      → (∀ a → Post (λ ls _ → 1 ≤ Σc cT ls) (loopStep {R = ⊤ {0ℓ}} body a))
      → ∀ a {s W} → loop {R = ⊤ {0ℓ}} body a ⟹⟨ s ⟩ W → #e s ≤ D * Σc cT (labels s) + D
trig0 {D = D} {cT} dp tg a {s} tr =
  subst (#e s ≤_) (trans (cong (D * Σc cT (labels s) + D +_) (Σc-0 (labels s))) (+-identityʳ _))
    (trigLoop {w = λ _ → 0} (λ a → Dp→DpW (dp a)) tg a tr)

-- a body whose first event is a trigger
trig-hd : ∀ {cT : Event → ℕ} {A R : Set} (e : Net_Api Payload A) {P : A → Tr R}
        → (∀ x → 1 ≤ cT (evLabel A e x)) → Post (λ ls _ → 1 ≤ Σc cT ls) (e ⟶ P)
trig-hd e h = Post-⟶ e (λ x → post λ _ → ≤-trans (h x) (m≤m+n _ _))

-- the trigger of a body is the trigger of its round
trig-ls : ∀ {cT : Event → ℕ} {A : Set} {body : A → Tr A} a
        → Post (λ ls _ → 1 ≤ Σc cT ls) (body a) → Post (λ ls _ → 1 ≤ Σc cT ls) (loopStep {R = ⊤ {0ℓ}} body a)
trig-ls {cT} a p =
  Post->>= {Q₁ = λ ls _ → 1 ≤ Σc cT ls} p
    (λ {ls₁} q → Post-Ret (subst (λ ls → 1 ≤ Σc cT ls) (sym (++-identityʳ ls₁)) q))

------------------------------------------------------------------------
-- the list helpers: depth and per-label facts
------------------------------------------------------------------------

-- the closure gate of an EB holds at most one mempool read (the body table of `lpP`)
aw-Dp : ∀ n (h : Bool) {P : Tr ℕ} → Dp 1 P → Dp 2 (awaitTxs n (ebTxs h) P)
aw-Dp n true  p = Dp-⟶ _ (λ _ → p)
aw-Dp n false p = Dp-mono (n≤1+n 1) p

-- … and returns what its continuation returns
aw-Ends : ∀ n (h : Bool) {a : ℕ} {P : Tr ℕ} → Ends a P → Ends a (awaitTxs n (ebTxs h) P)
aw-Ends n true  p = Ends-⟶ _ (λ _ → p)
aw-Ends n false p = p

-- every label of the closure gate is a mempool read
aw-All : ∀ {P : Event → Set} n hs {Q : Tr ℕ} → (∀ h x → P (evLabel _ (getTxEv n h) x)) → AllT P Q → AllT P (awaitTxs n hs Q)
aw-All n []             p q = q
aw-All n ((h , _) ∷ hs) p q = AllT-⟶ (getTxEv n h) (p h) (λ _ → aw-All n hs p q)

-- a vote delivery deposits one blob per element
pav-Dp : ∀ n vs → Dp (length vs) (putAllVotes n vs)
pav-Dp n []       = Dp-Ret
pav-Dp n (v ∷ vs) = Dp-Output ⦃ decVoteBlob ⦄ _ _ (pav-Dp n vs)

-- every label of a vote delivery is a deposit
pav-All : ∀ {P : Event → Set} n → (∀ v → P (evLabel _ (putVoteEv n) v)) → ∀ vs → AllT P (putAllVotes n vs)
pav-All n p []       = AllT-Ret
pav-All n p (v ∷ vs) = AllT-Output ⦃ decVoteBlob ⦄ (putVoteEv n) v (p v) (pav-All n p vs)

-- a checked tx-closure reply deposits at most one transaction per entry
pc-Dp : ∀ n h es → Dp (length es) (putChecked n h es)
pc-Dp n h []              = Dp-Ret
pc-Dp n h ((o , t₁) ∷ es) with at? o (ebTxs h)
... | nothing      = Dp-mono (n≤1+n _) (pc-Dp n h es)
... | just (k , _) = Dp-if ⌊ DecEq._≟_ decTxHash (txHash t₁) k ⌋ (Dp-Output ⦃ decTx ⦄ _ _ (pc-Dp n h es)) (Dp-mono (n≤1+n _) (pc-Dp n h es))

-- every label of a checked reply is a deposit
pc-All : ∀ {P : Event → Set} n h → (∀ tx → P (evLabel _ (putTxEv n) tx)) → ∀ es → AllT P (putChecked n h es)
pc-All n h p []              = AllT-Ret
pc-All n h p ((o , t₁) ∷ es) with at? o (ebTxs h)
... | nothing      = pc-All n h p es
... | just (k , _) = AllT-if ⌊ DecEq._≟_ decTxHash (txHash t₁) k ⌋ (AllT-Output ⦃ decTx ⦄ (putTxEv n) t₁ (p t₁) (pc-All n h p es)) (pc-All n h p es)

-- a TxSubmission reply deposits at most one transaction per element
pat-Dp : ∀ n ids txs → Dp (length txs) (putAllTx n ids txs)
pat-Dp n ids []         = Dp-Ret
pat-Dp n ids (t₁ ∷ txs) = Dp-if (memberOf ⦃ decTxHash ⦄ (txHash t₁) ids) (Dp-Output ⦃ decTx ⦄ _ _ (pat-Dp n ids txs)) (Dp-mono (n≤1+n _) (pat-Dp n ids txs))

-- every label of a TxSubmission deposit is a deposit
pat-All : ∀ {P : Event → Set} n ids → (∀ tx → P (evLabel _ (putTxEv n) tx)) → ∀ txs → AllT P (putAllTx n ids txs)
pat-All n ids p []         = AllT-Ret
pat-All n ids p (t₁ ∷ txs) = AllT-if (memberOf ⦃ decTxHash ⦄ (txHash t₁) ids) (AllT-Output ⦃ decTx ⦄ (putTxEv n) t₁ (p t₁) (pat-All n ids p txs)) (pat-All n ids p txs)

-- serving a closure: at most one mempool read per offset, then the reply
st-Dp : ∀ n l d q os acc → Dp (suc (length os)) (serveTxs n l d q os acc)
st-Dp n l d q []       acc = Dp-Output ⦃ DecEq-TxsReply ⦄ _ _ Dp-Ret
st-Dp n l d q (o ∷ os) acc with at? o (ebTxs (proj₁ q))
... | nothing      = Dp-mono (n≤1+n _) (st-Dp n l d q os acc)
... | just (h , _) = Dp-⟶ _ (λ t₁ → st-Dp n l d q os _)

-- every label of a closure serve is a mempool read or the reply
st-All : ∀ {P : Event → Set} n l d q → (∀ h x → P (evLabel _ (getTxEv n h) x))
       → (∀ acc → P (evLabel _ (apiLP l d lfpSendBlockTxs) (q , acc))) → ∀ os acc → AllT P (serveTxs n l d q os acc)
st-All n l d q pg ps []       acc = AllT-Output ⦃ DecEq-TxsReply ⦄ (apiLP l d lfpSendBlockTxs) (q , acc) (ps acc) AllT-Ret
st-All n l d q pg ps (o ∷ os) acc with at? o (ebTxs (proj₁ q))
... | nothing      = st-All n l d q pg ps os acc
... | just (h , _) = AllT-⟶ (getTxEv n h) (pg h) (λ t₁ → st-All n l d q pg ps os _)

------------------------------------------------------------------------
-- the pointer threads
------------------------------------------------------------------------

-- THE LN ANNOUNCER COUNT: a read and an announcement per round
lnServerLoopL-count : ∀ n l d B {s W} → lnServerLoopL n (l , d) ⟹⟨ s ⟩ W
                    → (∀ j → AnyE (IsGetAt j) s → j < B) → #e s ≤ 2 * B + 2
lnServerLoopL-count n l d B tr rb =
  ptrLoop {body = lnServerBodyL n l (opposite d)} {idx = λ k → k} {nxt = suc} (λ _ → refl)
    (λ k → Dp->>= {m = 2} {n = 0} (Dp-⟶ _ (λ _ → Dp-Output ⦃ DecEq-Header ⦄ _ _ Dp-Ret)) (λ _ → Dp-Ret))
    (λ k → Cm->>= {P = lnServerBodyL n l (opposite d) k}
             (Cm-⟶-rd _ (λ _ → refl) (λ _ → Ends-Output ⦃ DecEq-Header ⦄ _ _ Ends-Ret)) Ends-Ret) 0 tr rb

-- THE EB-INDEX COUNT: a read and at most one entry per round
ebIndex-count : ∀ n B {s W} → ebIndex n ⟹⟨ s ⟩ W → (∀ j → AnyE (IsGetAt j) s → j < B) → #e s ≤ 2 * B + 2
ebIndex-count n B tr rb =
  ptrLoop {body = ebIndexBody n} {idx = λ k → k} {nxt = suc} (λ _ → refl)
    (λ k → Dp->>= {m = 2} {n = 0}
             (Dp-⟶ _ (λ b → Dp-maybe′ (λ _ → Dp-Output ⦃ DecEq-LeiosPoint ⦄ _ _ Dp-Ret) (Dp-mono z≤n Dp-Ret) b)) (λ _ → Dp-Ret))
    (λ k → Cm->>= {P = ebIndexBody n k}
             (Cm-⟶-rd _ (λ _ → refl) (λ b → Ends-maybe′ (λ _ → Ends-Output ⦃ DecEq-LeiosPoint ⦄ _ _ Ends-Ret) Ends-Ret b)) Ends-Ret) 0 tr rb

-- THE VOTER COUNT: a read, at most one body read and one vote per round
voter-count : ∀ n B {s W} → voter n ⟹⟨ s ⟩ W → (∀ j → AnyE (IsGetAt j) s → j < B) → #e s ≤ 3 * B + 3
voter-count n B tr rb =
  ptrLoop {body = voterBody n} {idx = λ k → k} {nxt = suc} (λ _ → refl)
    (λ k → Dp->>= {m = 3} {n = 0}
             (Dp-⟶ _ (λ b → Dp-maybe′ (λ _ → Dp-⟶ _ (λ _ → Dp-Output ⦃ decVoteBlob ⦄ _ _ Dp-Ret)) (Dp-mono z≤n Dp-Ret) b)) (λ _ → Dp-Ret))
    (λ k → Cm->>= {P = voterBody n k}
             (Cm-⟶-rd _ (λ _ → refl) (λ b → Ends-maybe′ (λ _ → Ends-⟶ _ (λ _ → Ends-Output ⦃ decVoteBlob ⦄ _ _ Ends-Ret)) Ends-Ret b))
             Ends-Ret) 0 tr rb

-- THE BODY-OFFER COUNT: read, body read, offer, at most one closure read, closure offer
bodyOfferLoop-count : ∀ n l d B {s W} → bodyOfferLoop n (l , d) ⟹⟨ s ⟩ W
                    → (∀ j → AnyE (IsGetAt j) s → j < B) → #e s ≤ 5 * B + 5
bodyOfferLoop-count n l d B tr rb =
  ptrLoop {body = bodyOfferBody n l (opposite d)} {idx = λ k → k} {nxt = suc} (λ _ → refl)
    (λ k → Dp->>= {m = 5} {n = 0}
             (Dp-⟶ _ (λ b → Dp-maybe′ (λ h → Dp-⟶ _ (λ _ → Dp-Output ⦃ DecEq-Offer ⦄ _ _ (aw-Dp n h (Dp-Output ⦃ DecEq-EBPoint ⦄ _ _ Dp-Ret))))
                                       (Dp-mono z≤n Dp-Ret) b))
             (λ _ → Dp-Ret))
    (λ k → Cm->>= {P = bodyOfferBody n l (opposite d) k}
             (Cm-⟶-rd _ (λ _ → refl) (λ b → Ends-maybe′ (λ h → Ends-⟶ _ (λ _ →
                Ends-Output ⦃ DecEq-Offer ⦄ _ _ (aw-Ends n h (Ends-Output ⦃ DecEq-EBPoint ⦄ _ _ Ends-Ret)))) Ends-Ret b))
             Ends-Ret) 0 tr rb

-- THE VOTE-OFFER COUNT: a blob read and its notification per round
voteOfferLoop-count : ∀ n l d B {s W} → voteOfferLoop n (l , d) ⟹⟨ s ⟩ W
                    → (∀ j → AnyE (IsGetVoteAt j) s → j < B) → #e s ≤ 2 * B + 2
voteOfferLoop-count n l d B tr rb =
  ptrLoop {body = voteOfferBody n l (opposite d)} {idx = λ k → k} {nxt = suc} (λ _ → refl)
    (λ k → Dp->>= {m = 2} {n = 0} (Dp-⟶ _ (λ _ → Dp-Output ⦃ iVs ⦄ _ _ Dp-Ret)) (λ _ → Dp-Ret))
    (λ k → Cm->>= {P = voteOfferBody n l (opposite d) k}
             (Cm-⟶-rd _ (λ _ → refl) (λ _ → Ends-Output ⦃ iVs ⦄ _ _ Ends-Ret)) Ends-Ret) 0 tr rb

-- THE TX-SERVE COUNT: five events per round, reading mempool index k in round k
tsServe-count : ∀ n l d B {s W} → tsServe n (l , d) ⟹⟨ s ⟩ W
              → (∀ j → AnyE (IsGetTxAt j) s → j < B) → #e s ≤ 5 * B + 5
tsServe-count n l d B tr rb =
  ptrLoop {body = tsServeBody n l d} {idx = λ k → k} {nxt = suc} (λ _ → refl)
    (λ k → Dp->>= {m = 5} {n = 0}
             (Dp-⟶ _ (λ _ → Dp-⟶ _ (λ _ → Dp-Output ⦃ iHs ⦄ _ _ (Dp-⟶ _ (λ _ → Dp-Output ⦃ iTs ⦄ _ _ Dp-Ret))))) (λ _ → Dp-Ret))
    (λ k → Cm->>= {P = tsServeBody n l d k}
             (Cm-⟶ _ (λ _ → Cm-⟶-rd _ (λ _ → refl) (λ _ →
                Ends-Output ⦃ iHs ⦄ _ _ (Ends-⟶ _ (λ _ → Ends-Output ⦃ iTs ⦄ _ _ Ends-Ret))))) Ends-Ret) 0 tr rb

------------------------------------------------------------------------
-- the triggered threads
------------------------------------------------------------------------

-- THE FORGE COUNT: at most four events per forge
forgeL-count : ∀ n {s W} → forgeL n ⟹⟨ s ⟩ W → #e s ≤ 4 * Σc cForge (labels s) + 4
forgeL-count n =
  trig0 (λ _ → Dp->>= {m = 4} {n = 0}
                 (Dp-⟶ _ (λ { (me , b) → Dp-if (forgeOK (me , b)) (Dp-maybe′ (λ _ → Dp-Output ⦃ decEB ⦄ _ _ (fc b)) (Dp-mono (n≤1+n 2) (fc b)) me)
                                                 (Dp-mono z≤n Dp-Ret) }))
                 (λ _ → Dp-Ret))
        (λ _ → trig-ls tt (trig-hd (forgeEv n) (λ _ → ≤-refl))) tt
  where
    -- the certificate half of a pass: at most two events
    fc : ∀ b → Dp 2 (forgeCertL n b)
    fc b = Dp-maybe′ (λ _ → Dp-⟶ _ (λ _ → Dp-Output ⦃ decBlock ⦄ _ _ Dp-Ret)) (Dp-mono z≤n Dp-Ret) (rbCert b)

-- THE SUBMISSION COUNT: two events per submission
submit-count : ∀ n {s W} → submit n ⟹⟨ s ⟩ W → #e s ≤ 2 * Σc cSubmit (labels s) + 2
submit-count n =
  trig0 (λ _ → Dp->>= {m = 2} {n = 0} (Dp-⟶ _ (λ _ → Dp-Output ⦃ decTx ⦄ _ _ Dp-Ret)) (λ _ → Dp-Ret))
        (λ _ → trig-ls tt (trig-hd (submitEv n) (λ _ → ≤-refl))) tt

-- THE CERTIFICATE-SINK COUNT: one event per certificate
certSink-count : ∀ n {s W} → certSink n ⟹⟨ s ⟩ W → #e s ≤ 1 * Σc cCert (labels s) + 1
certSink-count n =
  trig0 (λ _ → Dp->>= {m = 1} {n = 0} (Dp-⟶ _ (λ _ → Dp-Ret)) (λ _ → Dp-Ret))
        (λ _ → trig-ls tt (trig-hd (certEv n) (λ _ → ≤-refl))) tt

-- THE CHAINSYNC CLIENT COUNT: five events per RollForward report
clientLoop-count : ∀ n l d {s W} → clientLoop n (l , d) ⟹⟨ s ⟩ W
                 → #e s ≤ 5 * Σc (cRep recvCSRollforward) (labels s) + 5
clientLoop-count n l d =
  trig0 (λ _ → Dp->>= {m = 5} {n = 0} (Dp-⟶ _ (λ _ → Dp-⟶ _ ck)) (λ _ → Dp-Ret))
        (λ _ → trig-ls tt (Post-⟶ (apiCS l d sendCSRequestNext) (λ _ →
                 trig-hd (apiCS l d recvCSRollforward) (λ _ → ≤-refl)))) tt
  where
    -- the fetch half of a round: at most three events
    ck : ∀ ht → Dp 3 (clientBody-k n l d ht)
    ck (header b , _) = Dp-Output ⦃ DecEq-ChainRange ⦄ _ _ (Dp-⟶ _ (λ _ → Dp-Output ⦃ decBlock ⦄ _ _ Dp-Ret))

-- THE LN CLIENT COUNT: five events per Notify report, plus one per delivered list entry
lnClientLoopL-count : ∀ n l d {s W} → lnClientLoopL n (l , d) ⟹⟨ s ⟩ W
                    → #e s ≤ 5 * Σc cLnRep (labels s) + 5 + Σc ℓLnRep (labels s)
lnClientLoopL-count n l d =
  trigLoop
    (λ _ → DpW->>= {m = 5} {n = 0}
      (DpW-⟶ (apiLP l d lnpSendRequestNext) (λ _ →
         DpW-□ (DpW-⟶ (apiLP l d lnpRecvBlockAnnouncement) (λ _ → DpW-Ret))
        (DpW-□ (DpW-⟶ (apiLP l d lnpRecvBlockOffer) (λ { (q , _) → Dp→DpW
                  (Dp-Output ⦃ DecEq-EBPoint ⦄ _ _ (Dp-⟶ _ (λ eb → Dp-if ⌊ DecEq._≟_ decEBHash (ebHash eb) (proj₁ q) ⌋ (Dp-Output ⦃ decEB ⦄ _ _ Dp-Ret) (Dp-mono z≤n Dp-Ret)))) }))
        (DpW-□ (DpW-⟶ (apiLP l d lnpRecvBlockTxsOffer) (λ q → DpW-⟶ _ (λ _ → DpW-Output ⦃ DecEq-TxsRequest ⦄ _ _
                  (DpW-⟶ _ (λ { (q′ , es) → DpW-if ⌊ DecEq._≟_ DecEq-EBPoint q′ q ⌋ (DpW-mono (m≤m+n _ 0) (Dp→DpW (pc-Dp n (proj₁ q) es))) DpW-Ret })))))
               (DpW-⟶ (apiLP l d lnpRecvVotes) (λ vs → DpW-mono (m≤n+m _ 3) (Dp→DpW (pav-Dp n vs))))))))
      (λ _ → DpW-Ret))
    (λ _ → trig-ls tt (Post-⟶ (apiLP l d lnpSendRequestNext) (λ _ →
       Post-□ (trig-hd (apiLP l d lnpRecvBlockAnnouncement) (λ _ → ≤-refl))
      (Post-□ (trig-hd (apiLP l d lnpRecvBlockOffer) (λ _ → ≤-refl))
      (Post-□ (trig-hd (apiLP l d lnpRecvBlockTxsOffer) (λ _ → ≤-refl))
              (trig-hd (apiLP l d lnpRecvVotes) (λ _ → ≤-refl))))))) tt

-- THE EB-SERVE COUNT: three events per body request
ebServeLoop-count : ∀ n l d {s W} → ebServeLoop n (l , d) ⟹⟨ s ⟩ W
                  → #e s ≤ 3 * Σc (cRep lfpReqBlockRequest) (labels s) + 3
ebServeLoop-count n l d =
  trig0 (λ _ → Dp->>= {m = 3} {n = 0} (Dp-⟶ _ (λ _ → Dp-⟶ _ (λ _ → Dp-Output ⦃ decEB ⦄ _ _ Dp-Ret))) (λ _ → Dp-Ret))
        (λ _ → trig-ls tt (trig-hd (apiLP l (opposite d) lfpReqBlockRequest) (λ _ → ≤-refl))) tt

-- THE CLOSURE-SERVE COUNT: three events per closure request, plus one per requested offset
ebTxsServeLoop-count : ∀ n l d {s W} → ebTxsServeLoop n (l , d) ⟹⟨ s ⟩ W
                     → #e s ≤ 3 * Σc (cRep lfpReqBlockTxsRequest) (labels s) + 3
                             + Σc (ℓRep lfpReqBlockTxsRequest) (labels s)
ebTxsServeLoop-count n l d =
  trigLoop
    (λ _ → DpW->>= {m = 3} {n = 0}
      (DpW-⟶ (apiLP l (opposite d) lfpReqBlockTxsRequest) (λ { (q , bm) →
         DpW-⟶ _ (λ _ → DpW-mono (m≤m+n _ 0) (Dp→DpW (st-Dp n l (opposite d) q bm []))) }))
      (λ _ → DpW-Ret))
    (λ _ → trig-ls tt (trig-hd (apiLP l (opposite d) lfpReqBlockTxsRequest) (λ _ → ≤-refl))) tt

-- THE TX-PULL COUNT: four events per id reply, plus one per delivered transaction
tsPull-count : ∀ n l d {s W} → tsPull n (l , d) ⟹⟨ s ⟩ W
             → #e s ≤ 4 * Σc (cRep recvTSReplyTxIds) (labels s) + 4 + Σc (ℓRep recvTSReplyTxs) (labels s)
tsPull-count n l d =
  trigLoop
    (λ _ → DpW->>= {m = 4} {n = 0}
      (DpW-Output ⦃ DecEq-ℕ×ℕ ⦄ _ _ (DpW-⟶ _ (λ ids → DpW-Output ⦃ iHs ⦄ _ _ (DpW-⟶ _ (λ txs → Dp→DpW (pat-Dp n ids txs))))))
      (λ _ → DpW-Ret))
    (λ _ → trig-ls tt (Post-Output ⦃ DecEq-ℕ×ℕ ⦄ (apiTS l (opposite d) sendTSRequestTxIdsBlocking) _
             (trig-hd (apiTS l (opposite d) recvTSReplyTxIds) (λ _ → ≤-refl)))) tt

------------------------------------------------------------------------
-- emission summaries (what a thread hands its peers, for the far side's relays)
------------------------------------------------------------------------

-- an EB's body table (in `lpP`) has at most one entry, so `allOffsets` has at most one offset
ao≤1 : ∀ h → length (allOffsets lpP h) ≤ 1
ao≤1 true  = ≤-refl
ao≤1 false = z≤n

-- a vote notification carries one blob
voteOffer-emits : ∀ n l d {s W} → voteOfferLoop n (l , d) ⟹⟨ s ⟩ W
                → Σc (ℓCmd lnpSendVotes) (labels s) ≤ Σc (cCmd lnpSendVotes) (labels s)
voteOffer-emits n l d tr =
  Σc-≤ (loopAll {body = voteOfferBody n l (opposite d)}
          (λ k → AllT-⟶ _ (λ _ → z≤n) (λ _ → AllT-Output ⦃ iVs ⦄ _ _ ≤-refl AllT-Ret)) 0 tr)

-- an id reply carries one hash and a tx reply one transaction; and the id replies are
-- commands of this thread
tsServe-emits : ∀ n l d {s W} → tsServe n (l , d) ⟹⟨ s ⟩ W
              → Σc (ℓCmd sendTSReplyTxIds) (labels s) ≤ Σc (cCmd sendTSReplyTxIds) (labels s)
              × Σc (ℓCmd sendTSReplyTxs) (labels s) ≤ Σc (cCmd sendTSReplyTxs) (labels s)
              × Σc (cCmd sendTSReplyTxIds) (labels s) ≤ #e s
tsServe-emits n l d {s} tr = Σc-≤ (AllL-map proj₁ a) , Σc-≤ (AllL-map (λ p → proj₁ (proj₂ p)) a)
                           , Σc1≤#e s (AllL-map (λ p → proj₂ (proj₂ p)) a)
  where
    -- every label, three facts at once
    a = loopAll {P = λ e → ℓCmd sendTSReplyTxIds e ≤ cCmd sendTSReplyTxIds e
                         × ℓCmd sendTSReplyTxs e ≤ cCmd sendTSReplyTxs e × cCmd sendTSReplyTxIds e ≤ 1}
                {body = tsServeBody n l d}
          (λ k → AllT-⟶ _ (λ _ → z≤n , z≤n , z≤n) (λ _ → AllT-⟶ _ (λ _ → z≤n , z≤n , z≤n) (λ _ →
                   AllT-Output ⦃ iHs ⦄ _ _ (≤-refl , z≤n , ≤-refl) (AllT-⟶ _ (λ _ → z≤n , z≤n , z≤n) (λ _ →
                   AllT-Output ⦃ iTs ⦄ _ _ (z≤n , ≤-refl , z≤n) AllT-Ret))))) 0 tr

-- a closure request carries at most one offset (the body table of `lpP`); and the body
-- and closure requests are commands of this thread
fetchTxs-emits : ∀ n l d {s W} → lnClientLoopL n (l , d) ⟹⟨ s ⟩ W
               → Σc (ℓCmd lfpSendBlockTxsRequest) (labels s) ≤ Σc (cCmd lfpSendBlockTxsRequest) (labels s)
               × Σc (cCmd lfpSendBlockRequest) (labels s) ≤ #e s
               × Σc (cCmd lfpSendBlockTxsRequest) (labels s) ≤ #e s
fetchTxs-emits n l d {s} tr = Σc-≤ (AllL-map proj₁ a) , Σc1≤#e s (AllL-map (λ p → proj₁ (proj₂ p)) a)
                            , Σc1≤#e s (AllL-map (λ p → proj₂ (proj₂ p)) a)
  where
    -- every label, three facts at once
    a = loopAll {P = λ e → ℓCmd lfpSendBlockTxsRequest e ≤ cCmd lfpSendBlockTxsRequest e
                         × cCmd lfpSendBlockRequest e ≤ 1 × cCmd lfpSendBlockTxsRequest e ≤ 1}
                {body = λ _ → lnClientBodyL n l d}
          (λ _ → AllT-⟶ (apiLP l d lnpSendRequestNext) (λ _ → z≤n , z≤n , z≤n) (λ _ →
             AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockAnnouncement) (λ _ → z≤n , z≤n , z≤n) (λ _ → AllT-Ret))
            (AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockOffer) (λ _ → z≤n , z≤n , z≤n) (λ { (q , _) →
                       AllT-Output ⦃ DecEq-EBPoint ⦄ _ _ (z≤n , ≤-refl , z≤n) (AllT-⟶ _ (λ _ → z≤n , z≤n , z≤n) (λ eb →
                       AllT-if ⌊ DecEq._≟_ decEBHash (ebHash eb) (proj₁ q) ⌋ (AllT-Output ⦃ decEB ⦄ _ _ (z≤n , z≤n , z≤n) AllT-Ret) AllT-Ret)) }))
            (AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockTxsOffer) (λ _ → z≤n , z≤n , z≤n) (λ q →
                       AllT-⟶ _ (λ _ → z≤n , z≤n , z≤n) (λ _ →
                       AllT-Output ⦃ DecEq-TxsRequest ⦄ _ _ (ao≤1 (proj₁ q) , z≤n , ≤-refl) (AllT-⟶ _ (λ _ → z≤n , z≤n , z≤n) (λ { (q′ , es) →
                       AllT-if ⌊ DecEq._≟_ DecEq-EBPoint q′ q ⌋ (pc-All n (proj₁ q) (λ _ → z≤n , z≤n , z≤n) es) AllT-Ret })))))
                    (AllT-⟶ (apiLP l d lnpRecvVotes) (λ _ → z≤n , z≤n , z≤n)
                       (λ vs → pav-All n (λ _ → z≤n , z≤n , z≤n) vs)))))) tt tr

-- a free prefix whose value is credited to the rest (`CountMore.PfxW`)
PfxW-⟶ : ∀ {c d : Event → ℕ} {k} {A R : Set} (e : Net_Api Payload A) {P : A → Tr R}
       → (∀ x → c (evLabel A e x) ≡ 0) → (∀ x → PfxW c d (d (evLabel A e x) + k) (P x)) → PfxW c d k (e ⟶ P)
PfxW-⟶ {c} {d} {k} {A} e z p tr with pfx-tr tr
... | inj₁ refl                   = z≤n
... | inj₂ (x , s′ , refl , rest) rewrite z x =
      ≤-trans (p x rest) (≤-≡ (trans (+-swap (Σc d (labels s′)) (d (evLabel A e x)) k)
                                         (sym (+-assoc (d (evLabel A e x)) (Σc d (labels s′)) k))))

-- an output that pays at most k, then a return
PfxW-Out : ∀ {c d : Event → ℕ} {k} {A R : Set} ⦃ _ : DecEq A ⦄ (e : Net_Api Payload A) (v : A) {x : R}
         → c (evLabel A e v) ≤ k → PfxW c d k (e ! v ⟶ Ret x)
PfxW-Out {c} {d} {k} {A} e v h tr with out-tr tr
... | inj₁ refl = z≤n
... | inj₂ (s′ , refl , rest) with Ret-tr rest
...   | inj₁ refl = ≤-trans (≤-≡ (+-identityʳ _)) (≤-trans h (m≤n+m k _))
...   | inj₂ refl = ≤-trans (≤-≡ (+-identityʳ _)) (≤-trans h (m≤n+m k _))

-- the trace of a return has no label
RetL : ∀ {R : Set} {x : R} {s W} → Ret x ⟹⟨ s ⟩ W → labels s ≡ []
RetL tr with Ret-tr tr
... | inj₁ refl = refl
... | inj₂ refl = refl

-- a round: the loop-back adds no label
PfxW->>=Ret : ∀ {c d : Event → ℕ} {k} {R S : Set} {P : Tr R} {f : R → S}
            → PfxW c d k P → PfxW c d k (P >>= λ r → Ret (f r))
PfxW->>=Ret {c} {d} {k} {P = P} {f} p tr with bind-elim-aux P (λ r → Ret (f r)) tr
... | bs-live tP eo = subst (λ ls → Σc c ls ≤ Σc d ls + k) (labels-EvlOnly eo) (p tP)
... | bs-term {sS = sS} {s_k = s_k} tP fr eo (_ , kt) refl =
      subst (λ ls → Σc c ls ≤ Σc d ls + k)
        (sym (trans (labels-++ sS s_k) (trans (cong (labels sS ++_) (RetL kt)) (++-identityʳ (labels sS)))))
        (subst (λ ls → Σc c ls ≤ Σc d ls + k) (labels-EvlOnly eo) (p tP))

-- a round that never overspends is a potential round without potential
pfx→rp : ∀ {c d : Event → ℕ} {A Rx : Set} {a : A} {t : Tr (A ⊎ Rx)}
       → PfxW c d 0 t → RoundPot {Φ = λ _ → 0} {cost = c} {credit = d} {K = 0} a t
pfx→rp {c} {d} {a = a} p = p , post λ {s} {x} tr → bk x (subst (λ ls → Σc c ls ≤ Σc d ls + 0) (labels-√ s) (p tr))
  where
    -- the drop check, from the bound
    bk : ∀ x {ls} → Σc c ls ≤ Σc d ls + 0 → Back (λ _ → 0) c d a ls x
    bk (inj₁ _) h = ≤-trans (≤-≡ (+-identityʳ _)) h
    bk (inj₂ _) h = U.tt

-- serving a closure from `acc`: the reply pays at most |acc| + |os| out of the budget
st-Pfx : ∀ n l d q os acc k → length acc + length os ≤ k
       → PfxW (ℓCmd lfpSendBlockTxs) (ℓRep lfpReqBlockTxsRequest) k (serveTxs n l d q os acc)
st-Pfx n l d q []       acc k h = PfxW-Out ⦃ DecEq-TxsReply ⦄ _ _ (≤-trans (m≤m+n _ 0) h)
st-Pfx n l d q (o ∷ os) acc k h with at? o (ebTxs (proj₁ q))
... | nothing      = st-Pfx n l d q os acc k (≤-trans (+-monoʳ-≤ (length acc) (n≤1+n _)) h)
... | just (x , _) = PfxW-⟶ _ (λ _ → refl) (λ t₁ → st-Pfx n l d q os _ k
                       (subst (_≤ k) (sym (trans (cong (_+ length os) (length-++ acc)) (+-assoc (length acc) 1 (length os)))) h))

-- a closure reply carries at most as many entries as the request had offsets
serveTxs-emits : ∀ n l d {s W} → ebTxsServeLoop n (l , d) ⟹⟨ s ⟩ W
               → Σc (ℓCmd lfpSendBlockTxs) (labels s) ≤ Σc (ℓRep lfpReqBlockTxsRequest) (labels s)
serveTxs-emits n l d {s} tr =
  slack0 {ℓCmd lfpSendBlockTxs} {ℓRep lfpReqBlockTxsRequest} {labels s} (potIter (λ _ → 0) (ℓCmd lfpSendBlockTxs) (ℓRep lfpReqBlockTxsRequest) 0
    (λ _ → pfx→rp (PfxW->>=Ret (PfxW-⟶ (apiLP l (opposite d) lfpReqBlockTxsRequest) (λ _ → refl) (λ { (q , bm) →
             PfxW-⟶ _ (λ _ → refl) (λ _ → st-Pfx n l (opposite d) q bm [] _ (m≤m+n _ 0)) })))) tt tr)

-- the RollForward announcements are commands of the ChainSync server thread
serverLoopL-cmd : ∀ n l d {s W} → serverLoopL n (l , d) ⟹⟨ s ⟩ W → Σc (cCmd sendCSRollForward) (labels s) ≤ #e s
serverLoopL-cmd n l d {s} tr =
  Σc1≤#e s (loopAll {body = serverBodyL n l (opposite d)}
              (λ k → AllT-⟶ _ (λ _ → z≤n) (λ _ → AllT-⟶ _ (λ _ → z≤n) (λ b → AllT->>= (sk b) (λ _ → AllT-Ret)))) 0 tr)
  where
    -- the serve half of a round: one RollForward
    sk : ∀ b → AllT (λ e → cCmd sendCSRollForward e ≤ 1) (serverBody-k n l (opposite d) b)
    sk b = AllT-⟶ _ (λ _ → z≤n) (λ _ → AllT-Output _ _ ≤-refl (AllT-⟶ _ (λ _ → z≤n) (λ _ →
             AllT-⟶ _ (λ _ → z≤n) (λ _ → AllT-Output _ _ z≤n (AllT-⟶ _ (λ _ → z≤n) (λ _ → AllT-Ret))))))

-- the block announcements are commands of the LN announcer
lnServerLoopL-cmd : ∀ n l d {s W} → lnServerLoopL n (l , d) ⟹⟨ s ⟩ W
                  → Σc (cCmd lnpSendBlockAnnouncement) (labels s) ≤ #e s
lnServerLoopL-cmd n l d {s} tr =
  Σc1≤#e s (loopAll {body = lnServerBodyL n l (opposite d)}
              (λ k → AllT-⟶ _ (λ _ → z≤n) (λ _ → AllT-Output ⦃ DecEq-Header ⦄ _ _ ≤-refl AllT-Ret)) 0 tr)

-- the body and closure offers are commands of the body offerer
bodyOfferLoop-cmd : ∀ n l d {s W} → bodyOfferLoop n (l , d) ⟹⟨ s ⟩ W
                  → Σc (cCmd lnpSendBlockOffer) (labels s) ≤ #e s × Σc (cCmd lnpSendBlockTxsOffer) (labels s) ≤ #e s
bodyOfferLoop-cmd n l d {s} tr = Σc1≤#e s (AllL-map proj₁ a) , Σc1≤#e s (AllL-map proj₂ a)
  where
    -- every label, both facts at once
    a = loopAll {P = λ e → cCmd lnpSendBlockOffer e ≤ 1 × cCmd lnpSendBlockTxsOffer e ≤ 1}
                {body = bodyOfferBody n l (opposite d)}
          (λ k → AllT-⟶ _ (λ _ → z≤n , z≤n) (λ b → AllT-maybe′ (λ h → AllT-⟶ _ (λ _ → z≤n , z≤n) (λ _ →
                   AllT-Output ⦃ DecEq-Offer ⦄ _ _ (≤-refl , z≤n) (aw-All n (ebTxs h) (λ _ _ → z≤n , z≤n)
                     (AllT-Output ⦃ DecEq-EBPoint ⦄ _ _ (z≤n , ≤-refl) AllT-Ret)))) AllT-Ret b)) 0 tr

------------------------------------------------------------------------
-- Task 9a (F1): the LN client's closure requests are bounded by the closure
-- OFFERS it was told about (one request per `lnpRecvBlockTxsOffer` round),
-- not by its own event count — `fetchTxs-emits`'s `≤ #e s` closes a
-- self-loop through the entries those requests bring back
------------------------------------------------------------------------

open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_□_)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono (Net_Api-≟ {Payload}) using (□-trace-elim)

-- a choice pays what its branches pay
PfxW-□ : ∀ {c d : Event → ℕ} {k} {R : Set} ⦃ _ : DecEq R ⦄ {P Q : Tr R}
       → PfxW c d k P → PfxW c d k Q → PfxW c d k (P □ Q)
PfxW-□ {P = P} {Q} p q tr with □-trace-elim P Q tr
... | inj₁ (_ , t) = p t
... | inj₂ (_ , t) = q t

-- a tree that never pays pays at most anything
PfxW-0 : ∀ {c d : Event → ℕ} {k} {R : Set} {t : Tr R} → AllT (λ e → c e ≤ 0) t → PfxW c d k t
PfxW-0 {c} {d} {k} a {s} tr =
  ≤-trans (Σc-≤ (a tr)) (≤-trans (≤-≡ (Σc-0 (labels s))) z≤n)

-- an output paying at most k, then a tree that never pays
PfxW-Out0 : ∀ {c d : Event → ℕ} {k} {A R : Set} ⦃ _ : DecEq A ⦄ (e : Net_Api Payload A) (v : A) {P : Tr R}
          → c (evLabel A e v) ≤ k → AllT (λ e → c e ≤ 0) P → PfxW c d k (e ! v ⟶ P)
PfxW-Out0 {c} {d} {k} {A} e v h a tr with out-tr tr
... | inj₁ refl               = z≤n
... | inj₂ (s′ , refl , rest) =
      ≤-trans (+-mono-≤ h (≤-trans (Σc-≤ (a rest)) (≤-≡ (Σc-0 (labels s′)))))
              (≤-trans (≤-≡ (+-identityʳ k)) (m≤n+m k _))

-- THE CLOSURE-REQUEST RELAY: every closure request answers a closure offer report
fetchTxs-req : ∀ n l d {s W} → lnClientLoopL n (l , d) ⟹⟨ s ⟩ W
             → Σc (cCmd lfpSendBlockTxsRequest) (labels s) ≤ Σc (cRep lnpRecvBlockTxsOffer) (labels s)
fetchTxs-req n l d {s} tr =
  slack0 {cCmd lfpSendBlockTxsRequest} {cRep lnpRecvBlockTxsOffer} {labels s}
    (potIter (λ _ → 0) (cCmd lfpSendBlockTxsRequest) (cRep lnpRecvBlockTxsOffer) 0 (λ _ → pfx→rp (PfxW->>=Ret rnd)) tt tr)
  where
    -- one round: only the closure-offer arm requests, once, after its report
    rnd : PfxW (cCmd lfpSendBlockTxsRequest) (cRep lnpRecvBlockTxsOffer) 0 (lnClientBodyL n l d)
    rnd = PfxW-⟶ (apiLP l d lnpSendRequestNext) (λ _ → refl) (λ _ →
       PfxW-□ (PfxW-0 (AllT-⟶ (apiLP l d lnpRecvBlockAnnouncement) (λ _ → z≤n) (λ _ → AllT-Ret)))
      (PfxW-□ (PfxW-0 (AllT-⟶ (apiLP l d lnpRecvBlockOffer) (λ _ → z≤n) (λ { (q , _) →
                 AllT-Output ⦃ DecEq-EBPoint ⦄ _ _ z≤n (AllT-⟶ _ (λ _ → z≤n) (λ eb →
                 AllT-if ⌊ DecEq._≟_ decEBHash (ebHash eb) (proj₁ q) ⌋ (AllT-Output ⦃ decEB ⦄ _ _ z≤n AllT-Ret) AllT-Ret)) })))
      (PfxW-□ (PfxW-⟶ (apiLP l d lnpRecvBlockTxsOffer) (λ _ → refl) (λ q → PfxW-⟶ _ (λ _ → refl) (λ _ →
                 PfxW-Out0 ⦃ DecEq-TxsRequest ⦄ _ _ ≤-refl (AllT-⟶ _ (λ _ → z≤n) (λ { (q′ , es) →
                 AllT-if ⌊ DecEq._≟_ DecEq-EBPoint q′ q ⌋ (pc-All n (proj₁ q) (λ _ → z≤n) es) AllT-Ret })))))
              (PfxW-0 (AllT-⟶ (apiLP l d lnpRecvVotes) (λ _ → z≤n) (λ vs → pav-All n (λ _ → z≤n) vs))))))

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C, premise (b): the NODE-LOGIC leaves of
-- `τ-AccReach rawSys2` (also `rawL`, Stage L) — every thread and every store of `nodeLogicL` is
-- modulo-∅ accessible at every reachable state (`MAccR ∅ES`), via the
-- Stage-G guarded-loop lemma `MAccR-loop` (rounds start visibly) and the
-- leaf closures (`MAccR-⟶`, `MAccR-Output`, `MAccR-□`, `MAccR->>=`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.TauLogic
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
open Topology tP using (Node)


open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; reverse)
open import Data.List.Relation.Unary.All using (universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.Maybe using (just; nothing)
open import Data.Bool using (not; _∧_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Net pP
open import Cardano_network.Data pP using (Payload)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (∅ES; Stop)
open import CSP.Laws.DivFree.ModAcc (Net_Api-≟ {Payload}) using (MAccR; MAccR→τ-AccReach; MAccR-mono)
open import CSP.Laws.DivFree.Reach (Net_Api-≟ {Payload}) using (MAccR-Ret; MAccR-Skip; MAccR-∥; MAccR-⦀; MAccR-⦀⁺)
open import CSP.Laws.DivFree.ReachExtra (Net_Api-≟ {Payload}) using (MAccR-if; MAccR-maybe′)
open import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload})
  using (Guarded; Guarded-react; Guarded-⟶-vis; Guarded-Output-vis
        ; MAccR-⟶; MAccR-⟶₀; MAccR-Output; MAccR->>=; MAccR-loop; MAccR-loop0; MAccR-Stop)
open import CSP.Laws.DivFree.ReachChoice (Net_Api-≟ {Payload}) using (MAccR-□; Guarded-□)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic pP tP apiES using (serverBody-k; offerHeld; DecEq-Header×Tip; clientLoop; clientBody-k; storeES)
open import Cardano_network.Data pP using (header; DecEq-ChainRange; DecEq-Header; DecEq-EBPoint; DecEq-TxsRequest; DecEq-TxsReply; DecEq-Offer)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
open LeiosP pP using (DecEq-LeiosPoint)
open LeiosP.LeiosParams lpP using (ebTxs; certifies)
open import Cardano_network.Parametric.Topology using (module Topology)
open Topology tP using (endpointsOf)
open import Cardano_network.Params using (module Params)
open Params pP using (decBlock; decEBHash; decTxHash; decRbHash; decVoteBlob; announcedEB)
import Class.DecEq.Instances as DecEqI
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic pP lpP tP apiES vo
  using (nodeLogicL; st₀; serverBodyL; serverLoopL; storeStepL; blockStoreL; offerIx
        ; DecEq-⊤poly; DecEq-Votes; DecEq-ℕ×ℕ; at?; memberOf
        ; forgeL; forgeOK; forgeBodyL; forgeCertL; ebIndex; ebIndexBody; voter; voterBody; submit; certSink
        ; lnServerLoopL; lnServerBodyL; awaitTxs; bodyOfferBody; bodyOfferLoop
        ; voteOfferBody; voteOfferLoop; fetchBody; putChecked; fetchTxs; putAllVotes
        ; lnClientBodyL; lnClientLoopL; ebServeBody; ebServeLoop; serveTxs; ebTxsServeBody
        ; ebTxsServeLoop; putAllTx; tsPullBody; tsPull; tsServeBody; tsServe
        ; ebStep; ebStore; bodyStep; offerBodies; bodyStore; memStep; offerTxs; mempool
        ; certify; offerCerts; voteStep; voteStore; endpointThreadsL; allThreadsL)

------------------------------------------------------------------------
-- a thread: the ChainSync server's read-pointer loop
------------------------------------------------------------------------

-- the served round's tail is accessible everywhere
sk-R : ∀ n l d b → MAccR ∅ES (serverBody-k n l d b)
sk-R n l d b =
  MAccR-⟶₀ _ (MAccR-Output _ _ (MAccR-⟶ _ (λ _ →
    MAccR-⟶₀ _ (MAccR-Output _ _ (MAccR-⟶₀ _ MAccR-Skip)))))

-- the whole round is accessible everywhere
sb-R : ∀ n l d k → MAccR ∅ES (serverBodyL n l d k)
sb-R n l d k = MAccR-⟶₀ _ (MAccR-⟶ _ (λ b → MAccR->>= (sk-R n l d b) (λ _ → MAccR-Ret _)))

-- the round starts with a visible event
sb-G : ∀ n l d k → Guarded ∅ES (serverBodyL n l d k)
sb-G n l d k = Guarded-⟶-vis _ (λ _ ())

-- THE THREAD LEAF
serverLoopL-R : ∀ n ld → MAccR ∅ES (serverLoopL n ld)
serverLoopL-R n (l , d) = MAccR-loop _ (sb-G n l _) (sb-R n l _) 0

------------------------------------------------------------------------
-- a store: the RB store's loop over its four-way menu
------------------------------------------------------------------------

-- `Stop` is guarded (it never returns)
Guarded-Stop : ∀ {R : Set} → Guarded ∅ES (Stop {R = R})
Guarded-Stop = Guarded-react refl (λ _ ())

-- the "hand over any held block" menu
oh-R : ∀ n held bs → MAccR ∅ES (offerHeld n held bs)
oh-R n held []       = MAccR-Stop
oh-R n held (b ∷ bs) = MAccR-□ (MAccR-Output _ _ (MAccR-Ret _)) (oh-R n held bs)

-- … is guarded
oh-G : ∀ n held bs → Guarded ∅ES (offerHeld n held bs)
oh-G n held []       = Guarded-Stop
oh-G n held (b ∷ bs) = Guarded-□ (Guarded-Output-vis _ _ (λ _ ())) (oh-G n held bs)

-- the read-pointer menu (generic in the carried type and the store state)
oi-R : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {S : Set} ⦃ _ : DecEq S ⦄ e (xs : List A) k (s : S)
     → MAccR ∅ES (offerIx e xs k s)
oi-R e []       k s = MAccR-Stop
oi-R e (x ∷ xs) k s = MAccR-□ (MAccR-Output _ _ (MAccR-Ret _)) (oi-R e xs (suc k) s)

-- … is guarded
oi-G : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {S : Set} ⦃ _ : DecEq S ⦄ e (xs : List A) k (s : S)
     → Guarded ∅ES (offerIx e xs k s)
oi-G e []       k s = Guarded-Stop
oi-G e (x ∷ xs) k s = Guarded-□ (Guarded-Output-vis _ _ (λ _ ())) (oi-G e xs (suc k) s)

-- one store step is accessible everywhere …
ss-R : ∀ n held → MAccR ∅ES (storeStepL n held)
ss-R n held =
  MAccR-□ (MAccR-⟶ _ (λ _ → MAccR-Ret _))
    (MAccR-□ (MAccR-⟶ _ (λ _ → MAccR-Ret _))
      (MAccR-□ (oh-R n held held) (oi-R _ (reverse held) 0 held)))

-- … and starts with a visible event
ss-G : ∀ n held → Guarded ∅ES (storeStepL n held)
ss-G n held =
  Guarded-□ (Guarded-⟶-vis _ (λ _ ()))
    (Guarded-□ (Guarded-⟶-vis _ (λ _ ()))
      (Guarded-□ (oh-G n held held) (oi-G _ (reverse held) 0 held)))

-- THE STORE LEAF
blockStoreL-R : ∀ n held → MAccR ∅ES (blockStoreL n held)
blockStoreL-R n held = MAccR-loop _ (ss-G n) (ss-R n) held

------------------------------------------------------------------------
-- the five node-level threads
------------------------------------------------------------------------

-- the certificate half of a forge pass
forgeCert-R : ∀ n b → MAccR ∅ES (forgeCertL n b)
forgeCert-R n b =
  MAccR-maybe′ (λ r → MAccR-⟶₀ _ (MAccR-Output _ _ MAccR-Skip)) MAccR-Skip (LeiosP.LeiosParams.rbCert lpP b)

-- one forge pass, after the offer
forgeBody-R : ∀ n mb → MAccR ∅ES (forgeBodyL n mb)
forgeBody-R n (me , b) =
  MAccR-if (forgeOK (me , b))
    (MAccR-maybe′ (λ eb → MAccR-Output _ _ (forgeCert-R n b)) (forgeCert-R n b) me)
    MAccR-Skip

-- THE FORGE THREAD LEAF (each pass opens with `envForge`)
forgeL-R : ∀ n → MAccR ∅ES (forgeL n)
forgeL-R n = MAccR-loop0 (Guarded-⟶-vis _ (λ _ ())) (MAccR-⟶ _ (forgeBody-R n))

-- one EB-index round
ebIndexBody-R : ∀ n k → MAccR ∅ES (ebIndexBody n k)
ebIndexBody-R n k =
  MAccR-⟶ _ (λ b → MAccR-maybe′ (λ h → MAccR-Output _ _ (MAccR-Ret _)) (MAccR-Ret _) (announcedEB b))

-- THE EB-INDEX THREAD LEAF (each round opens with `stGetAt k`)
ebIndex-R : ∀ n → MAccR ∅ES (ebIndex n)
ebIndex-R n = MAccR-loop _ (λ _ → Guarded-⟶-vis _ (λ _ ())) (ebIndexBody-R n) 0

-- one voting round
voterBody-R : ∀ n k → MAccR ∅ES (voterBody n k)
voterBody-R n k =
  MAccR-⟶ _ (λ b → MAccR-maybe′ (λ h → MAccR-⟶ _ (λ _ → MAccR-Output ⦃ decVoteBlob ⦄ _ _ (MAccR-Ret _))) (MAccR-Ret _) (announcedEB b))

-- THE VOTER THREAD LEAF (each round opens with `stGetAt k`)
voter-R : ∀ n → MAccR ∅ES (voter n)
voter-R n = MAccR-loop _ (λ _ → Guarded-⟶-vis _ (λ _ ())) (voterBody-R n) 0

-- THE SUBMISSION THREAD LEAF (each pass opens with `envSubmit`)
submit-R : ∀ n → MAccR ∅ES (submit n)
submit-R n = MAccR-loop0 (Guarded-⟶-vis _ (λ _ ())) (MAccR-⟶ _ (λ _ → MAccR-Output _ _ MAccR-Skip))

-- THE CERTIFICATE-SINK THREAD LEAF (each pass opens with `stCert`)
certSink-R : ∀ n → MAccR ∅ES (certSink n)
certSink-R n = MAccR-loop0 (Guarded-⟶-vis _ (λ _ ())) (MAccR-⟶ _ (λ _ → MAccR-Skip))

------------------------------------------------------------------------
-- the ten per-endpoint threads
------------------------------------------------------------------------

-- the ChainSync client's RollForward continuation
clientBody-k-R : ∀ n l d ht → MAccR ∅ES (clientBody-k n l d ht)
clientBody-k-R n l d (header b , _) =
  MAccR-Output ⦃ DecEq-ChainRange ⦄ _ _ (MAccR-⟶ _ (λ _ → MAccR-Output ⦃ decBlock ⦄ _ _ MAccR-Skip))

-- THE CHAINSYNC CLIENT LEAF (each pass opens with `sendCSRequestNext`)
clientLoop-R : ∀ n ld → MAccR ∅ES (clientLoop n ld)
clientLoop-R n (l , d) =
  MAccR-loop0 (Guarded-⟶-vis _ (λ _ ())) (MAccR-⟶₀ _ (MAccR-⟶ _ (clientBody-k-R n l d)))

-- one LN announce round
lnServerBody-R : ∀ n l d k → MAccR ∅ES (lnServerBodyL n l d k)
lnServerBody-R n l d k = MAccR-⟶ _ (λ b → MAccR-Output _ _ (MAccR-Ret _))

-- THE LN ANNOUNCER LEAF (each round opens with `stGetAt k`)
lnServerLoopL-R : ∀ n ld → MAccR ∅ES (lnServerLoopL n ld)
lnServerLoopL-R n (l , d) = MAccR-loop _ (λ _ → Guarded-⟶-vis _ (λ _ ())) (lnServerBody-R n l _) 0

-- the tx-closure gate keeps accessibility (structural on the closure)
awaitTxs-R : ∀ n hs {P} → MAccR ∅ES P → MAccR ∅ES (awaitTxs n hs P)
awaitTxs-R n []             rp = rp
awaitTxs-R n ((h , _) ∷ hs) rp = MAccR-⟶ _ (λ _ → awaitTxs-R n hs rp)

-- one body-offer round
bodyOfferBody-R : ∀ n l d k → MAccR ∅ES (bodyOfferBody n l d k)
bodyOfferBody-R n l d k =
  MAccR-⟶ _ (λ b → MAccR-maybe′
    (λ h → MAccR-⟶ _ (λ eb → MAccR-Output ⦃ DecEq-Offer ⦄ _ _
             (awaitTxs-R n (ebTxs h) (MAccR-Output ⦃ DecEq-EBPoint ⦄ _ _ (MAccR-Ret _)))))
    (MAccR-Ret _) (announcedEB b))

-- THE BODY-OFFER LEAF (each round opens with `stGetAt k`)
bodyOfferLoop-R : ∀ n ld → MAccR ∅ES (bodyOfferLoop n ld)
bodyOfferLoop-R n (l , d) = MAccR-loop _ (λ _ → Guarded-⟶-vis _ (λ _ ())) (bodyOfferBody-R n l _) 0

-- one vote-offer round
voteOfferBody-R : ∀ n l d k → MAccR ∅ES (voteOfferBody n l d k)
voteOfferBody-R n l d k = MAccR-⟶ _ (λ v → MAccR-Output ⦃ DecEqI.DecEq-List ⦃ decVoteBlob ⦄ ⦄ _ _ (MAccR-Ret _))

-- THE VOTE-OFFER LEAF (each round opens with `stGetVoteAt k`)
voteOfferLoop-R : ∀ n ld → MAccR ∅ES (voteOfferLoop n ld)
voteOfferLoop-R n (l , d) = MAccR-loop _ (λ _ → Guarded-⟶-vis _ (λ _ ())) (voteOfferBody-R n l _) 0

-- fetching an offered body
fetchBody-R : ∀ n l d qs → MAccR ∅ES (fetchBody n l d qs)
fetchBody-R n l d (q , _) =
  MAccR-Output ⦃ DecEq-EBPoint ⦄ _ _ (MAccR-⟶ _ (λ eb →
    MAccR-if ⌊ DecEq._≟_ decEBHash eb (proj₁ q) ⌋ (MAccR-Output _ _ MAccR-Skip) MAccR-Skip))

-- depositing the checked entries of a tx-closure reply (mirrors `putChecked`'s `with`)
putChecked-R : ∀ n h es → MAccR ∅ES (putChecked n h es)
putChecked-R n h []             = MAccR-Skip
putChecked-R n h ((o , x) ∷ es) with at? o (ebTxs h)
... | nothing      = putChecked-R n h es
... | just (k , _) =
  MAccR-if ⌊ DecEq._≟_ decTxHash x k ⌋ (MAccR-Output _ _ (putChecked-R n h es)) (putChecked-R n h es)

-- fetching a tx closure
fetchTxs-R : ∀ n l d q → MAccR ∅ES (fetchTxs n l d q)
fetchTxs-R n l d q =
  MAccR-⟶ _ (λ _ → MAccR-Output ⦃ DecEq-TxsRequest ⦄ _ _ (MAccR-⟶ _ (λ { (q′ , es) →
    MAccR-if ⌊ DecEq._≟_ DecEq-EBPoint q′ q ⌋ (putChecked-R n (proj₁ q) es) MAccR-Skip })))

-- depositing the delivered vote blobs
putAllVotes-R : ∀ n vs → MAccR ∅ES (putAllVotes n vs)
putAllVotes-R n []       = MAccR-Skip
putAllVotes-R n (v ∷ vs) = MAccR-Output ⦃ decVoteBlob ⦄ _ _ (putAllVotes-R n vs)

-- THE LN CLIENT LEAF (each pass opens with `lnpSendRequestNext`)
lnClientLoopL-R : ∀ n ld → MAccR ∅ES (lnClientLoopL n ld)
lnClientLoopL-R n (l , d) =
  MAccR-loop0 (Guarded-⟶-vis _ (λ _ ()))
    (MAccR-⟶₀ _ (MAccR-□ (MAccR-⟶ _ (λ _ → MAccR-Skip))
      (MAccR-□ (MAccR-⟶ _ (fetchBody-R n l d))
      (MAccR-□ (MAccR-⟶ _ (fetchTxs-R n l d)) (MAccR-⟶ _ (putAllVotes-R n))))))

-- THE EB-SERVE LEAF (each pass opens with `lfpReqBlockRequest`)
ebServeLoop-R : ∀ n ld → MAccR ∅ES (ebServeLoop n ld)
ebServeLoop-R n (l , d) =
  MAccR-loop0 (Guarded-⟶-vis _ (λ _ ()))
    (MAccR-⟶ _ (λ q → MAccR-⟶ _ (λ eb → MAccR-Output _ _ MAccR-Skip)))

-- building and sending a tx-closure reply (mirrors `serveTxs`'s `with`)
serveTxs-R : ∀ n l d q os acc → MAccR ∅ES (serveTxs n l d q os acc)
serveTxs-R n l d q []       acc = MAccR-Output ⦃ DecEq-TxsReply ⦄ _ _ MAccR-Skip
serveTxs-R n l d q (o ∷ os) acc with at? o (ebTxs (proj₁ q))
... | nothing      = serveTxs-R n l d q os acc
... | just (h , _) = MAccR-⟶ _ (λ y → serveTxs-R n l d q os _)

-- THE TX-CLOSURE-SERVE LEAF (each pass opens with `lfpReqBlockTxsRequest`)
ebTxsServeLoop-R : ∀ n ld → MAccR ∅ES (ebTxsServeLoop n ld)
ebTxsServeLoop-R n (l , d) =
  MAccR-loop0 (Guarded-⟶-vis _ (λ _ ()))
    (MAccR-⟶ _ (λ { (q , bm) → MAccR-⟶ _ (λ _ → serveTxs-R n l _ q bm []) }))

-- depositing the requested transactions of a TxSubmission reply
putAllTx-R : ∀ n ids txs → MAccR ∅ES (putAllTx n ids txs)
putAllTx-R n ids []         = MAccR-Skip
putAllTx-R n ids (x ∷ txs) =
  MAccR-if (memberOf ⦃ decTxHash ⦄ x ids) (MAccR-Output _ _ (putAllTx-R n ids txs)) (putAllTx-R n ids txs)

-- THE TXSUBMISSION PULL LEAF (each pass opens with the `sendTSRequestTxIdsBlocking` output)
tsPull-R : ∀ n ld → MAccR ∅ES (tsPull n ld)
tsPull-R n (l , d) =
  MAccR-loop0 (Guarded-Output-vis _ _ (λ _ ()))
    (MAccR-Output _ _ (MAccR-⟶ _ (λ ids → MAccR-Output _ _ (MAccR-⟶ _ (putAllTx-R n ids)))))

-- one TxSubmission serve round
tsServeBody-R : ∀ n l d k → MAccR ∅ES (tsServeBody n l d k)
tsServeBody-R n l d k =
  MAccR-⟶ _ (λ _ → MAccR-⟶ _ (λ y → MAccR-Output _ _ (MAccR-⟶ _ (λ _ → MAccR-Output _ _ (MAccR-Ret _)))))

-- THE TXSUBMISSION SERVE LEAF (each round opens with `recvTSRequestTxIds`)
tsServe-R : ∀ n ld → MAccR ∅ES (tsServe n ld)
tsServe-R n (l , d) = MAccR-loop _ (λ _ → Guarded-⟶-vis _ (λ _ ())) (tsServeBody-R n l d) 0

------------------------------------------------------------------------
-- the four Leios stores (each step is a menu of visible offers)
------------------------------------------------------------------------

-- THE EB-ENTRY STORE LEAF
ebStore-R : ∀ n es → MAccR ∅ES (ebStore n es)
ebStore-R n = MAccR-loop _
  (λ es → Guarded-□ (Guarded-⟶-vis _ (λ _ ())) (oi-G _ es 0 es))
  (λ es → MAccR-□ (MAccR-⟶ _ (λ _ → MAccR-Ret _)) (oi-R _ es 0 es))

-- the by-hash body menu …
offerBodies-R : ∀ n bs ebs → MAccR ∅ES (offerBodies n bs ebs)
offerBodies-R n bs []         = MAccR-Stop
offerBodies-R n bs (eb ∷ ebs) = MAccR-□ (MAccR-Output _ _ (MAccR-Ret _)) (offerBodies-R n bs ebs)

-- … is guarded
offerBodies-G : ∀ n bs ebs → Guarded ∅ES (offerBodies n bs ebs)
offerBodies-G n bs []         = Guarded-Stop
offerBodies-G n bs (eb ∷ ebs) = Guarded-□ (Guarded-Output-vis _ _ (λ _ ())) (offerBodies-G n bs ebs)

-- THE EB-BODY STORE LEAF
bodyStore-R : ∀ n bs → MAccR ∅ES (bodyStore n bs)
bodyStore-R n = MAccR-loop _
  (λ bs → Guarded-□ (Guarded-⟶-vis _ (λ _ ())) (offerBodies-G n bs bs))
  (λ bs → MAccR-□ (MAccR-⟶ _ (λ _ → MAccR-Ret _)) (offerBodies-R n bs bs))

-- the by-hash transaction menu …
offerTxs-R : ∀ n ts xs → MAccR ∅ES (offerTxs n ts xs)
offerTxs-R n ts []       = MAccR-Stop
offerTxs-R n ts (x ∷ xs) = MAccR-□ (MAccR-Output _ _ (MAccR-Ret _)) (offerTxs-R n ts xs)

-- … is guarded
offerTxs-G : ∀ n ts xs → Guarded ∅ES (offerTxs n ts xs)
offerTxs-G n ts []       = Guarded-Stop
offerTxs-G n ts (x ∷ xs) = Guarded-□ (Guarded-Output-vis _ _ (λ _ ())) (offerTxs-G n ts xs)

-- THE MEMPOOL LEAF
mempool-R : ∀ n ts → MAccR ∅ES (mempool n ts)
mempool-R n = MAccR-loop _
  (λ ts → Guarded-□ (Guarded-⟶-vis _ (λ _ ())) (Guarded-□ (Guarded-⟶-vis _ (λ _ ()))
            (Guarded-□ (oi-G _ ts 0 ts) (offerTxs-G n ts ts))))
  (λ ts → MAccR-□ (MAccR-⟶ _ (λ _ → MAccR-Ret _)) (MAccR-□ (MAccR-⟶ _ (λ _ → MAccR-Ret _))
            (MAccR-□ (oi-R _ ts 0 ts) (offerTxs-R n ts ts))))

-- the certification step after a vote deposit
certify-R : ∀ n bs cs r → MAccR ∅ES (certify n bs cs r)
certify-R n bs cs r =
  MAccR-if (certifies bs r ∧ not (memberOf ⦃ decRbHash ⦄ r cs))
    (MAccR-Output ⦃ decRbHash ⦄ _ _ (MAccR-Ret _)) (MAccR-Ret _)

-- the certificate-query menu …
offerCerts-R : ∀ n vs rs → MAccR ∅ES (offerCerts n vs rs)
offerCerts-R n vs []       = MAccR-Stop
offerCerts-R n vs (r ∷ rs) = MAccR-□ (MAccR-⟶₀ _ (MAccR-Ret _)) (offerCerts-R n vs rs)

-- … is guarded
offerCerts-G : ∀ n vs rs → Guarded ∅ES (offerCerts n vs rs)
offerCerts-G n vs []       = Guarded-Stop
offerCerts-G n vs (r ∷ rs) = Guarded-□ (Guarded-⟶-vis _ (λ _ ())) (offerCerts-G n vs rs)

-- one vote-store step is accessible everywhere …
voteStep-R : ∀ n vs → MAccR ∅ES (voteStep n vs)
voteStep-R n (bs , cs) =
  MAccR-□ (MAccR-⟶ _ (λ v → certify-R n _ cs _))
    (MAccR-□ (oi-R ⦃ decVoteBlob ⦄ _ bs 0 (bs , cs)) (offerCerts-R n (bs , cs) cs))

-- … and starts with a visible event
voteStep-G : ∀ n vs → Guarded ∅ES (voteStep n vs)
voteStep-G n (bs , cs) =
  Guarded-□ (Guarded-⟶-vis _ (λ _ ()))
    (Guarded-□ (oi-G ⦃ decVoteBlob ⦄ _ bs 0 (bs , cs)) (offerCerts-G n (bs , cs) cs))

-- THE VOTE STORE LEAF
voteStore-R : ∀ n vs → MAccR ∅ES (voteStore n vs)
voteStore-R n = MAccR-loop _ (voteStep-G n) (voteStep-R n)

------------------------------------------------------------------------
-- the whole node logic
------------------------------------------------------------------------

-- one endpoint's ten threads
endpoint-R : ∀ n e → MAccR ∅ES (endpointThreadsL n e)
endpoint-R n e =
  MAccR-⦀ ∅ES (clientLoop-R n e) (MAccR-⦀ ∅ES (serverLoopL-R n e)
  (MAccR-⦀ ∅ES (lnClientLoopL-R n e) (MAccR-⦀ ∅ES (lnServerLoopL-R n e)
  (MAccR-⦀ ∅ES (bodyOfferLoop-R n e) (MAccR-⦀ ∅ES (voteOfferLoop-R n e)
  (MAccR-⦀ ∅ES (ebServeLoop-R n e) (MAccR-⦀ ∅ES (ebTxsServeLoop-R n e)
  (MAccR-⦀ ∅ES (tsPull-R n e) (tsServe-R n e)))))))))

-- every endpoint's threads
allThreads-R : ∀ n → MAccR ∅ES (allThreadsL n)
allThreads-R n =
  MAccR-⦀⁺ ∅ES (endpoint-R n (proj₁ (endpointsOf n))) (map⁺ (universal (endpoint-R n) (proj₂ (endpointsOf n))))

-- THE NODE-LOGIC LEAF: every thread and store, synchronised on `storeES`
logic-R : ∀ n → MAccR ∅ES (nodeLogicL n st₀)
logic-R n =
  MAccR-∥ storeES ∅ES
    (MAccR-⦀ ∅ES (forgeL-R n) (MAccR-⦀ ∅ES (ebIndex-R n) (MAccR-⦀ ∅ES (voter-R n)
      (MAccR-⦀ ∅ES (submit-R n) (MAccR-⦀ ∅ES (certSink-R n) (allThreads-R n))))))
    (MAccR-mono (λ at a m → proj₁ m)
      (MAccR-⦀ ∅ES (blockStoreL-R n []) (MAccR-⦀ ∅ES (ebStore-R n [])
        (MAccR-⦀ ∅ES (bodyStore-R n []) (MAccR-⦀ ∅ES (mempool-R n []) (voteStore-R n ([] , [])))))))

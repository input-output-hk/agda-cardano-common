{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C, Task 9a (F3b): the THREAD alphabet facts the
-- assembly needs to charge a peer relay's command credit to ONE thread.
-- Every `nodeLogicL` thread performs no wire `input`/`output`, and emits
-- no command of a CREDIT GROUP (the commands the far side's relays are
-- paid with) other than the one group it owns:
--   gCS  serverLoopL     (RollForward)        gVot voteOfferLoop  (votes, count + list)
--   gAnn lnServerLoopL   (announcements)      gReq lnClientLoopL  (body / closure requests)
--   gOff bodyOfferLoop   (body / closure offers) gBTx ebTxsServeLoop (closure entries)
--   gTS  tsServe         (txid / tx replies)
-- The other eight threads own none.  Each fact is an `AllT` traversal whose
-- obligations reduce to `⊤` on every concrete label (`Alw o e = IsZ (fw o e)`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.ThreadAlpha
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
open Topology tP using (Node)


open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (⊤)
import Data.Unit.Polymorphic as UP
open UP using (tt)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Parametric.Topology using (opposite)
open import Cardano_network.Net pP
open import Cardano_network.Data pP
  using (Payload; header; DecEq-TxsRequest; DecEq-Offer; DecEq-EBPoint; DecEq-Header; DecEq-ChainRange)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import Cardano_network.Params using (module Params)
open Params pP using (decBlock; decVoteBlob; decTx; decEB; decEBHash; ebHash)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹⟨_⟩_)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
  using (labels; AllL; AllT; AllT-Ret; AllT-⟶; AllT-Output; AllT-□; AllT->>=)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (AllT-if; AllT-maybe′)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (Prefix)
open import Cardano_network.Parametric.Leios.NoLivelock.Weights pP using (cIn; cOut; cCmd; ℓCmd)
open import Cardano_network.Parametric.Leios.NoLivelock.Threads k m tP vo
  using (loopAll; aw-All; pav-All; pc-All; pat-All; st-All; iVs; iHs; iTs)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
open LeiosP pP using (DecEq-LeiosPoint)
open LeiosP.LeiosParams lpP using (ebTxs; rbCert)
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic pP tP apiES
  using (serverBody-k; DecEq-Header×Tip; clientBody; clientBody-k; clientLoop; forgeEv; putEv)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic pP lpP tP apiES vo
  using ( serverBodyL; serverLoopL; lnServerBodyL; lnServerLoopL; ebIndexBody; ebIndex; voterBody; voter
        ; bodyOfferBody; bodyOfferLoop; voteOfferBody; voteOfferLoop; tsServeBody; tsServe
        ; forgeL; forgeBodyL; forgeCertL; forgeOK; submit; certSink; lnClientBodyL; lnClientLoopL
        ; ebServeLoop; ebTxsServeLoop; tsPull
        ; getAtEv; putEBEv; getBodyEv; putBodyEv; putTxEv; getTxAtEv; putVoteEv; getVoteAtEv; certEv
        ; hasCertEv; getTxEv; submitEv; DecEq-⊤poly; DecEq-ℕ×ℕ )

------------------------------------------------------------------------
-- the credit groups and the forbidden weight
------------------------------------------------------------------------

-- the command groups the far side's relays are paid with
data Grp : Set where
  gCS gAnn gOff gVot gReq gBTx gTS : Grp

-- the weight of a group (counts and list lengths)
gw : Grp → Event → ℕ
gw gCS  e = cCmd sendCSRollForward e
gw gAnn e = cCmd lnpSendBlockAnnouncement e
gw gOff e = cCmd lnpSendBlockOffer e + cCmd lnpSendBlockTxsOffer e
gw gVot e = cCmd lnpSendVotes e + ℓCmd lnpSendVotes e
gw gReq e = cCmd lfpSendBlockRequest e + (cCmd lfpSendBlockTxsRequest e + ℓCmd lfpSendBlockTxsRequest e)
gw gBTx e = ℓCmd lfpSendBlockTxs e
gw gTS  e = cCmd sendTSReplyTxIds e + ℓCmd sendTSReplyTxs e

-- the same group
isG : Grp → Grp → Bool
isG gCS  gCS  = true
isG gAnn gAnn = true
isG gOff gOff = true
isG gVot gVot = true
isG gReq gReq = true
isG gBTx gBTx = true
isG gTS  gTS  = true
isG _    _    = false

-- a group's weight, masked when the thread owns it
gm : Maybe Grp → Grp → Event → ℕ
gm o g e = if maybe (isG g) false o then 0 else gw g e

-- THE FORBIDDEN WEIGHT of a thread owning `o`: wire io, and every group it does not own
fw : Maybe Grp → Event → ℕ
fw o e = cIn e + (cOut e + (gm o gCS e + (gm o gAnn e + (gm o gOff e + (gm o gVot e
       + (gm o gReq e + (gm o gBTx e + gm o gTS e)))))))

-- zero, as a type (so that a concrete obligation is solved by eta)
IsZ : ℕ → Set
IsZ zero    = ⊤
IsZ (suc _) = ⊥

-- the label is allowed to a thread owning `o`
Alw : Maybe Grp → Event → Set
Alw o e = IsZ (fw o e)

------------------------------------------------------------------------
-- the five node-level threads (they own no group)
------------------------------------------------------------------------

-- the forge thread
forgeL-α : ∀ n {s W} → forgeL n ⟹⟨ s ⟩ W → AllL (Alw nothing) (labels s)
forgeL-α n = loopAll {body = λ _ → forgeEv n ⟶ forgeBodyL n} (λ _ →
  AllT-⟶ (forgeEv n) (λ _ → _) (λ { (me , b) →
    AllT-if (forgeOK (me , b)) (AllT-maybe′ (λ eb → AllT-Output ⦃ decEB ⦄ (putBodyEv n) eb _ (fc b)) (fc b) me) AllT-Ret })) tt
  where
    -- the certificate half of a pass
    fc : ∀ b → AllT (Alw nothing) (forgeCertL n b)
    fc b = AllT-maybe′ (λ r → AllT-⟶ (hasCertEv n r) (λ _ → _) (λ _ → AllT-Output ⦃ decBlock ⦄ (putEv n) b _ AllT-Ret))
             AllT-Ret (rbCert b)

-- the EB index
ebIndex-α : ∀ n {s W} → ebIndex n ⟹⟨ s ⟩ W → AllL (Alw nothing) (labels s)
ebIndex-α n = loopAll {body = ebIndexBody n} (λ k →
  AllT-⟶ (getAtEv n k) (λ _ → _) (λ b →
    AllT-maybe′ (λ h → AllT-Output ⦃ DecEq-LeiosPoint ⦄ (putEBEv n) _ _ AllT-Ret) AllT-Ret b)) 0

-- the voter
voter-α : ∀ n {s W} → voter n ⟹⟨ s ⟩ W → AllL (Alw nothing) (labels s)
voter-α n = loopAll {body = voterBody n} (λ k →
  AllT-⟶ (getAtEv n k) (λ _ → _) (λ b →
    AllT-maybe′ (λ h → AllT-⟶ (getBodyEv n h) (λ _ → _) (λ _ →
                   AllT-Output ⦃ decVoteBlob ⦄ (putVoteEv n) _ _ AllT-Ret)) AllT-Ret b)) 0

-- the submission thread
submit-α : ∀ n {s W} → submit n ⟹⟨ s ⟩ W → AllL (Alw nothing) (labels s)
submit-α n = loopAll (λ _ →
  AllT-⟶ (submitEv n) (λ _ → _) (λ t → AllT-Output ⦃ decTx ⦄ (putTxEv n) t _ AllT-Ret)) tt

-- the certificate sink
certSink-α : ∀ n {s W} → certSink n ⟹⟨ s ⟩ W → AllL (Alw nothing) (labels s)
certSink-α n = loopAll (λ _ → AllT-⟶ (certEv n) (λ _ → _) (λ _ → AllT-Ret)) tt

------------------------------------------------------------------------
-- the ten endpoint threads
------------------------------------------------------------------------

-- the ChainSync client (owns nothing)
clientLoop-α : ∀ n l d {s W} → clientLoop n (l , d) ⟹⟨ s ⟩ W → AllL (Alw nothing) (labels s)
clientLoop-α n l d = loopAll {body = λ _ → clientBody n l d} (λ _ →
  AllT-⟶ (apiCS l d sendCSRequestNext) (λ _ → _) (λ _ → AllT-⟶ (apiCS l d recvCSRollforward) (λ _ → _) ck)) tt
  where
    -- the fetch half of a round
    ck : ∀ ht → AllT (Alw nothing) (clientBody-k n l d ht)
    ck (header b , _) =
      AllT-Output ⦃ DecEq-ChainRange ⦄ (apiBF l d sendBFRequestRange) _ _
        (AllT-⟶ (apiBF l d recvBFBlock) (λ _ → _) (λ b′ → AllT-Output ⦃ decBlock ⦄ (putEv n) b′ _ AllT-Ret))

-- the ChainSync server (owns the RollForward commands)
serverLoopL-α : ∀ n l d {s W} → serverLoopL n (l , d) ⟹⟨ s ⟩ W → AllL (Alw (just gCS)) (labels s)
serverLoopL-α n l d = loopAll {body = serverBodyL n l (opposite d)} (λ k →
  AllT-⟶ (apiCS l (opposite d) reqCSRequestNext) (λ _ → _) (λ _ →
    AllT-⟶ (getAtEv n k) (λ _ → _) (λ b → AllT->>= (sk b) (λ _ → AllT-Ret)))) 0
  where
    -- the serve half of a round
    sk : ∀ b → AllT (Alw (just gCS)) (serverBody-k n l (opposite d) b)
    sk b = AllT-⟶ (apiCS l (opposite d) sendCSAwaitReply) (λ _ → _) (λ _ →
           AllT-Output (apiCS l (opposite d) sendCSRollForward) _ _ (
           AllT-⟶ (apiBF l (opposite d) reqBFRange) (λ _ → _) (λ _ →
           AllT-⟶ (apiBF l (opposite d) sendBFStartBatch) (λ _ → _) (λ _ →
           AllT-Output ⦃ decBlock ⦄ (apiBF l (opposite d) sendBFBlock) b _
             (AllT-⟶ (apiBF l (opposite d) sendBFBatchDone) (λ _ → _) (λ _ → AllT-Ret))))))

-- the LN client (owns the body / closure requests)
lnClientLoopL-α : ∀ n l d {s W} → lnClientLoopL n (l , d) ⟹⟨ s ⟩ W → AllL (Alw (just gReq)) (labels s)
lnClientLoopL-α n l d = loopAll {body = λ _ → lnClientBodyL n l d} (λ _ →
  AllT-⟶ (apiLP l d lnpSendRequestNext) (λ _ → _) (λ _ →
     AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockAnnouncement) (λ _ → _) (λ _ → AllT-Ret))
    (AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockOffer) (λ _ → _) (λ { (q , _) →
               AllT-Output ⦃ DecEq-EBPoint ⦄ (apiLP l d lfpSendBlockRequest) q _
                 (AllT-⟶ (apiLP l d lfpRecvBlock) (λ _ → _) (λ eb →
                   AllT-if ⌊ DecEq._≟_ decEBHash (ebHash eb) (proj₁ q) ⌋
                     (AllT-Output ⦃ decEB ⦄ (putBodyEv n) eb _ AllT-Ret) AllT-Ret)) }))
    (AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockTxsOffer) (λ _ → _) (λ q →
               AllT-⟶ (getBodyEv n (proj₁ q)) (λ _ → _) (λ _ →
                 AllT-Output ⦃ DecEq-TxsRequest ⦄ (apiLP l d lfpSendBlockTxsRequest) _ _
                   (AllT-⟶ (apiLP l d lfpRecvBlockTxs) (λ _ → _) (λ { (q′ , es) →
                     AllT-if ⌊ DecEq._≟_ DecEq-EBPoint q′ q ⌋ (pc-All n (proj₁ q) (λ _ → _) es) AllT-Ret })))))
            (AllT-⟶ (apiLP l d lnpRecvVotes) (λ _ → _) (λ vs → pav-All n (λ _ → _) vs)))))) tt

-- the LN announcer (owns the announcements)
lnServerLoopL-α : ∀ n l d {s W} → lnServerLoopL n (l , d) ⟹⟨ s ⟩ W → AllL (Alw (just gAnn)) (labels s)
lnServerLoopL-α n l d = loopAll {body = lnServerBodyL n l (opposite d)} (λ k →
  AllT-⟶ (getAtEv n k) (λ _ → _) (λ b →
    AllT-Output ⦃ DecEq-Header ⦄ (apiLP l (opposite d) lnpSendBlockAnnouncement) _ _ AllT-Ret)) 0

-- the body offerer (owns the body and closure offers)
bodyOfferLoop-α : ∀ n l d {s W} → bodyOfferLoop n (l , d) ⟹⟨ s ⟩ W → AllL (Alw (just gOff)) (labels s)
bodyOfferLoop-α n l d = loopAll {body = bodyOfferBody n l (opposite d)} (λ k →
  AllT-⟶ (getAtEv n k) (λ _ → _) (λ b →
    AllT-maybe′ (λ h → AllT-⟶ (getBodyEv n h) (λ _ → _) (λ _ →
                   AllT-Output ⦃ DecEq-Offer ⦄ (apiLP l (opposite d) lnpSendBlockOffer) _ _
                     (aw-All n (ebTxs h) (λ _ _ → _)
                       (AllT-Output ⦃ DecEq-EBPoint ⦄ (apiLP l (opposite d) lnpSendBlockTxsOffer) _ _ AllT-Ret))))
                AllT-Ret b)) 0

-- the vote offerer (owns the votes)
voteOfferLoop-α : ∀ n l d {s W} → voteOfferLoop n (l , d) ⟹⟨ s ⟩ W → AllL (Alw (just gVot)) (labels s)
voteOfferLoop-α n l d = loopAll {body = voteOfferBody n l (opposite d)} (λ k →
  AllT-⟶ (getVoteAtEv n k) (λ _ → _) (λ v →
    AllT-Output ⦃ iVs ⦄ (apiLP l (opposite d) lnpSendVotes) _ _ AllT-Ret)) 0

-- the EB server (owns nothing)
ebServeLoop-α : ∀ n l d {s W} → ebServeLoop n (l , d) ⟹⟨ s ⟩ W → AllL (Alw nothing) (labels s)
ebServeLoop-α n l d = loopAll (λ _ →
  AllT-⟶ (apiLP l (opposite d) lfpReqBlockRequest) (λ _ → _) (λ q →
    AllT-⟶ (getBodyEv n (proj₁ q)) (λ _ → _) (λ eb →
      AllT-Output ⦃ decEB ⦄ (apiLP l (opposite d) lfpSendBlock) eb _ AllT-Ret))) tt

-- the closure server (owns the closure entries)
ebTxsServeLoop-α : ∀ n l d {s W} → ebTxsServeLoop n (l , d) ⟹⟨ s ⟩ W → AllL (Alw (just gBTx)) (labels s)
ebTxsServeLoop-α n l d = loopAll (λ _ →
  AllT-⟶ (apiLP l (opposite d) lfpReqBlockTxsRequest) (λ _ → _) (λ { (q , bm) →
    AllT-⟶ (getBodyEv n (proj₁ q)) (λ _ → _) (λ _ → st-All n l (opposite d) q (λ _ _ → _) (λ _ → _) bm []) })) tt

-- the TxSubmission puller (owns nothing)
tsPull-α : ∀ n l d {s W} → tsPull n (l , d) ⟹⟨ s ⟩ W → AllL (Alw nothing) (labels s)
tsPull-α n l d = loopAll (λ _ →
  AllT-Output ⦃ DecEq-ℕ×ℕ ⦄ (apiTS l (opposite d) sendTSRequestTxIdsBlocking) _ _
    (AllT-⟶ (apiTS l (opposite d) recvTSReplyTxIds) (λ _ → _) (λ ids →
      AllT-Output ⦃ iHs ⦄ (apiTS l (opposite d) sendTSRequestTxsPipelined) ids _
        (AllT-⟶ (apiTS l (opposite d) recvTSReplyTxs) (λ _ → _) (λ txs → pat-All n ids (λ _ → _) txs))))) tt

-- the TxSubmission server (owns the txid and tx replies)
tsServe-α : ∀ n l d {s W} → tsServe n (l , d) ⟹⟨ s ⟩ W → AllL (Alw (just gTS)) (labels s)
tsServe-α n l d = loopAll {body = tsServeBody n l d} (λ k →
  AllT-⟶ (apiTS l d recvTSRequestTxIds) (λ _ → _) (λ _ →
    AllT-⟶ (getTxAtEv n k) (λ _ → _) (λ t →
      AllT-Output ⦃ iHs ⦄ (apiTS l d sendTSReplyTxIds) _ _
        (AllT-⟶ (apiTS l d recvTSRequestTxs) (λ _ → _) (λ _ →
          AllT-Output ⦃ iTs ⦄ (apiTS l d sendTSReplyTxs) _ _ AllT-Ret))))) 0

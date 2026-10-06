{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C (D1-b): the THREAD provenance.  Every
-- `nodeLogicL` thread guarantees `PA ChS ChS InT`: every ranking block it
-- puts on a chain label is one it relies on (`InT`: a store read, a
-- BlockFetch delivery, a forge) or one an earlier chain label of its own
-- trace carried.  Three threads make a HOP (round-local, `provIter`):
--   * `forgeL`      — `putEv n ! b` follows `forgeEv n ⟶ (me , b)`
--   * `clientLoop`  — `putEv n ! b′` follows `recvBFBlock ⟶ b′`
--   * `serverLoopL` — `sendBFBlock ! b` follows `getAtEv n k ⟶ b`
-- The other twelve are RELY-ONLY (they read `stGetAt`) or CHAIN-FREE:
-- an `AllT` traversal (`AllT→PA`).  `threadsL-PA` interleaves all fifteen.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; VB; AllV; HP)

module Cardano_network.Parametric.Leios.NoLivelock.ThreadsProv
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
open Topology tP using (Node)


open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Parametric.Topology using (opposite; module Topology)
open Topology tP using (endpointsOf)
open import Cardano_network.Net pP
open import Cardano_network.Data pP
  using (Payload; header; DecEq-TxsRequest; DecEq-Offer; DecEq-EBPoint; DecEq-Header; DecEq-ChainRange)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import Cardano_network.Params using (module Params)
open Params pP using (decBlock; decVoteBlob; decTx; decEB; decEBHash; ebHash)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel)
open import CSP.Laws.DivFree.Loop (Net_Api-≟ {Payload}) using (loopStep)
open import CSP.Laws.DivFree.Count (Net_Api-≟ {Payload})
  using (AllT; AllT-Ret; AllT-⟶; AllT-Output; AllT-□; AllT->>=)
open import CSP.Laws.DivFree.CountMore (Net_Api-≟ {Payload}) using (AllT-if; AllT-maybe′)
open import CSP.Laws.DivFree.Prov (Net_Api-≟ {Payload})
  using (PA; pa; ProvT; ProvT-Ret; ProvT-⟶; ProvT-Output; ProvT->>=; provIter; PA-par≡)
open import CSP.Laws.DivFree.ProvMore (Net_Api-≟ {Payload}) using (AllT→PA; ProvT-if; ProvT-maybe′; PA-⦀⁺)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (Prefix; _⦀_)
open import Cardano_network.Parametric.Leios.NoLivelock.ProvBF pP using (ChS)
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
        ; fetchBody; fetchTxs; ebServeBody; ebServeLoop; ebTxsServeBody; ebTxsServeLoop; tsPullBody; tsPull
        ; endpointThreadsL; allThreadsL
        ; getAtEv; putEBEv; getBodyEv; putBodyEv; putTxEv; getTxAtEv; putVoteEv; getVoteAtEv; certEv
        ; hasCertEv; getTxEv; submitEv; DecEq-⊤poly; DecEq-ℕ×ℕ )

------------------------------------------------------------------------
-- the thread rely
------------------------------------------------------------------------

-- THE THREAD RELY: a block read from the RB store, delivered by BlockFetch, or forged
InT : Event → Maybe Bool → Set
InT (evLabel _ (store _ _ stGet) b)        y = b ≡ y
InT (evLabel _ (store _ _ (stGetAt _)) b)  y = b ≡ y
InT (evLabel _ (apiBF _ _ recvBFBlock) b)  y = b ≡ y
InT (evLabel _ (env _ _ envForge) (_ , b)) y = b ≡ y
InT _                                      y = ⊥

------------------------------------------------------------------------
-- the three hops
------------------------------------------------------------------------

-- the certificate half of a forge pass deposits only the block the pass made known
fcP : ∀ n {K} b → K b → ProvT ChS ChS InT K (forgeCertL n b)
fcP n b kb =
  ProvT-maybe′ (λ r → ProvT-⟶ (hasCertEv n r) (λ _ {_} ())
                  (λ _ → ProvT-Output ⦃ decBlock ⦄ (putEv n) b (λ { refl → inj₂ (inj₁ kb) }) ProvT-Ret))
               ProvT-Ret (rbCert b)

-- THE FORGE HOP: a forged block is deposited only after the forge that carried it
forgeL-PA : ∀ n → PA ChS ChS InT (forgeL n)
forgeL-PA n = pa λ tr → provIter (loopStep {R = ⊤ {0ℓ}} (λ _ → forgeEv n ⟶ forgeBodyL n))
  (λ _ → ProvT->>= (ProvT-⟶ (forgeEv n) (λ _ → inj₁) λ { (me , b) →
                      ProvT-if (forgeOK (me , b))
                        (ProvT-maybe′ (λ eb → ProvT-Output ⦃ decEB ⦄ (putBodyEv n) eb (λ {_} ()) (fcP n b (inj₁ (inj₂ refl))))
                                      (fcP n b (inj₂ refl)) me)
                        ProvT-Ret })
                   (λ _ → ProvT-Ret)) tt tr

-- the fetch half of a client round deposits only the block just received
ckP : ∀ n l d {K} ht → ProvT ChS ChS InT K (clientBody-k n l d ht)
ckP n l d (header b , _) =
  ProvT-Output ⦃ DecEq-ChainRange ⦄ (apiBF l d sendBFRequestRange) _ (λ {_} ())
    (ProvT-⟶ (apiBF l d recvBFBlock) (λ _ → inj₁)
      (λ b′ → ProvT-Output ⦃ decBlock ⦄ (putEv n) b′ (λ { refl → inj₂ (inj₂ refl) }) ProvT-Ret))

-- THE CLIENT HOP: a fetched block is deposited only after BlockFetch delivered it
clientLoop-PA : ∀ n l d → PA ChS ChS InT (clientLoop n (l , d))
clientLoop-PA n l d = pa λ tr → provIter (loopStep {R = ⊤ {0ℓ}} (λ _ → clientBody n l d))
  (λ _ → ProvT->>= (ProvT-⟶ (apiCS l d sendCSRequestNext) (λ _ {_} ()) (λ _ →
                      ProvT-⟶ (apiCS l d recvCSRollforward) (λ _ {_} ()) (ckP n l d)))
                   (λ _ → ProvT-Ret)) tt tr

-- the serve half of a server round sends only a known block
skP : ∀ n l d {K} b → K b → ProvT ChS ChS InT K (serverBody-k n l d b)
skP n l d b kb =
  ProvT-⟶ (apiCS l d sendCSAwaitReply) (λ _ {_} ()) (λ _ →
  ProvT-Output (apiCS l d sendCSRollForward) _ (λ {_} ()) (
  ProvT-⟶ (apiBF l d reqBFRange) (λ _ {_} ()) (λ _ →
  ProvT-⟶ (apiBF l d sendBFStartBatch) (λ _ {_} ()) (λ _ →
  ProvT-Output ⦃ decBlock ⦄ (apiBF l d sendBFBlock) b (λ { refl → inj₂ (inj₁ (inj₁ (inj₁ (inj₁ kb)))) })
    (ProvT-⟶ (apiBF l d sendBFBatchDone) (λ _ {_} ()) (λ _ → ProvT-Ret))))))

-- THE SERVER HOP: a served block is the block just read from the store
serverLoopL-PA : ∀ n l d → PA ChS ChS InT (serverLoopL n (l , d))
serverLoopL-PA n l d = pa λ tr → provIter (loopStep {R = ⊤ {0ℓ}} (serverBodyL n l (opposite d)))
  (λ k → ProvT->>= (ProvT-⟶ (apiCS l (opposite d) reqCSRequestNext) (λ _ {_} ()) (λ _ →
                      ProvT-⟶ (getAtEv n k) (λ _ → inj₁) (λ b →
                        ProvT->>= (skP n l (opposite d) b (inj₂ refl)) (λ _ → ProvT-Ret))))
                   (λ _ → ProvT-Ret)) 0 tr

------------------------------------------------------------------------
-- the rely-only and chain-free threads
------------------------------------------------------------------------

-- the EB index reads the store only
ebIndex-PA : ∀ n → PA ChS ChS InT (ebIndex n)
ebIndex-PA n = AllT→PA (loopAll {body = ebIndexBody n} (λ k →
  AllT-⟶ (getAtEv n k) (λ _ {_} p → p) (λ b →
    AllT-maybe′ (λ h → AllT-Output ⦃ DecEq-LeiosPoint ⦄ (putEBEv n) _ (λ {_} ()) AllT-Ret) AllT-Ret b)) 0)

-- the voter reads the store only
voter-PA : ∀ n → PA ChS ChS InT (voter n)
voter-PA n = AllT→PA (loopAll {body = voterBody n} (λ k →
  AllT-⟶ (getAtEv n k) (λ _ {_} p → p) (λ b →
    AllT-maybe′ (λ h → AllT-⟶ (getBodyEv n h) (λ _ {_} ()) (λ _ →
                   AllT-Output ⦃ decVoteBlob ⦄ (putVoteEv n) _ (λ {_} ()) AllT-Ret)) AllT-Ret b)) 0)

-- the submission thread touches no chain label
submit-PA : ∀ n → PA ChS ChS InT (submit n)
submit-PA n = AllT→PA (loopAll (λ _ →
  AllT-⟶ (submitEv n) (λ _ {_} ()) (λ t → AllT-Output ⦃ decTx ⦄ (putTxEv n) t (λ {_} ()) AllT-Ret)) tt)

-- the certificate sink touches no chain label
certSink-PA : ∀ n → PA ChS ChS InT (certSink n)
certSink-PA n = AllT→PA (loopAll (λ _ → AllT-⟶ (certEv n) (λ _ {_} ()) (λ _ → AllT-Ret)) tt)

-- the LN client touches no chain label
lnClientLoopL-PA : ∀ n l d → PA ChS ChS InT (lnClientLoopL n (l , d))
lnClientLoopL-PA n l d = AllT→PA (loopAll (λ _ →
  AllT-⟶ (apiLP l d lnpSendRequestNext) (λ _ {_} ()) (λ _ →
     AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockAnnouncement) (λ _ {_} ()) (λ _ → AllT-Ret))
    (AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockOffer) (λ _ {_} ()) (λ { (q , _) →
               AllT-Output ⦃ DecEq-EBPoint ⦄ (apiLP l d lfpSendBlockRequest) q (λ {_} ())
                 (AllT-⟶ (apiLP l d lfpRecvBlock) (λ _ {_} ()) (λ eb →
                   AllT-if ⌊ DecEq._≟_ decEBHash (ebHash eb) (proj₁ q) ⌋
                     (AllT-Output ⦃ decEB ⦄ (putBodyEv n) eb (λ {_} ()) AllT-Ret) AllT-Ret)) }))
    (AllT-□ (AllT-⟶ (apiLP l d lnpRecvBlockTxsOffer) (λ _ {_} ()) (λ q →
               AllT-⟶ (getBodyEv n (proj₁ q)) (λ _ {_} ()) (λ _ →
                 AllT-Output ⦃ DecEq-TxsRequest ⦄ (apiLP l d lfpSendBlockTxsRequest) _ (λ {_} ())
                   (AllT-⟶ (apiLP l d lfpRecvBlockTxs) (λ _ {_} ()) (λ { (q′ , es) →
                     AllT-if ⌊ DecEq._≟_ DecEq-EBPoint q′ q ⌋ (pc-All n (proj₁ q) (λ _ {_} ()) es) AllT-Ret })))))
            (AllT-⟶ (apiLP l d lnpRecvVotes) (λ _ {_} ()) (λ vs → pav-All n (λ _ {_} ()) vs)))))) tt)

-- the LN announcer reads the store only
lnServerLoopL-PA : ∀ n l d → PA ChS ChS InT (lnServerLoopL n (l , d))
lnServerLoopL-PA n l d = AllT→PA (loopAll {body = lnServerBodyL n l (opposite d)} (λ k →
  AllT-⟶ (getAtEv n k) (λ _ {_} p → p) (λ b →
    AllT-Output ⦃ DecEq-Header ⦄ (apiLP l (opposite d) lnpSendBlockAnnouncement) _ (λ {_} ()) AllT-Ret)) 0)

-- the body offerer reads the store only
bodyOfferLoop-PA : ∀ n l d → PA ChS ChS InT (bodyOfferLoop n (l , d))
bodyOfferLoop-PA n l d = AllT→PA (loopAll {body = bodyOfferBody n l (opposite d)} (λ k →
  AllT-⟶ (getAtEv n k) (λ _ {_} p → p) (λ b →
    AllT-maybe′ (λ h → AllT-⟶ (getBodyEv n h) (λ _ {_} ()) (λ _ →
                   AllT-Output ⦃ DecEq-Offer ⦄ (apiLP l (opposite d) lnpSendBlockOffer) _ (λ {_} ())
                     (aw-All n (ebTxs h) (λ _ _ {_} ())
                       (AllT-Output ⦃ DecEq-EBPoint ⦄ (apiLP l (opposite d) lnpSendBlockTxsOffer) _ (λ {_} ()) AllT-Ret))))
                AllT-Ret b)) 0)

-- the vote offerer touches no chain label
voteOfferLoop-PA : ∀ n l d → PA ChS ChS InT (voteOfferLoop n (l , d))
voteOfferLoop-PA n l d = AllT→PA (loopAll {body = voteOfferBody n l (opposite d)} (λ k →
  AllT-⟶ (getVoteAtEv n k) (λ _ {_} ()) (λ v →
    AllT-Output ⦃ iVs ⦄ (apiLP l (opposite d) lnpSendVotes) _ (λ {_} ()) AllT-Ret)) 0)

-- the EB server touches no chain label
ebServeLoop-PA : ∀ n l d → PA ChS ChS InT (ebServeLoop n (l , d))
ebServeLoop-PA n l d = AllT→PA (loopAll (λ _ →
  AllT-⟶ (apiLP l (opposite d) lfpReqBlockRequest) (λ _ {_} ()) (λ q →
    AllT-⟶ (getBodyEv n (proj₁ q)) (λ _ {_} ()) (λ eb →
      AllT-Output ⦃ decEB ⦄ (apiLP l (opposite d) lfpSendBlock) eb (λ {_} ()) AllT-Ret))) tt)

-- the closure server touches no chain label
ebTxsServeLoop-PA : ∀ n l d → PA ChS ChS InT (ebTxsServeLoop n (l , d))
ebTxsServeLoop-PA n l d = AllT→PA (loopAll (λ _ →
  AllT-⟶ (apiLP l (opposite d) lfpReqBlockTxsRequest) (λ _ {_} ()) (λ { (q , bm) →
    AllT-⟶ (getBodyEv n (proj₁ q)) (λ _ {_} ()) (λ _ → st-All n l (opposite d) q (λ _ _ {_} ()) (λ _ {_} ()) bm []) })) tt)

-- the TxSubmission puller touches no chain label
tsPull-PA : ∀ n l d → PA ChS ChS InT (tsPull n (l , d))
tsPull-PA n l d = AllT→PA (loopAll (λ _ →
  AllT-Output ⦃ DecEq-ℕ×ℕ ⦄ (apiTS l (opposite d) sendTSRequestTxIdsBlocking) _ (λ {_} ())
    (AllT-⟶ (apiTS l (opposite d) recvTSReplyTxIds) (λ _ {_} ()) (λ ids →
      AllT-Output ⦃ iHs ⦄ (apiTS l (opposite d) sendTSRequestTxsPipelined) ids (λ {_} ())
        (AllT-⟶ (apiTS l (opposite d) recvTSReplyTxs) (λ _ {_} ()) (λ txs → pat-All n ids (λ _ {_} ()) txs))))) tt)

-- the TxSubmission server touches no chain label
tsServe-PA : ∀ n l d → PA ChS ChS InT (tsServe n (l , d))
tsServe-PA n l d = AllT→PA (loopAll {body = tsServeBody n l d} (λ k →
  AllT-⟶ (apiTS l d recvTSRequestTxIds) (λ _ {_} ()) (λ _ →
    AllT-⟶ (getTxAtEv n k) (λ _ {_} ()) (λ t →
      AllT-Output ⦃ iHs ⦄ (apiTS l d sendTSReplyTxIds) _ (λ {_} ())
        (AllT-⟶ (apiTS l d recvTSRequestTxs) (λ _ {_} ()) (λ _ →
          AllT-Output ⦃ iTs ⦄ (apiTS l d sendTSReplyTxs) _ (λ {_} ()) AllT-Ret))))) 0)

------------------------------------------------------------------------
-- all fifteen
------------------------------------------------------------------------

-- every endpoint's ten threads
endpoint-PA : ∀ n e → PA ChS ChS InT (endpointThreadsL n e)
endpoint-PA n (l , d) =
  PA-par≡ (clientLoop-PA n l d) (PA-par≡ (serverLoopL-PA n l d) (PA-par≡ (lnClientLoopL-PA n l d)
  (PA-par≡ (lnServerLoopL-PA n l d) (PA-par≡ (bodyOfferLoop-PA n l d) (PA-par≡ (voteOfferLoop-PA n l d)
  (PA-par≡ (ebServeLoop-PA n l d) (PA-par≡ (ebTxsServeLoop-PA n l d) (PA-par≡ (tsPull-PA n l d) (tsServe-PA n l d)))))))))

-- THE THREADS' PROVENANCE: the five node-level threads and every endpoint's ten
threadsL-PA : ∀ n → PA ChS ChS InT (forgeL n ⦀ (ebIndex n ⦀ (voter n ⦀ (submit n ⦀ (certSink n ⦀ allThreadsL n)))))
threadsL-PA n =
  PA-par≡ (forgeL-PA n) (PA-par≡ (ebIndex-PA n) (PA-par≡ (voter-PA n) (PA-par≡ (submit-PA n)
  (PA-par≡ (certSink-PA n) (PA-⦀⁺ (endpoint-PA n (proj₁ (endpointsOf n)))
                            (map⁺ (All.universal (endpoint-PA n) (proj₂ (endpointsOf n)))))))))

{-# OPTIONS --guardedness #-}

-- Computation gates for the positional BlockTxs wire reply.  These compare the
-- visible branch's whole Maybe continuation with the expected Output, so refl
-- checks both acceptance and its exact output value (not just Is-just).
module Cardano_network.LeiosFetchPSanity where

open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Properties using (length-replicate)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Base using (lo; hi; FromInitiator; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open Params replayParams using (Tx; EBHash; LSlot; time₀; length₀)
open import Cardano_network.Data replayParams
  using (TxBitmap; leiosFetchP; MsgLFPBlockTxs; MsgLFPBlockTxsRequest;
         DecEq-TxsRequest; DecEq-TxsReply; DecEq-Payload)
open import Cardano_network.Net replayParams
  using (lfpRecvBlockTxs; lfpSendBlockTxs; lfpReqBlockTxsRequest)
open import Cardano_network.LeiosFetchP replayParams
  using (LFPEv; LFPEv-≟; LFPState; Rr; stIdle; stBlockTxs;
         clientStepP; serverStepP; receiveLFP; sendLFP; apiLPev)
import CSP.Operators {E = LFPEv} LFPEv-≟ as Op

-- The requested EB point is retained locally, rather than echoed on the wire.
q : EBHash × LSlot
q = 7 , 1

-- The continuation type of one client/server step at the concrete replay Params.
StepProc : Set₁
StepProc = PTree LFPEv (ExtI LFPEv) (LFPState ⊎ Rr)

-- Inspect the client's busy receive branch on the same link and direction.
clientReply : TxBitmap → List Tx → Maybe StepProc
clientReply bm txs = Op.viewV (PTree.force (clientStepP fzero lo (stBlockTxs q bm)))
  (_ , receiveLFP fzero lo)
  (time₀ , FromResponder , length₀ , leiosFetchP (MsgLFPBlockTxs txs))

-- Two transactions are paired positionally with the requested offsets 3 and 5.
countMatchAccepted : clientReply (3 ∷ 5 ∷ []) (tt ∷ tt ∷ [])
  ≡ just (Op.Output ⦃ DecEq-TxsReply ⦄ (apiLPev fzero lo lfpRecvBlockTxs)
       (q , (3 , tt) ∷ (5 , tt) ∷ []) (Op.Ret (inj₁ stIdle)))
countMatchAccepted = refl

-- A short reply is received and stops the client before reporting any entries.
countMismatchStops : clientReply (3 ∷ 5 ∷ []) (tt ∷ []) ≡ just Op.Stop
countMismatchStops = refl

-- A long reply also stops the client instead of silently truncating the zip.
countMismatchStopsLong : clientReply (3 ∷ 5 ∷ []) (tt ∷ tt ∷ tt ∷ []) ≡ just Op.Stop
countMismatchStopsLong = refl

-- A mismatched reply on the other direction is still refused by the lo client.
otherDirRefused :
  Op.viewV (PTree.force (clientStepP fzero lo (stBlockTxs q (3 ∷ 5 ∷ []))))
    (_ , receiveLFP fzero hi)
    (time₀ , FromResponder , length₀ , leiosFetchP (MsgLFPBlockTxs (tt ∷ [])))
  ≡ nothing
otherDirRefused = refl

-- The empty request accepts the empty reply and preserves its requested point.
emptyReplyAccepted : clientReply [] []
  ≡ just (Op.Output ⦃ DecEq-TxsReply ⦄ (apiLPev fzero lo lfpRecvBlockTxs)
       (q , []) (Op.Ret (inj₁ stIdle)))
emptyReplyAccepted = refl

-- The server drops both the API point and offsets, preserving transaction order.
serverSendsPositional :
  Op.viewV (PTree.force (serverStepP fzero lo (stBlockTxs q (3 ∷ 5 ∷ []))))
    (_ , apiLPev fzero lo lfpSendBlockTxs) (q , (3 , tt) ∷ (5 , tt) ∷ [])
  ≡ just (Op.Output ⦃ DecEq-Payload ⦄ (sendLFP fzero lo)
       (time₀ , FromResponder , length₀ , leiosFetchP (MsgLFPBlockTxs (tt ∷ tt ∷ [])))
       (Op.Ret (inj₁ stIdle)))
serverSendsPositional = refl

-- Distinct transaction values expose order changes hidden by replayParams' ⊤.
orderParams : Params
orderParams = record replayParams
  { Tx = Bool ; txHash = λ _ → tt ; txSize = λ _ → tt
  ; decTx = record { _≟_ = Data.Bool._≟_ }
  ; decCookie = Params.decCookie replayParams ; decBlock = Params.decBlock replayParams
  ; decLSlot = Params.decLSlot replayParams ; decVoterId = Params.decVoterId replayParams
  ; decVoteBlob = Params.decVoteBlob replayParams ; decTime = Params.decTime replayParams
  ; decLength = Params.decLength replayParams ; decEB = Params.decEB replayParams
  ; decEBHash = Params.decEBHash replayParams ; decRbHash = Params.decRbHash replayParams
  ; decTxHash = Params.decTxHash replayParams ; decSize = Params.decSize replayParams }

-- Keep the Bool-instantiated peers and their equality dictionaries qualified.
module TransactionOrder where
  import Cardano_network.Data orderParams as D
  import Cardano_network.Net orderParams as N
  import Cardano_network.LeiosFetchP orderParams as L
  import CSP.Operators {E = L.LFPEv} L.LFPEv-≟ as O

  -- Both inspected branches return this Bool-instantiated step continuation.
  OrderStepProc : Set₁
  OrderStepProc = PTree L.LFPEv (ExtI L.LFPEv) (L.LFPState ⊎ L.Rr)

  -- Inspect the client reply and the server API delivery for the same request.
  replies : Maybe OrderStepProc × Maybe OrderStepProc
  replies =
    ( O.viewV (PTree.force (L.clientStepP fzero lo (L.stBlockTxs q (3 ∷ 5 ∷ []))))
        (_ , L.receiveLFP fzero lo)
        (tt , FromResponder , tt , D.leiosFetchP (D.MsgLFPBlockTxs (true ∷ false ∷ [])))
    , O.viewV (PTree.force (L.serverStepP fzero lo (L.stBlockTxs q (3 ∷ 5 ∷ []))))
        (_ , L.apiLPev fzero lo N.lfpSendBlockTxs) (q , (3 , true) ∷ (5 , false) ∷ []) )

  -- One gate pins both client offset restoration and server positional send order.
  transactionOrderPreserved : replies
    ≡ ( just (O.Output ⦃ D.DecEq-TxsReply ⦄ (L.apiLPev fzero lo N.lfpRecvBlockTxs)
          (q , (3 , true) ∷ (5 , false) ∷ []) (O.Ret (inj₁ L.stIdle)))
      , just (O.Output ⦃ D.DecEq-Payload ⦄ (L.sendLFP fzero lo)
          (tt , FromResponder , tt , D.leiosFetchP (D.MsgLFPBlockTxs (true ∷ false ∷ [])))
          (O.Ret (inj₁ L.stIdle))) )
  transactionOrderPreserved = refl

-- Inspect a server request received on its own link and direction.
serverRequest : TxBitmap → Maybe StepProc
serverRequest bm = Op.viewV (PTree.force (serverStepP fzero lo stIdle))
  (_ , receiveLFP fzero lo)
  (time₀ , FromInitiator , length₀ , leiosFetchP (MsgLFPBlockTxsRequest q bm))

-- Duplicate offsets fail decoding after the request has been received.
nonCanonicalRequestStops : serverRequest (3 ∷ 3 ∷ []) ≡ just Op.Stop
nonCanonicalRequestStops = refl

-- The first offset outside the wire range also fails decoding.
outOfRangeRequestStops : serverRequest (17152 ∷ []) ≡ just Op.Stop
outOfRangeRequestStops = refl

-- Canonical offsets retain the exact application report and busy continuation.
canonicalRequestReported : serverRequest (3 ∷ 5 ∷ []) ≡ just
  (Op.Output ⦃ DecEq-TxsRequest ⦄ (apiLPev fzero lo lfpReqBlockTxsRequest)
    (q , 3 ∷ 5 ∷ []) (Op.Ret (inj₁ (stBlockTxs q (3 ∷ 5 ∷ [])))))
canonicalRequestReported = refl

-- A known decoder overflow stops before the positional count check.
clientReply-overCap : ∀ bm txs → (maxTxs <ᵇ length txs) ≡ true →
  clientReply bm txs ≡ just Op.Stop
clientReply-overCap bm txs over rewrite over = refl

-- Use the length lemma instead of reducing the large replicated reply in refl.
overCapReplyStops : clientReply (0 ∷ []) (replicate 17143 tt) ≡ just Op.Stop
overCapReplyStops = clientReply-overCap (0 ∷ []) (replicate 17143 tt)
  (trans (cong (maxTxs <ᵇ_) (length-replicate 17143 {x = tt})) refl)

-- Descending offsets fail the same strict-order decoder condition as duplicates.
descendingRequestStops : serverRequest (5 ∷ 3 ∷ []) ≡ just Op.Stop
descendingRequestStops = refl

-- Decoder padding offsets are reported even beyond the honest transaction cap.
paddingRequestReported : serverRequest (17142 ∷ []) ≡ just
  (Op.Output ⦃ DecEq-TxsRequest ⦄ (apiLPev fzero lo lfpReqBlockTxsRequest)
    (q , 17142 ∷ []) (Op.Ret (inj₁ (stBlockTxs q (17142 ∷ [])))))
paddingRequestReported = refl

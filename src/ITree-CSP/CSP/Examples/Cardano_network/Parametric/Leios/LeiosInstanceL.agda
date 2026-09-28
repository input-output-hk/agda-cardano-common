{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — A CONCRETE LINEAR-LEIOS SCENARIO: the same
-- three-node line as `Parametric.LeiosInstance`, over its OWN `Params`.
--
-- WHY ITS OWN `Params`.  `LeiosInstance.leiosParams` takes `VoteBlob = ⊤`,
-- and with a one-element `VoteBlob` the `LeiosParams` law `blobRb-mk`
-- (`blobRb (mkVoteBlob v r) ≡ r` for EVERY `r`) is unprovable — two distinct
-- RB hashes would have to be recovered from the same blob.  This scenario
-- therefore carries a vote blob that really does record `(voter , RB voted
-- on)`, and `LeiosInstance.agda` is untouched.
--
-- `linkConfig` gains BOTH LeiosFetch entries: without a `N2N_LeiosFetch`
-- cell the medium cannot carry `MsgLFBlockRequest`/`MsgLFBlock`, so no
-- body could ever be fetched and every body-diffusion property would hold
-- vacuously (the 2026-09-07 `N2N_LeiosNotify` lesson, `LeiosInstance.agda:68-80`).
--
-- THE NODE BUILDER IS `nodeBundleP`, the PROTOTYPE bundle: the Linear-Leios
-- logic needs the LeiosFetchP producer to REPORT the request it received
-- (`lfpReqBlockRequest`/`lfpReqBlockTxsRequest`) and the TxSubmission requester
-- to report the reply it received (`recvTSReplyTxIds`/`recvTSReplyTxs`).  The
-- builder comes from `Leios.PeersP`, never from `Leios.PeersPSanity`.
--
-- A COMPOSITION / TYPECHECKING WITNESS ONLY: nothing is proved here.  The
-- non-vacuity probe for the reporting producer is
-- `Leios.PeersPSanity.lfpP-reports-request`; the old `lfR-reports-request`
-- probe lived here and went with the old `LeiosFetch` peer.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Leios.LeiosInstanceL where

import Data.Unit as U
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
import Data.Bool.Properties as BoolProp
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Properties as FinProp
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeProp
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)
import Class.DecEq.Instances as DecEqI

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; mkTopology)
import CSP.Examples.Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import CSP.Examples.Cardano_network.Parametric.Leios.NodeLogicL as NLL

-- trivial decidable equality for the ⊤ domains that stay inert here
leiosLDecEq⊤ : DecEq U.⊤
leiosLDecEq⊤ = record { _≟_ = λ _ _ → yes refl }

-- decidable equality for the two-valued EB / EB-hash domain
leiosLDecEqBool : DecEq Bool
leiosLDecEqBool = record { _≟_ = BoolProp._≟_ }

-- decidable equality for the `Block` domain (`Maybe Bool`: no announcement, or one
-- of the two EB hashes)
leiosLDecEqBlock : DecEq (Maybe Bool)
leiosLDecEqBlock = record { _≟_ = MaybeProp.≡-dec BoolProp._≟_ }

-- decidable equality for the voter identity (one per node of the three-node line)
leiosLDecEqVoter : DecEq (Fin 3)
leiosLDecEqVoter = record { _≟_ = FinProp._≟_ }

-- A NON-DEGENERATE VOTE BLOB: who voted, and which RANKING BLOCK the vote names.  The
-- verdict component is gone — the prototype's votes carry no verdict.
LVoteBlob : Set
LVoteBlob = Fin 3 × Maybe Bool

-- decidable equality for the vote blob, from the product instance (every component
-- instance supplied explicitly — none of them is ambient in this module)
leiosLDecEqBlob : DecEq LVoteBlob
leiosLDecEqBlob = DecEqI.DecEq-× ⦃ leiosLDecEqVoter ⦄ ⦃ leiosLDecEqBlock ⦄

-- both directions × the four Praos protocols × LeiosNotify × LeiosFetch, on every link
leiosLCfg : List (Dir × IDs)
leiosLCfg = (lo , N2N_KeepAlive)    ∷ (hi , N2N_KeepAlive)
          ∷ (lo , N2N_ChainSync)    ∷ (hi , N2N_ChainSync)
          ∷ (lo , N2N_BlockFetch)   ∷ (hi , N2N_BlockFetch)
          ∷ (lo , N2N_TxSubmission) ∷ (hi , N2N_TxSubmission)
          ∷ (lo , N2N_LeiosNotify)  ∷ (hi , N2N_LeiosNotify)
          ∷ (lo , N2N_LeiosFetch)   ∷ (hi , N2N_LeiosFetch) ∷ []

-- concrete `Params` for the Linear-Leios scenario: two links, uniform config, two
-- distinguishable EBs/hashes, three voters, and the three hash-identified objects each
-- taking the object as its own hash
leiosLParams : Params
leiosLParams = record
  { Cookie = U.⊤ ; Block = Maybe Bool ; LSlot = U.⊤
  ; VoterId = Fin 3 ; VoteBlob = LVoteBlob
  ; numLinks = 2 ; linkConfig = λ _ → leiosLCfg
  ; decCookie = leiosLDecEq⊤ ; decBlock = leiosLDecEqBlock
  ; decLSlot = leiosLDecEq⊤ ; decVoterId = leiosLDecEqVoter
  ; decVoteBlob = leiosLDecEqBlob
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = leiosLDecEq⊤ ; decLength = leiosLDecEq⊤
  ; EB = Bool ; EBHash = Bool ; decEB = leiosLDecEqBool ; decEBHash = leiosLDecEqBool
  ; ebHash = λ e → e ; announcedEB = λ b → b
  -- the three hash-identified objects, each taking the object as its own hash.  `Tx` and
  -- `TxHash` are `Bool`, NOT the `⊤` of Task 1's mechanical filling: the mempool must be
  -- able to hold two distinguishable transactions or the tx-closure branch is vacuous.
  ; RbHash = Maybe Bool ; decRbHash = leiosLDecEqBlock ; rbHash = λ b → b
  ; Tx = Bool ; TxHash = Bool ; decTx = leiosLDecEqBool ; decTxHash = leiosLDecEqBool
  ; txHash = λ x → x
  ; Size = U.⊤ ; decSize = leiosLDecEq⊤ ; txSize = λ _ → U.tt
  ; slotOf = λ _ → U.tt }

-- the Leios parameters of the scenario.  `certifies` is the weakest non-trivial oracle —
-- one blob naming that RB.  `ebTxs` gives the EB `true` a one-entry body table so the
-- tx-closure branch has something to serve.
--
-- `rbCert` IS NON-TRIVIAL, AND HAS TO BE.  It marks the single block `just false` as
-- carrying a certificate for the ranking block `just true`, and every other block as
-- certificate-free.  With the constantly-`nothing` `rbCert` this instance used to carry,
-- `CertRbOrigin.vouchedRb` was identically `true` here, so S4 — although ∀-`Params`,
-- ∀-`LeiosParams` and premise-free — constrained NOTHING on the shipped Leios line.
-- That was one of the two independent reasons S4 was empty here; the other was that the
-- forge route could not fire at all, which `NodeLogicL`'s two new store arms fix.  Both
-- are closed now.  The value chosen is deliberately the one `CertRbOriginBad.leiosLP₃`
-- already used, so the control and the shipped line agree on which block is a
-- certificate RB; `leiosLP₃` is kept as an explicit record update so the control stays
-- independent of this field and its statement does not move.
leiosLP : LeiosP.LeiosParams leiosLParams
leiosLP = record
  { mkVoteBlob = λ v r → v , r
  ; blobVoter  = proj₁
  ; blobRb     = proj₂
  ; blobVoter-mk = λ _ _ → refl
  ; blobRb-mk    = λ _ _ → refl
  ; certifies  = λ vs r → any (λ v → ⌊ DecEq._≟_ leiosLDecEqBlock (proj₂ v) r ⌋) vs
  ; ebTxs      = λ h → if h then ((true , U.tt) ∷ []) else []
  ; ebSize     = λ _ → U.tt
  ; rbCert     = λ b → if ⌊ DecEq._≟_ leiosLDecEqBlock b (just false) ⌋
                       then just (just true) else nothing }

open import CSP.Examples.Cardano_network.Net leiosLParams using (Link)
open import CSP.Examples.Cardano_network.NetCommon leiosLParams
  using (NetworkLinkBreakableA)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosLParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Leios.PeersP leiosLParams
  using (nodeBundleP)

-- the (lo-end , hi-end) pair of each link: link 0 joins A—B, link 1 joins B—C
leiosLEnds : Link → Fin 3 × Fin 3
leiosLEnds fzero    = fzero , fsuc fzero
leiosLEnds (fsuc _) = fsuc fzero , fsuc (fsuc fzero)

-- the three-node line as a `Topology`, derived by `mkTopology`
leiosLLine : Topology leiosLParams
leiosLLine = mkTopology 2 leiosLEnds
               (λ { fzero → λ () ; (fsuc _) → λ () })
               (λ { fzero               → (fzero      , lo) , refl
                  ; (fsuc fzero)        → (fzero      , hi) , refl
                  ; (fsuc (fsuc fzero)) → (fsuc fzero , hi) , refl })

open import CSP.Examples.Cardano_network.Parametric.Node leiosLParams leiosLLine apiES
  using (Proc; nodeWith; systemOfWithNode)
open NLL.Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)
  using (StateL; nodeLogicL; st₀)

-- the Linear-Leios node logic at every node of the line, every store initially empty
nodeLogicL′ : Fin 3 → StateL → Proc
nodeLogicL′ = nodeLogicL

-- THE WITNESS: the three-node Leios line running the Linear-Leios logic at every node
-- over the PROTOTYPE peer bundle and the concrete per-link multiplexer
leiosSystemL : Proc
leiosSystemL =
  systemOfWithNode (nodeWith nodeBundleP) NetworkLinkBreakableA (λ n → nodeLogicL n st₀)

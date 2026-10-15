{-# OPTIONS --guardedness #-}

-- Concrete parameters for the trace-replay bridge (Phase 5, amendment B4):
-- EB = EBHash = LSlot = ℕ with `ebHash = id`, every other domain ⊤, no
-- mempool (`ebTxs = const []`), and a 2-node, 1-link topology.  Node 0 sits
-- at `(link 0 , lo)`, node 1 at `(link 0 , hi)`.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.ReplayParams where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
import Class.DecEq.Instances as DecEqI

open import Cardano_network.Base using (Dir; lo; hi; IDs; N2N_LeiosFetch)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology; mkTopology)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP

-- both directions of LeiosFetch on the single link
replayCfg : List (Dir × IDs)
replayCfg = (lo , N2N_LeiosFetch) ∷ (hi , N2N_LeiosFetch) ∷ []

-- the replay `Params`: real identifiers for EBs and slots, ⊤ elsewhere
replayParams : Params
replayParams = record
  { Cookie = ⊤ ; Block = ⊤ ; LSlot = ℕ ; VoterId = ⊤ ; VoteBlob = ⊤
  ; Time = ⊤ ; Length = ⊤ ; time₀ = tt ; length₀ = tt
  ; numLinks = 1 ; linkConfig = λ _ → replayCfg
  ; RbHash = ⊤ ; rbHash = λ _ → tt
  ; EB = ℕ ; EBHash = ℕ ; ebHash = λ h → h
  ; Tx = ⊤ ; TxHash = ⊤ ; txHash = λ _ → tt
  ; slotOf = λ _ → 0 ; announcedEB = λ _ → nothing
  ; Size = ⊤ ; txSize = λ _ → tt
  ; decCookie = DecEqI.DecEq-⊤ ; decBlock = DecEqI.DecEq-⊤
  ; decLSlot = DecEqI.DecEq-ℕ ; decVoterId = DecEqI.DecEq-⊤
  ; decVoteBlob = DecEqI.DecEq-⊤ ; decTime = DecEqI.DecEq-⊤
  ; decLength = DecEqI.DecEq-⊤ ; decEB = DecEqI.DecEq-ℕ
  ; decEBHash = DecEqI.DecEq-ℕ ; decRbHash = DecEqI.DecEq-⊤
  ; decTx = DecEqI.DecEq-⊤ ; decTxHash = DecEqI.DecEq-⊤
  ; decSize = DecEqI.DecEq-⊤ }

-- the replay Leios parameters: nothing certifies, no RB carries a certificate
replayLP : LeiosP.LeiosParams replayParams
replayLP = record
  { mkVoteBlob = λ _ _ → tt ; blobVoter = λ _ → tt ; blobRb = λ _ → tt
  ; blobVoter-mk = λ _ _ → refl ; blobRb-mk = λ _ _ → refl
  ; certifies = λ _ _ → false
  -- ponytail: no mempool, BlockTxs bodies always empty (the log forgets them);
  -- upgrade path = real ebTxs + mempool if bitmaps/numTxs ever get constrained
  ; ebTxs = λ _ → []
  ; ebSize = λ _ → tt ; rbCert = λ _ → nothing }

-- the link's (lo-end , hi-end) nodes: node 0 — node 1
replayEnds : Fin 1 → Fin 2 × Fin 2
replayEnds _ = fzero , fsuc fzero

-- the 2-node, 1-link topology
replayTopo : Topology replayParams
replayTopo = mkTopology 1 replayEnds (λ _ ())
  (λ { fzero → (fzero , lo) , refl ; (fsuc fzero) → (fzero , hi) , refl })

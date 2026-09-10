{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the first CONCRETE LEIOS SCENARIO: a
-- three-node line whose Leios data domains (`EB`, `EBHash`, `Block`)
-- are genuinely non-trivial.
--
-- WHY THIS FILE.  `Parametric.NodeLogic.Generic` (the topology-generic
-- relay logic) and `Parametric.AnnounceSafe.Generic` (the topology-generic
-- announcement-safety statement) are both only PARAMETERISED modules; the
-- only composed relay system anywhere in the repo is `NodeLogic.agda`'s
-- own `lineRelaySystem`, built over `Parametric.LineInstance.lineParams`
-- where `EB = EBHash = ⊤` and `announcedEB = λ _ → nothing`.  With that
-- `Params` the announcement gate is VACUOUS — `AnnounceSafe.Generic`'s
-- `announceOK` always returns `true`, because no header ever announces
-- an EB — and `AnnounceSafe.Generic` is instantiated NOWHERE in the repo.
-- This file supplies the missing composition: its own `Params` (`leiosParams`)
-- with `EB = EBHash = Bool` (two distinguishable EBs/hashes, so `mintedIn`
-- is non-degenerate) and `Block = Maybe Bool` (an RB either announces no
-- EB or one of the two hashes, so BOTH branches of `announceOK` are
-- reachable), plus the concrete `AnnounceSafe` statement and its concrete
-- per-node reduction, at that `Params` and the same three-node line graph
-- as `LineInstance`.
--
-- As with `LineInstance` and `NodeLogic`'s own sanity check, the premises
-- below are HYPOTHESES — nothing is discharged here.  This file is a
-- composition/typechecking witness only.
------------------------------------------------------------------------

import Data.Unit as U
open import Data.Bool using (Bool)
import Data.Bool.Properties as BoolProp
open import Data.Maybe using (Maybe)
import Data.Maybe.Properties as MaybeProp
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; [])
open import Relation.Nullary using (yes; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; mkTopology)

module CSP.Examples.Cardano_network.Parametric.LeiosInstance where

------------------------------------------------------------------------
-- The scenario parameters — same three-node line graph as `LineInstance`,
-- but its OWN `Params` (non-trivial Leios domains, so a fresh instantiation)
------------------------------------------------------------------------

-- trivial decidable equality for the ⊤ data domains that stay inert here (every
-- domain except `EB`/`EBHash`/`Block`, exactly as in `LineInstance.lineDecEq⊤`)
leiosDecEq⊤ : DecEq U.⊤
leiosDecEq⊤ = record { _≟_ = λ _ _ → yes refl }

-- decidable equality for the two-valued `EB`/`EBHash` domain, from the stdlib
leiosDecEqBool : DecEq Bool
leiosDecEqBool = record { _≟_ = BoolProp._≟_ }

-- decidable equality for the `Block` domain (`Maybe Bool`: no announcement, or one
-- of the two EB hashes), built from `leiosDecEqBool`'s underlying decision procedure
leiosDecEqMaybeBool : DecEq (Maybe Bool)
leiosDecEqMaybeBool = record { _≟_ = MaybeProp.≡-dec BoolProp._≟_ }

-- both directions × the four Praos wire protocols PLUS LeiosNotify, on every link.
-- This differs from `LineInstance.lineCfg`, which carries the four Praos protocols
-- only.  The LN entries are LOAD-BEARING, not decoration: `linkConfig` is what
-- builds the medium's cells — `linkCopy l = ⦀⋆ (map … (linkConfig l))`
-- (`Network.agda:269`) for the abstract copy medium, and `Inputsₗ`/`Outputsₗ`
-- (`NetworkLink.agda:114,118`) for the concrete multiplexer.  Without a
-- `N2N_LeiosNotify` entry there is no cell to carry `MsgLNRequestNext` or
-- `MsgLNBlockAnnouncement`, so no LN peer on one node can ever reach a peer on
-- another and every announcement is unreachable at system level.
--
-- LeiosFetch is deliberately still absent: nothing in `Parametric.NodeLogic`
-- drives an LF peer, so a cell for it would be dead weight.  Add it alongside the
-- LF threads when cross-protocol availability is taken up.
leiosCfg : List (Dir × IDs)
leiosCfg = (lo , N2N_KeepAlive)    ∷ (hi , N2N_KeepAlive)
         ∷ (lo , N2N_ChainSync)    ∷ (hi , N2N_ChainSync)
         ∷ (lo , N2N_BlockFetch)   ∷ (hi , N2N_BlockFetch)
         ∷ (lo , N2N_TxSubmission) ∷ (hi , N2N_TxSubmission)
         ∷ (lo , N2N_LeiosNotify)  ∷ (hi , N2N_LeiosNotify) ∷ []

-- concrete Params for the Leios scenario: every non-Leios domain ⊤, TWO links,
-- uniform config, and a NON-TRIVIAL Leios domain — two distinguishable EBs/hashes,
-- and an RB that either announces nothing or one of them
leiosParams : Params
leiosParams = record
  { Cookie = U.⊤ ; Block = Maybe Bool ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; numLinks = 2 ; linkConfig = λ _ → leiosCfg
  ; decCookie = leiosDecEq⊤ ; decBlock = leiosDecEqMaybeBool ; decTxid = leiosDecEq⊤
  ; decLSlot = leiosDecEq⊤ ; decVoterId = leiosDecEq⊤ ; decLFBitmap = leiosDecEq⊤
  ; decVoteBlob = leiosDecEq⊤
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = leiosDecEq⊤ ; decLength = leiosDecEq⊤
  -- Leios EB domains, NON-TRIVIAL here: two hashes, an RB announcing either or none
  ; EB = Bool ; EBHash = Bool ; decEB = leiosDecEqBool ; decEBHash = leiosDecEqBool
  ; ebHash = λ e → e ; announcedEB = λ b → b }

open import CSP.Examples.Cardano_network.Net leiosParams using (Link; Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data leiosParams using (Payload)
open import CSP.Examples.Cardano_network.NetCommon leiosParams
  using (NetworkLinkBreakableA; ioES)

-- the {| all api channels |} alphabet, shared with every other gate-free scenario
open import CSP.Examples.Cardano_network.ApiAlphabet leiosParams using (apiES)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (_∥⇘_⇙_; _∖_; ⦀Fin⁺)

------------------------------------------------------------------------
-- The line graph (identical shape to `LineInstance.line`, at `leiosParams`)
------------------------------------------------------------------------

-- the (lo-end , hi-end) pair of each link: link 0 joins A—B, link 1 joins B—C,
-- with node 0 = A, node 1 = B (the degree-2 middle), node 2 = C
leiosEnds : Link → Fin 3 × Fin 3
leiosEnds fzero    = fzero , fsuc fzero
leiosEnds (fsuc _) = fsuc fzero , fsuc (fsuc fzero)

-- the three-node line as a `Topology` at `leiosParams`: `endpointsOf` and its three
-- endpoint laws are all DERIVED by `mkTopology` from `leiosEnds`, exactly as in
-- `LineInstance.line`
leiosLine : Topology leiosParams
leiosLine = mkTopology 2 leiosEnds
              (λ { fzero → λ () ; (fsuc _) → λ () })
              (λ { fzero            → (fzero      , lo) , refl
                 ; (fsuc fzero)     → (fzero      , hi) , refl
                 ; (fsuc (fsuc fzero)) → (fsuc fzero , hi) , refl })

------------------------------------------------------------------------
-- The composed system: the real relay logic over the non-trivial Leios domains
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Parametric.Node leiosParams leiosLine apiES
  using (Proc; node; systemOf)
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
open NL.Generic leiosParams leiosLine apiES using (nodeLogic)
open AS.Generic leiosParams leiosLine apiES
  using (AnnounceSpec; AnnounceSafe; announceSafe-from-nodes)

-- the three-node Leios line running the real relay logic at every node, each store
-- initially empty: a TYPECHECKING WITNESS that the relay logic composes over a
-- `Params` whose EB/hash/Block domains are genuinely non-trivial
leiosSystem : Proc
leiosSystem = systemOf (λ n → nodeLogic n [])

------------------------------------------------------------------------
-- Announcement safety at the Leios line, concretely
------------------------------------------------------------------------

open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⊑F_)

-- announcement safety of the concrete three-node Leios line: no `apiLN …
-- sendLNBlockAnnouncement` may announce an EB hash that no `env … envMint` minted.
-- The property is non-vacuous here (unlike at `LineInstance.lineParams`, where
-- `announcedEB` is always `nothing`) because `leiosParams.announcedEB` genuinely
-- announces both hashes.
leiosAnnounceSafe : Set₁
leiosAnnounceSafe = AnnounceSafe

-- the reduction of `leiosAnnounceSafe` to one `⊑F` obligation per node plus one for
-- the medium, plus a residual composite-safety goal — `AnnounceSafe.Generic`'s
-- `announceSafe-from-nodes` instantiated at `Node := Fin 3`, `numNodes-1 := 2`.  The
-- premises are HYPOTHESES; nothing is discharged here (same framing as
-- `LineInstance.line-assembly`).
leios-announceSafe-from-nodes :
    (mSpec : Proc) (nSpec : Fin 3 → Proc)
  → mSpec ⊑F NetworkLinkBreakableA
  → (∀ n → nSpec n ⊑F node n (nodeLogic n []))
  → AnnounceSpec ⊑F ((mSpec ∥⇘ ioES ⇙ ⦀Fin⁺ 2 nSpec) ∖ ioES)
  → AnnounceSafe
leios-announceSafe-from-nodes = announceSafe-from-nodes NetworkLinkBreakableA

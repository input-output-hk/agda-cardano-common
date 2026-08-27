{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- InFlightOpen completion, Tasks 1 and 2c — THE io INTRO LADDERS.
-- Task 1 built the OUTPUT-direction pair (§1-§5); Task 2c added the three the
-- SERVER positions need: the INPUT-direction medium ladder (§6, §8), the medium-τ
-- ladder for the `draining` arm (§7, §8) and the server-fired nodes ladder (§9).
--
-- WHY THIS MODULE EXISTS.  Every `IoOffers` INTRO lemma banked before this file
-- is an **api** one (`LiveStableOffer`'s `bundle-offer-recv` / `nodes-offer-B` /
-- `apiNodes-whole` family): the api ladders lift a driver↔peer SYNC.  The two
-- io in-flight positions (`lpUpCell`/`lpDnCell`) need the OTHER shape — a
-- medium⊗nodes io SYNC, whose two operands are (a) the whole breakable medium
-- and (b) the whole four-node interleave, and inside a node the io event goes
-- SOLO past the `∥⇘ apiES ⇙` gate rather than syncing with the driver.  Neither
-- operand's intro existed; both are built here, and NOTHING here mentions an
-- invariant, a leg, a block or reachability — these are operand-generic
-- transport lemmas, exactly the two priced-ladder premises the LegPos-24 spike
-- left as module parameters (`medOfferOut` / `cliOutNodes`).
--
-- CONTENTS
--   §1  LN (pre-rename `Net Payload`) plumbing: the offer existential, the
--       `viewV`-nothing bridge and the interleave intro/non-offer, i.e. the
--       `Net Payload` mirrors of `SysStep`'s `IoOffers`/`⦀-ev-L`/`⦀-noOffer`
--       (the banked ones are all at `Net_Api Payload`).
--   §2  the CELL rung: a `full x` cell FIRES its `output` (rung 1 is the banked
--       `SysOracle_NodeTauEv.offer-full`), and a cell at any OTHER key refuses.
--   §3  the 12-cell `⦀⋆` rung at the `(hi , N2N_BlockFetch)` key — the one
--       genuinely new rung the spike named.  It is specialised to that key on
--       purpose: the general lemma would be a 12-way dispatch (`uniformCfg` has
--       twelve cells per link) and no consumer in the campaign needs any other
--       key, since both cell positions are BlockFetch `hi` cells
--       (`PipeInv.cellUp`/`cellDn`).
--   §4  the RENAME rung (`renameMap` FORWARD — the banked direction is
--       `renameMap-ev-reflect-ι`), the `△` rung with the LEFT operand firing
--       (mirror of `WalkBrkFire.△-fire-Q`), the per-link fire and the four-link
--       `⦀Fin` rung: `medOfferOut`, the whole-medium io intro.
--   §5  the four nodes-side READER ladders (`cliOutNodes-*`).
--   §6  (Task 2c) the same cell/fold/rename/`△` rungs in the INPUT direction, for
--       the SENDER's wire-send — H19's `empty` arm.
--   §7  (Task 2c) the medium-τ rungs, for H19's `draining` arm: the cell's own
--       drain `sil`, the τ push-forward through the rename (the one substantive
--       new rung) and the `△`-τ intro.
--   §8  (Task 2c) the two whole-medium intros the two new ladders end in:
--       `medOfferIn` and `medDrainτ`.
--   §9  (Task 2c) the four nodes-side SERVER ladders (`srvInNodes-*`), one per
--       cell-filling BF server: node A twice, node B, node C.
--
-- *** KEEP IN SYNC — THE SEVEN CROSS-ALPHABET MIRRORS, PART BY PART. ***  This
-- module edits nothing banked, but seven of its rungs are TRANSCRIPTIONS of banked
-- lemmas at another alphabet instance or another operand side, so a change to a
-- counterpart would rot them silently.  Every anchor was re-derived by grep
-- (Task 2 of the InFlightOpen completion campaign; the last three by Task 2c,
-- whose insertions also shifted — and so re-derived — every self-anchor below):
--
--   · §1's five LN items — `IoOffersN` (`:213`), `noOfferN→viewV` (`:218`),
--     `⦀N-ev-L` (`:229`), `⦀N-ev-R` (`:236`), `⦀N-noOffer` (`:244`) — mirror
--     `R2_Bisim/SysStep`'s `IoOffers` (`:386-387`), `⦀-ev-L` (`:1618-1622`),
--     `⦀-ev-R` (`:1624-1628`), `⦀-noOffer` (`:895-897`) and
--     `R2_Bisim/SysOracle_GapBDisj.noOffer→viewV` (`:1096-1099`).  SAME proofs at
--     the `Net Payload` instance of the same generic `TraceLawsParallel` /
--     `TraceLawsParallelElim` laws — the banked ones are all at `Net_Api Payload`.
--   · `rnN-vis-just` (`:373`) mirrors
--     `CSP/Laws/Traces/TraceLawsRename.ren-vis-just` (`:82-88`), which is stated
--     for the SAME-alphabet `_⟦ inv ⟧ⁱ` and does not apply to this
--     cross-alphabet `CSP.Rename` instance.
--   · `△-fire-P` (`:405`) mirrors `LTL/Walk/WalkBrkFire.△-fire-Q` (`:109-114`) —
--     the OTHER operand side of the same `△-merge` clause.
--   · the four-link `⦀Fin` nest inside `medOfferOut` (`:482-556`, `nestEq = refl`
--     at `:495-496`) is spelled out exactly as
--     `LTL/Walk/WalkBrkFire.medium-break-fire` (`:199-241`, its own `nestEq` at
--     `:196-197`) does, one channel harder (a break needs no cell fold).
--   · `extBranchN-just` (`:1027`) mirrors
--     `CSP/Laws/Traces/TraceLawsRename.extBranch-just-inv` (`:98-105`) and
--     `renameMap-τ-fwd` (`:1040`) mirrors its `ren-τ-fwd` (`:107-114`) — again the
--     same-alphabet `_⟦ inv ⟧ⁱ` statements, at this `ιNet` instance instead.  The
--     `sil` half is genuinely banked and is USED, not transcribed
--     (`R2_Bisim/SysOracle_TauCore.RenTC.force-renameMap-sil`, `:311-314`).
--   · `△-τ-tag0` (`:1051`) is the INTRO mirror of
--     `R2_Bisim/SysOracle_TauCore.△-τ-branch-inv`'s firing clause (`:817-819`) —
--     same `pair fin _ / lift fzero` tag, same `viewT` reduction, other direction.
--   · §8's private four-link nest (`gnestEq`, `:1128-1129`) is a COPY of §4's
--     (`:495-496`): §4's is private to its own `module _ (m : MedState)` block and
--     hoisting it would have touched a landed proof.  Both are `numLinks = 4`
--     spelled out; change one, change the other.
--
-- DELIBERATELY NOT INSTANTIATED, and recorded so the choice is not re-litigated:
-- `R2_Bisim/SysIoLink5`'s `RenFwd` (module `:223`, `renameMap-ev-fwd` `:262-266`)
-- IS the generic cross-alphabet visible intro and has six instances, but no
-- `ιNet` one; `rnN-vis-just` + `renameMap-ev-out-fwd` (20 lines) were transcribed
-- locally instead, to keep the frozen 8,585-line `SysIoLink5` out of this
-- module's stated dependencies.  Instantiating `RenFwd` saves ~15 lines and
-- inherits that dependency.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using ( 0ℓ; Lift; lift )
open import Data.Bool using ( Bool; true; false )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Unit using () renaming ( ⊤ to ⊤₀; tt to tt₀ )
open import Data.List using ( List; []; _∷_; map )
open import Data.Fin using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Relation.Nullary using ( ¬_; yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )

open import Process_Trees
  using ( PTree; ExtI; AnyTypes; ContinueType; ret; sil; react; react-injective
        ; pair; fin )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveIoIntro
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Net_Api; Net_Api-≟; Link; break; input; output )
-- (T11) §10's two ladders are stated at the RANGE-REQUEST payload: the server's
-- read rung is lenient in `(time , mode , length)` exactly as `ceqBFs01` is, and
-- the client's write rung is pinned at `ceqBFc07`'s own literal tuple
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; blockFetch; ChainRange; MsgRequestRange )
open import CSP.Examples.Cardano_network.NetCommon p
  using ( ιNet; ιNet⁻¹; ιNet-linv; ioES )
open import CSP.Examples.Cardano_network.Params using ( Params )
-- (T11) §10's server-read rung quantifies the payload's three lenient components
open Params p using ( numLinks; linkConfig; time₀; length₀; Time; Length )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi; IDs; FromResponder; Mode; FromInitiator
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive
  ; N2N_LeiosNotify; N2N_LeiosFetch )
import CSP.Examples.Cardano_network.BlockFetch p as BF

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as OpA
open OpA using ( _△_; _⦀_; Skip; Prefix₀; ⦀Fin; viewV; EventSet )
open EventSet using ( mem )

import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; sVis; τ; sSil; sTau )
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN

import CSP.Laws.Traces.TraceLawsParallel     (Net-≟ {Payload}) as TLPN
import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Payload}) as PEN

-- the medium's own alphabet rename (the SAME `CSP.Rename` instance `decLink`
-- is defined with — see `SysMedium.decLink`)
import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload}
  ιNet ιNet⁻¹ ιNet-linv as RenNet
open RenNet using ( renameMap; rnFan; rnCollect; invRel; invPreimg; ι-vis-inv
                  ; extBranch; extBwd; extFwd; ext-linv )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; phase; broken; decMed; decLink; decCopy
        ; CopyPhase; empty; full; draining; NetProcN; vis-of )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( NetProc; VmapN; TmapN; VmapNN; TmapNN; fold-react; ReactF; mkReactF
               ; ffull-react; fdrain; force-△-react )
open STC.MedNO using ( force-renameMap-react; force-renameMap-sil )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA as SNT
open SNT using ( retN-no-ev; offer-empty; offer-full )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( IoOffers; ⦀-ev-L; ⦀-ev-R; ⦀-noOffer; ∥⇘⇙-ev-soloL; ⦀-τ-L; ⦀-τ-R
        ; absBFc; absBFs; absBundleG; absNodeA; absNodeB; absNodeC; absNodeD
        ; absNodesOf; coarsenBFc; coarsenBFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; nA; nB; nC; nD )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( ApiHasLink; ahlIn; ahlOut; io⇒¬api; linkAB≢linkAC )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  -- (T11) §10's two rung-1s: the BF client's own request WRITE (`ceqBFc07`) and
  -- the BF server's own request READ (`ceqBFs01`)
  using ( aBFc; ceqBFc05; ceqBFc07; aBFs; ceqBFs11; ceqBFs01 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteKaTs blkA
  using ( absBFs-dir-noBoth; absBundle-BFs-ev; absBundle-BFc-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( absKAc-noBF; absKAs-noBF; absCSc-noBF; absCSs-noBF
        ; absTSc-noBF; absTSs-noBF; absLNc-noBF; absLNs-noBF
        ; absLFc-noBF; absLFs-noBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( absBundleG-io-no; nodeA-drv-io-no; nodeB-drv-io-no; nodeC-drv-io-no
        ; nodeD-drv-io-no; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink3 blkA
  using ( absNodeA-io-fp; absNodeB-io-fp; absNodeC-io-fp; absNodeD-io-fp
        ; absGroupA-io-no; absGroupB-io-no
        ; absNodeA-io-no-when-B; absNodeA-io-no-when-C; absNodeA-io-no-when-D
        ; absNodeB-io-no-when-C; absNodeB-io-no-when-D
        ; absNodeC-io-no-when-D; absNodeD-io-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeMedKey blkA
  using ( cell-in-key; decLink-ev-in-key; cell-out-key; decLink-ev-out-key )

------------------------------------------------------------------------
-- §1  LN PLUMBING — the `Net Payload` mirrors of `SysStep`'s currency.
--
-- The cells live in the PRE-RENAME alphabet `Net Payload` (`decCopy`), so none
-- of `SysStep`'s `IoOffers`/`⦀-ev-L`/`⦀-noOffer` applies to them: those are
-- `Net_Api Payload`.  All four items below are the SAME proofs at the other
-- alphabet instance of the same generic parallel laws.
------------------------------------------------------------------------

-- `Skip` pinned at the whole-system result level (kills the `ℓr` level meta —
-- the `WalkBrkFire.SkipN` trick)
SkipA : NetProc
SkipA = Skip

-- the LN offer existential (mirror of `SysStep.IoOffers`)
IoOffersN : NetProcN → {X : Set 0ℓ} → Net Payload X → X → Set₁
IoOffersN P {X} e a = Σ[ M ∈ NetProcN ] (P LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M)

-- an LN process offering no visible step at `(e,a)` has `viewV … ≡ nothing`
-- there (mirror of `SysOracle_GapBDisj.noOffer→viewV`)
noOfferN→viewV : (P : NetProcN) {X : Set 0ℓ} {e : Net Payload X} {a : X}
  → ¬ IoOffersN P e a → OpN.viewV (PTree.force P) (X , e) a ≡ nothing
noOfferN→viewV P {X} {e} {a} ¬off with PTree.force P in fEq
... | ret _  = refl
... | sil _  = refl
... | react v τc with v (X , e) a in vEq
...   | nothing = refl
...   | just P′ = ⊥-elim (¬off (P′ , LN.sVis fEq vEq))

-- solo visible intro through the LN interleave, LEFT operand firing
-- (mirror of `SysStep.⦀-ev-L`)
⦀N-ev-L : (P Q : NetProcN) {X : Set 0ℓ} {e : Net Payload X} {a : X} {P′ : NetProcN}
  → P LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► P′
  → OpN.viewV (PTree.force Q) (X , e) a ≡ nothing
  → (P OpN.⦀ Q) LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► (P′ OpN.⦀ Q)
⦀N-ev-L P Q step nq = TLPN.Par-soloL OpN.∅ES (λ _ _ → tt) P Q (λ z → z) step nq

-- … RIGHT operand firing (mirror of `SysStep.⦀-ev-R`)
⦀N-ev-R : (P Q : NetProcN) {X : Set 0ℓ} {e : Net Payload X} {a : X} {Q′ : NetProcN}
  → Q LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Q′
  → OpN.viewV (PTree.force P) (X , e) a ≡ nothing
  → (P OpN.⦀ Q) LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► (P OpN.⦀ Q′)
⦀N-ev-R P Q step np = TLPN.Par-soloR OpN.∅ES (λ _ _ → tt) P Q (λ z → z) step np

-- an LN interleave offers nothing when neither operand does
-- (mirror of `SysStep.⦀-noOffer`)
⦀N-noOffer : {X : Set 0ℓ} {e : Net Payload X} {a : X} (P Q : NetProcN)
  → ¬ IoOffersN P e a → ¬ IoOffersN Q e a → ¬ IoOffersN (P OpN.⦀ Q) e a
⦀N-noOffer P Q ¬P ¬Q (M , step) with PEN.Par-ev-elim OpN.∅ES (λ _ _ → tt) P Q step
... | PEN.evSync () _ _
... | PEN.evL  _ sP     = ¬P (_ , sP)
... | PEN.evR  _ sQ     = ¬Q (_ , sQ)
... | PEN.evBoth _ sP _ = ¬P (_ , sP)

-- the fold's empty tail (`⦀⋆ [] = Skip`, a `ret`) offers nothing
skipN-no-ev : {X : Set 0ℓ} {e : Net Payload X} {a : X} → ¬ IoOffersN (⦀⋆ []) e a
skipN-no-ev (M , step) = retN-no-ev {P = OpN.Skip} refl step

------------------------------------------------------------------------
-- §2  THE CELL RUNG.
------------------------------------------------------------------------

-- a `full x` cell FIRES its own `output l d id ! x`: `ffull-react` exposes the
-- react force and the banked `offer-full` menu reads the successor off it
-- (rung 1 of the medium ladder, in the INTRO direction)
cell-out-fire : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → IoOffersN (decCopy l d id (full x)) (output l d id) x
cell-out-fire l d id x with ffull-react l d id x
... | V , T , feq , _ =
    _
  , LN.sVis feq
      (trans (sym (cong (λ n → vis-of n (Payload , output l d id) x) feq))
             (offer-full l d id x))

-- a cell whose OWN direction differs from the fired one refuses: the banked
-- `cell-out-key` pins the fired key to the cell's own key
cell-no-out-d : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → d₀ ≢ d → ¬ IoOffersN (decCopy l d id ph) (output l d₀ id₀) x
cell-no-out-d l d id ph ¬d (M , step) with cell-out-key l d id ph step
... | _ , de , _ , _ , _ = ¬d de

-- … and one whose own PROTOCOL id differs
cell-no-out-i : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → id₀ ≢ id → ¬ IoOffersN (decCopy l d id ph) (output l d₀ id₀) x
cell-no-out-i l d id ph ¬i (M , step) with cell-out-key l d id ph step
... | _ , _ , ide , _ , _ = ¬i ide

-- … the two, as the `viewV`-nothing the interleave intro consumes
cell-no-out-dv : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → d₀ ≢ d
  → OpN.viewV (PTree.force (decCopy l d id ph)) (Payload , output l d₀ id₀) x ≡ nothing
cell-no-out-dv l d id ph ¬d = noOfferN→viewV _ (cell-no-out-d l d id ph ¬d)

cell-no-out-iv : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → id₀ ≢ id
  → OpN.viewV (PTree.force (decCopy l d id ph)) (Payload , output l d₀ id₀) x ≡ nothing
cell-no-out-iv l d id ph ¬i = noOfferN→viewV _ (cell-no-out-i l d id ph ¬i)

------------------------------------------------------------------------
-- §3  THE 12-CELL `⦀⋆` RUNG at the `(hi , N2N_BlockFetch)` key.
--
-- `linkConfig l` is `uniformCfg` at every link (`FourNodeDiamond`, and
-- `SysOracle_TauCore.cfgEq l = refl`), so the fold is the explicit twelve-cell
-- nest below and the BlockFetch `hi` cell sits at position 5.  The five cells
-- before it and the six after it (plus the `Skip` tail) refuse by §2's key
-- mismatch.
------------------------------------------------------------------------

-- the whole link fold OFFERS the `hi`-BlockFetch cell's `output` when that cell
-- holds `x`
fold-offers-out : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_BlockFetch ≡ full x
  → IoOffersN (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))
              (output l hi N2N_BlockFetch) x
fold-offers-out l ph x hf =
    _
  , ⦀N-ev-R c0 _
      (⦀N-ev-R c1 _
        (⦀N-ev-R c2 _
          (⦀N-ev-R c3 _
            (⦀N-ev-R c4 _
              (⦀N-ev-L c5 _ fire
                (noOfferN→viewV _ noTail))
              (cell-no-out-dv l lo N2N_BlockFetch (ph lo N2N_BlockFetch) (λ ())))
            (cell-no-out-iv l hi N2N_ChainSync (ph hi N2N_ChainSync) (λ ())))
          (cell-no-out-dv l lo N2N_ChainSync (ph lo N2N_ChainSync) (λ ())))
        (cell-no-out-iv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) (λ ())))
      (cell-no-out-dv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) (λ ()))
  where
  -- the twelve cells of the link's `uniformCfg` fold, in the config's order
  c0 c1 c2 c3 c4 c5 : NetProcN
  c0 = decCopy l lo N2N_KeepAlive    (ph lo N2N_KeepAlive)
  c1 = decCopy l hi N2N_KeepAlive    (ph hi N2N_KeepAlive)
  c2 = decCopy l lo N2N_ChainSync    (ph lo N2N_ChainSync)
  c3 = decCopy l hi N2N_ChainSync    (ph hi N2N_ChainSync)
  c4 = decCopy l lo N2N_BlockFetch   (ph lo N2N_BlockFetch)
  c5 = decCopy l hi N2N_BlockFetch   (ph hi N2N_BlockFetch)
  -- the fired cell's own step, with the phase hypothesis substituted in
  fire : c5 LN.─[ LN.ev (LN.evl (LN.evLabel Payload (output l hi N2N_BlockFetch) x)) ]─►
         proj₁ (cell-out-fire l hi N2N_BlockFetch x)
  fire = subst (λ z → decCopy l hi N2N_BlockFetch z
                        LN.─[ LN.ev (LN.evl (LN.evLabel Payload (output l hi N2N_BlockFetch) x)) ]─►
                      proj₁ (cell-out-fire l hi N2N_BlockFetch x))
               (sym hf) (proj₂ (cell-out-fire l hi N2N_BlockFetch x))
  -- the six cells AFTER the BlockFetch `hi` cell, plus the `Skip` tail
  noTail : ¬ IoOffersN
             (decCopy l lo N2N_TxSubmission (ph lo N2N_TxSubmission) OpN.⦀
              (decCopy l hi N2N_TxSubmission (ph hi N2N_TxSubmission) OpN.⦀
               (decCopy l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) OpN.⦀
                (decCopy l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) OpN.⦀
                 (decCopy l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) OpN.⦀
                  (decCopy l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) OpN.⦀ ⦀⋆ []))))))
             (output l hi N2N_BlockFetch) x
  noTail =
    ⦀N-noOffer _ _ (cell-no-out-d l lo N2N_TxSubmission (ph lo N2N_TxSubmission) (λ ()))
      (⦀N-noOffer _ _ (cell-no-out-i l hi N2N_TxSubmission (ph hi N2N_TxSubmission) (λ ()))
        (⦀N-noOffer _ _ (cell-no-out-d l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) (λ ()))
          (⦀N-noOffer _ _ (cell-no-out-i l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) (λ ()))
            (⦀N-noOffer _ _ (cell-no-out-d l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) (λ ()))
              (⦀N-noOffer _ _ (cell-no-out-i l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) (λ ()))
                skipN-no-ev)))))

------------------------------------------------------------------------
-- §4  THE RENAME, `△` AND `⦀Fin` RUNGS — `medOfferOut`.
------------------------------------------------------------------------

-- the fan-in offer map of the medium's rename, at an ι-IMAGE event whose source
-- offer is `just P₁`: the preimage is a singleton, so the fan collapses to the
-- renamed successor.  (Transcription of `TraceLawsRename.ren-vis-just` at THIS
-- cross-alphabet `CSP.Rename` instance — the banked one is stated for the
-- same-alphabet `_⟦ inv ⟧ⁱ` and does not apply here.)
rnN-vis-just : (X : Set 0ℓ) (e₂ : Net_Api Payload X) (b : X) (vP : VmapNN)
               {at : AnyTypes (Net Payload)} {a : proj₁ at} {P₁ : NetProcN}
  → ι-vis-inv (X , e₂) b ≡ just (at , a) → vP at a ≡ just P₁
  → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
          (rnCollect vP (invPreimg ι-vis-inv (X , e₂) b))
    ≡ just (renameMap P₁)
rnN-vis-just X e₂ b vP eq-inv eq-v
  with ι-vis-inv (X , e₂) b | eq-inv
... | just (at , a) | refl with vP at a | eq-v
...   | just P₁ | refl = refl

-- the medium's ι sends the LN `output` to the api `output` and the inverse
-- takes it back, so the visible preimage of the fired label is the source event
ι-vis-inv-out : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → ι-vis-inv (Payload , output l d id) x
    ≡ just ((Payload , output l d id) , x)
ι-vis-inv-out l d id x = refl

-- FORWARD transport of a visible step through the medium's rename (the banked
-- direction is `renameMap-ev-reflect-ι`; this is its intro mirror, at the ONE
-- label shape the ladder fires)
renameMap-ev-out-fwd : (P : NetProcN) (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → IoOffersN P (output l d id) x
  → IoOffers (renameMap P) (output l d id) x
renameMap-ev-out-fwd P l d id x (M , LN.sVis {v = vP} {τc = τcP} feq br) =
    renameMap M
  , sVis (force-renameMap-react {P = P} feq)
         (rnN-vis-just Payload (output l d id) x vP (ι-vis-inv-out l d id x) br)

-- the `△` interrupt fires the LEFT operand's offer when the RIGHT refuses
-- (mirror of `WalkBrkFire.△-fire-Q`, other side: `△-merge`'s
-- `just P′ | nothing` clause commits to `P′ △ Q`)
△-fire-P : {P Q : NetProc}
    {vP : (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe NetProc)}
    {τcP : (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe NetProc)}
    {vQ : (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe NetProc)}
    {τcQ : (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe NetProc)}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {P′ : NetProc}
  → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
  → vP (X , e) a ≡ just P′ → vQ (X , e) a ≡ nothing
  → (P △ Q) ─[ ev (evl (evLabel X e a)) ]─► (P′ △ Q)
△-fire-P {P} {Q} {vP} {τcP} {vQ} {τcQ} {X} {e} {a} {P′} eqP eqQ vPj vQno =
  sVis (force-△-react eqP eqQ) mergeEq
  where
  mergeEq : OpA.△-merge (react vP τcP) (react vQ τcQ) Q (X , e) a ≡ just (P′ △ Q)
  mergeEq rewrite vPj | vQno = refl

-- the `break l ⟶₀ Skip` prefix does NOT offer a copy-channel io: `Net_Api-≟`
-- decides the two constructors apart with no link/dir/id test at all
prefix-no-out : (i l : Link) (d : Dir) (id : IDs) (x : Payload)
  → viewV (PTree.force (Prefix₀ (break i) (SkipA))) (Payload , output l d id) x
    ≡ nothing
prefix-no-out i l d id x = refl

-- an UNBROKEN link whose `hi`-BlockFetch cell holds `x` offers that cell's
-- `output` out of the WHOLE per-link decode: the fold fires (§3), the rename
-- transports it (§4) and the `△` commits to the left operand
link-offers-out : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_BlockFetch ≡ full x
  → IoOffers (decLink l ph false) (output l hi N2N_BlockFetch) x
link-offers-out l ph x hf with fold-react l ph
... | mkReactF V T feq =
    _
  , △-fire-P
      (force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
      refl
      (proj₂ renOff)
      (prefix-no-out l l hi N2N_BlockFetch x)
  where
  renOff : Σ[ M ∈ NetProc ]
             (rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
                    (rnCollect V (invPreimg ι-vis-inv (Payload , output l hi N2N_BlockFetch) x))
              ≡ just M)
  renOff with fold-offers-out l ph x hf
  ... | M , LN.sVis {v = vP} {τc = τcP} feq′ br =
        renameMap M
      , rnN-vis-just Payload (output l hi N2N_BlockFetch) x V
          (ι-vis-inv-out l hi N2N_BlockFetch x)
          (trans (cong (λ n → OpN.viewV n (Payload , output l hi N2N_BlockFetch) x)
                       (trans (sym feq) feq′))
                 br)

-- a link OTHER than the fired one refuses the io: `decLink-ev-out-key` pins any
-- `output` fire to the link's own channel
link-no-other-out : (j : Link) (ph : Dir → IDs → CopyPhase) (bj : Bool)
    {l : Link} {d : Dir} {id : IDs} {x : Payload}
  → j ≢ l → ¬ IoOffers (decLink j ph bj) (output l d id) x
link-no-other-out j ph bj j≢l (M , step) =
  j≢l (sym (proj₁ (decLink-ev-out-key j ph bj step)))

-- the whole-medium component function (mirror of `WalkBrkFire.medF`)
medF : (m : MedState) → Link → NetProc
medF m i = decLink i (phase m i) (broken m i)

-- a sibling link's non-offer, packaged at a medium state
medF-no-out : (m : MedState) (j : Link) {l : Link} {d : Dir} {id : IDs} {x : Payload}
  → j ≢ l → ¬ IoOffers (medF m j) (output l d id) x
medF-no-out m j = link-no-other-out j (phase m j) (broken m j)

-- `Skip` at the api alphabet (the `⦀Fin zero` tail) offers nothing
skipA-no-ev : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ¬ IoOffers (SkipA) e a
skipA-no-ev (M , step) = SNT.ret-no-ev {P = SkipA} refl step

-- *** (L1) THE MEDIUM-SIDE io INTRO, OUTPUT DIRECTION. ***  An UNBROKEN link
-- whose BlockFetch `hi` cell holds `x` offers `output i hi N2N_BlockFetch ! x`
-- out of the WHOLE breakable medium.  The four-link `⦀Fin` nest is spelled out
-- exactly as `WalkBrkFire.medium-break-fire` does (`⦀Fin`/`decMed` are defined
-- functions, so a meta-laden unification would stall).
module _ (m : MedState) where

  private
    f0 f1 f2 f3 rest1 rest2 rest3 : NetProc
    f0 = medF m fzero
    f1 = medF m (fsuc fzero)
    f2 = medF m (fsuc (fsuc fzero))
    f3 = medF m (fsuc (fsuc (fsuc fzero)))
    rest3 = f3 ⦀ SkipA
    rest2 = f2 ⦀ rest3
    rest1 = f1 ⦀ rest2

    -- the medium decode IS the explicit four-link nest (`numLinks = 4`)
    nestEq : decMed m ≡ (f0 ⦀ rest1)
    nestEq = refl

  medOfferOut : (i : Link) (x : Payload)
    → broken m i ≡ false → phase m i hi N2N_BlockFetch ≡ full x
    → IoOffers (decMed m) (output i hi N2N_BlockFetch) x
  medOfferOut i x ebr hf =
      proj₁ (nest i ebr hf)
    , subst (λ z → z ─[ ev (evl (evLabel Payload (output i hi N2N_BlockFetch) x)) ]─►
                   proj₁ (nest i ebr hf))
        (sym nestEq) (proj₂ (nest i ebr hf))
    where
    -- the fired link's own step, with the `broken` flag rewritten in
    fire : (j : Link) → broken m j ≡ false → phase m j hi N2N_BlockFetch ≡ full x
         → IoOffers (medF m j) (output j hi N2N_BlockFetch) x
    fire j eb h =
      subst (λ b → IoOffers (decLink j (phase m j) b) (output j hi N2N_BlockFetch) x)
            (sym eb) (link-offers-out j (phase m j) x h)
    -- the four-link nest, one clause per link (the sibling refusals are §4's
    -- channel pinning at the three other links)
    nest : (j : Link) → broken m j ≡ false → phase m j hi N2N_BlockFetch ≡ full x
         → Σ[ M ∈ NetProc ]
             ((f0 ⦀ rest1) ─[ ev (evl (evLabel Payload (output j hi N2N_BlockFetch) x)) ]─► M)
    nest fzero eb h =
        _
      , ⦀-ev-L f0 rest1 (proj₂ (fire fzero eb h))
          (noOffer→viewV rest1
            (⦀-noOffer f1 rest2 (medF-no-out m (fsuc fzero) (λ ()))
              (⦀-noOffer f2 rest3 (medF-no-out m (fsuc (fsuc fzero)) (λ ()))
                (⦀-noOffer f3 (SkipA) (medF-no-out m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev))))
    nest (fsuc fzero) eb h =
        _
      , ⦀-ev-R f0 rest1
          (⦀-ev-L f1 rest2 (proj₂ (fire (fsuc fzero) eb h))
            (noOffer→viewV rest2
              (⦀-noOffer f2 rest3 (medF-no-out m (fsuc (fsuc fzero)) (λ ()))
                (⦀-noOffer f3 (SkipA) (medF-no-out m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev))))
          (noOffer→viewV f0 (medF-no-out m fzero (λ ())))
    nest (fsuc (fsuc fzero)) eb h =
        _
      , ⦀-ev-R f0 rest1
          (⦀-ev-R f1 rest2
            (⦀-ev-L f2 rest3 (proj₂ (fire (fsuc (fsuc fzero)) eb h))
              (noOffer→viewV rest3
                (⦀-noOffer f3 (SkipA) (medF-no-out m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev)))
            (noOffer→viewV f1 (medF-no-out m (fsuc fzero) (λ ()))))
          (noOffer→viewV f0 (medF-no-out m fzero (λ ())))
    nest (fsuc (fsuc (fsuc fzero))) eb h =
        _
      , ⦀-ev-R f0 rest1
          (⦀-ev-R f1 rest2
            (⦀-ev-R f2 rest3
              (⦀-ev-L f3 (SkipA) (proj₂ (fire (fsuc (fsuc (fsuc fzero))) eb h))
                (noOffer→viewV (SkipA)
                  (skipA-no-ev {Payload}
                    {output (fsuc (fsuc (fsuc fzero))) hi N2N_BlockFetch} {x})))
              (noOffer→viewV f2 (medF-no-out m (fsuc (fsuc fzero)) (λ ()))))
            (noOffer→viewV f1 (medF-no-out m (fsuc fzero) (λ ()))))
          (noOffer→viewV f0 (medF-no-out m fzero (λ ())))

------------------------------------------------------------------------
-- §5  THE NODES-SIDE io INTRO LADDER (L2) — the item the charter omitted.
--
-- Four rungs, and the CONTRAST with the api family is at rung 3: an io event is
-- NOT in `apiES`, so at the node it must go SOLO past `∥⇘ apiES ⇙` with the
-- DRIVER REFUSING (`∥⇘⇙-ev-soloL` + `nodeX-drv-io-no`), where the api ladders
-- SYNC (`lift-api-node-ev`).  Rungs 2 and 4 reuse the banked sibling non-offer
-- families verbatim — the per-peer ones are keyed on `ιBF e₁`, and
-- `ιBF (BF.receiveBF l d)` IS `output l d N2N_BlockFetch`, so the SAME lemmas the
-- api ladders use apply here with `e₁ := BF.receiveBF l d`.
------------------------------------------------------------------------

-- the fired label IS an io event (`ioSet` answers `⊤` on `output`), PINNED at
-- the label so no membership meta survives at the eleven use sites below
iomem-out : (l : Link) (d : Dir) (id : IDs) (x : Payload)
          → ioES .mem (Payload , output l d id) x
iomem-out l d id x = tt

-- RUNG 1: the READER peer's own io offer, at any fine position that coarsens to
-- `bcStream` — `bfCnxt` accepts a `MsgBlock` delivery exactly there
-- (`ceqBFc05`), and `absBFc l d q` depends on `q` only through `coarsenBFc q`.
-- (The LegPos-24 spike's `bfc-offer-out`, promoted.)
bfc-offer-out : (i : Link) (d : Dir) (q : SN.BFcPos) (b : Block₃)
              → coarsenBFc q ≡ NS.bcStream
              → IoOffers (absBFc i d q) (output i d N2N_BlockFetch) (blkPayload b)
bfc-offer-out i d q b pin =
    absBFc i d (SN.bcBlk1 b)
  , aBFc i d q (SN.bcBlk1 b)
      (subst (λ z → NS.bfCfin z ≡ false) (sym pin) refl)
      (subst (λ z → NS.bfCnxt i d z (Payload , output i d N2N_BlockFetch) (blkPayload b)
                    ≡ just (NS.bcAblk b))
             (sym pin) (ceqBFc05 {time₀} {FromResponder} {length₀} {b} i d))

-- RUNG 2: the 12-peer BUNDLE offers what its BF CLIENT offers.  The BF server
-- refuses by DIRECTION (`absBFs-dir-noBoth`, payload-blind at the delivery row)
-- and the other ten peers by CHANNEL (`abs*-noBF`) — the SAME eleven refusals
-- the api `bundle-offer-recv` uses, at `e₁ := BF.receiveBF l cl`.
cliOutBundle : (l : Link) (cl sv : Dir) (cl≢sv : cl ≢ sv)
     (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
     (ip : SN.InertPos) (x : Payload)
   → IoOffers (absBFc l cl bfc) (output l cl N2N_BlockFetch) x
   → IoOffers (absBundleG l cl sv csc css bfc bfs ip) (output l cl N2N_BlockFetch) x
cliOutBundle l cl sv cl≢sv csc css bfc bfs ip x cOff =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _
          (⦀-ev-R _ _
            (⦀-ev-L _ _ (proj₂ cOff)
              (noOffer→viewV _
                (⦀-noOffer _ _ (absBFs-dir-noBoth l sv bfs (BF.receiveBF l cl) cl≢sv)
                 (⦀-noOffer _ _ (absTSc-noBF l cl (SN.tsc ip) (BF.receiveBF l cl))
                  (⦀-noOffer _ _ (absTSs-noBF l sv (SN.tss ip) (BF.receiveBF l cl))
                   (⦀-noOffer _ _ (absLNc-noBF l cl (SN.lnc ip) (BF.receiveBF l cl))
                    (⦀-noOffer _ _ (absLNs-noBF l sv (SN.lns ip) (BF.receiveBF l cl))
                     (⦀-noOffer _ _ (absLFc-noBF l cl (SN.lfc ip) (BF.receiveBF l cl))
                                    (absLFs-noBF l sv (SN.lfs ip) (BF.receiveBF l cl))))))))))
            (noOffer→viewV _ (absCSs-noBF l sv css (BF.receiveBF l cl))))
          (noOffer→viewV _ (absCSc-noBF l cl csc (BF.receiveBF l cl))))
        (noOffer→viewV _ (absKAs-noBF l sv (SN.kas ip) (BF.receiveBF l cl))))
      (noOffer→viewV _ (absKAc-noBF l cl (SN.kac ip) (BF.receiveBF l cl)))

-- RUNG 3, node B: the up-link bundle's client offer goes SOLO past node B's
-- `apiES` gate (its relay driver offers no io at all) and past the leg's OTHER
-- bundle (which refuses by LINK)
cliOutNodeB : (nb : SN.NodeStateB) (x : Payload)
  → IoOffers (absBFc linkAB hi (SN.NodeStateB.bfC-AB nb)) (output linkAB hi N2N_BlockFetch) x
  → IoOffers (absNodeB nb) (output linkAB hi N2N_BlockFetch) x
cliOutNodeB nb x cOff =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkAB hi N2N_BlockFetch} {x}
                            (iomem-out linkAB hi N2N_BlockFetch x))
      (⦀-ev-L _ _
        (proj₂ (cliOutBundle linkAB hi lo (λ ())
                  (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
                  (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
                  (SN.NodeStateB.inert-AB nb) x cOff))
        (noOffer→viewV _
          (absBundleG-io-no linkBD lo hi
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb)
             (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
             ahlOut linkAB≢linkBD (iomem-out linkAB hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeB-drv-io-no nb (iomem-out linkAB hi N2N_BlockFetch x)))

-- RUNG 3, node C: the linkAC mirror
cliOutNodeC : (nc : SN.NodeStateC) (x : Payload)
  → IoOffers (absBFc linkAC hi (SN.NodeStateC.bfC-AC nc)) (output linkAC hi N2N_BlockFetch) x
  → IoOffers (absNodeC nc) (output linkAC hi N2N_BlockFetch) x
cliOutNodeC nc x cOff =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkAC hi N2N_BlockFetch} {x}
                            (iomem-out linkAC hi N2N_BlockFetch x))
      (⦀-ev-L _ _
        (proj₂ (cliOutBundle linkAC hi lo (λ ())
                  (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
                  (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
                  (SN.NodeStateC.inert-AC nc) x cOff))
        (noOffer→viewV _
          (absBundleG-io-no linkCD lo hi
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc)
             (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
             ahlOut linkAC≢linkCD (iomem-out linkAC hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeC-drv-io-no nc (iomem-out linkAC hi N2N_BlockFetch x)))

-- RUNG 3, node D on link BD: node D's TWO bundles are both `hi/lo`, so the
-- sibling refusal is again by LINK; its driver pair offers no io
cliOutNodeD-BD : (nd : SN.NodeStateD) (x : Payload)
  → IoOffers (absBFc linkBD hi (SN.NodeStateD.bfC-BD nd)) (output linkBD hi N2N_BlockFetch) x
  → IoOffers (absNodeD nd) (output linkBD hi N2N_BlockFetch) x
cliOutNodeD-BD nd x cOff =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkBD hi N2N_BlockFetch} {x}
                            (iomem-out linkBD hi N2N_BlockFetch x))
      (⦀-ev-L _ _
        (proj₂ (cliOutBundle linkBD hi lo (λ ())
                  (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
                  (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd)
                  (SN.NodeStateD.inert-BD nd) x cOff))
        (noOffer→viewV _
          (absBundleG-io-no linkCD hi lo
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd)
             (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
             ahlOut linkBD≢linkCD (iomem-out linkBD hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeD-drv-io-no nd (iomem-out linkBD hi N2N_BlockFetch x)))

-- RUNG 3, node D on link CD: the reader bundle is node D's SECOND operand, so
-- the interleave peels the other way
cliOutNodeD-CD : (nd : SN.NodeStateD) (x : Payload)
  → IoOffers (absBFc linkCD hi (SN.NodeStateD.bfC-CD nd)) (output linkCD hi N2N_BlockFetch) x
  → IoOffers (absNodeD nd) (output linkCD hi N2N_BlockFetch) x
cliOutNodeD-CD nd x cOff =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkCD hi N2N_BlockFetch} {x}
                            (iomem-out linkCD hi N2N_BlockFetch x))
      (⦀-ev-R _ _
        (proj₂ (cliOutBundle linkCD hi lo (λ ())
                  (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd)
                  (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd)
                  (SN.NodeStateD.inert-CD nd) x cOff))
        (noOffer→viewV _
          (absBundleG-io-no linkBD hi lo
             (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
             (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
             ahlOut (λ e → linkBD≢linkCD (sym e))
             (iomem-out linkCD hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeD-drv-io-no nd (iomem-out linkCD hi N2N_BlockFetch x)))

-- RUNG 4: the FOUR-NODE interleave.  The three idle nodes refuse by the banked
-- io FINGERPRINT family, and the fingerprint is DERIVED FROM THE FIRING NODE'S
-- OWN STEP (`absNodeX-io-fp`) — so no payload or role premise enters the
-- statement, even though node A's BF SERVER sits at the same `(link,dir)` as
-- node B's firing BF client (the discriminator is `msgOrigin`, which the
-- client's own table edge already decides).
--
-- *** (L2) THE NODES-SIDE io INTRO, leg BD's UP cell reader (node B). ***
cliOutNodes-B : (s : SysState) (x : Payload)
  → IoOffers (absBFc linkAB hi (SN.NodeStateB.bfC-AB (nB s))) (output linkAB hi N2N_BlockFetch) x
  → IoOffers (absNodesOf s) (output linkAB hi N2N_BlockFetch) x
cliOutNodes-B s x cOff =
    _
  , ⦀-ev-R _ _
      (⦀-ev-L _ _ (proj₂ nOff)
        (noOffer→viewV _ (absGroupB-io-no (nB s) (nC s) (nD s) iom (proj₂ nOff))))
      (noOffer→viewV _ (absNodeA-io-no-when-B (nA s) iom fpB))
  where
  iom = iomem-out linkAB hi N2N_BlockFetch x
  nOff : IoOffers (absNodeB (nB s)) (output linkAB hi N2N_BlockFetch) x
  nOff = cliOutNodeB (nB s) x cOff
  fpB = absNodeB-io-fp (nB s) iom (proj₂ nOff)

-- … leg CD's UP cell reader (node C)
cliOutNodes-C : (s : SysState) (x : Payload)
  → IoOffers (absBFc linkAC hi (SN.NodeStateC.bfC-AC (nC s))) (output linkAC hi N2N_BlockFetch) x
  → IoOffers (absNodesOf s) (output linkAC hi N2N_BlockFetch) x
cliOutNodes-C s x cOff =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-L _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeD-io-no-when-C (nD s) iom fpC)))
        (noOffer→viewV _ (absNodeB-io-no-when-C (nB s) iom fpC)))
      (noOffer→viewV _ (absNodeA-io-no-when-C (nA s) iom fpC))
  where
  iom = iomem-out linkAC hi N2N_BlockFetch x
  nOff : IoOffers (absNodeC (nC s)) (output linkAC hi N2N_BlockFetch) x
  nOff = cliOutNodeC (nC s) x cOff
  fpC = absNodeC-io-fp (nC s) iom (proj₂ nOff)

-- … leg BD's DOWN cell reader (node D on link BD)
cliOutNodes-D-BD : (s : SysState) (x : Payload)
  → IoOffers (absBFc linkBD hi (SN.NodeStateD.bfC-BD (nD s))) (output linkBD hi N2N_BlockFetch) x
  → IoOffers (absNodesOf s) (output linkBD hi N2N_BlockFetch) x
cliOutNodes-D-BD s x cOff =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iom fpD)))
        (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iom fpD)))
      (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iom fpD))
  where
  iom = iomem-out linkBD hi N2N_BlockFetch x
  nOff : IoOffers (absNodeD (nD s)) (output linkBD hi N2N_BlockFetch) x
  nOff = cliOutNodeD-BD (nD s) x cOff
  fpD = absNodeD-io-fp (nD s) iom (proj₂ nOff)

-- … leg CD's DOWN cell reader (node D on link CD)
cliOutNodes-D-CD : (s : SysState) (x : Payload)
  → IoOffers (absBFc linkCD hi (SN.NodeStateD.bfC-CD (nD s))) (output linkCD hi N2N_BlockFetch) x
  → IoOffers (absNodesOf s) (output linkCD hi N2N_BlockFetch) x
cliOutNodes-D-CD s x cOff =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iom fpD)))
        (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iom fpD)))
      (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iom fpD))
  where
  iom = iomem-out linkCD hi N2N_BlockFetch x
  nOff : IoOffers (absNodeD (nD s)) (output linkCD hi N2N_BlockFetch) x
  nOff = cliOutNodeD-CD (nD s) x cOff
  fpD = absNodeD-io-fp (nD s) iom (proj₂ nOff)

------------------------------------------------------------------------
-- §6  THE MEDIUM-SIDE io INTRO, INPUT DIRECTION — the per-cell, fold, rename
--     and `△` rungs (Task 2c).
--
-- WHY THE INPUT DIRECTION IS A SEPARATE LADDER AND NOT A COROLLARY.  §2-§4
-- transport an `output` fire, whose SOURCE cell is `full x`; the server-side
-- refutations need the mirror, an `input` fire whose source cell is `empty` (the
-- server's own wire-send is the enabled move on H19's `empty` arm,
-- `LiveChanInv.H19`).  Nothing about the `output` chain is reusable at the level
-- of statements — every rung is keyed on the label's constructor — but the
-- OPERAND-generic machinery of §1 and §4 is reused verbatim: `IoOffersN`,
-- `noOfferN→viewV`, `⦀N-ev-L`/`-R`, `⦀N-noOffer`, `skipN-no-ev`,
-- `rnN-vis-just`, `△-fire-P`, `medF`, `skipA-no-ev`.  That reuse is why this
-- ladder is ~110 lines against §2-§4's 302.
--
-- ONE genuine direction-CHEAPENING, and it is at rung 1: `decCopy l d id empty`
-- is the `Copy` head, whose force is a `react` with NO `≟`-resolution pending,
-- so `refl` exposes it (`decCopy-empty-no-τ` uses the same `refl`).  The `full x`
-- cell needed the banked `ffull-react` existential instead.
------------------------------------------------------------------------

-- an `empty` cell FIRES its own `input l d id ? x`, landing on `full x`: the
-- head's force IS a react (`refl`) and the banked `offer-empty` menu reads the
-- successor off it (rung 1 of the medium ladder, INPUT direction)
cell-in-fire : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → IoOffersN (decCopy l d id empty) (input l d id) x
cell-in-fire l d id x = decCopy l d id (full x) , LN.sVis refl (offer-empty l d id x)

-- a cell whose OWN direction differs from the fired one refuses the `input`:
-- the banked `cell-in-key` pins the fired key to the cell's own key
cell-no-in-d : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → d₀ ≢ d → ¬ IoOffersN (decCopy l d id ph) (input l d₀ id₀) x
cell-no-in-d l d id ph ¬d (M , step) with cell-in-key l d id ph step
... | _ , de , _ , _ , _ = ¬d de

-- … and one whose own PROTOCOL id differs
cell-no-in-i : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → id₀ ≢ id → ¬ IoOffersN (decCopy l d id ph) (input l d₀ id₀) x
cell-no-in-i l d id ph ¬i (M , step) with cell-in-key l d id ph step
... | _ , _ , ide , _ , _ = ¬i ide

-- … the two, as the `viewV`-nothing the interleave intro consumes
cell-no-in-dv : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → d₀ ≢ d
  → OpN.viewV (PTree.force (decCopy l d id ph)) (Payload , input l d₀ id₀) x ≡ nothing
cell-no-in-dv l d id ph ¬d = noOfferN→viewV _ (cell-no-in-d l d id ph ¬d)

cell-no-in-iv : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → id₀ ≢ id
  → OpN.viewV (PTree.force (decCopy l d id ph)) (Payload , input l d₀ id₀) x ≡ nothing
cell-no-in-iv l d id ph ¬i = noOfferN→viewV _ (cell-no-in-i l d id ph ¬i)

-- the whole link fold ACCEPTS the `hi`-BlockFetch cell's `input` when that cell
-- is EMPTY (the §3 nest at the same key, INPUT direction: the BlockFetch `hi`
-- cell is position 5 of `uniformCfg`, the five before and the six after it plus
-- the `Skip` tail refuse by §6's key mismatch)
fold-offers-in : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_BlockFetch ≡ empty
  → IoOffersN (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))
              (input l hi N2N_BlockFetch) x
fold-offers-in l ph x he =
    _
  , ⦀N-ev-R c0 _
      (⦀N-ev-R c1 _
        (⦀N-ev-R c2 _
          (⦀N-ev-R c3 _
            (⦀N-ev-R c4 _
              (⦀N-ev-L c5 _ fire
                (noOfferN→viewV _ noTail))
              (cell-no-in-dv l lo N2N_BlockFetch (ph lo N2N_BlockFetch) (λ ())))
            (cell-no-in-iv l hi N2N_ChainSync (ph hi N2N_ChainSync) (λ ())))
          (cell-no-in-dv l lo N2N_ChainSync (ph lo N2N_ChainSync) (λ ())))
        (cell-no-in-iv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) (λ ())))
      (cell-no-in-dv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) (λ ()))
  where
  -- the twelve cells of the link's `uniformCfg` fold, in the config's order
  c0 c1 c2 c3 c4 c5 : NetProcN
  c0 = decCopy l lo N2N_KeepAlive    (ph lo N2N_KeepAlive)
  c1 = decCopy l hi N2N_KeepAlive    (ph hi N2N_KeepAlive)
  c2 = decCopy l lo N2N_ChainSync    (ph lo N2N_ChainSync)
  c3 = decCopy l hi N2N_ChainSync    (ph hi N2N_ChainSync)
  c4 = decCopy l lo N2N_BlockFetch   (ph lo N2N_BlockFetch)
  c5 = decCopy l hi N2N_BlockFetch   (ph hi N2N_BlockFetch)
  -- the fired cell's own step, with the phase hypothesis substituted in
  fire : c5 LN.─[ LN.ev (LN.evl (LN.evLabel Payload (input l hi N2N_BlockFetch) x)) ]─►
         proj₁ (cell-in-fire l hi N2N_BlockFetch x)
  fire = subst (λ z → decCopy l hi N2N_BlockFetch z
                        LN.─[ LN.ev (LN.evl (LN.evLabel Payload (input l hi N2N_BlockFetch) x)) ]─►
                      proj₁ (cell-in-fire l hi N2N_BlockFetch x))
               (sym he) (proj₂ (cell-in-fire l hi N2N_BlockFetch x))
  -- the six cells AFTER the BlockFetch `hi` cell, plus the `Skip` tail
  noTail : ¬ IoOffersN
             (decCopy l lo N2N_TxSubmission (ph lo N2N_TxSubmission) OpN.⦀
              (decCopy l hi N2N_TxSubmission (ph hi N2N_TxSubmission) OpN.⦀
               (decCopy l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) OpN.⦀
                (decCopy l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) OpN.⦀
                 (decCopy l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) OpN.⦀
                  (decCopy l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) OpN.⦀ ⦀⋆ []))))))
             (input l hi N2N_BlockFetch) x
  noTail =
    ⦀N-noOffer _ _ (cell-no-in-d l lo N2N_TxSubmission (ph lo N2N_TxSubmission) (λ ()))
      (⦀N-noOffer _ _ (cell-no-in-i l hi N2N_TxSubmission (ph hi N2N_TxSubmission) (λ ()))
        (⦀N-noOffer _ _ (cell-no-in-d l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) (λ ()))
          (⦀N-noOffer _ _ (cell-no-in-i l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) (λ ()))
            (⦀N-noOffer _ _ (cell-no-in-d l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) (λ ()))
              (⦀N-noOffer _ _ (cell-no-in-i l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) (λ ()))
                skipN-no-ev)))))

-- the medium's ι sends the LN `input` to the api `input` and the inverse takes
-- it back (the §4 `ι-vis-inv-out` mirror; `rnN-vis-just` itself is label-generic
-- and is REUSED as is)
ι-vis-inv-in : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → ι-vis-inv (Payload , input l d id) x
    ≡ just ((Payload , input l d id) , x)
ι-vis-inv-in l d id x = refl

-- the `break l ⟶₀ Skip` prefix does not offer a copy-channel `input` either
prefix-no-in : (i l : Link) (d : Dir) (id : IDs) (x : Payload)
  → viewV (PTree.force (Prefix₀ (break i) (SkipA))) (Payload , input l d id) x
    ≡ nothing
prefix-no-in i l d id x = refl

-- an UNBROKEN link whose `hi`-BlockFetch cell is EMPTY accepts that cell's
-- `input` out of the WHOLE per-link decode: the fold fires (§6), the rename
-- transports it (§4's `rnN-vis-just`) and the `△` commits to the left operand
link-offers-in : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_BlockFetch ≡ empty
  → IoOffers (decLink l ph false) (input l hi N2N_BlockFetch) x
link-offers-in l ph x he with fold-react l ph
... | mkReactF V T feq =
    _
  , △-fire-P
      (force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
      refl
      (proj₂ renOff)
      (prefix-no-in l l hi N2N_BlockFetch x)
  where
  renOff : Σ[ M ∈ NetProc ]
             (rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
                    (rnCollect V (invPreimg ι-vis-inv (Payload , input l hi N2N_BlockFetch) x))
              ≡ just M)
  renOff with fold-offers-in l ph x he
  ... | M , LN.sVis {v = vP} {τc = τcP} feq′ br =
        renameMap M
      , rnN-vis-just Payload (input l hi N2N_BlockFetch) x V
          (ι-vis-inv-in l hi N2N_BlockFetch x)
          (trans (cong (λ n → OpN.viewV n (Payload , input l hi N2N_BlockFetch) x)
                       (trans (sym feq) feq′))
                 br)

-- a link OTHER than the fired one refuses the `input`: `decLink-ev-in-key` pins
-- any `input` fire to the link's own channel
link-no-other-in : (j : Link) (ph : Dir → IDs → CopyPhase) (bj : Bool)
    {l : Link} {d : Dir} {id : IDs} {x : Payload}
  → j ≢ l → ¬ IoOffers (decLink j ph bj) (input l d id) x
link-no-other-in j ph bj j≢l (M , step) =
  j≢l (sym (proj₁ (decLink-ev-in-key j ph bj step)))

-- a sibling link's `input` non-offer, packaged at a medium state
medF-no-in : (m : MedState) (j : Link) {l : Link} {d : Dir} {id : IDs} {x : Payload}
  → j ≢ l → ¬ IoOffers (medF m j) (input l d id) x
medF-no-in m j = link-no-other-in j (phase m j) (broken m j)

------------------------------------------------------------------------
-- §7  THE MEDIUM-τ INTRO — the `draining` arm's enabled move (Task 2c).
--
-- H19's third arm is a cell holding a payload its reader has ALREADY taken
-- (`draining x`): no peer is involved, the enabled move is the medium's OWN
-- drain τ, and refuting stability needs it lifted from the cell to the whole
-- medium.  Every rung is a τ, and that makes this ladder MATERIALLY cheaper than
-- the two ev ones: a τ of an interleave needs NO sibling `viewV`-nothing
-- (`Par-τ-L`/`-R` are unconditional), so the twelve-cell fold and the four-link
-- nest carry no refusals at all.
--
-- THE ONE SUBSTANTIVE RUNG is the push-forward through the medium's
-- `renameMap`: the banked `SysOracle_TauCore.RenTC` exports only the REFLECT
-- direction (`renameMap-τ-reflect`, `:342`), and its `sil` half's forward twin IS
-- banked (`force-renameMap-sil`, `:311`), but the react half needs the
-- `extBranch` FORWARD equation, which is a transcription of
-- `CSP/Laws/Traces/TraceLawsRename.extBranch-just-inv` (`:98-105`) — stated there
-- for the SAME-alphabet `_⟦ inv ⟧ⁱ`, so it does not apply to this cross-alphabet
-- `CSP.Rename` instance.  (Same reason `rnN-vis-just` exists in §4.)
--
-- THREE of this section's items are cross-alphabet TRANSCRIPTIONS
-- (`extBranchN-just`, `renameMap-τ-fwd`, `△-τ-tag0`); their counterparts and
-- anchors are in the module header's single KEEP-IN-SYNC list, which is the
-- authoritative one — do not duplicate the anchors here.
------------------------------------------------------------------------

-- rung 1: the `draining x` cell's own drain τ — the post-`output` loop-back
-- `sil` back to the `Copy` head (the banked `fdrain` IS the force equation)
cell-drain-τ : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → decCopy l d id (draining x) LN.─[ LN.τ ]─► decCopy l d id empty
cell-drain-τ l d id x = LN.sSil (fdrain l d id x)

-- τ-intro through the LN interleave, LEFT operand (mirror of `SysStep.⦀-τ-L`;
-- unlike the ev intro this takes NO sibling non-offer)
⦀N-τ-L : (P Q : NetProcN) {P′ : NetProcN}
  → P LN.─[ LN.τ ]─► P′ → (P OpN.⦀ Q) LN.─[ LN.τ ]─► (P′ OpN.⦀ Q)
⦀N-τ-L P Q = TLPN.Par-τ-L OpN.∅ES (λ _ _ → tt) P Q

-- … RIGHT operand (mirror of `SysStep.⦀-τ-R`)
⦀N-τ-R : (P Q : NetProcN) {Q′ : NetProcN}
  → Q LN.─[ LN.τ ]─► Q′ → (P OpN.⦀ Q) LN.─[ LN.τ ]─► (P OpN.⦀ Q′)
⦀N-τ-R P Q = TLPN.Par-τ-R OpN.∅ES (λ _ _ → tt) P Q

-- rung 2: the 12-cell fold's τ, at the `(hi , N2N_BlockFetch)` cell.  Same nest
-- as §3/§6 with the refusals REMOVED — that is the whole τ discount.
fold-drain-τ : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_BlockFetch ≡ draining x
  → Σ[ M ∈ NetProcN ]
      (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
         LN.─[ LN.τ ]─► M)
fold-drain-τ l ph x hd =
    _
  , ⦀N-τ-R c0 _
      (⦀N-τ-R c1 _
        (⦀N-τ-R c2 _
          (⦀N-τ-R c3 _
            (⦀N-τ-R c4 _
              (⦀N-τ-L c5 _ fire)))))
  where
  -- the six cells up to and including the BlockFetch `hi` one (position 5)
  c0 c1 c2 c3 c4 c5 : NetProcN
  c0 = decCopy l lo N2N_KeepAlive    (ph lo N2N_KeepAlive)
  c1 = decCopy l hi N2N_KeepAlive    (ph hi N2N_KeepAlive)
  c2 = decCopy l lo N2N_ChainSync    (ph lo N2N_ChainSync)
  c3 = decCopy l hi N2N_ChainSync    (ph hi N2N_ChainSync)
  c4 = decCopy l lo N2N_BlockFetch   (ph lo N2N_BlockFetch)
  c5 = decCopy l hi N2N_BlockFetch   (ph hi N2N_BlockFetch)
  -- the draining cell's own τ, with the phase hypothesis substituted in
  fire : c5 LN.─[ LN.τ ]─► decCopy l hi N2N_BlockFetch empty
  fire = subst (λ z → decCopy l hi N2N_BlockFetch z
                        LN.─[ LN.τ ]─► decCopy l hi N2N_BlockFetch empty)
               (sym hd) (cell-drain-τ l hi N2N_BlockFetch x)

-- the renamed τ-branch at a target index whose `extBwd` is `just eι₁` is the
-- RENAMED source τ (transcription of `TraceLawsRename.extBranch-just-inv` at
-- this cross-alphabet instance; `rnMc _ _ (just t) = just (renameMap t)` holds
-- definitionally, `CSP/Rename.agda:138-139`, `:193-195`)
extBranchN-just : {T : TmapNN} {A : Set 0ℓ}
    {eι₂ : ExtI (Net_Api Payload) A} {eι₁ : ExtI (Net Payload) A} {a : A}
    {P₁ : NetProcN}
  → extBwd eι₂ ≡ just eι₁ → T (A , eι₁) a ≡ just P₁
  → extBranch (invRel ι-vis-inv) (invPreimg ι-vis-inv) T (A , eι₂) a
    ≡ just (renameMap P₁)
extBranchN-just {eι₂ = eι₂} eqb eqt with extBwd eι₂ | eqb
... | just eι₁ | refl rewrite eqt = refl

-- rung 3: FORWARD transport of a τ through the medium's rename.  A source `sil`
-- rides `force-renameMap-sil`; a source react-τ rides `force-renameMap-react`
-- with the index pushed forward by `extFwd` (its `extBwd` comes back by
-- `ext-linv`).
renameMap-τ-fwd : (P : NetProcN) {P′ : NetProcN}
  → P LN.─[ LN.τ ]─► P′ → renameMap P ─[ τ ]─► renameMap P′
renameMap-τ-fwd P (LN.sSil eq) = sSil (force-renameMap-sil {P = P} eq)
renameMap-τ-fwd P (LN.sTau {τc = T} {i = A , eι₁} {a = a} eq br) =
  sTau {i = A , extFwd eι₁} {a = a}
       (force-renameMap-react {P = P} eq)
       (extBranchN-just {T = T} {eι₂ = extFwd eι₁} {eι₁ = eι₁} {a = a}
                        (ext-linv eι₁) br)

-- the `△-τ` branch map's tag0 (`pair fin _` / `lift fzero`) IS the LEFT
-- operand's own τ-branch (intro mirror of `△-τ-branch-inv`'s firing clause)
△-τ-tag0 : (P Q : NetProc) (vP : VmapN) (τcP : TmapN) (vQ : VmapN) (τcQ : TmapN)
    {A : Set 0ℓ} {iι : ExtI (Net_Api Payload) A} {a : A} {P′ : NetProc}
  → τcP (A , iι) a ≡ just P′
  → OpA.△-τ (react vP τcP) (react vQ τcQ) P Q
            ((Lift 0ℓ (Fin 2) × A) , pair fin iι) (lift fzero , a)
    ≡ just (P′ △ Q)
△-τ-tag0 P Q vP τcP vQ τcQ beq rewrite beq = refl

-- the `△` interrupt mirrors the LEFT operand's τ when both operands are stable
-- reacts (the `△-τ` half of `force-△-react`'s clause; `△-fire-P` is its visible
-- twin).  The source `sil` case is REFUTED from the left operand's react force —
-- which is exactly what the medium supplies (`force-renameMap-react`).
--
-- *** SCOPE OF THAT REFUTATION — do NOT read it as a fact about `△` (Task-3
-- rider, Task-2c review I-1).  The `sSil` clause dies because THIS LEMMA
-- HYPOTHESISES `PTree.force P ≡ react vP τcP`, not because `△` blocks a
-- `sil`-headed left operand.  It does not: `viewT (sil t) = oneτ t`
-- (`CSP/Operators.agda:65`), `oneτ t (_ , fin) (lift fzero) = just t` (`:53`), and
-- `△-τ nP nQ P Q (_ , pair fin i) (lift fzero , a) = viewT nP (_ , i) a` (`:444`),
-- so at tag `pair fin fin` a `sil`-headed left operand's τ DOES propagate through
-- `_△_`.  The Task-2c report's "`△-τ-L` refutes a sil-headed left operand"
-- method note is therefore RETRACTED; what is true is only that a caller wanting
-- this lemma must supply the react force, and every caller here can. ***
△-τ-L : {P Q : NetProc} {vP : VmapN} {τcP : TmapN} {vQ : VmapN} {τcQ : TmapN}
        {P′ : NetProc}
  → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
  → P ─[ τ ]─► P′
  → (P △ Q) ─[ τ ]─► (P′ △ Q)
△-τ-L eqP eqQ (sSil sileq) with trans (sym eqP) sileq
... | ()
△-τ-L {P} {Q} {vP} {τcP} {vQ} {τcQ} eqP eqQ (sTau {τc = τc′} {i = A , iι} {a = a} feq′ beq)
    with react-injective (trans (sym feq′) eqP)
... | _ , refl =
      sTau {i = (Lift 0ℓ (Fin 2) × A) , pair fin iι} {a = (lift fzero , a)}
           (force-△-react eqP eqQ) (△-τ-tag0 P Q vP τcP vQ τcQ {a = a} beq)

-- rung 4: the whole per-link decode's τ — the fold's drain τ rides the rename
-- and the `△` commits to the left operand (the `break` prefix is a react, so the
-- `force-△-react` clause applies)
link-drain-τ : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_BlockFetch ≡ draining x
  → Σ[ M ∈ NetProc ] (decLink l ph false ─[ τ ]─► M)
link-drain-τ l ph x hd with fold-react l ph
... | mkReactF V T feq =
    _
  , △-τ-L
      (force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
      refl
      (renameMap-τ-fwd
        (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))
        (proj₂ (fold-drain-τ l ph x hd)))

------------------------------------------------------------------------
-- §8  *** THE TWO WHOLE-MEDIUM INTROS: `medOfferIn` AND `medDrainτ`. ***
--
-- Both are the four-link `⦀Fin` rung, spelled out exactly as §4's `medOfferOut`
-- is (`⦀Fin`/`decMed` are defined functions, so a meta-laden unification would
-- stall).  The private nest below is a COPY of §4's — ten lines, duplicated
-- rather than shared because §4's copy is private to its own `module _
-- (m : MedState)` block and hoisting it would touch a landed proof; keep the two
-- copies in step (both are just `numLinks = 4` spelled out).
------------------------------------------------------------------------

module _ (m : MedState) where

  private
    g0 g1 g2 g3 grest1 grest2 grest3 : NetProc
    g0 = medF m fzero
    g1 = medF m (fsuc fzero)
    g2 = medF m (fsuc (fsuc fzero))
    g3 = medF m (fsuc (fsuc (fsuc fzero)))
    grest3 = g3 ⦀ SkipA
    grest2 = g2 ⦀ grest3
    grest1 = g1 ⦀ grest2

    -- the medium decode IS the explicit four-link nest (`numLinks = 4`)
    gnestEq : decMed m ≡ (g0 ⦀ grest1)
    gnestEq = refl

  -- *** (L3) THE MEDIUM-SIDE io INTRO, INPUT DIRECTION. ***  An UNBROKEN link
  -- whose BlockFetch `hi` cell is EMPTY accepts `input i hi N2N_BlockFetch ? x`
  -- out of the WHOLE breakable medium — the enabled move on H19's `empty` arm.
  medOfferIn : (i : Link) (x : Payload)
    → broken m i ≡ false → phase m i hi N2N_BlockFetch ≡ empty
    → IoOffers (decMed m) (input i hi N2N_BlockFetch) x
  medOfferIn i x ebr he =
      proj₁ (nest i ebr he)
    , subst (λ z → z ─[ ev (evl (evLabel Payload (input i hi N2N_BlockFetch) x)) ]─►
                   proj₁ (nest i ebr he))
        (sym gnestEq) (proj₂ (nest i ebr he))
    where
    -- the fired link's own step, with the `broken` flag rewritten in
    fire : (j : Link) → broken m j ≡ false → phase m j hi N2N_BlockFetch ≡ empty
         → IoOffers (medF m j) (input j hi N2N_BlockFetch) x
    fire j eb h =
      subst (λ b → IoOffers (decLink j (phase m j) b) (input j hi N2N_BlockFetch) x)
            (sym eb) (link-offers-in j (phase m j) x h)
    -- the four-link nest, one clause per link (the sibling refusals are §6's
    -- channel pinning at the three other links)
    nest : (j : Link) → broken m j ≡ false → phase m j hi N2N_BlockFetch ≡ empty
         → Σ[ M ∈ NetProc ]
             ((g0 ⦀ grest1) ─[ ev (evl (evLabel Payload (input j hi N2N_BlockFetch) x)) ]─► M)
    nest fzero eb h =
        _
      , ⦀-ev-L g0 grest1 (proj₂ (fire fzero eb h))
          (noOffer→viewV grest1
            (⦀-noOffer g1 grest2 (medF-no-in m (fsuc fzero) (λ ()))
              (⦀-noOffer g2 grest3 (medF-no-in m (fsuc (fsuc fzero)) (λ ()))
                (⦀-noOffer g3 (SkipA) (medF-no-in m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev))))
    nest (fsuc fzero) eb h =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-L g1 grest2 (proj₂ (fire (fsuc fzero) eb h))
            (noOffer→viewV grest2
              (⦀-noOffer g2 grest3 (medF-no-in m (fsuc (fsuc fzero)) (λ ()))
                (⦀-noOffer g3 (SkipA) (medF-no-in m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev))))
          (noOffer→viewV g0 (medF-no-in m fzero (λ ())))
    nest (fsuc (fsuc fzero)) eb h =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-R g1 grest2
            (⦀-ev-L g2 grest3 (proj₂ (fire (fsuc (fsuc fzero)) eb h))
              (noOffer→viewV grest3
                (⦀-noOffer g3 (SkipA) (medF-no-in m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev)))
            (noOffer→viewV g1 (medF-no-in m (fsuc fzero) (λ ()))))
          (noOffer→viewV g0 (medF-no-in m fzero (λ ())))
    nest (fsuc (fsuc (fsuc fzero))) eb h =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-R g1 grest2
            (⦀-ev-R g2 grest3
              (⦀-ev-L g3 (SkipA) (proj₂ (fire (fsuc (fsuc (fsuc fzero))) eb h))
                (noOffer→viewV (SkipA)
                  (skipA-no-ev {Payload}
                    {input (fsuc (fsuc (fsuc fzero))) hi N2N_BlockFetch} {x})))
              (noOffer→viewV g2 (medF-no-in m (fsuc (fsuc fzero)) (λ ()))))
            (noOffer→viewV g1 (medF-no-in m (fsuc fzero) (λ ()))))
          (noOffer→viewV g0 (medF-no-in m fzero (λ ())))

  -- *** (L4) THE MEDIUM-τ INTRO. ***  An UNBROKEN link whose BlockFetch `hi`
  -- cell is DRAINING performs a τ of the WHOLE breakable medium — the enabled
  -- move on H19's `draining` arm.  No sibling obligations at any rung.
  medDrainτ : (i : Link) (x : Payload)
    → broken m i ≡ false → phase m i hi N2N_BlockFetch ≡ draining x
    → Σ[ M ∈ NetProc ] (decMed m ─[ τ ]─► M)
  medDrainτ i x ebr hd =
      proj₁ (nestτ i ebr hd)
    , subst (λ z → z ─[ τ ]─► proj₁ (nestτ i ebr hd))
        (sym gnestEq) (proj₂ (nestτ i ebr hd))
    where
    -- the draining link's own τ, with the `broken` flag rewritten in
    fireτ : (j : Link) → broken m j ≡ false → phase m j hi N2N_BlockFetch ≡ draining x
          → Σ[ M ∈ NetProc ] (medF m j ─[ τ ]─► M)
    fireτ j eb h =
      subst (λ b → Σ[ M ∈ NetProc ] (decLink j (phase m j) b ─[ τ ]─► M))
            (sym eb) (link-drain-τ j (phase m j) x h)
    -- the four-link nest, one clause per link
    nestτ : (j : Link) → broken m j ≡ false → phase m j hi N2N_BlockFetch ≡ draining x
          → Σ[ M ∈ NetProc ] ((g0 ⦀ grest1) ─[ τ ]─► M)
    nestτ fzero eb h = _ , ⦀-τ-L g0 grest1 (proj₂ (fireτ fzero eb h))
    nestτ (fsuc fzero) eb h =
      _ , ⦀-τ-R g0 grest1 (⦀-τ-L g1 grest2 (proj₂ (fireτ (fsuc fzero) eb h)))
    nestτ (fsuc (fsuc fzero)) eb h =
      _ , ⦀-τ-R g0 grest1
            (⦀-τ-R g1 grest2
              (⦀-τ-L g2 grest3 (proj₂ (fireτ (fsuc (fsuc fzero)) eb h))))
    nestτ (fsuc (fsuc (fsuc fzero))) eb h =
      _ , ⦀-τ-R g0 grest1
            (⦀-τ-R g1 grest2
              (⦀-τ-R g2 grest3
                (⦀-τ-L g3 (SkipA) (proj₂ (fireτ (fsuc (fsuc (fsuc fzero))) eb h)))))

------------------------------------------------------------------------
-- §9  THE NODES-SIDE io INTRO LADDER, SERVER-FIRED (L5) — Task 2c.
--
-- §5's ladder lifts the READER's `output`; this one lifts the SENDER's `input`,
-- i.e. the BF SERVER's own wire-send, which is the nodes half of H19's `empty`
-- arm.  THREE nodes host the four servers, not one: `oUpSrv` at both legs is
-- node A (its two bundles, `absBundleG linkAB lo hi` / `linkAC lo hi`), while
-- `oDnSrv` is node B on leg BD (`absBundleG linkBD lo hi`) and node C on leg CD
-- (`absBundleG linkCD lo hi`).  In every case the SERVER sits at direction `hi`,
-- which is the same `(link , hi , N2N_BlockFetch)` key the cell accessors read —
-- one cell, one writer, one reader, both at `hi`.
--
-- WHAT IS BANKED AND REUSED, rung by rung (the reuse-before-transcribe rule):
--   · rung 2 (the 12-peer bundle) is `SysOracle_RouteKaTs.absBundle-BFs-ev`
--     (`:1723-1749`) VERBATIM — the BF-server twin of §5's hand-rolled
--     `cliOutBundle`, keyed on `ιBF e₁` with `ιBF (BF.sendBF l d) ≡ input l d
--     N2N_BlockFetch` by `refl` (`NetworkPar.agda:130`) and `bfEvDir
--     (BF.sendBF l d) ≡ d` by `refl` (`SysOracle_GapBDisj.agda:319`).  So this
--     rung costs SIX lines, against `cliOutBundle`'s twenty-four.
--   · rung 4's node-A case is `SysIoLink3.absGroupA-io-no` (`:2853-2861`), which
--     derives the io FINGERPRINT from the firing node's own step internally.
--     `absGroupC-io-no` does NOT exist and is NOT needed: node C fires as the
--     THIRD operand, so the nest is `⦀-ev-R`/`⦀-ev-R`/`⦀-ev-L` with the three
--     banked PAIRWISE refusals (`absNodeA-io-no-when-C`, `absNodeB-io-no-when-C`,
--     `absNodeD-io-no-when-C`) — exactly §5's `cliOutNodes-C` shape.
--   · the per-node driver refusals (`nodeA-drv-io-no` … ) and the sibling-bundle
--     refusal `absBundleG-io-no` are banked and label-generic: the only change
--     from §5 is the `ApiHasLink` constructor, `ahlIn` for `ahlOut`.
------------------------------------------------------------------------

-- the fired label IS an io event, INPUT direction (`ioSet` answers `⊤` on
-- `input` too), PINNED at the label so no membership meta survives below
iomem-in : (l : Link) (d : Dir) (id : IDs) (x : Payload)
         → ioES .mem (Payload , input l d id) x
iomem-in l d id x = tt

-- RUNG 1: the SENDER peer's own io offer, at any fine position that coarsens to
-- `bsWblk b` — `bfSnxt` accepts the wire-send of `MsgBlock b` exactly there
-- (`ceqBFs11`), and `absBFs l d q` depends on `q` only through `coarsenBFs q`.
-- The step is returned at its EXPLICIT target (`bsHead stStreaming`, the fine
-- position `coarsenBFs` sends to `bsStream`) because rung 2's banked lemma is
-- stated between two named positions, not between offers.
bfs-in-step : (i : Link) (d : Dir) (q : SN.BFsPos) (b : Block₃)
            → coarsenBFs q ≡ NS.bsWblk b
            → absBFs i d q
                ─[ ev (evl (evLabel Payload (input i d N2N_BlockFetch) (blkPayload b))) ]─►
              absBFs i d (SN.bsHead BF.stStreaming)
bfs-in-step i d q b pin =
  aBFs i d q (SN.bsHead BF.stStreaming)
    (subst (λ z → NS.bfSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfSnxt i d z (Payload , input i d N2N_BlockFetch) (blkPayload b)
                  ≡ just NS.bsStream)
           (sym pin) (ceqBFs11 {b} i d))

-- RUNG 2: the 12-peer BUNDLE offers what its BF SERVER offers — the banked
-- `absBundle-BFs-ev` at `e₁ := BF.sendBF l sv` (its eleven internal refusals are
-- the same families §5's `cliOutBundle` spells out, with the BF client refused
-- by DIRECTION instead of the server)
srvInBundle : (l : Link) (cl sv : Dir) → cl ≢ sv
   → (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos)
     (bfs bfs′ : SN.BFsPos) (ip : SN.InertPos) (x : Payload)
   → absBFs l sv bfs ─[ ev (evl (evLabel Payload (input l sv N2N_BlockFetch) x)) ]─►
     absBFs l sv bfs′
   → IoOffers (absBundleG l cl sv csc css bfc bfs ip) (input l sv N2N_BlockFetch) x
srvInBundle l cl sv cl≢sv csc css bfc bfs bfs′ ip x sStep =
    _
  , absBundle-BFs-ev l cl sv csc css bfc bfs ip
      {e₁ = BF.sendBF l sv} {qbs′ = bfs′} cl≢sv refl sStep

-- RUNG 3, node A on link AB: the AB bundle's server offer goes SOLO past node
-- A's `apiES` gate (its two produce drivers offer no io) and past the AC bundle
-- (which refuses by LINK)
srvInNodeA-AB : (na : SN.NodeStateA) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkAB hi (SN.NodeStateA.bfS-AB na)
      ─[ ev (evl (evLabel Payload (input linkAB hi N2N_BlockFetch) x)) ]─►
    absBFs linkAB hi bfs′
  → IoOffers (absNodeA na) (input linkAB hi N2N_BlockFetch) x
srvInNodeA-AB na x bfs′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkAB hi N2N_BlockFetch} {x}
                            (iomem-in linkAB hi N2N_BlockFetch x))
      (⦀-ev-L _ _
        (proj₂ (srvInBundle linkAB lo hi (λ ())
                  (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na)
                  (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) bfs′
                  (SN.NodeStateA.inert-AB na) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAC lo hi
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na)
             (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)
             ahlIn linkAB≢linkAC (iomem-in linkAB hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeA-drv-io-no na (iomem-in linkAB hi N2N_BlockFetch x)))

-- RUNG 3, node A on link AC: the AC bundle is node A's SECOND operand, so the
-- interleave peels the other way
srvInNodeA-AC : (na : SN.NodeStateA) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkAC hi (SN.NodeStateA.bfS-AC na)
      ─[ ev (evl (evLabel Payload (input linkAC hi N2N_BlockFetch) x)) ]─►
    absBFs linkAC hi bfs′
  → IoOffers (absNodeA na) (input linkAC hi N2N_BlockFetch) x
srvInNodeA-AC na x bfs′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkAC hi N2N_BlockFetch} {x}
                            (iomem-in linkAC hi N2N_BlockFetch x))
      (⦀-ev-R _ _
        (proj₂ (srvInBundle linkAC lo hi (λ ())
                  (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na)
                  (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) bfs′
                  (SN.NodeStateA.inert-AC na) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAB lo hi
             (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na)
             (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
             ahlIn (λ q → linkAB≢linkAC (sym q)) (iomem-in linkAC hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeA-drv-io-no na (iomem-in linkAC hi N2N_BlockFetch x)))

-- RUNG 3, node B on link BD: the relay's DOWN server; its BD bundle is node B's
-- second operand and its AB bundle refuses by LINK
srvInNodeB-BD : (nb : SN.NodeStateB) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkBD hi (SN.NodeStateB.bfS-BD nb)
      ─[ ev (evl (evLabel Payload (input linkBD hi N2N_BlockFetch) x)) ]─►
    absBFs linkBD hi bfs′
  → IoOffers (absNodeB nb) (input linkBD hi N2N_BlockFetch) x
srvInNodeB-BD nb x bfs′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkBD hi N2N_BlockFetch} {x}
                            (iomem-in linkBD hi N2N_BlockFetch x))
      (⦀-ev-R _ _
        (proj₂ (srvInBundle linkBD lo hi (λ ())
                  (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb)
                  (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) bfs′
                  (SN.NodeStateB.inert-BD nb) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAB hi lo
             (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
             (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
             ahlIn (λ q → linkAB≢linkBD (sym q)) (iomem-in linkBD hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeB-drv-io-no nb (iomem-in linkBD hi N2N_BlockFetch x)))

-- RUNG 3, node C on link CD: the leg-CD mirror
srvInNodeC-CD : (nc : SN.NodeStateC) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkCD hi (SN.NodeStateC.bfS-CD nc)
      ─[ ev (evl (evLabel Payload (input linkCD hi N2N_BlockFetch) x)) ]─►
    absBFs linkCD hi bfs′
  → IoOffers (absNodeC nc) (input linkCD hi N2N_BlockFetch) x
srvInNodeC-CD nc x bfs′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkCD hi N2N_BlockFetch} {x}
                            (iomem-in linkCD hi N2N_BlockFetch x))
      (⦀-ev-R _ _
        (proj₂ (srvInBundle linkCD lo hi (λ ())
                  (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc)
                  (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) bfs′
                  (SN.NodeStateC.inert-CD nc) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAC hi lo
             (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
             (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
             ahlIn (λ q → linkAC≢linkCD (sym q)) (iomem-in linkCD hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeC-drv-io-no nc (iomem-in linkCD hi N2N_BlockFetch x)))

-- *** (L5) THE NODES-SIDE SERVER io INTRO, leg BD's UP server (node A). ***
-- RUNG 4: the FOUR-NODE interleave.  Node A is the FIRST operand, so the whole
-- sibling group is refuted in one banked step.
srvInNodes-A-AB : (s : SysState) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkAB hi (SN.NodeStateA.bfS-AB (nA s))
      ─[ ev (evl (evLabel Payload (input linkAB hi N2N_BlockFetch) x)) ]─►
    absBFs linkAB hi bfs′
  → IoOffers (absNodesOf s) (input linkAB hi N2N_BlockFetch) x
srvInNodes-A-AB s x bfs′ sStep =
    _
  , ⦀-ev-L _ _ (proj₂ nOff)
      (noOffer→viewV _ (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) iom (proj₂ nOff)))
  where
  iom = iomem-in linkAB hi N2N_BlockFetch x
  nOff : IoOffers (absNodeA (nA s)) (input linkAB hi N2N_BlockFetch) x
  nOff = srvInNodeA-AB (nA s) x bfs′ sStep

-- … leg CD's UP server (node A again, its other link)
srvInNodes-A-AC : (s : SysState) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkAC hi (SN.NodeStateA.bfS-AC (nA s))
      ─[ ev (evl (evLabel Payload (input linkAC hi N2N_BlockFetch) x)) ]─►
    absBFs linkAC hi bfs′
  → IoOffers (absNodesOf s) (input linkAC hi N2N_BlockFetch) x
srvInNodes-A-AC s x bfs′ sStep =
    _
  , ⦀-ev-L _ _ (proj₂ nOff)
      (noOffer→viewV _ (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) iom (proj₂ nOff)))
  where
  iom = iomem-in linkAC hi N2N_BlockFetch x
  nOff : IoOffers (absNodeA (nA s)) (input linkAC hi N2N_BlockFetch) x
  nOff = srvInNodeA-AC (nA s) x bfs′ sStep

-- … leg BD's DOWN server (node B): node A refuses by the banked reverse pairwise
-- fingerprint and the C/D group by `absGroupB-io-no`
srvInNodes-B-BD : (s : SysState) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkBD hi (SN.NodeStateB.bfS-BD (nB s))
      ─[ ev (evl (evLabel Payload (input linkBD hi N2N_BlockFetch) x)) ]─►
    absBFs linkBD hi bfs′
  → IoOffers (absNodesOf s) (input linkBD hi N2N_BlockFetch) x
srvInNodes-B-BD s x bfs′ sStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-L _ _ (proj₂ nOff)
        (noOffer→viewV _ (absGroupB-io-no (nB s) (nC s) (nD s) iom (proj₂ nOff))))
      (noOffer→viewV _ (absNodeA-io-no-when-B (nA s) iom fpB))
  where
  iom = iomem-in linkBD hi N2N_BlockFetch x
  nOff : IoOffers (absNodeB (nB s)) (input linkBD hi N2N_BlockFetch) x
  nOff = srvInNodeB-BD (nB s) x bfs′ sStep
  fpB = absNodeB-io-fp (nB s) iom (proj₂ nOff)

-- … leg CD's DOWN server (node C): the THIRD operand, so all three refusals are
-- the banked pairwise ones — this is where `absGroupC-io-no` would have gone
srvInNodes-C-CD : (s : SysState) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkCD hi (SN.NodeStateC.bfS-CD (nC s))
      ─[ ev (evl (evLabel Payload (input linkCD hi N2N_BlockFetch) x)) ]─►
    absBFs linkCD hi bfs′
  → IoOffers (absNodesOf s) (input linkCD hi N2N_BlockFetch) x
srvInNodes-C-CD s x bfs′ sStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-L _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeD-io-no-when-C (nD s) iom fpC)))
        (noOffer→viewV _ (absNodeB-io-no-when-C (nB s) iom fpC)))
      (noOffer→viewV _ (absNodeA-io-no-when-C (nA s) iom fpC))
  where
  iom = iomem-in linkCD hi N2N_BlockFetch x
  nOff : IoOffers (absNodeC (nC s)) (input linkCD hi N2N_BlockFetch) x
  nOff = srvInNodeC-CD (nC s) x bfs′ sStep
  fpC = absNodeC-io-fp (nC s) iom (proj₂ nOff)

------------------------------------------------------------------------
-- §10  (T11) *** THE TWO MISSING BLOCKFETCH DIRECTIONS — the range request's
-- own READ and WRITE. ***
--
-- The BlockFetch io inventory before this section: §5's `cliOut*` (the hop's
-- CLIENT reading a responder payload) and §9's `srvIn*` (the hop's SERVER
-- writing one).  The `pp3` arm needs the OTHER TWO — node D's client WRITING its
-- `MsgRequestRange` and the relay's server READING it — which are exactly the
-- two the campaign's own inventory note calls "the other two directions" on this
-- axis (`LiveRelayCS` §5b(ii) says it of the ChainSync pair; the BlockFetch pair
-- is here).
--
-- *** WHAT IT COST, MEASURED, AND IT CONFIRMS THE BANKED RULE IN ITS SHARPER
-- FORM. ***  T10 banked "the ladder does not exist" is almost always "RUNG 1
-- does not exist".  Here not even rung 1 was missing: `ceqBFs01` (the server's
-- read row) and `ceqBFc07` (the client's write row) were both already banked, so
-- BOTH ladders are pure re-plumbing of rungs 2-4 — every refusal family below is
-- an existing lemma at a different `ApiHasLink` constructor (`ahlOut` for
-- `ahlIn`) or a different `BF.BFEv` (`BF.receiveBF` for `BF.sendBF`), which is
-- what §9's own header predicted ("the only change from §5 is the `ApiHasLink`
-- constructor").  The honest reading of the rule is therefore: *** a missing
-- POLARITY on an axis that already has the other one costs rungs 2-4 and no new
-- table fact at all. ***
--
-- The four rungs are §5's and §9's, unchanged in structure: rung 1 the peer's own
-- offer off its banked row, rung 2 the 12-peer bundle, rung 3 the node, rung 4
-- the four-node interleave.
------------------------------------------------------------------------

-- RUNG 1(a): the SERVER's own io offer at any fine position coarsening to
-- `bsIdle` — `bfSnxt` accepts the delivery of a `MsgRequestRange r` exactly
-- there (`ceqBFs01`), and the row is LENIENT in the payload's other three
-- components, exactly as the cell predicate that feeds it is
bfs-out-step : (i : Link) (d : Dir) (q : SN.BFsPos)
               (t0 : Time) (md : Mode) (ln : Length) (r : ChainRange)
             → coarsenBFs q ≡ NS.bsIdle
             → absBFs i d q
                 ─[ ev (evl (evLabel Payload (output i d N2N_BlockFetch)
                              (t0 , md , ln , blockFetch (MsgRequestRange r)))) ]─►
               absBFs i d (SN.bsReq1 r)
bfs-out-step i d q t0 md ln r pin =
  aBFs i d q (SN.bsReq1 r)
    (subst (λ z → NS.bfSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfSnxt i d z (Payload , output i d N2N_BlockFetch)
                    (t0 , md , ln , blockFetch (MsgRequestRange r))
                  ≡ just (NS.bsAreq r))
           (sym pin) (ceqBFs01 {t0} {md} {ln} {r} i d))

-- RUNG 1(b): … and the CLIENT's, at any fine position coarsening to `bcWrr r` —
-- `ceqBFc07`, whose payload is PINNED (the client writes its own request, so the
-- row tests the tuple with `≟`)
bfc-in-step : (i : Link) (d : Dir) (q : SN.BFcPos) (r : ChainRange)
            → coarsenBFc q ≡ NS.bcWrr r
            → absBFc i d q
                ─[ ev (evl (evLabel Payload (input i d N2N_BlockFetch)
                             (time₀ , FromInitiator , length₀
                             , blockFetch (MsgRequestRange r)))) ]─►
              absBFc i d (SN.bcHead BF.stBusy)
bfc-in-step i d q r pin =
  aBFc i d q (SN.bcHead BF.stBusy)
    (subst (λ z → NS.bfCfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfCnxt i d z (Payload , input i d N2N_BlockFetch)
                    (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
                  ≡ just NS.bcBusy)
           (sym pin) (ceqBFc07 {r} i d))

-- RUNG 2(a): the 12-peer BUNDLE offers what its BF SERVER offers, at the READ
-- polarity — `absBundle-BFs-ev` at `e₁ := BF.receiveBF l sv` (§9's rung 2 with
-- the other `BF.BFEv`; `ιBF (BF.receiveBF l d) ≡ output l d N2N_BlockFetch` and
-- `bfEvDir (BF.receiveBF l d) ≡ d`, both by `refl`)
srvOutBundle : (l : Link) (cl sv : Dir) → cl ≢ sv
   → (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos)
     (bfs bfs′ : SN.BFsPos) (ip : SN.InertPos) (x : Payload)
   → absBFs l sv bfs ─[ ev (evl (evLabel Payload (output l sv N2N_BlockFetch) x)) ]─►
     absBFs l sv bfs′
   → IoOffers (absBundleG l cl sv csc css bfc bfs ip) (output l sv N2N_BlockFetch) x
srvOutBundle l cl sv cl≢sv csc css bfc bfs bfs′ ip x sStep =
    _
  , absBundle-BFs-ev l cl sv csc css bfc bfs ip
      {e₁ = BF.receiveBF l sv} {qbs′ = bfs′} cl≢sv refl sStep

-- RUNG 2(b): … and what its BF CLIENT offers, at the WRITE polarity —
-- `absBundle-BFc-ev` at `e₁ := BF.sendBF l cl`.  (§5's rung 2 is hand-rolled at
-- the other polarity; this one takes the banked lemma, so the eleven internal
-- refusals are not re-listed)
cliInBundle : (l : Link) (cl sv : Dir) → cl ≢ sv
   → (csc : SN.CScPos) (css : SN.CSsPos) (bfc bfc′ : SN.BFcPos)
     (bfs : SN.BFsPos) (ip : SN.InertPos) (x : Payload)
   → absBFc l cl bfc ─[ ev (evl (evLabel Payload (input l cl N2N_BlockFetch) x)) ]─►
     absBFc l cl bfc′
   → IoOffers (absBundleG l cl sv csc css bfc bfs ip) (input l cl N2N_BlockFetch) x
cliInBundle l cl sv cl≢sv csc css bfc bfc′ bfs ip x cStep =
    _
  , absBundle-BFc-ev l cl sv csc css bfc bfs ip
      {e₁ = BF.sendBF l cl} {qbc′ = bfc′} cl≢sv refl cStep

-- RUNG 3(a), node B on link BD: `srvInNodeB-BD` at the READ polarity — `ahlOut`
-- for `ahlIn` and `iomem-out` for `iomem-in`, nothing else
srvOutNodeB-BD : (nb : SN.NodeStateB) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkBD hi (SN.NodeStateB.bfS-BD nb)
      ─[ ev (evl (evLabel Payload (output linkBD hi N2N_BlockFetch) x)) ]─►
    absBFs linkBD hi bfs′
  → IoOffers (absNodeB nb) (output linkBD hi N2N_BlockFetch) x
srvOutNodeB-BD nb x bfs′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkBD hi N2N_BlockFetch} {x}
                            (iomem-out linkBD hi N2N_BlockFetch x))
      (⦀-ev-R _ _
        (proj₂ (srvOutBundle linkBD lo hi (λ ())
                  (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb)
                  (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) bfs′
                  (SN.NodeStateB.inert-BD nb) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAB hi lo
             (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
             (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
             ahlOut (λ q → linkAB≢linkBD (sym q)) (iomem-out linkBD hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeB-drv-io-no nb (iomem-out linkBD hi N2N_BlockFetch x)))

-- RUNG 3(a), node C on link CD: the leg-CD mirror
srvOutNodeC-CD : (nc : SN.NodeStateC) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkCD hi (SN.NodeStateC.bfS-CD nc)
      ─[ ev (evl (evLabel Payload (output linkCD hi N2N_BlockFetch) x)) ]─►
    absBFs linkCD hi bfs′
  → IoOffers (absNodeC nc) (output linkCD hi N2N_BlockFetch) x
srvOutNodeC-CD nc x bfs′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkCD hi N2N_BlockFetch} {x}
                            (iomem-out linkCD hi N2N_BlockFetch x))
      (⦀-ev-R _ _
        (proj₂ (srvOutBundle linkCD lo hi (λ ())
                  (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc)
                  (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) bfs′
                  (SN.NodeStateC.inert-CD nc) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAC hi lo
             (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
             (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
             ahlOut (λ q → linkAC≢linkCD (sym q)) (iomem-out linkCD hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeC-drv-io-no nc (iomem-out linkCD hi N2N_BlockFetch x)))

-- RUNG 3(b), node D on link BD: `cliOutNodeD-BD` at the WRITE polarity
cliInNodeD-BD : (nd : SN.NodeStateD) (x : Payload) (bfc′ : SN.BFcPos)
  → absBFc linkBD hi (SN.NodeStateD.bfC-BD nd)
      ─[ ev (evl (evLabel Payload (input linkBD hi N2N_BlockFetch) x)) ]─►
    absBFc linkBD hi bfc′
  → IoOffers (absNodeD nd) (input linkBD hi N2N_BlockFetch) x
cliInNodeD-BD nd x bfc′ cStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkBD hi N2N_BlockFetch} {x}
                            (iomem-in linkBD hi N2N_BlockFetch x))
      (⦀-ev-L _ _
        (proj₂ (cliInBundle linkBD hi lo (λ ())
                  (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
                  (SN.NodeStateD.bfC-BD nd) bfc′ (SN.NodeStateD.bfS-BD nd)
                  (SN.NodeStateD.inert-BD nd) x cStep))
        (noOffer→viewV _
          (absBundleG-io-no linkCD hi lo
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd)
             (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
             ahlIn linkBD≢linkCD (iomem-in linkBD hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeD-drv-io-no nd (iomem-in linkBD hi N2N_BlockFetch x)))

-- RUNG 3(b), node D on link CD: its SECOND operand, so the interleave peels the
-- other way
cliInNodeD-CD : (nd : SN.NodeStateD) (x : Payload) (bfc′ : SN.BFcPos)
  → absBFc linkCD hi (SN.NodeStateD.bfC-CD nd)
      ─[ ev (evl (evLabel Payload (input linkCD hi N2N_BlockFetch) x)) ]─►
    absBFc linkCD hi bfc′
  → IoOffers (absNodeD nd) (input linkCD hi N2N_BlockFetch) x
cliInNodeD-CD nd x bfc′ cStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkCD hi N2N_BlockFetch} {x}
                            (iomem-in linkCD hi N2N_BlockFetch x))
      (⦀-ev-R _ _
        (proj₂ (cliInBundle linkCD hi lo (λ ())
                  (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd)
                  (SN.NodeStateD.bfC-CD nd) bfc′ (SN.NodeStateD.bfS-CD nd)
                  (SN.NodeStateD.inert-CD nd) x cStep))
        (noOffer→viewV _
          (absBundleG-io-no linkBD hi lo
             (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
             (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
             ahlIn (λ e → linkBD≢linkCD (sym e))
             (iomem-in linkCD hi N2N_BlockFetch x))))
      (noOffer→viewV _ (nodeD-drv-io-no nd (iomem-in linkCD hi N2N_BlockFetch x)))

-- RUNG 4(a): the four-node interleave for the DOWN server's READ — `srvInNodes-B-BD`
-- and `srvInNodes-C-CD` at the other polarity
srvOutNodes-B-BD : (s : SysState) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkBD hi (SN.NodeStateB.bfS-BD (nB s))
      ─[ ev (evl (evLabel Payload (output linkBD hi N2N_BlockFetch) x)) ]─►
    absBFs linkBD hi bfs′
  → IoOffers (absNodesOf s) (output linkBD hi N2N_BlockFetch) x
srvOutNodes-B-BD s x bfs′ sStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-L _ _ (proj₂ nOff)
        (noOffer→viewV _ (absGroupB-io-no (nB s) (nC s) (nD s) iom (proj₂ nOff))))
      (noOffer→viewV _ (absNodeA-io-no-when-B (nA s) iom fpB))
  where
  iom = iomem-out linkBD hi N2N_BlockFetch x
  nOff : IoOffers (absNodeB (nB s)) (output linkBD hi N2N_BlockFetch) x
  nOff = srvOutNodeB-BD (nB s) x bfs′ sStep
  fpB = absNodeB-io-fp (nB s) iom (proj₂ nOff)

srvOutNodes-C-CD : (s : SysState) (x : Payload) (bfs′ : SN.BFsPos)
  → absBFs linkCD hi (SN.NodeStateC.bfS-CD (nC s))
      ─[ ev (evl (evLabel Payload (output linkCD hi N2N_BlockFetch) x)) ]─►
    absBFs linkCD hi bfs′
  → IoOffers (absNodesOf s) (output linkCD hi N2N_BlockFetch) x
srvOutNodes-C-CD s x bfs′ sStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-L _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeD-io-no-when-C (nD s) iom fpC)))
        (noOffer→viewV _ (absNodeB-io-no-when-C (nB s) iom fpC)))
      (noOffer→viewV _ (absNodeA-io-no-when-C (nA s) iom fpC))
  where
  iom = iomem-out linkCD hi N2N_BlockFetch x
  nOff : IoOffers (absNodeC (nC s)) (output linkCD hi N2N_BlockFetch) x
  nOff = srvOutNodeC-CD (nC s) x bfs′ sStep
  fpC = absNodeC-io-fp (nC s) iom (proj₂ nOff)

-- RUNG 4(b): … and for node D's CLIENT's WRITE — `cliOutNodes-D-BD`/`-CD` at the
-- other polarity
cliInNodes-D-BD : (s : SysState) (x : Payload) (bfc′ : SN.BFcPos)
  → absBFc linkBD hi (SN.NodeStateD.bfC-BD (nD s))
      ─[ ev (evl (evLabel Payload (input linkBD hi N2N_BlockFetch) x)) ]─►
    absBFc linkBD hi bfc′
  → IoOffers (absNodesOf s) (input linkBD hi N2N_BlockFetch) x
cliInNodes-D-BD s x bfc′ cStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iom fpD)))
        (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iom fpD)))
      (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iom fpD))
  where
  iom = iomem-in linkBD hi N2N_BlockFetch x
  nOff : IoOffers (absNodeD (nD s)) (input linkBD hi N2N_BlockFetch) x
  nOff = cliInNodeD-BD (nD s) x bfc′ cStep
  fpD = absNodeD-io-fp (nD s) iom (proj₂ nOff)

cliInNodes-D-CD : (s : SysState) (x : Payload) (bfc′ : SN.BFcPos)
  → absBFc linkCD hi (SN.NodeStateD.bfC-CD (nD s))
      ─[ ev (evl (evLabel Payload (input linkCD hi N2N_BlockFetch) x)) ]─►
    absBFc linkCD hi bfc′
  → IoOffers (absNodesOf s) (input linkCD hi N2N_BlockFetch) x
cliInNodes-D-CD s x bfc′ cStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iom fpD)))
        (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iom fpD)))
      (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iom fpD))
  where
  iom = iomem-in linkCD hi N2N_BlockFetch x
  nOff : IoOffers (absNodeD (nD s)) (input linkCD hi N2N_BlockFetch) x
  nOff = cliInNodeD-CD (nD s) x bfc′ cStep
  fpD = absNodeD-io-fp (nD s) iom (proj₂ nOff)

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cross-node api campaign, Task 6b — *** THE ChainSync io INTRO LADDERS ***
-- (inventory items 2c and 2d): the two operand-side moves a `csWar` stability
-- refutation needs, at the ChainSync key.
--
-- WHY A SEPARATE MODULE AND NOT AN EXTENSION OF `LiveIoIntro`.  `LiveIoIntro` is
-- BlockFetch-keyed in the STATEMENT of six of its rungs — `fold-offers-in`,
-- `link-offers-in`, `medOfferIn`, `fold-drain-τ`, `link-drain-τ`, `medDrainτ` all
-- name `N2N_BlockFetch` literally, because the BF `hi` cell is position **5** of
-- the twelve-cell `uniformCfg` fold while the CS `hi` cell is position **3**
-- (`LiveIoIntro:842-892`, `:995-1021`), so the interleave nest has to be REBUILT
-- and cannot be re-parameterised.  Everything ELSE in that module is key-generic
-- and is CALLED here, never copied: the whole LN plumbing (`IoOffersN`,
-- `⦀N-ev-L`/`-R`, `⦀N-noOffer`, `noOfferN→viewV`, `skipN-no-ev`, `⦀N-τ-L`/`-R`),
-- the per-cell rungs (`cell-in-fire`, `cell-no-in-{d,i,dv,iv}`, `cell-drain-τ`),
-- the whole drain chain (`renameMap-τ-fwd`, `△-τ-L` and their transitive
-- machinery), the rename/`△` rungs (`rnN-vis-just` via `ι-vis-inv-in`,
-- `△-fire-P`, `prefix-no-in`) and the sibling-link refusals (`medF`,
-- `medF-no-in`).  Adding the six new definitions HERE also keeps `LiveIoIntro`
-- byte-identical, so nothing downstream of it is re-checked.
--
-- CONTENTS
--   §1  (item 2d) the CS-keyed medium ladders: the 12-cell fold at position 3, the
--       per-link decode, and the whole-medium `input` intro / drain τ.  The
--       four-link `⦀Fin` nest is written ONCE, CHANNEL-GENERIC (`medOfferInAt` /
--       `medτ-lift`), because the only channel-specific part of `medOfferIn` was
--       the per-link premise — so the CS instances are three lines each and a
--       future PROTOCOL pays nothing for that rung.  *** BUT IT IS `id`-GENERIC AND
--       `hi`-FIXED (T6b review, finding M-9): *** both bake `hi` into the label, so
--       the `lo` DIRECTION is not free — it needs the `hi` widened to a `d : Dir`
--       parameter, which is a one-token change at each of the two call sites since
--       the nest's siblings refuse by LINK and `cell-no-in-{d,i,dv,iv}` are already
--       `(Dir , IDs)`-generic.  Left `hi` here because no consumer needs `lo`.
--   §2  (item 2c) the CS io ladder rungs 1-4, SERVER-fired: the peer's own offer
--       at `csWar`, the 12-peer bundle lift, the two node lifts and the two nodes
--       lifts — for the two DOWN CS servers (node B on link BD, node C on CD).
--   §3  the leg-level forms the `pp2` ladder consumes, wired to `LiveChanCS`'s
--       accessors: the two `CellPreQ` arms as medium moves, and the nodes-side
--       offer off the coarse pin `coarsenCSs (dnCSs l s) ≡ csWar`.
--
-- *** WHICH SERVERS, AND WHY ONLY TWO. ***  Four CS servers exist (node A's two,
-- plus the relay's two down ones).  Only the DOWN pair is built: `pp2`'s slot is
-- the leg's DOWN CS server (`LiveRelayCS.CSAt`'s `pp2` equation is on
-- `dnCSs l s`), and the remaining CS arms need either that same slot (`cp6`/`pp0`)
-- or a position that is io-CLOSED and therefore has no io ladder at all (`cp5`'s
-- `ccIdle` — `LiveCSRow.cscIdle-in-⊥`/`cscIdle-out-⊥`).  The node-A lifts would be
-- the `srvInNodeA-AB`/`-AC` shape with `srvInBundleCS` substituted, ~40 lines, and
-- are deliberately NOT built because no consumer can reach them (the same
-- discipline `LiveCSRow` §4b applies to the three unreachable `recvCS*` keys).
--
-- KEEP IN SYNC — `LiveIoIntro`'s §6/§7 nests (`fold-offers-in` `:842-892`,
-- `link-offers-in` `:911-935`, `fold-drain-τ` `:995-1021`, `link-drain-τ`
-- `:1090-1102`) and §8's private four-link nest (`gnestEq`, `:1128-1129`).  §1
-- below is those five at the ChainSync key with the fold index moved from 5 to 3;
-- §9's four `srvIn*` (`:1299-1458`) are §2's model.  If `Params.uniformCfg`'s cell
-- ORDER changes, both modules' folds move together.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Bool using ( Bool; false )
open import Data.Empty using ( ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.List using ( List; []; _∷_; map )
open import Data.Fin using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )

open import Process_Trees
  using ( PTree; ExtI; AnyTypes; ContinueType; react )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveIoIntroCS
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p
  -- (T8c-ii) `output` joins `input`: §1c is §1's `input` ladder at the READER's
  -- polarity, which is what the down CS SERVER's own wire-read needs
  using ( Net; Net-≟; Net_Api; Net_Api-≟; Link; break; input; output )
-- (T8c-ii) `chainSync`/`MsgCSRequestNext` are named by §2b's rung 1(b): the
-- server's read row is LENIENT in the payload tuple's first three components, so the
-- lemma quantifies them and spells the message out
open import CSP.Examples.Cardano_network.Data p
  -- (T11) §3's `csWrf` position instance names the ROLLFORWARD the relay's own
  -- server writes at `pp3`
  using ( Payload; chainSync; MsgCSRequestNext
        ; MsgCSRollForward; Header; Tip )
open import CSP.Examples.Cardano_network.NetCommon p using ( ιNet; ιNet⁻¹; ιNet-linv )
open import CSP.Examples.Cardano_network.Params using ( Params )
-- (T8c-ii) `Time`/`Length` are the two lenient components of the read row's payload
-- (T11) … and `time₀`/`length₀`, the two PINNED components of that write's payload
open Params p using ( linkConfig; Time; Length; time₀; length₀ )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi; IDs; Mode
  -- (T11) the responder-side mode the `csWrf` write's payload is pinned at
  ; FromResponder
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive
  ; N2N_LeiosNotify; N2N_LeiosFetch )
import CSP.Examples.Cardano_network.ChainSync p as CS

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as OpA
open OpA using ( _△_; _⦀_; Prefix₀ )

import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; τ )
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN

-- the medium's own alphabet rename (the SAME `CSP.Rename` instance `decLink` is
-- defined with)
import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload}
  ιNet ιNet⁻¹ ιNet-linv as RenNet
open RenNet using ( renameMap; rnFan; rnCollect; invRel; invPreimg; ι-vis-inv )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; phase; broken; decMed; decLink; decCopy
        ; CopyPhase; empty; draining; full; NetProcN )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( NetProc; fold-react; mkReactF )
open STC.MedNO using ( force-renameMap-react )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( IoOffers; ⦀-ev-L; ⦀-ev-R; ⦀-noOffer; ∥⇘⇙-ev-soloL; ⦀-τ-L; ⦀-τ-R
        ; absCSs; absBundleG; absNodeB; absNodeC; absNodesOf; coarsenCSs
        -- (T8c-ii) §2b's two new ladders: node D's own CS CLIENT (the writer) and
        -- the relay's CS SERVER at the READER's polarity
        ; absCSc; absNodeA; absNodeD; coarsenCSc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
-- (T6b review, finding M-4: this module opened `SysOracle blkA` TWICE at the same
-- instantiation with disjoint `using` lists; the two are merged here, restoring the
-- campaign's one-import-per-parameterised-module rule)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( io⇒¬api; ahlIn
        -- (T8c-ii) the READER polarity's link witness, for §2b(b)'s two rung-3 lifts
        ; ahlOut )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  using ( aCSs; ceqCSs16
        -- (T8c-ii) rung 1 of the two new ladders: the client's own request WRITE row
        -- (`ccWreq → ccAwait`, payload-gated) and the server's request READ row
        -- (`csIdle → csAreq`, LENIENT in the tuple's first three components — which
        -- is exactly `LiveChanCS.FullMsg`'s shape, so `ReqOnly` feeds it directly)
        -- (T11) … and the ROLLFORWARD wire-send row (`csWrf ht → csIdle`,
        -- payload-PINNED), which is §3's new position instance's rung 1
        ; aCSc; ceqCSc11; ceqCSs01; ceqCSs14 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteKaTs blkA
  using ( absBundle-CSs-ev
        -- (T8c-ii) rung 2 of the CLIENT ladder — the CS-client twin
        ; absBundle-CSc-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( absBundleG-io-no; nodeB-drv-io-no; nodeC-drv-io-no
        ; linkAB≢linkBD; linkAC≢linkCD
        -- (T8c-ii) node D's own driver refusal (rung 3 of the CLIENT ladder) and the
        -- two-link disequality its co-bundle refusal needs
        ; nodeD-drv-io-no; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink3 blkA
  using ( absNodeB-io-fp; absNodeC-io-fp; absGroupB-io-no
        ; absNodeA-io-no-when-B
        ; absNodeA-io-no-when-C; absNodeB-io-no-when-C; absNodeD-io-no-when-C
        -- (T8c-ii) node D's own fingerprint and the three siblings' refusals against
        -- it — rung 4 of the CLIENT ladder, node D being the FOURTH operand
        ; absNodeD-io-fp
        ; absNodeA-io-no-when-D; absNodeB-io-no-when-D; absNodeC-io-no-when-D )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( dnLink )

-- *** THE KEY-GENERIC HALF OF THE BF LADDERS, CALLED AND NEVER COPIED. ***
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveIoIntro blkA
  using ( SkipA; IoOffersN; noOfferN→viewV; ⦀N-ev-L; ⦀N-ev-R; ⦀N-noOffer
        ; skipN-no-ev; rnN-vis-just; △-fire-P
        ; cell-in-fire; cell-no-in-d; cell-no-in-i; cell-no-in-dv; cell-no-in-iv
        ; ι-vis-inv-in; prefix-no-in; medF; medF-no-in; skipA-no-ev; iomem-in
        ; cell-drain-τ; ⦀N-τ-L; ⦀N-τ-R; renameMap-τ-fwd; △-τ-L
        -- (T8c-ii) the OUT polarity of the same key-generic half — every one of these
        -- is `(Dir , IDs)`-generic, which is why §1c is a transcription of §1 rather
        -- than a second design
        ; cell-out-fire; cell-no-out-d; cell-no-out-i; cell-no-out-dv; cell-no-out-iv
        ; ι-vis-inv-out; prefix-no-out; medF-no-out; iomem-out )
-- the CS channel invariant's own accessors and the `MsgCSAwaitReply` payload
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanCS blkA
  using ( arPayload; dnCSsOf; cellCSDn
        -- (T8c-ii) the client's own request payload (rung 1 of the CLIENT ladder is
        -- payload-GATED, unlike the server's) and node D's CS-client accessor
        ; rnPayload; dnCScOf )

------------------------------------------------------------------------
-- §1  (ITEM 2d) THE CS-KEYED MEDIUM LADDERS.
--
-- Two ladders, `input` and drain-τ, each with three rungs: the twelve-cell fold,
-- the per-link decode (rename + `△`), and the four-link `⦀Fin`.  The first rung is
-- the only genuinely CS-specific one — the ChainSync `hi` cell is position 3 of
-- `uniformCfg`, so three cells refuse before it and eight plus the `Skip` tail
-- after it (against the BF cell's five before and six after).  The `△`/rename rung
-- is a verbatim re-parameterisation of `LiveIoIntro`'s, and the four-link rung is
-- written CHANNEL-GENERIC here, taking the fired link's own offer as an argument.
------------------------------------------------------------------------

-- the whole link fold ACCEPTS the `hi`-ChainSync cell's `input` when that cell is
-- EMPTY (the position-3 nest: three cells before, eight plus the `Skip` tail after)
fold-offers-in-cs : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_ChainSync ≡ empty
  → IoOffersN (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))
              (input l hi N2N_ChainSync) x
fold-offers-in-cs l ph x he =
    _
  , ⦀N-ev-R c0 _
      (⦀N-ev-R c1 _
        (⦀N-ev-R c2 _
          (⦀N-ev-L c3 _ fire
            (noOfferN→viewV _ noTail))
          (cell-no-in-dv l lo N2N_ChainSync (ph lo N2N_ChainSync) (λ ())))
        (cell-no-in-iv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) (λ ())))
      (cell-no-in-dv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) (λ ()))
  where
  -- the first four cells of the link's `uniformCfg` fold, in the config's order
  c0 c1 c2 c3 : NetProcN
  c0 = decCopy l lo N2N_KeepAlive (ph lo N2N_KeepAlive)
  c1 = decCopy l hi N2N_KeepAlive (ph hi N2N_KeepAlive)
  c2 = decCopy l lo N2N_ChainSync (ph lo N2N_ChainSync)
  c3 = decCopy l hi N2N_ChainSync (ph hi N2N_ChainSync)
  -- the fired cell's own step, with the phase hypothesis substituted in
  fire : c3 LN.─[ LN.ev (LN.evl (LN.evLabel Payload (input l hi N2N_ChainSync) x)) ]─►
         proj₁ (cell-in-fire l hi N2N_ChainSync x)
  fire = subst (λ z → decCopy l hi N2N_ChainSync z
                        LN.─[ LN.ev (LN.evl (LN.evLabel Payload (input l hi N2N_ChainSync) x)) ]─►
                      proj₁ (cell-in-fire l hi N2N_ChainSync x))
               (sym he) (proj₂ (cell-in-fire l hi N2N_ChainSync x))
  -- the eight cells AFTER the ChainSync `hi` cell, plus the `Skip` tail
  noTail : ¬ IoOffersN
             (decCopy l lo N2N_BlockFetch (ph lo N2N_BlockFetch) OpN.⦀
              (decCopy l hi N2N_BlockFetch (ph hi N2N_BlockFetch) OpN.⦀
               (decCopy l lo N2N_TxSubmission (ph lo N2N_TxSubmission) OpN.⦀
                (decCopy l hi N2N_TxSubmission (ph hi N2N_TxSubmission) OpN.⦀
                 (decCopy l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) OpN.⦀
                  (decCopy l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) OpN.⦀
                   (decCopy l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) OpN.⦀
                    (decCopy l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) OpN.⦀ ⦀⋆ []))))))))
             (input l hi N2N_ChainSync) x
  noTail =
    ⦀N-noOffer _ _ (cell-no-in-d l lo N2N_BlockFetch (ph lo N2N_BlockFetch) (λ ()))
      (⦀N-noOffer _ _ (cell-no-in-i l hi N2N_BlockFetch (ph hi N2N_BlockFetch) (λ ()))
        (⦀N-noOffer _ _ (cell-no-in-d l lo N2N_TxSubmission (ph lo N2N_TxSubmission) (λ ()))
          (⦀N-noOffer _ _ (cell-no-in-i l hi N2N_TxSubmission (ph hi N2N_TxSubmission) (λ ()))
            (⦀N-noOffer _ _ (cell-no-in-d l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) (λ ()))
              (⦀N-noOffer _ _ (cell-no-in-i l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) (λ ()))
                (⦀N-noOffer _ _ (cell-no-in-d l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) (λ ()))
                  (⦀N-noOffer _ _ (cell-no-in-i l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) (λ ()))
                    skipN-no-ev)))))))

-- an UNBROKEN link whose `hi`-ChainSync cell is EMPTY accepts that cell's `input`
-- out of the WHOLE per-link decode: the fold fires, the rename transports it and
-- the `△` commits to the left operand
link-offers-in-cs : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_ChainSync ≡ empty
  → IoOffers (decLink l ph false) (input l hi N2N_ChainSync) x
link-offers-in-cs l ph x he with fold-react l ph
... | mkReactF V T feq =
    _
  , △-fire-P
      (force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
      refl
      (proj₂ renOff)
      (prefix-no-in l l hi N2N_ChainSync x)
  where
  renOff : Σ[ M ∈ NetProc ]
             (rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
                    (rnCollect V (invPreimg ι-vis-inv (Payload , input l hi N2N_ChainSync) x))
              ≡ just M)
  renOff with fold-offers-in-cs l ph x he
  ... | M , LN.sVis {v = vP} {τc = τcP} feq′ br =
        renameMap M
      , rnN-vis-just Payload (input l hi N2N_ChainSync) x V
          (ι-vis-inv-in l hi N2N_ChainSync x)
          (trans (cong (λ n → OpN.viewV n (Payload , input l hi N2N_ChainSync) x)
                       (trans (sym feq) feq′))
                 br)

-- the 12-cell fold's drain τ, at the `(hi , N2N_ChainSync)` cell.  Same nest with
-- the refusals REMOVED — a τ of an interleave takes no sibling `viewV`-nothing.
fold-drain-τ-cs : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_ChainSync ≡ draining x
  → Σ[ M ∈ NetProcN ]
      (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
         LN.─[ LN.τ ]─► M)
fold-drain-τ-cs l ph x hd =
    _
  , ⦀N-τ-R c0 _
      (⦀N-τ-R c1 _
        (⦀N-τ-R c2 _
          (⦀N-τ-L c3 _ fire)))
  where
  -- the four cells up to and including the ChainSync `hi` one (position 3)
  c0 c1 c2 c3 : NetProcN
  c0 = decCopy l lo N2N_KeepAlive (ph lo N2N_KeepAlive)
  c1 = decCopy l hi N2N_KeepAlive (ph hi N2N_KeepAlive)
  c2 = decCopy l lo N2N_ChainSync (ph lo N2N_ChainSync)
  c3 = decCopy l hi N2N_ChainSync (ph hi N2N_ChainSync)
  -- the draining cell's own τ, with the phase hypothesis substituted in
  fire : c3 LN.─[ LN.τ ]─► decCopy l hi N2N_ChainSync empty
  fire = subst (λ z → decCopy l hi N2N_ChainSync z
                        LN.─[ LN.τ ]─► decCopy l hi N2N_ChainSync empty)
               (sym hd) (cell-drain-τ l hi N2N_ChainSync x)

-- the whole per-link decode's τ: the fold's drain τ rides the rename and the `△`
-- commits to the left operand (the `break` prefix is a react, so `force-△-react`
-- applies)
link-drain-τ-cs : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_ChainSync ≡ draining x
  → Σ[ M ∈ NetProc ] (decLink l ph false ─[ τ ]─► M)
link-drain-τ-cs l ph x hd with fold-react l ph
... | mkReactF V T feq =
    _
  , △-τ-L
      (force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
      refl
      (renameMap-τ-fwd
        (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))
        (proj₂ (fold-drain-τ-cs l ph x hd)))

------------------------------------------------------------------------
-- §1c  (T8c-ii) THE SAME TWO RUNGS AT THE READER'S POLARITY — the `output`
-- ladder.
--
-- *** WHY IT HAS TO BE BUILT AND CANNOT BE CALLED. ***  `LiveIoIntro`'s
-- `link-offers-out` (`:430-452`) is the BF instance, and it names `N2N_BlockFetch`
-- literally for §1's own reason: the twelve-cell fold's nest is POSITIONAL, and the
-- ChainSync `hi` cell is position 3 where the BlockFetch one is position 5.  So the
-- two lemmas below are `fold-offers-in-cs` / `link-offers-in-cs` with the polarity
-- flipped, and every ingredient of the flip is already key-generic in
-- `LiveIoIntro`: `cell-out-fire`, `cell-no-out-{d,i,dv,iv}`, `ι-vis-inv-out`,
-- `prefix-no-out`.  *** KEEP IN SYNC WITH §1's TWO, LINE BY LINE: *** the nest,
-- the four cell names and the eight-plus-`Skip` tail are identical; only the label
-- constructor, the cell-phase premise (`full x` for `empty`) and the four refusal
-- names change.
--
-- WHAT CONSUMES IT: the `cp6`/`pp0` arms' SECOND `⊥`-premise — the down CS server
-- at `csIdle` facing a cell that holds an unread `MsgCSRequestNext` can READ it, so
-- such a configuration is not stable.  That is the one arm of `LiveDrvCSD`'s
-- `CellFresh` that neither the drain τ nor the client's write covers.
------------------------------------------------------------------------

-- the whole link fold offers the `hi`-ChainSync cell's `output` when that cell is
-- FULL (the position-3 nest again: three cells before, eight plus the `Skip` tail
-- after — §1's `fold-offers-in-cs` with the polarity flipped)
fold-offers-out-cs : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_ChainSync ≡ full x
  → IoOffersN (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))
              (output l hi N2N_ChainSync) x
fold-offers-out-cs l ph x hf =
    _
  , ⦀N-ev-R c0 _
      (⦀N-ev-R c1 _
        (⦀N-ev-R c2 _
          (⦀N-ev-L c3 _ fire
            (noOfferN→viewV _ noTail))
          (cell-no-out-dv l lo N2N_ChainSync (ph lo N2N_ChainSync) (λ ())))
        (cell-no-out-iv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) (λ ())))
      (cell-no-out-dv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) (λ ()))
  where
  -- the first four cells of the link's `uniformCfg` fold, in the config's order
  c0 c1 c2 c3 : NetProcN
  c0 = decCopy l lo N2N_KeepAlive (ph lo N2N_KeepAlive)
  c1 = decCopy l hi N2N_KeepAlive (ph hi N2N_KeepAlive)
  c2 = decCopy l lo N2N_ChainSync (ph lo N2N_ChainSync)
  c3 = decCopy l hi N2N_ChainSync (ph hi N2N_ChainSync)
  -- the fired cell's own step, with the phase hypothesis substituted in
  fire : c3 LN.─[ LN.ev (LN.evl (LN.evLabel Payload (output l hi N2N_ChainSync) x)) ]─►
         proj₁ (cell-out-fire l hi N2N_ChainSync x)
  fire = subst (λ z → decCopy l hi N2N_ChainSync z
                        LN.─[ LN.ev (LN.evl (LN.evLabel Payload (output l hi N2N_ChainSync) x)) ]─►
                      proj₁ (cell-out-fire l hi N2N_ChainSync x))
               (sym hf) (proj₂ (cell-out-fire l hi N2N_ChainSync x))
  -- the eight cells AFTER the ChainSync `hi` cell, plus the `Skip` tail
  noTail : ¬ IoOffersN
             (decCopy l lo N2N_BlockFetch (ph lo N2N_BlockFetch) OpN.⦀
              (decCopy l hi N2N_BlockFetch (ph hi N2N_BlockFetch) OpN.⦀
               (decCopy l lo N2N_TxSubmission (ph lo N2N_TxSubmission) OpN.⦀
                (decCopy l hi N2N_TxSubmission (ph hi N2N_TxSubmission) OpN.⦀
                 (decCopy l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) OpN.⦀
                  (decCopy l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) OpN.⦀
                   (decCopy l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) OpN.⦀
                    (decCopy l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) OpN.⦀ ⦀⋆ []))))))))
             (output l hi N2N_ChainSync) x
  noTail =
    ⦀N-noOffer _ _ (cell-no-out-d l lo N2N_BlockFetch (ph lo N2N_BlockFetch) (λ ()))
      (⦀N-noOffer _ _ (cell-no-out-i l hi N2N_BlockFetch (ph hi N2N_BlockFetch) (λ ()))
        (⦀N-noOffer _ _ (cell-no-out-d l lo N2N_TxSubmission (ph lo N2N_TxSubmission) (λ ()))
          (⦀N-noOffer _ _ (cell-no-out-i l hi N2N_TxSubmission (ph hi N2N_TxSubmission) (λ ()))
            (⦀N-noOffer _ _ (cell-no-out-d l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) (λ ()))
              (⦀N-noOffer _ _ (cell-no-out-i l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) (λ ()))
                (⦀N-noOffer _ _ (cell-no-out-d l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) (λ ()))
                  (⦀N-noOffer _ _ (cell-no-out-i l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) (λ ()))
                    skipN-no-ev)))))))

-- an UNBROKEN link whose `hi`-ChainSync cell is FULL offers that cell's `output`
-- out of the WHOLE per-link decode (§1's `link-offers-in-cs` with the polarity
-- flipped: `ι-vis-inv-out` and `prefix-no-out` for their `in` twins)
link-offers-out-cs : (l : Link) (ph : Dir → IDs → CopyPhase) (x : Payload)
  → ph hi N2N_ChainSync ≡ full x
  → IoOffers (decLink l ph false) (output l hi N2N_ChainSync) x
link-offers-out-cs l ph x hf with fold-react l ph
... | mkReactF V T feq =
    _
  , △-fire-P
      (force-renameMap-react
        {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
      refl
      (proj₂ renOff)
      (prefix-no-out l l hi N2N_ChainSync x)
  where
  renOff : Σ[ M ∈ NetProc ]
             (rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
                    (rnCollect V (invPreimg ι-vis-inv (Payload , output l hi N2N_ChainSync) x))
              ≡ just M)
  renOff with fold-offers-out-cs l ph x hf
  ... | M , LN.sVis {v = vP} {τc = τcP} feq′ br =
        renameMap M
      , rnN-vis-just Payload (output l hi N2N_ChainSync) x V
          (ι-vis-inv-out l hi N2N_ChainSync x)
          (trans (cong (λ n → OpN.viewV n (Payload , output l hi N2N_ChainSync) x)
                       (trans (sym feq) feq′))
                 br)

------------------------------------------------------------------------
-- §1b  THE FOUR-LINK `⦀Fin` RUNG, ONCE AND CHANNEL-GENERIC.
--
-- `LiveIoIntro`'s `medOfferIn`/`medDrainτ` bake `N2N_BlockFetch` into their
-- statements, but the FOUR-LINK nest itself never looks at the channel: the fired
-- link supplies its own move and the three siblings refuse by LINK
-- (`medF-no-in`, which is `(d , id)`-generic) or, for the τ, refuse nothing at
-- all.  So the two lemmas below take the fired link's move as an ARGUMENT and are
-- reusable at every PROTOCOL id — which is why item 2d's six definitions cost four
-- here rather than six.  *** THE PRECISE SCOPE (T6b review, M-9): `id`-GENERIC,
-- `hi`-FIXED. ***  Both signatures below quantify over `id : IDs` but write `hi`
-- literally, so a new protocol is free and the `lo` DIRECTION IS NOT: it wants the
-- `hi` widened to a `d : Dir` parameter.  That widening is one token at each of the
-- two call sites (the sibling refusals are by LINK and the per-cell rungs are
-- already `(Dir , IDs)`-generic); it is not done because no consumer needs `lo`.
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

  -- *** THE CHANNEL-GENERIC WHOLE-MEDIUM io INTRO. ***  whatever `input i hi id`
  -- the fired link accepts, the whole breakable medium accepts
  medOfferInAt : (id : IDs) (i : Link) (x : Payload)
    → IoOffers (medF m i) (input i hi id) x
    → IoOffers (decMed m) (input i hi id) x
  medOfferInAt id i x off =
      proj₁ (nest i off)
    , subst (λ z → z ─[ ev (evl (evLabel Payload (input i hi id) x)) ]─►
                   proj₁ (nest i off))
        (sym gnestEq) (proj₂ (nest i off))
    where
    -- the four-link nest, one clause per link (the sibling refusals are the
    -- channel pinning at the three other links, which is key-generic)
    nest : (j : Link) → IoOffers (medF m j) (input j hi id) x
         → Σ[ M ∈ NetProc ]
             ((g0 ⦀ grest1) ─[ ev (evl (evLabel Payload (input j hi id) x)) ]─► M)
    nest fzero o =
        _
      , ⦀-ev-L g0 grest1 (proj₂ o)
          (noOffer→viewV grest1
            (⦀-noOffer g1 grest2 (medF-no-in m (fsuc fzero) (λ ()))
              (⦀-noOffer g2 grest3 (medF-no-in m (fsuc (fsuc fzero)) (λ ()))
                (⦀-noOffer g3 (SkipA) (medF-no-in m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev))))
    nest (fsuc fzero) o =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-L g1 grest2 (proj₂ o)
            (noOffer→viewV grest2
              (⦀-noOffer g2 grest3 (medF-no-in m (fsuc (fsuc fzero)) (λ ()))
                (⦀-noOffer g3 (SkipA) (medF-no-in m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev))))
          (noOffer→viewV g0 (medF-no-in m fzero (λ ())))
    nest (fsuc (fsuc fzero)) o =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-R g1 grest2
            (⦀-ev-L g2 grest3 (proj₂ o)
              (noOffer→viewV grest3
                (⦀-noOffer g3 (SkipA) (medF-no-in m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev)))
            (noOffer→viewV g1 (medF-no-in m (fsuc fzero) (λ ()))))
          (noOffer→viewV g0 (medF-no-in m fzero (λ ())))
    nest (fsuc (fsuc (fsuc fzero))) o =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-R g1 grest2
            (⦀-ev-R g2 grest3
              (⦀-ev-L g3 (SkipA) (proj₂ o)
                (noOffer→viewV (SkipA)
                  (skipA-no-ev {Payload}
                    {input (fsuc (fsuc (fsuc fzero))) hi id} {x})))
              (noOffer→viewV g2 (medF-no-in m (fsuc (fsuc fzero)) (λ ()))))
            (noOffer→viewV g1 (medF-no-in m (fsuc fzero) (λ ()))))
          (noOffer→viewV g0 (medF-no-in m fzero (λ ())))

  -- *** THE CHANNEL-GENERIC WHOLE-MEDIUM τ LIFT. ***  a τ of one link is a τ of
  -- the whole medium; no sibling obligations at any rung
  medτ-lift : (i : Link) → Σ[ M ∈ NetProc ] (medF m i ─[ τ ]─► M)
            → Σ[ M ∈ NetProc ] (decMed m ─[ τ ]─► M)
  medτ-lift i off =
      proj₁ (nestτ i off)
    , subst (λ z → z ─[ τ ]─► proj₁ (nestτ i off)) (sym gnestEq) (proj₂ (nestτ i off))
    where
    nestτ : (j : Link) → Σ[ M ∈ NetProc ] (medF m j ─[ τ ]─► M)
          → Σ[ M ∈ NetProc ] ((g0 ⦀ grest1) ─[ τ ]─► M)
    nestτ fzero o = _ , ⦀-τ-L g0 grest1 (proj₂ o)
    nestτ (fsuc fzero) o =
      _ , ⦀-τ-R g0 grest1 (⦀-τ-L g1 grest2 (proj₂ o))
    nestτ (fsuc (fsuc fzero)) o =
      _ , ⦀-τ-R g0 grest1
            (⦀-τ-R g1 grest2 (⦀-τ-L g2 grest3 (proj₂ o)))
    nestτ (fsuc (fsuc (fsuc fzero))) o =
      _ , ⦀-τ-R g0 grest1
            (⦀-τ-R g1 grest2
              (⦀-τ-R g2 grest3 (⦀-τ-L g3 (SkipA) (proj₂ o))))

  -- *** (2d, i) THE WHOLE-MEDIUM CS io INTRO. ***  an UNBROKEN link whose
  -- ChainSync `hi` cell is EMPTY accepts `input i hi N2N_ChainSync ? x` out of the
  -- whole breakable medium — the medium half of the `CellPreQ` `empty` arm
  medOfferInCS : (i : Link) (x : Payload)
    → broken m i ≡ false → phase m i hi N2N_ChainSync ≡ empty
    → IoOffers (decMed m) (input i hi N2N_ChainSync) x
  medOfferInCS i x ebr he =
    medOfferInAt N2N_ChainSync i x
      (subst (λ b → IoOffers (decLink i (phase m i) b) (input i hi N2N_ChainSync) x)
             (sym ebr) (link-offers-in-cs i (phase m i) x he))

  -- *** (2d, ii) THE WHOLE-MEDIUM CS DRAIN τ. ***  an UNBROKEN link whose
  -- ChainSync `hi` cell is DRAINING performs a τ of the whole breakable medium —
  -- the medium half of the `CellPreQ` `draining` arm
  medDrainτCS : (i : Link) (x : Payload)
    → broken m i ≡ false → phase m i hi N2N_ChainSync ≡ draining x
    → Σ[ M ∈ NetProc ] (decMed m ─[ τ ]─► M)
  medDrainτCS i x ebr hd =
    medτ-lift i
      (subst (λ b → Σ[ M ∈ NetProc ] (decLink i (phase m i) b ─[ τ ]─► M))
             (sym ebr) (link-drain-τ-cs i (phase m i) x hd))

  -- *** (T8c-ii) THE CHANNEL-GENERIC WHOLE-MEDIUM io READ INTRO. ***  `medOfferInAt`
  -- at the other polarity: whatever `output i hi id` the fired link offers, the whole
  -- breakable medium offers.  Same four-clause nest, `medF-no-out` for `medF-no-in`
  medOfferOutAt : (id : IDs) (i : Link) (x : Payload)
    → IoOffers (medF m i) (output i hi id) x
    → IoOffers (decMed m) (output i hi id) x
  medOfferOutAt id i x off =
      proj₁ (nest i off)
    , subst (λ z → z ─[ ev (evl (evLabel Payload (output i hi id) x)) ]─►
                   proj₁ (nest i off))
        (sym gnestEq) (proj₂ (nest i off))
    where
    nest : (j : Link) → IoOffers (medF m j) (output j hi id) x
         → Σ[ M ∈ NetProc ]
             ((g0 ⦀ grest1) ─[ ev (evl (evLabel Payload (output j hi id) x)) ]─► M)
    nest fzero o =
        _
      , ⦀-ev-L g0 grest1 (proj₂ o)
          (noOffer→viewV grest1
            (⦀-noOffer g1 grest2 (medF-no-out m (fsuc fzero) (λ ()))
              (⦀-noOffer g2 grest3 (medF-no-out m (fsuc (fsuc fzero)) (λ ()))
                (⦀-noOffer g3 (SkipA) (medF-no-out m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev))))
    nest (fsuc fzero) o =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-L g1 grest2 (proj₂ o)
            (noOffer→viewV grest2
              (⦀-noOffer g2 grest3 (medF-no-out m (fsuc (fsuc fzero)) (λ ()))
                (⦀-noOffer g3 (SkipA) (medF-no-out m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev))))
          (noOffer→viewV g0 (medF-no-out m fzero (λ ())))
    nest (fsuc (fsuc fzero)) o =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-R g1 grest2
            (⦀-ev-L g2 grest3 (proj₂ o)
              (noOffer→viewV grest3
                (⦀-noOffer g3 (SkipA) (medF-no-out m (fsuc (fsuc (fsuc fzero))) (λ ()))
                  skipA-no-ev)))
            (noOffer→viewV g1 (medF-no-out m (fsuc fzero) (λ ()))))
          (noOffer→viewV g0 (medF-no-out m fzero (λ ())))
    nest (fsuc (fsuc (fsuc fzero))) o =
        _
      , ⦀-ev-R g0 grest1
          (⦀-ev-R g1 grest2
            (⦀-ev-R g2 grest3
              (⦀-ev-L g3 (SkipA) (proj₂ o)
                (noOffer→viewV (SkipA)
                  (skipA-no-ev {Payload}
                    {output (fsuc (fsuc (fsuc fzero))) hi id} {x})))
              (noOffer→viewV g2 (medF-no-out m (fsuc (fsuc fzero)) (λ ()))))
            (noOffer→viewV g1 (medF-no-out m (fsuc fzero) (λ ()))))
          (noOffer→viewV g0 (medF-no-out m fzero (λ ())))

  -- *** (T8c-ii) THE WHOLE-MEDIUM CS io READ INTRO. ***  an UNBROKEN link whose
  -- ChainSync `hi` cell is FULL offers `output i hi N2N_ChainSync ? x` out of the
  -- whole breakable medium — the medium half of the `ReqOnly` arm's refutation
  medOfferOutCS : (i : Link) (x : Payload)
    → broken m i ≡ false → phase m i hi N2N_ChainSync ≡ full x
    → IoOffers (decMed m) (output i hi N2N_ChainSync) x
  medOfferOutCS i x ebr hf =
    medOfferOutAt N2N_ChainSync i x
      (subst (λ b → IoOffers (decLink i (phase m i) b) (output i hi N2N_ChainSync) x)
             (sym ebr) (link-offers-out-cs i (phase m i) x hf))

------------------------------------------------------------------------
-- §2  (ITEM 2c) THE NODES-SIDE io INTRO LADDER, CS-SERVER-FIRED.
--
-- The mirror of `LiveIoIntro` §9 at the ChainSync key.  RUNG 2 is the banked
-- `SysOracle_RouteKaTs.absBundle-CSs-ev` at `e₁ := CS.sendCS l sv`, with
-- `ιCS (CS.sendCS l d) ≡ input l d N2N_ChainSync` and `csEvDir (CS.sendCS l d) ≡ d`
-- both `refl` — so that rung costs four lines, and the eleven internal sibling
-- refusals come for free.  RUNGS 3-4 are `srvInNodeB-BD`/`srvInNodes-B-BD` and
-- their leg-CD twins with the channel and the bundle lemma substituted; every
-- refusal they use (`absBundleG-io-no`, `nodeB-drv-io-no`, `absGroupB-io-no`, the
-- pairwise `absNode*-io-no-when-*`) is io-LABEL-generic, which is why this ladder
-- is materially cheaper than the BF one was.
------------------------------------------------------------------------

-- RUNG 1: the CS SERVER's own io offer, at any fine position that coarsens to
-- `csWar` — `csSnxt` accepts the wire-send of `MsgCSAwaitReply` exactly there
-- (`ceqCSs16`), and `absCSs l d q` depends on `q` only through `coarsenCSs q`.  The
-- step is returned at its EXPLICIT target (`ssHead CS.stMustReply`, the fine
-- position `coarsenCSs` sends to `csMust`) because rung 2's banked lemma is stated
-- between two named positions, not between offers.
css-in-step : (i : Link) (d : Dir) (q : SN.CSsPos)
            → coarsenCSs q ≡ NS.csWar
            → absCSs i d q
                ─[ ev (evl (evLabel Payload (input i d N2N_ChainSync) arPayload)) ]─►
              absCSs i d (SN.ssHead CS.stMustReply)
css-in-step i d q pin =
  aCSs i d q (SN.ssHead CS.stMustReply)
    (subst (λ z → NS.csSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csSnxt i d z (Payload , input i d N2N_ChainSync) arPayload
                  ≡ just NS.csMust)
           (sym pin) (ceqCSs16 i d))

-- RUNG 2: the 12-peer BUNDLE offers what its CS SERVER offers
srvInBundleCS : (l : Link) (cl sv : Dir) → cl ≢ sv
   → (csc : SN.CScPos) (css css′ : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
     (ip : SN.InertPos) (x : Payload)
   → absCSs l sv css ─[ ev (evl (evLabel Payload (input l sv N2N_ChainSync) x)) ]─►
     absCSs l sv css′
   → IoOffers (absBundleG l cl sv csc css bfc bfs ip) (input l sv N2N_ChainSync) x
srvInBundleCS l cl sv cl≢sv csc css css′ bfc bfs ip x sStep =
    _
  , absBundle-CSs-ev l cl sv csc css bfc bfs ip
      {e₁ = CS.sendCS l sv} {qcs′ = css′} cl≢sv refl sStep

-- RUNG 3, node B on link BD: the relay's DOWN CS server; its BD bundle is node B's
-- second operand and its AB bundle refuses by LINK
srvInNodeB-BD-CS : (nb : SN.NodeStateB) (x : Payload) (css′ : SN.CSsPos)
  → absCSs linkBD hi (SN.NodeStateB.csS-BD nb)
      ─[ ev (evl (evLabel Payload (input linkBD hi N2N_ChainSync) x)) ]─►
    absCSs linkBD hi css′
  → IoOffers (absNodeB nb) (input linkBD hi N2N_ChainSync) x
srvInNodeB-BD-CS nb x css′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkBD hi N2N_ChainSync} {x}
                            (iomem-in linkBD hi N2N_ChainSync x))
      (⦀-ev-R _ _
        (proj₂ (srvInBundleCS linkBD lo hi (λ ())
                  (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) css′
                  (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb)
                  (SN.NodeStateB.inert-BD nb) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAB hi lo
             (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
             (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.inert-AB nb)
             ahlIn (λ q → linkAB≢linkBD (sym q))
             (iomem-in linkBD hi N2N_ChainSync x))))
      (noOffer→viewV _ (nodeB-drv-io-no nb (iomem-in linkBD hi N2N_ChainSync x)))

-- RUNG 3, node C on link CD: the leg-CD mirror
srvInNodeC-CD-CS : (nc : SN.NodeStateC) (x : Payload) (css′ : SN.CSsPos)
  → absCSs linkCD hi (SN.NodeStateC.csS-CD nc)
      ─[ ev (evl (evLabel Payload (input linkCD hi N2N_ChainSync) x)) ]─►
    absCSs linkCD hi css′
  → IoOffers (absNodeC nc) (input linkCD hi N2N_ChainSync) x
srvInNodeC-CD-CS nc x css′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkCD hi N2N_ChainSync} {x}
                            (iomem-in linkCD hi N2N_ChainSync x))
      (⦀-ev-R _ _
        (proj₂ (srvInBundleCS linkCD lo hi (λ ())
                  (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) css′
                  (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc)
                  (SN.NodeStateC.inert-CD nc) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAC hi lo
             (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
             (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.inert-AC nc)
             ahlIn (λ q → linkAC≢linkCD (sym q))
             (iomem-in linkCD hi N2N_ChainSync x))))
      (noOffer→viewV _ (nodeC-drv-io-no nc (iomem-in linkCD hi N2N_ChainSync x)))

-- RUNG 4, leg BD's DOWN CS server (node B): node A refuses by the banked reverse
-- pairwise fingerprint and the C/D group by `absGroupB-io-no`
srvInNodes-B-BD-CS : (s : SysState) (x : Payload) (css′ : SN.CSsPos)
  → absCSs linkBD hi (SN.NodeStateB.csS-BD (nB s))
      ─[ ev (evl (evLabel Payload (input linkBD hi N2N_ChainSync) x)) ]─►
    absCSs linkBD hi css′
  → IoOffers (absNodesOf s) (input linkBD hi N2N_ChainSync) x
srvInNodes-B-BD-CS s x css′ sStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-L _ _ (proj₂ nOff)
        (noOffer→viewV _ (absGroupB-io-no (nB s) (nC s) (nD s) iom (proj₂ nOff))))
      (noOffer→viewV _ (absNodeA-io-no-when-B (nA s) iom fpB))
  where
  iom = iomem-in linkBD hi N2N_ChainSync x
  nOff : IoOffers (absNodeB (nB s)) (input linkBD hi N2N_ChainSync) x
  nOff = srvInNodeB-BD-CS (nB s) x css′ sStep
  fpB = absNodeB-io-fp (nB s) iom (proj₂ nOff)

-- RUNG 4, leg CD's DOWN CS server (node C): the THIRD operand, so all three
-- refusals are the banked pairwise ones
srvInNodes-C-CD-CS : (s : SysState) (x : Payload) (css′ : SN.CSsPos)
  → absCSs linkCD hi (SN.NodeStateC.csS-CD (nC s))
      ─[ ev (evl (evLabel Payload (input linkCD hi N2N_ChainSync) x)) ]─►
    absCSs linkCD hi css′
  → IoOffers (absNodesOf s) (input linkCD hi N2N_ChainSync) x
srvInNodes-C-CD-CS s x css′ sStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-L _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeD-io-no-when-C (nD s) iom fpC)))
        (noOffer→viewV _ (absNodeB-io-no-when-C (nB s) iom fpC)))
      (noOffer→viewV _ (absNodeA-io-no-when-C (nA s) iom fpC))
  where
  iom = iomem-in linkCD hi N2N_ChainSync x
  nOff : IoOffers (absNodeC (nC s)) (input linkCD hi N2N_ChainSync) x
  nOff = srvInNodeC-CD-CS (nC s) x css′ sStep
  fpC = absNodeC-io-fp (nC s) iom (proj₂ nOff)

------------------------------------------------------------------------
-- §2b  (T8c-ii) TWO MORE NODES-SIDE LADDERS — the two the `cp6`/`pp0` arms need,
-- and the two the T8 gate declared UNBUILT.
--
--   (a) NODE D's OWN CS CLIENT, WRITING (`input`).  Its `ccWreq → ccAwait` row is
--       the client's request write, and a stable configuration cannot have it
--       pending.  *** THIS IS THE FIRST CLIENT-SIDE io INTRO LADDER ON THE CS AXIS
--       *** — §2's four rungs are all SERVER-fired — and it differs from them at
--       exactly two rungs: rung 1 is PAYLOAD-GATED (`ceqCSc11` tests the tuple, so
--       the ladder is `rnPayload`-specific where §2's is payload-generic), and rung
--       3/4 walk NODE D, which is the FOURTH `⦀` operand of `absNodesOf` and whose
--       own bundle pair puts the fired link FIRST (`absNodeD`, `SysStep`) — where
--       node B's puts it second.
--   (b) THE RELAY's DOWN CS SERVER, READING (`output`).  §2's ladder at the other
--       polarity, on §1c's medium half.  Rungs 2-4 are §2's with `CS.sendCS`
--       replaced by `CS.receiveCS` and `ahlIn` by `ahlOut`; every refusal is
--       io-LABEL-generic, so nothing else moves.
--
-- *** WHY BOTH, AND WHY NEITHER IS OPTIONAL. ***  `LiveDrvCSD`'s `CellFresh` has
-- THREE arms — `empty`, `draining x` and `ReqOnly` — and the `csIdle` refutation
-- needs one enabled move per arm.  `draining` is the medium's solo τ (§1, landed at
-- T6b); `empty` with the client at `ccWreq` is ladder (a); `ReqOnly` is ladder (b).
-- Narrowing `CellFresh` to drop an arm is not an escape: the client's own request
-- write ESTABLISHES the `ReqOnly` arm (`LiveDrvCSD.dnFresh-cliSend`), so the
-- invariant must admit it and stability must refute it here.
------------------------------------------------------------------------

-- (a) RUNG 1: the CS CLIENT's own io offer, at any fine position that coarsens to
-- `ccWreq` — `csCnxt` accepts the wire-send of `MsgCSRequestNext` exactly there
-- (`ceqCSc11`), and `absCSc l d q` depends on `q` only through `coarsenCSc q`.  The
-- step is returned at its EXPLICIT target `csHead CS.stCanAwait`, the fine position
-- `coarsenCSc` sends to `ccAwait`
csc-in-step : (i : Link) (d : Dir) (q : SN.CScPos)
            → coarsenCSc q ≡ NS.ccWreq
            → absCSc i d q
                ─[ ev (evl (evLabel Payload (input i d N2N_ChainSync) rnPayload)) ]─►
              absCSc i d (SN.csHead CS.stCanAwait)
csc-in-step i d q pin =
  aCSc i d q (SN.csHead CS.stCanAwait)
    (subst (λ z → NS.csCfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csCnxt i d z (Payload , input i d N2N_ChainSync) rnPayload
                  ≡ just NS.ccAwait)
           (sym pin) (ceqCSc11 i d))

-- (a) RUNG 2: the 12-peer BUNDLE offers what its CS CLIENT offers (§2's rung 2 at
-- the other peer; the eleven internal sibling refusals ride the banked lemma)
cliInBundleCS : (l : Link) (cl sv : Dir) → cl ≢ sv
   → (csc csc′ : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
     (ip : SN.InertPos) (x : Payload)
   → absCSc l cl csc ─[ ev (evl (evLabel Payload (input l cl N2N_ChainSync) x)) ]─►
     absCSc l cl csc′
   → IoOffers (absBundleG l cl sv csc css bfc bfs ip) (input l cl N2N_ChainSync) x
cliInBundleCS l cl sv cl≢sv csc csc′ css bfc bfs ip x cStep =
    _
  , absBundle-CSc-ev l cl sv csc css bfc bfs ip
      {e₁ = CS.sendCS l cl} {qcc′ = csc′} cl≢sv refl cStep

-- (a) RUNG 3, node D on link BD: its BD bundle is node D's FIRST operand (node B's
-- was its second), its CD bundle refuses by LINK, and BOTH consume drivers refuse
-- the io as a CLASS (`nodeD-drv-io-no`, which is the pair's refusal in one lemma)
cliInNodeD-BD : (nd : SN.NodeStateD) (x : Payload) (csc′ : SN.CScPos)
  → absCSc linkBD hi (SN.NodeStateD.csC-BD nd)
      ─[ ev (evl (evLabel Payload (input linkBD hi N2N_ChainSync) x)) ]─►
    absCSc linkBD hi csc′
  → IoOffers (absNodeD nd) (input linkBD hi N2N_ChainSync) x
cliInNodeD-BD nd x csc′ cStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkBD hi N2N_ChainSync} {x}
                            (iomem-in linkBD hi N2N_ChainSync x))
      (⦀-ev-L _ _
        (proj₂ (cliInBundleCS linkBD hi lo (λ ())
                  (SN.NodeStateD.csC-BD nd) csc′ (SN.NodeStateD.csS-BD nd)
                  (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd)
                  (SN.NodeStateD.inert-BD nd) x cStep))
        (noOffer→viewV _
          (absBundleG-io-no linkCD hi lo
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd)
             (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd)
             (SN.NodeStateD.inert-CD nd)
             ahlIn linkBD≢linkCD
             (iomem-in linkBD hi N2N_ChainSync x))))
      (noOffer→viewV _ (nodeD-drv-io-no nd (iomem-in linkBD hi N2N_ChainSync x)))

-- (a) RUNG 3, node D on link CD: the mirror — the CD bundle is the SECOND operand
cliInNodeD-CD : (nd : SN.NodeStateD) (x : Payload) (csc′ : SN.CScPos)
  → absCSc linkCD hi (SN.NodeStateD.csC-CD nd)
      ─[ ev (evl (evLabel Payload (input linkCD hi N2N_ChainSync) x)) ]─►
    absCSc linkCD hi csc′
  → IoOffers (absNodeD nd) (input linkCD hi N2N_ChainSync) x
cliInNodeD-CD nd x csc′ cStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {input linkCD hi N2N_ChainSync} {x}
                            (iomem-in linkCD hi N2N_ChainSync x))
      (⦀-ev-R _ _
        (proj₂ (cliInBundleCS linkCD hi lo (λ ())
                  (SN.NodeStateD.csC-CD nd) csc′ (SN.NodeStateD.csS-CD nd)
                  (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd)
                  (SN.NodeStateD.inert-CD nd) x cStep))
        (noOffer→viewV _
          (absBundleG-io-no linkBD hi lo
             (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
             (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd)
             (SN.NodeStateD.inert-BD nd)
             ahlIn (λ q → linkBD≢linkCD (sym q))
             (iomem-in linkCD hi N2N_ChainSync x))))
      (noOffer→viewV _ (nodeD-drv-io-no nd (iomem-in linkCD hi N2N_ChainSync x)))

-- (a) RUNG 4, node D as the FOURTH `⦀` operand: three nested `⦀-ev-R`s and the
-- three banked pairwise refusals against node D's own fingerprint
cliInNodes-D-BD : (s : SysState) (x : Payload) (csc′ : SN.CScPos)
  → absCSc linkBD hi (SN.NodeStateD.csC-BD (nD s))
      ─[ ev (evl (evLabel Payload (input linkBD hi N2N_ChainSync) x)) ]─►
    absCSc linkBD hi csc′
  → IoOffers (absNodesOf s) (input linkBD hi N2N_ChainSync) x
cliInNodes-D-BD s x csc′ cStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iom fpD)))
        (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iom fpD)))
      (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iom fpD))
  where
  iom = iomem-in linkBD hi N2N_ChainSync x
  nOff : IoOffers (absNodeD (nD s)) (input linkBD hi N2N_ChainSync) x
  nOff = cliInNodeD-BD (nD s) x csc′ cStep
  fpD = absNodeD-io-fp (nD s) iom (proj₂ nOff)

cliInNodes-D-CD : (s : SysState) (x : Payload) (csc′ : SN.CScPos)
  → absCSc linkCD hi (SN.NodeStateD.csC-CD (nD s))
      ─[ ev (evl (evLabel Payload (input linkCD hi N2N_ChainSync) x)) ]─►
    absCSc linkCD hi csc′
  → IoOffers (absNodesOf s) (input linkCD hi N2N_ChainSync) x
cliInNodes-D-CD s x csc′ cStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iom fpD)))
        (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iom fpD)))
      (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iom fpD))
  where
  iom = iomem-in linkCD hi N2N_ChainSync x
  nOff : IoOffers (absNodeD (nD s)) (input linkCD hi N2N_ChainSync) x
  nOff = cliInNodeD-CD (nD s) x csc′ cStep
  fpD = absNodeD-io-fp (nD s) iom (proj₂ nOff)

-- (b) RUNG 1: the CS SERVER's own io READ offer, at any fine position that coarsens
-- to `csIdle` — `csSnxt` accepts a `MsgCSRequestNext` delivery exactly there
-- (`ceqCSs01`), LENIENTLY in the tuple's first three components, which is why the
-- three are quantified here rather than fixed: that is precisely
-- `LiveChanCS.FullMsg`'s shape, so a `ReqOnly` hypothesis feeds this rung directly
css-out-step : (i : Link) (d : Dir) (q : SN.CSsPos)
               (t : Time) (md : Mode) (ln : Length)
             → coarsenCSs q ≡ NS.csIdle
             → absCSs i d q
                 ─[ ev (evl (evLabel Payload (output i d N2N_ChainSync)
                              (t , md , ln , chainSync MsgCSRequestNext))) ]─►
               absCSs i d SN.ssReqNext1
css-out-step i d q t md ln pin =
  aCSs i d q SN.ssReqNext1
    (subst (λ z → NS.csSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csSnxt i d z (Payload , output i d N2N_ChainSync)
                    (t , md , ln , chainSync MsgCSRequestNext) ≡ just NS.csAreq)
           -- the row's three LENIENT components are passed EXPLICITLY: the `subst`
           -- motive does not determine them, so a bare `ceqCSs01 i d` leaves three
           -- unsolved metas (measured)
           (sym pin) (ceqCSs01 {t} {md} {ln} i d))

-- (b) RUNG 2: §2's rung 2 at the READER's polarity — `CS.receiveCS` for
-- `CS.sendCS`, and `ιCS (CS.receiveCS l d)` IS `output l d N2N_ChainSync`
srvOutBundleCS : (l : Link) (cl sv : Dir) → cl ≢ sv
   → (csc : SN.CScPos) (css css′ : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
     (ip : SN.InertPos) (x : Payload)
   → absCSs l sv css ─[ ev (evl (evLabel Payload (output l sv N2N_ChainSync) x)) ]─►
     absCSs l sv css′
   → IoOffers (absBundleG l cl sv csc css bfc bfs ip) (output l sv N2N_ChainSync) x
srvOutBundleCS l cl sv cl≢sv csc css css′ bfc bfs ip x sStep =
    _
  , absBundle-CSs-ev l cl sv csc css bfc bfs ip
      {e₁ = CS.receiveCS l sv} {qcs′ = css′} cl≢sv refl sStep

-- (b) RUNG 3, node B on link BD: §2's rung 3 with the polarity flipped (`ahlOut`
-- for `ahlIn`, `iomem-out` for `iomem-in`)
srvOutNodeB-BD-CS : (nb : SN.NodeStateB) (x : Payload) (css′ : SN.CSsPos)
  → absCSs linkBD hi (SN.NodeStateB.csS-BD nb)
      ─[ ev (evl (evLabel Payload (output linkBD hi N2N_ChainSync) x)) ]─►
    absCSs linkBD hi css′
  → IoOffers (absNodeB nb) (output linkBD hi N2N_ChainSync) x
srvOutNodeB-BD-CS nb x css′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkBD hi N2N_ChainSync} {x}
                            (iomem-out linkBD hi N2N_ChainSync x))
      (⦀-ev-R _ _
        (proj₂ (srvOutBundleCS linkBD lo hi (λ ())
                  (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) css′
                  (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb)
                  (SN.NodeStateB.inert-BD nb) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAB hi lo
             (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
             (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.inert-AB nb)
             ahlOut (λ q → linkAB≢linkBD (sym q))
             (iomem-out linkBD hi N2N_ChainSync x))))
      (noOffer→viewV _ (nodeB-drv-io-no nb (iomem-out linkBD hi N2N_ChainSync x)))

-- (b) RUNG 3, node C on link CD: the leg-CD mirror
srvOutNodeC-CD-CS : (nc : SN.NodeStateC) (x : Payload) (css′ : SN.CSsPos)
  → absCSs linkCD hi (SN.NodeStateC.csS-CD nc)
      ─[ ev (evl (evLabel Payload (output linkCD hi N2N_ChainSync) x)) ]─►
    absCSs linkCD hi css′
  → IoOffers (absNodeC nc) (output linkCD hi N2N_ChainSync) x
srvOutNodeC-CD-CS nc x css′ sStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkCD hi N2N_ChainSync} {x}
                            (iomem-out linkCD hi N2N_ChainSync x))
      (⦀-ev-R _ _
        (proj₂ (srvOutBundleCS linkCD lo hi (λ ())
                  (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) css′
                  (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc)
                  (SN.NodeStateC.inert-CD nc) x sStep))
        (noOffer→viewV _
          (absBundleG-io-no linkAC hi lo
             (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
             (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.inert-AC nc)
             ahlOut (λ q → linkAC≢linkCD (sym q))
             (iomem-out linkCD hi N2N_ChainSync x))))
      (noOffer→viewV _ (nodeC-drv-io-no nc (iomem-out linkCD hi N2N_ChainSync x)))

-- (b) RUNG 4, leg BD's DOWN CS server (node B), reading
srvOutNodes-B-BD-CS : (s : SysState) (x : Payload) (css′ : SN.CSsPos)
  → absCSs linkBD hi (SN.NodeStateB.csS-BD (nB s))
      ─[ ev (evl (evLabel Payload (output linkBD hi N2N_ChainSync) x)) ]─►
    absCSs linkBD hi css′
  → IoOffers (absNodesOf s) (output linkBD hi N2N_ChainSync) x
srvOutNodes-B-BD-CS s x css′ sStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-L _ _ (proj₂ nOff)
        (noOffer→viewV _ (absGroupB-io-no (nB s) (nC s) (nD s) iom (proj₂ nOff))))
      (noOffer→viewV _ (absNodeA-io-no-when-B (nA s) iom fpB))
  where
  iom = iomem-out linkBD hi N2N_ChainSync x
  nOff : IoOffers (absNodeB (nB s)) (output linkBD hi N2N_ChainSync) x
  nOff = srvOutNodeB-BD-CS (nB s) x css′ sStep
  fpB = absNodeB-io-fp (nB s) iom (proj₂ nOff)

-- (b) RUNG 4, leg CD's DOWN CS server (node C), reading
srvOutNodes-C-CD-CS : (s : SysState) (x : Payload) (css′ : SN.CSsPos)
  → absCSs linkCD hi (SN.NodeStateC.csS-CD (nC s))
      ─[ ev (evl (evLabel Payload (output linkCD hi N2N_ChainSync) x)) ]─►
    absCSs linkCD hi css′
  → IoOffers (absNodesOf s) (output linkCD hi N2N_ChainSync) x
srvOutNodes-C-CD-CS s x css′ sStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-L _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeD-io-no-when-C (nD s) iom fpC)))
        (noOffer→viewV _ (absNodeB-io-no-when-C (nB s) iom fpC)))
      (noOffer→viewV _ (absNodeA-io-no-when-C (nA s) iom fpC))
  where
  iom = iomem-out linkCD hi N2N_ChainSync x
  nOff : IoOffers (absNodeC (nC s)) (output linkCD hi N2N_ChainSync) x
  nOff = srvOutNodeC-CD-CS (nC s) x css′ sStep
  fpC = absNodeC-io-fp (nC s) iom (proj₂ nOff)

------------------------------------------------------------------------
-- §3  THE LEG-LEVEL FORMS the `pp2` ladder consumes.
--
-- `LiveChanCS` §6 delivers `CellPreQ (cellCSDn l s)` at `csWar`; its two arms are
-- `empty` and `draining x`, and these three lemmas are the moves each arm enables,
-- stated at the leg's own down link.  A `csWar-⊥` is then: take the coarse pin,
-- take `CellPreQ`, dispatch on its two arms, and in each arm pair the medium's
-- move with the nodes' — the io sync of `decMed ∥⇘ ioES ⇙ absNodesOf` in the
-- `empty` arm, and the medium's solo τ in the `draining` one.
------------------------------------------------------------------------

-- the MEDIUM half at the leg's down CS cell, `empty` arm
medOfferInCS-dn : (l : TwoLegs) (s : SysState) (x : Payload)
                → broken (med s) (dnLink l) ≡ false
                → cellCSDn l s ≡ empty
                → IoOffers (decMed (med s)) (input (dnLink l) hi N2N_ChainSync) x
medOfferInCS-dn l s x ebr he = medOfferInCS (med s) (dnLink l) x ebr he

-- … and the `draining` arm
medDrainτCS-dn : (l : TwoLegs) (s : SysState) (x : Payload)
               → broken (med s) (dnLink l) ≡ false
               → cellCSDn l s ≡ draining x
               → Σ[ M ∈ NetProc ] (decMed (med s) ─[ τ ]─► M)
medDrainτCS-dn l s x ebr hd = medDrainτCS (med s) (dnLink l) x ebr hd

-- *** THE NODES HALF, OFF THE COARSE PIN. ***  the shape a `csWar-⊥` holds: the
-- leg's down CS server is at `csWar`, so the whole four-node interleave offers
-- that server's own `MsgCSAwaitReply` wire-send.  Rungs 1-4 composed, per leg.
srvInNodes-dnCS : (l : TwoLegs) (s : SysState)
                → coarsenCSs (dnCSsOf l s) ≡ NS.csWar
                → IoOffers (absNodesOf s) (input (dnLink l) hi N2N_ChainSync) arPayload
srvInNodes-dnCS legBD s pin =
  srvInNodes-B-BD-CS s arPayload (SN.ssHead CS.stMustReply)
    (css-in-step linkBD hi (SN.NodeStateB.csS-BD (nB s)) pin)
srvInNodes-dnCS legCD s pin =
  srvInNodes-C-CD-CS s arPayload (SN.ssHead CS.stMustReply)
    (css-in-step linkCD hi (SN.NodeStateC.csS-CD (nC s)) pin)

-- *** (T8c-ii) THE MEDIUM HALF AT THE READER's POLARITY. ***  §3's `medOfferInCS-dn`
-- at a FULL cell — the move the `ReqOnly` arm's refutation pairs with the server's
medOfferOutCS-dn : (l : TwoLegs) (s : SysState) (x : Payload)
                 → broken (med s) (dnLink l) ≡ false
                 → cellCSDn l s ≡ full x
                 → IoOffers (decMed (med s)) (output (dnLink l) hi N2N_ChainSync) x
medOfferOutCS-dn l s x ebr hf = medOfferOutCS (med s) (dnLink l) x ebr hf

-- *** (T8c-ii) THE NODES HALF for the `empty`-cell arm, CLIENT-fired. ***  the shape
-- a `cliWreq-⊥` holds: node D's own down-hop CS client is at `ccWreq`, so the whole
-- four-node interleave offers that client's own `MsgCSRequestNext` wire-send.
-- §2b(a)'s rungs 1-4 composed, per leg
cliInNodes-dnCS : (l : TwoLegs) (s : SysState)
                → coarsenCSc (dnCScOf l s) ≡ NS.ccWreq
                → IoOffers (absNodesOf s) (input (dnLink l) hi N2N_ChainSync) rnPayload
cliInNodes-dnCS legBD s pin =
  cliInNodes-D-BD s rnPayload (SN.csHead CS.stCanAwait)
    (csc-in-step linkBD hi (SN.NodeStateD.csC-BD (nD s)) pin)
cliInNodes-dnCS legCD s pin =
  cliInNodes-D-CD s rnPayload (SN.csHead CS.stCanAwait)
    (csc-in-step linkCD hi (SN.NodeStateD.csC-CD (nD s)) pin)

-- *** (T8c-ii) … and the NODES HALF for the `ReqOnly` arm, SERVER-fired at the
-- READER's polarity. ***  the leg's down CS server is at `csIdle`, so the whole
-- four-node interleave offers its READ of whatever request the cell holds.  §2b(b)'s
-- rungs 1-4 composed, per leg; the payload's three lenient components travel because
-- `LiveChanCS.FullMsg` quantifies exactly those three
srvOutNodes-dnCS : (l : TwoLegs) (s : SysState) (t : Time) (md : Mode) (ln : Length)
                 → coarsenCSs (dnCSsOf l s) ≡ NS.csIdle
                 → IoOffers (absNodesOf s) (output (dnLink l) hi N2N_ChainSync)
                     (t , md , ln , chainSync MsgCSRequestNext)
srvOutNodes-dnCS legBD s t md ln pin =
  srvOutNodes-B-BD-CS s (t , md , ln , chainSync MsgCSRequestNext) SN.ssReqNext1
    (css-out-step linkBD hi (SN.NodeStateB.csS-BD (nB s)) t md ln pin)
srvOutNodes-dnCS legCD s t md ln pin =
  srvOutNodes-C-CD-CS s (t , md , ln , chainSync MsgCSRequestNext) SN.ssReqNext1
    (css-out-step linkCD hi (SN.NodeStateC.csS-CD (nC s)) t md ln pin)

-- *** (T11) §2's RUNG 1 AT THE ROLLFORWARD's OWN POSITION — the `csWrf` write. ***
-- `css-in-step` is hard-wired at `csWar`/`arPayload` (the `pp2` arm's write); this is
-- the SAME rung at the position the `pp3` arm's server sits in, off the banked
-- `ceqCSs14`.  *** THIS IS THE 12-22-LINE "POSITION INSTANCE" THE T9 VERIFICATION
-- MEASURED *** ("the server-write ladder = 22 lines off the banked `ceqCSs14`, the
-- missing piece is a POSITION, not two directions") — spent here, and the
-- measurement holds
css-in-step-rfw : (i : Link) (d : Dir) (q : SN.CSsPos) (h : Header) (tp : Tip)
                → coarsenCSs q ≡ NS.csWrf (h , tp)
                → absCSs i d q
                    ─[ ev (evl (evLabel Payload (input i d N2N_ChainSync)
                                 (time₀ , FromResponder , length₀
                                 , chainSync (MsgCSRollForward h tp)))) ]─►
                  absCSs i d (SN.ssHead CS.stIdle)
css-in-step-rfw i d q h tp pin =
  aCSs i d q (SN.ssHead CS.stIdle)
    (subst (λ z → NS.csSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csSnxt i d z (Payload , input i d N2N_ChainSync)
                    (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h tp))
                  ≡ just NS.csIdle)
           (sym pin) (ceqCSs14 {h} {tp} i d))

-- … and its leg-level form: `srvInNodes-dnCS` at the `csWrf` position
srvInNodesRfw-dnCS : (l : TwoLegs) (s : SysState) (h : Header) (tp : Tip)
                   → coarsenCSs (dnCSsOf l s) ≡ NS.csWrf (h , tp)
                   → IoOffers (absNodesOf s) (input (dnLink l) hi N2N_ChainSync)
                       (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h tp))
srvInNodesRfw-dnCS legBD s h tp pin =
  srvInNodes-B-BD-CS s _ (SN.ssHead CS.stIdle)
    (css-in-step-rfw linkBD hi (SN.NodeStateB.csS-BD (nB s)) h tp pin)
srvInNodesRfw-dnCS legCD s h tp pin =
  srvInNodes-C-CD-CS s _ (SN.ssHead CS.stIdle)
    (css-in-step-rfw linkCD hi (SN.NodeStateC.csS-CD (nC s)) h tp pin)

------------------------------------------------------------------------
-- §2c  (T11) *** THE FOURTH AND LAST CHAINSYNC DIRECTION — node D's CS CLIENT
-- READING. ***
--
-- The ChainSync io inventory before this section: §2's `srvIn*` (the relay's
-- server WRITING), §2b(a)'s `cliIn*` (node D's client WRITING) and §2b(b)'s
-- `srvOut*` (the relay's server READING).  This is the one that was missing, and
-- it is T9's `cp1`-leaf item (ii) half: **the reader is node D's client**, which
-- every full-cell case of the `pp3` arm's leaf turns on (a responder payload in
-- the down CS cell is refuted by its OWN reader's delivery).
--
-- *** IT IS TARGET- AND PAYLOAD-GENERIC ON PURPOSE, so ONE ladder serves all four
-- responder reads *** (`MsgCSAwaitReply` → `ccMust`, `MsgCSRollForward ht` →
-- `ccArf ht`, `MsgCSRollBackward pt` → `ccArb pt`, and the two intersect
-- replies): rung 1 is left to the CALLER, which supplies whichever `ceqCSc*` row
-- its own case names — exactly as §2b(b)'s reader ladder takes `css′` and a step.
-- The (T11) BlockFetch measurement applies here too: a missing POLARITY on an
-- axis that already has the other one costs rungs 2-4 and no new table fact.
------------------------------------------------------------------------

-- RUNG 2: the 12-peer BUNDLE offers what its CS CLIENT offers, at the READER's
-- polarity — §2b(a)'s rung 2 with `CS.receiveCS` for `CS.sendCS`, and
-- `ιCS (CS.receiveCS l d)` IS `output l d N2N_ChainSync`
cliOutBundleCS : (l : Link) (cl sv : Dir) → cl ≢ sv
   → (csc csc′ : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
     (ip : SN.InertPos) (x : Payload)
   → absCSc l cl csc ─[ ev (evl (evLabel Payload (output l cl N2N_ChainSync) x)) ]─►
     absCSc l cl csc′
   → IoOffers (absBundleG l cl sv csc css bfc bfs ip) (output l cl N2N_ChainSync) x
cliOutBundleCS l cl sv cl≢sv csc csc′ css bfc bfs ip x cStep =
    _
  , absBundle-CSc-ev l cl sv csc css bfc bfs ip
      {e₁ = CS.receiveCS l cl} {qcc′ = csc′} cl≢sv refl cStep

-- RUNG 3, node D on link BD: §2b(a)'s rung 3 with the polarity flipped (`ahlOut`
-- for `ahlIn`, `iomem-out` for `iomem-in`) and nothing else
cliOutNodeD-BD-CS : (nd : SN.NodeStateD) (x : Payload) (csc′ : SN.CScPos)
  → absCSc linkBD hi (SN.NodeStateD.csC-BD nd)
      ─[ ev (evl (evLabel Payload (output linkBD hi N2N_ChainSync) x)) ]─►
    absCSc linkBD hi csc′
  → IoOffers (absNodeD nd) (output linkBD hi N2N_ChainSync) x
cliOutNodeD-BD-CS nd x csc′ cStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkBD hi N2N_ChainSync} {x}
                            (iomem-out linkBD hi N2N_ChainSync x))
      (⦀-ev-L _ _
        (proj₂ (cliOutBundleCS linkBD hi lo (λ ())
                  (SN.NodeStateD.csC-BD nd) csc′ (SN.NodeStateD.csS-BD nd)
                  (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd)
                  (SN.NodeStateD.inert-BD nd) x cStep))
        (noOffer→viewV _
          (absBundleG-io-no linkCD hi lo
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd)
             (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd)
             (SN.NodeStateD.inert-CD nd)
             ahlOut linkBD≢linkCD
             (iomem-out linkBD hi N2N_ChainSync x))))
      (noOffer→viewV _ (nodeD-drv-io-no nd (iomem-out linkBD hi N2N_ChainSync x)))

-- RUNG 3, node D on link CD: the mirror — the CD bundle is the SECOND operand
cliOutNodeD-CD-CS : (nd : SN.NodeStateD) (x : Payload) (csc′ : SN.CScPos)
  → absCSc linkCD hi (SN.NodeStateD.csC-CD nd)
      ─[ ev (evl (evLabel Payload (output linkCD hi N2N_ChainSync) x)) ]─►
    absCSc linkCD hi csc′
  → IoOffers (absNodeD nd) (output linkCD hi N2N_ChainSync) x
cliOutNodeD-CD-CS nd x csc′ cStep =
    _
  , ∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {Payload} {output linkCD hi N2N_ChainSync} {x}
                            (iomem-out linkCD hi N2N_ChainSync x))
      (⦀-ev-R _ _
        (proj₂ (cliOutBundleCS linkCD hi lo (λ ())
                  (SN.NodeStateD.csC-CD nd) csc′ (SN.NodeStateD.csS-CD nd)
                  (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd)
                  (SN.NodeStateD.inert-CD nd) x cStep))
        (noOffer→viewV _
          (absBundleG-io-no linkBD hi lo
             (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
             (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd)
             (SN.NodeStateD.inert-BD nd)
             ahlOut (λ q → linkBD≢linkCD (sym q))
             (iomem-out linkCD hi N2N_ChainSync x))))
      (noOffer→viewV _ (nodeD-drv-io-no nd (iomem-out linkCD hi N2N_ChainSync x)))

-- RUNG 4, node D as the FOURTH `⦀` operand: three nested `⦀-ev-R`s and the three
-- banked pairwise refusals against node D's own fingerprint
cliOutNodes-D-BD-CS : (s : SysState) (x : Payload) (csc′ : SN.CScPos)
  → absCSc linkBD hi (SN.NodeStateD.csC-BD (nD s))
      ─[ ev (evl (evLabel Payload (output linkBD hi N2N_ChainSync) x)) ]─►
    absCSc linkBD hi csc′
  → IoOffers (absNodesOf s) (output linkBD hi N2N_ChainSync) x
cliOutNodes-D-BD-CS s x csc′ cStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iom fpD)))
        (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iom fpD)))
      (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iom fpD))
  where
  iom = iomem-out linkBD hi N2N_ChainSync x
  nOff : IoOffers (absNodeD (nD s)) (output linkBD hi N2N_ChainSync) x
  nOff = cliOutNodeD-BD-CS (nD s) x csc′ cStep
  fpD = absNodeD-io-fp (nD s) iom (proj₂ nOff)

cliOutNodes-D-CD-CS : (s : SysState) (x : Payload) (csc′ : SN.CScPos)
  → absCSc linkCD hi (SN.NodeStateD.csC-CD (nD s))
      ─[ ev (evl (evLabel Payload (output linkCD hi N2N_ChainSync) x)) ]─►
    absCSc linkCD hi csc′
  → IoOffers (absNodesOf s) (output linkCD hi N2N_ChainSync) x
cliOutNodes-D-CD-CS s x csc′ cStep =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ (proj₂ nOff)
          (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iom fpD)))
        (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iom fpD)))
      (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iom fpD))
  where
  iom = iomem-out linkCD hi N2N_ChainSync x
  nOff : IoOffers (absNodeD (nD s)) (output linkCD hi N2N_ChainSync) x
  nOff = cliOutNodeD-CD-CS (nD s) x csc′ cStep
  fpD = absNodeD-io-fp (nD s) iom (proj₂ nOff)

-- … and the LEG-LEVEL form, §3's shape: the reader is node D's own client on the
-- leg's DOWN link, and the caller supplies its step
cliOutNodes-dnCS : (l : TwoLegs) (s : SysState) (x : Payload) (csc′ : SN.CScPos)
  → absCSc (dnLink l) hi (dnCScOf l s)
      ─[ ev (evl (evLabel Payload (output (dnLink l) hi N2N_ChainSync) x)) ]─►
    absCSc (dnLink l) hi csc′
  → IoOffers (absNodesOf s) (output (dnLink l) hi N2N_ChainSync) x
cliOutNodes-dnCS legBD s x csc′ cStep = cliOutNodes-D-BD-CS s x csc′ cStep
cliOutNodes-dnCS legCD s x csc′ cStep = cliOutNodes-D-CD-CS s x csc′ cStep

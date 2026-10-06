{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — S0, AT THE SYSTEM LEVEL: ANNOUNCEMENT SAFETY
-- OF THE WHOLE N-NODE LEIOS-PROTOTYPE NETWORK running `nodeLogicL` at
-- every node over the PROTOTYPE peer bundle `PeersP.nodeBundleP`.
--
-- The Leios sibling of `Parametric.AnnounceSafeCopy` +
-- `Parametric.AnnounceSafeConcrete`, assembled in exactly their order:
-- alphabets → three `Sep` conditions → `Covers`/`HideCov` → the node
-- logic → the peer bundles → the node → the system → `noTick` → `Safe`
-- → the theorem → the medium transport.  Every leaf below the system
-- fold is imported, not re-proved:
--
--   * the node logic — `AnnounceThreadsL.wf-nodeLogicL` (threads) over
--     `AnnounceStoreL.wf-storesL` (the five stores), at `nodeG`;
--   * the BlockFetch peers — `BlockProvenancePeers.wf-BFclientA`/
--     `wf-BFserverA`, and the KA/CS/TS channel refutations `hKA`/`hCS`/
--     `hTS`, all verbatim;
--   * the medium — `BlockProvenanceMedium.wf-CopySpecBreakableA`, and
--     `AnnounceSafeConcrete.Medium.copy⊑T-netLink` for the transport.
--
-- TWO ALPHABET DECISIONS, both forced:
--
--   * `peersPG` is `BlockProvenanceBF.peersG` MINUS the prototype
--     announce channel.  `peersG` already excludes the OLD announce
--     channel `apiLN … sendLNBlockAnnouncement` because the LN server
--     peer relays rather than originates it; the prototype peer
--     (`LeiosNotifyP.agda:242-247`, renamed by `PeersP.ιLNP`) does the
--     same on `apiLP … lnpSendBlockAnnouncement`, so that channel is a
--     peer RELY too and must leave the peers' guarantee.  It is written
--     as a PRODUCT with `NotAnnP`, so `peersPG ⊆ peersG` is `proj₁` and
--     every BlockFetch fact transfers by `wf-mono-G` for free.  This is
--     waiver, not vacuity: the announcement really is fired by the peer,
--     and `sep-apiL` discharges it because `apiES` SYNCHRONISES it —
--     the same route `AnnounceSafeCopy.sep-api` takes for `apiLN`.
--   * `logicGL` is `BlockProvenanceNode.nodeG` shrunk to exclude
--     `output`, not `(threadsGL ∪α storeG)` shrunk: `wf-nodeLogicL` is
--     stated at `nodeG`, so the union form would cost a second trip
--     through `nodeG⊆`'s 33 clauses for nothing.  `nodeG` is `⊤` on
--     every channel but `apiBF … recvBFBlock`, which makes all nine
--     `Sep` clauses on this side either `tt , tt` or an absurd pattern.
--
-- WHAT IT SAYS.  Every trace of the whole network — N nodes, each
-- running the fifteen Linear-Leios thread families against its five
-- stores and the twelve prototype peers, over the concrete per-link
-- multiplexer with the io channels hidden — is a trace of
-- `AnnounceSpecT`: no node ever announces, on EITHER announce channel,
-- a ranking block whose announced EB hash no `env … envForge` produced.
-- WHAT IT DOES NOT SAY: nothing about liveness, nothing about which
-- node forged (the forged set is global — see `AnnounceSafe`'s header),
-- and nothing about divergence (`⊑T` is a safety order).
--
-- THE ONE PREMISE is `AnnounceSafeConcrete.LinkCfgWf` — every link's
-- configuration non-empty and duplicate-free — carried by the
-- copy→concrete medium transport alone, and DECIDED at the shipped
-- Leios line at the bottom of this file.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.AnnounceSystemL where

open import Level using (0ℓ)
open import Data.Bool using (if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product.Properties using (≡-dec)
open import Function using (case_of_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; from-yes)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (AnyTypes; ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Parametric.Topology using (Topology; opposite)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Net as N
import Cardano_network.Data as D
import CSP.Operators as O
import Cardano_network.NetCommon as NC
import Cardano_network.ApiAlphabet as AA
import Cardano_network.Parametric.NodeLogic as NL
import Cardano_network.Parametric.Assembly as Asm
import Cardano_network.Parametric.AnnounceSafe as AS
import Cardano_network.Parametric.AnnounceSafeCarrier as ASCar
import Cardano_network.Parametric.AnnounceSafeLeaves as ASL
import Cardano_network.Parametric.AnnounceSafeCopy as ASCopy
import Cardano_network.Parametric.AnnounceSafeConcrete as ASCon
import Cardano_network.Parametric.BlockProvenance as BP
import Cardano_network.Parametric.BlockProvenanceNode as BPN
import Cardano_network.Parametric.BlockProvenanceBF as BPBF
import Cardano_network.Parametric.BlockProvenancePeers as BPP
import Cardano_network.Parametric.BlockProvenanceCopy as BPC
import Cardano_network.Parametric.BlockProvenanceMedium as BPM
import Cardano_network.Parametric.BlockProvenanceSafe as BPS
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.Leios.AnnounceThreadsL as ATL
import Cardano_network.Parametric.Leios.PeersP as PP
import Cardano_network.Parametric.Leios.LeiosInstanceL as LIL
open import Cardano_network.Base using (Dir; IDs; DecEq-Dir; DecEq-IDs)

-- the system level of S0, parametric in the same five arguments `AnnounceThreadsL`
-- takes, so every leaf fact below is literally that module's
module Generic
  (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p}))
  (voterOf : Topology.Node t → Params.VoterId p) where

  open Params p using (Block; linkConfig)
  open import Cardano_network.Base
    using ( N2N_KeepAlive; N2N_ChainSync; N2N_BlockFetch
          ; N2N_TxSubmission; N2N_LeiosNotify; N2N_LeiosFetch )
  open N p
    using ( Link; Net_Api; Net_Api-≟; output; apiBF; apiLP
          ; sendBFBlock; recvBFBlock; lnpSendBlockAnnouncement )
  open D p using (Payload)
  open NC p using (ioES; CopySpecBreakableA; NetworkLinkBreakableA)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (EventSet; ⦀⁺; ⦀Fin⁺; Skip)
  open Topology t using (Node; numNodes-1; endpointsOf)
  open import Cardano_network.Parametric.Node p t apiES
    using (nodeWith; bundleAtWith; linkBundlesWith; systemOfWithNode)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using (Alpha; NoRet; NoRet-Par; NoRet-⦀; NoRet-loop0)
  open import Semantics.Failures
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (_⊑T_; ⊑T-trans; ⊑T-refl)
  open PP p using (nodeBundleP; clientPeerP; serverPeerP
                  ; ιLNP; ιLNP⁻¹; ιLNP-linv; ιLFP; ιLFP⁻¹; ιLFP-linv)
  open NL.Generic p t apiES using (storeES)
  open NLL.Generic p lp t apiES voterOf using (nodeLogicL; st₀)
  open AS.Generic p t apiES using (AnnounceSpecT)
  open ASCar.Generic p t apiES using (Safe; safe→⊑T)
  open ASL.Generic p t apiES using (AnnSync)
  open ASCopy.Generic p t apiES using (BFSync; notOutput)
  open BP.Generic p t apiES
  open BPN.Generic p t apiES using (nodeG)
  open BPBF.Generic p t apiES using (peersG)
  open BPP.Generic p t apiES
    using (wf-BFclientA; wf-BFserverA; hKA; hCS; hTS; module VKA; module VCS; module VTS)
  open BPC.Generic p t apiES using (medG)
  open BPM.Generic p t apiES using (wf-CopySpecBreakableA)
  open BPS.Generic p t apiES using (Covers; wf→safe; NoRet-ParR; NoRet-Hide; NoRet-⦀Fin⁺)
  open ATL.Generic p lp t apiES voterOf using (wf-nodeLogicL)

  ------------------------------------------------------------------------
  -- The alphabets
  ------------------------------------------------------------------------

  -- NOT the prototype announce channel: the LeiosNotify producer peer relays an
  -- announcement it was handed, so `apiLP … lnpSendBlockAnnouncement` is a peer RELY
  -- exactly as `apiLN … sendLNBlockAnnouncement` already is in `peersG`
  NotAnnP : Alpha
  NotAnnP (_ , apiLP _ _ lnpSendBlockAnnouncement) _ = ⊥
  NotAnnP _                                        _ = ⊤

  -- THE PROTOTYPE PEERS' ALPHABET: the stock one minus that rely.  A product, so
  -- `peersPG ⊆ peersG` is `proj₁` and every BlockFetch fact transfers by `wf-mono-G`.
  peersPG : Alpha
  peersPG at a = peersG at a × NotAnnP at a

  -- THE LEIOS NODE LOGIC'S ALPHABET: `nodeG` (what `wf-nodeLogicL` is stated at) minus
  -- `output`, which is the peers' rely from the medium and which the logic never performs
  logicGL : Alpha
  logicGL at a = nodeG at a × notOutput at a

  -- the whole system's: every block-carrying label is in it (`covers-sysGL`)
  sysGL : Alpha
  sysGL = medG ∪α (peersPG ∪α logicGL)

  ------------------------------------------------------------------------
  -- The prototype peer bundle
  ------------------------------------------------------------------------

  -- the three stock channel refutations, read at the shrunk alphabet
  hKAP : ∀ bt b at a → VKA.ι-vis-inv bt b ≡ just (at , a) → peersPG bt b
       → ∀ {blk} → ¬ Carries bt b blk
  hKAP bt b at a eq g = hKA bt b at a eq (proj₁ g)

  -- likewise ChainSync
  hCSP : ∀ bt b at a → VCS.ι-vis-inv bt b ≡ just (at , a) → peersPG bt b
       → ∀ {blk} → ¬ Carries bt b blk
  hCSP bt b at a eq g = hCS bt b at a eq (proj₁ g)

  -- likewise TxSubmission — which also covers `PeersR.TSserverRA`, the reply-reporting
  -- requester `nodeBundleP` puts in the TxSubmission server slot: it is a `renameMap`
  -- along the SAME `ιTS`, and `wf-renameMap-vacuous` is parametric in the peer
  hTSP : ∀ bt b at a → VTS.ι-vis-inv bt b ≡ just (at , a) → peersPG bt b
       → ∀ {blk} → ¬ Carries bt b blk
  hTSP bt b at a eq g = hTS bt b at a eq (proj₁ g)

  -- the prototype LeiosNotify renaming, as a vacuity instance
  module VLNP = Vacuous ιLNP ιLNP⁻¹ ιLNP-linv

  -- the prototype LeiosFetch renaming, as a vacuity instance
  module VLFP = Vacuous ιLFP ιLFP⁻¹ ιLFP-linv

  -- the ONE block-carrying channel in the prototype LeiosNotify image is the
  -- announcement, and that is outside `peersPG` — the producer peer RELIES on it
  hLNP : ∀ bt b at a → VLNP.ι-vis-inv bt b ≡ just (at , a) → peersPG bt b
       → ∀ {blk} → ¬ Carries bt b blk
  hLNP _ _ _ _ eq _ c-stGet   = case eq of λ ()
  hLNP _ _ _ _ eq _ c-stGetAt = case eq of λ ()
  hLNP _ _ _ _ eq _ c-stPut   = case eq of λ ()
  hLNP _ _ _ _ eq _ c-sendBF  = case eq of λ ()
  hLNP _ _ _ _ eq _ c-recvBF  = case eq of λ ()
  hLNP _ _ _ _ eq _ c-ann     = case eq of λ ()
  hLNP _ _ _ _ _  g c-annP    = proj₂ g
  hLNP _ _ _ _ eq _ c-input   = case eq of λ ()
  hLNP _ _ _ _ eq _ c-output  = case eq of λ ()

  -- likewise the prototype LeiosFetch image: `ιLFP` maps `apiLP` too, so the
  -- announcement is refuted by the alphabet and every other shape by the renaming
  hLFP : ∀ bt b at a → VLFP.ι-vis-inv bt b ≡ just (at , a) → peersPG bt b
       → ∀ {blk} → ¬ Carries bt b blk
  hLFP _ _ _ _ eq _ c-stGet   = case eq of λ ()
  hLFP _ _ _ _ eq _ c-stGetAt = case eq of λ ()
  hLFP _ _ _ _ eq _ c-stPut   = case eq of λ ()
  hLFP _ _ _ _ eq _ c-sendBF  = case eq of λ ()
  hLFP _ _ _ _ eq _ c-recvBF  = case eq of λ ()
  hLFP _ _ _ _ eq _ c-ann     = case eq of λ ()
  hLFP _ _ _ _ _  g c-annP    = proj₂ g
  hLFP _ _ _ _ eq _ c-input   = case eq of λ ()
  hLFP _ _ _ _ eq _ c-output  = case eq of λ ()

  -- the prototype client peer of each protocol, on `peersPG`
  wf-clientPeerP : ∀ {ms} (l : Link) (d : Dir) (id : IDs)
                 → Wf peersPG ms (clientPeerP l d id)
  wf-clientPeerP l d N2N_KeepAlive    = VKA.wf-renameMap-vacuous hKAP
  wf-clientPeerP l d N2N_ChainSync    = VCS.wf-renameMap-vacuous hCSP
  wf-clientPeerP l d N2N_BlockFetch   = wf-mono-G (λ _ _ → proj₁) (wf-BFclientA l d)
  wf-clientPeerP l d N2N_TxSubmission = VTS.wf-renameMap-vacuous hTSP
  wf-clientPeerP l d N2N_LeiosNotify  = VLNP.wf-renameMap-vacuous hLNP
  wf-clientPeerP l d N2N_LeiosFetch   = VLFP.wf-renameMap-vacuous hLFP

  -- … and the prototype server peer (the two prototype producers, the reply-reporting
  -- TxSubmission requester, the stock producers elsewhere)
  wf-serverPeerP : ∀ {ms} (l : Link) (d : Dir) (id : IDs)
                 → Wf peersPG ms (serverPeerP l d id)
  wf-serverPeerP l d N2N_KeepAlive    = VKA.wf-renameMap-vacuous hKAP
  wf-serverPeerP l d N2N_ChainSync    = VCS.wf-renameMap-vacuous hCSP
  wf-serverPeerP l d N2N_BlockFetch   = wf-mono-G (λ _ _ → proj₁) (wf-BFserverA l d)
  wf-serverPeerP l d N2N_TxSubmission = VTS.wf-renameMap-vacuous hTSP
  wf-serverPeerP l d N2N_LeiosNotify  = VLNP.wf-renameMap-vacuous hLNP
  wf-serverPeerP l d N2N_LeiosFetch   = VLFP.wf-renameMap-vacuous hLFP

  -- one configured instance's slot in `nodeBundleP` (the `with` mirrors the bundle's
  -- own dispatch)
  wf-slotP : ∀ {ms} (l : Link) (cl sv d : Dir) (id : IDs)
           → Wf peersPG ms (if ⌊ d ≟ cl ⌋ then clientPeerP l d id
                            else if ⌊ d ≟ sv ⌋ then serverPeerP l d id else Skip)
  wf-slotP l cl sv d id with d ≟ cl
  ... | yes _ = wf-clientPeerP l d id
  ... | no _ with d ≟ sv
  ...   | yes _ = wf-serverPeerP l d id
  ...   | no _  = wf-Skip

  -- THE PROTOTYPE PEER BUNDLE of one node on one link, over the configured instances
  wf-nodeBundleP : ∀ {ms} (l : Link) (cl sv : Dir) → Wf peersPG ms (nodeBundleP l cl sv)
  wf-nodeBundleP l cl sv = wf-⦀⋆ _ (linkConfig l) (λ { (d , id) → wf-slotP l cl sv d id })

  -- one incident endpoint's bundle: server peers on the opposite direction
  wf-bundleAtP : ∀ {ms} (ld : Link × Dir) → Wf peersPG ms (bundleAtWith nodeBundleP ld)
  wf-bundleAtP (l , d) = wf-nodeBundleP l d (opposite d)

  -- every incident endpoint's bundle, interleaved in `endpointsOf`'s order
  wf-linkBundlesP : ∀ {ms} n → Wf peersPG ms (linkBundlesWith nodeBundleP n)
  wf-linkBundlesP n = go (proj₁ (endpointsOf n)) (proj₂ (endpointsOf n))
    where
    go : ∀ {ms} x xs
       → Wf peersPG ms (⦀⁺ (bundleAtWith nodeBundleP x) (map (bundleAtWith nodeBundleP) xs))
    go x []       = wf-bundleAtP x
    go x (y ∷ ys) = wf-⦀ (wf-bundleAtP x) (go y ys)

  ------------------------------------------------------------------------
  -- The node logic, and the two `Sep` conditions that do not mention `apiES`
  ------------------------------------------------------------------------

  -- THE LEIOS NODE LOGIC from empty stores, shrunk from `nodeG` to `logicGL`.  The
  -- store invariant is `All _ []`, which is `All.[]` — no premise.  The five store
  -- components are passed EXPLICITLY: `nodeLogicL` destructures its state argument, so
  -- unifying `st₀` against five metas blocks on them (five unsolved constraints).
  wf-nodeLogicGL : ∀ {ms} n → Wf logicGL ms (nodeLogicL n st₀)
  wf-nodeLogicGL n =
    wf-mono-G (λ _ _ → proj₁)
      (wf-nodeLogicL n {held = []} {es = []} {bs = []} {ts = []} {vs = [] , []} All.[])

  -- medium vs nodes at `ioES`: `medG` is total outside `ioES`, and every non-io
  -- block-carrying label is in the peers' alphabet or the logic's
  sep-ioL : Sep ioES medG (peersPG ∪α logicGL)
  sep-ioL =
      (λ { c-stGet  _ _ → inj₂ (tt , tt) ; c-stPut   _ _ → inj₂ (tt , tt)
         ; c-stGetAt _ _ → inj₂ (tt , tt)
         ; c-sendBF _ _ → inj₂ (tt , tt) ; c-recvBF  _ _ → inj₁ (tt , tt)
         ; c-ann    _ _ → inj₂ (tt , tt) ; c-annP    _ _ → inj₂ (tt , tt)
         ; c-input  () _                 ; c-output  _ ¬m → ⊥-elim (¬m tt) })
    , (λ { c-stGet  _ _ → tt ; c-stPut _ _ → tt ; c-stGetAt _ _ → tt
         ; c-sendBF _ _ → tt ; c-recvBF _ _ → tt
         ; c-ann    _ _ → tt ; c-annP   _ _ → tt
         ; c-input  _ ¬m → ⊥-elim (¬m tt) ; c-output _ _ → tt })

  -- THE COVERAGE CONDITION: every one of the nine block-carrying shapes is guaranteed
  -- by some side of the top-level composite — no rely is left
  covers-sysGL : Covers sysGL
  covers-sysGL c-stGet   = inj₁ tt
  covers-sysGL c-stGetAt = inj₁ tt
  covers-sysGL c-stPut   = inj₁ tt
  covers-sysGL c-sendBF  = inj₁ tt
  covers-sysGL c-recvBF  = inj₁ tt
  covers-sysGL c-ann     = inj₁ tt
  covers-sysGL c-annP    = inj₁ tt
  covers-sysGL c-input   = inj₂ (inj₁ (tt , tt))
  covers-sysGL c-output  = inj₁ tt

  -- …so in particular every hidden io label is (`wf-Hide`'s side condition)
  hideCov-sysGL : HideCov ioES sysGL
  hideCov-sysGL c _ = covers-sysGL c

  ------------------------------------------------------------------------
  -- `noTick`
  ------------------------------------------------------------------------

  -- the Leios node logic: the threads sit LEFT of `∥⇘ storeES ⇙` and `forgeL` heads them
  noRet-nodeLogicL : ∀ n → NoRet (nodeLogicL n st₀)
  noRet-nodeLogicL n = NoRet-Par storeES (λ _ _ → tt) (NoRet-⦀ NoRet-loop0)

  -- the whole network over ANY medium and ANY peer bundle: hide, medium-right, node
  -- fold head, logic-right.  Nothing here inspects the bundle builder — only the shape
  -- `nodeWith mk n lg = linkBundlesWith mk n ∥⇘ apiES ⇙ lg`, which holds for every `mk`.
  noRet-systemL : ∀ (mk : Link → Dir → Dir → Proc) med (lg : Node → Proc)
                → (∀ n → NoRet (lg n)) → NoRet (systemOfWithNode (nodeWith mk) med lg)
  noRet-systemL mk med lg h =
    NoRet-Hide ioES (NoRet-ParR ioES (NoRet-⦀Fin⁺ numNodes-1 (NoRet-ParR apiES (h fzero))))

  ------------------------------------------------------------------------
  -- The assembly, under the two `apiES` facts
  ------------------------------------------------------------------------

  -- THE STATEMENT of S0 at the system level, over the CONCRETE per-link multiplexer,
  -- named so the headline below can quote it without re-opening `Node`
  AnnounceSafeLT : Set₁
  AnnounceSafeLT =
    AnnounceSpecT ⊑T
      systemOfWithNode (nodeWith nodeBundleP) NetworkLinkBreakableA
                       (λ n → nodeLogicL n st₀)

  module Assembly (annSync : AnnSync apiES) (bfSync : BFSync apiES) where

    -- peers vs logic at `apiES`: the four block-carrying api labels are synchronised;
    -- `output` is in neither alphabet; `store`/`input` are in both.  The `c-annP` arm
    -- is THE WAIVER — the prototype announcement is fired by the LeiosNotify producer
    -- peer, but only ever in lockstep with `lnServerLoopL`, so the peer is never asked
    -- to guarantee it and the LOGIC's gate is what `Covers` spends.
    sep-apiL : Sep apiES peersPG logicGL
    sep-apiL =
        (λ { c-stGet   _ _ → tt , tt ; c-stPut _ _ → tt , tt
           ; c-stGetAt _ _ → tt , tt
           ; c-sendBF  (() , _) _
           ; c-recvBF  _ ¬m → ⊥-elim (¬m (proj₂ (bfSync _)))
           ; c-ann     (() , _) _
           ; c-annP    (_ , ()) _
           ; c-input   _ _ → tt , tt
           ; c-output  (() , _) _ })
      , (λ { c-stGet   _ _ → tt , tt ; c-stPut _ _ → tt , tt
           ; c-stGetAt _ _ → tt , tt
           ; c-sendBF  _ ¬m → ⊥-elim (¬m (proj₁ (bfSync _)))
           ; c-recvBF  (() , _) _
           ; c-ann     _ ¬m → ⊥-elim (¬m (annSync annLN))
           ; c-annP    _ ¬m → ⊥-elim (¬m (annSync annLP))
           ; c-input   _ _ → tt , tt
           ; c-output  (_ , ()) _ })

    -- ONE LEIOS NODE: the twelve prototype peers against the Linear-Leios logic
    wf-nodeL : ∀ {ms} n
             → Wf (peersPG ∪α logicGL) ms (nodeWith nodeBundleP n (nodeLogicL n st₀))
    wf-nodeL n = wf-Par apiES sep-apiL (wf-linkBundlesP n) (wf-nodeLogicGL n)

    -- THE WHOLE LEIOS NETWORK over the copy medium, at every forged set
    wf-systemLCopy : ∀ {ms} → Wf sysGL ms
                       (systemOfWithNode (nodeWith nodeBundleP) CopySpecBreakableA
                                         (λ n → nodeLogicL n st₀))
    wf-systemLCopy =
      wf-Hide ioES hideCov-sysGL hideKeep-ioES
        (wf-Par ioES sep-ioL wf-CopySpecBreakableA (wf-⦀Fin⁺ numNodes-1 wf-nodeL))

    -- every state of the copy-medium Leios system is `Wf` on a covering alphabet and
    -- never ticks, hence `Safe`
    safe-systemLCopy : Safe []
                         (systemOfWithNode (nodeWith nodeBundleP) CopySpecBreakableA
                                           (λ n → nodeLogicL n st₀))
    safe-systemLCopy =
      wf→safe covers-sysGL
        (noRet-systemL nodeBundleP CopySpecBreakableA _ noRet-nodeLogicL)
        wf-systemLCopy

    -- S0 over the COPY medium: announcement safety of the whole Leios network
    annSafeLT-copy : AnnounceSpecT ⊑T
                       systemOfWithNode (nodeWith nodeBundleP) CopySpecBreakableA
                                        (λ n → nodeLogicL n st₀)
    annSafeLT-copy = safe→⊑T safe-systemLCopy

    -- S0 over the CONCRETE per-link multiplexer: the copy-medium theorem transported
    -- by `copy⊑T-netLink` (node-logic-free AND bundle-free) through the
    -- builder-parametric `systemN-monoWith-T`, the nodes held fixed at `⊑T-refl`
    annSafeLT : ASCon.LinkCfgWf p → AnnounceSafeLT
    annSafeLT hyp =
      ⊑T-trans annSafeLT-copy
        (Asm.Generic.systemN-monoWith-T p t apiES (nodeWith nodeBundleP)
          NetworkLinkBreakableA CopySpecBreakableA
          (λ n → nodeWith nodeBundleP n (nodeLogicL n st₀)) (λ n → nodeLogicL n st₀)
          (ASCon.Medium.copy⊑T-netLink p hyp) (λ n → ⊑T-refl _))

------------------------------------------------------------------------
-- THE THEOREM, at the shared api alphabet
------------------------------------------------------------------------

-- S0 AT THE SYSTEM LEVEL, for every parameter set, Leios parameters, topology and
-- voter map, under a well-formed link configuration: the whole N-node Leios-prototype
-- network running `nodeLogicL` from empty stores never announces a ranking block whose
-- announced EB hash was not forged.  Both `Assembly` premises are discharged at the
-- shared `ApiAlphabet.apiES`, exactly as `AnnounceSafeCopy`'s headline does.
annSafeLT : ∀ (p : Params) (lp : LeiosP.LeiosParams p) (t : Topology p)
              (voterOf : Topology.Node t → Params.VoterId p)
          → ASCon.LinkCfgWf p
          → Generic.AnnounceSafeLT p lp t (AA.apiES p) voterOf
annSafeLT p lp t voterOf =
  Generic.Assembly.annSafeLT p lp t (AA.apiES p) voterOf
    (ASL.annSync-apiES p t)
    (λ {l} {d} → ASCopy.bfSync-apiES p t {l} {d})

------------------------------------------------------------------------
-- The shipped Leios line: premise-free
------------------------------------------------------------------------

-- decidable equality of a configuration entry (the same construction
-- `AnnounceSafeInstances` uses to decide `LinkCfgWf` for the three Praos topologies)
entry-≟ : DecidableEquality (Dir × IDs)
entry-≟ = ≡-dec (DecEq._≟_ DecEq-Dir) (DecEq._≟_ DecEq-IDs)

open import Data.List.Relation.Unary.Unique.DecPropositional entry-≟ using (unique?)

-- every link of the Leios line carries the same literal twelve-entry configuration,
-- so the one premise is DECIDED rather than proved
leiosLCfgWf : ASCon.LinkCfgWf LIL.leiosLParams
leiosLCfgWf _ = (λ ()) , from-yes (unique? LIL.leiosLCfg)

open import Semantics.Failures
  {E = N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams)}
  {I = ExtI (N.Net_Api LIL.leiosLParams (D.Payload LIL.leiosLParams))} using (_⊑T_)

-- S0 AT THE SYSTEM LEVEL FOR THE SHIPPED LEIOS LINE, PREMISE-FREE, stated against the
-- shipped witness `LeiosInstanceL.leiosSystemL` itself: the three-node line, every node
-- running the whole Linear-Leios logic from empty stores behind the twelve prototype
-- peers, over the concrete per-link multiplexer with io hidden, never announces a
-- ranking block whose announced EB hash no forge produced.
leiosAnnSafeLT :
  AS.Generic.AnnounceSpecT LIL.leiosLParams LIL.leiosLLine (AA.apiES LIL.leiosLParams)
    ⊑T LIL.leiosSystemL
leiosAnnSafeLT =
  annSafeLT LIL.leiosLParams LIL.leiosLP LIL.leiosLLine (λ n → n) leiosLCfgWf

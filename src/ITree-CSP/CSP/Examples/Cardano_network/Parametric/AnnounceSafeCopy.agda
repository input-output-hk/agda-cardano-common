{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — ANNOUNCEMENT SAFETY OF THE N-NODE NETWORK
-- over the copy medium: `AnnounceSafeTWith CopySpecBreakableA`.
--
-- THE ASSEMBLY.  Every leaf is `Wf` on its own guarantee alphabet — its
-- block-carrying labels minus its relies — and `wf-Par` composes them at
-- each synchronisation set, discharging each rely with the other side's
-- guarantee AT THE SAME STEP.  The four alphabets and the three `Sep`
-- side conditions:
--
--   store (`storeG`) ∥⇘ storeES ⇙ threads (`threadsG`)   — relies `stPut`/`stGet`, both in `storeES`
--   peers (`peersG`) ∥⇘ apiES ⇙ logic  (`logicG`)        — relies `recvBFBlock`/announce, both in `apiES`
--   medium (`medG`)  ∥⇘ ioES ⇙  nodes                     — relies `input`/`output`, both in `ioES`
--
-- `logicG` is `threadsG ∪α storeG` SHRUNK to exclude `output`: `Sep apiES`
-- fails otherwise, `output` being block-carrying, outside `apiES`, and
-- the peers' rely (`BlockProvenancePeers`'s header).  The shrink is an
-- intersection, not a re-enumeration, so `wf-mono-G` costs `proj₁`.
--
-- At the top the union `sysG = medG ∪α (peersG ∪α logicG)` CONTAINS EVERY
-- BLOCK-CARRYING LABEL — no rely is left — which is `Covers sysG`, the
-- one side condition of `BlockProvenanceSafe.wf→safe`.  `noTick` is
-- `NoRet` of the composite, inherited from the head node's mint thread.
--
-- `apiES` is a module parameter, so the two facts about it the `Sep`
-- needs — it synchronises the announcement and both BlockFetch block
-- channels — are parameters of `Assembly`, discharged at the bottom for
-- the shared `ApiAlphabet.apiES`, as `AnnounceSafeLeaves.annSync-apiES`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceSafeCopy where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Unary.All as All
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; opposite)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.NetCommon as NC
import CSP.Examples.Cardano_network.ApiAlphabet as AA
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeCarrier as ASC
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeLeaves as ASL
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceNode as BPN
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceBF as BPBF
import CSP.Examples.Cardano_network.Parametric.BlockProvenancePeers as BPP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceCopy as BPC
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceMedium as BPM
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceSafe as BPS

-- the same three parameters as every other `Parametric.Announce*`/`BlockProvenance*`
-- module, so every leaf fact below is literally theirs
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block)
  open N p using (Link; Net_Api; Net_Api-≟; output; apiBF; sendBFBlock; recvBFBlock)
  open D p using (Payload)
  open import CSP.Examples.Cardano_network.Base using (Dir)
  open NC p using (ioES; CopySpecBreakableA)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (EventSet; ⦀⁺; ⦀Fin⁺)
  open Topology t using (Node; numNodes-1; endpointsOf)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES
    using (node; bundleAt; linkBundles; systemOfWith; systemOfCopy)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using (Alpha; NoRet; NoRet-Par; NoRet-⦀; NoRet-loop0)
  open NL.Generic p t apiES using (nodeLogic; storeES)
  open AS.Generic p t apiES using (AnnounceSafeTWith)
  open ASC.Generic p t apiES using (Safe; safe→announceSafeT)
  open ASL.Generic p t apiES using (AnnSync)
  open BP.Generic p t apiES
  open BPN.Generic p t apiES using (threadsG; storeG; StoreInv; wf-threads; wf-blockStore)
  open BPBF.Generic p t apiES using (peersG)
  open BPP.Generic p t apiES using (wf-nodeBundle)
  open BPC.Generic p t apiES using (medG)
  open BPM.Generic p t apiES using (wf-CopySpecBreakableA)
  open BPS.Generic p t apiES using (Covers; wf→safe; NoRet-ParR; NoRet-Hide; NoRet-⦀Fin⁺)

  ------------------------------------------------------------------------
  -- The alphabets
  ------------------------------------------------------------------------

  -- everything but the wire's `output`: the peers' rely, which the node logic never
  -- performs and must therefore not claim to guarantee
  notOutput : Alpha
  notOutput (_ , output _ _ _) _ = ⊥
  notOutput _                  _ = ⊤

  -- THE NODE LOGIC'S ALPHABET: the store's and the threads' together, minus `output`.
  -- An intersection, so the shrink from the union is a projection.
  logicG : Alpha
  logicG at a = (threadsG ∪α storeG) at a × notOutput at a

  -- the whole system's: every block-carrying label is in it (`covers-sysG`)
  sysG : Alpha
  sysG = medG ∪α (peersG ∪α logicG)

  -- `apiES` synchronises both BlockFetch block channels — the peers' rely
  -- (`recvBFBlock`) and the threads' guarantee (`sendBFBlock`) — as it does the
  -- announcement (`AnnounceSafeLeaves.AnnSync`)
  BFSync : EventSet → Set
  BFSync A = ∀ {l : Link} {d : Dir} (b : Block)
           → EventSet.mem A (Block , apiBF l d sendBFBlock) b
           × EventSet.mem A (Block , apiBF l d recvBFBlock) b

  ------------------------------------------------------------------------
  -- The side conditions that do not mention `apiES`
  ------------------------------------------------------------------------

  -- store vs threads at `storeES`: the two relies are both `store` labels, hence
  -- synchronised; every other block-carrying label is in both alphabets or in neither
  sep-store : Sep storeES threadsG storeG
  sep-store =
      (λ { c-stGet  () _        ; c-stPut  _ ¬m → ⊥-elim (¬m tt)
         ; c-sendBF _ _ → tt    ; c-recvBF () _
         ; c-ann    _ _ → tt    ; c-input  _ _ → tt ; c-output _ _ → tt })
    , (λ { c-stGet  _ ¬m → ⊥-elim (¬m tt) ; c-stPut  () _
         ; c-sendBF _ _ → tt    ; c-recvBF () _
         ; c-ann    _ _ → tt    ; c-input  _ _ → tt ; c-output _ _ → tt })

  -- medium vs nodes at `ioES`: `medG` is total outside `ioES`, and every non-io
  -- block-carrying label is in the peers' alphabet or the logic's
  sep-io : Sep ioES medG (peersG ∪α logicG)
  sep-io =
      (λ { c-stGet  _ _ → inj₂ (inj₂ tt , tt) ; c-stPut  _ _ → inj₂ (inj₁ tt , tt)
         ; c-sendBF _ _ → inj₂ (inj₁ tt , tt) ; c-recvBF _ _ → inj₁ tt
         ; c-ann    _ _ → inj₂ (inj₁ tt , tt)
         ; c-input  () _                      ; c-output _ ¬m → ⊥-elim (¬m tt) })
    , (λ { c-stGet  _ _ → tt ; c-stPut  _ _ → tt ; c-sendBF _ _ → tt ; c-recvBF _ _ → tt
         ; c-ann    _ _ → tt ; c-input  _ ¬m → ⊥-elim (¬m tt) ; c-output _ _ → tt })

  -- THE COVERAGE CONDITION: every one of the seven block-carrying shapes is guaranteed
  -- by some side of the top-level composite — no rely is left
  covers-sysG : Covers sysG
  covers-sysG c-stGet  = inj₁ tt
  covers-sysG c-stPut  = inj₁ tt
  covers-sysG c-sendBF = inj₁ tt
  covers-sysG c-recvBF = inj₁ tt
  covers-sysG c-ann    = inj₁ tt
  covers-sysG c-input  = inj₂ (inj₁ tt)
  covers-sysG c-output = inj₁ tt

  -- …so in particular every hidden io label is (`wf-Hide`'s side condition)
  hideCov-sysG : HideCov ioES sysG
  hideCov-sysG c _ = covers-sysG c

  ------------------------------------------------------------------------
  -- The node logic and the peer bundles
  ------------------------------------------------------------------------

  -- THE NODE LOGIC on `logicG`: store and threads composed at `storeES`, then shrunk
  wf-nodeLogic : ∀ {ms} n {held} → StoreInv ms held → Wf logicG ms (nodeLogic n held)
  wf-nodeLogic n inv =
    wf-mono-G (λ _ _ → proj₁) (wf-Par storeES sep-store (wf-threads n) (wf-blockStore n inv))

  -- one incident endpoint's bundle: `Node.bundleAt` puts the server peers on the
  -- opposite direction
  wf-bundleAt : ∀ {ms} (ld : Link × Dir) → Wf peersG ms (bundleAt ld)
  wf-bundleAt (l , d) = wf-nodeBundle l d (opposite d)

  -- every incident endpoint's bundle, interleaved in `endpointsOf`'s order
  wf-linkBundles : ∀ {ms} n → Wf peersG ms (linkBundles n)
  wf-linkBundles n = go (proj₁ (endpointsOf n)) (proj₂ (endpointsOf n))
    where
    go : ∀ {ms} x xs → Wf peersG ms (⦀⁺ (bundleAt x) (map bundleAt xs))
    go x []       = wf-bundleAt x
    go x (y ∷ ys) = wf-⦀ (wf-bundleAt x) (go y ys)

  ------------------------------------------------------------------------
  -- `noTick`: the system never terminates, because its head node's mint thread is a
  -- forever loop and every operator on the way up terminates only if that operand does
  ------------------------------------------------------------------------

  -- the node logic: the threads sit LEFT of `∥⇘ storeES ⇙`, the mint thread heads them
  noRet-nodeLogic : ∀ n held → NoRet (nodeLogic n held)
  noRet-nodeLogic n held = NoRet-Par storeES (λ _ _ → tt) (NoRet-⦀ NoRet-loop0)

  -- the whole network over ANY medium: hide, medium-right, node fold head, logic-right
  noRet-system : ∀ med lg → (∀ n → NoRet (lg n)) → NoRet (systemOfWith med lg)
  noRet-system med lg h =
    NoRet-Hide ioES (NoRet-ParR ioES (NoRet-⦀Fin⁺ numNodes-1 (NoRet-ParR apiES (h fzero))))

  ------------------------------------------------------------------------
  -- The assembly, under the two `apiES` facts
  ------------------------------------------------------------------------

  module Assembly (annSync : AnnSync apiES) (bfSync : BFSync apiES) where

    -- peers vs logic at `apiES`: the three block-carrying api labels are synchronised;
    -- `output` is in neither alphabet (the shrink); `store`/`input` are in both
    sep-api : Sep apiES peersG logicG
    sep-api =
        (λ { c-stGet  _ _  → inj₂ tt , tt ; c-stPut _ _ → inj₁ tt , tt
           ; c-sendBF () _
           ; c-recvBF _ ¬m → ⊥-elim (¬m (proj₂ (bfSync _)))
           ; c-ann    () _
           ; c-input  _ _  → inj₁ tt , tt ; c-output () _ })
      , (λ { c-stGet  _ _  → tt ; c-stPut _ _ → tt
           ; c-sendBF _ ¬m → ⊥-elim (¬m (proj₁ (bfSync _)))
           ; c-recvBF _ ¬m → ⊥-elim (¬m (proj₂ (bfSync _)))
           ; c-ann    _ ¬m → ⊥-elim (¬m (annSync _))
           ; c-input  _ _  → tt ; c-output (_ , ()) _ })

    -- ONE NODE, its store initially empty
    wf-node : ∀ {ms} n → Wf (peersG ∪α logicG) ms (node n (nodeLogic n []))
    wf-node n = wf-Par apiES sep-api (wf-linkBundles n) (wf-nodeLogic n All.[])

    -- THE WHOLE NETWORK over the copy medium, at every minted set
    wf-systemOfCopy : ∀ {ms} → Wf sysG ms (systemOfCopy (λ n → nodeLogic n []))
    wf-systemOfCopy =
      wf-Hide ioES hideCov-sysG hideKeep-ioES
        (wf-Par ioES sep-io wf-CopySpecBreakableA (wf-⦀Fin⁺ numNodes-1 wf-node))

    -- every state of the copy-medium system is `Wf` on a covering alphabet and never
    -- ticks, hence `Safe`
    safe-systemOfCopy : Safe [] (systemOfCopy (λ n → nodeLogic n []))
    safe-systemOfCopy =
      wf→safe covers-sysG
        (noRet-system CopySpecBreakableA _ (λ n → noRet-nodeLogic n []))
        wf-systemOfCopy

    -- THE THEOREM: announcement safety of the N-node network over the copy medium
    announceSafeT-copy : AnnounceSafeTWith CopySpecBreakableA
    announceSafeT-copy = safe→announceSafeT CopySpecBreakableA safe-systemOfCopy

------------------------------------------------------------------------
-- The shared api alphabet meets both `Assembly` premises
------------------------------------------------------------------------

-- `apiSet` answers `⊤` on every `apiBF` channel
bfSync-apiES : ∀ (p : Params) (t : Topology p) → Generic.BFSync p t (AA.apiES p) (AA.apiES p)
bfSync-apiES p t _ = tt , tt

-- THE HEADLINE, for every parameter set and topology, at the shared api alphabet.
-- (The two premises are passed under explicit hidden binders: `apiSet` reduces to `⊤`
-- before the link and direction are unified, which would leave them unsolved.)
announceSafeT-copy : ∀ (p : Params) (t : Topology p)
                   → AS.Generic.AnnounceSafeTWith p t (AA.apiES p) (NC.CopySpecBreakableA p)
announceSafeT-copy p t =
  Generic.Assembly.announceSafeT-copy p t (AA.apiES p)
    (λ {l} {d} → ASL.annSync-apiES p t {l} {d})
    (λ {l} {d} → bfSync-apiES p t {l} {d})

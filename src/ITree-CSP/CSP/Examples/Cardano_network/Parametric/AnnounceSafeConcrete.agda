{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — ANNOUNCEMENT SAFETY OF THE N-NODE NETWORK
-- over the CONCRETE per-link multiplexer: `AnnounceSafeT`, i.e.
--
--   AnnounceSpecT ⊑T systemOf (λ n → nodeLogic n [])
--
-- which is `Parametric.Node.systemOf` — the primary object of the
-- development — and not the abstract copy medium the invariant was
-- proved over (`AnnounceSafeCopy.announceSafeT-copy`).
--
-- THE TRANSPORT.  `systemOfWith med lg = (med ∥⇘ ioES ⇙ nodes) ∖ ioES`
-- puts the medium in the LEFT operand, so the copy-medium theorem
-- carries to the concrete medium by one `⊑T` fact about the media,
--
--   CopySpecBreakableA ⊑T NetworkLinkBreakableA
--
-- lifted by `AnnounceSafe.announceSafeT-from-nodes` (= `Hide-mono-⊑ᵀ`
-- over `∥-mono-⊑T`/`⦀Fin⁺-mono-⊑ᵀ`, all unconditional) and closed by
-- `⊑T-trans`.  ORIENTATION: `⊑T-trans : Spec ⊑T Copy → Copy ⊑T Net →
-- Spec ⊑T Net` needs the copy medium BELOW the concrete one, i.e. the
-- concrete medium's traces INSIDE the copy medium's.  That is the
-- `NetworkLinkBreakableA ≈DR CopySpecBreakableA` equivalence read
-- BACKWARDS: `drbisim-sym`, then `drbisim→⊑F`, whose `⊑T` half is
-- `proj₁` (`⊑F = ⊑T × ⊇F`, `Semantics.Failures`).
--
-- THE PREMISE.  `MediumEquivA.netLinkBreakable≈DR` carries the two
-- honest hypotheses of the per-link equivalence — every link has a
-- non-empty, duplicate-free configuration — and so does the theorem
-- here (`LinkCfgWf`).  Accepted by the owner (ledger, Decision 2): the
-- premise-free alternative is the same invariant over a four-buffer
-- pipeline per link.  `AnnounceSafeInstances` discharges it for the
-- three shipped topologies by a decision procedure.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceSafeConcrete where

open import Data.List using ([])
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (_×_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Process_Trees using (ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.NetCommon as NC
import CSP.Examples.Cardano_network.ApiAlphabet as AA
import CSP.Examples.Cardano_network.MediumEquivA as ME
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeCopy as ASC

-- a well-formed link configuration: every link is configured with at least one
-- mini-protocol instance, and no instance twice — `netLinkBreakable≈DR`'s premise
LinkCfgWf : Params → Set
LinkCfgWf p = ∀ l → Params.linkConfig p l ≢ [] × Unique (Params.linkConfig p l)

------------------------------------------------------------------------
-- The medium step — `Params` only, no topology
------------------------------------------------------------------------

module Medium (p : Params) where

  open N p using (Net_Api)
  open D p using (Payload)
  open NC p using (CopySpecBreakableA; NetworkLinkBreakableA)
  open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (_⊑T_)
  open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (drbisim-sym)
  open import Semantics.DRImpliesFD {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (drbisim→⊑F)

  -- the concrete medium's traces are the copy medium's: the BACKWARD reading of
  -- `NetworkLinkBreakableA ≈DR CopySpecBreakableA`, at its trace half
  copy⊑T-netLink : LinkCfgWf p → CopySpecBreakableA ⊑T NetworkLinkBreakableA
  copy⊑T-netLink hyp = proj₁ (drbisim→⊑F (drbisim-sym (ME.netLinkBreakable≈DR p hyp)))

------------------------------------------------------------------------
-- The lift — any topology, any api alphabet
------------------------------------------------------------------------

module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open N p using (Net_Api)
  open D p using (Payload)
  open NC p using (CopySpecBreakableA; NetworkLinkBreakableA)
  open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (⊑T-refl)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES using (node)
  open NL.Generic p t apiES using (nodeLogic)
  open AS.Generic p t apiES using (AnnounceSafeTWith; AnnounceSafeT; announceSafeT-from-nodes)
  open Medium p

  -- announcement safety over the copy medium transports to the concrete medium:
  -- the medium refines at `⊑T`, the nodes are held fixed
  transport : LinkCfgWf p → AnnounceSafeTWith CopySpecBreakableA → AnnounceSafeT
  transport hyp copy =
    announceSafeT-from-nodes NetworkLinkBreakableA CopySpecBreakableA
      (λ n → node n (nodeLogic n [])) (copy⊑T-netLink hyp) (λ n → ⊑T-refl _) copy

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

-- announcement safety of the N-node network over the CONCRETE per-link multiplexer,
-- for every parameter set and topology, at the shared api alphabet, under a
-- well-formed link configuration
announceSafeT : ∀ (p : Params) (t : Topology p) → LinkCfgWf p
              → AS.Generic.AnnounceSafeT p t (AA.apiES p)
announceSafeT p t hyp = Generic.transport p t (AA.apiES p) hyp (ASC.announceSafeT-copy p t)

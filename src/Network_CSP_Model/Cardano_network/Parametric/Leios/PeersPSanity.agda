{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — TYPECHECKING WITNESS that `Leios.PeersP`'s
-- `nodeBundleP` plugs into `Parametric.Node`'s builder slot exactly where
-- `NetworkPar.nodeBundle` and `Leios.PeersR.nodeBundleR` do, plus the ONE
-- non-vacuity probe the campaign needs from the new peers: the prototype
-- LeiosFetch producer really does REPORT the request it received.
--
-- It proves no property about the protocol; it certifies that Task 4 can
-- build the prototype system as `systemOfWithNode (nodeWith nodeBundleP)
-- med lg` with NO edit to `Parametric/Node.agda`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Leios.PeersPSanity where

open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (PTree; ExtI; AnyTypes; ContinueType; react)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; lo; FromInitiator)
open import CSP.Examples.Cardano_network.Parametric.LineInstance using (lineParams; line)
open Params lineParams using (EBHash; LSlot; time₀; length₀)
open import CSP.Examples.Cardano_network.Net lineParams
  using (Link; Net_Api; Net_Api-≟; lfpReqBlockRequest)
open import CSP.Examples.Cardano_network.Data lineParams
  using (Payload; leiosFetchP; MsgLFPBlockRequest; DecEq-EBPoint)
open import CSP.Examples.Cardano_network.NetCommon lineParams
  using (NetworkLinkBreakableA)
open import CSP.Examples.Cardano_network.ApiAlphabet lineParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node lineParams line apiES
  using (Proc; bundleAtWith; nodeWith; systemOfWithNode)
open import CSP.Examples.Cardano_network.Parametric.Leios.PeersP lineParams
  using (nodeBundleP)
import CSP.Examples.Cardano_network.LeiosFetchP lineParams as LFP

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Skip)
import CSP.Operators {E = LFP.LFPEv} LFP.LFPEv-≟ as LFPOps

-- the prototype bundle of one incident endpoint, the counterpart of `Node.bundleAt`
lineBundleAtP : Link × Dir → Proc
lineBundleAtP = bundleAtWith nodeBundleP

-- the whole line network built over the prototype bundles — the shape Task 4
-- instantiates with `nodeLogicL` in place of the trivial `Skip` logic
lineSystemP : Proc
lineSystemP = systemOfWithNode (nodeWith nodeBundleP) NetworkLinkBreakableA (λ _ → Skip)

-- the visible-offer map of a process whose head node is a `react`; the everywhere-
-- `nothing` map otherwise.  Used only by the probe below.
lfpVis : ∀ {R : Set} → PTree LFP.LFPEv (ExtI LFP.LFPEv) R
       → (at : AnyTypes LFP.LFPEv)
       → ContinueType at (Maybe (PTree LFP.LFPEv (ExtI LFP.LFPEv) R))
lfpVis P with PTree.force P
... | react v _ = v
... | _         = λ { (_ , _) _ → nothing }

-- NON-VACUITY: at `stIdle` the prototype LeiosFetch producer answers a
-- `MsgLFPBlockRequest q` off the wire with the api report `lfpReqBlockRequest ! q`
-- BEFORE moving to `stBlock`.  It FAILS if the reporting `Output` is ever dropped —
-- so it certifies that `nodeBundleP` really does expose the requested POINT to
-- `ebServeLoop`, which is what Task 4's `ebServeLoop` and Task 9's S1 both depend on.
lfpP-reports-request : (q : EBHash × LSlot) →
  lfpVis (LFP.serverStepP fzero lo LFP.stIdle) (_ , LFP.receiveLFP fzero lo)
         (time₀ , FromInitiator , length₀ , leiosFetchP (MsgLFPBlockRequest q))
  ≡ just (LFPOps.Output ⦃ DecEq-EBPoint ⦄ (LFP.apiLPev fzero lo lfpReqBlockRequest) q
            (LFPOps.Ret (inj₁ LFP.stBlock)))
lfpP-reports-request q = refl

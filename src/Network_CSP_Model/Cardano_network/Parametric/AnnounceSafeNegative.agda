{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE NEGATIVE CONTROL for announcement
-- safety: the forge guard is LOAD-BEARING.
--
-- WHY THIS MODULE EXISTS.  `Parametric.AnnounceSafeConcrete.announceSafeT`
-- proves `AnnounceSpecT ⊑T systemOf (λ n → nodeLogic n [])` for every
-- `Params` and every topology: the network never announces an EB hash
-- that no forge produced.  Two things could make such a theorem worthless,
-- and BOTH have already happened once in this campaign:
--
--   (a) the specification forbids nothing — pinned shut by
--       `Parametric.AnnounceContent` (`badTraceRefused` /
--       `goodTraceAllowed`);
--   (b) the announcement is unreachable, so the property holds
--       vacuously — pinned shut by `Parametric.RelayLive`
--       (`announce-fires`).
--
-- This module closes a third gap: is the guard the implementation relies
-- on actually DOING anything?  `NodeLogic.acceptForge` keeps a forged RB
-- only when `announcedEB b ≡ (ebHash <$> me)`.  Delete that one guard
-- (`AnnounceBadLogic.acceptForgeBad`, changing NOTHING else) and the
-- property FAILS — machine-checked below.  So the theorem is not true
-- for incidental reasons: it is true because of that guard.
--
-- WHICH LEVEL — READ THIS BEFORE QUOTING THE RESULT.  The refutation is
-- at NODE LEVEL, over `node nA (nodeLogicBad nA [])`, NOT at system level
-- over `systemOfWith med (λ n → nodeLogicBad n [])`.  It is the same
-- level `Parametric.RelayLive.announce-fires` reaches, and for the same
-- reason: the bad trace it spends comes from
-- `Parametric.AnnounceBadTrace.bad-announce-fires`, whose run is over one
-- node.  A SYSTEM-LEVEL refutation is NOT established here and must not
-- be inferred from what is: `systemOfWith` hides `ioES` and interleaves
-- the other two nodes, so a system-level bad trace has to be built
-- separately (the `MsgLNRequestNext` that opens the round must come out
-- of the medium, driven by the far node's `lnClientLoop`, across two
-- hidden cells).  What IS established is that the broken node, taken on
-- its own, violates the very specification the network is proved to
-- satisfy.
--
-- WHAT THE REFUTATION SPENDS.  Two independent halves:
--
--   * the IMPLEMENTATION half — `AnnounceBadTrace.bad-announce-fires`:
--     the broken node has the trace ⟨ill-announced forge, LN request, get,
--     announce⟩;
--   * the SPECIFICATION half — `noForge` below: that same trace is NOT a
--     trace of `AnnounceSpecT`, because the forge carries `nothing` as its
--     EB and so leaves the forged set empty, while the announcement
--     announces the EB hash `true`.
--
-- The specification half is `AnnounceContent.badTraceRefused` stretched
-- from one event to four: the same idiom (direct nested matching on
-- `sVis`/`sTau`/`sSil`, `refl` forcing the offer-map equations and `()`
-- where an offer map is definitionally `nothing`), with one extra lemma,
-- `backEdge`, absorbing the `sil` the loop emits between visible events.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceSafeNegative where

open import Level using (0ℓ)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function.Base using (case_of_)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.Parametric.LeiosInstance
  using (leiosParams; leiosLine)
open import CSP.Examples.Cardano_network.Net leiosParams using (Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data leiosParams using (Payload)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node leiosParams leiosLine apiES
  using (Proc)
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
open AS.Generic leiosParams leiosLine apiES
  using (AnnounceSpecT; Forged; announceOffer)
open import CSP.Examples.Cardano_network.Parametric.AnnounceBadTrace
  using (badNode; evForge; evReq; evGet; evAnn; bad-announce-fires)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Ret; pchoice; iter; iter-bind; _>>=_)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)

------------------------------------------------------------------------
-- The two states `AnnounceSpecT` alternates between
--
-- `AnnounceSpecT = loop (λ ms → pchoice (announceOffer ms)) []`, and `loop`
-- is `iter` over the state-threading step below.  Naming the two states
-- lets the lemmas be stated one visible event at a time instead of as one
-- seven-deep nest of patterns.
------------------------------------------------------------------------

-- the tree type the spec's `loop` iterates over
Tree : Set → Set₁
Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

-- `loop`'s state-threading continuation: hand the new forged set back to `iter`
κ : Forged → Tree (Forged ⊎ ⊤ {0ℓ})
κ ms = Ret (inj₁ ms)

-- the `iter` step `AnnounceSpecT`'s `loop` is built from
StepT : Forged → Tree (Forged ⊎ ⊤ {0ℓ})
StepT ms = pchoice (announceOffer ms) >>= κ

-- the spec's MENU state at forged set `ms`: a pure-visible `react` whose τ-part is
-- `∅t`, so it has no silent move at all
AT : Forged → Proc
AT ms = iter StepT ms

-- the spec's LOOP-BACK state, reached by any visible event that left the forged set
-- `ms`: a `sil` node whose only move is the τ back to `AT ms`
ST : Forged → Proc
ST ms = iter-bind (Ret ms >>= κ) StepT

-- the spec IS the menu at the empty forged set (a computation, as in `AnnounceSafe`)
specT≡AT : AnnounceSpecT ≡ AT []
specT≡AT = refl

------------------------------------------------------------------------
-- The specification half: the bad trace is refused
------------------------------------------------------------------------

-- from the loop-back edge the ONLY move is the `sil` back to the menu, so any run of
-- a NON-EMPTY trace from `ST ms` is a run of that trace from `AT ms`
backEdge : ∀ {ms e s q} → ST ms ⟹⟨ e ∷ s ⟩ q → Σ[ q′ ∈ Proc ] (AT ms ⟹⟨ e ∷ s ⟩ q′)
backEdge (⟹-τ (sSil refl) rest) = _ , rest
backEdge (⟹-τ (sTau eq _) _)    = case eq of λ ()
backEdge (⟹-ev (sRet eq) _)     = case eq of λ ()
backEdge (⟹-ev (sVis eq _) _)   = case eq of λ ()

-- THE GATE.  With nothing forged, the announcement of `header (just true)` is not
-- offered: `announceOK [] (header (just true))` computes to `false`, so the offer map
-- is definitionally `nothing`.  The menu has no τ either, hence three clauses.
noAnn : ∀ {q} → ¬ (AT [] ⟹⟨ evAnn ∷ [] ⟩ q)
noAnn (⟹-τ (sSil eq) _) = case eq of λ ()
noAnn (⟹-τ (sTau refl ()) _)
noAnn (⟹-ev (sVis refl ()) _)

-- the `get` event is on no gated channel, so the spec offers it freely and the forged
-- set is unchanged — which leaves the announcement still refused
noGet : ∀ {q} → ¬ (AT [] ⟹⟨ evGet ∷ evAnn ∷ [] ⟩ q)
noGet (⟹-τ (sSil eq) _) = case eq of λ ()
noGet (⟹-τ (sTau refl ()) _)
noGet (⟹-ev (sVis refl refl) rest) = noAnn (proj₂ (backEdge {ms = []} rest))

-- likewise the LeiosNotify request off the wire: free, and the forged set is unchanged
noReq : ∀ {q} → ¬ (AT [] ⟹⟨ evReq ∷ evGet ∷ evAnn ∷ [] ⟩ q)
noReq (⟹-τ (sSil eq) _) = case eq of λ ()
noReq (⟹-τ (sTau refl ()) _)
noReq (⟹-ev (sVis refl refl) rest) = noGet (proj₂ (backEdge {ms = []} rest))

-- THE WHOLE BAD TRACE IS REFUSED.  The forge IS on the gated channel, but it carries
-- `nothing` as its EB — `announceOffer ms (_ , env _ _ envForge) (nothing , _) =
-- just (Ret ms)` — so it grows the forged set by NOTHING and the announcement three
-- events later is still refused.
noForge : ∀ {q} → ¬ (AT [] ⟹⟨ evForge ∷ evReq ∷ evGet ∷ evAnn ∷ [] ⟩ q)
noForge (⟹-τ (sSil eq) _) = case eq of λ ()
noForge (⟹-τ (sTau refl ()) _)
noForge (⟹-ev (sVis refl refl) rest) = noReq (proj₂ (backEdge {ms = []} rest))

------------------------------------------------------------------------
-- THE NEGATIVE CONTROL
------------------------------------------------------------------------

-- the NODE-LEVEL announcement-safety property, over the BROKEN logic: exactly
-- `AnnounceSafe.AnnounceSafeTWith`'s specification and order, but over one node
-- running `nodeLogicBad` instead of over `systemOfWith med (λ n → nodeLogic n [])`
AnnounceSafeT-node-Bad : Set₁
AnnounceSafeT-node-Bad = AnnounceSpecT ⊑T badNode

-- THE REFUTATION: deleting `NodeLogic.acceptForge`'s announcement guard BREAKS
-- announcement safety.  The broken node has a trace the specification forbids, so the
-- trace refinement cannot hold.  Together with `AnnounceSafeConcrete.announceSafeT`
-- (which does hold, for the unbroken logic, at every `Params` and topology) this shows
-- the shipped theorem is not vacuous and the forge guard is load-bearing.
--
-- LEVEL: node, not system — see the module header.  This does NOT by itself refute
-- `AnnounceSafe.AnnounceSafeTWith med` for the broken logic.
announceSafeT-node-FAILS : ¬ AnnounceSafeT-node-Bad
announceSafeT-node-FAILS h = noForge (proj₂ (h _ bad-announce-fires))

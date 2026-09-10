{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE LEVEL-MATCHED NEGATIVE CONTROL for
-- announcement safety: the good node and the broken node, side by side,
-- over ONE predicate at ONE alphabet.
--
-- WHY THIS MODULE EXISTS.  The campaign's two announcement-safety results
-- sit at different levels.  `Parametric.AnnounceSafeConcrete.announceSafeT`
-- proves the good logic safe at SYSTEM level, while
-- `Parametric.AnnounceSafeNegative.announceSafeT-node-FAILS` refutes the
-- property for the broken logic (`AnnounceBadLogic.nodeLogicBad`, the
-- shipped logic with the mint guard deleted and nothing else changed) only
-- at NODE level.  A sceptic can therefore ask whether it is COMPOSITION,
-- rather than the mint guard, that makes the good side safe: the two
-- statements never meet.
--
-- This module makes them meet.  Both halves below are stated at node
-- level, about the same shape of process — one node of the concrete Leios
-- line with its store initially empty — under the same predicate `Wf`, at
-- the same guarantee alphabet `peersG ∪α logicG`, and at the same initial
-- minted set `[]`.  The only difference between the two sides is which
-- relay logic the node runs.  That symmetry is the whole point: nothing
-- about the composition changes between the positive and the negative
-- half, so the mint guard is the only thing left that can explain the
-- difference.
--
-- WHAT `Wf` MEANS.  `BlockProvenance.Wf G ms M` is the assume-guarantee
-- carrier: at every minted set `ms′ ⊇ ms`, `M` GUARANTEES that every
-- label of the alphabet `G` it can perform carries only well-announced
-- blocks, and — GIVEN that the label it just performed was itself
-- well-announced (the rely, which appears as the `OK s′ a` ARGUMENT of
-- `stepW`, not as a global hypothesis) — every successor is again
-- well-formed.  Because the rely is an argument rather than an assumption
-- about the environment, `Wf` is not vacuous: a process that emits a
-- badly-announced block on one of its own guarantee channels cannot
-- satisfy it, whatever it was handed.
--
-- WHAT `wf→gate` BUYS.  `Wf` on its own is a carrier, not a readable
-- property.  `BlockProvenance.wf→gate` spends it at the announce channel:
-- given that the announcement is in the guarantee alphabet (`AnnIn`, the
-- one side condition, discharged in one line below), `Wf G ms M` yields
-- `Gated ms M` — "every announcement `M` can make next announces an EB
-- hash already in `ms`".  That is the announcement gate itself, so the
-- positive half is spent, not merely stated.
--
-- WHY `Wf` AND NOT `⊑T`.  The obvious level-matched alternative — a node
-- level trace refinement `AnnounceSpecT ⊑T node n (nodeLogic n [])` — is
-- FALSE for the good node and cannot be rescued by a rely hypothesis: the
-- node's BlockFetch client peer accepts an arbitrary `MsgBlock b` off the
-- wire (`BlockProvenanceBF`), so any hypothesis strong enough to make the
-- refinement provable ("this node never receives or emits a badly
-- announced block") is itself false for the good node, and an implication
-- with a false premise is vacuously true — hence equally provable for the
-- BROKEN node, which would destroy the control.  `Wf` avoids the trap
-- precisely because its rely is per-step and per-label rather than a
-- global quantification over the node's wire input.
--
-- WHAT THIS MODULE DOES NOT CLAIM.  Nothing here is a system-level
-- statement.  The positive half is `AnnounceSafeCopy.Assembly.wf-node`
-- specialised to the Leios line; the negative half spends the first two
-- steps of `AnnounceBadTrace` and one further `stGet`.  System-level
-- announcement safety remains `AnnounceSafeConcrete.announceSafeT`, and no
-- system-level refutation for the broken logic is established anywhere.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceControlNode where

open import Level using (0ℓ)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl)

open import Process_Trees using (ExtI)

open import CSP.Examples.Cardano_network.Parametric.LeiosInstance
  using (leiosParams; leiosLine)
open import CSP.Examples.Cardano_network.Net leiosParams
  using (Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data leiosParams using (Payload)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node leiosParams leiosLine apiES
  using (Proc; node)

import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeLeaves as ASL
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceBF as BPBF
import CSP.Examples.Cardano_network.Parametric.AnnounceSafeCopy as ASCp

open NL.Generic leiosParams leiosLine apiES using (nodeLogic)
open AI.Generic leiosParams leiosLine apiES using (WellAnnounced; Gated)
open BP.Generic leiosParams leiosLine apiES
  using (Wf; nowW; stepW; _∪α_; AnnIn; wf→gate; blockOK-mint; c-stGet)
open BPBF.Generic leiosParams leiosLine apiES using (peersG)
open ASCp.Generic leiosParams leiosLine apiES using (logicG)
open ASCp.Generic.Assembly leiosParams leiosLine apiES
  (λ {l} {d} → ASL.annSync-apiES leiosParams leiosLine {l} {d})
  (λ {l} {d} → ASCp.bfSync-apiES leiosParams leiosLine {l} {d})
  using (wf-node)

open import CSP.Examples.Cardano_network.Parametric.AnnounceBadTrace
  using (badNode; blk; evGet; step₁; step₂)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (ev; sVis; _─[_]─►_)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using (Par-sync; Par-soloR)
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload}) using (Alpha)

------------------------------------------------------------------------
-- THE ALPHABET BOTH HALVES ARE STATED AT
------------------------------------------------------------------------

-- the node's guarantee alphabet: its BlockFetch peers' (`peersG`) together with its
-- relay logic's (`logicG`).  This is literally the alphabet
-- `AnnounceSafeCopy.Assembly.wf-node` produces, so the positive half below is that
-- fact and not a weakening of it.
nodeG : Alpha
nodeG = peersG ∪α logicG

------------------------------------------------------------------------
-- THE POSITIVE HALF — the good node, and what its `Wf` buys
------------------------------------------------------------------------

-- the announce channel is in `nodeG`: it is a threads label (`threadsG`), and it is
-- not `output`, so it survives the `logicG` shrink.  `wf→gate`'s only side condition.
annIn-nodeG : AnnIn nodeG
annIn-nodeG _ = inj₂ (inj₁ tt , tt)

-- THE SYMMETRY, MACHINE-CHECKED.  `AnnounceSafeCopy.Assembly.wf-node` really does
-- land at the very type the negative half below negates — same predicate, same
-- alphabet `nodeG`, same initial minted set `[]` — with only the relay logic differing.
-- Stated separately (rather than left implicit in `gated-goodNode`) so that a reader
-- can compare the two signatures line for line.
wf-goodNode : ∀ n → Wf nodeG [] (node n (nodeLogic n []))
wf-goodNode n = wf-node n

-- THE POSITIVE HALF, SPENT.  Every node of the Leios line running the SHIPPED relay
-- logic from an empty store is gated: whatever it announces next announces an EB hash
-- already in the (here empty) minted set.  Premise-free — `wf-node`'s two `Assembly`
-- premises are discharged above for the shipped api alphabet.
gated-goodNode : ∀ n → Gated [] (node n (nodeLogic n []))
gated-goodNode n = wf→gate (λ {l} {d} → annIn-nodeG {l} {d}) (wf-node n)

------------------------------------------------------------------------
-- THE NEGATIVE HALF — the broken node fails the SAME predicate
------------------------------------------------------------------------

-- the ill-announced block is not well-announced against the EMPTY minted set: it
-- announces the EB hash `true` (`announcedEB = λ b → b`, `blk = just true`), and
-- nothing at all has been minted.
¬wellAnnounced-blk : ¬ WellAnnounced [] blk
¬wellAnnounced-blk (inj₁ ())
¬wellAnnounced-blk (inj₂ (_ , _ , ()))

-- the `stGet` that takes the ill-announced block back out of the broken store,
-- available already after the mint and its loop-back τ — `AnnounceBadTrace.step₅`'s
-- proof term re-sourced at `proj₁ step₂`, the LN peer's two steps being irrelevant to
-- it.  `store ∉ apiES`, so the peer bundle stays put while the announce thread and
-- the broken block store synchronise inside the logic.
badGet : Σ[ Q ∈ Proc ] (proj₁ step₂ ─[ ev evGet ]─► Q)
badGet = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ _
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ())
      (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)
        refl) refl) refl)
      (sVis refl refl))
    refl

-- THE NEGATIVE HALF.  The BROKEN node — the same node, at the same alphabet, from the
-- same empty store and the same empty minted set — is NOT `Wf`.  Walk `stepW` over the
-- ill-announced mint (whose own label is `blockOK-mint`, and which mints no EB, so the
-- minted set stays `[]`) and over the store's loop-back τ; at the state so reached the
-- broken store OFFERS the ill-announced block on `stGet`, which is one of the node's
-- own guarantee channels, so `nowW` demands it be well-announced against `[]`.  It is
-- not.
¬wf-badNode : ¬ Wf nodeG [] badNode
¬wf-badNode w =
  ¬wellAnnounced-blk
    (nowW (stepW (stepW w ⊆-refl (proj₂ step₁) blockOK-mint) ⊆-refl (proj₂ step₂) tt)
          ⊆-refl (inj₂ (inj₂ tt , tt)) (proj₂ badGet) c-stGet)

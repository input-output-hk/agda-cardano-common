{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — NEGATIVE CONTROL for the trace-level
-- announcement-safety specification
-- `AnnounceSafe.Generic.AnnounceSpecT`, at the concrete `LeiosInstance`
-- parameters.
--
-- WHY THIS MODULE EXISTS.  A specification that is accidentally
-- satisfied by EVERYTHING makes the entire campaign above it worthless:
-- every refinement proof discharged against it would be true and
-- meaningless.  That exact failure mode has ALREADY OCCURRED once on
-- this very spec — the RUN-shaped draft of `AnnounceSpec` (see the
-- `⊓ Stop` discussion in `AnnounceSafe`'s header) — so the content of
-- the specification is pinned here by machine-checked results rather
-- than by prose.  The two directions are:
--
--   * `badTraceRefused`  — the spec genuinely FORBIDS something: a
--     one-event trace announcing an EB hash that no mint produced is
--     NOT a trace of `AnnounceSpecT`.  Without this, the spec could be
--     `Chaos` and nothing would notice.
--   * `goodTraceAllowed` — the spec is not merely `Stop` in disguise:
--     the very same announcement IS permitted once the matching mint
--     has happened.  Without this, the gate could be vacuously closed
--     and every implementation would trivially fail to refine it.
--
-- Together they show the announcement gate is neither open nor shut but
-- actually keyed to the minted set, which is the whole content of the
-- property.
--
-- Note the target is `AnnounceSpecT` (trace refinement), NOT the older
-- `AnnounceSpec`: `⊑F` ranges over stable failures only, so it is the
-- wrong order for a safety property (see `AnnounceSafe`'s header).
-- `AnnounceSpecT` drops the `⊓ Stop`, which makes `badTraceRefused`
-- STRICTLY EASIER — there is no internal choice to case-split and no
-- `Stop` branch to dismiss; the top state has no τ at all.
--
-- PROOF TECHNIQUE.  Direct nested pattern-matching against the
-- `_─[_]─►_` / `_⟹⟨_⟩_` constructors (`sVis`/`sTau`/`sSil`, with `refl`
-- forcing the relevant `force`/offer-map equalities and absurd patterns
-- `()` where an offer map is definitionally `nothing`), the same idiom
-- used throughout `CSP.Examples.InvariantMini`.  No inversion lemmas
-- from `CSP.Laws.Traces.*` are needed: `loop`/`iter`/`_>>=_`/`pchoice`
-- are plain non-abstract functions Agda reduces through on its own.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceContent where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Function.Base using (case_of_)

open import Process_Trees using (ExtI)

open import CSP.Examples.Cardano_network.Parametric.LeiosInstance
  using (leiosParams; leiosLine)
open import CSP.Examples.Cardano_network.Net leiosParams
  using (Net_Api; env; apiLN; envMint; sendLNBlockAnnouncement)
open import CSP.Examples.Cardano_network.Data leiosParams
  using (Payload; Header; header)
open import CSP.Examples.Cardano_network.Base using (lo)
open import CSP.Examples.Cardano_network.ApiAlphabet leiosParams using (apiES)

import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
open AS.Generic leiosParams leiosLine apiES
  using (AnnounceSpecT; AnnounceSpec; announceSpecT-traces⊆)

open import Semantics.LTS
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Failures
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)

------------------------------------------------------------------------
-- The two events: an RB header `h` announcing the EB hash `true`, and a
-- mint of that same EB.  Both live on link 0, direction `lo` — the
-- choice of link/direction is arbitrary, `AnnounceSpecT` treats every
-- link and direction alike.
------------------------------------------------------------------------

-- the ranking-block header announcing EB hash `true`
h : Header
h = header (just true)

-- the announcement event: `apiLN 0 lo sendLNBlockAnnouncement ! h`
evAnnounce : Event√ (⊤ {0ℓ})
evAnnounce = evl (evLabel Header (apiLN fzero lo sendLNBlockAnnouncement) h)

-- the mint event: `env 0 lo envMint ! (just true , nothing)`, minting the EB
-- whose hash is `true`
evMint : Event√ (⊤ {0ℓ})
evMint = evl (evLabel (_ × _) (env fzero lo envMint) (just true , nothing))

------------------------------------------------------------------------
-- RESULT (1): the spec FORBIDS the bad announcement.  With nothing
-- minted beforehand, `⟨evAnnounce⟩` is not a trace of `AnnounceSpecT`.
--
-- `AnnounceSpecT`'s initial state is a pure-visible `react` node: its
-- τ-map is `∅t` (no `⊓` here, unlike `AnnounceSpec`), so there is no
-- silent move to take at all, and the single visible step is refused
-- because `announceOK [] h` computes to `false` — nothing has been
-- minted, so the announce channel is closed.  Three clauses suffice:
-- the visible dead end, the `sil` shape (the node is a `react`, so the
-- forcing equation is absurd), and the `sTau` shape (`∅t` offers
-- nothing at any index).
------------------------------------------------------------------------

badTraceRefused : ¬ traces AnnounceSpecT (evAnnounce ∷ [])
-- the announce channel is GATED and nothing is minted, so the event is not offered
badTraceRefused (_ , ⟹-ev (sVis refl ()) _)
-- the initial state forces to a `react`, never to a `sil`
badTraceRefused (_ , ⟹-τ (sSil eq) _) = case eq of λ ()
-- and its τ-map is `∅t` — no internal choice is available at any index
badTraceRefused (_ , ⟹-τ (sTau refl ()) _)

------------------------------------------------------------------------
-- RESULT (2): the spec PERMITS the corresponding good trace.
-- `⟨evMint, evAnnounce⟩` IS a trace of `AnnounceSpecT` — mint the EB
-- hashing to `true`, then announce it.  The only silent step is the
-- `loop`-back `sil` that `iter-bind` emits between the two visible
-- events; there is no internal-choice τ to resolve.
------------------------------------------------------------------------

goodTraceAllowed : traces AnnounceSpecT (evMint ∷ evAnnounce ∷ [])
goodTraceAllowed =
  _ , ⟹-ev (sVis {at = _ , env fzero lo envMint} {a = just true , nothing} refl refl)
      ( ⟹-τ (sSil refl)
      ( ⟹-ev (sVis {at = _ , apiLN fzero lo sendLNBlockAnnouncement} {a = h} refl refl)
        ⟹-refl))

------------------------------------------------------------------------
-- RESULT (3): the trace transport of `AnnounceSafe.announceSpecT-traces⊆`
-- is not vacuous — it carries the good trace above over to the
-- Chaos-shaped `AnnounceSpec`, whose extra `⊓ Stop` therefore costs the
-- gate none of its content.
------------------------------------------------------------------------

goodTraceAllowedF : traces AnnounceSpec (evMint ∷ evAnnounce ∷ [])
goodTraceAllowedF = announceSpecT-traces⊆ _ goodTraceAllowed

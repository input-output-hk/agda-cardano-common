{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE COINDUCTIVE CARRIER of announcement
-- safety, its monotonicity, and the bridge from it to `⊑T`.
--
-- `Parametric.AnnounceInvariant` states the residual obligation as
-- `Preservation`: every state the composite REACHES is `Gated`.  That
-- phrasing is an INDUCTION over an accumulated run, and discharging it
-- needs a strengthened hypothesis carried along that run.  This module
-- supplies the carrier for it: `Safe ms M` is `Reach` turned inside out
-- — coinductive, indexed by the CURRENT state and the CURRENT minted
-- set rather than by an accumulated history — so its four step fields
-- (`onτ`/`onMint`/`onOther`, plus the `gate` `Reach` had to state
-- separately) sit ONE-TO-ONE against `Reach`'s four constructors.
--
-- WHY A PREDICATE ON PROCESSES AND NOT A STATE FAMILY.  A design spike
-- established that `⦀Fin⁺`'s reachable set is NOT `{⦀Fin⁺ n g}`: it is
-- that set closed under the `par-brBoth` COLLISION nodes `Par`'s
-- `par-pVis` builds whenever two components offer the same event
-- (pairwise alphabet disjointness is REFUTED for nodes — they share
-- link alphabets with their neighbours).  A config-indexed state family
-- therefore has an outright FALSE step-soundness lemma here.  `Safe`
-- names no syntactic shape at all: a collision node offers no visible
-- event, so `gate` is vacuous there, and the two τ-successors it
-- resolves into are handled by `onτ` like any other τ.
--
-- WHAT IT BUYS.  `safe→announceSafeT` turns ONE `Safe` fact about the
-- initial composite into `AnnounceSafeTWith` — the whole announcement
-- safety property — with no confinement premise: `MediumConfined` is
-- what one needs to PROVE a `Safe` fact, not to SPEND one.  Nothing
-- below proves any leaf `Safe` fact; that is the successor task.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceSafeCarrier where

open import Level using (0ℓ)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; ptree; react; AnyTypes; ContinueType; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI

------------------------------------------------------------------------
-- The generic layer
------------------------------------------------------------------------

-- the carrier, parametric in the network parameters, the topology and the api
-- alphabet — the same three parameters `Parametric.AnnounceSafe` and
-- `Parametric.AnnounceInvariant` take, so `Gated`, `AnnounceSpecT` and
-- `systemOfWith` below are literally those modules'
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block; EB; EBHash; ebHash)
  open N p
    using ( Net_Api; Net_Api-≟; env; envMint; apiLN; store; break
          ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
          ; apiCS; apiBF; apiTS; apiKA; apiLF
          ; sendLNBlockAnnouncement; sendLNRequestNext; sendLNDone
          ; sendLNBlockOffer; sendLNBlockTxsOffer; sendLNVotesOffer
          ; recvLNBlockAnnouncement; recvLNBlockOffer
          ; recvLNBlockTxsOffer; recvLNVotesOffer )
  open D p using (Payload; Header; header)
  open Topology t using (Node)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload})
    using ( pchoice; Ret; _>>=_; iter; iter-bind
          ; EventSet; ∅ES; Par; par-brBoth; _⦀_; _∥⇘_⇙_; _∖_; ⦀Fin⁺ )
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES
    using (Proc; systemOfWith)
  open NL.Generic p t apiES using (nodeLogic)
  open AS.Generic p t apiES
    using (Minted; announceOK; announceOffer; AnnounceSpecT; AnnounceSafeTWith)
  open AI.Generic p t apiES
    using (WellAnnounced; wellAnnounced-mono; wellAnnounced→announceOK
          ; mintedAfter; NotMint; Gated)
  open import Semantics.LTS
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; Event√; ev; τ; evl; √; evLabel; _─[_]─►_; sRet; sVis; sSil)
  open import Semantics.WeakBisim
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
  open import Semantics.WeakSim
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (WSim; wsim→⊑T)
  open import Semantics.BisimFromRel
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (module WSimFromRel)
  open import CSP.Laws.Bisim.IterCong (Net_Api-≟ {Payload}) using (iter-bind-ev)
  open import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) using (bind-ev)
  open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
    using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR; evBoth; ev√)
  open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload})
    using (brBoth-τ-elim; brBoth-no-ev)
  open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
    using (Hide-τ-elim; hτP; hτH; Hide-ev-elim; heV; he√)

  ------------------------------------------------------------------------
  -- The carrier
  ------------------------------------------------------------------------

  -- SAFETY AS A COINDUCTIVE PREDICATE ON PROCESSES.  `Safe ms M` says: `M` may
  -- announce only blocks well-announced against `ms`, and every state `M` steps to
  -- is safe against the minted set that step leaves behind.
  record Safe (ms : Minted) (M : Proc) : Set₁ where
    coinductive
    field
      -- here and now: `M` announces nothing unminted (`Reach`'s conclusion, made a
      -- field so the predicate is self-contained)
      gate    : Gated ms M
      -- τ — including the resolution of a `par-brBoth` collision — keeps `ms`
      onτ     : ∀ {M′} → M ─[ τ ]─► M′ → Safe ms M′
      -- a mint on any link and direction grows `ms` exactly as the spec's state grows
      onMint  : ∀ {l d M′} {mb : Maybe EB × Block}
              → M ─[ ev (evl (evLabel _ (env l d envMint) mb)) ]─► M′
              → Safe (mintedAfter mb ms) M′
      -- every other visible label leaves `ms` alone
      onOther : ∀ {M′} {a : Label (⊤ {0ℓ})} → NotMint a → M ─[ a ]─► M′ → Safe ms M′
      -- `M` never TICKS.  `AnnounceSpecT` is a `loop`, so it forces to a `react` node
      -- and has no `√` step to match one with; `AnnounceSafeTWith` is literally FALSE
      -- for a terminating implementation, so this obligation is not an artefact of
      -- the proof route.  It is discharged leaf-by-leaf (every node and every medium
      -- cell is a `loop`) exactly as `gate` is.
      noTick  : ∀ {x : ⊤ {0ℓ}} {M′} → M ─[ ev (√ x) ]─► M′ → ⊥
  open Safe

  -- `onOther` with the STEP first, so the label is already solved — and `NotMint`'s
  -- reduct therefore already known — when the trivial witness is elaborated
  onOther′ : ∀ {ms M M′} {a : Label (⊤ {0ℓ})}
           → Safe ms M → M ─[ a ]─► M′ → NotMint a → Safe ms M′
  onOther′ s st nm = onOther s nm st

  ------------------------------------------------------------------------
  -- Monotonicity
  ------------------------------------------------------------------------

  -- growing the minted set on both sides of a `∷` keeps the inclusion
  ∷-mono : ∀ {h : EBHash} {ms ms′} → ms ⊆ ms′ → (h ∷ ms) ⊆ (h ∷ ms′)
  ∷-mono sub (here eq) = here eq
  ∷-mono sub (there q) = there (sub q)

  -- a mint extends both minted sets by the same hash, so it preserves the inclusion
  mintedAfter-mono : ∀ (mb : Maybe EB × Block) {ms ms′}
                   → ms ⊆ ms′ → mintedAfter mb ms ⊆ mintedAfter mb ms′
  mintedAfter-mono (just _  , _) sub = ∷-mono sub
  mintedAfter-mono (nothing , _) sub = sub

  -- THE MONOTONICITY OF THE CARRIER: minting only ever ADDS permissions, so a state
  -- safe against a smaller minted set is safe against a larger one.  Corecursive
  -- through every step field, guarded by copatterns.
  safe-mono : ∀ {ms ms′ M} → ms ⊆ ms′ → Safe ms M → Safe ms′ M
  safe-mono sub s .gate st           = wellAnnounced-mono sub (gate s st)
  safe-mono sub s .onτ st            = safe-mono sub (onτ s st)
  safe-mono sub s .onMint {mb = mb} st = safe-mono (mintedAfter-mono mb sub) (onMint s st)
  safe-mono sub s .onOther nm st     = safe-mono sub (onOther s nm st)
  safe-mono sub s .noTick st         = noTick s st

  ------------------------------------------------------------------------
  -- The congruences
  --
  -- `Safe` is closed under the three operators the composite is built from:
  -- parallel (hence interleaving and its replicated form) and hiding.  Each is
  -- proved by ONE inversion of the operator's step relation, per field, with
  -- copattern-guarded corecursion — no state family, no reachability induction.
  ------------------------------------------------------------------------

  -- minting only ever ADDS to the minted set, so the pre-mint set is contained in the
  -- post-mint one.  This is what lets the operand that did NOT mint catch up.
  mintedAfter-⊇ : ∀ (mb : Maybe EB × Block) {ms} → ms ⊆ mintedAfter mb ms
  mintedAfter-⊇ (just _  , _) q = there q
  mintedAfter-⊇ (nothing , _) q = q

  -- THE PARALLEL CONGRUENCE, and its collision companion, mutually corecursive.
  --
  -- `safe-both` covers the `par-brBoth` COLLISION node `Par`'s `par-pVis` builds when
  -- both operands offer the same event outside the synchronisation set.  That node
  -- offers NO visible event at all (its offer map is constantly `nothing`), so `gate`,
  -- `onMint`, the visible half of `onOther` and `noTick` are all discharged outright by
  -- `brBoth-no-ev`; its only moves are the two internal-choice τ's committing to
  -- `Par P′ Q` or `Par P Q′`, and those go straight back into `safe-Par`.  This is the
  -- case a config-indexed state family cannot state, and it costs six lines here.
  safe-Par  : ∀ {ms} (A : EventSet) {P Q} → Safe ms P → Safe ms Q → Safe ms (P ∥⇘ A ⇙ Q)
  safe-both : ∀ {ms} (A : EventSet) {P Q P′ Q′}
            → Safe ms P → Safe ms Q → Safe ms P′ → Safe ms Q′
            → Safe ms (ptree (react (λ _ _ → nothing)
                              (par-brBoth A (λ _ _ → tt) P Q P′ Q′)))

  -- an announcement of the composite is an announcement of one operand
  safe-Par A {P = P} {Q = Q} sP sQ .gate st with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _ stP _   = gate sP stP
  ... | evL    _ stP     = gate sP stP
  ... | evR    _ stQ     = gate sQ stQ
  ... | evBoth _ stP _   = gate sP stP
  -- a τ of the composite is a τ of one operand; the other is untouched
  safe-Par A {P = P} {Q = Q} sP sQ .onτ st with Par-τ-elim A (λ _ _ → tt) P Q st
  ... | τL P′ stP refl   = safe-Par A (onτ sP stP) sQ
  ... | τR Q′ stQ refl   = safe-Par A sP (onτ sQ stQ)
  -- a mint: whichever operand(s) performed it move to the grown set, and the operand
  -- that did not is carried across by `safe-mono`
  safe-Par A {P = P} {Q = Q} sP sQ .onMint {mb = mb} st
    with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _ stP stQ = safe-Par A (onMint sP stP) (onMint sQ stQ)
  ... | evL    _ stP     = safe-Par A (onMint sP stP) (safe-mono (mintedAfter-⊇ mb) sQ)
  ... | evR    _ stQ     = safe-Par A (safe-mono (mintedAfter-⊇ mb) sP) (onMint sQ stQ)
  ... | evBoth _ stP stQ = safe-both A (safe-mono (mintedAfter-⊇ mb) sP)
                                       (safe-mono (mintedAfter-⊇ mb) sQ)
                                       (onMint sP stP) (onMint sQ stQ)
  -- every other label: τ as above, a visible event by the same four-way inversion,
  -- and a `√` is impossible because a joint tick needs BOTH operands at `ret`
  safe-Par A {P = P} {Q = Q} sP sQ .onOther {a = τ} nm st
    with Par-τ-elim A (λ _ _ → tt) P Q st
  ... | τL P′ stP refl   = safe-Par A (onτ sP stP) sQ
  ... | τR Q′ stQ refl   = safe-Par A sP (onτ sQ stQ)
  safe-Par A {P = P} {Q = Q} sP sQ .onOther {a = ev (evl _)} nm st
    with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | evSync _ stP stQ = safe-Par A (onOther′ sP stP nm) (onOther′ sQ stQ nm)
  ... | evL    _ stP     = safe-Par A (onOther′ sP stP nm) sQ
  ... | evR    _ stQ     = safe-Par A sP (onOther′ sQ stQ nm)
  ... | evBoth _ stP stQ = safe-both A sP sQ (onOther′ sP stP nm) (onOther′ sQ stQ nm)
  safe-Par A {P = P} {Q = Q} sP sQ .onOther {a = ev (√ _)} nm st
    with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | ev√ fpP _        = ⊥-elim (noTick sP (sRet fpP))
  -- `Par`'s joint `√` requires both operands to tick, so ONE operand's `noTick` suffices
  safe-Par A {P = P} {Q = Q} sP sQ .noTick st with Par-ev-elim A (λ _ _ → tt) P Q st
  ... | ev√ fpP _        = noTick sP (sRet fpP)

  safe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .gate st =
    ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
  safe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onτ st
    with brBoth-τ-elim A (λ _ _ → tt) P Q P′ Q′ st
  ... | inj₁ refl = safe-Par A sP′ sQ
  ... | inj₂ refl = safe-Par A sP sQ′
  safe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onMint st =
    ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
  safe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onOther {a = τ} nm st
    with brBoth-τ-elim A (λ _ _ → tt) P Q P′ Q′ st
  ... | inj₁ refl = safe-Par A sP′ sQ
  ... | inj₂ refl = safe-Par A sP sQ′
  safe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .onOther {a = ev _} nm st =
    ⊥-elim (brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st)
  safe-both A {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} sP sQ sP′ sQ′ .noTick st =
    brBoth-no-ev A (λ _ _ → tt) P Q P′ Q′ st

  -- INTERLEAVING is parallel at the empty synchronisation set, definitionally
  safe-⦀ : ∀ {ms P Q} → Safe ms P → Safe ms Q → Safe ms (P ⦀ Q)
  safe-⦀ = safe-Par ∅ES

  -- REPLICATED INTERLEAVING: `⦀Fin⁺ (suc n) f = f fzero ⦀ ⦀Fin⁺ n (f ∘ fsuc)` is
  -- definitional, so this is plain `Fin` recursion on top of `safe-⦀` — no inversion
  -- lemma for the fold is needed at all
  safe-⦀Fin⁺ : ∀ {ms} (n : ℕ) {f : Fin (suc n) → Proc}
             → (∀ i → Safe ms (f i)) → Safe ms (⦀Fin⁺ n f)
  safe-⦀Fin⁺ zero            h = h fzero
  safe-⦀Fin⁺ (suc n) {f = f} h =
    safe-⦀ (h fzero) (safe-⦀Fin⁺ n {f = λ i → f (fsuc i)} (λ i → h (fsuc i)))

  -- THE SIDE CONDITION OF HIDING: no hidden event is a mint.  A hidden mint would let
  -- the implementation grow its minted set SILENTLY while the spec's state stands
  -- still, and `Safe` would then be false — `safe-mono` runs the wrong way to repair
  -- it.  The announce event needs no condition: hiding it merely removes announcements.
  HideOK : EventSet → Set₁
  HideOK A = ∀ {B} {e : Net_Api Payload B} {x : B}
           → EventSet.mem A (B , e) x → NotMint (ev (evl (evLabel B e x)))

  -- THE HIDING CONGRUENCE.  A visible step of `P ∖ A` is the same visible step of `P`
  -- (so `gate`, `onMint` and the visible half of `onOther` transfer verbatim, and a
  -- `√` passes straight through to `noTick`); a τ of `P ∖ A` is either a τ of `P` or a
  -- hidden visible event of `P`, and `HideOK` says the latter is never a mint.
  safe-Hide : ∀ {ms} (A : EventSet) → HideOK A → ∀ {P} → Safe ms P → Safe ms (P ∖ A)
  safe-Hide A ok {P = P} s .gate st with Hide-ev-elim A P st
  ... | heV P′ _ stP      = gate s stP
  safe-Hide A ok {P = P} s .onτ st with Hide-τ-elim A P st
  ... | hτP P′ stP refl   = safe-Hide A ok (onτ s stP)
  ... | hτH P′ c stP refl = safe-Hide A ok (onOther′ s stP (ok c))
  safe-Hide A ok {P = P} s .onMint st with Hide-ev-elim A P st
  ... | heV P′ _ stP      = safe-Hide A ok (onMint s stP)
  safe-Hide A ok {P = P} s .onOther {a = τ} nm st with Hide-τ-elim A P st
  ... | hτP P′ stP refl   = safe-Hide A ok (onτ s stP)
  ... | hτH P′ c stP refl = safe-Hide A ok (onOther′ s stP (ok c))
  safe-Hide A ok {P = P} s .onOther {a = ev (evl _)} nm st with Hide-ev-elim A P st
  ... | heV P′ _ stP      = safe-Hide A ok (onOther′ s stP nm)
  safe-Hide A ok {P = P} s .onOther {a = ev (√ _)} nm st with Hide-ev-elim A P st
  ... | he√ eq            = ⊥-elim (noTick s (sRet eq))
  safe-Hide A ok {P = P} s .noTick st with Hide-ev-elim A P st
  ... | he√ eq            = noTick s (sRet eq)

  ------------------------------------------------------------------------
  -- The specification's own states
  --
  -- `AnnounceSafe` keeps these PRIVATE, so they are re-derived here.  They are
  -- definitionally the same processes — `specAt-init` pins that — because `loop`
  -- unfolds to `iter` over exactly this step function.
  ------------------------------------------------------------------------

  private
    -- the tree type the spec's `loop` iterates over
    Tree : Set → Set₁
    Tree X = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) X

    -- `loop`'s state-threading continuation: hand the new state back to `iter`
    κ : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
    κ ms = Ret (inj₁ ms)

    -- the `iter` step `loop` builds from `AnnounceSpecT`'s body
    StepT : Minted → Tree (Minted ⊎ ⊤ {0ℓ})
    StepT ms = pchoice (announceOffer ms) >>= κ

    -- the `sil` back-edge `loop` emits after a visible event
    ST : Minted → Proc
    ST ms = iter-bind (Ret ms >>= κ) StepT

  -- THE SPEC AT A MINTED SET: `AnnounceSpecT`'s state after a run whose mints
  -- produced `ms`.  This is what `Safe ms` is a simulation hypothesis for.
  AnnounceSpecAt : Minted → Proc
  AnnounceSpecAt ms = iter StepT ms

  -- …and at the empty minted set it IS the shipped spec, definitionally
  specAt-init : AnnounceSpecAt [] ≡ AnnounceSpecT
  specAt-init = refl

  ------------------------------------------------------------------------
  -- The spec's forward steps
  ------------------------------------------------------------------------

  -- the spec's menu offers the event and lands on the loop-back edge
  specEv : ∀ {ms ms′} {at : AnyTypes (Net_Api Payload)} {a : proj₁ at}
         → announceOffer ms at a ≡ just (Ret ms′)
         → AnnounceSpecAt ms ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► ST ms′
  specEv {ms} eq =
    iter-bind-ev StepT (StepT ms)
      (bind-ev κ (pchoice (announceOffer ms)) (sVis refl eq))

  -- and the loop-back edge τ's straight into the next menu
  specLoop : ∀ {ms} → ST ms ─[ τ ]─► AnnounceSpecAt ms
  specLoop = sSil refl

  -- the announce channel's gate opens for a well-announced block: the `if` of
  -- `announceOffer` takes its `just` branch, which is the whole point of the invariant
  announceEq : ∀ {ms b l d} → announceOK ms (header b) ≡ true
             → announceOffer ms (_ , apiLN l d sendLNBlockAnnouncement) (header b)
               ≡ just (Ret ms)
  announceEq eq rewrite eq = refl

  ------------------------------------------------------------------------
  -- The step correspondence
  ------------------------------------------------------------------------

  -- EVERY visible step the implementation can make is offered by the spec's menu,
  -- and the successor is safe against the state the menu moves to.  The announce
  -- channel is the only clause with content — it spends `gate` — and the mint
  -- channel is the only one that changes the state; the remaining twenty-four
  -- clauses are the free channels, enumerated because `announceOffer`'s catch-all
  -- does not reduce until the constructor is known.
  menuStep : ∀ {ms M M′} → Safe ms M
           → (at : AnyTypes (Net_Api Payload)) (a : proj₁ at)
           → M ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► M′
           → Σ[ ms′ ∈ Minted ] (announceOffer ms at a ≡ just (Ret ms′) × Safe ms′ M′)
  menuStep {ms} s (_ , input  _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , output _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , sndmsg _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , rcvmsg _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , tx     _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , sndack _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , rcvack _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , ack    _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , done   _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiCS  _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiBF  _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiTS  _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiKA  _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLF  _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , store  _ _ _) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , break  _)     a st = ms , refl , onOther′ s st tt
  -- the mint channel: the spec's state and `mintedAfter` grow by the same hash
  menuStep {ms} s (_ , env _ _ envMint) (just e  , b) st =
    mintedAfter (just e , b) ms , refl , onMint s st
  menuStep {ms} s (_ , env _ _ envMint) (nothing , b) st =
    mintedAfter (nothing , b) ms , refl , onMint s st
  -- THE LOAD-BEARING CLAUSE: `gate` says the announced block is well-announced, and
  -- `wellAnnounced→announceOK` turns that into the boolean the spec's gate tests
  menuStep {ms} s (_ , apiLN l d sendLNBlockAnnouncement) (header b) st =
    ms , announceEq {l = l} {d = d} (wellAnnounced→announceOK (gate s st)) , onOther′ s st tt
  -- the rest of LeiosNotify is free
  menuStep {ms} s (_ , apiLN _ _ sendLNRequestNext)       a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLN _ _ sendLNDone)              a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLN _ _ sendLNBlockOffer)        a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLN _ _ sendLNBlockTxsOffer)     a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLN _ _ sendLNVotesOffer)        a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLN _ _ recvLNBlockAnnouncement) a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLN _ _ recvLNBlockOffer)        a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLN _ _ recvLNBlockTxsOffer)     a st = ms , refl , onOther′ s st tt
  menuStep {ms} s (_ , apiLN _ _ recvLNVotesOffer)        a st = ms , refl , onOther′ s st tt

  ------------------------------------------------------------------------
  -- The bridge
  ------------------------------------------------------------------------

  private
    -- the step-matching relation `WSimFromRel` runs on: an implementation state is
    -- related to the spec state at the minted set it is safe against
    SafeR : Proc → Proc → Set₁
    SafeR M Q = Σ[ ms ∈ Minted ] (Safe ms M × (Q ≡ AnnounceSpecAt ms))

    -- a visible step is matched by the menu, then the loop-back τ
    safeE : ∀ {P Q} {l : Event√ (⊤ {0ℓ})} {P′} → SafeR P Q → P ─[ ev l ]─► P′
          → Σ[ Q′ ∈ Proc ] ((Q ═[ ev l ]═► Q′) × SafeR P′ Q′)
    safeE {l = evl (evLabel A e a)} (ms , s , refl) st with menuStep s (A , e) a st
    ... | ms′ , eq , s′ =
      AnnounceSpecAt ms′
      , wev τ*-refl (specEv eq) (τ*-step specLoop τ*-refl)
      , (ms′ , s′ , refl)
    -- a `√` is impossible: the spec is a `loop` and cannot match one
    safeE {l = √ x} (ms , s , refl) st = ⊥-elim (noTick s st)

    -- a τ is matched by the EMPTY weak τ-run: the spec's state is unchanged
    safeT : ∀ {P Q P′} → SafeR P Q → P ─[ τ ]─► P′
          → Σ[ Q′ ∈ Proc ] ((Q ═[ τ ]═► Q′) × SafeR P′ Q′)
    safeT (ms , s , refl) st = AnnounceSpecAt ms , wτ τ*-refl , (ms , onτ s st , refl)

    open WSimFromRel SafeR safeE safeT using (rel→wsim)

  -- A SAFE STATE IS SIMULATED BY THE SPEC AT ITS MINTED SET.  This is the whole
  -- content of the carrier: `Safe` was chosen to be exactly the relation
  -- `WSimFromRel` needs, so the coinduction principle discharges it outright.
  safe→wsim : ∀ {ms M} → Safe ms M → WSim (⊤ {0ℓ}) M (AnnounceSpecAt ms)
  safe→wsim {ms} s = rel→wsim (ms , s , refl)

  -- THE BRIDGE: one `Safe` fact about the initial composite IS announcement safety
  -- at `⊑T`.  Note the argument order — `wsim→⊑T` takes the IMPLEMENTATION first.
  -- No `MediumConfined` premise: confinement is what one needs to PROVE a `Safe`
  -- fact, not to spend one.
  safe→announceSafeT : (med : Proc)
                     → Safe [] (systemOfWith med (λ n → nodeLogic n []))
                     → AnnounceSafeTWith med
  safe→announceSafeT med s = wsim→⊑T (safe→wsim s)

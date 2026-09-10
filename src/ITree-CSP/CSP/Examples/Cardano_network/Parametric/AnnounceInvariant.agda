{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE RESIDUAL INVARIANT OBLIGATIONS OF
-- ANNOUNCEMENT SAFETY, stated as types.
--
-- `Parametric.AnnounceSafe` states announcement safety at `⊑T`
-- (`AnnounceSafeT`) and reduces it, via `announceSafeT-from-nodes`, to
-- one per-node obligation plus a residual on the abstracted composite.
-- What is left is a GLOBAL invariant over that composite, and that is a
-- campaign of its own.  This module makes that campaign start from a
-- COMPILING INTERFACE rather than from prose: it proves the easy parts
-- (`wellAnnounced-mono` and the bridge to the spec's boolean gate) and
-- states the hard part as an Agda type.
--
-- This is the repo's own idiom — `NodeLogic.NodeObligation`,
-- `NodeLogic.EndpointObligation` and `NodeLogic.InterchangeGoal` are all
-- `Set₁`-valued definitions with no proof term, written so that the
-- successor plan can name and size what it must discharge.
--
-- WHY A NEW MODULE RATHER THAN A SECTION OF `AnnounceSafe`.  Everything
-- here is about the IMPLEMENTATION's reachable states; `AnnounceSafe` is
-- about the SPECIFICATION and the compositional reduction.  Keeping the
-- reachability family out of `AnnounceSafe` keeps that module's import
-- surface (and `AnnounceContent`'s negative control over it) untouched.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.AnnounceInvariant where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any)
open import Data.List.Relation.Unary.Any.Properties using (any⁺; any⁻)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; fromWitness; toWitness)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Examples.Cardano_network.Parametric.NodeLogic as NL
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS

------------------------------------------------------------------------
-- The generic layer
------------------------------------------------------------------------

-- the residual obligations, parametric in the network parameters, the topology and
-- the api alphabet — the same three parameters `Parametric.Node`,
-- `Parametric.NodeLogic` and `Parametric.AnnounceSafe` take, so `systemOfWith`,
-- `nodeLogic` and `AnnounceSpecT` below are literally those modules'
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open Params p using (Block; EB; EBHash; ebHash; announcedEB; decEBHash)
  open N p
    using ( Net_Api; Net_Api-≟; env; envMint; apiLN; sendLNBlockAnnouncement )
  open D p using (Payload; Header; header)
  open Topology t using (Node)
  open import CSP.Examples.Cardano_network.NetCommon p using (NetworkLinkBreakableA)
  -- the medium's own event classification and the per-link confinement witnesses
  -- (`classify` sends the eight wire channels and `break` to `just`, and EVERY
  -- node-local channel — `done`/`api*`/`store`/`env` — to `nothing`)
  open import CSP.Examples.Cardano_network.MediumEquivA p
    using (classify; linkAlphaA; oo-breakableNetLinkA)
  open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
    using (Alpha; OffersOnly; OffersOnly-mono; OffersOnly-⦀Fin; unionAlpha)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES
    using (Proc; systemOfWith)
  open NL.Generic p t apiES using (nodeLogic)
  open AS.Generic p t apiES
    using (Minted; mintedIn; announceOK; AnnounceSpecT; AnnounceSafeTWith)
  open import Semantics.LTS
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (Label; ev; τ; evl; evLabel; _─[_]─►_)
  open import Semantics.WeakSim
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (WSim; wsim→⊑T)

  ------------------------------------------------------------------------
  -- The payload predicate
  ------------------------------------------------------------------------

  -- a block is well-announced against the minted set if it announces no EB, or
  -- announces one that has been minted
  WellAnnounced : Minted → Block → Set
  WellAnnounced ms b = announcedEB b ≡ nothing
                     ⊎ Σ[ eh ∈ EBHash ] (announcedEB b ≡ just eh × eh ∈ ms)

  -- the minted set only grows, and well-announcedness is monotone in it — this is
  -- what makes the mint step preserve the invariant for every OTHER block
  wellAnnounced-mono : ∀ {ms ms′ b} → ms ⊆ ms′ → WellAnnounced ms b → WellAnnounced ms′ b
  wellAnnounced-mono sub (inj₁ eq)              = inj₁ eq
  wellAnnounced-mono sub (inj₂ (eh , eq , mem)) = inj₂ (eh , eq , sub mem)

  ------------------------------------------------------------------------
  -- The bridge to the spec's own gate
  --
  -- `WellAnnounced` uses PROPOSITIONAL membership, but the shipped spec gate
  -- `AnnounceSafe.announceOK` is BOOLEAN (`any (λ x → ⌊ x ≟ eh ⌋)`).  Without the
  -- two lemmas below the invariant would never meet `announceOffer`'s
  -- `if announceOK ms h then just … else nothing`, and the successor proof would
  -- stall at exactly the step that matters.
  ------------------------------------------------------------------------

  -- propositional membership implies the spec gate's boolean membership test
  ∈→mintedIn : ∀ {eh ms} → eh ∈ ms → mintedIn eh ms ≡ true
  ∈→mintedIn {eh} mem =
    Equivalence.to T-≡
      (any⁺ (λ x → ⌊ x ≟ eh ⌋)
            (Any.map (λ {x} e → fromWitness {a? = x ≟ eh} (sym e)) mem))

  -- … and conversely, so nothing is lost by phrasing the invariant propositionally
  mintedIn→∈ : ∀ {eh} ms → mintedIn eh ms ≡ true → eh ∈ ms
  mintedIn→∈ {eh} ms ok =
    Any.map (λ {x} w → sym (toWitness {a? = x ≟ eh} w))
            (any⁻ (λ x → ⌊ x ≟ eh ⌋) ms (Equivalence.from T-≡ ok))

  -- THE BRIDGE: a well-announced block's header passes the spec's announcement gate,
  -- so `announceOffer` offers it rather than refusing it
  wellAnnounced→announceOK : ∀ {ms b} → WellAnnounced ms b → announceOK ms (header b) ≡ true
  wellAnnounced→announceOK (inj₁ eq)              rewrite eq = refl
  wellAnnounced→announceOK (inj₂ (eh , eq , mem)) rewrite eq = ∈→mintedIn mem

  -- the converse: the gate is exactly `WellAnnounced`, not merely implied by it.  It
  -- costs two lines, and it is what tells the successor campaign that strengthening
  -- the invariant beyond `WellAnnounced` buys nothing at the announce step.
  announceOK→wellAnnounced : ∀ ms b → announceOK ms (header b) ≡ true → WellAnnounced ms b
  announceOK→wellAnnounced ms b ok with announcedEB b
  ... | nothing = inj₁ refl
  ... | just eh = inj₂ (eh , refl , mintedIn→∈ ms ok)

  ------------------------------------------------------------------------
  -- The medium side condition
  --
  -- WHY IT IS NEEDED.  `apiLN ∉ ioES` (`NetCommon.ioSet-dec` sends every `api*`
  -- channel to `no`), so an announcement is neither synchronised at `∥⇘ ioES ⇙`
  -- nor hidden by `∖ ioES`: `Par-ev-elim` admits the `evL` case, in which the
  -- MEDIUM alone performs the announcement.  Without a hypothesis excluding that,
  -- `PreservationWith`/`AnnounceWSimGoalWith` are refuted outright by a medium
  -- that announces a never-minted block, and every later task would be trying to
  -- discharge a false statement.  The same `evL` case is what would otherwise let
  -- the medium perform `env … envMint` and `store … stPut` solo, so the condition
  -- is stated as full LINK-ALPHABET confinement rather than as "never announces":
  -- one hypothesis kills the whole medium-solo branch of `Par-ev-elim`, and it is
  -- exactly the `OffersOnly` invariant the repo already proves for both shipped
  -- mediums (`MediumEquivA`, `FourNode.BreakableSystemEquiv`).
  ------------------------------------------------------------------------

  -- the alphabet of events that BELONG TO A LINK — the wire channels and `break`
  linkEvents : Alpha
  linkEvents at a = classify at a ≢ nothing

  -- THE SIDE CONDITION: every event `med` can ever offer — now or after any run,
  -- `OffersOnly` being closed under all steps — belongs to a link.  A confined
  -- medium therefore performs no node-local event at all, in particular no
  -- announcement, no mint and no store write.
  MediumConfined : Proc → Set₁
  MediumConfined med = OffersOnly linkEvents med

  -- what the side condition buys at the announce step: a confined medium can never
  -- itself announce a block, because `classify` sends every `apiLN` to `nothing`
  confined-noAnnounce :
    ∀ {med : Proc} {l d h M′}
    → MediumConfined med
    → ¬ (med ─[ ev (evl (evLabel _ (apiLN l d sendLNBlockAnnouncement) h)) ]─► M′)
  confined-noAnnounce oo st = OffersOnly.now oo st refl

  -- STEP 2 DISCHARGED: the default breakable medium is confined.  Each cell
  -- `breakableNetLinkA l` offers only link-`l` wire events or its own `break l`
  -- (`MediumEquivA.oo-breakableNetLinkA`), and `⦀Fin` unions those alphabets; an
  -- event in the union carries a link classification, hence is not `nothing`.
  confined-NetworkLinkBreakableA : MediumConfined NetworkLinkBreakableA
  confined-NetworkLinkBreakableA =
    OffersOnly-mono conf (OffersOnly-⦀Fin oo-breakableNetLinkA)
    where
    -- a link-classified event is not a node-local one
    conf : ∀ at a → unionAlpha linkAlphaA at a → linkEvents at a
    conf at a (i , k , q) eq with trans (sym q) eq
    ... | ()

  ------------------------------------------------------------------------
  -- The reachable-state family
  ------------------------------------------------------------------------

  -- the minted set after an `env … envMint` event carrying `(me , b)` — exactly the
  -- state update `AnnounceSafe.announceOffer` performs on its two mint clauses
  mintedAfter : Maybe EB × Block → Minted → Minted
  mintedAfter (just e  , _) ms = ebHash e ∷ ms
  mintedAfter (nothing , _) ms = ms

  -- is this label something OTHER than a mint?  `Reach` must not let a mint slip
  -- through its state-preserving step, or the minted set it carries would be too
  -- small and the announcement gate below would simply be false.
  NotMint : Label (⊤ {0ℓ}) → Set
  NotMint (ev (evl (evLabel _ (env _ _ envMint) _))) = ⊥
  NotMint _                                          = ⊤ {0ℓ}

  -- THE STATE FAMILY: `Reach med ms M` says the composite over medium `med` can reach
  -- `M` along a run whose mints produced exactly `ms`.
  --
  -- COLLISION-CLOSED BY CONSTRUCTION.  `⦀Fin⁺`'s reachable set is NOT `{⦀Fin⁺ n g}`:
  -- when two components both offer the same event, `Par`'s `par-pVis` builds a
  -- `par-brBoth` internal-choice node that a later τ resolves — the third disjunct of
  -- `CSP.Laws.Traces.TraceLawsRepElim.FoldEvR`, which that module keeps precisely
  -- because pairwise alphabet disjointness is REFUTED for nodes (they share link
  -- alphabets with their neighbours, so `NoBoth` is unavailable).  The family below
  -- therefore does NOT name a syntactic shape at all: it closes over ARBITRARY LTS
  -- steps, so a `par-brBoth` collision node is a reachable state like any other and
  -- `reach-τ` covers the step that resolves it.  This is the honest price of the
  -- refutation — the family is bigger and less informative than a positional one, and
  -- an induction over it gets no structural decomposition for free.
  data Reach (med : Proc) : Minted → Proc → Set₁ where
    -- the initial composite, no mint yet performed
    reach-init  : Reach med [] (systemOfWith med (λ n → nodeLogic n []))
    -- τ (including the resolution of a `par-brBoth` collision) leaves the minted set
    reach-τ     : ∀ {ms M M′} → Reach med ms M → M ─[ τ ]─► M′ → Reach med ms M′
    -- a mint on ANY link and direction grows the minted set; `env` survives `∖ ioES`
    reach-mint  : ∀ {ms M M′ l d} {mb : Maybe EB × Block}
                → Reach med ms M
                → M ─[ ev (evl (evLabel _ (env l d envMint) mb)) ]─► M′
                → Reach med (mintedAfter mb ms) M′
    -- every other label — visible api/store/break events and `√` alike — leaves it
    reach-other : ∀ {ms M M′} {a : Label (⊤ {0ℓ})}
                → Reach med ms M → NotMint a → M ─[ a ]─► M′ → Reach med ms M′

  ------------------------------------------------------------------------
  -- The residual obligations
  ------------------------------------------------------------------------

  -- the invariant ONE state must carry: every announcement it can make next is of a
  -- block well-announced against the minted set it was reached with.  `Header` has
  -- the single constructor `header`, so quantifying over `header b` loses nothing.
  Gated : Minted → Proc → Set₁
  Gated ms M = ∀ {l d b M′}
             → M ─[ ev (evl (evLabel _ (apiLN l d sendLNBlockAnnouncement) (header b))) ]─► M′
             → WellAnnounced ms b

  -- THE RESIDUAL OBLIGATION.  For the composite to simulate `AnnounceSpecT`, every
  -- reachable state must be `Gated`: it may only announce a block whose announced EB
  -- has already been minted somewhere in the network.
  --
  -- The strengthened induction hypothesis this needs (and which cannot be written
  -- here, because the repo has no decomposition of a composite state into its
  -- components' stores) is: every block held in any node's store, and every block in
  -- flight, is `WellAnnounced` against `ms`.  The in-flight population is BOUNDED — a
  -- `Block` sits in exactly three state kinds between a server's
  -- `apiBF … sendBFBlock ! b` and a client's `recvBFBlock`:
  --   (A) server-local        (BlockFetch.lagda.md:288-291)
  --   (B) the medium cell, phase `full`/`draining` — the medium is a genuine ONE-PLACE
  --       buffer (`Network.agda:260`), confirmed by `CopyPhase` in SysMedium.agda:118
  --   (C) client-local        (BlockFetch.lagda.md:229-230)
  --
  -- The load-bearing case is `NodeLogic.storeStep`'s `store … stPut`: `putEv` is
  -- UNGUARDED, so nothing node-local justifies it — the deposited block was received
  -- over BlockFetch, hence was in flight, hence is already well-announced.  The mint
  -- guard of `acceptMint` alone does NOT make a store well-announced.
  --
  -- `wellAnnounced-mono` is what makes `reach-mint` cheap: minting only extends `ms`,
  -- so every block already covered stays covered.
  PreservationWith : Proc → Set₁
  PreservationWith med = MediumConfined med → ∀ {ms M} → Reach med ms M → Gated ms M

  -- the same at the DEFAULT medium (the concrete per-link multiplexer), i.e. exactly
  -- the composite `Parametric.Node.systemOf` builds — the `Set₁` the plan names.
  -- PREMISE-FREE: the default medium's confinement is discharged above.
  Preservation : Set₁
  Preservation = ∀ {ms M} → Reach NetworkLinkBreakableA ms M → Gated ms M

  -- …and the premise really is dischargeable at the default medium, so narrowing
  -- `PreservationWith` costs the concrete obligation nothing
  preservation-from-with : PreservationWith NetworkLinkBreakableA → Preservation
  preservation-from-with pw = pw confined-NetworkLinkBreakableA

  -- THE SIMULATION GOAL `Preservation` feeds.  `WSimFromRel.rel→wsim` turns a
  -- step-matching relation between composite states and spec states into this
  -- `WSim`; the relation's `on-ev` obligation at an `apiLN … sendLNBlockAnnouncement`
  -- label is discharged by `Gated` composed with `wellAnnounced→announceOK`, which is
  -- precisely what makes `announceOffer`'s `if announceOK ms h` take the `just`
  -- branch.  Note the ARGUMENT ORDER: `wsim→⊑T` expects the IMPLEMENTATION first.
  -- The same narrowing: at a medium free to announce on its own there is no such
  -- simulation, so the goal carries the confinement premise too.
  AnnounceWSimGoalWith : Proc → Set₁
  AnnounceWSimGoalWith med =
    MediumConfined med
    → WSim (⊤ {0ℓ}) (systemOfWith med (λ n → nodeLogic n [])) AnnounceSpecT

  -- the same at the default medium — the `Set₁` the plan names, premise-free
  AnnounceWSimGoal : Set₁
  AnnounceWSimGoal =
    WSim (⊤ {0ℓ}) (systemOfWith NetworkLinkBreakableA (λ n → nodeLogic n []))
         AnnounceSpecT

  -- again: the premise is dischargeable at the default medium
  announceWSimGoal-from-with : AnnounceWSimGoalWith NetworkLinkBreakableA → AnnounceWSimGoal
  announceWSimGoal-from-with aw = aw confined-NetworkLinkBreakableA

  -- the goal really is the goal: a weak simulation of the composite by the spec IS
  -- announcement safety at `⊑T`.  One line, but it is what stops the interface above
  -- from being decorative — `AnnounceWSimGoalWith` is now known to be sufficient.
  announceSafeT-from-wsim : (med : Proc) → MediumConfined med
                          → AnnounceWSimGoalWith med → AnnounceSafeTWith med
  announceSafeT-from-wsim med mc sim = wsim→⊑T (sim mc)

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — BLOCK PROVENANCE AT THE COPY MEDIUM, proved
-- over the medium's OWN alphabet `Net`.
--
-- The copy medium `NetCommon.CopySpecBreakableA` is, per link, the
-- `renameMap` along `ιNet : Net ↪ Net_Api` of `Network.linkCopy l` — the
-- `⦀⋆`-interleaving of one `Copy l d id` per configured instance — under
-- a `break` interrupt.  Its `Wf` fact is proved HERE, at the source
-- alphabet, and carried across the renaming in
-- `Parametric.BlockProvenanceMedium`, exactly as the BlockFetch peers'
-- facts are split between `BlockProvenanceBF` and `BlockProvenancePeers`.
--
-- ONE CELL IS A GENUINE ONE-PLACE BUFFER AND A RELAY:
-- `Copy l d id = loop0 (pchoice (copyMenu l d id))`, and the menu answers
-- `input l d id ? x` with `output l d id ! x ⟶ Skip` (`Network.copyMenu`),
-- so the block a cell holds lives in exactly one continuation —
--
--     rely       `input  l d N2N_BlockFetch ? (…, MsgBlock b)`
--     guarantee  `output l d N2N_BlockFetch ! (…, MsgBlock b)`
--
-- and the carried value crosses the cell in ONE step: `wfR-Output`'s
-- guarantee at `output` is discharged from the `OK` the `input` step
-- handed the continuation (`ok c-input`), monotonised to the state the
-- guarantee is asked at.  Every other menu entry is answered `nothing`.
--
-- THE ALPHABET AND THE CARRIER ARE PULLBACKS.  The medium's guarantee
-- alphabet `medG` is everything but its ONE rely, `input _ _ _` — so it
-- INCLUDES `output _ _ _`, which the node side (`peersG`, and `nodeG`
-- shrunk to match) deliberately excludes, and the top-level union covers
-- `ioES` for `wf-Hide`'s `HideCov`.  Outside `ioES` it is total, so
-- `Sep ioES` against the node side is trivial.  `cpG`/`CarriesCp` are
-- `medG`/`Carries` read through `ιNet`, not a second enumeration.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.BlockProvenanceCopy where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl; ⊆-trans)
open import Data.Product using (_,_; proj₁)
import Data.Unit.Polymorphic as Poly
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O
import CSP.Laws.Bisim.DRCongruenceRep as DR
import CSP.Examples.Cardano_network.Parametric.AnnounceSafe as AS
import CSP.Examples.Cardano_network.Parametric.AnnounceInvariant as AI
import CSP.Examples.Cardano_network.Parametric.BlockProvenance as BP
import CSP.Examples.Cardano_network.Parametric.BlockProvenanceWfR as BPW

-- the same three parameters as every other `Parametric.BlockProvenance*` module
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  -- the SAME opens as `Network`, so `_≟_` on links/directions/ids and the `DecEq`
  -- instance inside the cell's `!`-output elaborate to the terms the cells were
  -- built with (the `with`s below have to abstract exactly those)
  open Params p
  open import CSP.Examples.Cardano_network.Base
  open import CSP.Examples.Cardano_network.Data p
  open import CSP.Examples.Cardano_network.Net p
  open import CSP.Examples.Cardano_network.Network p Payload using (copyMenu; Copy; linkCopy)
  open import CSP.Examples.Cardano_network.NetCommon p using (ιNet)
  open O {E = Net Payload} (Net-≟ {Payload}) using (pchoice)
  open import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)}
    using (sRet; sSil; sVis; sTau)
  open AS.Generic p t apiES using (Minted)
  open AI.Generic p t apiES using (WellAnnounced; wellAnnounced-mono)
  open BP.Generic p t apiES using (Carries; c-input; c-output)

  ------------------------------------------------------------------------
  -- The alphabets and the source carrier
  ------------------------------------------------------------------------

  -- THE MEDIUM'S GUARANTEE ALPHABET: everything but its one rely, the block a node's
  -- BlockFetch server peer puts on the wire (`input`, `ioES`-synchronised)
  medG : DR.Alpha (Net_Api-≟ {Payload})
  medG (_ , input _ _ _) _ = ⊥
  medG _                 _ = Poly.⊤

  -- its pullback along `ιNet`: the copy cells' alphabet at the source
  cpG : DR.Alpha (Net-≟ {Payload})
  cpG (A , e) a = medG (A , ιNet e) a

  -- the pullback of the Cardano `Carries`: which `Net` events carry which block
  CarriesCp : (at : AnyTypes (Net Payload)) → proj₁ at → Block → Set
  CarriesCp (A , e) a b = Carries (A , ιNet e) a b

  -- the source carrier, STATE-AGNOSTIC (`next = λ _ s → s`): the medium never mints.
  -- These are exactly the arguments `BlockProvenance.Rename` gives its `C1`.
  open BP.Carrier (Net-≟ {Payload}) Minted Block CarriesCp WellAnnounced
                  (λ _ s → s) _⊆_ ⊆-trans (λ _ _ → ⊆-refl)
    using (Wf; wf-⦀⋆)
  open BPW.Body (Net-≟ {Payload}) Minted Block CarriesCp WellAnnounced
                (λ _ s → s) _⊆_ ⊆-refl ⊆-trans (λ _ _ → ⊆-refl)

  ------------------------------------------------------------------------
  -- One copy cell
  ------------------------------------------------------------------------

  -- the body of one cell, one pass: `nowR` — the only offered channel is `input`,
  -- the rely, outside `cpG` (`⊥-elim`); every other menu entry is `nothing` (`()`).
  -- `stepR` — the `with` mirrors the menu's own three-way dispatch, and the relay
  -- hands the block's well-announcedness from `c-input` (rely) to `c-output`
  -- (guarantee) across the one-place buffer.  The cell has no τ and never returns.
  cpBody : ∀ {ms} (l : Link) (d : Dir) (id : IDs)
         → WfR cpG ms (λ _ _ → Poly.⊤ {0ℓ}) (pchoice (copyMenu l d id))
  cpBody l d id .nowR _ g (sVis {at = (_ , input  _ _ _)} refl _) = ⊥-elim g
  cpBody l d id .nowR _ _ (sVis {at = (_ , output _ _ _)} refl ())
  cpBody l d id .nowR _ _ (sVis {at = (_ , sndmsg _ _ _)} refl ())
  cpBody l d id .nowR _ _ (sVis {at = (_ , rcvmsg _ _ _)} refl ())
  cpBody l d id .nowR _ _ (sVis {at = (_ , tx     _ _ _)} refl ())
  cpBody l d id .nowR _ _ (sVis {at = (_ , sndack _ _ _)} refl ())
  cpBody l d id .nowR _ _ (sVis {at = (_ , rcvack _ _ _)} refl ())
  cpBody l d id .nowR _ _ (sVis {at = (_ , ack    _ _ _)} refl ())
  cpBody l d id .stepR _ (sRet ())
  cpBody l d id .stepR _ (sSil ())
  cpBody l d id .stepR _ (sTau refl ())
  cpBody l d id .stepR _ (sVis {at = (_ , output _ _ _)} refl ())
  cpBody l d id .stepR _ (sVis {at = (_ , sndmsg _ _ _)} refl ())
  cpBody l d id .stepR _ (sVis {at = (_ , rcvmsg _ _ _)} refl ())
  cpBody l d id .stepR _ (sVis {at = (_ , tx     _ _ _)} refl ())
  cpBody l d id .stepR _ (sVis {at = (_ , sndack _ _ _)} refl ())
  cpBody l d id .stepR _ (sVis {at = (_ , rcvack _ _ _)} refl ())
  cpBody l d id .stepR _ (sVis {at = (_ , ack    _ _ _)} refl ())
  -- THE RELAY: `ok c-input` is the rely, `c-output` names the guarantee.  The
  -- `with`s are NESTED, as the menu's are: a simultaneous three-way `with` abstracts
  -- only the outermost decision and leaves the inner helpers stuck.
  cpBody l d id .stepR _ (sVis {at = (_ , input l′ d′ id′)} refl br) ok with l′ ≟ l
  ... | no _     = case br of λ ()
  ... | yes refl with d′ ≟ d
  ...   | no _     = case br of λ ()
  ...   | yes refl with id′ ≟ id
  ...     | no _     = case br of λ ()
  ...     | yes refl = case br of λ { refl →
              wfR-Output (λ le′ _ → λ { c-output → wellAnnounced-mono le′ (ok c-input) })
                         (λ _ _ → wfR-Ret (λ _ → Poly.tt)) }
  cpBody l d id .retR _ ()

  -- ONE COPY CELL: a forever loop of the body
  wf-Copy : ∀ {ms} (l : Link) (d : Dir) (id : IDs) → Wf cpG ms (Copy l d id)
  wf-Copy l d id = wf-loop0 (cpBody l d id)

  ------------------------------------------------------------------------
  -- One link's bundle of cells
  ------------------------------------------------------------------------

  -- THE COPY BUNDLE of one link, over exactly its configured instances
  wf-linkCopy : ∀ {ms} (l : Link) → Wf cpG ms (linkCopy l)
  wf-linkCopy l = wf-⦀⋆ _ (linkConfig l) (λ { (d , id) → wf-Copy l d id })

  ------------------------------------------------------------------------
  -- Non-vacuity: the medium's guarantee is a real guarantee
  ------------------------------------------------------------------------

  -- the block-carrying channel the medium EMITS on is in `medG`, so `nowW` of the
  -- facts above really says "the delivered block is well-announced"; the channel it
  -- RECEIVES on is not — that is its rely, discharged by the far node's server peer
  medG-output : ∀ {l d} (x : Payload) → medG (_ , output l d N2N_BlockFetch) x
  medG-output _ = Poly.tt

  medG-input : ∀ {l d id} {x : Payload} → ¬ medG (_ , input l d id) x
  medG-input ()

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — a FIVE-NODE STAR as a `Topology` instance.
--
-- THIS IS A SCAFFOLDING TEST, NOT A SCENARIO.  Every node's application
-- logic is `Skip`, so the system built here has no interesting
-- behaviour and no property is claimed about it.  Its only purpose is
-- to check that the topology-generic layer (`Parametric.Topology`,
-- `Parametric.Node`, `Parametric.Assembly`) is genuinely parametric —
-- i.e. that it was not accidentally specialised to the four-node
-- diamond it was reverse-engineered from.  Do not mistake `starSystem`
-- for a network model of anything.
--
-- The star deliberately differs from the diamond in three ways the
-- diamond could not exercise:
--   * FIVE nodes over FOUR links (`numNodes ≢ numLinks`, and
--     `numNodes ≢ 4`), so any residual hard-coded four-ness shows up;
--   * four DEGREE-1 nodes (the leaves), whose `endpointsOf` tail is
--     EMPTY — this is the `⦀⁺ P [] = P` clause of `CSP.Operators`,
--     which no previous instance reached (see `leaf-bundle-refl`);
--   * one DEGREE-4 node (the hub), a four-deep `⦀⁺` fold, deeper than
--     any previous instance (see `hub-bundle-refl`).
--
-- There is NO faithfulness gate here and none is possible: unlike the
-- diamond, this topology has no pre-existing hand-written counterpart
-- to match, so `endpointsOf`'s list order is entirely free (any order
-- gives an equally legitimate system, `⦀` being commutative up to
-- strong bisimulation — `CSP/Laws/FD/ParallelComm.agda`).
--
-- The `Params` are this module's own (they are NOT the diamond's), so
-- nothing here depends on `FourNode.FourNodeDiamond`; that also checks
-- that `Parametric.Node`'s `apiES` parameter can be supplied afresh.
------------------------------------------------------------------------

import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.AllPairs as AP
import Data.List.Relation.Unary.All as All
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; mkTopology)

module CSP.Examples.Cardano_network.Parametric.Instances where

------------------------------------------------------------------------
-- The scenario parameters (own, not the diamond's)
------------------------------------------------------------------------

-- trivial decidable equality for the ⊤ data domains (all domains are ⊤ here: this
-- module tests the graph layer, so no payload needs to be distinguishable)
instance
  starDecEq⊤ : DecEq U.⊤
  starDecEq⊤ = record { _≟_ = λ _ _ → yes refl }

-- both directions × the four wire protocols, on every link (Leios ids have no peers)
starCfg : List (Dir × IDs)
starCfg = (lo , N2N_KeepAlive)    ∷ (hi , N2N_KeepAlive)
        ∷ (lo , N2N_ChainSync)    ∷ (hi , N2N_ChainSync)
        ∷ (lo , N2N_BlockFetch)   ∷ (hi , N2N_BlockFetch)
        ∷ (lo , N2N_TxSubmission) ∷ (hi , N2N_TxSubmission) ∷ []

-- concrete Params for the star: all data domains ⊤, FOUR links, uniform config
starParams : Params
starParams = record
  { Cookie = U.⊤ ; Block = U.⊤ ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; numLinks = 4 ; linkConfig = λ _ → starCfg
  ; decCookie = starDecEq⊤ ; decBlock = starDecEq⊤ ; decTxid = starDecEq⊤
  ; decLSlot = starDecEq⊤ ; decVoterId = starDecEq⊤ ; decLFBitmap = starDecEq⊤
  ; decVoteBlob = starDecEq⊤
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = starDecEq⊤ ; decLength = starDecEq⊤ }

open import CSP.Examples.Cardano_network.Net starParams
  using ( Link; Net_Api; Net_Api-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break )
open import CSP.Examples.Cardano_network.Data starParams using (Payload)
open import CSP.Examples.Cardano_network.NetCommon starParams
  using (CopySpecBreakableA; ioES)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Skip; _⦀_; _∥⇘_⇙_; _∖_; ⦀Fin⁺; chanSet; EventSet)

------------------------------------------------------------------------
-- The api synchronisation alphabet (this module's own `apiES`)
------------------------------------------------------------------------

-- membership of the {| all api channels |} sync set (by channel, ignoring payload)
starApiSet : AnyTypes (Net_Api Payload) → Set
starApiSet (_ , apiCS _ _ _) = ⊤
starApiSet (_ , apiBF _ _ _) = ⊤
starApiSet (_ , apiKA _ _ _) = ⊤
starApiSet (_ , apiTS _ _ _) = ⊤
starApiSet (_ , apiLN _ _ _) = ⊤
starApiSet (_ , apiLF _ _ _) = ⊤
starApiSet (_ , done _ _ _)  = ⊤
starApiSet _                 = ⊥

-- decidability of `starApiSet` membership
starApiSet-dec : (at : AnyTypes (Net_Api Payload)) → Dec (starApiSet at)
starApiSet-dec (_ , apiCS  _ _ _) = yes tt
starApiSet-dec (_ , apiBF  _ _ _) = yes tt
starApiSet-dec (_ , input  _ _ _) = no λ ()
starApiSet-dec (_ , output _ _ _) = no λ ()
starApiSet-dec (_ , sndmsg _ _ _) = no λ ()
starApiSet-dec (_ , rcvmsg _ _ _) = no λ ()
starApiSet-dec (_ , tx     _ _ _) = no λ ()
starApiSet-dec (_ , sndack _ _ _) = no λ ()
starApiSet-dec (_ , rcvack _ _ _) = no λ ()
starApiSet-dec (_ , ack    _ _ _) = no λ ()
starApiSet-dec (_ , done   _ _ _) = yes tt
starApiSet-dec (_ , apiTS  _ _ _) = yes tt
starApiSet-dec (_ , apiKA  _ _ _) = yes tt
starApiSet-dec (_ , apiLN  _ _ _) = yes tt
starApiSet-dec (_ , apiLF  _ _ _) = yes tt
starApiSet-dec (_ , break  _)     = no λ ()

-- the {| all api channels |} event set for the star
starApiES : EventSet
starApiES = chanSet starApiSet starApiSet-dec

------------------------------------------------------------------------
-- The star graph
------------------------------------------------------------------------

-- the five nodes: `hub` is node 0, `leaf l` is node `1 + l` (one per link)
hub : Fin 5
hub = fzero

-- the leaf attached to link `l`
leaf : Link → Fin 5
leaf l = fsuc l

-- the (lo-end , hi-end) pair of link `l`: the hub at `lo`, its own leaf at `hi`
-- (a single non-matching clause, which is what makes `ends-irrefl` a one-liner)
starEnds : Link → Fin 5 × Fin 5
starEnds l = hub , leaf l

-- each node's incident (link , own-direction) endpoints: the hub carries all four
-- links at `lo` (degree 4), each leaf its own single link at `hi` (degree 1, so the
-- tail is EMPTY — the `⦀⁺ P [] = P` case)
starEndpointsOf : Fin 5 → (Link × Dir) × List (Link × Dir)
starEndpointsOf fzero    = (fzero , lo)
                         , (fsuc fzero , lo)
                         ∷ (fsuc (fsuc fzero) , lo)
                         ∷ (fsuc (fsuc (fsuc fzero)) , lo) ∷ []
starEndpointsOf (fsuc l) = (l , hi) , []

-- the five-node star as a `Topology`; as in `Parametric.DiamondInstance` the
-- soundness/completeness proofs are inline pattern lambdas, because their types
-- mention the record's derived `endAt` (an extended lambda that only reduces once
-- the link and direction are concrete)
star : Topology starParams
star = record
  { numNodes-1 = 4
  ; ends = starEnds
  ; ends-irrefl = λ _ ()
  ; endpointsOf = starEndpointsOf
  ; endpoints-sound = λ { fzero _ _ (here refl) → refl
                        ; fzero _ _ (there (here refl)) → refl
                        ; fzero _ _ (there (there (here refl))) → refl
                        ; fzero _ _ (there (there (there (here refl)))) → refl
                        ; (fsuc _) _ _ (here refl) → refl }
  ; endpoints-complete = λ { _ fzero lo refl → here refl
                           ; _ fzero hi refl → here refl
                           ; _ (fsuc fzero) lo refl → there (here refl)
                           ; _ (fsuc fzero) hi refl → here refl
                           ; _ (fsuc (fsuc fzero)) lo refl → there (there (here refl))
                           ; _ (fsuc (fsuc fzero)) hi refl → here refl
                           ; _ (fsuc (fsuc (fsuc fzero))) lo refl → there (there (there (here refl)))
                           ; _ (fsuc (fsuc (fsuc fzero))) hi refl → here refl }
    -- the hub (degree 4) needs 4·3/2 = 6 pairwise `≢`s, arranged as the 3+2+1 `All`
    -- rows of an `AllPairs`; each leaf (degree 1) is the empty singleton witness
  ; endpoints-unique = λ { fzero    → AP._∷_ (All._∷_ (λ ()) (All._∷_ (λ ()) (All._∷_ (λ ()) All.[])))
                                     (AP._∷_ (All._∷_ (λ ()) (All._∷_ (λ ()) All.[]))
                                     (AP._∷_ (All._∷_ (λ ()) All.[])
                                     (AP._∷_ All.[] AP.[])))
                         ; (fsuc _) → AP._∷_ All.[] AP.[] }
  }

------------------------------------------------------------------------
-- The generic scaffolding at the star
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Parametric.Node starParams star starApiES
  using (Proc; bundleAt; linkBundles; node; systemOf)

-- the star network with trivial (`Skip`) logic at every node — a TYPECHECKING
-- WITNESS that `systemOf` builds at a five-node, four-link graph, nothing more
starSystem : Proc
starSystem = systemOf (λ _ → Skip)

-- DEGREE-1 CHECK: a leaf's bundle is exactly `bundleAt` of its ONE endpoint, with
-- no trailing `Skip` — i.e. `linkBundles` really goes through `⦀⁺ P [] = P`, the
-- clause no previous instance reached
leaf-bundle-refl : ∀ (l : Link) → linkBundles (leaf l) ≡ bundleAt (l , hi)
leaf-bundle-refl _ = refl

-- DEGREE-4 CHECK: the hub's bundle is the four-deep right-nested `⦀` chain of its
-- four `lo` endpoints — a fold deeper than any previous instance
hub-bundle-refl : linkBundles hub
                ≡ ( bundleAt (fzero , lo)
                  ⦀ ( bundleAt (fsuc fzero , lo)
                    ⦀ ( bundleAt (fsuc (fsuc fzero) , lo)
                      ⦀ bundleAt (fsuc (fsuc (fsuc fzero)) , lo))))
hub-bundle-refl = refl

------------------------------------------------------------------------
-- The assembly lemma at the star
------------------------------------------------------------------------

import CSP.Examples.Cardano_network.Parametric.Assembly as Asm
open import Semantics.FailuresDivergences
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⊑FD_; divergences)

-- `systemN-mono` instantiated at the star: FIVE node obligations (one per `Fin 5`,
-- not four), one medium obligation and one divergence-freedom obligation give the
-- whole star refinement.  The premises are HYPOTHESES — none is discharged here;
-- this is a check that the generic lemma applies at a non-diamond topology.
star-assembly : (mSpec : Proc) (nSpec lg : Fin 5 → Proc)
              → mSpec ⊑FD CopySpecBreakableA
              → (∀ n → nSpec n ⊑FD node n (lg n))
              → (∀ {s} → ¬ divergences (systemOf lg) s)
              → ((mSpec ∥⇘ ioES ⇙ ⦀Fin⁺ 4 nSpec) ∖ ioES) ⊑FD systemOf lg
star-assembly = Asm.Generic.systemN-mono starParams star starApiES

------------------------------------------------------------------------
-- A THREE-NODE LINE, built with `mkTopology` — the derivation test
--
-- The star above is hand-built: its `endpointsOf` is written out node
-- by node and its three endpoint laws are written out as terms (the
-- hub alone needing six pairwise `≢`s for `endpoints-unique`).  The
-- line below supplies ONLY `ends` plus the two hypotheses `mkTopology`
-- genuinely needs — no self-loops, no isolated nodes — and gets
-- `endpointsOf`, soundness, completeness and uniqueness derived.
--
-- A—B—C: two links, degrees 1, 2, 1.  The degree-2 middle node
-- exercises the non-empty-tail path through the derived list and the
-- two degree-1 ends exercise the empty-tail (`⦀⁺ P [] = P`) path.
--
-- There is deliberately NO `refl` gate here: the derived list's order
-- is `filter`'s order over the endpoint enumeration, which is exactly
-- the dependence that makes derivation and definitional gates
-- incompatible (see `Parametric.Topology`'s note on `mkTopology`).
--
-- Everything lives in a nested module because the line needs its own
-- `Params` (two links, not four) and hence its own instantiations of
-- `Net`/`Data`/`NetCommon`/`CSP.Operators`, whose names would other-
-- wise clash with the star's.
------------------------------------------------------------------------

module Line where

  -- concrete Params for the line: as the star's, but TWO links
  lineParams : Params
  lineParams = record
    { Cookie = U.⊤ ; Block = U.⊤ ; Txid = U.⊤ ; LSlot = U.⊤
    ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
    ; numLinks = 2 ; linkConfig = λ _ → starCfg
    ; decCookie = starDecEq⊤ ; decBlock = starDecEq⊤ ; decTxid = starDecEq⊤
    ; decLSlot = starDecEq⊤ ; decVoterId = starDecEq⊤ ; decLFBitmap = starDecEq⊤
    ; decVoteBlob = starDecEq⊤
    ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
    ; decTime = starDecEq⊤ ; decLength = starDecEq⊤ }

  -- the line's `Net`/`Data`/`NetCommon`/`CSP.Operators` instantiations.  Every name
  -- is brought in under an `L`-prefixed alias: the star's same-named notions are
  -- already in scope at the enclosing module and an inner `open` does NOT shadow
  -- them in Agda — it makes the bare name ambiguous.
  import CSP.Examples.Cardano_network.Net lineParams as LNet
  open LNet using () renaming (Link to LLink; Net_Api to LApi; Net_Api-≟ to LApi-≟)
  open import CSP.Examples.Cardano_network.Data lineParams
    using () renaming (Payload to LPayload)
  open import CSP.Examples.Cardano_network.NetCommon lineParams
    using () renaming (CopySpecBreakableA to LCopySpec; ioES to LioES)

  import CSP.Operators {E = LApi LPayload} (LApi-≟ {LPayload}) as LOp
  open LOp using () renaming ( Skip to LSkip; _∥⇘_⇙_ to _L∥⇘_⇙_; _∖_ to _L∖_
                             ; ⦀Fin⁺ to L⦀Fin⁺; chanSet to LchanSet
                             ; EventSet to LEventSet )

  -- membership of the {| all api channels |} sync set (by channel, ignoring payload);
  -- the same predicate as the star's, but over `lineParams`' `Net_Api`
  lineApiSet : AnyTypes (LApi LPayload) → Set
  lineApiSet (_ , LNet.apiCS _ _ _) = ⊤
  lineApiSet (_ , LNet.apiBF _ _ _) = ⊤
  lineApiSet (_ , LNet.apiKA _ _ _) = ⊤
  lineApiSet (_ , LNet.apiTS _ _ _) = ⊤
  lineApiSet (_ , LNet.apiLN _ _ _) = ⊤
  lineApiSet (_ , LNet.apiLF _ _ _) = ⊤
  lineApiSet (_ , LNet.done  _ _ _) = ⊤
  lineApiSet _                      = ⊥

  -- decidability of `lineApiSet` membership
  lineApiSet-dec : (at : AnyTypes (LApi LPayload)) → Dec (lineApiSet at)
  lineApiSet-dec (_ , LNet.apiCS  _ _ _) = yes tt
  lineApiSet-dec (_ , LNet.apiBF  _ _ _) = yes tt
  lineApiSet-dec (_ , LNet.input  _ _ _) = no λ ()
  lineApiSet-dec (_ , LNet.output _ _ _) = no λ ()
  lineApiSet-dec (_ , LNet.sndmsg _ _ _) = no λ ()
  lineApiSet-dec (_ , LNet.rcvmsg _ _ _) = no λ ()
  lineApiSet-dec (_ , LNet.tx     _ _ _) = no λ ()
  lineApiSet-dec (_ , LNet.sndack _ _ _) = no λ ()
  lineApiSet-dec (_ , LNet.rcvack _ _ _) = no λ ()
  lineApiSet-dec (_ , LNet.ack    _ _ _) = no λ ()
  lineApiSet-dec (_ , LNet.done   _ _ _) = yes tt
  lineApiSet-dec (_ , LNet.apiTS  _ _ _) = yes tt
  lineApiSet-dec (_ , LNet.apiKA  _ _ _) = yes tt
  lineApiSet-dec (_ , LNet.apiLN  _ _ _) = yes tt
  lineApiSet-dec (_ , LNet.apiLF  _ _ _) = yes tt
  lineApiSet-dec (_ , LNet.break  _)     = no λ ()

  -- the {| all api channels |} event set for the line
  lineApiES : LEventSet
  lineApiES = LchanSet lineApiSet lineApiSet-dec

  -- the (lo-end , hi-end) pair of each link: link 0 joins A—B, link 1 joins B—C,
  -- with node 0 = A, node 1 = B (the degree-2 middle), node 2 = C
  lineEnds : LLink → Fin 3 × Fin 3
  lineEnds fzero    = fzero , fsuc fzero
  lineEnds (fsuc _) = fsuc fzero , fsuc (fsuc fzero)

  -- the three-node line as a `Topology`.  THIS IS THE WHOLE INSTANCE: `endpointsOf`,
  -- `endpoints-sound`, `endpoints-complete` and `endpoints-unique` are all derived by
  -- `mkTopology` from `lineEnds`; only irreflexivity and one incident endpoint per
  -- node are supplied, and both are one-liners.
  line : Topology lineParams
  line = mkTopology 2 lineEnds
           (λ { fzero → λ () ; (fsuc _) → λ () })
           (λ { fzero            → (fzero      , lo) , refl
              ; (fsuc fzero)     → (fzero      , hi) , refl
              ; (fsuc (fsuc fzero)) → (fsuc fzero , hi) , refl })

  open import CSP.Examples.Cardano_network.Parametric.Node lineParams line lineApiES
    using () renaming (Proc to LProc; node to Lnode; systemOf to LsystemOf)

  -- the line network with trivial (`Skip`) logic at every node — a TYPECHECKING
  -- WITNESS that `systemOf` builds over a DERIVED `endpointsOf`
  lineSystem : LProc
  lineSystem = LsystemOf (λ _ → LSkip)

  open import Semantics.FailuresDivergences
    {E = LApi LPayload} {I = ExtI (LApi LPayload)}
    using () renaming (_⊑FD_ to _L⊑FD_; divergences to Ldivergences)

  -- `systemN-mono` instantiated at the line: THREE node obligations, one medium
  -- obligation and one divergence-freedom obligation.  The premises are HYPOTHESES —
  -- none is discharged here; this checks the generic lemma applies to a topology
  -- whose endpoint structure was derived rather than written.
  line-assembly : (mSpec : LProc) (nSpec lg : Fin 3 → LProc)
                → mSpec L⊑FD LCopySpec
                → (∀ n → nSpec n L⊑FD Lnode n (lg n))
                → (∀ {s} → ¬ Ldivergences (LsystemOf lg) s)
                → ((mSpec L∥⇘ LioES ⇙ L⦀Fin⁺ 2 nSpec) L∖ LioES) L⊑FD LsystemOf lg
  line-assembly = Asm.Generic.systemN-mono lineParams line lineApiES

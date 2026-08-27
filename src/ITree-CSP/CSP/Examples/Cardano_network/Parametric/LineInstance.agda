{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — A THREE-NODE LINE, built with `mkTopology`:
-- the DERIVATION TEST.
--
-- `Parametric.StarInstance` is hand-built: its `endpointsOf` is written
-- out node by node and its three endpoint laws are written out as terms
-- (the hub alone needing six pairwise `≢`s for `endpoints-unique`).
-- The line here supplies ONLY `ends` plus the two hypotheses
-- `mkTopology` genuinely needs — no self-loops, no isolated nodes — and
-- gets `endpointsOf`, soundness, completeness and uniqueness derived.
--
-- A—B—C: two links, degrees 1, 2, 1.  The degree-2 middle node
-- exercises the non-empty-tail path through the derived list and the
-- two degree-1 ends exercise the empty-tail (`⦀⁺ P [] = P`) path.
--
-- There is deliberately NO `refl` gate here: the derived list's order
-- is `filter`'s order over the endpoint enumeration, which is exactly
-- the dependence that makes derivation and definitional gates
-- incompatible (see `Parametric.Topology`'s note on `mkTopology`).
-- That absence is also what lets the api alphabet come from the shared
-- `Cardano_network.ApiAlphabet`: no `refl` here depends on which
-- `EventSet` record `Parametric.Node` receives.
--
-- ONE SCENARIO PER FILE.  The line needs its own `Params` (two links,
-- not four) and hence its own instantiations of
-- `Net`/`Data`/`NetCommon`/`ApiAlphabet`/`CSP.Operators`.  While it
-- shared a file with the star, every one of those names clashed with
-- the star's — an inner `open` does NOT shadow in Agda, it makes the
-- bare name ambiguous — and had to be brought in under an `L`-prefixed
-- alias.  With one `Params` per file the prefixes are gone.
------------------------------------------------------------------------

import Data.Unit as U
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; _∷_; [])
open import Relation.Nullary using (yes; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; mkTopology)

module CSP.Examples.Cardano_network.Parametric.LineInstance where

------------------------------------------------------------------------
-- The scenario parameters (own, as the star's but TWO links)
------------------------------------------------------------------------

-- trivial decidable equality for the ⊤ data domains (all domains are ⊤ here: this
-- module tests the graph layer, so no payload needs to be distinguishable)
instance
  lineDecEq⊤ : DecEq U.⊤
  lineDecEq⊤ = record { _≟_ = λ _ _ → yes refl }

-- both directions × the four wire protocols, on every link (Leios ids have no peers)
lineCfg : List (Dir × IDs)
lineCfg = (lo , N2N_KeepAlive)    ∷ (hi , N2N_KeepAlive)
        ∷ (lo , N2N_ChainSync)    ∷ (hi , N2N_ChainSync)
        ∷ (lo , N2N_BlockFetch)   ∷ (hi , N2N_BlockFetch)
        ∷ (lo , N2N_TxSubmission) ∷ (hi , N2N_TxSubmission) ∷ []

-- concrete Params for the line: all data domains ⊤, TWO links, uniform config
import Data.Maybe as PMaybe

lineParams : Params
lineParams = record
  { Cookie = U.⊤ ; Block = U.⊤ ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; numLinks = 2 ; linkConfig = λ _ → lineCfg
  ; decCookie = lineDecEq⊤ ; decBlock = lineDecEq⊤ ; decTxid = lineDecEq⊤
  ; decLSlot = lineDecEq⊤ ; decVoterId = lineDecEq⊤ ; decLFBitmap = lineDecEq⊤
  ; decVoteBlob = lineDecEq⊤
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = lineDecEq⊤ ; decLength = lineDecEq⊤
  -- Leios EB domains, inert here: both ⊤, no RB ever announces an EB
  ; EB = U.⊤ ; EBHash = U.⊤ ; decEB = lineDecEq⊤ ; decEBHash = lineDecEq⊤
  ; ebHash = λ _ → U.tt ; announcedEB = λ _ → PMaybe.nothing }

open import CSP.Examples.Cardano_network.Net lineParams using (Link; Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data lineParams using (Payload)
open import CSP.Examples.Cardano_network.NetCommon lineParams
  using (CopySpecBreakableA; ioES)

-- the {| all api channels |} alphabet, shared with every other gate-free scenario
open import CSP.Examples.Cardano_network.ApiAlphabet lineParams using (apiES)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Skip; _∥⇘_⇙_; _∖_; ⦀Fin⁺)

------------------------------------------------------------------------
-- The line graph
------------------------------------------------------------------------

-- the (lo-end , hi-end) pair of each link: link 0 joins A—B, link 1 joins B—C,
-- with node 0 = A, node 1 = B (the degree-2 middle), node 2 = C
lineEnds : Link → Fin 3 × Fin 3
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

------------------------------------------------------------------------
-- The generic scaffolding at the line
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Parametric.Node lineParams line apiES
  using (Proc; node; systemOf)

-- the line network with trivial (`Skip`) logic at every node — a TYPECHECKING
-- WITNESS that `systemOf` builds over a DERIVED `endpointsOf`
lineSystem : Proc
lineSystem = systemOf (λ _ → Skip)

------------------------------------------------------------------------
-- The assembly lemma at the line
------------------------------------------------------------------------

import CSP.Examples.Cardano_network.Parametric.Assembly as Asm
open import Semantics.FailuresDivergences
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⊑FD_; divergences)

-- `systemN-mono` instantiated at the line: THREE node obligations, one medium
-- obligation and one divergence-freedom obligation.  The premises are HYPOTHESES —
-- none is discharged here; this checks the generic lemma applies to a topology
-- whose endpoint structure was derived rather than written.
line-assembly : (mSpec : Proc) (nSpec lg : Fin 3 → Proc)
              → mSpec ⊑FD CopySpecBreakableA
              → (∀ n → nSpec n ⊑FD node n (lg n))
              → (∀ {s} → ¬ divergences (systemOf lg) s)
              → ((mSpec ∥⇘ ioES ⇙ ⦀Fin⁺ 2 nSpec) ∖ ioES) ⊑FD systemOf lg
line-assembly = Asm.Generic.systemN-mono lineParams line apiES

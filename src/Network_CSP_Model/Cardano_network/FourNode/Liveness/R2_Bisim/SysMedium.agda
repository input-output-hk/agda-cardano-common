{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R1 — MEDIUM sub-decode (`Praos.SysMedium`).
--
-- The FIRST genuine piece of the whole-system decode `⟦_⟧ : SysState →
-- NetProc` whose `dec-init : ⟦ initial ⟧ ≡ breakableSystem` is the LHS of the
-- R2 bisim `breakableSystem ≈DR abstractSystem`.  `breakableSystem` and
-- `abstractSystem` share the SAME medium `CopySpecBreakableA`, so the medium
-- decode must track the medium's REAL position (not just be inert), or a
-- medium-only step in the R2 bisim could not be matched by a `SysState` move.
--
-- `breakableSystem`'s medium is `CopySpecBreakableA = ⦀Fin numLinks
-- breakableLinkA`, with `breakableLinkA l = linkMediumA l △ (break l ⟶₀
-- Skip)`, `linkMediumA l = RenNet.renameMap (linkCopy l)`, and `linkCopy l =
-- ⦀⋆ (map Copy (linkConfig l))`.  Each copy cell `Copy l d id = loop0
-- (pchoice (copyMenu l d id))` accepts `input l d id ? x` then emits `output
-- l d id ! x` and loops.  So the REAL per-cell state is a phase
-- `{ empty | full x }` (x : Payload), aligned to the link's configured
-- `(Dir × IDs)` instances, plus a per-link `break` flag.
--
-- The decode rebuilds `linkCopy l` cell-by-cell over the Net Payload
-- alphabet, THEN applies the SAME `RenNet.renameMap` and `△ (break l ⟶₀
-- Skip)` (renameMap is corecursive and does NOT distribute over `⦀⋆`, so the
-- rename must wrap the whole reconstructed fold, exactly as `linkMediumA`
-- does).  A `full x` cell names its post-`input` derivative with the `succV`
-- successor trick (copied from `PerLink.Decode`), avoiding the
-- `iter`-`bind`-wrapped `loop0` normal form.  `decMed-home` is `refl`:
-- at the initial (all-`empty`, unbroken) state every cell decode reduces to
-- `Copy l d id`, so the fold is `linkCopy l` and the whole cell is
-- `breakableLinkA l` — no forcing of the composite tree to WHNF.
--
-- No postulates, holes, or `--allow-unsolved-metas` (R1 must be genuine).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; AnyTypes; ExtI; NodeKind; react)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium (blkA : Block₃) where

open PTree

------------------------------------------------------------------------
-- The concrete model under study (Phase-1, `examples/praos_liveness`).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using (p)
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p using (numLinks; linkConfig)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)
open import CSP.Examples.Cardano_network.Net p
  using ( Net; Net-≟; Net_Api; Net_Api-≟; Link; input; output; break )
open import CSP.Examples.Cardano_network.Data p using (Payload; DecEq-Payload)
open import CSP.Examples.Cardano_network.NetCommon p
  using ( CopySpecBreakableA; breakableLinkA; ιNet; ιNet⁻¹; ιNet-linv )
open import CSP.Examples.Cardano_network.Network p Payload using (Copy)

-- the SAME renaming NetCommon's `linkMediumA` uses (re-instantiated with the
-- SAME ι/ι⁻¹/ι-linv, so `renameMap (linkCopy l)` matches `linkMediumA l`)
import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload}
  ιNet ιNet⁻¹ ιNet-linv as RenNet

-- Net_Api operators (the whole-system alphabet): interrupt, prefix, ⦀Fin
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( ⦀Fin; Skip; _△_; Prefix₀ )

-- Net Payload operators (the pre-rename copy medium): the `⦀⋆` fold
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆ )

-- the whole-system process type (same alias as the spike / `breakableSystem`)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the pre-rename copy-medium process type (Net Payload alphabet)
NetProcN : Set₁
NetProcN = PTree (Net Payload) (ExtI (Net Payload)) (⊤ {0ℓ})

------------------------------------------------------------------------
-- Visible-successor helper `succV` (copied verbatim from
-- `PerLink.Decode`): it COMPUTES the derivative of a process along one
-- offered visible event, naming a stepped leaf without writing its
-- `iter`-`bind`-wrapped `loop0` normal form by hand.
------------------------------------------------------------------------

-- the copy-cell return type (unit on √)
NetR : Set
NetR = ⊤ {0ℓ}

-- the visible-offer map of a node (empty for non-react nodes)
vis-of : NodeKind (Net Payload) (ExtI (Net Payload)) NetR
       → (at : AnyTypes (Net Payload)) → proj₁ at → Maybe NetProcN
vis-of (react v _) = v
vis-of _           = λ _ _ → nothing

-- visible successor of `q` along `at`/`a` (identity if not offered)
succV : NetProcN → (at : AnyTypes (Net Payload)) → proj₁ at → NetProcN
succV q at a with vis-of (PTree.force q) at a
... | just t  = t
... | nothing = q

------------------------------------------------------------------------
-- Medium abstract state: per link, the phase of each configured copy cell
-- plus a break flag.
------------------------------------------------------------------------

-- one copy cell's phase: `empty` (idle, offering `input`), `full x` (holding
-- payload `x`, offering `output`), or `draining x` (the post-`output` transient
-- that has already delivered `x` and does one loop-back `sil` to `Copy l d id`)
data CopyPhase : Set where
  empty    : CopyPhase
  full     : Payload → CopyPhase
  draining : Payload → CopyPhase

-- the per-link medium cell state: the phase of each `(d, id)` copy cell and
-- whether the link's `break` event has already fired (`true` ⇒ terminated)
record MedState : Set where
  constructor mkMed
  field
    phase  : Link → Dir → IDs → CopyPhase
    broken : Link → Bool
open MedState public

------------------------------------------------------------------------
-- Per-cell, per-link and whole-medium decode.
------------------------------------------------------------------------

-- decode one copy cell: `empty` is the loop head `Copy l d id`; `full x` is
-- its post-`input` derivative (offering `output l d id ! x`), named by `succV`;
-- `draining x` is the post-`output` derivative — `succV` of `full x` along the
-- `output l d id ! x` step — i.e. `iter-bind (Skip >>= …) step`, whose force is
-- the loop-back node `sil (Copy l d id)` (DEFINITIONALLY the real derivative; no
-- WHNF is forced here, exactly as `full x` names its successor symbolically)
decCopy : (l : Link) (d : Dir) (id : IDs) → CopyPhase → NetProcN
decCopy l d id empty        = Copy l d id
decCopy l d id (full x)     = succV (Copy l d id) (Payload , input l d id) x
decCopy l d id (draining x) =
  succV (succV (Copy l d id) (Payload , input l d id) x) (Payload , output l d id) x

-- decode one link's breakable cell: unbroken ⇒ the reconstructed copy fold
-- renamed into `Net_Api`, interrupted by `break l` (i.e. `breakableLinkA l`
-- at the all-`empty` phase); broken ⇒ the post-`break` `Skip` continuation
decLink : (l : Link) → (Dir → IDs → CopyPhase) → Bool → NetProc
decLink l ph false =
  RenNet.renameMap (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))
    △ (break l ⟶₀ Skip)
decLink l ph true  = Skip

-- decode the whole breakable medium: rebuild `⦀Fin numLinks breakableLinkA`
-- cell by cell, each link selected by its per-link state (GENUINE `⦀Fin`).
decMed : MedState → NetProc
decMed m = ⦀Fin numLinks (λ l → decLink l (phase m l) (broken m l))

------------------------------------------------------------------------
-- Initial state and the genuine medium home-equality.
------------------------------------------------------------------------

-- the initial medium: every configured cell `empty`, every link unbroken
initMed : MedState
initMed = mkMed (λ _ _ _ → empty) (λ _ → false)

-- MEDIUM home-lemma, GENUINE and `refl`: at the all-`empty`/unbroken state
-- each cell decode `decCopy l d id empty` is `Copy l d id`, so the fold is
-- `linkCopy l`, its rename is `linkMediumA l`, and the whole link is
-- `breakableLinkA l`; hence the composite is `⦀Fin numLinks breakableLinkA
-- = CopySpecBreakableA` by η — WITHOUT forcing the composite tree to WHNF.
decMed-home : decMed initMed ≡ CopySpecBreakableA
decMed-home = refl

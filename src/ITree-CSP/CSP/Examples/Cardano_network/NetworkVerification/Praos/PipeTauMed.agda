{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the MEDIUM-τ half of the `TauStep` discharge
-- (`Praos.PipeTauMed`).
--
-- `PipeStepEmit.stepEmitFrom` folds a per-τ preservation combinator `TauStep l`
-- across the hidden τ-runs of a weak move.  A hidden τ is EITHER a medium-τ
-- (autonomous drain-to-empty, `flipCell`) OR an io-sync (fill / client-read
-- drain).  This module discharges the MEDIUM-τ case as the light,
-- cone-free preservation reflector `τpreserve-med` (mirror
-- `PipeClassCell.τreflect-med-classcell`, but PRODUCING the
-- `PipeInv⁺`-preservation map instead of a Fix/Adv report).
--
-- A medium-τ moves NO node (`s′ = mkSys m′ (nA s) … (nD s)`), so all three
-- drivers and both BF clients of every leg are `refl`.  The single drained cell
-- key `(i,d₀,id₀)` is DECIDED against leg-`l`'s up/dn cell keys by `_≟_` (exactly
-- `cell-drain-class`'s dispatch): if it is leg-`l`'s UPSTREAM cell going
-- `draining → empty`, apply `PipeIoHandoff.pipeInv⁺-up-empty` (`cellUp l s′ ≡
-- empty` by `refl` once the sub-key matches); if it is the DOWNSTREAM cell,
-- `pipeInv⁺-dn-empty`; otherwise every leg cell is FIXED and `pipeInv⁺-frame`
-- (all seven `refl`) carries `PipeInv⁺` across.  No io-source is needed here (an
-- emptied cell's coupling clause is vacuous).  Pure phase logic; imports only
-- the light medium machinery (no node cone).  No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import Class.DecEq using ( DecEq; _≟_ )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeTauMed (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; IDs; hi; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( CopyPhase; MedState; mkMed; phase; broken; decMed; empty )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( NetProc; absNodesOf; nodesOf; lift-med-whole-τ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( PipeInv⁺; pipeInv⁺-frame; cellUp; cellDn )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeIoHandoff blkA
  using ( pipeInv⁺-up-empty; pipeInv⁺-dn-empty )

------------------------------------------------------------------------
-- The per-leg preservation DECISION for a medium-τ drain at cell key
-- `(i,d₀,id₀)`, on the built successor `s′` (nodes unchanged).  Mirror
-- `cell-drain-class`'s nested `_≟_` dispatch, but emit the matching
-- `PipeIoHandoff` core.  All seven frame equalities are `refl`: the drivers /
-- clients are node-fixed, and the non-drained leg cells reduce through
-- `phase-upd`/`flipCell` to their source (`_≟_` being a deterministic function).
------------------------------------------------------------------------

-- the medium-τ SUCCESSOR state (drain of key `(i,d₀,id₀)`, nodes unchanged)
drainSucc : SysState → Link → Dir → IDs → SysState
drainSucc s i d₀ id₀ =
  mkSys (mkMed (phase-upd (phase (med s)) i (flipCell (phase (med s) i) d₀ id₀))
               (broken (med s)))
        (nA s) (nB s) (nC s) (nD s)

-- ONE cell of the drained medium: either FIXED (equals its source, when the key
-- misses the drained cell) or EMPTIED (with the hit-witness `kl ≡ i`, so two
-- distinct query links cannot both be emptied).  The `_≟_` dispatch is
-- `cell-drain-class`'s, but the GOAL type carries the `phase-upd`/`flipCell`
-- term, so after each match the term reduces (which inline `refl`s could not).
cell-drain-eq : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                (kl : Link) (kd : Dir) (kid : IDs)
  → (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀) kl kd kid ≡ phase m kl kd kid)
    ⊎ ((kl ≡ i) × (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀) kl kd kid ≡ empty))
cell-drain-eq m i d₀ id₀ kl kd kid with kl ≟ i
... | no  _ = inj₁ refl
... | yes refl with kd ≟ d₀ | kid ≟ id₀
...   | yes refl | yes refl = inj₂ (refl , refl)
...   | no  _    | _        = inj₁ refl
...   | yes refl | no  _    = inj₁ refl

-- leg-`l`'s two cell keys are distinct links, so they can never be emptied
-- by the SAME medium-τ (`_≟_` on the concrete `Link` literals reduces)
linkAB≢linkBD : linkAB ≡ linkBD → ⊥
linkAB≢linkBD ()

linkAC≢linkCD : linkAC ≡ linkCD → ⊥
linkAC≢linkCD ()

-- leg-`l` preservation across the drain of key `(i,d₀,id₀)` on `drainSucc`.
-- Read the up/dn leg cells off `cell-drain-eq`; at most one is emptied.  Cased
-- on `l` at the top so `cellUp l`/`cellDn l` reduce to the concrete link keys
-- and each `≡` aligns directly with a `cell-drain-eq` result.
drain-preserve : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
  → PipeInv⁺ l s → PipeInv⁺ l (drainSucc s i d₀ id₀)
drain-preserve legBD s i d₀ id₀ pinv
  with cell-drain-eq (med s) i d₀ id₀ linkAB hi N2N_BlockFetch
     | cell-drain-eq (med s) i d₀ id₀ linkBD hi N2N_BlockFetch
... | inj₁ ufix | inj₁ dfix =
      pipeInv⁺-frame    legBD s (drainSucc s i d₀ id₀)
        refl refl refl (sym ufix) (sym dfix) refl refl pinv
... | inj₂ (_ , uemp) | inj₁ dfix =
      pipeInv⁺-up-empty legBD s (drainSucc s i d₀ id₀)
        refl refl refl (sym dfix) refl refl uemp pinv
... | inj₁ ufix | inj₂ (_ , demp) =
      pipeInv⁺-dn-empty legBD s (drainSucc s i d₀ id₀)
        refl refl refl (sym ufix) refl refl demp pinv
... | inj₂ (ui , _) | inj₂ (di , _) =
      ⊥-elim (linkAB≢linkBD (trans ui (sym di)))
drain-preserve legCD s i d₀ id₀ pinv
  with cell-drain-eq (med s) i d₀ id₀ linkAC hi N2N_BlockFetch
     | cell-drain-eq (med s) i d₀ id₀ linkCD hi N2N_BlockFetch
... | inj₁ ufix | inj₁ dfix =
      pipeInv⁺-frame    legCD s (drainSucc s i d₀ id₀)
        refl refl refl (sym ufix) (sym dfix) refl refl pinv
... | inj₂ (_ , uemp) | inj₁ dfix =
      pipeInv⁺-up-empty legCD s (drainSucc s i d₀ id₀)
        refl refl refl (sym dfix) refl refl uemp pinv
... | inj₁ ufix | inj₂ (_ , demp) =
      pipeInv⁺-dn-empty legCD s (drainSucc s i d₀ id₀)
        refl refl refl (sym ufix) refl refl demp pinv
... | inj₂ (ui , _) | inj₂ (di , _) =
      ⊥-elim (linkAC≢linkCD (trans ui (sym di)))

------------------------------------------------------------------------
-- The MEDIUM-τ preservation reflector (mirror
-- `PipeClassCell.τreflect-med-classcell`): invert the medium-τ, build the
-- reachable successor `r′`, and emit the leg-`l` preservation via
-- `drain-preserve`.
------------------------------------------------------------------------

τpreserve-med : (l : TwoLegs) (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (PipeInv⁺ l (toSys r) → PipeInv⁺ l (toSys r′))
-- NB one `let`, no `with`/`where`: since this module became
-- `(blkA : Block₃)`-parameterised, a `with`/`where` clause abstracts the block
-- out of the imported `PipeInv` copies and the abstracted goal stops
-- converting ("one is a variable and one a defined identifier").
τpreserve-med l r {M} {M′} ms Meq =
  let (i , d₀ , id₀ , x , drainEq , M′≡) = medium-τ-inv-wt (med (toSys r)) ms
      s′ : SysState
      s′ = drainSucc (toSys r) i d₀ id₀
      wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
      wrun = wτ (τ*-step
               (lift-med-whole-τ (decMed (med (toSys r))) (nodesOf (toSys r))
                 (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms))
               τ*-refl)
      r′ : RState
      r′ = mkR s′ (rStepʷ (reach r) wrun)
      Meq′ : M ≡ radec r′
      Meq′ = trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES) M′≡)
  in  r′ , Meq′ , drain-preserve l (toSys r) i d₀ id₀

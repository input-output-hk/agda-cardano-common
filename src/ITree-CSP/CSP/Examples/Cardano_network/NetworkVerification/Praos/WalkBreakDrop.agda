{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the medium BREAK budget-DROP (sub-lemma 1 of `deliver`).
--
-- A visible `break l` event of the abstract medium `decMed m` fires exactly
-- ONE still-UNBROKEN link: a broken link decodes to `Skip` (= `ret`) which
-- offers nothing (`ret-no-ev`), so the fired link's `broken` flag was `false`
-- and flips `false → true`.  Hence the finite `breakBudget m` (the number of
-- the four diamond links still unbroken, `Walk.breakBudget`) strictly DROPS.
--
-- This is the arithmetic core the `break` branch of the `deliver` walk
-- classifier feeds into `Walk.μTot-break` (`breakBudget ↓`, `μG1`/`μG2` fixed
-- by the medium leaving the nodes untouched ⇒ `μTot ↓`).  It RE-MIRRORS the
-- frozen `SysRoute.medium-break-ev-inv` (never edited) for the `M ≡ decMed m′`
-- reconstruction, ADDING the strict `breakBudget m′ < breakBudget m` drop
-- (extracted via a `broken m i ≡ false` witness the frozen inversion erases).
--
-- LIGHT (`SysRoute`/`SysMedium`/`SysOracle*` primitives only, no SysBisim
-- cone).  No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Bool using ( Bool; true; false; not )
open import Data.Nat using ( _<_; _≤_ )
open import Data.Nat.Properties using ( ≤-refl; +-monoʳ-< )
open import Data.Fin using ( Fin; #_ ) renaming ( zero to fzero; suc to fsuc )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Nullary using ( ¬_; yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans; cong )

open import Process_Trees using ( PTree; ExtI )
open import Class.DecEq using ( _≟_ )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkBreakDrop (blkA : Block₃) where

------------------------------------------------------------------------
-- The model, the medium decode, the break inversion, and the budget.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; break )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; IDs )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( ⦀Fin; Skip )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

-- the medium state, its decode, and the per-link decode
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( MedState; mkMed; phase; broken; decLink; decMed; CopyPhase; NetProc )
-- the frozen break inversion + the `broken`-flip successor + reconstruction
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysRoute blkA
  using ( broken-upd; link-break-chan; break-noBoth; recon-decMed-brk )
-- the four-link interleave ev-inversion + the `ret` no-event refuter
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( ⦀Fin-ev-inv; ret-no-ev )
-- the positional finite update (target of `⦀Fin-ev-inv`)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA
  using ( finUpd )
-- the whole-trace break budget (the descent's break summand)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA
  using ( breakBudget; b2n; linkBudget )

------------------------------------------------------------------------
-- A `break` step forces its link UNBROKEN.
--
-- `decLink i ph true = Skip` (= `ret`) offers no visible event, so a `break`
-- of `decLink i ph b` forces `b ≡ false` (the `true` case is refuted by
-- `ret-no-ev`, mirroring the frozen `link-break-chan`'s `true` clause).
------------------------------------------------------------------------

link-broken-false : (i : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l : Link} {a : ⊤₀} {M : NetProc}
  → decLink i ph b ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M → b ≡ false
link-broken-false i ph true  step = ⊥-elim (ret-no-ev {P = decLink i ph true} refl step)
link-broken-false i ph false step = refl

------------------------------------------------------------------------
-- `broken-upd` hit / miss (mirror the `with j ≟ i` shape of the frozen
-- `SysRoute.brokenUpd-finUpd`, so they hold WITHOUT relying on `_≟_`
-- reduction on concrete links).
------------------------------------------------------------------------

-- the updated link now reads `true`
bupd-hit : (brk : Link → Bool) (i : Link) → broken-upd brk i i ≡ true
bupd-hit brk i with i ≟ i
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

-- every other link is unchanged
bupd-miss : (brk : Link → Bool) (i j : Link) → j ≢ i → broken-upd brk i j ≡ brk j
bupd-miss brk i j j≢i with j ≟ i
... | yes p  = ⊥-elim (j≢i p)
... | no _   = refl

------------------------------------------------------------------------
-- The budget arithmetic: flipping an UNBROKEN link's flag drops the four-link
-- `breakBudget` by exactly one.  Case on the fired link (`Link = Fin 4`): its
-- summand goes `1 → 0` (`broken m i ≡ false` ⇒ `b2n (not false) = 1`, and
-- `bupd-hit` ⇒ `b2n (not true) = 0`), the other three stay fixed (`bupd-miss`).
------------------------------------------------------------------------

budget-drop : (m : MedState) (i : Link) → broken m i ≡ false
  → breakBudget (mkMed (phase m) (broken-upd (broken m) i)) < breakBudget m
budget-drop m fzero ef
  rewrite ef
        | bupd-hit  (broken m) fzero
        | bupd-miss (broken m) fzero linkAC (λ ())
        | bupd-miss (broken m) fzero linkBD (λ ())
        | bupd-miss (broken m) fzero linkCD (λ ())
        = ≤-refl
budget-drop m (fsuc fzero) ef
  rewrite ef
        | bupd-hit  (broken m) (fsuc fzero)
        | bupd-miss (broken m) (fsuc fzero) linkAB (λ ())
        | bupd-miss (broken m) (fsuc fzero) linkBD (λ ())
        | bupd-miss (broken m) (fsuc fzero) linkCD (λ ())
        = +-monoʳ-< (b2n (not (broken m fzero))) ≤-refl
budget-drop m (fsuc (fsuc fzero)) ef
  rewrite ef
        | bupd-hit  (broken m) (fsuc (fsuc fzero))
        | bupd-miss (broken m) (fsuc (fsuc fzero)) linkAB (λ ())
        | bupd-miss (broken m) (fsuc (fsuc fzero)) linkAC (λ ())
        | bupd-miss (broken m) (fsuc (fsuc fzero)) linkCD (λ ())
        = +-monoʳ-< (b2n (not (broken m fzero)))
            (+-monoʳ-< (b2n (not (broken m (fsuc fzero)))) ≤-refl)
budget-drop m (fsuc (fsuc (fsuc fzero))) ef
  rewrite ef
        | bupd-hit  (broken m) (fsuc (fsuc (fsuc fzero)))
        | bupd-miss (broken m) (fsuc (fsuc (fsuc fzero))) linkAB (λ ())
        | bupd-miss (broken m) (fsuc (fsuc (fsuc fzero))) linkAC (λ ())
        | bupd-miss (broken m) (fsuc (fsuc (fsuc fzero))) linkBD (λ ())
        = +-monoʳ-< (b2n (not (broken m fzero)))
            (+-monoʳ-< (b2n (not (broken m (fsuc fzero))))
              (+-monoʳ-< (b2n (not (broken m (fsuc (fsuc fzero))))) ≤-refl))

------------------------------------------------------------------------
-- The medium break budget-DROP: a `break l` of `decMed m` lands on a medium
-- `m′` (the frozen `broken`-flip successor) with `M ≡ decMed m′` AND a strict
-- `breakBudget m′ < breakBudget m`.  RE-MIRRORS `SysRoute.medium-break-ev-inv`
-- (`⦀Fin-ev-inv` peels the four-link interleave, `link-break-chan` reads the
-- fired `Skip`, `recon-decMed-brk` rebuilds the `MedState`), adding the drop.
------------------------------------------------------------------------

medium-break-drop : (m : MedState) (l : Link) {a : ⊤₀} {M : NetProc}
  → decMed m ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → Σ[ m′ ∈ MedState ] (M ≡ decMed m′) × (breakBudget m′ < breakBudget m)
medium-break-drop m l step
    with ⦀Fin-ev-inv numLinks (λ i → decLink i (phase m i) (broken m i)) (break-noBoth m) step
... | i , Mi , linkStep , Meq
    with link-break-chan i (phase m i) (broken m i) linkStep
       | link-broken-false i (phase m i) (broken m i) linkStep
...   | _ , MiSkip | brkFalse =
        mkMed (phase m) (broken-upd (broken m) i)
      , trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                     (finUpd (λ k → decLink k (phase m k) (broken m k)) i z)) MiSkip)
                 (recon-decMed-brk m i))
      , budget-drop m i brkFalse

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the KEY-EXPOSING medium io inversion
-- (`Praos.PipeMedKey`), sub-obligation (a) of the `PipeInvProd.TauIoS` arm.
--
-- `WalkConvEvInv.medium-ev-inv-wt` returns the touched cell key `(i,d₀,id₀)`
-- and the new phase `np`, but its STATEMENT does not tie either to the FIRED
-- LABEL: the proof cases on the label at `decLink-ev-inv-wt` and then discards
-- it.  So a consumer that holds a node-side step at a CONCRETE key — e.g.
-- `PipeSrvFire.fill-{up,dn}-nodes`, which needs
-- `input (upLink l) hi N2N_BlockFetch ! pl` at the LEG's own key — cannot line
-- the two sides up and the io `TauStep` cannot be assembled.
--
-- THIS leaf re-mirrors the same inversion chain
--
--     cell-{in,out}-key  →  cellFlip-{in,out}  →  decLink-ev-{in,out}-key
--                        →  medium-ev-{in,out}-key
--
-- but SPECIALISED to the two io label shapes (`input l₀ d₀ id₀ ! x` and
-- `output l₀ d₀ id₀ ! x`), which is exactly what removes the gap: the fired
-- key IS the label's key, the new phase IS `full x` / `draining x`, and the
-- SOURCE phase is pinned too (`empty` resp. `full x`).  Specialising also makes
-- the per-cell step cheap — no key case split survives, because
-- `SysOracle_NodeTauEv.cell-key-{empty,full}` already pins the channel and the
-- concrete `offer-{empty,full}` menus read the successor off.
--
-- Nothing here is weaker than `medium-ev-inv-wt`: `cellWt (full x) ≡
-- suc (cellWt empty)` and `cellWt (draining x) ≡ suc (cellWt (full x))` both
-- hold by `refl`, so the weight rise is recoverable from the pinned phases.
--
-- Also provided (deliberate over-provisioning for the (d) assembly): `setRead`,
-- the decidable per-key read of an io successor's medium — an ARBITRARY cell
-- key is either untouched (its phase is literally the source one) or IS the
-- fired key (its phase is `np`).
--
-- Imported by nothing yet.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Bool using ( Bool; true; false )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.List using ( List; []; _∷_; length; lookup; updateAt; map )
open import Data.Fin using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong )

open import Class.DecEq using ( DecEq; _≟_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeMedKey (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Net; Net-≟; Link; break; input; output )
open import CSP.Examples.Cardano_network.Data p using ( Payload; DecEq-Payload )
open import CSP.Examples.Cardano_network.NetCommon p
  using ( ιNet; ιNet⁻¹; ιNet-linv; ioES )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi; IDs
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive
  ; N2N_LeiosNotify; N2N_LeiosFetch )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as OpA
open OpA using ( _△_; Skip; Prefix₀; ⦀Fin; EventSet )
open EventSet using ( mem )
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed; decLink; decCopy; MedState; mkMed; phase; broken
        ; CopyPhase; empty; full; draining; NetProcN )

-- R2's frozen inversion primitives (all re-derivations reuse these verbatim)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( NetProc; △-ev-elim; finUpd; fold-react; phase-upd; recon-decMed
               ; ReactF; mkReactF )
open STC.MedNO using ( force-renameMap-react; renameMap-ev-reflect-ι )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA as SNT
open SNT using ( ret-no-ev; nothing-absurd; cell-view; offer-empty; offer-full
               ; full-menu-input; full-menu-output-val; draining-evL
               ; CellChan; chIn; chOut; cell-key-empty; cell-key-full
               ; ⦀⋆-ev-inv; ⦀Fin-ev-inv; cell-noBoth; link-io-diff; setCell )

-- the medium's alphabet rename (SAME instance `decLink` is defined with)
import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload}
  ιNet ιNet⁻¹ ιNet-linv as RenNet
open RenNet using ( renameMap )

------------------------------------------------------------------------
-- (1) PER-CELL, at the two concrete io label shapes.  The key is pinned by the
-- frozen `cell-key-{empty,full}` channel readers; the source phase and the
-- successor are then read straight off the concrete offer menus.
------------------------------------------------------------------------

-- an `input l₀ d₀ id₀ ! x` fire of the copy cell at key `(l,d,id)` pins the
-- fired key to the cell's OWN key, forces the cell to have been `empty`, and
-- lands it on `full x`
cell-in-key : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload} {Mk : NetProcN}
  → decCopy l d id ph LN.─[ LN.ev (LN.evl (LN.evLabel Payload (input l₀ d₀ id₀) x)) ]─► Mk
  → (l₀ ≡ l) × (d₀ ≡ d) × (id₀ ≡ id) × (ph ≡ empty)
    × (Mk ≡ decCopy l d id (full x))
cell-in-key l d id empty {x = x} step with cell-key-empty l d id step
... | chIn = refl , refl , refl , refl ,
             just-injective (trans (sym (cell-view l d id empty step))
                                   (offer-empty l d id x))
cell-in-key l d id (full y) step =
  ⊥-elim (nothing-absurd (trans (sym (full-menu-input l d id y))
                                (cell-view l d id (full y) step)))
cell-in-key l d id (draining y) step = ⊥-elim (draining-evL l d id y step)

-- an `output l₀ d₀ id₀ ! x` fire of the copy cell at key `(l,d,id)` pins the
-- fired key, forces the cell to have held exactly `x` (`full x`), and lands it
-- on `draining x`
cell-out-key : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload} {Mk : NetProcN}
  → decCopy l d id ph LN.─[ LN.ev (LN.evl (LN.evLabel Payload (output l₀ d₀ id₀) x)) ]─► Mk
  → (l₀ ≡ l) × (d₀ ≡ d) × (id₀ ≡ id) × (ph ≡ full x)
    × (Mk ≡ decCopy l d id (draining x))
cell-out-key l d id empty (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-out-key l d id (full y) {x = x} step with cell-key-full l d id y step
... | chOut with x ≟ y
...   | yes refl = refl , refl , refl , refl ,
                   just-injective (trans (sym (cell-view l d id (full y) step))
                                         (offer-full l d id y))
...   | no ¬p = ⊥-elim (nothing-absurd
                  (trans (sym (full-menu-output-val l d id y ¬p))
                         (cell-view l d id (full y) step)))
cell-out-key l d id (draining y) step = ⊥-elim (draining-evL l d id y step)

------------------------------------------------------------------------
-- (2) PER-LINK CELL FOLD.  Mirror of `WalkConvEvInv.cellFlipEv-wt`'s 12
-- positional clauses, at the two concrete label shapes: the positional
-- `updateAt` equals the KEY-set `map` at the LABEL's own key.
------------------------------------------------------------------------

-- the fired position of a link's copy fold, on an `input` label: the label's
-- key is the position's key and the positional update is the `setCell` update
cellFlip-in : (l : Link) (ph : Dir → IDs → CopyPhase)
    (k : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))))
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload} {Mk : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k
      LN.─[ LN.ev (LN.evl (LN.evLabel Payload (input l₀ d₀ id₀) x)) ]─► Mk
  → (l₀ ≡ l) × (ph d₀ id₀ ≡ empty)
    × (updateAt (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k (λ _ → Mk)
        ≡ map (λ { (d , id) → decCopy l d id (setCell ph d₀ id₀ (full x) d id) }) (linkConfig l))
cellFlip-in l ph fzero cs
  with cell-in-key l lo N2N_KeepAlive (ph lo N2N_KeepAlive) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc fzero) cs
  with cell-in-key l hi N2N_KeepAlive (ph hi N2N_KeepAlive) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc fzero)) cs
  with cell-in-key l lo N2N_ChainSync (ph lo N2N_ChainSync) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc fzero))) cs
  with cell-in-key l hi N2N_ChainSync (ph hi N2N_ChainSync) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc (fsuc fzero)))) cs
  with cell-in-key l lo N2N_BlockFetch (ph lo N2N_BlockFetch) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) cs
  with cell-in-key l hi N2N_BlockFetch (ph hi N2N_BlockFetch) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) cs
  with cell-in-key l lo N2N_TxSubmission (ph lo N2N_TxSubmission) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) cs
  with cell-in-key l hi N2N_TxSubmission (ph hi N2N_TxSubmission) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) cs
  with cell-in-key l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) cs
  with cell-in-key l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) cs
  with cell-in-key l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-in l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) cs
  with cell-in-key l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl

-- the fired position of a link's copy fold, on an `output` label
cellFlip-out : (l : Link) (ph : Dir → IDs → CopyPhase)
    (k : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))))
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload} {Mk : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k
      LN.─[ LN.ev (LN.evl (LN.evLabel Payload (output l₀ d₀ id₀) x)) ]─► Mk
  → (l₀ ≡ l) × (ph d₀ id₀ ≡ full x)
    × (updateAt (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k (λ _ → Mk)
        ≡ map (λ { (d , id) → decCopy l d id (setCell ph d₀ id₀ (draining x) d id) }) (linkConfig l))
cellFlip-out l ph fzero cs
  with cell-out-key l lo N2N_KeepAlive (ph lo N2N_KeepAlive) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc fzero) cs
  with cell-out-key l hi N2N_KeepAlive (ph hi N2N_KeepAlive) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc fzero)) cs
  with cell-out-key l lo N2N_ChainSync (ph lo N2N_ChainSync) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc fzero))) cs
  with cell-out-key l hi N2N_ChainSync (ph hi N2N_ChainSync) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc (fsuc fzero)))) cs
  with cell-out-key l lo N2N_BlockFetch (ph lo N2N_BlockFetch) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) cs
  with cell-out-key l hi N2N_BlockFetch (ph hi N2N_BlockFetch) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) cs
  with cell-out-key l lo N2N_TxSubmission (ph lo N2N_TxSubmission) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) cs
  with cell-out-key l hi N2N_TxSubmission (ph hi N2N_TxSubmission) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) cs
  with cell-out-key l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) cs
  with cell-out-key l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) cs
  with cell-out-key l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl
cellFlip-out l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) cs
  with cell-out-key l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) cs
... | refl , refl , refl , pe , Mkeq rewrite Mkeq = refl , pe , refl

------------------------------------------------------------------------
-- (3) PER-LINK.  Mirror of `WalkConvEvInv.decLink-ev-inv-wt`'s two io clauses;
-- the `ι`-carrying rename reflection identifies the source event with the
-- label, after which `cellFlip-{in,out}` pins the link and the key.
------------------------------------------------------------------------

-- an `input l₀ d₀ id₀ ! x` fire of link `l`'s breakable cell fold: the link is
-- `l`, the link is unbroken, the keyed cell was `empty`, successor is the
-- `setCell`-updated fold
decLink-ev-in-key : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload} {M : NetProc}
  → decLink l ph b ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M
  → (l₀ ≡ l) × (b ≡ false) × (ph d₀ id₀ ≡ empty)
    × (M ≡ decLink l (setCell ph d₀ id₀ (full x)) false)
decLink-ev-in-key l ph true step = ⊥-elim (ret-no-ev {P = decLink l ph true} refl step)
decLink-ev-in-key l ph false step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , Meq
        with renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , P′eq
          with just-injective iota
...       | refl
            with ⦀⋆-ev-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
                           (cell-noBoth l ph) srcStep
...         | k , Mk , cellStep , Q′eq
              with cellFlip-in l ph k cellStep
...           | refl , pe , listEq =
                refl , refl , pe ,
                trans Meq
                  (trans (cong (λ z → z △ (break l ⟶₀ Skip)) P′eq)
                    (trans (cong (λ z → renameMap z △ (break l ⟶₀ Skip)) Q′eq)
                           (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Skip)) listEq)))

-- an `output l₀ d₀ id₀ ! x` fire of link `l`'s breakable cell fold
decLink-ev-out-key : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload} {M : NetProc}
  → decLink l ph b ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M
  → (l₀ ≡ l) × (b ≡ false) × (ph d₀ id₀ ≡ full x)
    × (M ≡ decLink l (setCell ph d₀ id₀ (draining x)) false)
decLink-ev-out-key l ph true step = ⊥-elim (ret-no-ev {P = decLink l ph true} refl step)
decLink-ev-out-key l ph false step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , Meq
        with renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , P′eq
          with just-injective iota
...       | refl
            with ⦀⋆-ev-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
                           (cell-noBoth l ph) srcStep
...         | k , Mk , cellStep , Q′eq
              with cellFlip-out l ph k cellStep
...           | refl , pe , listEq =
                refl , refl , pe ,
                trans Meq
                  (trans (cong (λ z → z △ (break l ⟶₀ Skip)) P′eq)
                    (trans (cong (λ z → renameMap z △ (break l ⟶₀ Skip)) Q′eq)
                           (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Skip)) listEq)))

------------------------------------------------------------------------
-- (4) THE MEDIUM.  Mirror of `WalkConvEvInv.medium-ev-inv-wt`, but the fired
-- key IS the label's key — which is exactly what (a) had to deliver.
------------------------------------------------------------------------

-- a medium `input l₀ d₀ id₀ ! x`: the cell at THAT key was `empty` and the
-- successor is the medium with THAT key set to `full x`
medium-ev-in-key : (m : MedState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {M : NetProc}
  → decMed m ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M
  → (phase m l₀ d₀ id₀ ≡ empty)
    × (M ≡ decMed (mkMed (phase-upd (phase m) l₀ (setCell (phase m l₀) d₀ id₀ (full x)))
                         (broken m)))
medium-ev-in-key m l₀ d₀ id₀ x step
    with ⦀Fin-ev-inv numLinks (λ l → decLink l (phase m l) (broken m l))
           (link-io-diff m {Payload} {input l₀ d₀ id₀} {x} tt) step
... | i , Mi , linkStep , Meq
      with decLink-ev-in-key i (phase m i) (broken m i) linkStep
...   | refl , brEq , pe , MiEq =
        pe ,
        trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                    (finUpd (λ l → decLink l (phase m l) (broken m l)) l₀ z))
                    (trans MiEq (cong (decLink l₀ (setCell (phase m l₀) d₀ id₀ (full x)))
                                      (sym brEq))))
                 (recon-decMed m l₀ (setCell (phase m l₀) d₀ id₀ (full x))))

-- a medium `output l₀ d₀ id₀ ! x`: the cell at THAT key held exactly `x` and
-- the successor is the medium with THAT key set to `draining x`
medium-ev-out-key : (m : MedState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {M : NetProc}
  → decMed m ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M
  → (phase m l₀ d₀ id₀ ≡ full x)
    × (M ≡ decMed (mkMed (phase-upd (phase m) l₀ (setCell (phase m l₀) d₀ id₀ (draining x)))
                         (broken m)))
medium-ev-out-key m l₀ d₀ id₀ x step
    with ⦀Fin-ev-inv numLinks (λ l → decLink l (phase m l) (broken m l))
           (link-io-diff m {Payload} {output l₀ d₀ id₀} {x} tt) step
... | i , Mi , linkStep , Meq
      with decLink-ev-out-key i (phase m i) (broken m i) linkStep
...   | refl , brEq , pe , MiEq =
        pe ,
        trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                    (finUpd (λ l → decLink l (phase m l) (broken m l)) l₀ z))
                    (trans MiEq (cong (decLink l₀ (setCell (phase m l₀) d₀ id₀ (draining x)))
                                      (sym brEq))))
                 (recon-decMed m l₀ (setCell (phase m l₀) d₀ id₀ (draining x))))

------------------------------------------------------------------------
-- (5) THE PER-KEY READ of an io successor's medium (over-provisioning for the
-- (d) assembly): an ARBITRARY tracked cell key is either UNTOUCHED — its phase
-- literally the source one, giving the `cvFix` arm of `PipeInv.ClauseEvo` — or
-- it IS the fired key, and its phase is the new one.
------------------------------------------------------------------------

-- read an arbitrary cell key at a `setCell` io successor
setRead : (g : Link → Dir → IDs → CopyPhase) (i : Link) (d₀ : Dir) (id₀ : IDs)
          (np : CopyPhase) (kl : Link) (kd : Dir) (kid : IDs)
        → (g kl kd kid ≡ phase-upd g i (setCell (g i) d₀ id₀ np) kl kd kid)
        ⊎ ((kl ≡ i) × (kd ≡ d₀) × (kid ≡ id₀)
           × (phase-upd g i (setCell (g i) d₀ id₀ np) kl kd kid ≡ np))
setRead g i d₀ id₀ np kl kd kid with kl ≟ i
... | no ¬p = inj₁ refl
setRead g i d₀ id₀ np kl kd kid | yes refl with kd ≟ d₀ | kid ≟ id₀
... | yes refl | yes refl = inj₂ (refl , refl , refl , refl)
... | no ¬p    | _        = inj₁ refl
... | yes refl | no ¬p    = inj₁ refl

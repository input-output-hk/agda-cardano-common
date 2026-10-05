{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the SUCCESSOR-EXPOSING medium-τ inversion (WalkConv item (m1)).
--
-- R2's `SysOracle_TauCore.medium-τ-inv` returns the flipped-cell successor
-- `MedState` and `M ≡ decMed m′`, but HIDES the drained cell's coordinates
-- `(i, d₀, id₀, x)` and the crucial fact `phase m i d₀ id₀ ≡ draining x`
-- (they are produced by `decCopy-τ-inv` deep inside `cellFlip` and discarded).
-- `WalkConvMedium.medWt-flip` needs exactly that fact to prove the medium
-- weight drops by 2.  This module RE-DERIVES the inversion chain
--
--     cellFlip-wt  →  decLink-τ-inv-wt  →  medium-τ-inv-wt
--
-- threading the drained-cell coordinates + `phase m i d₀ id₀ ≡ draining x`
-- alongside the successor `m′` and `M ≡ decMed m′`.  The bodies mirror the
-- frozen `cellFlip`/`decLink-τ-inv`/`medium-τ-inv` VERBATIM (reusing the
-- exported `decCopy-τ-inv`/`△-τ-elim`/`renameMap-τ-reflect`/`⦀⋆-τ-inv`/
-- `⦀Fin-τ-inv`/`fold-react`/`recon-decMed`/`flipCell`/`phase-upd`) with the
-- ONLY change being the extra `(x , draining-fact)` component in the output.
-- Frozen R2 modules are imported, never edited.  No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (nothing)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; length; lookup; updateAt; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Net; Net-≟; Link; break )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ιNet; ιNet⁻¹; ιNet-linv )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi; IDs
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive
  ; N2N_LeiosNotify; N2N_LeiosFetch )

-- the Net_Api operators (for the `△` / `⟶₀` / `Skip` reconstruction)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _△_; Skip; Prefix₀; ⦀Fin )
-- the Net Payload operators (the pre-rename copy fold `⦀⋆`)
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆ )

-- the Net_Api / Net Payload LTS vocabularies
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ )
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN

-- the shared medium decode + records
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed; decLink; decCopy; MedState; mkMed; phase; broken
        ; CopyPhase; empty; full; draining; NetProcN )

-- R2's frozen inversion primitives (all re-derivations reuse these verbatim)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using
  ( NetProc; decCopy-τ-inv; flipCell; ⦀⋆-τ-inv; ⦀Fin-τ-inv; finUpd
  ; fold-react; △-τ-elim; ret-no-τ; phase-upd; recon-decMed
  ; ReactF; mkReactF )
open STC.MedNO using ( force-renameMap-react; renameMap-τ-reflect )
-- the medium's alphabet rename (the SAME `RenNet` `decLink` is defined with)
import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload}
  ιNet ιNet⁻¹ ιNet-linv as RenNet
open RenNet using ( renameMap )

------------------------------------------------------------------------
-- cellFlip-wt — `cellFlip` PLUS the drained-cell payload `x` and the fact
-- `ph d₀ id₀ ≡ draining x`.  The 12 clauses mirror `cellFlip`; the ONLY change
-- is that `decCopy-τ-inv`'s `(x , ph≡draining x)` (there discarded) is returned.
------------------------------------------------------------------------

cellFlip-wt : (l : Link) (ph : Dir → IDs → CopyPhase)
    (k : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))) {Mk : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k LN.─[ LN.τ ]─► Mk
  → Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ] Σ[ x ∈ Payload ]
       (ph d₀ id₀ ≡ draining x)
     × (updateAt (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k (λ _ → Mk)
          ≡ map (λ { (d , id) → decCopy l d id (flipCell ph d₀ id₀ d id) }) (linkConfig l))
cellFlip-wt l ph fzero cs with decCopy-τ-inv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) cs
... | x , pheq , Mkeq rewrite Mkeq = lo , N2N_KeepAlive , x , pheq , refl
cellFlip-wt l ph (fsuc fzero) cs with decCopy-τ-inv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) cs
... | x , pheq , Mkeq rewrite Mkeq = hi , N2N_KeepAlive , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc fzero)) cs with decCopy-τ-inv l lo N2N_ChainSync (ph lo N2N_ChainSync) cs
... | x , pheq , Mkeq rewrite Mkeq = lo , N2N_ChainSync , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc fzero))) cs with decCopy-τ-inv l hi N2N_ChainSync (ph hi N2N_ChainSync) cs
... | x , pheq , Mkeq rewrite Mkeq = hi , N2N_ChainSync , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc (fsuc fzero)))) cs with decCopy-τ-inv l lo N2N_BlockFetch (ph lo N2N_BlockFetch) cs
... | x , pheq , Mkeq rewrite Mkeq = lo , N2N_BlockFetch , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) cs with decCopy-τ-inv l hi N2N_BlockFetch (ph hi N2N_BlockFetch) cs
... | x , pheq , Mkeq rewrite Mkeq = hi , N2N_BlockFetch , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) cs with decCopy-τ-inv l lo N2N_TxSubmission (ph lo N2N_TxSubmission) cs
... | x , pheq , Mkeq rewrite Mkeq = lo , N2N_TxSubmission , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) cs with decCopy-τ-inv l hi N2N_TxSubmission (ph hi N2N_TxSubmission) cs
... | x , pheq , Mkeq rewrite Mkeq = hi , N2N_TxSubmission , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) cs with decCopy-τ-inv l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) cs
... | x , pheq , Mkeq rewrite Mkeq = lo , N2N_LeiosNotify , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) cs with decCopy-τ-inv l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) cs
... | x , pheq , Mkeq rewrite Mkeq = hi , N2N_LeiosNotify , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) cs with decCopy-τ-inv l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) cs
... | x , pheq , Mkeq rewrite Mkeq = lo , N2N_LeiosFetch , x , pheq , refl
cellFlip-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) cs with decCopy-τ-inv l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) cs
... | x , pheq , Mkeq rewrite Mkeq = hi , N2N_LeiosFetch , x , pheq , refl

------------------------------------------------------------------------
-- decLink-τ-inv-wt — `decLink-τ-inv` PLUS the drained-cell payload/fact.  The
-- body mirrors `decLink-τ-inv` verbatim; `cellFlip-wt` supplies the extra
-- `(x , ph d₀ id₀ ≡ draining x)` alongside the positional `listEq`.
------------------------------------------------------------------------

decLink-τ-inv-wt : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool) {Mi : NetProc}
  → decLink l ph b ─[ τ ]─► Mi
  → Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ] Σ[ x ∈ Payload ]
       (b ≡ false) × (ph d₀ id₀ ≡ draining x)
     × (Mi ≡ decLink l (flipCell ph d₀ id₀) false)
decLink-τ-inv-wt l ph true  step = ⊥-elim (ret-no-τ {P = decLink l ph true} refl step)
decLink-τ-inv-wt l ph false step with fold-react l ph
... | mkReactF V T feq
    with △-τ-elim (force-renameMap-react
                    {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                  refl (λ _ _ → refl) step
...   | P′ , renStep , Meq2
      with renameMap-τ-reflect renStep
...     | Q′ , foldStep , P′eq
        with ⦀⋆-τ-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) foldStep
...       | k , Mk , cellStep , Q′eq with cellFlip-wt l ph k cellStep
...         | d₀ , id₀ , x , pheq , listEq =
              d₀ , id₀ , x , refl , pheq ,
              trans Meq2
                (trans (cong (λ z → z △ (break l ⟶₀ Skip)) P′eq)
                  (trans (cong (λ z → renameMap z △ (break l ⟶₀ Skip)) Q′eq)
                         (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Skip)) listEq)))

------------------------------------------------------------------------
-- medium-τ-inv-wt — `medium-τ-inv` PLUS the drained cell's `(i, d₀, id₀, x)`
-- and `phase m i d₀ id₀ ≡ draining x`.  The successor `m′` is the SAME
-- `flipCell`/`phase-upd`-updated `MedState` the frozen inversion produces, so
-- `WalkConvMedium.medWt-flip m i d₀ id₀ x drainEq` applies directly.
------------------------------------------------------------------------

medium-τ-inv-wt : (m : MedState) {M : NetProc}
  → decMed m ─[ τ ]─► M
  → Σ[ i ∈ Link ] Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ] Σ[ x ∈ Payload ]
       (phase m i d₀ id₀ ≡ draining x)
     × (M ≡ decMed (mkMed (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀)) (broken m)))
medium-τ-inv-wt m step
    with ⦀Fin-τ-inv numLinks (λ l → decLink l (phase m l) (broken m l)) step
... | i , Mi , linkStep , Meq with decLink-τ-inv-wt i (phase m i) (broken m i) linkStep
...   | d₀ , id₀ , x , brEq , drainEq , MiEq =
        i , d₀ , id₀ , x , drainEq ,
        trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                    (finUpd (λ l → decLink l (phase m l) (broken m l)) i z))
                    (trans MiEq (cong (decLink i (flipCell (phase m i) d₀ id₀)) (sym brEq))))
                 (recon-decMed m i (flipCell (phase m i) d₀ id₀)))

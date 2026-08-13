{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the SUCCESSOR-EXPOSING medium io-EVENT inversion (WalkConv item (4)).
--
-- The io-sync branch of `τreflect` (`τreflect-io`) needs, for the medium side
-- of a hidden io-sync, both the successor `MedState` AND the fact that the
-- medium weight `medWt` rises by exactly one (the synced copy cell goes
-- `empty → full x` on an INPUT or `full x → draining x` on an OUTPUT, each
-- `cellWt +1`).  R2's `SysOracle_NodeTauEv.medium-ev-inv` returns the successor
-- but HIDES the fired cell coordinates `(i, d₀, id₀, np)` and the pre/post
-- phase relation, so it cannot feed the weight arithmetic.
--
-- This module RE-DERIVES the ev-inversion chain
--
--     cellFlipEv-wt  →  decLink-ev-inv-wt  →  medium-ev-inv-wt
--
-- threading, alongside the successor, the crucial fact
-- `cellWt np ≡ suc (cellWt (phase m i d₀ id₀))` (the fired cell weight rises by
-- one), then closes it into
--
--     medium-ev-inv-wt′ : (m)(iomem)(step)
--       → Σ m′. (M ≡ decMed m′) × (medWt m′ ≡ suc (medWt m))
--
-- the exact `medWt` rise `WalkConvMeasure.μτ-io-dec` consumes on the io-sync
-- class.  The inversion bodies MIRROR the frozen
-- `cellFlipEv`/`decLink-ev-inv`/`medium-ev-inv` VERBATIM (reusing the exported
-- `decCopy-ev-inv`/`△-ev-elim`/`renameMap-ev-reflect`/`⦀⋆-ev-inv`/`⦀Fin-ev-inv`/
-- `cell-noBoth`/`link-io-diff`/`fold-react`/`recon-decMed`/`setCell`/`phase-upd`);
-- the ONLY change is the extra weight-rise component.  Frozen R2 modules are
-- imported, never edited.  The `rowWt`/`medWt` arithmetic mirrors
-- `WalkConvMedium.rowWt-flip`/`medWt-flip` (the +1 dual of the medium-τ −2).
-- No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (nothing)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; length; lookup; updateAt; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvEvInv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Net; Net-≟; Link; break
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack
        ; done; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ιNet; ιNet⁻¹; ιNet-linv; ioES )
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
open STC.MedNO using ( force-renameMap-react; renameMap-ev-reflect )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA as SNT
open SNT using ( ret-no-ev; decCopy-ev-inv; CopyEvR; cevIn; cevOut
               ; ⦀⋆-ev-inv; ⦀Fin-ev-inv; cell-noBoth; link-io-diff; setCell )

-- the medium's alphabet rename (SAME instance `decLink` is defined with)
import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload}
  ιNet ιNet⁻¹ ιNet-linv as RenNet
open RenNet using ( renameMap )

-- the measure's cell/row/medium weights
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvMeasure blkA
  using ( cellWt; rowWt; medWt )

------------------------------------------------------------------------
-- cellFlipEv-wt — `cellFlipEv` PLUS the fired cell's weight-rise fact
-- `cellWt np ≡ suc (cellWt (ph d₀ id₀))`.  The 12 clauses mirror `cellFlipEv`;
-- `decCopy-ev-inv`'s pre-phase equality (there discarded) supplies the rise
-- (`empty → full x`: 0→1; `full x → draining x`: 1→2) by `cong (suc ∘ cellWt)`.
------------------------------------------------------------------------

cellFlipEv-wt : (l : Link) (ph : Dir → IDs → CopyPhase)
    (k : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))))
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {Mk : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mk
  → Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ] Σ[ np ∈ CopyPhase ]
       (cellWt np ≡ suc (cellWt (ph d₀ id₀)))
     × (updateAt (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k (λ _ → Mk)
          ≡ map (λ { (d , id) → decCopy l d id (setCell ph d₀ id₀ np d id) }) (linkConfig l))
cellFlipEv-wt l ph fzero cs with decCopy-ev-inv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) cs
... | cevIn  x pe Mkeq rewrite Mkeq = lo , N2N_KeepAlive , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = lo , N2N_KeepAlive , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc fzero) cs with decCopy-ev-inv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) cs
... | cevIn  x pe Mkeq rewrite Mkeq = hi , N2N_KeepAlive , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = hi , N2N_KeepAlive , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc fzero)) cs with decCopy-ev-inv l lo N2N_ChainSync (ph lo N2N_ChainSync) cs
... | cevIn  x pe Mkeq rewrite Mkeq = lo , N2N_ChainSync , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = lo , N2N_ChainSync , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc fzero))) cs with decCopy-ev-inv l hi N2N_ChainSync (ph hi N2N_ChainSync) cs
... | cevIn  x pe Mkeq rewrite Mkeq = hi , N2N_ChainSync , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = hi , N2N_ChainSync , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc (fsuc fzero)))) cs with decCopy-ev-inv l lo N2N_BlockFetch (ph lo N2N_BlockFetch) cs
... | cevIn  x pe Mkeq rewrite Mkeq = lo , N2N_BlockFetch , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = lo , N2N_BlockFetch , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) cs with decCopy-ev-inv l hi N2N_BlockFetch (ph hi N2N_BlockFetch) cs
... | cevIn  x pe Mkeq rewrite Mkeq = hi , N2N_BlockFetch , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = hi , N2N_BlockFetch , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) cs with decCopy-ev-inv l lo N2N_TxSubmission (ph lo N2N_TxSubmission) cs
... | cevIn  x pe Mkeq rewrite Mkeq = lo , N2N_TxSubmission , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = lo , N2N_TxSubmission , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) cs with decCopy-ev-inv l hi N2N_TxSubmission (ph hi N2N_TxSubmission) cs
... | cevIn  x pe Mkeq rewrite Mkeq = hi , N2N_TxSubmission , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = hi , N2N_TxSubmission , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) cs with decCopy-ev-inv l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) cs
... | cevIn  x pe Mkeq rewrite Mkeq = lo , N2N_LeiosNotify , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = lo , N2N_LeiosNotify , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) cs with decCopy-ev-inv l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) cs
... | cevIn  x pe Mkeq rewrite Mkeq = hi , N2N_LeiosNotify , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = hi , N2N_LeiosNotify , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) cs with decCopy-ev-inv l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) cs
... | cevIn  x pe Mkeq rewrite Mkeq = lo , N2N_LeiosFetch , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = lo , N2N_LeiosFetch , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl
cellFlipEv-wt l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) cs with decCopy-ev-inv l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) cs
... | cevIn  x pe Mkeq rewrite Mkeq = hi , N2N_LeiosFetch , full x     , cong (λ z → suc (cellWt z)) (sym pe) , refl
... | cevOut x pe Mkeq rewrite Mkeq = hi , N2N_LeiosFetch , draining x , cong (λ z → suc (cellWt z)) (sym pe) , refl

------------------------------------------------------------------------
-- decLink-ev-inv-wt — `decLink-ev-inv` PLUS the fired cell coords + weight rise.
-- Body mirrors `decLink-ev-inv` verbatim (both io events); `cellFlipEv-wt`
-- supplies `(d₀, id₀, np, riseEq)` alongside the positional `listEq`.
------------------------------------------------------------------------

decLink-ev-inv-wt : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decLink l ph b ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ] Σ[ np ∈ CopyPhase ]
       (b ≡ false) × (cellWt np ≡ suc (cellWt (ph d₀ id₀)))
     × (M ≡ decLink l (setCell ph d₀ id₀ np) false)
decLink-ev-inv-wt l ph true iomem step = ⊥-elim (ret-no-ev {P = decLink l ph true} refl step)
decLink-ev-inv-wt l ph false {e = input l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , Meq
        with renameMap-ev-reflect leftStep
...     | e₁ , Q′ , srcStep , P′eq
          with ⦀⋆-ev-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
                         (cell-noBoth l ph) srcStep
...       | k , Mk , cellStep , Q′eq
            with cellFlipEv-wt l ph k cellStep
...         | d₀ , id₀ , np , riseEq , listEq =
              d₀ , id₀ , np , refl , riseEq ,
              trans Meq
                (trans (cong (λ z → z △ (break l ⟶₀ Skip)) P′eq)
                  (trans (cong (λ z → renameMap z △ (break l ⟶₀ Skip)) Q′eq)
                         (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Skip)) listEq)))
decLink-ev-inv-wt l ph false {e = output l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , Meq
        with renameMap-ev-reflect leftStep
...     | e₁ , Q′ , srcStep , P′eq
          with ⦀⋆-ev-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
                         (cell-noBoth l ph) srcStep
...       | k , Mk , cellStep , Q′eq
            with cellFlipEv-wt l ph k cellStep
...         | d₀ , id₀ , np , riseEq , listEq =
              d₀ , id₀ , np , refl , riseEq ,
              trans Meq
                (trans (cong (λ z → z △ (break l ⟶₀ Skip)) P′eq)
                  (trans (cong (λ z → renameMap z △ (break l ⟶₀ Skip)) Q′eq)
                         (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Skip)) listEq)))
decLink-ev-inv-wt l ph false {e = sndmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = rcvmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = tx     l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = sndack l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = rcvack l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = ack    l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = done   l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = apiCS  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = apiBF  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = apiTS  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = apiKA  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = apiLN  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = apiLF  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv-wt l ph false {e = break  l₀}        iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- medium-ev-inv-wt — `medium-ev-inv` PLUS the fired link/cell coords + weight
-- rise.  Successor is the SAME `phase-upd`/`setCell`-updated `MedState`.
------------------------------------------------------------------------

medium-ev-inv-wt : (m : MedState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decMed m ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ i ∈ Link ] Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ] Σ[ np ∈ CopyPhase ]
       (cellWt np ≡ suc (cellWt (phase m i d₀ id₀)))
     × (M ≡ decMed (mkMed (phase-upd (phase m) i (setCell (phase m i) d₀ id₀ np)) (broken m)))
medium-ev-inv-wt m iomem step
    with ⦀Fin-ev-inv numLinks (λ l → decLink l (phase m l) (broken m l)) (link-io-diff m iomem) step
... | i , Mi , linkStep , Meq
      with decLink-ev-inv-wt i (phase m i) (broken m i) iomem linkStep
...   | d₀ , id₀ , np , brEq , riseEq , MiEq =
        i , d₀ , id₀ , np , riseEq ,
        trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                    (finUpd (λ l → decLink l (phase m l) (broken m l)) i z))
                    (trans MiEq (cong (decLink i (setCell (phase m i) d₀ id₀ np)) (sym brEq))))
                 (recon-decMed m i (setCell (phase m i) d₀ id₀ np)))

------------------------------------------------------------------------
-- rowWt-setCell — a cell of one link's phase-row advanced with `cellWt`-rise 1
-- raises that row's `rowWt` by exactly one.  The 12 `(Dir, IDs)` clauses reduce
-- `setCell`'s `_≟_`-guards at each concrete key; `riseEq` turns the fired cell's
-- weight into `suc (cellWt (g d₀ id₀))` and the solver closes the linear identity.
------------------------------------------------------------------------

rowWt-setCell : (g : Dir → IDs → CopyPhase) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
  → cellWt np ≡ suc (cellWt (g d₀ id₀))
  → rowWt (setCell g d₀ id₀ np) ≡ suc (rowWt g)
rowWt-setCell g lo N2N_KeepAlive np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              (con 1 :+ a) :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g hi N2N_KeepAlive np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ (con 1 :+ b) :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g lo N2N_ChainSync np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ (con 1 :+ c) :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g hi N2N_ChainSync np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ (con 1 :+ d) :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g lo N2N_BlockFetch np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ d :+ (con 1 :+ e) :+ f :+ h :+ i :+ j :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g hi N2N_BlockFetch np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ d :+ e :+ (con 1 :+ f) :+ h :+ i :+ j :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g lo N2N_TxSubmission np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ d :+ e :+ f :+ (con 1 :+ h) :+ i :+ j :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g hi N2N_TxSubmission np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ (con 1 :+ i) :+ j :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g lo N2N_LeiosNotify np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ (con 1 :+ j) :+ k :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g hi N2N_LeiosNotify np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ (con 1 :+ k) :+ l :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g lo N2N_LeiosFetch np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ (con 1 :+ l) :+ n
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
rowWt-setCell g hi N2N_LeiosFetch np riseEq rewrite riseEq =
  solve 12 (λ a b c d e f h i j k l n →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ (con 1 :+ n)
           := con 1 :+ (a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ n)) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))

------------------------------------------------------------------------
-- medWt-setCell — the whole-medium rise.  `phase-upd` changes only link `i`'s
-- row; the four `Link = Fin 4` cases reduce `phase-upd`'s `_≟_`-guard and
-- `rowWt-setCell` supplies the fired-row +1; the solver rearranges the link-sum.
------------------------------------------------------------------------

medWt-setCell : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
  → cellWt np ≡ suc (cellWt (phase m i d₀ id₀))
  → medWt (mkMed (phase-upd (phase m) i (setCell (phase m i) d₀ id₀ np)) (broken m))
     ≡ suc (medWt m)
medWt-setCell m fzero d₀ id₀ np riseEq =
  trans (cong (λ z → ((z + rowWt (phase m linkAC)) + rowWt (phase m linkBD)) + rowWt (phase m linkCD))
              (rowWt-setCell (phase m linkAB) d₀ id₀ np riseEq))
        (solve 4 (λ r1 r2 r3 r4 →
                    (((con 1 :+ r1) :+ r2) :+ r3) :+ r4
                 := con 1 :+ (((r1 :+ r2) :+ r3) :+ r4)) refl
           (rowWt (phase m linkAB)) (rowWt (phase m linkAC))
           (rowWt (phase m linkBD)) (rowWt (phase m linkCD)))
medWt-setCell m (fsuc fzero) d₀ id₀ np riseEq =
  trans (cong (λ z → ((rowWt (phase m linkAB) + z) + rowWt (phase m linkBD)) + rowWt (phase m linkCD))
              (rowWt-setCell (phase m linkAC) d₀ id₀ np riseEq))
        (solve 4 (λ r1 r2 r3 r4 →
                    ((r1 :+ (con 1 :+ r2)) :+ r3) :+ r4
                 := con 1 :+ (((r1 :+ r2) :+ r3) :+ r4)) refl
           (rowWt (phase m linkAB)) (rowWt (phase m linkAC))
           (rowWt (phase m linkBD)) (rowWt (phase m linkCD)))
medWt-setCell m (fsuc (fsuc fzero)) d₀ id₀ np riseEq =
  trans (cong (λ z → ((rowWt (phase m linkAB) + rowWt (phase m linkAC)) + z) + rowWt (phase m linkCD))
              (rowWt-setCell (phase m linkBD) d₀ id₀ np riseEq))
        (solve 4 (λ r1 r2 r3 r4 →
                    ((r1 :+ r2) :+ (con 1 :+ r3)) :+ r4
                 := con 1 :+ (((r1 :+ r2) :+ r3) :+ r4)) refl
           (rowWt (phase m linkAB)) (rowWt (phase m linkAC))
           (rowWt (phase m linkBD)) (rowWt (phase m linkCD)))
medWt-setCell m (fsuc (fsuc (fsuc fzero))) d₀ id₀ np riseEq =
  trans (cong (λ z → ((rowWt (phase m linkAB) + rowWt (phase m linkAC)) + rowWt (phase m linkBD)) + z)
              (rowWt-setCell (phase m linkCD) d₀ id₀ np riseEq))
        (solve 4 (λ r1 r2 r3 r4 →
                    ((r1 :+ r2) :+ r3) :+ (con 1 :+ r4)
                 := con 1 :+ (((r1 :+ r2) :+ r3) :+ r4)) refl
           (rowWt (phase m linkAB)) (rowWt (phase m linkAC))
           (rowWt (phase m linkBD)) (rowWt (phase m linkCD)))

------------------------------------------------------------------------
-- medium-ev-inv-wt′ — the packaged consumer form: an io medium step maps to a
-- successor `MedState` whose `medWt` rises by exactly one (`medWt m′ ≤ suc …`
-- for `μτ-io-dec`, delivered as the stronger `≡ suc`).
------------------------------------------------------------------------

medium-ev-inv-wt′ : (m : MedState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decMed m ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ m′ ∈ MedState ] (M ≡ decMed m′) × (medWt m′ ≡ suc (medWt m))
medium-ev-inv-wt′ m iomem step with medium-ev-inv-wt m iomem step
... | i , d₀ , id₀ , np , riseEq , Meq =
      mkMed (phase-upd (phase m) i (setCell (phase m i) d₀ id₀ np)) (broken m) ,
      Meq , medWt-setCell m i d₀ id₀ np riseEq

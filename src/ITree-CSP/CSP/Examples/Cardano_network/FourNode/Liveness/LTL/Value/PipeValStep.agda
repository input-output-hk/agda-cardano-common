{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the `PipeVal` STEP ENGINE (`Praos.PipeValStep`),
-- SESSION-36 steps (ii)–(iv) scaffolding.
--
-- `PipeValInv.PipeVal l s` is the per-leg block-VALUE invariant (session 35,
-- gated TRUE by `PipeValGate`).  To reach the delivery point it must be carried
-- along the SAME weak-step walk `PipeInvProd`'s product rides.  This module is
-- the exact mirror of `PipeInvProd`'s §2–§5 at `PipeVal`:
--
--   · the three per-step combinator types `TauStepV` / `EvStepV` / `StepEmitV`;
--   · the io-sync arm `TauIoV`, stated exactly (the FIRST open obligation);
--   · the MEDIUM-τ arm — **DISCHARGED here** (`pipeVal-drain`,
--     `τpreserveV-med`);
--   · the τ dispatch `tauStepV-from` (medium arm closed, io arm from outside);
--   · the τ-run fold and the weak-move fold `stepEmitFromV`.
--
-- WHY THE MEDIUM ARM IS CHEAPER AT `PipeVal` THAN AT `PipeInv⁺`.  A medium τ is
-- a DRAIN: it sets one cell to `empty` and moves no node.  `CellValOK empty` is
-- `⊤`, so a drain can only ever DISCHARGE a value clause — never threaten one.
-- In particular `drain-preserve`'s "the two leg cells are distinct links, so at
-- most one is emptied" case analysis (`linkAB≢linkBD`) is NOT needed here: both
-- cells being emptied at once would be fine.  Six of the eight clauses are node
-- components, which a drain leaves literally fixed.
--
-- STYLE.  `let`, never `with`, in every function whose type mentions the
-- imported `PipeVal` — this module is `(blkA : Block₃)`-parameterised, and a
-- `with` abstracts the block out of the imported `PipeValInv` copy, after which
-- the abstracted goal stops converting (the session-32/33 hazard, recorded in
-- `PipeTauMed.τpreserve-med`'s own note).
--
-- REMAINING OBLIGATIONS after this module: `TauIoV l` and `EvStepV l`.  Both
-- are taken as explicit combinator ARGUMENTS — no postulate, no premise added
-- to any chain module (the `PipeInvProd` convention).
--
-- Imported by nothing yet.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValStep (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi; IDs; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel; Event )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev; wτ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining; MedState; phase; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absNodesOf; nodesOf; lift-med-whole-τ
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( cellUp; cellDn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauMed blkA
  using ( drainSucc; cell-drain-eq )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( PipeVal; CellValOK )

------------------------------------------------------------------------
-- (1) THE PER-STEP COMBINATOR TYPES (mirrors of `PipeInvProd`'s at `PipeVal`).
------------------------------------------------------------------------

-- one hidden τ hop preserves the value invariant
TauStepV : TwoLegs → Set₁
TauStepV l = (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
           → Σ[ r′ ∈ RState ]
               (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))

-- one strong visible hop preserves the value invariant
EvStepV : TwoLegs → Set₁
EvStepV l = (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
          → Σ[ r′ ∈ RState ]
              (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))

-- one WEAK visible move preserves the value invariant (what the delivery walk
-- `WalkDeliverB` and the locate walk both consume)
StepEmitV : TwoLegs → Set₁
StepEmitV l = (r : RState) {e : Event} {t′ : NetProc} → radec r ═[ ev (evl e) ]═► t′
            → Σ[ r′ ∈ RState ]
                (t′ ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))

------------------------------------------------------------------------
-- (2) THE io-SYNC ARM — the FIRST open obligation, stated exactly (mirror
-- `PipeInvProd.TauIoS`).  Medium and nodes fire the SAME hidden io.  Its three
-- shapes are the cell FILL (needs `PipeValGate.srv-wblk-pins` — the sending BF
-- server at `bsBlk1 b` writes exactly `MsgBlock b` — composed with clause (1)
-- or (5) of `PipeVal`), the cell OUTPUT/drain into a BF client (needs
-- `PipeValGate.cli-stream-reads`), and the client advance.
------------------------------------------------------------------------

TauIoV : TwoLegs → Set₁
TauIoV l = (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
           {M₁ N₁ M : NetProc}
         → ioES .mem (X , e) a
         → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁
         → absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁
         → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
         → Σ[ r′ ∈ RState ]
             (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))

------------------------------------------------------------------------
-- (3) THE MEDIUM-τ ARM — DISCHARGED.  A drain empties one cell and moves no
-- node; `CellValOK empty` is `⊤`, so no value clause can be threatened.
------------------------------------------------------------------------

-- a cell that is either UNCHANGED or EMPTIED keeps its value clause (this is
-- the shape `PipeTauMed.cell-drain-eq` delivers, hit-witness and all)
cellValOK-drain : {ph ph′ : CopyPhase} {i kl : Link}
                → (ph′ ≡ ph) ⊎ ((kl ≡ i) × (ph′ ≡ empty))
                → CellValOK ph → CellValOK ph′
cellValOK-drain (inj₁ refl)        h = h
cellValOK-drain (inj₂ (_ , refl))  _ = tt

-- leg-`l` VALUE preservation across the drain of cell key `(i,d₀,id₀)`.  Cased
-- on `l` at the top (so `cellUp l`/`cellDn l` reduce to their concrete link
-- keys); the six NODE clauses ride across literally — a drain rebuilds only the
-- medium — and the two cell clauses go through `cellValOK-drain`.  No `with`.
pipeVal-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
  → PipeVal l s → PipeVal l (drainSucc s i d₀ id₀)
pipeVal-drain legBD s i d₀ id₀ (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) =
  let u = cell-drain-eq (med s) i d₀ id₀ linkAB hi N2N_BlockFetch
      d = cell-drain-eq (med s) i d₀ id₀ linkBD hi N2N_BlockFetch
  in  h1 , cellValOK-drain u h2 , h3 , h4
    , h5 , cellValOK-drain d h6 , h7 , h8
pipeVal-drain legCD s i d₀ id₀ (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) =
  let u = cell-drain-eq (med s) i d₀ id₀ linkAC hi N2N_BlockFetch
      d = cell-drain-eq (med s) i d₀ id₀ linkCD hi N2N_BlockFetch
  in  h1 , cellValOK-drain u h2 , h3 , h4
    , h5 , cellValOK-drain d h6 , h7 , h8

-- the medium-τ preservation reflector at `PipeVal` (mirror
-- `PipeTauMed.τpreserve-med` / `PipeInvProd.τpreserveS-med`; ONE `let`)
τpreserveV-med : (l : TwoLegs) (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (PipeVal l (toSys r) → PipeVal l (toSys r′))
τpreserveV-med l r {M} {M′} ms Meq =
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
  in  r′ , Meq′ , pipeVal-drain l (toSys r) i d₀ id₀

------------------------------------------------------------------------
-- (4) THE τ DISPATCH — a hidden τ is a medium drain (closed above) or an
-- io-SYNC (the open arm).  `absNodesOf` has no autonomous τ.
------------------------------------------------------------------------

-- assemble `TauStepV` from the open io arm (mirror `PipeInvProd.tauStepS-from`)
tauStepV-from : (l : TwoLegs) → TauIoV l → TauStepV l
tauStepV-from l tio r stp with reflect-absDec-τ (toSys r) stp
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τpreserveV-med l r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
tauStepV-from l tio r stp | hidSync M₁ N₁ iomem sM sN Peq = tio r iomem sM sN Peq

------------------------------------------------------------------------
-- (5) THE FOLDS.  Fold `TauStepV` across the two τ-runs of a weak move, apply
-- `EvStepV` to the strong middle, compose the three preservation maps.
------------------------------------------------------------------------

module _ (l : TwoLegs) where

  -- fold `TauStepV` across a hidden τ-run, threading the composed preservation
  -- (generalised over the start tree with a `start ≡ radec r` witness so the
  -- `Star` sub-term recurses structurally, exactly as `PipeStepEmit`'s does)
  liftτ*-preserveV′ : TauStepV l → (r : RState) {start u : NetProc}
                    → start ≡ radec r → start ─[τ*]─► u
                    → Σ[ r′ ∈ RState ]
                        (u ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))
  liftτ*-preserveV′ ts r eq τ*-refl = r , eq , (λ x → x)
  liftτ*-preserveV′ ts r eq (τ*-step s rest)
    with ts r (subst (λ z → z ─[ τ ]─► _) eq s)
  ... | r₁ , eq₁ , p₁ with liftτ*-preserveV′ ts r₁ eq₁ rest
  ...   | r′ , equ , p′ = r′ , equ , (λ x → p′ (p₁ x))

  -- the fine-step fold: decompose `wev pre mid post`, fold the τ-runs, dispatch
  -- the middle, compose
  stepEmitFromV : TauStepV l → EvStepV l → StepEmitV l
  stepEmitFromV ts es r (wev pre mid post)
    with liftτ*-preserveV′ ts r refl pre
  ... | r₁ , eq₁ , p₁
      with es r₁ (subst (λ z → z ─[ ev (evl _) ]─► _) eq₁ mid)
  ...   | r₂ , eq₂ , p₂
        with liftτ*-preserveV′ ts r₂ refl (subst (λ z → z ─[τ*]─► _) eq₂ post)
  ...     | r′ , equ , p₃ = r′ , equ , (λ x → p₃ (p₂ (p₁ x)))

  -- the fully assembled weak-move transporter from the io arm + the visible arm
  stepEmitV : TauIoV l → EvStepV l → StepEmitV l
  stepEmitV tio es = stepEmitFromV (tauStepV-from l tio) es

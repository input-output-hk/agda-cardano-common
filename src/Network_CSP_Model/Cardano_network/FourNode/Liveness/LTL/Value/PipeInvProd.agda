{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the PRODUCT invariant and its walk engine
-- (`Praos.PipeInvProd`), steps F3 + F4 of the session-28 frontier.
--
-- `PipeInv⁺` (token level + cell/client coupling) is NOT closed on its own:
-- the io FILL case of its upstream/downstream CELL clause needs "the sending BF
-- SERVER holds a block ⇒ the producer has sent / the relay has forwarded",
-- which is `PipeSrvInv.SrvCoupled` — an invariant `PipeInv⁺` does not carry
-- (`Coupled` covers cells and CLIENTS only).  So the object that is actually
-- inductive is the PRODUCT
--
--     `PipeInvS l s = PipeInv⁺ l s × SrvCoupled l s`
--
-- and this module builds the whole forward pipeline over it: base, the
-- `Pr`-bridge, the three per-step combinator types, the τ-run fold, the
-- fine-step fold, and the walk fold to the `producedA` frame — a re-mirror of
-- `PipeStepEmit` + `PipeExpose.pipeInv⁺-along-walk′` at the product.
--
-- TWO arms are DISCHARGED here:
--   · the medium-τ arm `τpreserveS-med` (a drain moves NO node, so the server
--     coupling rides across by `srvCoupled-frame`, and the `PipeInv⁺` half is
--     `PipeTauMed.drain-preserve` verbatim);
--   · the whole hidden-τ DISPATCH `tauStepS-from`, which splits a τ into the
--     discharged medium arm and the isolated io-sync arm.
--
-- TWO combinators remain OPEN, and they are exactly the residue of `pcone`:
--   · `TauIoS l` — the io-SYNC arm (fill / output-drain / client advance);
--   · `SrvEvStep l` — the server-coupling half of the VISIBLE step (the
--     `PipeInv⁺` half is already TOTAL, `PipeEvStep.evStep`).
-- They are taken as explicit combinator ARGUMENTS, exactly as
-- `PipeExpose.pipeInv⁺-along-walk` takes `StepEmit` — no postulate, no premise
-- added to any chain module.
--
-- Imported by nothing yet.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
import Data.Unit as U
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI; deadlock )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInvProd (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel; Event; Event√; √ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev; wτ )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; step; done; stuck; div; frameOf; IsTermᵂ
        ; drop; dropIdx; tail; tailIdx; dropIdx-stutter )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; med; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( pp5 )
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
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkCausal blkA
  using ( term-no-prod; noWeakVis-deadlock; sqrt-target-deadlock )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; Pr )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( PipeInv; PipeInv⁺; pipeInv⁺-init; pipeInv⁺⇒PipeInv; pipeInv⇒Pr; prodOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( SrvCoupled; srvCoupled-init; srvCoupled-frame )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauMed blkA
  using ( drainSucc; drain-preserve )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvStep blkA
  using ( evStep )

------------------------------------------------------------------------
-- (1) THE PRODUCT INVARIANT, its base and its `Pr` bridge.
------------------------------------------------------------------------

-- the genuinely inductive per-leg invariant: the token/coupling invariant TIMES
-- the server coupling (the missing half the io FILL case consumes)
PipeInvS : TwoLegs → SysState → Set
PipeInvS l s = PipeInv⁺ l s × SrvCoupled l s

-- BASE — both halves hold at `initial`
pipeInvS-init : (l : TwoLegs) → PipeInvS l initial
pipeInvS-init l = pipeInv⁺-init l , srvCoupled-init l

-- forget both strengthenings: the product still delivers the `Pr` pending fact
pipeInvS⇒Pr : (b : Block₃) (l : TwoLegs) (r : RState)
            → prodOf l (toSys r) ≡ pp5 → PipeInvS l (toSys r) → Pr b r
pipeInvS⇒Pr b l r eq (pinv , _) =
  pipeInv⇒Pr b l r eq (pipeInv⁺⇒PipeInv l (toSys r) pinv)

------------------------------------------------------------------------
-- (2) THE PER-STEP COMBINATOR TYPES (product analogues of
-- `PipeStepEmit.TauStep`/`EvStep` and `PipeExpose.StepEmit`).
------------------------------------------------------------------------

-- one hidden τ hop preserves the product
TauStepS : TwoLegs → Set₁
TauStepS l = (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
           → Σ[ r′ ∈ RState ]
               (M ≡ radec r′) × (PipeInvS l (toSys r) → PipeInvS l (toSys r′))

-- one strong visible hop preserves the product
EvStepS : TwoLegs → Set₁
EvStepS l = (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
          → Σ[ r′ ∈ RState ]
              (M ≡ radec r′) × (PipeInvS l (toSys r) → PipeInvS l (toSys r′))

-- one weak visible move preserves the product
StepEmitS : TwoLegs → Set₁
StepEmitS l = (r : RState) {e : Event} {t′ : NetProc} → radec r ═[ ev (evl e) ]═► t′
            → Σ[ r′ ∈ RState ]
                (t′ ≡ radec r′) × (PipeInvS l (toSys r) → PipeInvS l (toSys r′))

------------------------------------------------------------------------
-- (3) THE TWO OPEN COMBINATORS, stated exactly.
------------------------------------------------------------------------

-- THE io-SYNC arm of `TauStepS` (the remaining `TauStep` work): medium and
-- nodes fire the SAME io.  Its three cases are the cell FILL (discharged for
-- the leg's own cell by `PipeSrvFire.fill-{up,dn}-nodes` once the medium
-- inversion exposes the fired key), the cell OUTPUT/drain, and the BF-client
-- advance; plus the server-coupling half (`bsBlk1` is api-entered only, so no
-- io fire can create a holder).
TauIoS : TwoLegs → Set₁
TauIoS l = (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
           {M₁ N₁ M : NetProc}
         → ioES .mem (X , e) a
         → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁
         → absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁
         → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
         → Σ[ r′ ∈ RState ]
             (M ≡ radec r′) × (PipeInvS l (toSys r) → PipeInvS l (toSys r′))

-- THE server-coupling half of the VISIBLE step, stated AT `evStep`'s own
-- reflected successor (the `PipeInv⁺` half is already total)
SrvEvStep : TwoLegs → Set₁
SrvEvStep l = (r : RState) {e : Event} {M : NetProc}
              (st : radec r ─[ ev (evl e) ]─► M)
            → SrvCoupled l (toSys r)
            → SrvCoupled l (toSys (proj₁ (evStep l r st)))

------------------------------------------------------------------------
-- (4) THE MEDIUM-τ ARM — DISCHARGED.  A medium drain rebuilds `drainSucc`
-- (nodes untouched), so `PipeTauMed.drain-preserve` carries `PipeInv⁺` and
-- `srvCoupled-frame` (all four reads `refl`) carries `SrvCoupled`.
------------------------------------------------------------------------

-- a drain moves no node, so the server coupling rides across unchanged
srvCoupled-drain : (l : TwoLegs) (s : SysState) (i : _) (d₀ : _) (id₀ : _)
                 → SrvCoupled l s → SrvCoupled l (drainSucc s i d₀ id₀)
srvCoupled-drain legBD s i d₀ id₀ sc =
  srvCoupled-frame legBD s (drainSucc s i d₀ id₀) refl refl refl refl sc
srvCoupled-drain legCD s i d₀ id₀ sc =
  srvCoupled-frame legCD s (drainSucc s i d₀ id₀) refl refl refl refl sc

-- the medium-τ preservation reflector at the PRODUCT (mirror
-- `PipeTauMed.τpreserve-med`; ONE `let`, no `with`/`where` — the module is
-- `blkA`-parameterised, so a `with` would abstract the block out of the
-- imported `PipeInv`/`PipeSrvInv` copies and stop the goal converting)
τpreserveS-med : (l : TwoLegs) (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (PipeInvS l (toSys r) → PipeInvS l (toSys r′))
τpreserveS-med l r {M} {M′} ms Meq =
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
      pres : PipeInvS l (toSys r) → PipeInvS l s′
      pres = λ ps → drain-preserve l (toSys r) i d₀ id₀ (proj₁ ps)
                  , srvCoupled-drain l (toSys r) i d₀ id₀ (proj₂ ps)
  in  r′ , Meq′ , pres

------------------------------------------------------------------------
-- (5) THE τ DISPATCH — a hidden τ is a medium drain (discharged above) or an
-- io-SYNC (the open arm).  `absNodesOf` has no autonomous τ.
------------------------------------------------------------------------

-- assemble `TauStepS` from the open io arm (mirror
-- `PipeClassCell.τreflect-classcell`'s dispatch)
tauStepS-from : (l : TwoLegs) → TauIoS l → TauStepS l
tauStepS-from l tio r stp with reflect-absDec-τ (toSys r) stp
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τpreserveS-med l r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
tauStepS-from l tio r stp | hidSync M₁ N₁ iomem sM sN Peq = tio r iomem sM sN Peq

------------------------------------------------------------------------
-- (6) THE VISIBLE STEP — the `PipeInv⁺` half is `PipeEvStep.evStep` (TOTAL,
-- unconditional); only the server-coupling half is supplied from outside.
------------------------------------------------------------------------

-- assemble `EvStepS` from the green `evStep` and the open server half
evStepS-from : (l : TwoLegs) → SrvEvStep l → EvStepS l
evStepS-from l sev r st =
  let (r′ , eq , mp) = evStep l r st
  in  r′ , eq , (λ ps → mp (proj₁ ps) , sev r st (proj₂ ps))

------------------------------------------------------------------------
-- (7) THE FINE-STEP FOLD (mirror `PipeStepEmit.stepEmitFrom`): fold `TauStepS`
-- across the two τ-runs of a weak move and apply `EvStepS` to the middle.
------------------------------------------------------------------------

module _ (l : TwoLegs) where

  -- fold `TauStepS` across a hidden τ-run, threading the composed preservation
  liftτ*S′ : TauStepS l → (r : RState) {start u : NetProc}
           → start ≡ radec r → start ─[τ*]─► u
           → Σ[ r′ ∈ RState ]
               (u ≡ radec r′) × (PipeInvS l (toSys r) → PipeInvS l (toSys r′))
  liftτ*S′ ts r eq τ*-refl = r , eq , (λ x → x)
  liftτ*S′ ts r eq (τ*-step s rest)
    with ts r (subst (λ z → z ─[ τ ]─► _) eq s)
  ... | r₁ , eq₁ , p₁ with liftτ*S′ ts r₁ eq₁ rest
  ...   | r′ , equ , p′ = r′ , equ , (λ x → p′ (p₁ x))

  -- decompose `wev pre mid post`, fold the τ-runs, dispatch the middle, compose
  stepEmitFromS : TauStepS l → EvStepS l → StepEmitS l
  stepEmitFromS ts es r (wev pre mid post)
    with liftτ*S′ ts r refl pre
  ... | r₁ , eq₁ , p₁
      with es r₁ (subst (λ z → z ─[ ev (evl _) ]─► _) eq₁ mid)
  ...   | r₂ , eq₂ , p₂
        with liftτ*S′ ts r₂ refl (subst (λ z → z ─[τ*]─► _) eq₂ post)
  ...     | r′ , equ , p₃ = r′ , equ , (λ x → p₃ (p₂ (p₁ x)))

------------------------------------------------------------------------
-- (8) THE WALK FOLD (mirror `PipeExpose.pipeInv⁺-along-walk′` at the product):
-- thread `PipeInvS` from the seed at `initial` to the located `producedA`
-- frame.  The √/terminal backbone is `WalkCausal`'s, verbatim.
------------------------------------------------------------------------

module _ (b : Block₃) (l : TwoLegs) where

  -- fold the product preservation along the walk to the frame at position `n`
  pipeInvS-along-walk′ : StepEmitS l → (r : RState) {t : NetProc} → t ≡ radec r
                       → PipeInvS l (toSys r)
                       → (w : WTrace (⊤ {0ℓ}) t) (n : ℕ)
                       → producedA b (frameOf (drop n w))
                       → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′) × PipeInvS l (toSys r′)
  pipeInvS-along-walk′ emit r eq pinv w zero pn = r , eq , pinv
  -- a visible `evl`-step: classify it, advance the product, recurse on the tail
  pipeInvS-along-walk′ emit r eq pinv (step {e = evl e0} wstep tr) (suc m) pn
    with emit r (subst (λ z → z ═[ ev (evl e0) ]═► _) eq wstep)
  ... | r₁ , eq₁ , ps =
        pipeInvS-along-walk′ emit r₁ eq₁ (ps pinv)
          (tail (step {e = evl e0} wstep tr)) m pn
  -- a `√`-step: the tail lives over `deadlock`, hence terminal ⇒ no `producedA`
  pipeInvS-along-walk′ emit r eq pinv (step {e = √ x} wstep tr) (suc m) pn =
    ⊥-elim (term-no-prod b (tail (step {e = √ x} wstep tr)) termTail m pn)
    where
      tdead : tailIdx (step {e = √ x} wstep tr) ≡ deadlock
      tdead = sqrt-target-deadlock wstep
      termTail : IsTermᵂ (tail (step {e = √ x} wstep tr))
      termTail with tail (step {e = √ x} wstep tr)
      ... | step wstep₂ _ =
              ⊥-elim (noWeakVis-deadlock (subst (λ z → z ═[ ev _ ]═► _) tdead wstep₂))
      ... | done _ _  = U.tt
      ... | stuck _ _ = U.tt
      ... | div _     = U.tt
  -- terminal frames: `dropIdx` stutters back to the start index; product kept
  pipeInvS-along-walk′ emit r eq pinv (done q eqr) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (done q eqr) U.tt) eq , pinv
  pipeInvS-along-walk′ emit r eq pinv (stuck q st) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (stuck q st) U.tt) eq , pinv
  pipeInvS-along-walk′ emit r eq pinv (div dv) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (div dv) U.tt) eq , pinv

  -- headline: seeded at `initial`, the walk delivers `PipeInvS` at the frame
  pipeInvS-along-walk : StepEmitS l → (r : RState) → toSys r ≡ initial
                      → (w : WTrace (⊤ {0ℓ}) (radec r)) (n : ℕ)
                      → producedA b (frameOf (drop n w))
                      → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′) × PipeInvS l (toSys r′)
  pipeInvS-along-walk emit r ini w n pn =
    pipeInvS-along-walk′ emit r refl
      (subst (PipeInvS l) (sym ini) (pipeInvS-init l)) w n pn

  -- the fully assembled product walk: from the two OPEN combinators alone
  pipeInvS-along-walk-from : TauIoS l → SrvEvStep l
                           → (r : RState) → toSys r ≡ initial
                           → (w : WTrace (⊤ {0ℓ}) (radec r)) (n : ℕ)
                           → producedA b (frameOf (drop n w))
                           → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′) × PipeInvS l (toSys r′)
  pipeInvS-along-walk-from tio sev =
    pipeInvS-along-walk
      (stepEmitFromS l (tauStepS-from l tio) (evStepS-from l sev))

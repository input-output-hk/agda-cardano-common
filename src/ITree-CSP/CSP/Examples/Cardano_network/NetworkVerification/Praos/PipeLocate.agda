{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — `locate` REBUILT from the pipeline walk
-- (`Praos.PipeLocate`), item (E) of the session-32 frontier.
--
-- `WalkLocate.locate` is currently `walkReach′` composed with the OPEN premise
-- `pcone`.  This module rebuilds the SAME type constructively from
--
--   · `PipeInvProd.pipeInvS-along-walk′` — the product-invariant walk fold,
--     seeded at `rinit` (`rinit-toSys`), which delivers `PipeInvS l (toSys r0)`
--     at the located `producedA` frame;
--   · (E1) `PipeProdFix.liftτ*-prodFix` — a hidden τ-run moves NO producer, so
--     the `pp5` fact transports back across the frame's τ-PREFIX;
--   · (E2) `PipeProdFire.prodFire-{AB,AC}` — the STRONG middle of the frame's
--     weak `apiBF … sendBFBlock` forces the firing leg's producer to `pp5`;
--   · `PipeInvProd.pipeInvS⇒Pr` — `PipeInvS` + `prodOf ≡ pp5` ⇒ `Pr`.
--
-- WHY (E1)+(E2) ARE BOTH NEEDED (the session-32 finding).  `producedA b` is a
-- FRAME predicate: it records that the frame's next move is a WEAK
-- `apiBF … sendBFBlock` (τ*·ev·τ*), NOT a strong step out of the frame's own
-- state.  `pipeInvS⇒Pr` wants `prodOf l (toSys r0) ≡ pp5` AT the frame state.
-- (E2) only sees the strong middle; (E1) carries its verdict back over the
-- τ-prefix.  The τ-SUFFIX is irrelevant — nothing downstream of the middle is
-- read.
--
-- THE ONE REMAINING INPUT is the visible-step product combinator `EvStepS`
-- (item G2: the `PipeInv⁺` half is the total `PipeEvStep.evStep`; only the
-- `SrvCoupled` half is open).  It is taken as a MODULE PREMISE here — exactly
-- as `PipeInvProd` takes its combinators — so that `locate″` is otherwise
-- CLOSED: `TauIoS` is discharged in-module by `PipeTauIo.tauIo`.
--
-- The result type matches `WalkLocate.locate`'s EXACTLY, i.e. the slot
-- `AbstractLive.walkPos` fills with `WL.locate pcone`.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( ℕ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeLocate (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; linkAB; linkAC )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; apiBF; sendBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( hi )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; _═[_]═►_; wev )
open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( LTLᵗ; atom )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; step; ⟦_⟧ᵂ; drop; dropIdx; frameOf )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondLiveness
  using ( producedA )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( pp5 )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; radec; toSys; rinit; rinit-toSys; radec-init )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs; legBD; legCD; Pr )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( prodOf )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInvProd blkA
  using ( PipeInvS; pipeInvS-init; pipeInvS⇒Pr
        ; TauStepS; EvStepS; StepEmitS; tauStepS-from; stepEmitFromS
        ; pipeInvS-along-walk′ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeTauIo blkA
  using ( tauIo )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeEvStep blkA
  using ( evStepS )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeProdFix blkA
  using ( AllProdFix; prodFixOf; liftτ*-prodFix )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeProdFire blkA
  using ( prodFire-AB; prodFire-AC )

------------------------------------------------------------------------
-- (1) THE FRAME INVERSION.  A `producedA b` frame IS a weak
-- `apiBF (linkAB|linkAC) hi sendBFBlock ! b` move out of the frame's state.
-- ONE clause per link disjunct — every other frame shape makes the hypothesis
-- `⊥`, so Agda's coverage discharges them automatically.
------------------------------------------------------------------------

-- the weak `sendBFBlock` move a `producedA` frame records, tagged by its link
prodFrame-inv : (b : Block₃) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t)
              → producedA b (frameOf w)
              → Σ[ t′ ∈ NetProc ]
                  ( (t ═[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]═► t′)
                  ⊎ (t ═[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]═► t′) )
prodFrame-inv b (step {e = evl (evLabel _ (apiBF l d sendBFBlock) a)} ws _)
              (inj₁ refl , refl , refl) = _ , inj₁ ws
prodFrame-inv b (step {e = evl (evLabel _ (apiBF l d sendBFBlock) a)} ws _)
              (inj₂ refl , refl , refl) = _ , inj₂ ws

------------------------------------------------------------------------
-- (2) (E1) ∘ (E2): the WEAK move's `pp5` verdict at its SOURCE state.  Fold
-- the τ-prefix with the producer-fixity run, invert the strong middle, compose.
-- Clause-level `wev` match + a single `let` — no `with`, so the `PipeInv`
-- types in the statement cannot be renormalised out of convertibility.
------------------------------------------------------------------------

-- a WEAK `apiBF linkAB hi sendBFBlock` out of `radec r` pins leg BD's producer
weak-pp5-AB : (r : RState) (b : Block₃) {t′ : NetProc}
            → radec r ═[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]═► t′
            → prodOf legBD (toSys r) ≡ pp5
weak-pp5-AB r b (wev pre mid post) =
  let (r₁ , eq₁ , fix) = liftτ*-prodFix r pre
      mid′ : radec r₁ ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]─► _
      mid′ = subst (λ z → z ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]─► _)
                   eq₁ mid
  in  trans (prodFixOf legBD (toSys r) (toSys r₁) fix) (prodFire-AB r₁ mid′)

-- a WEAK `apiBF linkAC hi sendBFBlock` out of `radec r` pins leg CD's producer
weak-pp5-AC : (r : RState) (b : Block₃) {t′ : NetProc}
            → radec r ═[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]═► t′
            → prodOf legCD (toSys r) ≡ pp5
weak-pp5-AC r b (wev pre mid post) =
  let (r₁ , eq₁ , fix) = liftτ*-prodFix r pre
      mid′ : radec r₁ ─[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]─► _
      mid′ = subst (λ z → z ─[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]─► _)
                   eq₁ mid
  in  trans (prodFixOf legCD (toSys r) (toSys r₁) fix) (prodFire-AC r₁ mid′)

------------------------------------------------------------------------
-- (3) THE ASSEMBLY, under the ONE open combinator.
------------------------------------------------------------------------

module _ (evs : (l : TwoLegs) → EvStepS l) where

  -- the fully assembled weak-move product transporter (τ-io arm discharged
  -- in-module by `PipeTauIo.tauIo`; visible arm from the premise)
  emitS : (l : TwoLegs) → StepEmitS l
  emitS l = stepEmitFromS l (tauStepS-from l (tauIo l)) (evs l)

  -- walk the product invariant from `rinit` to the located `producedA` frame
  walkTo : (l : TwoLegs) (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
         → producedA b (frameOf (drop n tr))
         → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × PipeInvS l (toSys r0)
  walkTo l b tr n pn =
    pipeInvS-along-walk′ b l (emitS l) rinit (sym radec-init)
      (subst (PipeInvS l) (sym rinit-toSys) (pipeInvS-init l)) tr n pn

  -- the AB-leg branch: walk, transport the weak move to `r0`, cash in `Pr`
  locate-AB : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
            → (pn : producedA b (frameOf (drop n tr)))
            → (t′ : NetProc)
            → dropIdx n tr ═[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]═► t′
            → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × Pr b r0
  locate-AB b tr n pn t′ ws =
    let (r0 , eq0 , pinv) = walkTo legBD b tr n pn
        ws′ : radec r0 ═[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]═► t′
        ws′ = subst (λ z → z ═[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]═► t′)
                    eq0 ws
    in  r0 , eq0 , pipeInvS⇒Pr b legBD r0 (weak-pp5-AB r0 b ws′) pinv

  -- the AC-leg branch (symmetric)
  locate-AC : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
            → (pn : producedA b (frameOf (drop n tr)))
            → (t′ : NetProc)
            → dropIdx n tr ═[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]═► t′
            → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × Pr b r0
  locate-AC b tr n pn t′ ws =
    let (r0 , eq0 , pinv) = walkTo legCD b tr n pn
        ws′ : radec r0 ═[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]═► t′
        ws′ = subst (λ z → z ═[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]═► t′)
                    eq0 ws
    in  r0 , eq0 , pipeInvS⇒Pr b legCD r0 (weak-pp5-AC r0 b ws′) pinv

  ------------------------------------------------------------------------
  -- (E): `locate″` — the constructive replacement for `WalkLocate.locate`.
  -- Same type, so `AbstractLive.walkPos` swaps `WL.locate pcone` for it.
  ------------------------------------------------------------------------

  -- the pending-cone-free `locate`
  locate″ : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
          → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
          → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × Pr b r0
  locate″ b tr n pn with prodFrame-inv b (drop n tr) pn
  ... | t′ , inj₁ ws = locate-AB b tr n pn t′ ws
  ... | t′ , inj₂ ws = locate-AC b tr n pn t′ ws

------------------------------------------------------------------------
-- (E) CLOSED.  `PipeEvStep.evStepS` (session-33 G2) discharges the last
-- combinator, so `locate` is UNCONDITIONAL: no `pcone`, no premise module.
-- Same type as `WalkLocate.locate`, i.e. the slot `AbstractLive.walkPos` fills.
------------------------------------------------------------------------

-- the premise-free `locate` (drop-in replacement for `WalkLocate.locate pcone`)
locate : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
       → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
       → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × Pr b r0
locate = locate″ evStepS

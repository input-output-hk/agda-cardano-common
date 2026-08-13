{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the VALUE-CARRYING relay classifier
-- (`Praos.PipeValRelay`), SESSION-44 threading 2(a).
--
-- `PipeEvRelay.cpStepKindL-of`'s label component is
--
--     RelayPre x → RelayHas x′ → Σ[ b″ ] evLabel X e a ≡ … recvBFBlock … b″
--
-- with `b″` tied to nothing.  `cpStepKindL-of⁺` widens it INSIDE the existing
-- `Σ` to `… × (relayBlk x′ ≡ b″)`, which is what `LegDriverStep.ldRelay`'s
-- widened `wUp` needs so that `PipeVal` clause (3) can hand clause (4) its value.
--
-- A FULL MIRROR, NOT A WRAPPER — the session-43 cost correction in force.  The
-- twelve non-`cp3` clauses cannot delegate to `cpStepKindL-of`: it returns `x′`
-- ABSTRACTLY, so `RelayHas x′` does not reduce and the vacuity is unavailable at
-- the call site.  Matching the `ConsAdv`/`ProdAdv` witness in each clause makes
-- `x′` concrete and the guard reduces, which is why every clause is two lines.
--
-- The `cp3` clause deliberately uses `WalkDAnchor.cons-c34-anchor` INSTEAD of
-- `consAdv-of`: the latter binds its successor block independently of the
-- label's, which is precisely the gap being closed.
--
-- AGDA 2.8.0 INTERNAL ERROR — TRIGGER AND WORKAROUND (banked; cost two builds).
-- Stating the new component as `relayBlk x′ ≡ b″` — i.e. applying an ACCESSOR
-- FUNCTION to the `with`-abstracted `x′` inside the returned `Σ` — makes Agda
-- die with `__IMPOSSIBLE__` at `TypeChecking/Substitute.hs:139` (a de Bruijn
-- fault during with-abstraction), NOT with a type error.  Naming the successor's
-- SHAPE instead — `x′ ≡ consuming b″ cp4` — typechecks immediately, and is the
-- better interface anyway: the consumer reads `relayBlk` off the equation.
-- RULE: never apply a function to a `with`-abstracted variable inside the
-- result type; equate the variable to a constructor form instead.
--
-- No postulate/hole/meta.  `PipeEvRelay` stays READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValRelay (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃; produce )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; Event )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( decCons; decCP; CPPh; consuming; producing
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; ProdPh; pp0; pp1 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ConsAdv; c01; c12; c23; c34; c45; c56
        ; ProdAdv; a01 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify blkA
  using ( consAdv-of; prodAdv-of )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( bind-ev-inv; step-fcong; output-ev-inv )
-- SESSION-51: the generic `⟶₀` visible-step inversion (the `cp5` hop's tail) and
-- the bind the relay driver is built from
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload})
  using ( ⟶₀-ev-inv )
open import CSP.Operators (Net_Api-≟ {Payload}) using ( _>>=_ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( RelayPre; RelayHas; RelayFwd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriver blkA
  using ( RelayStepKind; rMove; rFwd; rRecv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeProdFire blkA
  using ( IsSBB; decCons-sbb-⊥; decProd-sbb-pp5 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvRelay blkA
  using ( consAdv→rk; prodAdv→rk; pp0≢pp5; padv-pp5-fwd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA
  using ( cons-c34-anchor )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( relayBlk; RelayValOK )

------------------------------------------------------------------------
-- `cpStepKindL-of` with the label component's block tied to the SUCCESSOR's.
------------------------------------------------------------------------

cpStepKindL-of⁺ : (l₁ l₂ : Link) (x : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ x ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ x′ ∈ CPPh ] (M ≡ decCP l₁ l₂ x′) × RelayStepKind x x′
      × (RelayPre x → RelayHas x′
         → Σ[ b″ ∈ Block₃ ]
             (evLabel X e a ≡ evLabel Block₃ (apiBF l₁ hi recvBFBlock) b″)
           × (x′ ≡ consuming b″ cp4))
      × (IsSBB (evLabel X e a) → RelayFwd x′)
      -- SESSION-51: OFF the receive region the relay's recorded block is FIXED,
      -- so the value clause rides across; ON it (`RelayPre x`) the component is
      -- vacuous and the value comes from the co-firing BF client via `wUp`
      × ((RelayPre x → ⊥) → RelayValOK x → RelayValOK x′)
-- cp0/cp1/cp2: the successor is cp1/cp2/cp3, so `RelayHas` is `⊥`
cpStepKindL-of⁺ l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp0 sc
...   | b′ , _ , refl , c01 = consuming b′ cp1 , refl , consAdv→rk c01 , (λ _ hHas → ⊥-elim hHas)
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp0 sc sbb))
                            , (λ _ _ → tt)
cpStepKindL-of⁺ l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp1 sc
...   | b′ , _ , refl , c12 = consuming b′ cp2 , refl , consAdv→rk c12 , (λ _ hHas → ⊥-elim hHas)
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp1 sc sbb))
                            , (λ _ _ → tt)
cpStepKindL-of⁺ l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp2 sc
...   | b′ , _ , refl , c23 = consuming b′ cp3 , refl , consAdv→rk c23 , (λ _ hHas → ⊥-elim hHas)
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp2 sc sbb))
                            , (λ _ _ → tt)
-- cp3: THE REAL CLAUSE.  The anchor names the successor block AND the label's
-- with the SAME `b″`, so the new component is `refl`.
cpStepKindL-of⁺ l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl with cons-c34-anchor l₁ hi b sc
...   | b″ , lbl , refl = consuming b″ cp4 , refl , consAdv→rk c34
                        , (λ _ _ → b″ , lbl , refl)
                        , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp3 sc sbb))
                        , (λ nPre _ → ⊥-elim (nPre tt))
-- cp4/cp5: `RelayPre` is `⊥`
cpStepKindL-of⁺ l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl = consuming b cp5
                    , cong (λ z → z >>= (λ b′ → produce l₂ hi b′)) (output-ev-inv sc)
                    , consAdv→rk c45 , (λ hPre _ → ⊥-elim hPre)
                    , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp4 sc sbb))
                    , (λ _ h → h)
cpStepKindL-of⁺ l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl = consuming b cp6
                    , cong (λ z → z >>= (λ b′ → produce l₂ hi b′))
                           (proj₂ (proj₂ (⟶₀-ev-inv sc)))
                    , consAdv→rk c56 , (λ hPre _ → ⊥-elim hPre)
                    , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp5 sc sbb))
                    , (λ _ h → h)
-- the composite `consuming cp6 → producing pp1` hop: `RelayPre` is `⊥`
cpStepKindL-of⁺ l₁ l₂ (consuming b cp6) step
  with prodAdv-of l₂ hi b pp0 (step-fcong refl step)
... | _ , refl , a01 = producing b pp1 , refl
                     , rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
                     , (λ hPre _ → ⊥-elim hPre)
                     , (λ sbb → ⊥-elim (pp0≢pp5 (decProd-sbb-pp5 l₂ hi b pp0 (step-fcong refl step) sbb)))
                     , (λ _ h → h)
-- produce side: `RelayPre` is `⊥`
cpStepKindL-of⁺ l₁ l₂ (producing b pp) step with prodAdv-of l₂ hi b pp step
... | pp′ , refl , pa = producing b pp′ , refl , prodAdv→rk pa , (λ hPre _ → ⊥-elim hPre)
                      , (λ sbb → padv-pp5-fwd
                          (subst (λ q → ProdAdv q pp′)
                                 (decProd-sbb-pp5 l₂ hi b pp step sbb) pa))
                      , (λ _ h → h)

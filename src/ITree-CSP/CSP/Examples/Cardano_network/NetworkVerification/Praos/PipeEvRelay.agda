{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the GENUINE relay-step classifier (`Praos.PipeEvRelay`).
--
-- `PipeEvDriver.pres-relay` consumes a `WalkMeasure.CPAdv (relayOf l s)
-- (relayOf l s′)` — a SINGLE relay adjacency.  But the relay driver has ONE
-- visible step that is NOT a single `CPAdv`: at the `consuming _ cp6` phase
-- (`Ret b >>= produce = produce b`) a single visible event fires `produce`'s
-- FIRST event, so the phase jumps `consuming b cp6 → producing b pp1` — a
-- 2-hop drop (`cpB` bind hop + `cpP a01`) that no single `CPAdv` constructor
-- represents.  So instead of exposing a genuine `CPAdv`, THIS module classifies
-- the relay's isolated `decCP` transition DIRECTLY into `PipeEvDriver`'s
-- `RelayStepKind` (the `pres-relay`-ready maps): the standard cases go through
-- `cpadv-step (cpC …)` / `cpadv-step (cpP …)`, and the `consuming cp6` composite
-- is built as a plain `rMove` (pre ⊥ ⇒ non-receive; both has ⇒ `RelayHas`
-- preserved).
--
-- Mirror of `WalkClassify.cpAdv-of` (same `bind-ev-inv`/`consAdv-of`/
-- `prodAdv-of`/`step-fcong` inversion structure), replacing the `cpW` drop with
-- the `RelayStepKind`.  LIGHT (pure phase logic, no node cone).  No
-- postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( tt )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeEvRelay (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃; produce )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; sVis )

-- the generic prefix-head fire inversion (for the `cp3` receive-label witness)
import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) as PInv
open PInv using ( Prefix-cont-fires )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( decCP; decCons; decProd
        ; ProdPh; pp0; pp1; pp5; pp6
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; CPPh; consuming; producing )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkMeasure blkA
  using ( ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89
        ; ConsAdv; c01; c12; c23; c34; c45; c56 )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkClassify blkA
  using ( consAdv-of; prodAdv-of )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( bind-ev-inv; step-fcong )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeEvDriver blkA
  using ( RelayStepKind; rMove; rFwd; rRecv )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( NetProc )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( RelayPre; RelayHas; RelayFwd )
-- the `sendBFBlock` tag classifier + the two driver-table inversions (E2)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeProdFire blkA
  using ( IsSBB; decProd-sbb-pp5; decCons-sbb-⊥ )

------------------------------------------------------------------------
-- The genuine relay step classifier: turn the isolated `decCP` transition into
-- the `RelayStepKind` the `pres-relay` glue consumes.
------------------------------------------------------------------------

-- consume-side single adjacency → `RelayStepKind` (blocks may differ: the
-- consume driver rebinds the carried block).  Mirror `cpadv-step (cpC …)` but
-- block-agnostic (the relay predicates read only the phase).  `c34` = the
-- `recvBFBlock` RECEIVE (`cp3 → cp4`, pre → holding).
consAdv→rk : ∀ {b b′ c c′} → ConsAdv c c′ → RelayStepKind (consuming b c) (consuming b′ c′)
consAdv→rk c01 = rMove (λ _ → tt) (λ ()) (λ ()) (λ { (_ , ()) })
consAdv→rk c12 = rMove (λ _ → tt) (λ ()) (λ ()) (λ { (_ , ()) })
consAdv→rk c23 = rMove (λ _ → tt) (λ ()) (λ ()) (λ { (_ , ()) })
consAdv→rk c34 = rRecv tt tt
consAdv→rk c45 = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
consAdv→rk c56 = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })

-- produce-side single adjacency → `RelayStepKind`.  Mirror `cpadv-step (cpP …)`;
-- `a56` = the FORWARD boundary (`pp5 → pp6`, holding → forwarded).
prodAdv→rk : ∀ {b b′ p p′} → ProdAdv p p′ → RelayStepKind (producing b p) (producing b′ p′)
prodAdv→rk a01 = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
prodAdv→rk a12 = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
prodAdv→rk a23 = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
prodAdv→rk a34 = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
prodAdv→rk a45 = rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
prodAdv→rk a56 = rFwd tt tt (λ { (() , _) })
prodAdv→rk a67 = rMove (λ ()) (λ ()) (λ _ → tt) (λ { (() , _) })
prodAdv→rk a78 = rMove (λ ()) (λ ()) (λ _ → tt) (λ { (() , _) })
prodAdv→rk a89 = rMove (λ ()) (λ ()) (λ _ → tt) (λ { (() , _) })

-- classify the relay's isolated `decCP l₁ l₂ x` single visible step: the
-- successor phase `x′`, the process equality, and the `RelayStepKind`.  Mirror
-- of `WalkClassify.cpAdv-of`; the only case NOT a single `CPAdv` is the
-- `consuming cp6` composite (`consuming cp6 → producing pp1`), built as `rMove`.
cpStepKind-of : (l₁ l₂ : Link) (x : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ x ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ x′ ∈ CPPh ] (M ≡ decCP l₁ l₂ x′) × RelayStepKind x x′
cpStepKind-of l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp0 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca
cpStepKind-of l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp1 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca
cpStepKind-of l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp2 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca
cpStepKind-of l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp3 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca
cpStepKind-of l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp4 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca
cpStepKind-of l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp5 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca
-- the composite: `decCP l₁ l₂ (consuming b cp6) = Ret b >>= produce = decProd
-- l₂ hi b pp0`, so a single event fires produce's first hop (`a01`) landing at
-- `producing b pp1`; `rMove` — `consuming cp6` is neither pre nor forwarded, and
-- both source & target `RelayHas` hold
cpStepKind-of l₁ l₂ (consuming b cp6) step
  with prodAdv-of l₂ hi b pp0 (step-fcong refl step)
... | _ , refl , a01 = producing b pp1 , refl
                     , rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
cpStepKind-of l₁ l₂ (producing b pp) step with prodAdv-of l₂ hi b pp step
... | pp′ , refl , pa = producing b pp′ , refl , prodAdv→rk pa

------------------------------------------------------------------------
-- The LABEL-carrying variant (session-26 cone-witness extension): the relay's
-- receive boundary is the ONLY pre→has crossing, and its firing event is the
-- upstream `recvBFBlock` prefix head — so the classifier can HAND OUT the
-- receive-label witness `evLabel X e a ≡ evLabel Block₃ (apiBF l₁ hi
-- recvBFBlock) b″`, guarded by the (refutable elsewhere) pre→has antecedents.
------------------------------------------------------------------------

-- a fired visible step of the `recvBFBlock` prefix phase (`decCons cp3`) is
-- labelled `apiBF l hi recvBFBlock` (decCons-level mirror of
-- `WalkClassify.consD-c34-lbl`, without the `>> Skip` bind)
cons-c34-lbl : (l : Link) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : _}
  → decCons l hi b cp3 ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ b′ ∈ Block₃ ] evLabel X e a ≡ evLabel Block₃ (apiBF l hi recvBFBlock) b′
cons-c34-lbl l b {a = a} (sVis refl br) with Prefix-cont-fires br
... | refl , _ , _ = a , refl

-- the guarded receive-label witness out of a consume-side single adjacency:
-- only `c34` can cross pre→has, and its step is the `cp3` prefix fire; every
-- other adjacency refutes one antecedent
consAdv-recv-lbl : (l₁ : Link) (b : Block₃) {c c′ : ConsPh} {b′ : Block₃}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ : _}
  → ConsAdv c c′
  → decCons l₁ hi b c ─[ ev (evl (evLabel X e a)) ]─► M₁
  → RelayPre (consuming b c) → RelayHas (consuming b′ c′)
  → Σ[ b″ ∈ Block₃ ] evLabel X e a ≡ evLabel Block₃ (apiBF l₁ hi recvBFBlock) b″
consAdv-recv-lbl l₁ b c01 sc _ ()
consAdv-recv-lbl l₁ b c12 sc _ ()
consAdv-recv-lbl l₁ b c23 sc _ ()
consAdv-recv-lbl l₁ b c34 sc _ _ = cons-c34-lbl l₁ b sc
consAdv-recv-lbl l₁ b c45 sc () _
consAdv-recv-lbl l₁ b c56 sc () _

-- `cpStepKind-of` PLUS the guarded receive-label witness (same inversion
-- structure; the label component is genuine only on the `cp3` receive, and
-- vacuously discharged on every other clause by the pre/has exclusivities)
-- out of the OFFERING phase `pp5` the only genuine adjacency is `a56`, landing
-- on `pp6` — a FORWARDED relay position
padv-pp5-fwd : {b : Block₃} {q : ProdPh} → ProdAdv pp5 q → RelayFwd (producing b q)
padv-pp5-fwd a56 = tt

-- `pp0` is not the offering phase
pp0≢pp5 : pp0 ≡ pp5 → ⊥
pp0≢pp5 ()

cpStepKindL-of : (l₁ l₂ : Link) (x : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ x ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ x′ ∈ CPPh ] (M ≡ decCP l₁ l₂ x′) × RelayStepKind x x′
      × (RelayPre x → RelayHas x′
         → Σ[ b″ ∈ Block₃ ] evLabel X e a ≡ evLabel Block₃ (apiBF l₁ hi recvBFBlock) b″)
      -- SESSION-33 (G2b): a `sendBFBlock` fire can only be the PRODUCE leg's
      -- `pp5 → pp6` hop, so the successor is FORWARDED outright
      × (IsSBB (evLabel X e a) → RelayFwd x′)
cpStepKindL-of l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp0 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca , consAdv-recv-lbl l₁ b ca sc
                             , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp0 sc sbb))
cpStepKindL-of l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp1 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca , consAdv-recv-lbl l₁ b ca sc
                             , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp1 sc sbb))
cpStepKindL-of l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp2 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca , consAdv-recv-lbl l₁ b ca sc
                             , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp2 sc sbb))
cpStepKindL-of l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp3 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca , consAdv-recv-lbl l₁ b ca sc
                             , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp3 sc sbb))
cpStepKindL-of l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp4 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca , consAdv-recv-lbl l₁ b ca sc
                             , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp4 sc sbb))
cpStepKindL-of l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp5 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , consAdv→rk ca , consAdv-recv-lbl l₁ b ca sc
                             , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp5 sc sbb))
-- the composite `consuming cp6 → producing pp1` hop: not pre (vacuous label)
cpStepKindL-of l₁ l₂ (consuming b cp6) step
  with prodAdv-of l₂ hi b pp0 (step-fcong refl step)
... | _ , refl , a01 = producing b pp1 , refl
                     , rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
                     , (λ ())
                     , (λ sbb → ⊥-elim (pp0≢pp5 (decProd-sbb-pp5 l₂ hi b pp0 (step-fcong refl step) sbb)))
-- produce-side: not pre (vacuous label)
cpStepKindL-of l₁ l₂ (producing b pp) step with prodAdv-of l₂ hi b pp step
... | pp′ , refl , pa = producing b pp′ , refl , prodAdv→rk pa , (λ ())
                      , (λ sbb → padv-pp5-fwd
                          (subst (λ q → ProdAdv q pp′)
                                 (decProd-sbb-pp5 l₂ hi b pp step sbb) pa))

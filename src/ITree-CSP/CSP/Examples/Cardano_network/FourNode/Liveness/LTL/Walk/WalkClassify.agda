{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the DRIVER-ADVANCE CLASSIFIERS (`Praos.WalkClassify`).
--
-- STEP-0 verdict (settled from the driver scripts + the driver inversions
-- `SysOracle_NodeTauEv.decProd-ev-inv`/`decCons-ev-inv`): the committed
-- driver measure `Walk.μTot` SUFFICES — NO CS/BF peer-weight augmentation is
-- needed.  Reason: the node decode is `bundle ∥⇘ apiES ⇙ driver`, and the model
-- gates ALL api channels (`apiES` synchronises every api event), so every
-- SURVIVING visible event (only apiCS/apiBF/`done` survive `∖ ioES`; the inert
-- apiKA/TS/LN/LF + io are already refuted at every reachable state by
-- `SysBisim.oevB-impl`) is a driver↔bundle SYNC — it advances exactly ONE
-- driver phase by exactly ONE linear-script adjacency (`decProd-ev-inv` maps
-- pp0→pp1→…→pp9 deterministically; `decCons-ev-inv` maps cp0→…→cp6, with the
-- `recvBFBlock` = `arrivedD` event being the cp3→cp4 hop).  Peer FSM positions
-- also move in lock-step, but `μTot` never reads them (`WalkMeasure.μGk-cong`),
-- so they are measure-neutral.  A `break` advances the finite break budget.
-- No surviving visible event fails to advance the measure.
--
-- THIS module extracts, from a driver step, the ORDER-THEORETIC adjacency
-- witness (`WalkMeasure.ProdAdv`/`ConsAdv`/`CPAdv`) that the whole-system
-- measure lemmas `μGk-adv-*` consume, re-inverting each driver phase (mirror of
-- `decProd-ev-inv`/`decCons-ev-inv`, but returning the ADJACENCY constructor
-- alongside the successor phase).  These classifiers are the arithmetic heart
-- of `WalkEngine.deliver`'s ev-hop: once the forward node peel identifies the
-- firing node + its driver step, these turn that step into the `μTot` strict
-- decrease.
--
-- No postulates, holes, or `--allow-unsolved-metas`.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( _<_ )
open import Data.Nat.Properties using ( ≤-refl; <-trans; +-monoʳ-< )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify (blkA : Block₃) where

------------------------------------------------------------------------
-- The model, driver decodes, driver phases, and the measure adjacencies.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃; produce )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload; Header; header )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( decProd; decCons; decConsD; decCP
        ; ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; CPPh; consuming; producing
        ; ConsDPh; consD; cblk; cph )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89
        ; ConsAdv; c01; c12; c23; c34; c45; c56
        ; CPAdv; cpC; cpB; cpP
        ; cpW; prodW-adv; consW-adv )

-- the driver-step inversion primitives: the generic `⟶₀` visible-step
-- inversion (from the general prefix-inversion laws) + the `Output`/`Prefix`
-- inversions, the `ret`-has-no-ev refuter, and the single-step `>>=` inversion
-- (from the node-τ-ev module)
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload})
  using ( ⟶₀-ev-inv; Prefix-cont-fires )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( output-ev-inv; prefix-ev-inv; ret-no-ev; bind-ev-inv; step-fcong )
-- `Skip` (the `>> Skip` tail of node-D's consume driver `decConsD`)
open import CSP.Operators (Net_Api-≟ {Payload}) using ( Skip; Prefix )

------------------------------------------------------------------------
-- The LTS visible-transition vocabulary.
------------------------------------------------------------------------

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; sVis )

-- the whole-system process type at the shared alphabet
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the block-carrying driver decode's return type (`consume` returns a `Block₃`)
ConsProc : Set₁
ConsProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃

------------------------------------------------------------------------
-- PRODUCE driver: a visible step advances the produce phase by one adjacency.
--
-- Mirror of `decProd-ev-inv`, appending the `ProdAdv` witness.  Each phase
-- pp0..pp8 fires its head api event (`⟶₀`/`Output`) and lands on the successor
-- phase; pp9 = `Skip` offers no visible event (refuted by `ret-no-ev`).
------------------------------------------------------------------------

prodAdv-of : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pp′ ∈ ProdPh ] (M ≡ decProd l d blk pp′) × ProdAdv pp pp′
prodAdv-of l d blk pp0 step with ⟶₀-ev-inv step
... | _ , _ , refl = pp1 , refl , a01
prodAdv-of l d blk pp1 step with ⟶₀-ev-inv step
... | _ , _ , refl = pp2 , refl , a12
prodAdv-of l d blk pp2 step = pp3 , output-ev-inv step , a23
prodAdv-of l d blk pp3 step with ⟶₀-ev-inv step
... | _ , _ , refl = pp4 , refl , a34
prodAdv-of l d blk pp4 step = pp5 , output-ev-inv step , a45
prodAdv-of l d blk pp5 step = pp6 , output-ev-inv step , a56
prodAdv-of l d blk pp6 step = pp7 , output-ev-inv step , a67
prodAdv-of l d blk pp7 step with ⟶₀-ev-inv step
... | _ , _ , refl = pp8 , refl , a78
prodAdv-of l d blk pp8 step with ⟶₀-ev-inv step
... | _ , _ , refl = pp9 , refl , a89
prodAdv-of l d blk pp9 step = ⊥-elim (ret-no-ev refl step)

------------------------------------------------------------------------
-- CONSUME driver: a visible step advances the consume phase by one adjacency.
--
-- Mirror of `decCons-ev-inv`, appending the `ConsAdv` witness.  cp1/cp3 are the
-- data-carrying `recvCSRollforward`/`recvBFBlock` phases (`Prefix`, new block
-- `b′`); the others are `⟶₀`/`Output`.  The cp3→cp4 hop is D's `recvBFBlock` =
-- `arrivedD`.  The `ConsAdv` reads only the phase, so the received block is
-- existentially returned but measure-irrelevant.  cp6 = `Ret` (refuted).
------------------------------------------------------------------------

consAdv-of : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : ConsProc}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ b′ ∈ Block₃ ] Σ[ cp′ ∈ ConsPh ] (M ≡ decCons l d b′ cp′) × ConsAdv cp cp′
consAdv-of l d b cp0 step with ⟶₀-ev-inv step
... | _ , _ , refl = b , cp1 , refl , c01
consAdv-of l d b cp1 step with prefix-ev-inv step
... | (header b′ , _) , refl = b′ , cp2 , refl , c12
consAdv-of l d b cp2 step = b , cp3 , output-ev-inv step , c23
consAdv-of l d b cp3 step with prefix-ev-inv step
... | b′ , refl = b′ , cp4 , refl , c34
consAdv-of l d b cp4 step = b , cp5 , output-ev-inv step , c45
consAdv-of l d b cp5 step with ⟶₀-ev-inv step
... | _ , _ , refl = b , cp6 , refl , c56
consAdv-of l d b cp6 step = ⊥-elim (ret-no-ev refl step)

------------------------------------------------------------------------
-- NODE-D consume driver (`decConsD = decCons … >> Skip`): a visible step
-- advances the consume phase by one adjacency.  Mirror of `decConsD-ev-inv`:
-- fire the inner consume event through the `>> Skip` bind (`bind-ev-inv`) and
-- delegate to `consAdv-of`; cp6 = `Ret b >> Skip = Skip = ret` (refuted).  This
-- is the D-side classifier whose cp3→cp4 hop IS `arrivedD` (`recvBFBlock@D`).
-- The `ConsAdv` reads only the phase, so `WalkMeasure.consDW-adv` gives the
-- `consDW` strict decrease regardless of the (rebound) carried block.
------------------------------------------------------------------------

consDAdv-of : (l : Link) (cd : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cd ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ b′ ∈ Block₃ ] Σ[ cp′ ∈ ConsPh ] (M ≡ decConsD l (consD b′ cp′)) × ConsAdv (cph cd) cp′
consDAdv-of l (consD b cp0) step with bind-ev-inv (λ _ → Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl with consAdv-of l hi b cp0 sc
...   | b′ , cp′ , refl , ca = b′ , cp′ , refl , ca
consDAdv-of l (consD b cp1) step with bind-ev-inv (λ _ → Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl with consAdv-of l hi b cp1 sc
...   | b′ , cp′ , refl , ca = b′ , cp′ , refl , ca
consDAdv-of l (consD b cp2) step with bind-ev-inv (λ _ → Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl with consAdv-of l hi b cp2 sc
...   | b′ , cp′ , refl , ca = b′ , cp′ , refl , ca
consDAdv-of l (consD b cp3) step with bind-ev-inv (λ _ → Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl with consAdv-of l hi b cp3 sc
...   | b′ , cp′ , refl , ca = b′ , cp′ , refl , ca
consDAdv-of l (consD b cp4) step with bind-ev-inv (λ _ → Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl with consAdv-of l hi b cp4 sc
...   | b′ , cp′ , refl , ca = b′ , cp′ , refl , ca
consDAdv-of l (consD b cp5) step with bind-ev-inv (λ _ → Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl with consAdv-of l hi b cp5 sc
...   | b′ , cp′ , refl , ca = b′ , cp′ , refl , ca
consDAdv-of l (consD b cp6) step = ⊥-elim (ret-no-ev refl step)

------------------------------------------------------------------------
-- DELIVERING-HOP LABEL CLASSIFIER (the `deliver`/`arrivedD` linchpin).
--
-- Node D's consume driver at phase `cp3` (`decConsD l (consD b cp3) =
-- decCons l hi b cp3 >> Skip`, and `decCons l hi b cp3 = apiBF l hi
-- recvBFBlock ⟶ …`) fires EXACTLY the event `apiBF l hi recvBFBlock`, whose
-- carried value is the received block `b′`.  This exposes that label identity
-- (the c34 = cp3→cp4 hop is the ONLY `recvBFBlock` hop of the consume driver),
-- so a delivering step's whole-system event is pinned to
-- `apiBF l hi recvBFBlock` — the fact `deliver` needs to tie the D-consume
-- c34 phase advance to the `arrivedD` atom (link `l`, dir `hi`, value `b′`).
------------------------------------------------------------------------

-- The delivering-hop label extractor.  `prefix-ev-inv` discards the fired
-- label (its result type omits `X`/`e`/`a`), so the `sVis`/`Prefix-cont-fires`
-- match is INLINED here: matching `sVis refl br` + the `(Block₃, apiBF l hi
-- recvBFBlock) ≡ (X, e)` head equality (`Prefix-cont-fires`) forces `X ≡ Block₃`
-- and `e ≡ apiBF l hi recvBFBlock` IN THIS scope, so the received value `a` is a
-- `Block₃` and the label identity holds by `refl`.
consD-c34-lbl : (l : Link) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b cp3) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ b′ ∈ Block₃ ] evLabel X e a ≡ evLabel Block₃ (apiBF l hi recvBFBlock) b′
consD-c34-lbl l b {a = a} step with bind-ev-inv (λ _ → Skip) (decCons l hi b cp3) refl step
... | _ , sVis refl br , refl with Prefix-cont-fires br
...   | refl , _ , _ = a , refl

------------------------------------------------------------------------
-- RELAY driver (`decCP = decCons l₁ hi >>= produce l₂ hi`): a visible step
-- strictly decreases the relay weight `cpW`.  Mirror of `decCP-ev-inv`, but
-- returning a DIRECT `cpW`-strict-decrease (NOT a single `CPAdv`): the
-- `consuming cp6 → producing pp1` boundary is a SINGLE visible event that both
-- crosses the `>>=`-ret bind hop AND fires `produce`'s first event, so it drops
-- `cpW` by 2 (10 → 8) — two `CPAdv` steps' worth, hence the direct arithmetic.
--   · consuming cp0..cp5 : fire the inner consume (`bind-ev-inv` + `consAdv-of`),
--     `cpW (consuming _ cp′) = 10 + consW cp′ < 10 + consW cp`;
--   · consuming cp6 : the definitional `Ret b >>= produce l₂ hi` reduction views
--     the step as `produce l₂ hi b`'s first (`step-fcong refl` + `prodAdv-of` at
--     pp0), `cpW (producing _ pp′) = prodW pp′ < 9 < 10 = cpW (consuming _ cp6)`;
--   · producing pp : delegate to `prodAdv-of` (`decCP … producing = decProd`).
------------------------------------------------------------------------

cpAdv-of : (l₁ l₂ : Link) (x : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ x ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ x′ ∈ CPPh ] (M ≡ decCP l₁ l₂ x′) × (cpW x′ < cpW x)
cpAdv-of l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp0 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , +-monoʳ-< 10 (consW-adv ca)
cpAdv-of l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp1 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , +-monoʳ-< 10 (consW-adv ca)
cpAdv-of l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp2 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , +-monoʳ-< 10 (consW-adv ca)
cpAdv-of l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp3 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , +-monoʳ-< 10 (consW-adv ca)
cpAdv-of l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp4 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , +-monoʳ-< 10 (consW-adv ca)
cpAdv-of l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp5 sc
...   | b′ , cp′ , refl , ca = consuming b′ cp′ , refl , +-monoʳ-< 10 (consW-adv ca)
cpAdv-of l₁ l₂ (consuming b cp6) step
  with prodAdv-of l₂ hi b pp0 (step-fcong refl step)
... | pp′ , refl , pa = producing b pp′ , refl , <-trans (prodW-adv pa) ≤-refl
cpAdv-of l₁ l₂ (producing b pp) step with prodAdv-of l₂ hi b pp step
... | pp′ , refl , pa = producing b pp′ , refl , prodW-adv pa

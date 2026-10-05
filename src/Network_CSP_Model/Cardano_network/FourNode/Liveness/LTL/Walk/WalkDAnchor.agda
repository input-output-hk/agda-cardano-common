{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the DELIVERING-HOP VALUE ANCHOR
-- (`Praos.WalkDAnchor`), SESSION-36 step (i).
--
-- THE PROBLEM (session-35 interface finding).  `WalkClassify.consD-c34-lbl`
-- returns the delivering label with the received block EXISTENTIAL:
--
--     Σ[ b″ ∈ Block₃ ] evLabel X e a ≡ evLabel Block₃ (apiBF l hi recvBFBlock) b″
--
-- and `WalkClassify.consDAdv-of` returns the SUCCESSOR slot `consD b′ cp′` with
-- its own, separately-bound `b′`.  Nothing ties `b″` to `b′`, so the value
-- invariant `PipeValInv.PipeVal` — which pins the block *in the state* — cannot
-- reach the block *on the label*.  That gap is what forced `arrivedD` to drop
-- its `a ≡ b` conjunct.
--
-- THE ANCHOR.  Both `b′` and `b″` ARE the fired value `a`: `decCons l hi b cp3`
-- is the `Prefix (apiBF l hi recvBFBlock) (λ b′ → decCons l hi b′ cp4)` whose
-- continuation family is indexed by the fired value (machine-checked as
-- `PipeValGate.cons-cp3-rebind`).  `consD-c34-anchor` below returns them as ONE
-- witness — label identity AND successor slot, same `b′` — so
-- `PipeValInv.pipeVal⇒recorded` at the delivering SUCCESSOR discharges
-- `b″ ≡ blkA`.
--
-- WHY IT IS A SEPARATE LEAF.  `WalkClassify` stays READ-ONLY: the anchor needs
-- no change to any existing statement, only a strictly stronger companion.  The
-- module is imported by `WalkApiDrop` alone.
--
-- METHOD NOTE.  The value pin cannot go through `WalkClassify.prefix-ev-inv`
-- (it existentialises the value) nor through `Prefix-cont-fires` (same).  The
-- offer-map `with` is INLINED here, exactly as `SysOracle_NodeTauEv.output-ev-inv`
-- does for `Output`: matching `yes refl` on `Net_Api-≟` both unifies the fired
-- carrier/event with the prefix's own AND reduces `Prefix-cont` to `just (P a)`,
-- so `just-injective` names the successor at the FIRED value.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_; proj₁; proj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe.Properties using ( just-injective )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; cong )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃; produce )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; sVis )

open import CSP.Operators (Net_Api-≟ {Payload}) using ( Skip; _>>=_ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( decCons; decConsD; decCP
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; ConsDPh; consD; cblk; cph
        ; CPPh; consuming; producing )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( bind-ev-inv; nothing-absurd; output-ev-inv; ret-no-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ConsAdv; c34; c45; c56 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify blkA
  using ( consDAdv-of )
-- SESSION-51: the generic `⟶₀` visible-step inversion (the `cp5` hop's tail)
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload})
  using ( ⟶₀-ev-inv )

-- the whole-system process type at the shared alphabet
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

------------------------------------------------------------------------
-- THE ANCHOR.  A visible step of node D's consume driver at `cp3` fires
-- `apiBF l hi recvBFBlock` carrying some `b′`, AND lands on the slot
-- `consD b′ cp4` carrying THE SAME `b′`.  This is the conjunction
-- `consD-c34-lbl` and `consDAdv-of` each deliver half of.
------------------------------------------------------------------------

-- the delivering `cp3 → cp4` hop: label value = recorded value
consD-c34-anchor : (l : Link) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b cp3) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ b′ ∈ Block₃ ]
      (evLabel X e a ≡ evLabel Block₃ (apiBF l hi recvBFBlock) b′)
    × (M ≡ decConsD l (consD b′ cp4))
consD-c34-anchor l b {X} {e} {a} step
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp3) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload} (Block₃ , apiBF l hi recvBFBlock) (X , e)
...   | no  _    = ⊥-elim (nothing-absurd br)
...   | yes refl = a , refl , cong (λ z → z >>= (λ _ → Skip)) (sym (just-injective br))

------------------------------------------------------------------------
-- THE ANCHORED CLASSIFIER.  `WalkClassify.consDAdv-of` with the delivering
-- label identity attached AT THE SAME successor block `b′` — the drop-in
-- replacement the node-D peels need, so that the `dBD`/`dCD` reports can carry
-- `cblk (cons-BD (nD s′)) ≡ b″` by `refl`.
--
-- The `cp3` clause is the anchor above; every other source phase discharges
-- the `≡ cp3` trigger by absurdity, so the strengthening is FREE off the
-- delivering hop.
------------------------------------------------------------------------

-- SESSION-51: the POST-RECEIVE region of the consume phase (`cp4`/`cp5`/`cp6`) —
-- exactly `PipeInv.ConsRecv`, but restated here because `PipeInv` sits ABOVE this
-- module in the import order (`PipeInv → WalkPr → WalkDExpose → WalkApiDrop →
-- WalkDAnchor`), so importing it would be a cycle
ConsHeld : ConsPh → Set
ConsHeld cp0 = ⊥
ConsHeld cp1 = ⊥
ConsHeld cp2 = ⊥
ConsHeld cp3 = ⊥
ConsHeld cp4 = ⊤
ConsHeld cp5 = ⊤
ConsHeld cp6 = ⊤

-- node-D consume classifier PLUS the value-anchored delivering label AND
-- (SESSION-51) the block FIXITY past the receive: off the `cp3` hop the recorded
-- block never changes, which is what `PipeValInv`'s clause (8) needs on the
-- `c45`/`c56` tail hops (`consAdv-of` returns exactly `b` there, but
-- existentialises it, so the two post-receive clauses are re-derived directly
-- off `output-ev-inv`/`⟶₀-ev-inv` instead of delegating).
consDAdv-of⁺ : (l : Link) (cd : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cd ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ b′ ∈ Block₃ ] Σ[ cp′ ∈ ConsPh ]
      (M ≡ decConsD l (consD b′ cp′)) × ConsAdv (cph cd) cp′
    × (cph cd ≡ cp3 → evLabel X e a ≡ evLabel Block₃ (apiBF l hi recvBFBlock) b′)
    × (ConsHeld (cph cd) → b′ ≡ cblk cd)
consDAdv-of⁺ l (consD b cp3) step with consD-c34-anchor l b step
... | b′ , lbl , meq = b′ , cp4 , meq , c34 , (λ _ → lbl) , λ ()
consDAdv-of⁺ l (consD b cp0) step with consDAdv-of l (consD b cp0) step
... | b′ , cp′ , meq , ca = b′ , cp′ , meq , ca , (λ ()) , λ ()
consDAdv-of⁺ l (consD b cp1) step with consDAdv-of l (consD b cp1) step
... | b′ , cp′ , meq , ca = b′ , cp′ , meq , ca , (λ ()) , λ ()
consDAdv-of⁺ l (consD b cp2) step with consDAdv-of l (consD b cp2) step
... | b′ , cp′ , meq , ca = b′ , cp′ , meq , ca , (λ ()) , λ ()
-- the `cp4 → cp5` hop: an `Output` (`sendBFClientDone !`) whose tail IS
-- `decCons l hi b cp5` — the SAME block, read off the step, not existentialised
consDAdv-of⁺ l (consD b cp4) step
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl =
      b , cp5 , cong (λ z → z >>= (λ _ → Skip)) (output-ev-inv sc) , c45
    , (λ ()) , λ _ → refl
-- the `cp5 → cp6` hop: a `⟶₀` whose tail is `Ret b` = `decCons l hi b cp6`
consDAdv-of⁺ l (consD b cp5) step
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl =
      b , cp6 , cong (λ z → z >>= (λ _ → Skip)) (proj₂ (proj₂ (⟶₀-ev-inv sc))) , c56
    , (λ ()) , λ _ → refl
-- `cp6` is `Ret b >> Skip`: no visible step at all
consDAdv-of⁺ l (consD b cp6) step = ⊥-elim (ret-no-ev refl step)

------------------------------------------------------------------------
-- THE RELAY-SIDE ANCHOR.  The relay driver `decCP l₁ l₂ = decCons l₁ hi >>=
-- produce l₂ hi` has exactly the same `cp3 → cp4` hop as node D's consumer, and
-- `PipeEvRelay.cpStepKindL-of` drops the tie in exactly the same way
-- (`consAdv-of` names the successor's block, `consAdv-recv-lbl` names the
-- label's, nothing relates them).  Same proof as `consD-c34-anchor`, with
-- `produce l₂ hi` in place of the `>> Skip` continuation.
--
-- This is the witness `LegDriverStep.ldRelay`'s widened `wUp` needs, so that
-- `PipeVal` clause (3) can hand clause (4) its value.
------------------------------------------------------------------------

-- the relay's delivering `cp3 → cp4` hop: label value = recorded value
consCP-c34-anchor : (l₁ l₂ : Link) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ (consuming b cp3) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ b′ ∈ Block₃ ]
      (evLabel X e a ≡ evLabel Block₃ (apiBF l₁ hi recvBFBlock) b′)
    × (M ≡ decCP l₁ l₂ (consuming b′ cp4))
consCP-c34-anchor l₁ l₂ b {X} {e} {a} step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp3) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload} (Block₃ , apiBF l₁ hi recvBFBlock) (X , e)
...   | no  _    = ⊥-elim (nothing-absurd br)
...   | yes refl =
        a , refl , cong (λ z → z >>= (λ b′ → produce l₂ hi b′)) (sym (just-injective br))

------------------------------------------------------------------------
-- THE BARE `decCons` ANCHOR.  Simpler than both siblings — `decCons l d b cp3`
-- IS the `Prefix`, with no bind wrapper at all — and it is what the relay
-- classifier needs, because there the successor block must be the one the
-- anchor names (using `consAdv-of` instead would re-introduce the very gap the
-- anchor closes: its `b′` is bound independently of the label's).
------------------------------------------------------------------------

-- the consume driver's delivering `cp3 → cp4` hop: label value = successor block
cons-c34-anchor : (l : Link) (d : Dir) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp3 ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ b′ ∈ Block₃ ]
      (evLabel X e a ≡ evLabel Block₃ (apiBF l d recvBFBlock) b′)
    × (M ≡ decCons l d b′ cp4)
cons-c34-anchor l d b {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (Block₃ , apiBF l d recvBFBlock) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = a , refl , sym (just-injective br)

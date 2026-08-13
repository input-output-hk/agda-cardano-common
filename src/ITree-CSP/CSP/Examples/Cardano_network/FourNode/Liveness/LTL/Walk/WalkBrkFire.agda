{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 (SESSION-34, `wprog` discharge) — the BREAK-OFFER
-- INTRO and its consequences (`Praos.WalkBrkFire`).
--
-- THE OBSERVATION THAT DELETES THE `wprog` PREMISE: an UNBROKEN link's
-- decode is `renameMap (copy fold) △ (break l ⟶₀ Skip)` — an interrupt
-- whose `break l` offer is available at EVERY cell-phase (the fold's force
-- is a react at ANY phases, `fold-react`), and the whole-system stack
-- keeps it visible (`break ∉ ioES`, medium solo).  Hence:
--
--   · `sys-break-fire`     — `broken (med s) l ≡ false` ⇒ `absDec s` FIRES
--     `break l` (the positive offer-INTRO; medium-level `sVis` on the `△`
--     merge, lifted by the frozen `lift-med-whole-ev`).
--   · `sys-break-unbroken` — the converse inversion (via the frozen
--     `link-break-chan` + `link-broken-false`), making the `broken` flag
--     DECODE-TRANSPORTABLE:
--   · `unb-transport`      — `absDec s ≡ absDec s′` carries unbrokenness
--     across INDEPENDENTLY-constructed reachable states (the radec-not-
--     injective trap of session 30 is dodged SEMANTICALLY: the offer is
--     readable off the tree).
--   · `unb-stuck-⊥` / `unb-ret-⊥` — a state with an unbroken link is
--     neither stuck nor a `ret`: the confinement-side replacement for
--     `WalkEnabled`'s `wprog`-driven terminal refutations.
--
-- Plus the `GSide`/`Unb` vocabulary: the CONFINED group (`□¬brkG1` protects
-- {AB,BD} = `g1`; `□¬brkG2` protects {AC,CD} = `g2`) and the walk invariant
-- `Unb gs s` = both protected links still unbroken.
--
-- No postulate/hole/meta; no `dne`.  All base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀; tt to tt₀ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Bool using ( Bool; true; false )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Nullary using ( ¬_; yes; no )
import Data.Fin.Properties as FinP
open import Data.Fin using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans; subst )

open import Process_Trees using ( PTree; ExtI; ret; react; AnyTypes; ContinueType )
open import Data.Maybe using ( Maybe; just; nothing )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBrkFire (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net; Net-≟; Net_Api; Net_Api-≟; Link; break )
open import Data.List using ( map )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; IDs )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( ⦀Fin; Skip; _⦀_; _△_; △-merge; viewV; _∥⇘_⇙_; _∖_ )

-- Net Payload operators (the pre-rename copy medium): the `⦀⋆` fold
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; sVis; ev-inv )
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( IsStuck )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; phase; broken; decLink; decMed; decCopy; CopyPhase; NetProc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep
  using ( absDec; absNodesOf; lift-med-whole-ev; reflect-top-ev
        ; medEv; nodesEv; ⦀-ev-L; ⦀-ev-R; ⦀-noOffer; IoOffers )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( fold-react; ReactF; mkReactF; force-△-react )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( ⦀Fin-ev-inv; ret-no-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBreakDrop blkA
  using ( link-broken-false )

------------------------------------------------------------------------
-- §1  The per-link break FIRE: an unbroken link's decode offers `break i`
--     at EVERY cell phase — the `△`'s right operand commits.
------------------------------------------------------------------------

-- the whole-alphabet visible-offer map type (the `react` payload)
VmapA : Set₁
VmapA = (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe NetProc)

-- the whole-alphabet τ-branch map type (the `react` payload's second slot)
TmapA : Set₁
TmapA = (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe NetProc)

-- the `△` interrupt FIRES the right operand's offer when the left refuses:
-- the offer maps are pinned by the force-equality ARGUMENT TYPES (first-order),
-- and `△-merge`'s with-pair reduces once both scrutinees are rewritten — the
-- intro mirror of the frozen `SysRoute.△-Q-ev-inv`
△-fire-Q : {P Q : NetProc} {vP : VmapA} {τcP : TmapA} {vQ : VmapA} {τcQ : TmapA}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Q′ : NetProc}
  → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
  → vP (X , e) a ≡ nothing → vQ (X , e) a ≡ just Q′
  → (P △ Q) ─[ ev (evl (evLabel X e a)) ]─► Q′
△-fire-Q {P} {Q} {vP} {τcP} {vQ} {τcQ} {X} {e} {a} {Q′} eqP eqQ vPno vQj =
  sVis (force-△-react eqP eqQ) mergeEq
  where
    mergeEq : △-merge (react vP τcP) (react vQ τcQ) Q (X , e) a ≡ just Q′
    mergeEq rewrite vPno | vQj = refl

-- `Skip` pinned at the whole-system result level (kills the `ℓr` level meta)
SkipN : NetProc
SkipN = Skip

-- the `break i ⟶₀ Skip` prefix offers `just Skip` at its OWN event: the
-- event-decidability chain bottoms out at the link's `Fin` self-test `i ≟ i`
prefix-self-offer : (i : Link)
  → viewV (PTree.force (Op.Prefix₀ (break i) SkipN)) (⊤₀ , break i) tt₀ ≡ just SkipN
prefix-self-offer i with i FinP.≟ i
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- an unbroken link fires its own `break i`, landing on `Skip`: the fold's
-- force is a react (`fold-react`, any phases), the rename keeps it a react
-- with NO break offer (`ιNet⁻¹ (break i) ≡ nothing`, definitional), so the
-- `△-merge` commits to the prefix's `just Skip`
link-break-fire : (i : Link) (ph : Dir → IDs → CopyPhase)
  → decLink i ph false ─[ ev (evl (evLabel ⊤₀ (break i) tt₀)) ]─► SkipN
link-break-fire i ph with fold-react i ph
... | mkReactF V T feq =
      △-fire-Q
        (STC.MedNO.force-renameMap-react
          {P = ⦀⋆ (map (λ { (d , id) → decCopy i d id (ph d id) }) (linkConfig i))}
          feq)
        refl refl (prefix-self-offer i)

-- a DIFFERENT link (or a broken one) offers nothing on `break l`:
-- `link-break-chan` pins any break fire to the link's OWN channel
link-no-other-break : (j : Link) (ph : Dir → IDs → CopyPhase) (bj : Bool)
    {l : Link} {a : ⊤₀}
  → j ≢ l → ¬ IoOffers (decLink j ph bj) (break l) a
link-no-other-break j ph bj j≢l (M , st) =
  j≢l (proj₁ (SR.link-break-chan j ph bj st))

------------------------------------------------------------------------
-- §2  The MEDIUM break fire: lift the firing link through the four-link
--     `⦀Fin` interleave (siblings refuse by §1's channel pinning).
------------------------------------------------------------------------

-- shorthand: the medium's per-link component function
medF : (m : MedState) → Link → NetProc
medF m i = decLink i (phase m i) (broken m i)

-- sibling non-offer, packaged at a medium state
medF-no-break : (m : MedState) (j : Link) {l : Link} {a : ⊤₀}
  → j ≢ l → ¬ IoOffers (medF m j) (break l) a
medF-no-break m j j≢l = link-no-other-break j (phase m j) (broken m j) j≢l

-- `SkipN` (the `⦀Fin zero` tail) offers nothing
skip-no-ev : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ¬ IoOffers SkipN e a
skip-no-ev (M , st) = ret-no-ev {P = SkipN} refl st

-- the fired component's step, with the `broken ≡ false` hypothesis rewritten in
medF-fire : (m : MedState) (l : Link) → broken m l ≡ false
  → medF m l ─[ ev (evl (evLabel ⊤₀ (break l) tt₀)) ]─► SkipN
medF-fire m l ef =
  subst (λ b → decLink l (phase m l) b ─[ ev (evl (evLabel ⊤₀ (break l) tt₀)) ]─► SkipN)
        (sym ef) (link-break-fire l (phase m l))

-- an unbroken link's `break l` fires out of the WHOLE medium `decMed m`.
-- The step is built at the EXPLICIT four-link `⦀`-nest (all operands spelled
-- out — `⦀`/`decMed` are defined functions, so meta-laden unification stalls)
-- and carried to `decMed m` by the definitional home-equality `nestEq`.
module _ (m : MedState) where

  private
    f0 f1 f2 f3 rest1 rest2 rest3 : NetProc
    f0 = medF m linkAB
    f1 = medF m linkAC
    f2 = medF m linkBD
    f3 = medF m linkCD
    rest3 = f3 ⦀ SkipN
    rest2 = f2 ⦀ rest3
    rest1 = f1 ⦀ rest2

    -- the medium decode IS the explicit nest (definitional: `numLinks = 4`)
    nestEq : decMed m ≡ (f0 ⦀ rest1)
    nestEq = refl

  medium-break-fire : (l : Link) → broken m l ≡ false
    → Σ[ M ∈ NetProc ] (decMed m ─[ ev (evl (evLabel ⊤₀ (break l) tt₀)) ]─► M)
  medium-break-fire fzero ef =
    _ , subst (λ z → z ─[ ev (evl (evLabel ⊤₀ (break linkAB) tt₀)) ]─► (SkipN ⦀ rest1))
          (sym nestEq)
          (⦀-ev-L f0 rest1 (medF-fire m linkAB ef)
            (noOffer→viewV rest1
              (⦀-noOffer f1 rest2 (medF-no-break m linkAC (λ ()))
                (⦀-noOffer f2 rest3 (medF-no-break m linkBD (λ ()))
                  (⦀-noOffer f3 SkipN (medF-no-break m linkCD (λ ()))
                    skip-no-ev)))))
  medium-break-fire (fsuc fzero) ef =
    _ , subst (λ z → z ─[ ev (evl (evLabel ⊤₀ (break linkAC) tt₀)) ]─► (f0 ⦀ ((SkipN ⦀ rest2))))
          (sym nestEq)
          (⦀-ev-R f0 rest1
            (⦀-ev-L f1 rest2 (medF-fire m linkAC ef)
              (noOffer→viewV rest2
                (⦀-noOffer f2 rest3 (medF-no-break m linkBD (λ ()))
                  (⦀-noOffer f3 SkipN (medF-no-break m linkCD (λ ()))
                    skip-no-ev))))
            (noOffer→viewV f0 (medF-no-break m linkAB (λ ()))))
  medium-break-fire (fsuc (fsuc fzero)) ef =
    _ , subst (λ z → z ─[ ev (evl (evLabel ⊤₀ (break linkBD) tt₀)) ]─► (f0 ⦀ (f1 ⦀ (SkipN ⦀ rest3))))
          (sym nestEq)
          (⦀-ev-R f0 rest1
            (⦀-ev-R f1 rest2
              (⦀-ev-L f2 rest3 (medF-fire m linkBD ef)
                (noOffer→viewV rest3
                  (⦀-noOffer f3 SkipN (medF-no-break m linkCD (λ ()))
                    skip-no-ev)))
              (noOffer→viewV f1 (medF-no-break m linkAC (λ ()))))
            (noOffer→viewV f0 (medF-no-break m linkAB (λ ()))))
  medium-break-fire (fsuc (fsuc (fsuc fzero))) ef =
    _ , subst (λ z → z ─[ ev (evl (evLabel ⊤₀ (break linkCD) tt₀)) ]─► (f0 ⦀ (f1 ⦀ (f2 ⦀ (SkipN ⦀ SkipN)))))
          (sym nestEq)
          (⦀-ev-R f0 rest1
            (⦀-ev-R f1 rest2
              (⦀-ev-R f2 rest3
                (⦀-ev-L f3 SkipN (medF-fire m linkCD ef)
                  (noOffer→viewV SkipN (skip-no-ev {⊤₀} {break linkCD} {tt₀})))
                (noOffer→viewV f2 (medF-no-break m linkBD (λ ()))))
              (noOffer→viewV f1 (medF-no-break m linkAC (λ ()))))
            (noOffer→viewV f0 (medF-no-break m linkAB (λ ()))))

------------------------------------------------------------------------
-- §3  The WHOLE-SYSTEM break fire and its inversion: the `broken` flag is
--     readable off the decode.
------------------------------------------------------------------------

-- the offer-INTRO: an unbroken link fires `break l` out of `absDec s`
-- (medium solo through the io-gate: `break ∉ ioES`, abstract nodes refuse)
sys-break-fire : (s : SysState) (l : Link) → broken (med s) l ≡ false
  → Σ[ M ∈ NetProc ] (absDec s ─[ ev (evl (evLabel ⊤₀ (break l) tt₀)) ]─► M)
sys-break-fire s l ef =
  let (M₁ , ms) = medium-break-fire (med s) l ef
  in  ((M₁ ∥⇘ ioES ⇙ absNodesOf s) ∖ ioES)
    , lift-med-whole-ev (decMed (med s)) (absNodesOf s)
        (SR.break∉ioES {l} {tt₀}) ms
        (noOffer→viewV (absNodesOf s) (SR.absnodes-no-break s))

-- the INVERSION: a `break l` fire out of `absDec s` forces the flag `false`
-- (nodes refuse break; the medium's fired link is pinned to `l` and unbroken)
sys-break-unbroken : (s : SysState) (l : Link) {a : ⊤₀} {M : NetProc}
  → absDec s ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → broken (med s) l ≡ false
sys-break-unbroken s l step
    with reflect-top-ev (decMed (med s)) (absNodesOf s)
           (inj₂ (SR.absnodes-no-break s)) step
... | nodesEv N₁ ns _ = ⊥-elim (SR.absnodes-no-break s (N₁ , ns))
... | medEv M₁ medStep _
    with ⦀Fin-ev-inv numLinks (λ i → decLink i (phase (med s) i) (broken (med s) i))
           (SR.break-noBoth (med s)) medStep
...   | i , Mi , linkStep , _ =
        subst (λ k → broken (med s) k ≡ false)
              (proj₁ (SR.link-break-chan i (phase (med s) i) (broken (med s) i) linkStep))
              (link-broken-false i (phase (med s) i) (broken (med s) i) linkStep)

-- DECODE TRANSPORT: equal decodes carry unbrokenness — the semantic dodge of
-- the radec-not-injective trap (fire at `s`, transport the STEP, invert at `s′`)
unb-transport : (s s′ : SysState) (l : Link) → absDec s ≡ absDec s′
  → broken (med s) l ≡ false → broken (med s′) l ≡ false
unb-transport s s′ l eq ef =
  sys-break-unbroken s′ l
    (subst (λ z → z ─[ ev (evl (evLabel ⊤₀ (break l) tt₀)) ]─►
                  proj₁ (sys-break-fire s l ef)) eq
           (proj₂ (sys-break-fire s l ef)))

------------------------------------------------------------------------
-- §4  The TERMINAL refutations (the `wprog` replacement): a state with an
--     unbroken link is neither stuck nor a `ret`.
------------------------------------------------------------------------

-- an unbroken link refutes stuckness: the break offer IS a transition
unb-stuck-⊥ : (s : SysState) (l : Link) → broken (med s) l ≡ false
  → IsStuck (absDec s) → ⊥
unb-stuck-⊥ s l ef stk = stk (proj₂ (sys-break-fire s l ef))

-- an unbroken link refutes a `ret` force: the break fire's `ev-inv` exposes a
-- react, which cannot equal the `ret`
unb-ret-⊥ : (s : SysState) (l : Link) {x : ⊤ {0ℓ}} → broken (med s) l ≡ false
  → PTree.force (absDec s) ≡ ret x → ⊥
unb-ret-⊥ s l ef eq with ev-inv (proj₂ (sys-break-fire s l ef))
... | _ , _ , reacteq , _ with trans (sym eq) reacteq
...   | ()

------------------------------------------------------------------------
-- §5  `GSide` / `Unb` — the confined-group vocabulary the walk threads.
------------------------------------------------------------------------

-- which group the trace-level confinement PROTECTS (never breaks):
-- `□¬brkG1` protects {AB,BD} (= `g1`), `□¬brkG2` protects {AC,CD} (= `g2`)
data GSide : Set where
  g1 g2 : GSide

-- the two protected links of a side
protA : GSide → Link
protA g1 = linkAB
protA g2 = linkAC

protB : GSide → Link
protB g1 = linkBD
protB g2 = linkCD

-- the walk invariant: BOTH protected links are still unbroken
Unb : GSide → SysState → Set
Unb gs s = (broken (med s) (protA gs) ≡ false) × (broken (med s) (protB gs) ≡ false)

-- `Unb` at the ALL-unbroken initial medium (both components `refl` at any `s`
-- whose medium is `initMed`; stated for the concrete field function)
-- (the seed is produced inline at `rinit` where both reduce to `refl`)

-- transport `Unb` across equal decodes
unbT : (s s′ : SysState) (gs : GSide) → absDec s ≡ absDec s′ → Unb gs s → Unb gs s′
unbT s s′ gs eq (ua , ub) =
  unb-transport s s′ (protA gs) eq ua , unb-transport s s′ (protB gs) eq ub

-- `Unb` rides across a pointwise `broken`-fixity
unbFix : (s s′ : SysState) (gs : GSide)
  → (∀ (l : Link) → broken (med s′) l ≡ broken (med s) l)
  → Unb gs s → Unb gs s′
unbFix s s′ gs fx (ua , ub) = trans (fx (protA gs)) ua , trans (fx (protB gs)) ub

-- the terminal refutations at `Unb` (use the side's first protected link)
unb-stuckU : (s : SysState) (gs : GSide) → Unb gs s → IsStuck (absDec s) → ⊥
unb-stuckU s gs u = unb-stuck-⊥ s (protA gs) (proj₁ u)

unb-retU : (s : SysState) (gs : GSide) {x : ⊤ {0ℓ}} → Unb gs s
  → PTree.force (absDec s) ≡ ret x → ⊥
unb-retU s gs u = unb-ret-⊥ s (protA gs) (proj₁ u)

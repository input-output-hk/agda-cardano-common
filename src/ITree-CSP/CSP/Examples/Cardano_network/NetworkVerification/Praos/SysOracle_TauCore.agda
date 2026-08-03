{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 D3 (helper) — the STEP CLASSIFIERS for `StepOracle`
-- (`Praos.SysOracle`).
--
-- D3 must populate `StepOracle` TOTALLY: for every LTS step of the stuck
-- neutral `⟦ toSys r ⟧` / `absDec (toSys r)`, reflect it to a reachable
-- successor.  The reflection is done in two stages:
--   (1) a TOTAL STRUCTURAL CLASSIFIER (this module) peels the whole-system
--       step through the OPERATOR stack (`∖ ioES`, `∥⇘ ioES ⇙`, the four-node
--       `⦀`) down to a SINGLE component's leaf sub-step — the medium, one of
--       the four nodes, or a medium/nodes io-sync — using ONLY the generic
--       operand-polymorphic reflections of `SysStep` applied OPAQUELY at the
--       real `decMed`/`decNodeX` operands (no WHNF forcing);
--   (2) the per-component LEAF INVERSIONS (bundle/driver/peer/cell splits) that
--       reconstruct the concrete target `SysState s′` — the remaining grind.
--
-- This module delivers stage (1): the concrete-τ classifier `classify-conτ`,
-- the abstract-τ classifier `classify-absτ`, and the per-node bundle-vs-driver
-- classifier `classify-nodeτ` — all TOTAL and hole-free (they merely chain the
-- `SysStep` reflections, so they are cheap and WHNF-safe).  Stage (2) consumes
-- them.  No postulates, holes, or `--allow-unsolved-metas`.
------------------------------------------------------------------------

open import Level using (0ℓ; Level)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to ttU; ⊤ to ⊤U)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Level using (Lift; lift)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Process_Trees using
  ( PTree; ExtI; AnyTypes; ContinueType; react; ret; sil; react-injective; sil-injective
  ; base; pair; fin )

module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore where

------------------------------------------------------------------------
-- The shared alphabet, the whole-system process type, and the model.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Net; Net-≟; break
  ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack
  ; done; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF )
open import CSP.Examples.Cardano_network.Data p using ( Payload; DecEq-Payload; Header; header; Vote )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES; ιNet; ιNet⁻¹; ιNet-linv )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig; Cookie )

-- Net_Api operators (the whole-system alphabet)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; EventSet; _△_; △-merge; △-τ; ⦀Fin; Prefix₀ )
-- bind operators + bind force-equation / offer-map inversion (node-D / relay drivers)
open Op using ( _>>_; _>>=_ )
import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) as TLB
open TLB using ( fBind-react; bindV-elim )
open EventSet using ( mem )
-- the Net_Api Par τ-elimination (peel a `⦀`/`⦀Fin` link-interleave τ)
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
-- the Net_Api empty event-set (the `⦀`/`⦀Fin` sync alphabet)
open Op using () renaming (∅ES to ∅ESa)

-- the whole-system process type (shared with `⟦_⟧` / `absDec` / the endpoints)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the concrete decode + its state and projections
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode
  using ( SysState; med; nA; nB; nC; nD; ⟦_⟧ )
-- the shared medium decode + its state and per-cell / per-link decodes
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium
  using ( decMed; decLink; decCopy; MedState; mkMed; phase; broken
        ; CopyPhase; empty; full; draining; NetProcN; vis-of )
-- the pre-rename copy cell head (Net Payload alphabet)
open import CSP.Examples.Cardano_network.Network p Payload using ( Copy )
-- the Net Payload operators (the pre-rename copy medium: `⦀⋆` fold)
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆; Skip; ∅ES )
-- the Net Payload LTS (the copy-cell leaf steps live here, pre-rename)
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN
-- the Net Payload Par τ-elimination (peel a `⦀`/`⦀⋆` τ to one operand's τ)
import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Payload}) as PEN
-- the Net Payload Par force lemmas (react-witness for the copy-cell fold)
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Payload}) using ( fPar-er; fPar-sr; fPar-nn )
-- list helpers for the positional cell/list peel reconstruction
open import Data.List using ( List; []; _∷_; length; lookup; updateAt; map )
-- the concrete node decodes + the generic 12-peer bundle
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( decNodeA; decNodeB; decNodeC; decNodeD; bundleG; bundleA )

-- the generic step machinery (R2 Task 4): the reflect-half's operand-generic
-- inversions of a whole-system step down the operator stack
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep
  using ( absDec; nodesOf; absNodesOf
        ; ReflOut; innerτ; hidSync; reflect-⟦⟧-τ; reflect-absDec-τ
        ; InnerτR; medτ; nodesτ; reflect-inner-τ
        ; NodesτR; nAτ; nBτ; nCτ; nDτ; reflect-nodes-τ
        ; NodeτR; bundleτ; driverτ; reflect-node-τ
        -- the abstract (τ-free `tableSpec`) node decodes + their bundles/peers
        ; absNodeA; absNodeB; absNodeC; absNodeD
        ; absBundleG; absCSc; absCSs; absBFc; absBFs; absTSc; absTSs; absKAc; absKAs
        ; absLNc; absLNs; absLFc; absLFs
        ; coarsenCSc; coarsenCSs; coarsenBFc; coarsenBFs; coarsenTSc; coarsenTSs; coarsenKAc; coarsenKAs
        ; coarsenLNc; coarsenLNs; coarsenLFc; coarsenLFs
        -- io-offer predicate (GAP-B disjointness leaves; `RenNO` via `SStep`)
        ; IoOffers )

-- the four-node links + the api sync alphabet + the node-state records (SN)
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( apiES; linkAB; linkAC; linkBD; linkCD; Block₃; b1; produce )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode as SN

-- the abstract τ-free peer interpreter (`tableSpec`) + the inert KA/TS specs
import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs as NS
open NS using ( tableSpec; tsNode; tMenu; tGo
              ; kaClientSpec; kaServerSpec; tsClientSpec; tsServerSpec )

-- the LTS vocabulary at the whole-system instantiation
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; Label; ev; τ; evl; evLabel; τ-inv; ev-inv; sRet; sSil; sTau; sVis )

------------------------------------------------------------------------
-- The concrete-τ classifier: peel a hidden τ of `⟦ s ⟧` to a single
-- component's τ (medium / node A/B/C/D) or a medium/nodes io-sync.
------------------------------------------------------------------------

-- the outcome of classifying a hidden τ of `⟦ s ⟧` (which is definitionally
-- `(decMed (med s) ∥⇘ ioES ⇙ nodesOf s) ∖ ioES`), reduced to one component
data ConτR (s : SysState) (M : NetProc) : Set₁ where
  -- a MEDIUM τ: `decMed (med s)` steps; the nodes are unchanged
  cτ-med : (M′ : NetProc) → decMed (med s) ─[ τ ]─► M′
         → M ≡ ((M′ ∥⇘ ioES ⇙ nodesOf s) ∖ ioES) → ConτR s M
  -- a NODE-A τ: `decNodeA (nA s)` steps; medium + other nodes unchanged
  cτ-nA  : (A′ : NetProc) → decNodeA (nA s) ─[ τ ]─► A′
         → M ≡ ((decMed (med s) ∥⇘ ioES ⇙
                 (A′ ⦀ (decNodeB (nB s) ⦀ (decNodeC (nC s) ⦀ decNodeD (nD s))))) ∖ ioES)
         → ConτR s M
  -- a NODE-B τ
  cτ-nB  : (B′ : NetProc) → decNodeB (nB s) ─[ τ ]─► B′
         → M ≡ ((decMed (med s) ∥⇘ ioES ⇙
                 (decNodeA (nA s) ⦀ (B′ ⦀ (decNodeC (nC s) ⦀ decNodeD (nD s))))) ∖ ioES)
         → ConτR s M
  -- a NODE-C τ
  cτ-nC  : (C′ : NetProc) → decNodeC (nC s) ─[ τ ]─► C′
         → M ≡ ((decMed (med s) ∥⇘ ioES ⇙
                 (decNodeA (nA s) ⦀ (decNodeB (nB s) ⦀ (C′ ⦀ decNodeD (nD s))))) ∖ ioES)
         → ConτR s M
  -- a NODE-D τ
  cτ-nD  : (D′ : NetProc) → decNodeD (nD s) ─[ τ ]─► D′
         → M ≡ ((decMed (med s) ∥⇘ ioES ⇙
                 (decNodeA (nA s) ⦀ (decNodeB (nB s) ⦀ (decNodeC (nC s) ⦀ D′)))) ∖ ioES)
         → ConτR s M
  -- a hidden io-sync: BOTH the medium and the nodes fire the SAME io ∈ ioES
  cτ-io  : ∀ {X} {e : Net_Api Payload X} {a : X} (M₁ N₁ : NetProc)
         → ioES .mem (X , e) a
         → decMed (med s) ─[ ev (evl (evLabel X e a)) ]─► M₁
         → nodesOf s      ─[ ev (evl (evLabel X e a)) ]─► N₁
         → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES) → ConτR s M

-- TOTAL classifier of a concrete hidden τ into one component (stage 1).  Chains
-- `reflect-⟦⟧-τ` (hide) → `reflect-inner-τ` (medium vs nodes) → `reflect-nodes-τ`
-- (the four-node `⦀`); every application is opaque (no operand forced to WHNF).
classify-conτ : (s : SysState) {M : NetProc} → ⟦ s ⟧ ─[ τ ]─► M → ConτR s M
classify-conτ s step with reflect-⟦⟧-τ s step
... | hidSync M₁ N₁ iomem sM sN eq = cτ-io M₁ N₁ iomem sM sN eq
... | innerτ P′ innerStep eq
      with reflect-inner-τ (decMed (med s)) (nodesOf s) innerStep
...   | medτ M′ ms eqP = cτ-med M′ ms (trans eq (cong (_∖ ioES) eqP))
...   | nodesτ N′ ns eqP
        with reflect-nodes-τ (decNodeA (nA s)) (decNodeB (nB s)) (decNodeC (nC s)) (decNodeD (nD s)) ns
...     | nAτ A′ as eqN =
          cτ-nA A′ as (trans eq (cong (_∖ ioES) (trans eqP (cong (decMed (med s) ∥⇘ ioES ⇙_) eqN))))
...     | nBτ B′ bs eqN =
          cτ-nB B′ bs (trans eq (cong (_∖ ioES) (trans eqP (cong (decMed (med s) ∥⇘ ioES ⇙_) eqN))))
...     | nCτ C′ cs eqN =
          cτ-nC C′ cs (trans eq (cong (_∖ ioES) (trans eqP (cong (decMed (med s) ∥⇘ ioES ⇙_) eqN))))
...     | nDτ D′ ds eqN =
          cτ-nD D′ ds (trans eq (cong (_∖ ioES) (trans eqP (cong (decMed (med s) ∥⇘ ioES ⇙_) eqN))))

------------------------------------------------------------------------
-- The abstract-τ classifier: identical structure at the ABSTRACT operands
-- (`absNodesOf s` in place of `nodesOf s`).  `absDec s` is definitionally
-- `(decMed (med s) ∥⇘ ioES ⇙ absNodesOf s) ∖ ioES` and the medium is SHARED
-- verbatim, so the same reflect cascade applies.  Since the abstract nodes are
-- τ-free, stage-2 will discharge the node branches as VACUOUS.
------------------------------------------------------------------------

-- the outcome of classifying a hidden τ of the abstract `absDec s`
data AbsτR (s : SysState) (M : NetProc) : Set₁ where
  aτ-med : (M′ : NetProc) → decMed (med s) ─[ τ ]─► M′
         → M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf s) ∖ ioES) → AbsτR s M
  aτ-nds : (N′ : NetProc) → absNodesOf s ─[ τ ]─► N′
         → M ≡ ((decMed (med s) ∥⇘ ioES ⇙ N′) ∖ ioES) → AbsτR s M
  aτ-io  : ∀ {X} {e : Net_Api Payload X} {a : X} (M₁ N₁ : NetProc)
         → ioES .mem (X , e) a
         → decMed (med s)  ─[ ev (evl (evLabel X e a)) ]─► M₁
         → absNodesOf s    ─[ ev (evl (evLabel X e a)) ]─► N₁
         → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES) → AbsτR s M

-- TOTAL classifier of an abstract hidden τ (stage 1, backward direction)
classify-absτ : (s : SysState) {M : NetProc} → absDec s ─[ τ ]─► M → AbsτR s M
classify-absτ s step with reflect-absDec-τ s step
... | hidSync M₁ N₁ iomem sM sN eq = aτ-io M₁ N₁ iomem sM sN eq
... | innerτ P′ innerStep eq
      with reflect-inner-τ (decMed (med s)) (absNodesOf s) innerStep
...   | medτ   M′ ms eqP = aτ-med M′ ms (trans eq (cong (_∖ ioES) eqP))
...   | nodesτ N′ ns eqP = aτ-nds N′ ns (trans eq (cong (_∖ ioES) eqP))

-- NOTE (stage 2): the per-node bundle-vs-driver split is `SysStep.reflect-node-τ`
-- applied at each `decNodeX`'s definitional `bundle ∥⇘ apiES ⇙ driver` operands
-- (a node τ is a bundle τ — a peer sil — or a τ-free driver τ, refuted); it is
-- reused verbatim there, so it is not re-exported here.

------------------------------------------------------------------------
-- STAGE-2 GENERIC ELIM — `renameMap`-τc-nothing / renamed-react has-no-τ.
--
-- A driven peer decode is `RenXX.renameMap (…-src l d pos)`; an inert peer / a
-- driver is likewise a renamed (or native) react.  To INVERT a leaf τ we must,
-- at every NON-`…Sil` (react) position, REFUTE the `sTau` case — i.e. show the
-- renamed react's τ-branch map is `nothing` everywhere.  `renameMap`'s force
-- gives `τc = extBranch (invRel ι-vis-inv) (invPreimg ι-vis-inv) τcP`, which
-- pulls the target index back via `extBwd` and consults the SOURCE `τcP`; so if
-- the source react has an everywhere-`nothing` τ-branch (the FSM peers loop via
-- a `sil`, NEVER an internal-choice τc), the renamed τ-branch is `nothing` too,
-- and a renamed react admits NO τ at all (its force is a `react`, not a `sil`).
-- This is the non-trivial `sTau` refutation; it is fully symbolic (no WHNF of
-- the composite tree — only the single renamed peer's force layer).
------------------------------------------------------------------------

-- generic `renameMap` non-τ transport, parametrised over an alphabet injection
-- `ι : E₁ → Net_Api Payload` (instantiated at ιCS / ιBF / … per peer kind)
module RenTC {ℓe₁ : Level} {E₁ : Set 0ℓ → Set ℓe₁}
  (ι      : ∀ {A} → E₁ A → Net_Api Payload A)
  (ι⁻¹    : ∀ {A} → Net_Api Payload A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  where
  open import CSP.Rename {E₁ = E₁} {E₂ = Net_Api Payload} ι ι⁻¹ ι-linv
    using ( renameMap; extBranch; extBwd; invRel; invPreimg; ι-vis-inv
          ; rnFan; rnCollect )

  -- force of a renamed react: the `rnFan`/`extBranch` pipeline over the source
  -- react's offer/τ maps (a definitional unfolding, matched under `P .force`)
  force-renameMap-react : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr}
      {vP  : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))}
      {τcP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr))}
    → PTree.force P ≡ react vP τcP
    → PTree.force (renameMap P) ≡
        react (λ bt b → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
                              (rnCollect vP (invPreimg ι-vis-inv bt b)))
              (extBranch (invRel ι-vis-inv) (invPreimg ι-vis-inv) τcP)
  force-renameMap-react {P = P} eq with PTree.force P | eq
  ... | react vP τcP | refl = refl

  -- the renamed τ-branch is `nothing` when the source τ-branch is (item-1's
  -- disjointness for τ: `extBwd` pulls back, the source `nothing` propagates)
  extBranch-nothing : {Rr : Set}
      (τcP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr)))
    → (∀ i a → τcP i a ≡ nothing)
    → ∀ i a → extBranch (invRel ι-vis-inv) (invPreimg ι-vis-inv) τcP i a ≡ nothing
  extBranch-nothing τcP h (A , eι₂) a with extBwd eι₂
  ... | nothing  = refl
  ... | just eι₁ rewrite h (A , eι₁) a = refl

  -- a renamed react with an everywhere-`nothing` source τ-branch admits NO τ
  renameMap-react-no-τ : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr}
      {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
      {vP  : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))}
      {τcP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr))}
    → PTree.force P ≡ react vP τcP
    → (∀ i a → τcP i a ≡ nothing)
    → ¬ (renameMap P ─[ τ ]─► M)
  renameMap-react-no-τ {P = P} feqP h step with τ-inv step
  ... | inj₁ sileq with trans (sym sileq) (force-renameMap-react {P = P} feqP)
  ...   | ()
  renameMap-react-no-τ {P = P} feqP h step | inj₂ (v′ , τc′ , i , a , feq′ , beq)
    with proj₂ (react-injective (trans (sym feq′) (force-renameMap-react {P = P} feqP)))
  ...   | refl with trans (sym beq) (extBranch-nothing _ h i a)
  ...     | ()

  -- force of a renamed `ret`: `ret r` passes through unchanged
  force-renameMap-ret : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr} {r : Rr}
    → PTree.force P ≡ ret r → PTree.force (renameMap P) ≡ ret r
  force-renameMap-ret {P = P} eq with PTree.force P | eq
  ... | ret r | refl = refl

  -- a renamed `ret` (a terminated peer, e.g. a `…Head stDone`) admits NO τ
  renameMap-ret-no-τ : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr}
      {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr} {r : Rr}
    → PTree.force P ≡ ret r → ¬ (renameMap P ─[ τ ]─► M)
  renameMap-ret-no-τ {P = P} feqP step with τ-inv step
  ... | inj₁ sileq with trans (sym sileq) (force-renameMap-ret {P = P} feqP)
  ...   | ()
  renameMap-ret-no-τ {P = P} feqP step | inj₂ (v′ , τc′ , i , a , feq′ , beq)
    with trans (sym feq′) (force-renameMap-ret {P = P} feqP)
  ...   | ()

  -- force of a renamed `sil`: `renameMap` preserves the silent step
  force-renameMap-sil : {Rr : Set} {P P′ : PTree E₁ (ExtI E₁) Rr}
    → PTree.force P ≡ sil P′ → PTree.force (renameMap P) ≡ sil (renameMap P′)
  force-renameMap-sil {P = P} eq with PTree.force P | eq
  ... | sil P′ | refl = refl

  -- the SOURCE-alphabet LTS (the reconstructed source τ-step lives at E₁, not
  -- Net_Api), imported qualified to avoid clashing with the outer Net_Api arrow
  import Semantics.LTS {E = E₁} {I = ExtI E₁} as L₁

  -- invert a `just` result of the renamed τ-branch at target index `(A , eι₂)`:
  -- the target index pulls back (`extBwd`) to a source index `(A , eι₁)` whose
  -- source τc yields some `t′` with `M ≡ renameMap t′` (the `rnMc` push-forward)
  ext-just-inv : {Rr : Set}
      (τcP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr)))
      {A : Set 0ℓ} (eι₂ : ExtI (Net_Api Payload) A) (a : A)
      {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    → extBranch (invRel ι-vis-inv) (invPreimg ι-vis-inv) τcP (A , eι₂) a ≡ just M
    → Σ[ eι₁ ∈ ExtI E₁ A ] Σ[ t′ ∈ PTree E₁ (ExtI E₁) Rr ]
         (τcP (A , eι₁) a ≡ just t′) × (M ≡ renameMap t′)
  ext-just-inv τcP eι₂ a eq with extBwd eι₂
  ext-just-inv τcP eι₂ a eq | nothing with eq
  ... | ()
  ext-just-inv τcP eι₂ a eq | just eι₁ with τcP (_ , eι₁) a in eqτ
  ... | nothing with eq
  ...   | ()
  ext-just-inv τcP eι₂ a eq | just eι₁ | just t′ =
    eι₁ , t′ , eqτ , sym (just-injective eq)

  -- REVERSE of `force-renameMap-sil` (+ react τ): a τ of a renamed tree comes
  -- from a SOURCE τ (a source `sil`, or a source react-τ pulled back through
  -- `extBranch`), and the target is the rename of the source successor.
  renameMap-τ-reflect : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr}
      {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    → renameMap P ─[ τ ]─► M
    → Σ[ P′ ∈ PTree E₁ (ExtI E₁) Rr ] (P L₁.─[ L₁.τ ]─► P′) × (M ≡ renameMap P′)
  renameMap-τ-reflect {P = P} step with PTree.force P in eqP
  ... | ret r = ⊥-elim (renameMap-ret-no-τ {P = P} eqP step)
  ... | sil P′ with τ-inv step
  ...   | inj₁ sileq =
          P′ , L₁.sSil eqP , sil-injective (trans (sym sileq) (force-renameMap-sil {P = P} eqP))
  ...   | inj₂ (v′ , τc′ , i , a , feq′ , beq)
          with trans (sym feq′) (force-renameMap-sil {P = P} eqP)
  ...     | ()
  renameMap-τ-reflect {P = P} step | react vP τcP with τ-inv step
  ...   | inj₁ sileq with trans (sym (force-renameMap-react {P = P} eqP)) sileq
  ...     | ()
  renameMap-τ-reflect {P = P} step | react vP τcP | inj₂ (v′ , τc′ , (A , eι₂) , a , feq′ , beq)
          with react-injective (trans (sym feq′) (force-renameMap-react {P = P} eqP))
  ...     | _ , refl with ext-just-inv τcP eι₂ a beq
  ...       | eι₁ , t′ , tp , meq = t′ , L₁.sTau eqP tp , meq

  -- invert a `just` result of the renamed VISIBLE-offer at target `(X , e₂)`:
  -- the injective `invPreimg`/`rnCollect`/`rnFan` pipeline has at most one entry,
  -- so a fired offer pins the SOURCE event `e₁` + the source continuation `t′`
  -- (`vP (X , e₁) b ≡ just t′`), with `M ≡ renameMap t′`
  rn-vis-inv : {Rr : Set}
      (vP : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr)))
      {X : Set 0ℓ} (e₂ : Net_Api Payload X) (b : X)
      {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
            (rnCollect vP (invPreimg ι-vis-inv (X , e₂) b)) ≡ just M
    → Σ[ e₁ ∈ E₁ X ] Σ[ t′ ∈ PTree E₁ (ExtI E₁) Rr ]
         (vP (X , e₁) b ≡ just t′) × (M ≡ renameMap t′)
  rn-vis-inv vP e₂ b eq with ι⁻¹ e₂
  ... | nothing with eq
  ...   | ()
  rn-vis-inv vP e₂ b eq | just e₁ with vP (_ , e₁) b in vpe
  ...   | nothing with eq
  ...     | ()
  rn-vis-inv vP e₂ b eq | just e₁ | just t′ = e₁ , t′ , vpe , sym (just-injective eq)

  -- REVERSE of `force-renameMap-react` at the visible layer: a visible step of a
  -- renamed tree comes from a SOURCE visible step (the source react offers the
  -- ι-preimage event), and the target is the rename of the source successor.
  renameMap-ev-reflect : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr} {X : Set 0ℓ}
      {e₂ : Net_Api Payload X} {b : X}
      {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    → renameMap P ─[ ev (evl (evLabel X e₂ b)) ]─► M
    → Σ[ e₁ ∈ E₁ X ] Σ[ P′ ∈ PTree E₁ (ExtI E₁) Rr ]
         (P L₁.─[ L₁.ev (L₁.evl (L₁.evLabel X e₁ b)) ]─► P′) × (M ≡ renameMap P′)
  renameMap-ev-reflect {P = P} {X} {e₂} {b} step with PTree.force P in eqP
  ... | ret r with ev-inv step
  ...   | v , τc , feq , _ with trans (sym feq) (force-renameMap-ret {P = P} eqP)
  ...     | ()
  renameMap-ev-reflect {P = P} {X} {e₂} {b} step | sil P′ with ev-inv step
  ...   | v , τc , feq , _ with trans (sym feq) (force-renameMap-sil {P = P} eqP)
  ...     | ()
  renameMap-ev-reflect {P = P} {X} {e₂} {b} step | react vP τcP with ev-inv step
  ...   | v , τc , feq , veq
          with react-injective (trans (sym feq) (force-renameMap-react {P = P} eqP))
  ...     | vEq , _ with rn-vis-inv vP e₂ b (trans (sym (cong (λ w → w (X , e₂) b) vEq)) veq)
  ...       | e₁ , t′ , vpe , meq = e₁ , t′ , L₁.sVis eqP vpe , meq

  -- like `rn-vis-inv`, but ALSO returns the ι-preimage relation `ι⁻¹ e₂ ≡ just e₁`
  -- (recovered via the `with`-abstraction: in the `just e₁` branch `ι⁻¹ e₂` is
  -- abstracted to `just e₁`, so the relation is `refl`) — needed to pin a renamed
  -- event's link component through the injection.
  rn-vis-inv-ι : {Rr : Set}
      (vP : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr)))
      {X : Set 0ℓ} (e₂ : Net_Api Payload X) (b : X)
      {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
            (rnCollect vP (invPreimg ι-vis-inv (X , e₂) b)) ≡ just M
    → Σ[ e₁ ∈ E₁ X ] Σ[ t′ ∈ PTree E₁ (ExtI E₁) Rr ]
         (ι⁻¹ e₂ ≡ just e₁) × (vP (X , e₁) b ≡ just t′) × (M ≡ renameMap t′)
  rn-vis-inv-ι vP e₂ b eq with ι⁻¹ e₂
  ... | nothing with eq
  ...   | ()
  rn-vis-inv-ι vP e₂ b eq | just e₁ with vP (_ , e₁) b in vpe
  ...   | nothing with eq
  ...     | ()
  rn-vis-inv-ι vP e₂ b eq | just e₁ | just t′ = e₁ , t′ , refl , vpe , sym (just-injective eq)

  -- like `renameMap-ev-reflect`, but ALSO returns `ι⁻¹ e₂ ≡ just e₁`
  renameMap-ev-reflect-ι : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr} {X : Set 0ℓ}
      {e₂ : Net_Api Payload X} {b : X}
      {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    → renameMap P ─[ ev (evl (evLabel X e₂ b)) ]─► M
    → Σ[ e₁ ∈ E₁ X ] Σ[ P′ ∈ PTree E₁ (ExtI E₁) Rr ]
         (ι⁻¹ e₂ ≡ just e₁)
         × (P L₁.─[ L₁.ev (L₁.evl (L₁.evLabel X e₁ b)) ]─► P′) × (M ≡ renameMap P′)
  renameMap-ev-reflect-ι {P = P} {X} {e₂} {b} step with PTree.force P in eqP
  ... | ret r with ev-inv step
  ...   | v , τc , feq , _ with trans (sym feq) (force-renameMap-ret {P = P} eqP)
  ...     | ()
  renameMap-ev-reflect-ι {P = P} {X} {e₂} {b} step | sil P′ with ev-inv step
  ...   | v , τc , feq , _ with trans (sym feq) (force-renameMap-sil {P = P} eqP)
  ...     | ()
  renameMap-ev-reflect-ι {P = P} {X} {e₂} {b} step | react vP τcP with ev-inv step
  ...   | v , τc , feq , veq
          with react-injective (trans (sym feq) (force-renameMap-react {P = P} eqP))
  ...     | vEq , _ with rn-vis-inv-ι vP e₂ b (trans (sym (cong (λ w → w (X , e₂) b) vEq)) veq)
  ...       | e₁ , t′ , iota , vpe , meq = e₁ , t′ , iota , L₁.sVis eqP vpe , meq

------------------------------------------------------------------------
-- STAGE-2 PEER-LEAF τ-INVERSIONS.  A driven peer's ONLY τ is a loop re-entry
-- `…Sil st → …Head st`; every other position is a stable react (or terminated
-- `ret`) whose source τ-branch is everywhere-`nothing` (`pchoice = react _ ∅t`,
-- threaded through `iter`/`succVC`), so it admits no τ.  Mid-positions force
-- through an offer-map `l′ ≟ l | d′ ≟ d` guard, unstuck by `≟-yes-refl`.
------------------------------------------------------------------------

open import Class.DecEq using ( DecEq; _≟_ )
open import Relation.Nullary using ( yes; no )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi
  ; IDs; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive
  ; N2N_LeiosNotify; N2N_LeiosFetch
  ; BlockingStyle; Blocking; NonBlocking )
open import CSP.Examples.Cardano_network.Net p using ( Link )
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( ιCS; ιCS⁻¹; ιCS-linv; ιBF; ιBF⁻¹; ιBF-linv )
import CSP.Examples.Cardano_network.ChainSync    p as CS
import CSP.Examples.Cardano_network.BlockFetch   p as BF
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.KeepAlive    p as KA
import CSP.Examples.Cardano_network.LeiosNotify  p as LNp
import CSP.Examples.Cardano_network.LeiosFetch   p as LFp
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( CScPos; csHead; csReqNext1; csFindInt1; csDone1
        ; csRF1; csRB1; csIF1; csINF1; csSil
        ; decCSc; decCSc-src )

-- a DecEq comparison of an element with itself is `yes refl` (K/UIP)
≟-yes-refl : ∀ {a} {A : Set a} ⦃ _ : DecEq A ⦄ (x : A) → (x ≟ x) ≡ yes refl
≟-yes-refl x with x ≟ x
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

-- the RenTC instance for ChainSync
module CSNO = RenTC ιCS ιCS⁻¹ ιCS-linv

-- source-force lemmas at the mid positions (unstick the offer-map DecEq guard)
fReqNext1 : (l : Link) (d : Dir) → PTree.force (decCSc-src l d csReqNext1) ≡ react _ _
fReqNext1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
fFindInt1 : (l : Link) (d : Dir) (ps : _) → PTree.force (decCSc-src l d (csFindInt1 ps)) ≡ react _ _
fFindInt1 l d ps rewrite ≟-yes-refl l | ≟-yes-refl d = refl
fDone1 : (l : Link) (d : Dir) → PTree.force (decCSc-src l d csDone1) ≡ react _ _
fDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
fRF1 : (l : Link) (d : Dir) (h : _) (t : _) → PTree.force (decCSc-src l d (csRF1 h t)) ≡ react _ _
fRF1 l d h t rewrite ≟-yes-refl l | ≟-yes-refl d = refl
fRB1 : (l : Link) (d : Dir) (pt : _) (t : _) → PTree.force (decCSc-src l d (csRB1 pt t)) ≡ react _ _
fRB1 l d pt t rewrite ≟-yes-refl l | ≟-yes-refl d = refl
fIF1 : (l : Link) (d : Dir) (pt : _) (t : _) → PTree.force (decCSc-src l d (csIF1 pt t)) ≡ react _ _
fIF1 l d pt t rewrite ≟-yes-refl l | ≟-yes-refl d = refl
fINF1 : (l : Link) (d : Dir) (t : _) → PTree.force (decCSc-src l d (csINF1 t)) ≡ react _ _
fINF1 l d t rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- ChainSync CLIENT τ-inversion: recover the loop-state and the target head
decCSc-τ-inv : (l : Link) (d : Dir) (pos : CScPos) {M : NetProc}
  → decCSc l d pos ─[ τ ]─► M
  → Σ[ st ∈ CS.CSState ] (pos ≡ csSil st) × (M ≡ decCSc l d (csHead st))
decCSc-τ-inv l d (csHead CS.stIdle)      step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csHead CS.stIdle)} refl (λ _ _ → refl) step)
decCSc-τ-inv l d (csHead CS.stCanAwait)  step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csHead CS.stCanAwait)} refl (λ _ _ → refl) step)
decCSc-τ-inv l d (csHead CS.stMustReply) step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csHead CS.stMustReply)} refl (λ _ _ → refl) step)
decCSc-τ-inv l d (csHead CS.stIntersect) step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csHead CS.stIntersect)} refl (λ _ _ → refl) step)
decCSc-τ-inv l d (csHead CS.stDone)      step = ⊥-elim (CSNO.renameMap-ret-no-τ   {P = decCSc-src l d (csHead CS.stDone)} refl step)
decCSc-τ-inv l d csReqNext1      step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d csReqNext1} (fReqNext1 l d) (λ _ _ → refl) step)
decCSc-τ-inv l d (csFindInt1 ps) step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csFindInt1 ps)} (fFindInt1 l d ps) (λ _ _ → refl) step)
decCSc-τ-inv l d csDone1         step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d csDone1} (fDone1 l d) (λ _ _ → refl) step)
decCSc-τ-inv l d (csRF1 h t)     step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csRF1 h t)} (fRF1 l d h t) (λ _ _ → refl) step)
decCSc-τ-inv l d (csRB1 pt t)    step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csRB1 pt t)} (fRB1 l d pt t) (λ _ _ → refl) step)
decCSc-τ-inv l d (csIF1 pt t)    step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csIF1 pt t)} (fIF1 l d pt t) (λ _ _ → refl) step)
decCSc-τ-inv l d (csINF1 t)      step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSc-src l d (csINF1 t)} (fINF1 l d t) (λ _ _ → refl) step)
decCSc-τ-inv l d (csSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (CSNO.force-renameMap-sil
             {P = decCSc-src l d (csSil st)} {P′ = decCSc-src l d (csHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (CSNO.force-renameMap-sil
             {P = decCSc-src l d (csSil st)} {P′ = decCSc-src l d (csHead st)} refl)
...   | ()

------------------------------------------------------------------------
-- CS-server / BF-client / BF-server τ-inversions (analogous to CS-client).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( CSsPos; ssHead; ssReqNext1; ssFindInt1; ssDone1
        ; ssRF1; ssRB1; ssAw1; ssIF1; ssINF1; ssSil
        ; BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
        ; BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil
        ; TScPos; tcHead; tcReqIdsB1; tcReqIdsNB1; tcReqTxs1; tcRepB1; tcDone1; tcRepNB1; tcRepTxs1; tcSil; TSsPos; tsHead; tsDone1; tsReqB1; tsReqNB1; tsReqTxs1; tsSil
        ; KAcPos; kcHead; kcErr1; kcReq1; kcDone1; kcSil; kcTermE1; KAsPos; ksHead; ksRecv1; ksDdone1; ksSil
        ; LNcPos; lncHead; lncRann1; lncRoff1; lncRtxs1; lncRvot1; lncReq1; lncDone1; lncSil; LNsPos; lnsHead; lnsDone1; lnsWann1; lnsWoff1; lnsWtxs1; lnsWvot1; lnsSil
        ; LFcPos; lfcHead; lfcRblk1; lfcRbtx1; lfcRvot1; lfcRnext1; lfcRlast1; lfcWblk1; lfcWtxs1; lfcWvot1; lfcWrng1; lfcDone1; lfcSil; LFsPos; lfsHead; lfsDone1; lfsWblk1; lfsWtxs1; lfsWvot1; lfsWnext1; lfsWlast1; lfsSil
        ; InertPos; mkInert; tsc; tss; kac; kas; lnc; lns; lfc; lfs
        ; decTSc; decTSc-src; decTSs; decTSs-src
        ; decKAc; decKAc-src; decKAs; decKAs-src
        ; decLNc; decLNc-src; decLNs; decLNs-src
        ; decLFc; decLFc-src; decLFs; decLFs-src
        ; decCSs; decCSs-src; decBFc; decBFc-src; decBFs; decBFs-src )

module BFNO = RenTC ιBF ιBF⁻¹ ιBF-linv

-- CS-server source-force lemmas (succVC mid positions; unstick DecEq guard)
gReqNext1 : (l : Link) (d : Dir) → PTree.force (decCSs-src l d ssReqNext1) ≡ react _ _
gReqNext1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
gFindInt1 : (l : Link) (d : Dir) (ps : _) → PTree.force (decCSs-src l d (ssFindInt1 ps)) ≡ react _ _
gFindInt1 l d ps rewrite ≟-yes-refl l | ≟-yes-refl d = refl
gDone1 : (l : Link) (d : Dir) → PTree.force (decCSs-src l d ssDone1) ≡ react _ _
gDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
gRF1 : (l : Link) (d : Dir) (h : _) (t : _) → PTree.force (decCSs-src l d (ssRF1 h t)) ≡ react _ _
gRF1 l d h t rewrite ≟-yes-refl l | ≟-yes-refl d = refl
gRB1 : (l : Link) (d : Dir) (pt : _) (t : _) → PTree.force (decCSs-src l d (ssRB1 pt t)) ≡ react _ _
gRB1 l d pt t rewrite ≟-yes-refl l | ≟-yes-refl d = refl
gAw1 : (l : Link) (d : Dir) → PTree.force (decCSs-src l d ssAw1) ≡ react _ _
gAw1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
gIF1 : (l : Link) (d : Dir) (pt : _) (t : _) → PTree.force (decCSs-src l d (ssIF1 pt t)) ≡ react _ _
gIF1 l d pt t rewrite ≟-yes-refl l | ≟-yes-refl d = refl
gINF1 : (l : Link) (d : Dir) (t : _) → PTree.force (decCSs-src l d (ssINF1 t)) ≡ react _ _
gINF1 l d t rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- ChainSync SERVER τ-inversion
decCSs-τ-inv : (l : Link) (d : Dir) (pos : CSsPos) {M : NetProc}
  → decCSs l d pos ─[ τ ]─► M
  → Σ[ st ∈ CS.CSState ] (pos ≡ ssSil st) × (M ≡ decCSs l d (ssHead st))
decCSs-τ-inv l d (ssHead CS.stIdle)      step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssHead CS.stIdle)} refl (λ _ _ → refl) step)
decCSs-τ-inv l d (ssHead CS.stCanAwait)  step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssHead CS.stCanAwait)} refl (λ _ _ → refl) step)
decCSs-τ-inv l d (ssHead CS.stMustReply) step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssHead CS.stMustReply)} refl (λ _ _ → refl) step)
decCSs-τ-inv l d (ssHead CS.stIntersect) step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssHead CS.stIntersect)} refl (λ _ _ → refl) step)
decCSs-τ-inv l d (ssHead CS.stDone)      step = ⊥-elim (CSNO.renameMap-ret-no-τ   {P = decCSs-src l d (ssHead CS.stDone)} refl step)
decCSs-τ-inv l d ssReqNext1      step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d ssReqNext1} (gReqNext1 l d) (λ _ _ → refl) step)
decCSs-τ-inv l d (ssFindInt1 ps) step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssFindInt1 ps)} (gFindInt1 l d ps) (λ _ _ → refl) step)
decCSs-τ-inv l d ssDone1         step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d ssDone1} (gDone1 l d) (λ _ _ → refl) step)
decCSs-τ-inv l d (ssRF1 h t)     step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssRF1 h t)} (gRF1 l d h t) (λ _ _ → refl) step)
decCSs-τ-inv l d (ssRB1 pt t)    step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssRB1 pt t)} (gRB1 l d pt t) (λ _ _ → refl) step)
decCSs-τ-inv l d ssAw1           step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d ssAw1} (gAw1 l d) (λ _ _ → refl) step)
decCSs-τ-inv l d (ssIF1 pt t)    step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssIF1 pt t)} (gIF1 l d pt t) (λ _ _ → refl) step)
decCSs-τ-inv l d (ssINF1 t)      step = ⊥-elim (CSNO.renameMap-react-no-τ {P = decCSs-src l d (ssINF1 t)} (gINF1 l d t) (λ _ _ → refl) step)
decCSs-τ-inv l d (ssSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (CSNO.force-renameMap-sil
             {P = decCSs-src l d (ssSil st)} {P′ = decCSs-src l d (ssHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (CSNO.force-renameMap-sil
             {P = decCSs-src l d (ssSil st)} {P′ = decCSs-src l d (ssHead st)} refl)
...   | ()

-- BF-client source-force lemmas
hReq1 : (l : Link) (d : Dir) (r : _) → PTree.force (decBFc-src l d (bcReq1 r)) ≡ react _ _
hReq1 l d r rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hcDone1 : (l : Link) (d : Dir) → PTree.force (decBFc-src l d bcDone1) ≡ react _ _
hcDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hBlk1 : (l : Link) (d : Dir) (b : _) → PTree.force (decBFc-src l d (bcBlk1 b)) ≡ react _ _
hBlk1 l d b rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- BlockFetch CLIENT τ-inversion
decBFc-τ-inv : (l : Link) (d : Dir) (pos : BFcPos) {M : NetProc}
  → decBFc l d pos ─[ τ ]─► M
  → Σ[ st ∈ BF.BFState ] (pos ≡ bcSil st) × (M ≡ decBFc l d (bcHead st))
decBFc-τ-inv l d (bcHead BF.stIdle)      step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFc-src l d (bcHead BF.stIdle)} refl (λ _ _ → refl) step)
decBFc-τ-inv l d (bcHead BF.stBusy)      step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFc-src l d (bcHead BF.stBusy)} refl (λ _ _ → refl) step)
decBFc-τ-inv l d (bcHead BF.stStreaming) step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFc-src l d (bcHead BF.stStreaming)} refl (λ _ _ → refl) step)
decBFc-τ-inv l d (bcHead BF.stDone)      step = ⊥-elim (BFNO.renameMap-ret-no-τ   {P = decBFc-src l d (bcHead BF.stDone)} refl step)
decBFc-τ-inv l d (bcReq1 r)  step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFc-src l d (bcReq1 r)} (hReq1 l d r) (λ _ _ → refl) step)
decBFc-τ-inv l d bcDone1     step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFc-src l d bcDone1} (hcDone1 l d) (λ _ _ → refl) step)
decBFc-τ-inv l d (bcBlk1 b)  step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFc-src l d (bcBlk1 b)} (hBlk1 l d b) (λ _ _ → refl) step)
decBFc-τ-inv l d (bcSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (BFNO.force-renameMap-sil
             {P = decBFc-src l d (bcSil st)} {P′ = decBFc-src l d (bcHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (BFNO.force-renameMap-sil
             {P = decBFc-src l d (bcSil st)} {P′ = decBFc-src l d (bcHead st)} refl)
...   | ()

-- BF-server source-force lemmas
kReq1 : (l : Link) (d : Dir) (r : _) → PTree.force (decBFs-src l d (bsReq1 r)) ≡ react _ _
kReq1 l d r rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ksDone1 : (l : Link) (d : Dir) → PTree.force (decBFs-src l d bsDone1) ≡ react _ _
ksDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
kStart1 : (l : Link) (d : Dir) → PTree.force (decBFs-src l d bsStart1) ≡ react _ _
kStart1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
kNoBlk1 : (l : Link) (d : Dir) → PTree.force (decBFs-src l d bsNoBlk1) ≡ react _ _
kNoBlk1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
kBlk1 : (l : Link) (d : Dir) (b : _) → PTree.force (decBFs-src l d (bsBlk1 b)) ≡ react _ _
kBlk1 l d b rewrite ≟-yes-refl l | ≟-yes-refl d = refl
kBatchDone1 : (l : Link) (d : Dir) → PTree.force (decBFs-src l d bsBatchDone1) ≡ react _ _
kBatchDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- BlockFetch SERVER τ-inversion
decBFs-τ-inv : (l : Link) (d : Dir) (pos : BFsPos) {M : NetProc}
  → decBFs l d pos ─[ τ ]─► M
  → Σ[ st ∈ BF.BFState ] (pos ≡ bsSil st) × (M ≡ decBFs l d (bsHead st))
decBFs-τ-inv l d (bsHead BF.stIdle)      step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d (bsHead BF.stIdle)} refl (λ _ _ → refl) step)
decBFs-τ-inv l d (bsHead BF.stBusy)      step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d (bsHead BF.stBusy)} refl (λ _ _ → refl) step)
decBFs-τ-inv l d (bsHead BF.stStreaming) step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d (bsHead BF.stStreaming)} refl (λ _ _ → refl) step)
decBFs-τ-inv l d (bsHead BF.stDone)      step = ⊥-elim (BFNO.renameMap-ret-no-τ   {P = decBFs-src l d (bsHead BF.stDone)} refl step)
decBFs-τ-inv l d (bsReq1 r)    step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d (bsReq1 r)} (kReq1 l d r) (λ _ _ → refl) step)
decBFs-τ-inv l d bsDone1       step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d bsDone1} (ksDone1 l d) (λ _ _ → refl) step)
decBFs-τ-inv l d bsStart1      step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d bsStart1} (kStart1 l d) (λ _ _ → refl) step)
decBFs-τ-inv l d bsNoBlk1      step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d bsNoBlk1} (kNoBlk1 l d) (λ _ _ → refl) step)
decBFs-τ-inv l d (bsBlk1 b)    step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d (bsBlk1 b)} (kBlk1 l d b) (λ _ _ → refl) step)
decBFs-τ-inv l d bsBatchDone1  step = ⊥-elim (BFNO.renameMap-react-no-τ {P = decBFs-src l d bsBatchDone1} (kBatchDone1 l d) (λ _ _ → refl) step)
decBFs-τ-inv l d (bsSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (BFNO.force-renameMap-sil
             {P = decBFs-src l d (bsSil st)} {P′ = decBFs-src l d (bsHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (BFNO.force-renameMap-sil
             {P = decBFs-src l d (bsSil st)} {P′ = decBFs-src l d (bsHead st)} refl)
...   | ()

------------------------------------------------------------------------
-- STAGE-2 NATIVE no-τ + DRIVER / INERT-PEER τ-FREEDOM.
--
-- The produce/consume/relay drivers are NATIVE Net_Api prefix chains
-- (`⟶`/`!⟶`/`⟶₀`/`Skip`/`>>=`) — react with `∅t` τ-branch, or `ret` (Skip);
-- the eight inert KA/TS/LN/LF peers are renamed reacts (fixed constants in
-- `decNodeX`).  Neither admits a τ.  Native `react-no-τ`/`ret-no-τ` mirror the
-- `RenTC` refutations without a rename.
------------------------------------------------------------------------

-- a native react with everywhere-`nothing` τ-branch admits NO τ
react-no-τ : {Rr : Set} {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    {vP  : (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr))}
    {τcP : (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr))}
  → PTree.force P ≡ react vP τcP → (∀ i a → τcP i a ≡ nothing) → ¬ (P ─[ τ ]─► M)
react-no-τ feqP h step with τ-inv step
... | inj₁ sileq with trans (sym sileq) feqP
...   | ()
react-no-τ feqP h step | inj₂ (v′ , τc′ , i , a , feq′ , beq)
  with proj₂ (react-injective (trans (sym feq′) feqP))
...   | refl with trans (sym beq) (h i a)
...     | ()

-- a native `ret` admits NO τ
ret-no-τ : {Rr : Set} {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr} {r : Rr}
  → PTree.force P ≡ ret r → ¬ (P ─[ τ ]─► M)
ret-no-τ feqP step with τ-inv step
... | inj₁ sileq with trans (sym sileq) feqP
...   | ()
ret-no-τ feqP step | inj₂ (v′ , τc′ , i , a , feq′ , beq)
  with trans (sym feq′) feqP
...   | ()

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; ConsDPh; consD
        ; CPPh; consuming; producing
        ; decProd; decCons; decConsD; decCP )

-- produce-driver τ-freedom (pp0..pp7 are prefix reacts; pp8 = Skip = ret)
decProd-no-τ : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh) {M : NetProc} → ¬ (decProd l d blk pp ─[ τ ]─► M)
decProd-no-τ l d blk pp0 = react-no-τ {P = decProd l d blk pp0} refl (λ _ _ → refl)
decProd-no-τ l d blk pp1 = react-no-τ {P = decProd l d blk pp1} refl (λ _ _ → refl)
decProd-no-τ l d blk pp2 = react-no-τ {P = decProd l d blk pp2} refl (λ _ _ → refl)
decProd-no-τ l d blk pp3 = react-no-τ {P = decProd l d blk pp3} refl (λ _ _ → refl)
decProd-no-τ l d blk pp4 = react-no-τ {P = decProd l d blk pp4} refl (λ _ _ → refl)
decProd-no-τ l d blk pp5 = react-no-τ {P = decProd l d blk pp5} refl (λ _ _ → refl)
decProd-no-τ l d blk pp6 = react-no-τ {P = decProd l d blk pp6} refl (λ _ _ → refl)
decProd-no-τ l d blk pp7 = react-no-τ {P = decProd l d blk pp7} refl (λ _ _ → refl)
decProd-no-τ l d blk pp8 = react-no-τ {P = decProd l d blk pp8} refl (λ _ _ → refl)
decProd-no-τ l d blk pp9 = ret-no-τ  {P = decProd l d blk pp9} refl

-- consume-driver τ-freedom (cp0..cp5 prefix reacts; cp6 = Ret b)
decCons-no-τ : (l : Link) (d : Dir) (b : _) (cp : ConsPh)
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) _} → ¬ (decCons l d b cp ─[ τ ]─► M)
decCons-no-τ l d b cp0 = react-no-τ {P = decCons l d b cp0} refl (λ _ _ → refl)
decCons-no-τ l d b cp1 = react-no-τ {P = decCons l d b cp1} refl (λ _ _ → refl)
decCons-no-τ l d b cp2 = react-no-τ {P = decCons l d b cp2} refl (λ _ _ → refl)
decCons-no-τ l d b cp3 = react-no-τ {P = decCons l d b cp3} refl (λ _ _ → refl)
decCons-no-τ l d b cp4 = react-no-τ {P = decCons l d b cp4} refl (λ _ _ → refl)
decCons-no-τ l d b cp5 = react-no-τ {P = decCons l d b cp5} refl (λ _ _ → refl)
decCons-no-τ l d b cp6 = ret-no-τ  {P = decCons l d b cp6} refl

-- node-D consume driver `decCons l hi b1 ph >> Skip` (cp0..cp5 react; cp6 = Skip>>… = ret? no: react bind then Skip)
decConsD-no-τ : (l : Link) (cph : ConsDPh) {M : NetProc} → ¬ (decConsD l cph ─[ τ ]─► M)
decConsD-no-τ l (consD b cp0) = react-no-τ {P = decConsD l (consD b cp0)} refl (λ _ _ → refl)
decConsD-no-τ l (consD b cp1) = react-no-τ {P = decConsD l (consD b cp1)} refl (λ _ _ → refl)
decConsD-no-τ l (consD b cp2) = react-no-τ {P = decConsD l (consD b cp2)} refl (λ _ _ → refl)
decConsD-no-τ l (consD b cp3) = react-no-τ {P = decConsD l (consD b cp3)} refl (λ _ _ → refl)
decConsD-no-τ l (consD b cp4) = react-no-τ {P = decConsD l (consD b cp4)} refl (λ _ _ → refl)
decConsD-no-τ l (consD b cp5) = react-no-τ {P = decConsD l (consD b cp5)} refl (λ _ _ → refl)
decConsD-no-τ l (consD b cp6) = ret-no-τ  {P = decConsD l (consD b cp6)} refl

-- relay driver `consume l₁ hi >>= produce l₂ hi` τ-freedom
decCP-no-τ : (l₁ l₂ : Link) (ph : CPPh) {M : NetProc} → ¬ (decCP l₁ l₂ ph ─[ τ ]─► M)
decCP-no-τ l₁ l₂ (consuming b cp0) = react-no-τ {P = decCP l₁ l₂ (consuming b cp0)} refl (λ _ _ → refl)
decCP-no-τ l₁ l₂ (consuming b cp1) = react-no-τ {P = decCP l₁ l₂ (consuming b cp1)} refl (λ _ _ → refl)
decCP-no-τ l₁ l₂ (consuming b cp2) = react-no-τ {P = decCP l₁ l₂ (consuming b cp2)} refl (λ _ _ → refl)
decCP-no-τ l₁ l₂ (consuming b cp3) = react-no-τ {P = decCP l₁ l₂ (consuming b cp3)} refl (λ _ _ → refl)
decCP-no-τ l₁ l₂ (consuming b cp4) = react-no-τ {P = decCP l₁ l₂ (consuming b cp4)} refl (λ _ _ → refl)
decCP-no-τ l₁ l₂ (consuming b cp5) = react-no-τ {P = decCP l₁ l₂ (consuming b cp5)} refl (λ _ _ → refl)
decCP-no-τ l₁ l₂ (consuming b cp6) = react-no-τ {P = decCP l₁ l₂ (consuming b cp6)} refl (λ _ _ → refl)
decCP-no-τ l₁ l₂ (producing b pp) = decProd-no-τ l₂ hi b pp
  where open import CSP.Examples.Cardano_network.Base using ( hi )

------------------------------------------------------------------------
-- INERT-PEER τ-FREEDOM (KA/TS/LN/LF client+server) — fixed renamed reacts in
-- `decNodeX` (SysNode tracks no inert-peer state), source τ-branch `∅t`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.NetworkPar p
  using ( ιKA; ιKA⁻¹; ιKA-linv; ιTS; ιTS⁻¹; ιTS-linv
        ; ιLN; ιLN⁻¹; ιLN-linv; ιLF; ιLF⁻¹; ιLF-linv
        ; KAclientA; KAserverA; TSclientA; TSserverA
        ; LNclientA; LNserverA; LFclientA; LFserverA )
open import CSP.Examples.Cardano_network.KeepAlive p using ( KAclientStClient; KAserverStClient )
open import CSP.Examples.Cardano_network.TxSubmission p using ( TSclientStClient; TSserverStClient )
open import CSP.Examples.Cardano_network.LeiosNotify p using ( LNclientStClient; LNserverStClient )
open import CSP.Examples.Cardano_network.LeiosFetch p using ( LFclientStClient; LFserverStClient )

module KANO = RenTC ιKA ιKA⁻¹ ιKA-linv
module TSNO = RenTC ιTS ιTS⁻¹ ιTS-linv
module LNNO = RenTC ιLN ιLN⁻¹ ιLN-linv
module LFNO = RenTC ιLF ιLF⁻¹ ιLF-linv

-- the eight inert peers admit no τ (renamed react with everywhere-`nothing` τ-branch)
KAclientA-no-τ : (l : Link) (d : Dir) {M : NetProc} → ¬ (KAclientA l d ─[ τ ]─► M)
KAclientA-no-τ l d = KANO.renameMap-react-no-τ {P = KAclientStClient l d} refl (λ _ _ → refl)
KAserverA-no-τ : (l : Link) (d : Dir) {M : NetProc} → ¬ (KAserverA l d ─[ τ ]─► M)
KAserverA-no-τ l d = KANO.renameMap-react-no-τ {P = KAserverStClient l d} refl (λ _ _ → refl)
TSclientA-no-τ : (l : Link) (d : Dir) {M : NetProc} → ¬ (TSclientA l d ─[ τ ]─► M)
TSclientA-no-τ l d = TSNO.renameMap-react-no-τ {P = TSclientStClient l d} refl (λ _ _ → refl)
TSserverA-no-τ : (l : Link) (d : Dir) {M : NetProc} → ¬ (TSserverA l d ─[ τ ]─► M)
TSserverA-no-τ l d = TSNO.renameMap-react-no-τ {P = TSserverStClient l d} refl (λ _ _ → refl)
LNclientA-no-τ : (l : Link) (d : Dir) {M : NetProc} → ¬ (LNclientA l d ─[ τ ]─► M)
LNclientA-no-τ l d = LNNO.renameMap-react-no-τ {P = LNclientStClient l d} refl (λ _ _ → refl)
LNserverA-no-τ : (l : Link) (d : Dir) {M : NetProc} → ¬ (LNserverA l d ─[ τ ]─► M)
LNserverA-no-τ l d = LNNO.renameMap-react-no-τ {P = LNserverStClient l d} refl (λ _ _ → refl)
LFclientA-no-τ : (l : Link) (d : Dir) {M : NetProc} → ¬ (LFclientA l d ─[ τ ]─► M)
LFclientA-no-τ l d = LFNO.renameMap-react-no-τ {P = LFclientStClient l d} refl (λ _ _ → refl)
LFserverA-no-τ : (l : Link) (d : Dir) {M : NetProc} → ¬ (LFserverA l d ─[ τ ]─► M)
LFserverA-no-τ l d = LFNO.renameMap-react-no-τ {P = LFserverStClient l d} refl (λ _ _ → refl)

------------------------------------------------------------------------
-- STAGE-2 GENERIC `△`-τ-ELIM.  The medium cell `decLink l ph false` is
-- `renameMap (⦀⋆ …) △ (break l ⟶₀ Skip)`.  The RIGHT operand `break l ⟶₀ Skip`
-- is a `Prefix` (its force is `react _ ∅t`), so its τ-branch is everywhere
-- `nothing` and it contributes NO τ; hence a τ of `P △ Q` is a LEFT-`P` τ giving
-- target `P′ △ Q`.  `△-τ-elim` inverts a `△` τ under these hypotheses.
------------------------------------------------------------------------

-- the visible-offer and τ-branch map types at the whole-system alphabet
VmapN : Set₁
VmapN = (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe NetProc)
TmapN : Set₁
TmapN = (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe NetProc)

-- force of `P △ Q` when BOTH operands are stable reacts (the third `_△_` clause)
force-△-react : {P Q : NetProc} {vP : VmapN} {τcP : TmapN} {vQ : VmapN} {τcQ : TmapN}
  → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
  → PTree.force (P △ Q)
      ≡ react (△-merge (react vP τcP) (react vQ τcQ) Q) (△-τ (react vP τcP) (react vQ τcQ) P Q)
force-△-react {P = P} {Q = Q} eqP eqQ with PTree.force P | eqP | PTree.force Q | eqQ
... | react vP τcP | refl | react vQ τcQ | refl = refl

-- invert a `just` result of the `△-τ` branch map (mirrors `△-τ`'s clauses):
-- the only firing index is `pair fin _ / lift fzero` (a left-`P` τ), giving the
-- source step + `M ≡ P′ △ Q`; every other index is `nothing` (refuted), and the
-- `lift (fsuc fzero)` (right-`Q`) tag is `nothing` by the τ-freedom hypothesis
△-τ-branch-inv : (P Q : NetProc) (vP : VmapN) (τcP : TmapN) (vQ : VmapN) (τcQ : TmapN)
  → PTree.force P ≡ react vP τcP
  → (∀ i a → τcQ i a ≡ nothing)
  → (i : AnyTypes (ExtI (Net_Api Payload))) (a : proj₁ i) {M : NetProc}
  → △-τ (react vP τcP) (react vQ τcQ) P Q i a ≡ just M
  → Σ[ P′ ∈ NetProc ] (P ─[ τ ]─► P′) × (M ≡ (P′ △ Q))
△-τ-branch-inv P Q vP τcP vQ τcQ eqP hQ (_ , base _) a ()
△-τ-branch-inv P Q vP τcP vQ τcQ eqP hQ (_ , fin) a ()
△-τ-branch-inv P Q vP τcP vQ τcQ eqP hQ (_ , pair (base _) _) a ()
△-τ-branch-inv P Q vP τcP vQ τcQ eqP hQ (_ , pair (pair _ _) _) a ()
△-τ-branch-inv P Q vP τcP vQ τcQ eqP hQ (_ , pair fin i) (lift fzero , a₀) beq
    with τcP (_ , i) a₀ in eqτ
... | just P′ = P′ , sTau eqP eqτ , sym (just-injective beq)
... | nothing with beq
...   | ()
△-τ-branch-inv P Q vP τcP vQ τcQ eqP hQ (_ , pair fin i) (lift (fsuc fzero) , a₀) beq
    rewrite hQ (_ , i) a₀ with beq
... | ()
△-τ-branch-inv P Q vP τcP vQ τcQ eqP hQ (_ , pair fin i) (lift (fsuc (fsuc _)) , a₀) ()

-- `△`-τ-elim: a τ of `P △ Q` (both reacts, `Q` τ-free) is a left-`P` τ ⇒ `P′ △ Q`
△-τ-elim : {P Q M : NetProc} {vP : VmapN} {τcP : TmapN} {vQ : VmapN} {τcQ : TmapN}
  → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
  → (∀ i a → τcQ i a ≡ nothing)
  → (P △ Q) ─[ τ ]─► M
  → Σ[ P′ ∈ NetProc ] (P ─[ τ ]─► P′) × (M ≡ (P′ △ Q))
△-τ-elim {P = P} {Q = Q} eqP eqQ hQ step with τ-inv step
... | inj₁ sileq with trans (sym (force-△-react eqP eqQ)) sileq
...   | ()
△-τ-elim {P = P} {Q = Q} eqP eqQ hQ step | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with react-injective (trans (sym feq′) (force-△-react eqP eqQ))
...   | _ , refl = △-τ-branch-inv P Q _ _ _ _ eqP hQ i a beq

------------------------------------------------------------------------
-- STAGE-2 GENERIC `△`-ev-ELIM.  A VISIBLE step of `P △ Q` at an event that the
-- RIGHT operand `Q` does NOT offer (`vQ (X,e) a ≡ nothing`) is a LEFT-`P` step
-- with target `P′ △ Q` (the `△-merge` `just P' | nothing` clause).  For the
-- medium's live link, `Q = break l ⟶₀ Skip` offers ONLY the `break l` event, so
-- every copy-channel io (`input`/`output`) satisfies the `vQ`-nothing hypothesis.
------------------------------------------------------------------------

-- invert a `just` of the `△-merge` offer at an event `Q` does not offer: only
-- the `just P' | nothing` clause can fire (both-offer / Q-only refuted by `vQno`);
-- builds the LEFT-`P` step directly (offer `in`-eq consumed by `sVis`, not returned)
△-merge-ev-inv : (P : NetProc) (vP : VmapN) (τcP : TmapN) (vQ : VmapN) (τcQ : TmapN)
    (Q : NetProc) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) {M : NetProc}
  → PTree.force P ≡ react vP τcP
  → vQ (X , e) a ≡ nothing
  → △-merge (react vP τcP) (react vQ τcQ) Q (X , e) a ≡ just M
  → Σ[ P′ ∈ NetProc ] (P ─[ ev (evl (evLabel X e a)) ]─► P′) × (M ≡ (P′ △ Q))
△-merge-ev-inv P vP τcP vQ τcQ Q e a eqP vQno meq rewrite vQno with vP (_ , e) a in vpe
... | just P′ = P′ , sVis eqP vpe , sym (just-injective meq)
... | nothing with meq
...   | ()

-- `△`-ev-elim: a visible step of `P △ Q` (both reacts) at an event `Q` refuses is
-- a left-`P` step ⇒ `P′ △ Q`
△-ev-elim : {P Q M : NetProc} {vP : VmapN} {τcP : TmapN} {vQ : VmapN} {τcQ : TmapN}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
  → vQ (X , e) a ≡ nothing
  → (P △ Q) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ P′ ∈ NetProc ] (P ─[ ev (evl (evLabel X e a)) ]─► P′) × (M ≡ (P′ △ Q))
△-ev-elim {P = P} {Q = Q} {vP = vP} {τcP = τcP} {vQ = vQ} {τcQ = τcQ} {X} {e} {a}
          eqP eqQ vQno step with ev-inv step
... | v , τc , feq , veq with react-injective (trans (sym feq) (force-△-react eqP eqQ))
...   | vEq , _ = △-merge-ev-inv P vP τcP vQ τcQ Q e a eqP vQno
                       (trans (sym (cong (λ w → w (X , e) a) vEq)) veq)

------------------------------------------------------------------------
-- STEP-1 PER-CELL DRAIN INVERSION.  A copy cell `decCopy l d id ph` (Net Payload,
-- pre-rename) has its ONLY τ at `draining x` (the post-`output` loop-back sil to
-- `Copy l d id = decCopy … empty`); `empty` (the `loop0`/`pchoice` head) and
-- `full x` are STABLE reacts (offer input/output, everywhere-`nothing` τ-branch).
------------------------------------------------------------------------

-- a native Net-Payload react with everywhere-`nothing` τ-branch admits NO τ
reactN-no-τ : {Rr : Set} {P M : PTree (Net Payload) (ExtI (Net Payload)) Rr}
    {vP  : (at : AnyTypes (Net Payload)) → ContinueType at (Maybe (PTree (Net Payload) (ExtI (Net Payload)) Rr))}
    {τcP : (i : AnyTypes (ExtI (Net Payload))) → ContinueType i (Maybe (PTree (Net Payload) (ExtI (Net Payload)) Rr))}
  → PTree.force P ≡ react vP τcP → (∀ i a → τcP i a ≡ nothing) → ¬ (P LN.─[ LN.τ ]─► M)
reactN-no-τ feqP h step with LN.τ-inv step
... | inj₁ sileq with trans (sym sileq) feqP
...   | ()
reactN-no-τ feqP h step | inj₂ (v′ , τc′ , i , a , feq′ , beq)
  with proj₂ (react-injective (trans (sym feq′) feqP))
...   | refl with trans (sym beq) (h i a)
...     | ()

-- the `empty` cell (`Copy` head, `loop0`/`pchoice`) is τ-free: its force is a
-- stable react with everywhere-`nothing` τ-branch, MANIFEST by `refl` (no `succV`
-- resolution needed — the `iter-bind`/`>>=`/`pchoice` layer forces to a react and
-- its τ-branch propagates `pchoice`'s `∅t`).  The `full x` / `draining x` cells
-- need `succV`-unfolding force lemmas (DecEq resolution) — the remaining step-1 piece.
decCopy-empty-no-τ : (l : Link) (d : Dir) (id : IDs) {M : NetProcN}
  → ¬ (decCopy l d id empty LN.─[ LN.τ ]─► M)
decCopy-empty-no-τ l d id = reactN-no-τ {P = decCopy l d id empty} refl (λ _ _ → refl)

-- `succV`-FORCE for the `full x` cell: after the `input l d id` fire resolves
-- (`copyMenu`'s `l≟l|d≟d|id≟id`), the cell forces to a stable react offering
-- `output l d id ! x` with an everywhere-`nothing` τ-branch.  Existentially
-- packaged (the react's offer/τ maps are `iter`/`bind` internals we don't name).
ffull-react : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → Σ[ V ∈ ((at : AnyTypes (Net Payload)) → ContinueType at (Maybe NetProcN)) ]
    Σ[ T ∈ ((i : AnyTypes (ExtI (Net Payload))) → ContinueType i (Maybe NetProcN)) ]
      (PTree.force (decCopy l d id (full x)) ≡ react V T) × (∀ i a → T i a ≡ nothing)
ffull-react l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id =
  _ , _ , refl , λ _ _ → refl

-- `full x` cell is τ-free (offers only the visible `output`, no τ-branch)
decCopy-full-no-τ : (l : Link) (d : Dir) (id : IDs) (x : Payload) {M : NetProcN}
  → ¬ (decCopy l d id (full x) LN.─[ LN.τ ]─► M)
decCopy-full-no-τ l d id x step with ffull-react l d id x
... | V , T , feq , hT = reactN-no-τ {P = decCopy l d id (full x)} {vP = V} {τcP = T} feq hT step

-- `succV`-FORCE for the `draining x` cell: after the `input` fire AND the
-- `output l d id ! x` fire resolve (`Net-≟` output reuses `l≟l|d≟d|id≟id`;
-- `Output-cont`'s value match adds `x≟x`), the cell's force is the loop-back
-- `sil (Copy l d id) = sil (decCopy l d id empty)` — the drain sil.
fdrain : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → PTree.force (decCopy l d id (draining x)) ≡ sil (decCopy l d id empty)
fdrain l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id
                      | ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id | ≟-yes-refl x = refl

-- per-cell τ-inversion: a copy cell's ONLY τ is the `draining x → empty` drain sil
decCopy-τ-inv : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase) {M : NetProcN}
  → decCopy l d id ph LN.─[ LN.τ ]─► M
  → Σ[ x ∈ Payload ] (ph ≡ draining x) × (M ≡ decCopy l d id empty)
decCopy-τ-inv l d id empty      step = ⊥-elim (decCopy-empty-no-τ l d id step)
decCopy-τ-inv l d id (full x)   step = ⊥-elim (decCopy-full-no-τ l d id x step)
decCopy-τ-inv l d id (draining x) step with LN.τ-inv step
... | inj₁ sileq = x , refl , sil-injective (trans (sym sileq) (fdrain l d id x))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq) with trans (sym feq′) (fdrain l d id x)
...   | ()

------------------------------------------------------------------------
-- STEP-3 POSITIONAL PEELS.  A τ of a `⦀⋆` / `⦀Fin` interleave is exactly one
-- operand's τ; the peel returns the POSITION (list index / Fin) + the operand
-- step + the target as the interleave with that position updated.  Both are
-- generic; `Par-τ-elim ∅ES` peels each layer (empty sync set, no evSync).
------------------------------------------------------------------------

-- a native Net-Payload `ret` admits NO τ (the `⦀⋆ []` = `Skip` tail)
retN-no-τ : {Rr : Set} {P M : PTree (Net Payload) (ExtI (Net Payload)) Rr} {r : Rr}
  → PTree.force P ≡ ret r → ¬ (P LN.─[ LN.τ ]─► M)
retN-no-τ feqP step with LN.τ-inv step
... | inj₁ sileq with trans (sym sileq) feqP
...   | ()
retN-no-τ feqP step | inj₂ (v′ , τc′ , i , a , feq′ , beq) with trans (sym feq′) feqP
...   | ()

-- `⦀⋆` list peel: a τ of `⦀⋆ Ps` is a τ of `Ps`'s cell at some position `k`,
-- with target `⦀⋆ (Ps` updated at `k)` (positional; reconstruction is `cong`)
⦀⋆-τ-inv : (Ps : List NetProcN) {M : NetProcN} → ⦀⋆ Ps LN.─[ LN.τ ]─► M
  → Σ[ k ∈ Fin (length Ps) ] Σ[ Mk ∈ NetProcN ]
      (lookup Ps k LN.─[ LN.τ ]─► Mk) × (M ≡ ⦀⋆ (updateAt Ps k (λ _ → Mk)))
⦀⋆-τ-inv []       step = ⊥-elim (retN-no-τ {P = Skip} refl step)
⦀⋆-τ-inv (P ∷ Ps) step with PEN.Par-τ-elim ∅ES (λ _ _ → tt) P (⦀⋆ Ps) step
... | PEN.τL P' pstep refl = fzero , P' , pstep , refl
... | PEN.τR Q' qstep refl with ⦀⋆-τ-inv Ps qstep
...   | k , Mk , lstep , meq = fsuc k , Mk , lstep , cong (P OpN.⦀_) meq

-- functional pointwise update of a `Fin n`-indexed family at index `i` (defined
-- by Fin recursion, so `⦀Fin`'s peel reconstruction reduces definitionally)
finUpd : ∀ {n} → (Fin n → NetProc) → Fin n → NetProc → Fin n → NetProc
finUpd f fzero    Mi fzero    = Mi
finUpd f fzero    Mi (fsuc j) = f (fsuc j)
finUpd f (fsuc i) Mi fzero    = f fzero
finUpd f (fsuc i) Mi (fsuc j) = finUpd (λ k → f (fsuc k)) i Mi j

-- `⦀Fin` link peel: a τ of `⦀Fin n f` is a τ of `f` at some index `i`, with
-- target `⦀Fin n (finUpd f i Mi)` (positional; `Skip` tail at n=0 is τ-free)
⦀Fin-τ-inv : (n : ℕ) (f : Fin n → NetProc) {M : NetProc} → ⦀Fin n f ─[ τ ]─► M
  → Σ[ i ∈ Fin n ] Σ[ Mi ∈ NetProc ]
      (f i ─[ τ ]─► Mi) × (M ≡ ⦀Fin n (finUpd f i Mi))
⦀Fin-τ-inv zero f step = ⊥-elim (ret-no-τ {P = ⦀Fin zero f} refl step)
⦀Fin-τ-inv (suc n) f step
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (f fzero) (⦀Fin n (λ i → f (fsuc i))) step
... | PEA.τL P' pstep refl = fzero , P' , pstep , refl
... | PEA.τR Q' qstep refl with ⦀Fin-τ-inv n (λ i → f (fsuc i)) qstep
...   | i , Mi , istep , meq = fsuc i , Mi , istep , cong (f fzero ⦀_) meq

------------------------------------------------------------------------
-- STEP-1 WRAP — `fold-react` (react-witness for `△-τ-elim`'s LEFT operand).
--
-- The medium's live link is `renameMap (⦀⋆ cells) △ (break l ⟶₀ Skip)` with
-- `cells = map (decCopy l · · (ph · ·)) (linkConfig l)` — 8 concrete cells over
-- `uniformCfg`.  Each cell forces to a `react` (`empty`/`full`) or a `sil`
-- (`draining`), NEVER a `ret`; folding ≥2 such cells with `_⦀_` yields a react
-- (both operands non-`ret` ⇒ `fPar-nn`).  The tail `cell ⦀ Skip` is `fPar-er`
-- (react) / `fPar-sr` (sil).  So `force (⦀⋆ cells) ≡ react _ _`, and applying
-- `MedNO.force-renameMap-react` transports it through the rename.
------------------------------------------------------------------------

-- the Net-Payload visible-offer / τ-branch map types
VmapNN : Set₁
VmapNN = (at : AnyTypes (Net Payload)) → ContinueType at (Maybe NetProcN)
TmapNN : Set₁
TmapNN = (i : AnyTypes (ExtI (Net Payload))) → ContinueType i (Maybe NetProcN)

-- a react-or-sil force witness (a cell / fold is never `ret`)
data RSForce (P : NetProcN) : Set₁ where
  rsR : (v : VmapNN) (τc : TmapNN) → PTree.force P ≡ react v τc → RSForce P
  rsS : (P′ : NetProcN) → PTree.force P ≡ sil P′ → RSForce P

-- every copy cell forces to a react (`empty`/`full`) or a sil (`draining`)
cell-RS : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase) → RSForce (decCopy l d id ph)
cell-RS l d id empty        = rsR _ _ refl
cell-RS l d id (full x)     with ffull-react l d id x
... | V , T , feq , _ = rsR V T feq
cell-RS l d id (draining x) = rsS _ (fdrain l d id x)

-- the fold of a nonempty mapped config is react-or-sil (never `ret`): the
-- innermost `cell ⦀ Skip` is `fPar-er`/`fPar-sr`; an outer `cell ⦀ fold` is
-- `fPar-nn` (both non-`ret`, so a react)
foldRS : (l : Link) (ph : Dir → IDs → CopyPhase) (hd : Dir × IDs) (tl : List (Dir × IDs))
       → RSForce (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (hd ∷ tl)))
foldRS l ph (d , id) [] with cell-RS l d id (ph d id)
... | rsR v τc feq = rsR _ _ (fPar-er ∅ES (λ _ _ → tt) feq refl)
... | rsS P′ feq   = rsS _ (fPar-sr ∅ES (λ _ _ → tt) feq refl)
foldRS l ph (d , id) (hd1 ∷ tl) with cell-RS l d id (ph d id) | foldRS l ph hd1 tl
... | rsR v τc feq | rsR v' τc' geq = rsR _ _ (fPar-nn ∅ES (λ _ _ → tt) feq geq ttU ttU)
... | rsR v τc feq | rsS Q′ geq     = rsR _ _ (fPar-nn ∅ES (λ _ _ → tt) feq geq ttU ttU)
... | rsS P′ feq   | rsR v' τc' geq = rsR _ _ (fPar-nn ∅ES (λ _ _ → tt) feq geq ttU ttU)
... | rsS P′ feq   | rsS Q′ geq     = rsR _ _ (fPar-nn ∅ES (λ _ _ → tt) feq geq ttU ttU)

-- a react-force witness (a fold of ≥2 non-`ret` cells is a react)
data ReactF (P : NetProcN) : Set₁ where
  mkReactF : (v : VmapNN) (τc : TmapNN) → PTree.force P ≡ react v τc → ReactF P

-- a fold over ≥2 mapped cells forces to a react (top `_⦀_` is `fPar-nn`)
foldRS2 : (l : Link) (ph : Dir → IDs → CopyPhase) (hd0 hd1 : Dir × IDs) (tl : List (Dir × IDs))
  → ReactF (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (hd0 ∷ hd1 ∷ tl)))
foldRS2 l ph (d , id) hd1 tl with cell-RS l d id (ph d id) | foldRS l ph hd1 tl
... | rsR v τc feq | rsR v' τc' geq = mkReactF _ _ (fPar-nn ∅ES (λ _ _ → tt) feq geq ttU ttU)
... | rsR v τc feq | rsS Q′ geq     = mkReactF _ _ (fPar-nn ∅ES (λ _ _ → tt) feq geq ttU ttU)
... | rsS P′ feq   | rsR v' τc' geq = mkReactF _ _ (fPar-nn ∅ES (λ _ _ → tt) feq geq ttU ttU)
... | rsS P′ feq   | rsS Q′ geq     = mkReactF _ _ (fPar-nn ∅ES (λ _ _ → tt) feq geq ttU ttU)

-- the concrete link config (`uniformCfg`), spelled out (used to `rewrite`
-- `linkConfig l` to a manifest cons so the fold reduces / the react is exposed)
cfgEq : (l : Link) → linkConfig l
  ≡ ( (lo , N2N_KeepAlive)    ∷ (hi , N2N_KeepAlive)
    ∷ (lo , N2N_ChainSync)    ∷ (hi , N2N_ChainSync)
    ∷ (lo , N2N_BlockFetch)   ∷ (hi , N2N_BlockFetch)
    ∷ (lo , N2N_TxSubmission) ∷ (hi , N2N_TxSubmission)
    ∷ (lo , N2N_LeiosNotify)  ∷ (hi , N2N_LeiosNotify)
    ∷ (lo , N2N_LeiosFetch)   ∷ (hi , N2N_LeiosFetch) ∷ [] )
cfgEq l = refl

-- `fold-react`: the reconstructed copy fold forces to a react (`linkConfig l`
-- is `uniformCfg`, 12 ≥2 cells, so the top `_⦀_` is `fPar-nn`).  `rewrite cfgEq`
-- makes the config a manifest cons (substitution, NOT coinductive unification).
fold-react : (l : Link) (ph : Dir → IDs → CopyPhase)
  → ReactF (⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))
fold-react l ph rewrite cfgEq l = foldRS2 l ph (lo , N2N_KeepAlive) (hi , N2N_KeepAlive)
  ( (lo , N2N_ChainSync)    ∷ (hi , N2N_ChainSync)
  ∷ (lo , N2N_BlockFetch)   ∷ (hi , N2N_BlockFetch)
  ∷ (lo , N2N_TxSubmission) ∷ (hi , N2N_TxSubmission)
  ∷ (lo , N2N_LeiosNotify)  ∷ (hi , N2N_LeiosNotify)
  ∷ (lo , N2N_LeiosFetch)   ∷ (hi , N2N_LeiosFetch) ∷ [] )

------------------------------------------------------------------------
-- STEP-2 GLUE HELPERS — the medium reconstruction backbone.
------------------------------------------------------------------------

-- the `RenTC` instance for the copy medium (Net → Net_Api), SAME ι as `decLink`
module MedNO = RenTC ιNet ιNet⁻¹ ιNet-linv
-- the copy-medium rename (SAME instance `decLink` uses; imported for the congs)
open import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv using ( renameMap )

-- `⦀Fin`-congruence WITHOUT funext (structural `cong₂` on `_⦀_`)
⦀Fin-cong : (n : ℕ) (f g : Fin n → NetProc) → (∀ j → f j ≡ g j) → ⦀Fin n f ≡ ⦀Fin n g
⦀Fin-cong zero    f g h = refl
⦀Fin-cong (suc n) f g h =
  cong₂ _⦀_ (h fzero) (⦀Fin-cong n (λ j → f (fsuc j)) (λ j → g (fsuc j)) (λ j → h (fsuc j)))

-- flip one cell `(d₀,id₀)` of a link's cell-phase function to `empty`
flipCell : (Dir → IDs → CopyPhase) → Dir → IDs → (Dir → IDs → CopyPhase)
flipCell g d₀ id₀ d id with d ≟ d₀ | id ≟ id₀
... | no  _ | _     = g d id
... | yes _ | no  _ = g d id
... | yes _ | yes _ = empty

------------------------------------------------------------------------
-- STEP-2 LINK τ-INVERSION.  The `break`-interrupted rename of the copy fold:
-- `△-τ-elim` (LEFT-`P` τ) → `renameMap-τ-reflect` (source τ) → `⦀⋆-τ-inv`
-- (one cell position) → `decCopy-τ-inv` (that cell drained `draining x → empty`).
-- The stepped position `k` is enumerated CONCRETELY over `uniformCfg`'s 8 keys,
-- and the positional `updateAt` reconstruction equals a KEY-indexed `flipCell`
-- (distinct keys ⇒ each cell equality holds by `refl`).
------------------------------------------------------------------------

-- per-position drain: at concrete cell index `k` the cell `(dₖ,idₖ)` drained
-- (`draining x → empty`), so the positional `updateAt` equals the key-flip `map`
cellFlip : (l : Link) (ph : Dir → IDs → CopyPhase)
    (k : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)))) {Mk : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k LN.─[ LN.τ ]─► Mk
  → Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ]
       (updateAt (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k (λ _ → Mk)
          ≡ map (λ { (d , id) → decCopy l d id (flipCell ph d₀ id₀ d id) }) (linkConfig l))
cellFlip l ph fzero cs with decCopy-τ-inv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) cs
... | x , _ , Mkeq rewrite Mkeq = lo , N2N_KeepAlive , refl
cellFlip l ph (fsuc fzero) cs with decCopy-τ-inv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) cs
... | x , _ , Mkeq rewrite Mkeq = hi , N2N_KeepAlive , refl
cellFlip l ph (fsuc (fsuc fzero)) cs with decCopy-τ-inv l lo N2N_ChainSync (ph lo N2N_ChainSync) cs
... | x , _ , Mkeq rewrite Mkeq = lo , N2N_ChainSync , refl
cellFlip l ph (fsuc (fsuc (fsuc fzero))) cs with decCopy-τ-inv l hi N2N_ChainSync (ph hi N2N_ChainSync) cs
... | x , _ , Mkeq rewrite Mkeq = hi , N2N_ChainSync , refl
cellFlip l ph (fsuc (fsuc (fsuc (fsuc fzero)))) cs with decCopy-τ-inv l lo N2N_BlockFetch (ph lo N2N_BlockFetch) cs
... | x , _ , Mkeq rewrite Mkeq = lo , N2N_BlockFetch , refl
cellFlip l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) cs with decCopy-τ-inv l hi N2N_BlockFetch (ph hi N2N_BlockFetch) cs
... | x , _ , Mkeq rewrite Mkeq = hi , N2N_BlockFetch , refl
cellFlip l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) cs with decCopy-τ-inv l lo N2N_TxSubmission (ph lo N2N_TxSubmission) cs
... | x , _ , Mkeq rewrite Mkeq = lo , N2N_TxSubmission , refl
cellFlip l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) cs with decCopy-τ-inv l hi N2N_TxSubmission (ph hi N2N_TxSubmission) cs
... | x , _ , Mkeq rewrite Mkeq = hi , N2N_TxSubmission , refl
cellFlip l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) cs with decCopy-τ-inv l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) cs
... | x , _ , Mkeq rewrite Mkeq = lo , N2N_LeiosNotify , refl
cellFlip l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) cs with decCopy-τ-inv l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) cs
... | x , _ , Mkeq rewrite Mkeq = hi , N2N_LeiosNotify , refl
cellFlip l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) cs with decCopy-τ-inv l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) cs
... | x , _ , Mkeq rewrite Mkeq = lo , N2N_LeiosFetch , refl
cellFlip l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) cs with decCopy-τ-inv l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) cs
... | x , _ , Mkeq rewrite Mkeq = hi , N2N_LeiosFetch , refl

-- link τ-inversion: an unbroken link's τ is one cell draining; the target is the
-- same link with that cell's key flipped to `empty` (broken link `Skip` is τ-free)
decLink-τ-inv : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool) {Mi : NetProc}
  → decLink l ph b ─[ τ ]─► Mi
  → Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ]
       (b ≡ false) × (Mi ≡ decLink l (flipCell ph d₀ id₀) false)
decLink-τ-inv l ph true  step = ⊥-elim (ret-no-τ {P = decLink l ph true} refl step)
decLink-τ-inv l ph false step with fold-react l ph
... | mkReactF V T feq
    with △-τ-elim (MedNO.force-renameMap-react
                    {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                  refl (λ _ _ → refl) step
...   | P′ , renStep , Meq2
      with MedNO.renameMap-τ-reflect renStep
...     | Q′ , foldStep , P′eq
        with ⦀⋆-τ-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) foldStep
...       | k , Mk , cellStep , Q′eq with cellFlip l ph k cellStep
...         | d₀ , id₀ , listEq =
              d₀ , id₀ , refl ,
              trans Meq2
                (trans (cong (λ z → z △ (break l ⟶₀ Op.Skip)) P′eq)
                  (trans (cong (λ z → renameMap z △ (break l ⟶₀ Op.Skip)) Q′eq)
                         (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Op.Skip)) listEq)))

------------------------------------------------------------------------
-- STEP-2 MEDIUM τ-INVERSION.  `⦀Fin-τ-inv` peels the four-link interleave to one
-- stepping link `i`; `decLink-τ-inv` flips that link's drained cell to `empty`.
-- The reconstructed `MedState` uses a key-indexed phase update `phase-upd`,
-- bridged to the positional `finUpd` by `phaseUpd-finUpd` (generic in `i`,`j`,
-- so NO `numLinks` case split): `finUpd`-hit/miss + `phase-upd`-hit/miss.
------------------------------------------------------------------------

-- `finUpd` returns the update at its own index
finUpd-hit : ∀ {n} (f : Fin n → NetProc) (i : Fin n) (Mi : NetProc) → finUpd f i Mi i ≡ Mi
finUpd-hit f fzero    Mi = refl
finUpd-hit f (fsuc i) Mi = finUpd-hit (λ k → f (fsuc k)) i Mi

-- `finUpd` is the identity away from its index
finUpd-miss : ∀ {n} (f : Fin n → NetProc) (i j : Fin n) (Mi : NetProc)
  → i ≢ j → finUpd f i Mi j ≡ f j
finUpd-miss f fzero    fzero    Mi i≢j = ⊥-elim (i≢j refl)
finUpd-miss f fzero    (fsuc j) Mi i≢j = refl
finUpd-miss f (fsuc i) fzero    Mi i≢j = refl
finUpd-miss f (fsuc i) (fsuc j) Mi i≢j =
  finUpd-miss (λ k → f (fsuc k)) i j Mi (λ p → i≢j (cong fsuc p))

-- key-indexed link-phase update (change link `i`'s cell function to `g`)
phase-upd : (Link → Dir → IDs → CopyPhase) → Link → (Dir → IDs → CopyPhase)
          → Link → Dir → IDs → CopyPhase
phase-upd ph i g l with l ≟ i
... | yes _ = g
... | no  _ = ph l

-- the KEY↔POSITIONAL bridge: decoding a `phase-upd`-updated medium at link `j`
-- equals the positional `finUpd` of the link decode (generic in `i`,`j`).  The
-- shared `j ≟ i` scrutinee auto-reduces `phase-upd` in each branch, so only the
-- `finUpd` hit/miss facts remain.
phaseUpd-finUpd : (m : MedState) (i : Link) (g : Dir → IDs → CopyPhase) (j : Link)
  → decLink j (phase-upd (phase m) i g j) (broken m j)
     ≡ finUpd (λ l → decLink l (phase m l) (broken m l)) i (decLink i g (broken m i)) j
phaseUpd-finUpd m i g j with j ≟ i
... | yes p rewrite p =
      sym (finUpd-hit (λ l → decLink l (phase m l) (broken m l)) i (decLink i g (broken m i)))
... | no ¬p =
      sym (finUpd-miss (λ l → decLink l (phase m l) (broken m l)) i j
             (decLink i g (broken m i)) (λ q → ¬p (sym q)))

-- reconstruct: the positional `⦀Fin`/`finUpd` target is the decode of the
-- `phase-upd`-updated `MedState`
recon-decMed : (m : MedState) (i : Link) (g : Dir → IDs → CopyPhase)
  → ⦀Fin numLinks (finUpd (λ l → decLink l (phase m l) (broken m l)) i (decLink i g (broken m i)))
     ≡ decMed (mkMed (phase-upd (phase m) i g) (broken m))
recon-decMed m i g =
  sym (⦀Fin-cong numLinks
         (λ l → decLink l (phase-upd (phase m) i g l) (broken m l))
         (finUpd (λ l → decLink l (phase m l) (broken m l)) i (decLink i g (broken m i)))
         (λ j → phaseUpd-finUpd m i g j))

-- MEDIUM τ-inversion (TOTAL): a medium τ is one link's cell draining
-- (`draining x → empty`), reflected to a reachable `MedState` successor
medium-τ-inv : (m : MedState) {M : NetProc}
  → decMed m ─[ τ ]─► M → Σ[ m′ ∈ MedState ] (M ≡ decMed m′)
medium-τ-inv m step
    with ⦀Fin-τ-inv numLinks (λ l → decLink l (phase m l) (broken m l)) step
... | i , Mi , linkStep , Meq with decLink-τ-inv i (phase m i) (broken m i) linkStep
...   | d₀ , id₀ , brEq , MiEq =
        mkMed (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀)) (broken m) ,
        trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                    (finUpd (λ l → decLink l (phase m l) (broken m l)) i z))
                    (trans MiEq (cong (decLink i (flipCell (phase m i) d₀ id₀)) (sym brEq))))
                 (recon-decMed m i (flipCell (phase m i) d₀ id₀)))


------------------------------------------------------------------------
-- TxSubmission client / server τ-inversions (R2 D3, folded threading).  The
-- TS pair is now TRACKED in `bundleG`, so `bundle-τ-inv` must INVERT — not
-- refute — the TS peer's loop-re-entry τ.  Only the `…Sil` position carries a
-- τ (identical shape to `csSil`); every `…Head st` is react/ret and refuted.
------------------------------------------------------------------------

-- source-force lemmas at the TS-client stIdle receive leaves (unstick the receiveTS `l≟l|d≟d` guard)
htcReqIdsB1 : (l : Link) (d : Dir) (a r : _) → PTree.force (decTSc-src l d (tcReqIdsB1 a r)) ≡ react _ _
htcReqIdsB1 l d a r rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htcReqIdsNB1 : (l : Link) (d : Dir) (a r : _) → PTree.force (decTSc-src l d (tcReqIdsNB1 a r)) ≡ react _ _
htcReqIdsNB1 l d a r rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htcReqTxs1 : (l : Link) (d : Dir) (ids : _) → PTree.force (decTSc-src l d (tcReqTxs1 ids)) ≡ react _ _
htcReqTxs1 l d ids rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htcRepB1 : (l : Link) (d : Dir) (ids : _) → PTree.force (decTSc-src l d (tcRepB1 ids)) ≡ react _ _
htcRepB1 l d ids rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htcDone1 : (l : Link) (d : Dir) → PTree.force (decTSc-src l d tcDone1) ≡ react _ _
htcDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htcRepNB1 : (l : Link) (d : Dir) (ids : _) → PTree.force (decTSc-src l d (tcRepNB1 ids)) ≡ react _ _
htcRepNB1 l d ids rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htcRepTxs1 : (l : Link) (d : Dir) (txs : _) → PTree.force (decTSc-src l d (tcRepTxs1 txs)) ≡ react _ _
htcRepTxs1 l d txs rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- TxSubmission client τ-inversion: only the loop re-entry sil carries a τ
decTSc-τ-inv : (l : Link) (d : Dir) (pos : TScPos) {M : NetProc}
  → decTSc l d pos ─[ τ ]─► M
  → Σ[ st ∈ TS.TSState ] (pos ≡ tcSil st) × (M ≡ decTSc l d (tcHead st))
decTSc-τ-inv l d (tcHead TS.stInit)             step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcHead TS.stInit)} refl (λ _ _ → refl) step)
decTSc-τ-inv l d (tcHead TS.stIdle)             step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcHead TS.stIdle)} refl (λ _ _ → refl) step)
decTSc-τ-inv l d (tcHead TS.stTxIdsBlocking)    step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcHead TS.stTxIdsBlocking)} refl (λ _ _ → refl) step)
decTSc-τ-inv l d (tcHead TS.stTxIdsNonBlocking) step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcHead TS.stTxIdsNonBlocking)} refl (λ _ _ → refl) step)
decTSc-τ-inv l d (tcHead TS.stTxs)              step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcHead TS.stTxs)} refl (λ _ _ → refl) step)
decTSc-τ-inv l d (tcHead TS.stDone)             step = ⊥-elim (TSNO.renameMap-ret-no-τ   {P = decTSc-src l d (tcHead TS.stDone)} refl step)
decTSc-τ-inv l d (tcReqIdsB1 a r)  step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcReqIdsB1 a r)}  (htcReqIdsB1 l d a r)  (λ _ _ → refl) step)
decTSc-τ-inv l d (tcReqIdsNB1 a r) step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcReqIdsNB1 a r)} (htcReqIdsNB1 l d a r) (λ _ _ → refl) step)
decTSc-τ-inv l d (tcReqTxs1 ids)   step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcReqTxs1 ids)}   (htcReqTxs1 l d ids)   (λ _ _ → refl) step)
decTSc-τ-inv l d (tcRepB1 ids)  step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcRepB1 ids)}  (htcRepB1 l d ids)  (λ _ _ → refl) step)
decTSc-τ-inv l d tcDone1        step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d tcDone1}        (htcDone1 l d)      (λ _ _ → refl) step)
decTSc-τ-inv l d (tcRepNB1 ids) step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcRepNB1 ids)} (htcRepNB1 l d ids) (λ _ _ → refl) step)
decTSc-τ-inv l d (tcRepTxs1 txs) step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSc-src l d (tcRepTxs1 txs)} (htcRepTxs1 l d txs) (λ _ _ → refl) step)
decTSc-τ-inv l d (tcSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (TSNO.force-renameMap-sil
             {P = decTSc-src l d (tcSil st)} {P′ = decTSc-src l d (tcHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (TSNO.force-renameMap-sil
             {P = decTSc-src l d (tcSil st)} {P′ = decTSc-src l d (tcHead st)} refl)
...   | ()

-- source-force lemma at the TS-server receive-done leaf (unstick the receiveTS `l≟l|d≟d` guard)
htsDone1 : (l : Link) (d : Dir) → PTree.force (decTSs-src l d tsDone1) ≡ react _ _
htsDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htsReqB1 : (l : Link) (d : Dir) (ar : _) → PTree.force (decTSs-src l d (tsReqB1 ar)) ≡ react _ _
htsReqB1 l d ar rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htsReqNB1 : (l : Link) (d : Dir) (ar : _) → PTree.force (decTSs-src l d (tsReqNB1 ar)) ≡ react _ _
htsReqNB1 l d ar rewrite ≟-yes-refl l | ≟-yes-refl d = refl
htsReqTxs1 : (l : Link) (d : Dir) (ids : _) → PTree.force (decTSs-src l d (tsReqTxs1 ids)) ≡ react _ _
htsReqTxs1 l d ids rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- TxSubmission server τ-inversion: only the loop re-entry sil carries a τ
decTSs-τ-inv : (l : Link) (d : Dir) (pos : TSsPos) {M : NetProc}
  → decTSs l d pos ─[ τ ]─► M
  → Σ[ st ∈ TS.TSState ] (pos ≡ tsSil st) × (M ≡ decTSs l d (tsHead st))
decTSs-τ-inv l d (tsHead TS.stInit)             step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d (tsHead TS.stInit)} refl (λ _ _ → refl) step)
decTSs-τ-inv l d (tsHead TS.stIdle)             step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d (tsHead TS.stIdle)} refl (λ _ _ → refl) step)
decTSs-τ-inv l d (tsHead TS.stTxIdsBlocking)    step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d (tsHead TS.stTxIdsBlocking)} refl (λ _ _ → refl) step)
decTSs-τ-inv l d (tsHead TS.stTxIdsNonBlocking) step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d (tsHead TS.stTxIdsNonBlocking)} refl (λ _ _ → refl) step)
decTSs-τ-inv l d (tsHead TS.stTxs)              step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d (tsHead TS.stTxs)} refl (λ _ _ → refl) step)
decTSs-τ-inv l d (tsHead TS.stDone)             step = ⊥-elim (TSNO.renameMap-ret-no-τ   {P = decTSs-src l d (tsHead TS.stDone)} refl step)
decTSs-τ-inv l d tsDone1                        step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d tsDone1} (htsDone1 l d) (λ _ _ → refl) step)
decTSs-τ-inv l d (tsReqB1 ar)  step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d (tsReqB1 ar)}  (htsReqB1 l d ar)  (λ _ _ → refl) step)
decTSs-τ-inv l d (tsReqNB1 ar) step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d (tsReqNB1 ar)} (htsReqNB1 l d ar) (λ _ _ → refl) step)
decTSs-τ-inv l d (tsReqTxs1 ids) step = ⊥-elim (TSNO.renameMap-react-no-τ {P = decTSs-src l d (tsReqTxs1 ids)} (htsReqTxs1 l d ids) (λ _ _ → refl) step)
decTSs-τ-inv l d (tsSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (TSNO.force-renameMap-sil
             {P = decTSs-src l d (tsSil st)} {P′ = decTSs-src l d (tsHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (TSNO.force-renameMap-sil
             {P = decTSs-src l d (tsSil st)} {P′ = decTSs-src l d (tsHead st)} refl)
...   | ()

-- source-force lemmas at the KA-client send leaves (unstick the api `l≟l|d≟d` guard)
hkcReq1 : (l : Link) (d : Dir) (c : Cookie) → PTree.force (decKAc-src l d (kcReq1 c)) ≡ react _ _
hkcReq1 l d c rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hkcDone1 : (l : Link) (d : Dir) → PTree.force (decKAc-src l d kcDone1) ≡ react _ _
hkcDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- KeepAlive client τ-inversion: only the loop re-entry sil carries a τ
-- (every head state is a react (client offers api / server offers wire) or a
-- ret (stDone) — no head τ; mirrors `decTSc-τ-inv`)
decKAc-τ-inv : (l : Link) (d : Dir) (pos : KAcPos) {M : NetProc}
  → decKAc l d pos ─[ τ ]─► M
  → Σ[ st ∈ KA.KAState ] (pos ≡ kcSil st) × (M ≡ decKAc l d (kcHead st))
decKAc-τ-inv l d (kcHead KA.stClient)     step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAc-src l d (kcHead KA.stClient)} refl (λ _ _ → refl) step)
decKAc-τ-inv l d (kcHead (KA.stServer c)) step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAc-src l d (kcHead (KA.stServer c))} refl (λ _ _ → refl) step)
decKAc-τ-inv l d (kcHead KA.stDone)       step = ⊥-elim (KANO.renameMap-ret-no-τ   {P = decKAc-src l d (kcHead KA.stDone)} refl step)
-- io-case error leaf: direct decode forces to react (errCookie offer), so no τ
decKAc-τ-inv l d (kcErr1 cq cr ne)        step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAc-src l d (kcErr1 cq cr ne)} refl (λ _ _ → refl) step)
-- io-case send leaves: force to react (sendKA offer), so no τ
decKAc-τ-inv l d (kcReq1 c)               step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAc-src l d (kcReq1 c)} (hkcReq1 l d c) (λ _ _ → refl) step)
decKAc-τ-inv l d kcDone1                  step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAc-src l d kcDone1} (hkcDone1 l d) (λ _ _ → refl) step)
-- io-case errCookie terminal: forces to `ret`, so no τ
decKAc-τ-inv l d kcTermE1                 step = ⊥-elim (KANO.renameMap-ret-no-τ   {P = decKAc-src l d kcTermE1} refl step)
decKAc-τ-inv l d (kcSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (KANO.force-renameMap-sil
             {P = decKAc-src l d (kcSil st)} {P′ = decKAc-src l d (kcHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (KANO.force-renameMap-sil
             {P = decKAc-src l d (kcSil st)} {P′ = decKAc-src l d (kcHead st)} refl)
...   | ()

-- source-force lemma at the KA-server receive leaf (unstick the receiveKA `l≟l|d≟d` guard)
hksRecv1 : (l : Link) (d : Dir) (c : Cookie) → PTree.force (decKAs-src l d (ksRecv1 c)) ≡ react _ _
hksRecv1 l d c rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- source-force lemma at the KA-server receive-done leaf (unstick the receiveKA `l≟l|d≟d` guard)
hksDdone1 : (l : Link) (d : Dir) → PTree.force (decKAs-src l d ksDdone1) ≡ react _ _
hksDdone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- KeepAlive server τ-inversion: only the loop re-entry sil carries a τ
decKAs-τ-inv : (l : Link) (d : Dir) (pos : KAsPos) {M : NetProc}
  → decKAs l d pos ─[ τ ]─► M
  → Σ[ st ∈ KA.KAState ] (pos ≡ ksSil st) × (M ≡ decKAs l d (ksHead st))
decKAs-τ-inv l d (ksHead KA.stClient)     step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAs-src l d (ksHead KA.stClient)} refl (λ _ _ → refl) step)
decKAs-τ-inv l d (ksHead (KA.stServer c)) step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAs-src l d (ksHead (KA.stServer c))} refl (λ _ _ → refl) step)
decKAs-τ-inv l d (ksRecv1 c)              step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAs-src l d (ksRecv1 c)} (hksRecv1 l d c) (λ _ _ → refl) step)
decKAs-τ-inv l d ksDdone1                 step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAs-src l d ksDdone1} (hksDdone1 l d) (λ _ _ → refl) step)
decKAs-τ-inv l d (ksHead KA.stDone)       step = ⊥-elim (KANO.renameMap-ret-no-τ   {P = decKAs-src l d (ksHead KA.stDone)} refl step)
decKAs-τ-inv l d (ksSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (KANO.force-renameMap-sil
             {P = decKAs-src l d (ksSil st)} {P′ = decKAs-src l d (ksHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (KANO.force-renameMap-sil
             {P = decKAs-src l d (ksSil st)} {P′ = decKAs-src l d (ksHead st)} refl)
...   | ()

-- source-force lemmas at the LN-client receive leaves (unstick the receiveLN `l≟l|d≟d` guard)
hlncRann1 : (l : Link) (d : Dir) (h : Header) → PTree.force (decLNc-src l d (lncRann1 h)) ≡ react _ _
hlncRann1 l d h rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlncRoff1 : (l : Link) (d : Dir) (q : _) → PTree.force (decLNc-src l d (lncRoff1 q)) ≡ react _ _
hlncRoff1 l d q rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlncRtxs1 : (l : Link) (d : Dir) (q : _) → PTree.force (decLNc-src l d (lncRtxs1 q)) ≡ react _ _
hlncRtxs1 l d q rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlncRvot1 : (l : Link) (d : Dir) (vs : List Vote) → PTree.force (decLNc-src l d (lncRvot1 vs)) ≡ react _ _
hlncRvot1 l d vs rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlncReq1 : (l : Link) (d : Dir) → PTree.force (decLNc-src l d lncReq1) ≡ react _ _
hlncReq1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlncDone1 : (l : Link) (d : Dir) → PTree.force (decLNc-src l d lncDone1) ≡ react _ _
hlncDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- LeiosNotify client τ-inversion: only the loop re-entry sil carries a τ
-- (stIdle/stBusy heads are react (offer api/wire), stDone is ret; recv leaves are react (offer api); mirrors KA)
decLNc-τ-inv : (l : Link) (d : Dir) (pos : LNcPos) {M : NetProc}
  → decLNc l d pos ─[ τ ]─► M
  → Σ[ st ∈ LNp.LNState ] (pos ≡ lncSil st) × (M ≡ decLNc l d (lncHead st))
decLNc-τ-inv l d (lncHead LNp.stIdle) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d (lncHead LNp.stIdle)} refl (λ _ _ → refl) step)
decLNc-τ-inv l d (lncHead LNp.stBusy) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d (lncHead LNp.stBusy)} refl (λ _ _ → refl) step)
decLNc-τ-inv l d (lncHead LNp.stDone) step = ⊥-elim (LNNO.renameMap-ret-no-τ   {P = decLNc-src l d (lncHead LNp.stDone)} refl step)
decLNc-τ-inv l d (lncRann1 h)  step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d (lncRann1 h)}  (hlncRann1 l d h)  (λ _ _ → refl) step)
decLNc-τ-inv l d (lncRoff1 q)  step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d (lncRoff1 q)}  (hlncRoff1 l d q)  (λ _ _ → refl) step)
decLNc-τ-inv l d (lncRtxs1 q)  step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d (lncRtxs1 q)}  (hlncRtxs1 l d q)  (λ _ _ → refl) step)
decLNc-τ-inv l d (lncRvot1 vs) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d (lncRvot1 vs)} (hlncRvot1 l d vs) (λ _ _ → refl) step)
decLNc-τ-inv l d lncReq1  step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d lncReq1}  (hlncReq1 l d)  (λ _ _ → refl) step)
decLNc-τ-inv l d lncDone1 step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d lncDone1} (hlncDone1 l d) (λ _ _ → refl) step)
decLNc-τ-inv l d (lncSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (LNNO.force-renameMap-sil
             {P = decLNc-src l d (lncSil st)} {P′ = decLNc-src l d (lncHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (LNNO.force-renameMap-sil
             {P = decLNc-src l d (lncSil st)} {P′ = decLNc-src l d (lncHead st)} refl)
...   | ()

-- LeiosNotify server τ-inversion: only the loop re-entry sil carries a τ
-- source-force lemma at the LN-server receive-done leaf (unstick the receiveLN `l≟l|d≟d` guard)
hlnsDone1 : (l : Link) (d : Dir) → PTree.force (decLNs-src l d lnsDone1) ≡ react _ _
hlnsDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlnsWann1 : (l : Link) (d : Dir) (h : Header) → PTree.force (decLNs-src l d (lnsWann1 h)) ≡ react _ _
hlnsWann1 l d h rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlnsWoff1 : (l : Link) (d : Dir) (q : _) → PTree.force (decLNs-src l d (lnsWoff1 q)) ≡ react _ _
hlnsWoff1 l d q rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlnsWtxs1 : (l : Link) (d : Dir) (q : _) → PTree.force (decLNs-src l d (lnsWtxs1 q)) ≡ react _ _
hlnsWtxs1 l d q rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlnsWvot1 : (l : Link) (d : Dir) (vs : List Vote) → PTree.force (decLNs-src l d (lnsWvot1 vs)) ≡ react _ _
hlnsWvot1 l d vs rewrite ≟-yes-refl l | ≟-yes-refl d = refl

decLNs-τ-inv : (l : Link) (d : Dir) (pos : LNsPos) {M : NetProc}
  → decLNs l d pos ─[ τ ]─► M
  → Σ[ st ∈ LNp.LNState ] (pos ≡ lnsSil st) × (M ≡ decLNs l d (lnsHead st))
decLNs-τ-inv l d (lnsHead LNp.stIdle) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d (lnsHead LNp.stIdle)} refl (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsHead LNp.stBusy) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d (lnsHead LNp.stBusy)} refl (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsHead LNp.stDone) step = ⊥-elim (LNNO.renameMap-ret-no-τ   {P = decLNs-src l d (lnsHead LNp.stDone)} refl step)
decLNs-τ-inv l d lnsDone1             step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d lnsDone1} (hlnsDone1 l d) (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsWann1 h)  step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d (lnsWann1 h)}  (hlnsWann1 l d h)  (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsWoff1 q)  step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d (lnsWoff1 q)}  (hlnsWoff1 l d q)  (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsWtxs1 q)  step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d (lnsWtxs1 q)}  (hlnsWtxs1 l d q)  (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsWvot1 vs) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d (lnsWvot1 vs)} (hlnsWvot1 l d vs) (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (LNNO.force-renameMap-sil
             {P = decLNs-src l d (lnsSil st)} {P′ = decLNs-src l d (lnsHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (LNNO.force-renameMap-sil
             {P = decLNs-src l d (lnsSil st)} {P′ = decLNs-src l d (lnsHead st)} refl)
...   | ()

-- LeiosFetch client τ-inversion: only the loop re-entry sil carries a τ
-- (the five busy heads are react (offer api/wire), stDone is ret; mirrors LN).
-- DORMANT (step-4 leaf lemma): not yet routed by `bundle-τ-inv` (LF still a
-- frozen constant in `bundleG`); lands green ahead of the LF-tracking wiring.
-- source-force lemmas at the LF-client receive leaves (unstick the receiveLF `l≟l|d≟d` guard)
hlfcRblk1 : (l : Link) (d : Dir) (b : _) → PTree.force (decLFc-src l d (lfcRblk1 b)) ≡ react _ _
hlfcRblk1 l d b rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcRbtx1 : (l : Link) (d : Dir) (ts : _) → PTree.force (decLFc-src l d (lfcRbtx1 ts)) ≡ react _ _
hlfcRbtx1 l d ts rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcRvot1 : (l : Link) (d : Dir) (vs : _) → PTree.force (decLFc-src l d (lfcRvot1 vs)) ≡ react _ _
hlfcRvot1 l d vs rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcRnext1 : (l : Link) (d : Dir) (b : _) (ts : _) → PTree.force (decLFc-src l d (lfcRnext1 b ts)) ≡ react _ _
hlfcRnext1 l d b ts rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcRlast1 : (l : Link) (d : Dir) (b : _) (ts : _) → PTree.force (decLFc-src l d (lfcRlast1 b ts)) ≡ react _ _
hlfcRlast1 l d b ts rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcWblk1 : (l : Link) (d : Dir) (pt : _) → PTree.force (decLFc-src l d (lfcWblk1 pt)) ≡ react _ _
hlfcWblk1 l d pt rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcWtxs1 : (l : Link) (d : Dir) (pb : _) → PTree.force (decLFc-src l d (lfcWtxs1 pb)) ≡ react _ _
hlfcWtxs1 l d pb rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcWvot1 : (l : Link) (d : Dir) (vs : _) → PTree.force (decLFc-src l d (lfcWvot1 vs)) ≡ react _ _
hlfcWvot1 l d vs rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcWrng1 : (l : Link) (d : Dir) (r : _) → PTree.force (decLFc-src l d (lfcWrng1 r)) ≡ react _ _
hlfcWrng1 l d r rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfcDone1 : (l : Link) (d : Dir) → PTree.force (decLFc-src l d lfcDone1) ≡ react _ _
hlfcDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl

decLFc-τ-inv : (l : Link) (d : Dir) (pos : LFcPos) {M : NetProc}
  → decLFc l d pos ─[ τ ]─► M
  → Σ[ st ∈ LFp.LFState ] (pos ≡ lfcSil st) × (M ≡ decLFc l d (lfcHead st))
decLFc-τ-inv l d (lfcHead LFp.stIdle) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcHead LFp.stIdle)} refl (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcHead LFp.stBlock) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcHead LFp.stBlock)} refl (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcHead LFp.stBlockTxs) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcHead LFp.stBlockTxs)} refl (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcHead LFp.stVotes) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcHead LFp.stVotes)} refl (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcHead LFp.stBlockRange) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcHead LFp.stBlockRange)} refl (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcHead LFp.stDone) step = ⊥-elim (LFNO.renameMap-ret-no-τ   {P = decLFc-src l d (lfcHead LFp.stDone)} refl step)
decLFc-τ-inv l d (lfcRblk1 b)     step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcRblk1 b)}     (hlfcRblk1 l d b)     (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcRbtx1 ts)    step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcRbtx1 ts)}    (hlfcRbtx1 l d ts)    (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcRvot1 vs)    step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcRvot1 vs)}    (hlfcRvot1 l d vs)    (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcRnext1 b ts) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcRnext1 b ts)} (hlfcRnext1 l d b ts) (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcRlast1 b ts) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcRlast1 b ts)} (hlfcRlast1 l d b ts) (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcWblk1 pt) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcWblk1 pt)} (hlfcWblk1 l d pt) (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcWtxs1 pb) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcWtxs1 pb)} (hlfcWtxs1 l d pb) (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcWvot1 vs) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcWvot1 vs)} (hlfcWvot1 l d vs) (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcWrng1 r)  step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d (lfcWrng1 r)}  (hlfcWrng1 l d r)  (λ _ _ → refl) step)
decLFc-τ-inv l d lfcDone1      step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFc-src l d lfcDone1}      (hlfcDone1 l d)    (λ _ _ → refl) step)
decLFc-τ-inv l d (lfcSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (LFNO.force-renameMap-sil
             {P = decLFc-src l d (lfcSil st)} {P′ = decLFc-src l d (lfcHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (LFNO.force-renameMap-sil
             {P = decLFc-src l d (lfcSil st)} {P′ = decLFc-src l d (lfcHead st)} refl)
...   | ()

-- LeiosFetch server τ-inversion: only the loop re-entry sil carries a τ (DORMANT)
-- source-force lemma at the LF-server receive-done leaf (unstick the receiveLF `l≟l|d≟d` guard)
hlfsDone1 : (l : Link) (d : Dir) → PTree.force (decLFs-src l d lfsDone1) ≡ react _ _
hlfsDone1 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfsWblk1 : (l : Link) (d : Dir) (b : _) → PTree.force (decLFs-src l d (lfsWblk1 b)) ≡ react _ _
hlfsWblk1 l d b rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfsWtxs1 : (l : Link) (d : Dir) (ts : _) → PTree.force (decLFs-src l d (lfsWtxs1 ts)) ≡ react _ _
hlfsWtxs1 l d ts rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfsWvot1 : (l : Link) (d : Dir) (vs : _) → PTree.force (decLFs-src l d (lfsWvot1 vs)) ≡ react _ _
hlfsWvot1 l d vs rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfsWnext1 : (l : Link) (d : Dir) (bt : _) → PTree.force (decLFs-src l d (lfsWnext1 bt)) ≡ react _ _
hlfsWnext1 l d bt rewrite ≟-yes-refl l | ≟-yes-refl d = refl
hlfsWlast1 : (l : Link) (d : Dir) (bt : _) → PTree.force (decLFs-src l d (lfsWlast1 bt)) ≡ react _ _
hlfsWlast1 l d bt rewrite ≟-yes-refl l | ≟-yes-refl d = refl

decLFs-τ-inv : (l : Link) (d : Dir) (pos : LFsPos) {M : NetProc}
  → decLFs l d pos ─[ τ ]─► M
  → Σ[ st ∈ LFp.LFState ] (pos ≡ lfsSil st) × (M ≡ decLFs l d (lfsHead st))
decLFs-τ-inv l d (lfsHead LFp.stIdle) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsHead LFp.stIdle)} refl (λ _ _ → refl) step)
decLFs-τ-inv l d lfsDone1             step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d lfsDone1} (hlfsDone1 l d) (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsHead LFp.stBlock) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsHead LFp.stBlock)} refl (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsHead LFp.stBlockTxs) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsHead LFp.stBlockTxs)} refl (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsHead LFp.stVotes) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsHead LFp.stVotes)} refl (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsHead LFp.stBlockRange) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsHead LFp.stBlockRange)} refl (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsHead LFp.stDone) step = ⊥-elim (LFNO.renameMap-ret-no-τ   {P = decLFs-src l d (lfsHead LFp.stDone)} refl step)
decLFs-τ-inv l d (lfsWblk1 b)  step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsWblk1 b)}  (hlfsWblk1 l d b)  (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsWtxs1 ts) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsWtxs1 ts)} (hlfsWtxs1 l d ts) (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsWvot1 vs) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsWvot1 vs)} (hlfsWvot1 l d vs) (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsWnext1 bt) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsWnext1 bt)} (hlfsWnext1 l d bt) (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsWlast1 bt) step = ⊥-elim (LFNO.renameMap-react-no-τ {P = decLFs-src l d (lfsWlast1 bt)} (hlfsWlast1 l d bt) (λ _ _ → refl) step)
decLFs-τ-inv l d (lfsSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (LFNO.force-renameMap-sil
             {P = decLFs-src l d (lfsSil st)} {P′ = decLFs-src l d (lfsHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (LFNO.force-renameMap-sil
             {P = decLFs-src l d (lfsSil st)} {P′ = decLFs-src l d (lfsHead st)} refl)
...   | ()


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

module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle where

------------------------------------------------------------------------
-- The shared alphabet, the whole-system process type, and the model.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Net; Net-≟; break
  ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack
  ; done; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF )
open import CSP.Examples.Cardano_network.Data p using ( Payload; DecEq-Payload; Header; header )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES; ιNet; ιNet⁻¹; ιNet-linv )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig )

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
        ; coarsenCSc; coarsenCSs; coarsenBFc; coarsenBFs; coarsenTSc; coarsenTSs; coarsenKAc; coarsenKAs
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
        ; TScPos; tcHead; tcSil; TSsPos; tsHead; tsSil
        ; KAcPos; kcHead; kcSil; KAsPos; ksHead; ksSil
        ; LNcPos; lncHead; lncSil; LNsPos; lnsHead; lnsSil
        ; LFcPos; lfcHead; lfcSil; LFsPos; lfsHead; lfsSil
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
decTSc-τ-inv l d (tcSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (TSNO.force-renameMap-sil
             {P = decTSc-src l d (tcSil st)} {P′ = decTSc-src l d (tcHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (TSNO.force-renameMap-sil
             {P = decTSc-src l d (tcSil st)} {P′ = decTSc-src l d (tcHead st)} refl)
...   | ()

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
decTSs-τ-inv l d (tsSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (TSNO.force-renameMap-sil
             {P = decTSs-src l d (tsSil st)} {P′ = decTSs-src l d (tsHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (TSNO.force-renameMap-sil
             {P = decTSs-src l d (tsSil st)} {P′ = decTSs-src l d (tsHead st)} refl)
...   | ()

-- KeepAlive client τ-inversion: only the loop re-entry sil carries a τ
-- (every head state is a react (client offers api / server offers wire) or a
-- ret (stDone) — no head τ; mirrors `decTSc-τ-inv`)
decKAc-τ-inv : (l : Link) (d : Dir) (pos : KAcPos) {M : NetProc}
  → decKAc l d pos ─[ τ ]─► M
  → Σ[ st ∈ KA.KAState ] (pos ≡ kcSil st) × (M ≡ decKAc l d (kcHead st))
decKAc-τ-inv l d (kcHead KA.stClient)     step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAc-src l d (kcHead KA.stClient)} refl (λ _ _ → refl) step)
decKAc-τ-inv l d (kcHead (KA.stServer c)) step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAc-src l d (kcHead (KA.stServer c))} refl (λ _ _ → refl) step)
decKAc-τ-inv l d (kcHead KA.stDone)       step = ⊥-elim (KANO.renameMap-ret-no-τ   {P = decKAc-src l d (kcHead KA.stDone)} refl step)
decKAc-τ-inv l d (kcSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (KANO.force-renameMap-sil
             {P = decKAc-src l d (kcSil st)} {P′ = decKAc-src l d (kcHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (KANO.force-renameMap-sil
             {P = decKAc-src l d (kcSil st)} {P′ = decKAc-src l d (kcHead st)} refl)
...   | ()

-- KeepAlive server τ-inversion: only the loop re-entry sil carries a τ
decKAs-τ-inv : (l : Link) (d : Dir) (pos : KAsPos) {M : NetProc}
  → decKAs l d pos ─[ τ ]─► M
  → Σ[ st ∈ KA.KAState ] (pos ≡ ksSil st) × (M ≡ decKAs l d (ksHead st))
decKAs-τ-inv l d (ksHead KA.stClient)     step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAs-src l d (ksHead KA.stClient)} refl (λ _ _ → refl) step)
decKAs-τ-inv l d (ksHead (KA.stServer c)) step = ⊥-elim (KANO.renameMap-react-no-τ {P = decKAs-src l d (ksHead (KA.stServer c))} refl (λ _ _ → refl) step)
decKAs-τ-inv l d (ksHead KA.stDone)       step = ⊥-elim (KANO.renameMap-ret-no-τ   {P = decKAs-src l d (ksHead KA.stDone)} refl step)
decKAs-τ-inv l d (ksSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (KANO.force-renameMap-sil
             {P = decKAs-src l d (ksSil st)} {P′ = decKAs-src l d (ksHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (KANO.force-renameMap-sil
             {P = decKAs-src l d (ksSil st)} {P′ = decKAs-src l d (ksHead st)} refl)
...   | ()

-- LeiosNotify client τ-inversion: only the loop re-entry sil carries a τ
-- (stIdle/stBusy heads are react (offer api/wire), stDone is ret; mirrors KA)
decLNc-τ-inv : (l : Link) (d : Dir) (pos : LNcPos) {M : NetProc}
  → decLNc l d pos ─[ τ ]─► M
  → Σ[ st ∈ LNp.LNState ] (pos ≡ lncSil st) × (M ≡ decLNc l d (lncHead st))
decLNc-τ-inv l d (lncHead LNp.stIdle) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d (lncHead LNp.stIdle)} refl (λ _ _ → refl) step)
decLNc-τ-inv l d (lncHead LNp.stBusy) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNc-src l d (lncHead LNp.stBusy)} refl (λ _ _ → refl) step)
decLNc-τ-inv l d (lncHead LNp.stDone) step = ⊥-elim (LNNO.renameMap-ret-no-τ   {P = decLNc-src l d (lncHead LNp.stDone)} refl step)
decLNc-τ-inv l d (lncSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (LNNO.force-renameMap-sil
             {P = decLNc-src l d (lncSil st)} {P′ = decLNc-src l d (lncHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (LNNO.force-renameMap-sil
             {P = decLNc-src l d (lncSil st)} {P′ = decLNc-src l d (lncHead st)} refl)
...   | ()

-- LeiosNotify server τ-inversion: only the loop re-entry sil carries a τ
decLNs-τ-inv : (l : Link) (d : Dir) (pos : LNsPos) {M : NetProc}
  → decLNs l d pos ─[ τ ]─► M
  → Σ[ st ∈ LNp.LNState ] (pos ≡ lnsSil st) × (M ≡ decLNs l d (lnsHead st))
decLNs-τ-inv l d (lnsHead LNp.stIdle) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d (lnsHead LNp.stIdle)} refl (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsHead LNp.stBusy) step = ⊥-elim (LNNO.renameMap-react-no-τ {P = decLNs-src l d (lnsHead LNp.stBusy)} refl (λ _ _ → refl) step)
decLNs-τ-inv l d (lnsHead LNp.stDone) step = ⊥-elim (LNNO.renameMap-ret-no-τ   {P = decLNs-src l d (lnsHead LNp.stDone)} refl step)
decLNs-τ-inv l d (lnsSil st) step with τ-inv step
... | inj₁ sileq = st , refl ,
      sym (sil-injective (trans (sym (LNNO.force-renameMap-sil
             {P = decLNs-src l d (lnsSil st)} {P′ = decLNs-src l d (lnsHead st)} refl)) sileq))
... | inj₂ (v′ , τc′ , i , a , feq′ , beq)
      with trans (sym feq′) (LNNO.force-renameMap-sil
             {P = decLNs-src l d (lnsSil st)} {P′ = decLNs-src l d (lnsHead st)} refl)
...   | ()

------------------------------------------------------------------------
-- STAGE-2 NODE-τ BACKBONE — the 12-peer bundle τ-inversion.  A τ of a
-- `bundleG l cl sv csc css bfc bfs ip` interleave is exactly ONE of the SIX
-- moving peers' loop re-entry sil (`…Sil st → …Head st`): the four DRIVEN
-- CS/BF peers OR the TxSubmission client/server (now tracked in `ip`); the six
-- frozen KA/LN/LF peers are τ-free (refuted).  Peels the 11 nested `⦀` with
-- `Par-τ-elim ∅ESa`, refuting the frozen peers and inverting the moving one.
------------------------------------------------------------------------

-- which moving peer of a bundle carried the τ (+ its loop state + target)
data BundleτR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     (Bd′ : NetProc) : Set₁ where
  bcsc : (st : CS.CSState) → csc ≡ csSil st
       → Bd′ ≡ bundleG l cl sv (csHead st) css bfc bfs ip → BundleτR l cl sv csc css bfc bfs ip Bd′
  bcss : (st : CS.CSState) → css ≡ ssSil st
       → Bd′ ≡ bundleG l cl sv csc (ssHead st) bfc bfs ip → BundleτR l cl sv csc css bfc bfs ip Bd′
  bbfc : (st : BF.BFState) → bfc ≡ bcSil st
       → Bd′ ≡ bundleG l cl sv csc css (bcHead st) bfs ip → BundleτR l cl sv csc css bfc bfs ip Bd′
  bbfs : (st : BF.BFState) → bfs ≡ bsSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc (bsHead st) ip → BundleτR l cl sv csc css bfc bfs ip Bd′
  btsc : (st : TS.TSState) → tsc ip ≡ tcSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tcHead st) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  btss : (st : TS.TSState) → tss ip ≡ tsSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tsHead st) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  bkac : (st : KA.KAState) → kac ip ≡ kcSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kcHead st) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  bkas : (st : KA.KAState) → kas ip ≡ ksSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (ksHead st) (lnc ip) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  blnc : (st : LNp.LNState) → lnc ip ≡ lncSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lncHead st) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  blns : (st : LNp.LNState) → lns ip ≡ lnsSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lnsHead st) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′

-- finisher for a KA-client peel (peer 1): M is the KA client at `kcHead st`
finishKAc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ M : NetProc}
  → Bd′ ≡ (M ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))))))))
  → (Σ[ st ∈ KA.KAState ] (kac ip ≡ kcSil st) × (M ≡ decKAc l cl (kcHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishKAc l cl sv csc css bfc bfs ip e1 (st , poseq , refl) = bkac st poseq e1

-- finisher for a KA-server peel (peer 2): M is the KA server at `ksHead st`
finishKAs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1)
  → R1 ≡ (M ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (LFclientA l cl ⦀ LFserverA l sv))))))))))
  → (Σ[ st ∈ KA.KAState ] (kas ip ≡ ksSil st) × (M ≡ decKAs l sv (ksHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishKAs l cl sv csc css bfc bfs ip e1 e2 (st , poseq , refl) =
  bkas st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_) e2))

-- finisher for a CS-client peel: fold the three prefix eqs + the CS-client
-- inversion into a `bcsc` (the `refl` match on the target eq fixes the peer)
finishCSc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (M ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))))))
  → (Σ[ st ∈ CS.CSState ] (csc ≡ csSil st) × (M ≡ decCSc l cl (csHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishCSc l cl sv csc css bfc bfs ip e1 e2 e3 (st , poseq , refl) =
  bcsc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_) e3))))

-- finisher for a CS-server peel
finishCSs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3)
  → R3 ≡ (M ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (LFclientA l cl ⦀ LFserverA l sv))))))))
  → (Σ[ st ∈ CS.CSState ] (css ≡ ssSil st) × (M ≡ decCSs l sv (ssHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishCSs l cl sv csc css bfc bfs ip e1 e2 e3 e4 (st , poseq , refl) =
  bcss st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_) e4))))))

-- finisher for a BF-client peel
finishBFc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (M ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))))
  → (Σ[ st ∈ BF.BFState ] (bfc ≡ bcSil st) × (M ≡ decBFc l cl (bcHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishBFc l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 (st , poseq , refl) =
  bbfc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_)
                (trans e4 (cong (decCSs l sv css ⦀_) e5))))))))

-- finisher for a BF-server peel
finishBFs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5)
  → R5 ≡ (M ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (LFclientA l cl ⦀ LFserverA l sv))))))
  → (Σ[ st ∈ BF.BFState ] (bfs ≡ bsSil st) × (M ≡ decBFs l sv (bsHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishBFs l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 (st , poseq , refl) =
  bbfs st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_)
                (trans e4 (cong (decCSs l sv css ⦀_)
                (trans e5 (cong (decBFc l cl bfc ⦀_) e6))))))))))

-- finisher for a TS-client peel (peer 7): M is the TS client at `tcHead st`
finishTSc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (M ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))
  → (Σ[ st ∈ TS.TSState ] (tsc ip ≡ tcSil st) × (M ≡ decTSc l cl (tcHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishTSc l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 (st , poseq , refl) =
  btsc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_)
                (trans e4 (cong (decCSs l sv css ⦀_)
                (trans e5 (cong (decBFc l cl bfc ⦀_)
                (trans e6 (cong (decBFs l sv bfs ⦀_) e7))))))))))))

-- finisher for a TS-server peel (peer 8): M is the TS server at `tsHead st`
finishTSs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 R7 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (decTSc l cl (tsc ip) ⦀ R7)
  → R7 ≡ (M ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (LFclientA l cl ⦀ LFserverA l sv))))
  → (Σ[ st ∈ TS.TSState ] (tss ip ≡ tsSil st) × (M ≡ decTSs l sv (tsHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishTSs l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 e8 (st , poseq , refl) =
  btss st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_)
                (trans e4 (cong (decCSs l sv css ⦀_)
                (trans e5 (cong (decBFc l cl bfc ⦀_)
                (trans e6 (cong (decBFs l sv bfs ⦀_)
                (trans e7 (cong (decTSc l cl (tsc ip) ⦀_) e8))))))))))))))

-- finisher for a LeiosNotify-client peel (peer 9): M is the LN client at `lncHead st`
finishLNc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 R7 R8 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (decTSc l cl (tsc ip) ⦀ R7) → R7 ≡ (decTSs l sv (tss ip) ⦀ R8)
  → R8 ≡ (M ⦀ (decLNs l sv (lns ip) ⦀ (LFclientA l cl ⦀ LFserverA l sv)))
  → (Σ[ st ∈ LNp.LNState ] (lnc ip ≡ lncSil st) × (M ≡ decLNc l cl (lncHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishLNc l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 e8 e9 (st , poseq , refl) =
  blnc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_) (trans e2 (cong (decKAs l sv (kas ip) ⦀_) (trans e3 (cong (decCSc l cl csc ⦀_) (trans e4 (cong (decCSs l sv css ⦀_) (trans e5 (cong (decBFc l cl bfc ⦀_) (trans e6 (cong (decBFs l sv bfs ⦀_) (trans e7 (cong (decTSc l cl (tsc ip) ⦀_) (trans e8 (cong (decTSs l sv (tss ip) ⦀_) e9))))))))))))))))

-- finisher for a LeiosNotify-server peel (peer 10): M is the LN server at `lnsHead st`
finishLNs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 R7 R8 R9 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (decTSc l cl (tsc ip) ⦀ R7) → R7 ≡ (decTSs l sv (tss ip) ⦀ R8)
  → R8 ≡ (decLNc l cl (lnc ip) ⦀ R9)
  → R9 ≡ (M ⦀ (LFclientA l cl ⦀ LFserverA l sv))
  → (Σ[ st ∈ LNp.LNState ] (lns ip ≡ lnsSil st) × (M ≡ decLNs l sv (lnsHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishLNs l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 (st , poseq , refl) =
  blns st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_) (trans e2 (cong (decKAs l sv (kas ip) ⦀_) (trans e3 (cong (decCSc l cl csc ⦀_) (trans e4 (cong (decCSs l sv css ⦀_) (trans e5 (cong (decBFc l cl bfc ⦀_) (trans e6 (cong (decBFs l sv bfs ⦀_) (trans e7 (cong (decTSc l cl (tsc ip) ⦀_) (trans e8 (cong (decTSs l sv (tss ip) ⦀_) (trans e9 (cong (decLNc l cl (lnc ip) ⦀_) e10))))))))))))))))))

-- 12-peer bundle τ-inversion (TOTAL): peel each `⦀`, refute the six frozen
-- KA/LN/LF peers, invert the six moving CS/BF/TS peers
bundle-τ-inv : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos) {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ τ ]─► Bd′
  → BundleτR l cl sv csc css bfc bfs ip Bd′
bundle-τ-inv l cl sv csc css bfc bfs ip step
  with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.τL _ cstep eq1 = finishKAc l cl sv csc css bfc bfs ip eq1 (decKAc-τ-inv l cl (kac ip) cstep)
... | PEA.τR _ q1 eq1
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.τL _ cstep eq2 = finishKAs l cl sv csc css bfc bfs ip eq1 eq2 (decKAs-τ-inv l sv (kas ip) cstep)
...   | PEA.τR _ q2 eq2
      with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.τL _ cstep eq3 = finishCSc l cl sv csc css bfc bfs ip eq1 eq2 eq3 (decCSc-τ-inv l cl csc cstep)
...     | PEA.τR _ q3 eq3
        with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.τL _ cstep eq4 = finishCSs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 (decCSs-τ-inv l sv css cstep)
...       | PEA.τR _ q4 eq4
          with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.τL _ cstep eq5 = finishBFc l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 (decBFc-τ-inv l cl bfc cstep)
...         | PEA.τR _ q5 eq5
            with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.τL _ cstep eq6 = finishBFs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 (decBFs-τ-inv l sv bfs cstep)
...           | PEA.τR _ q6 eq6
              with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.τL _ cstep eq7 = finishTSc l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 (decTSc-τ-inv l cl (tsc ip) cstep)
...             | PEA.τR _ q7 eq7
                with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.τL _ cstep eq8 = finishTSs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 (decTSs-τ-inv l sv (tss ip) cstep)
...               | PEA.τR _ q8 eq8
                  with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.τL _ cstep eq9 = finishLNc l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 (decLNc-τ-inv l cl (lnc ip) cstep)
...                 | PEA.τR _ q9 eq9
                    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.τL _ cstep eq10 = finishLNs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 (decLNs-τ-inv l sv (lns ip) cstep)
...                   | PEA.τR _ q10 eq10
                      with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (LFclientA l cl) (LFserverA l sv) q10
...                     | PEA.τL _ ps _ = ⊥-elim (LFclientA-no-τ l cl ps)
...                     | PEA.τR _ qs _ = ⊥-elim (LFserverA-no-τ l sv qs)


------------------------------------------------------------------------
-- STAGE-2 NODE τ-INVERSIONS.  A node `(bundle₁ ⦀ bundle₂) ∥⇘ apiES ⇙ driver`
-- τ is a BUNDLE τ (peel via `reflect-node-τ` → `Par-τ-elim ∅ESa` → the two
-- links → `bundle-τ-inv`); the DRIVER τ is refuted (produce/consume/relay are
-- τ-free prefix chains).  Each `finishX-{L,R}` folds the per-link `BundleτR`
-- into the node-state successor `nX′` (one peer advanced `…Sil st → …Head st`),
-- `refl`-defeq to `decNodeX` (`bundleA ≡ bundleG lo hi`).  `rewrite` on the peel
-- equalities collapses the target; the driven-peer target eq is matched `refl`.
------------------------------------------------------------------------

-- fold a link-AB bundle inversion into node A's successor
finishA-L : (na : SN.NodeStateA) {A′ Bd′ M1 : NetProc}
  → A′ ≡ (Bd′ ∥⇘ apiES ⇙ (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)))
  → Bd′ ≡ (M1 ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
  → BundleτR linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) M1
  → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′)
finishA-L na eq eqL (bcsc st _ refl) rewrite eqL =
  SN.mkNodeA (csHead st) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bcss st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (ssHead st) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bbfc st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (bcHead st) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bbfs st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (bsHead st) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (btsc st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tcHead st) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (btss st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tsHead st) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bkac st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kcHead st) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bkas st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (ksHead st) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (blnc st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lncHead st) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (blns st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lnsHead st) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq

-- fold a link-AC bundle inversion into node A's successor
finishA-R : (na : SN.NodeStateA) {A′ Bd′ M2 : NetProc}
  → A′ ≡ (Bd′ ∥⇘ apiES ⇙ (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)))
  → Bd′ ≡ (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ M2)
  → BundleτR linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) M2
  → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′)
finishA-R na eq eqR (bcsc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (csHead st) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-R na eq eqR (bcss st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (ssHead st) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-R na eq eqR (bbfc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (bcHead st) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-R na eq eqR (bbfs st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (bsHead st) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-R na eq eqR (btsc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tcHead st) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (btss st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tsHead st) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (bkac st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kcHead st) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (bkas st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (ksHead st) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (blnc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lncHead st) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (blns st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lnsHead st) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq

-- NODE-A τ-inversion
nodeA-τ-inv : (na : SN.NodeStateA) {A′ : NetProc}
  → decNodeA na ─[ τ ]─► A′ → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′)
nodeA-τ-inv na step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na))
           (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) ds
...   | PEA.τL _ ps _ = ⊥-elim (decProd-no-τ linkAB hi b1 (SN.NodeStateA.prod-AB na) ps)
...   | PEA.τR _ qs _ = ⊥-elim (decProd-no-τ linkAC hi b1 (SN.NodeStateA.prod-AC na) qs)
nodeA-τ-inv na step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _ bs
...   | PEA.τL _ s1 eqL = finishA-L na eq eqL
          (bundle-τ-inv linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) s1)
...   | PEA.τR _ s2 eqR = finishA-R na eq eqR
          (bundle-τ-inv linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) s2)

-- fold a link-AB bundle inversion into node B's successor
finishB-L : (nb : SN.NodeStateB) {B′ Bd′ M1 : NetProc}
  → B′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
  → Bd′ ≡ (M1 ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
  → BundleτR linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) M1
  → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′)
finishB-L nb eq eqL (bcsc st _ refl) rewrite eqL =
  SN.mkNodeB (csHead st) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bcss st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (ssHead st) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bbfc st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (bcHead st) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bbfs st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (bsHead st)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (btsc st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tcHead st) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (btss st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tsHead st) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bkac st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kcHead st) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bkas st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (ksHead st) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (blnc st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lncHead st) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (blns st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lnsHead st) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq

-- fold a link-BD bundle inversion into node B's successor
finishB-R : (nb : SN.NodeStateB) {B′ Bd′ M2 : NetProc}
  → B′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
  → Bd′ ≡ (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ M2)
  → BundleτR linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) M2
  → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′)
finishB-R nb eq eqR (bcsc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (csHead st) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-R nb eq eqR (bcss st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (ssHead st) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-R nb eq eqR (bbfc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (bcHead st) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-R nb eq eqR (bbfs st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (bsHead st) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-R nb eq eqR (btsc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tcHead st) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (btss st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tsHead st) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (bkac st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kcHead st) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (bkas st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (ksHead st) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (blnc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lncHead st) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (blns st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lnsHead st) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq

-- NODE-B τ-inversion
nodeB-τ-inv : (nb : SN.NodeStateB) {B′ : NetProc}
  → decNodeB nb ─[ τ ]─► B′ → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′)
nodeB-τ-inv nb step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _ = ⊥-elim (decCP-no-τ linkAB linkBD (SN.NodeStateB.cp-B nb) ds)
nodeB-τ-inv nb step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)) _ bs
...   | PEA.τL _ s1 eqL = finishB-L nb eq eqL
          (bundle-τ-inv linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) s1)
...   | PEA.τR _ s2 eqR = finishB-R nb eq eqR
          (bundle-τ-inv linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) s2)

-- fold a link-AC bundle inversion into node C's successor
finishC-L : (nc : SN.NodeStateC) {C′ Bd′ M1 : NetProc}
  → C′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
  → Bd′ ≡ (M1 ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
  → BundleτR linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) M1
  → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′)
finishC-L nc eq eqL (bcsc st _ refl) rewrite eqL =
  SN.mkNodeC (csHead st) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bcss st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (ssHead st) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bbfc st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (bcHead st) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bbfs st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (bsHead st)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (btsc st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tcHead st) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (btss st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tsHead st) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bkac st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kcHead st) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bkas st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (ksHead st) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (blnc st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lncHead st) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (blns st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lnsHead st) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq

-- fold a link-CD bundle inversion into node C's successor
finishC-R : (nc : SN.NodeStateC) {C′ Bd′ M2 : NetProc}
  → C′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
  → Bd′ ≡ (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ M2)
  → BundleτR linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) M2
  → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′)
finishC-R nc eq eqR (bcsc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (csHead st) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-R nc eq eqR (bcss st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (ssHead st) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-R nc eq eqR (bbfc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (bcHead st) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-R nc eq eqR (bbfs st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (bsHead st) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-R nc eq eqR (btsc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tcHead st) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (btss st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tsHead st) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (bkac st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kcHead st) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (bkas st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (ksHead st) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (blnc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lncHead st) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (blns st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lnsHead st) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq

-- NODE-C τ-inversion
nodeC-τ-inv : (nc : SN.NodeStateC) {C′ : NetProc}
  → decNodeC nc ─[ τ ]─► C′ → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′)
nodeC-τ-inv nc step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _ = ⊥-elim (decCP-no-τ linkAC linkCD (SN.NodeStateC.cp-C nc) ds)
nodeC-τ-inv nc step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)) _ bs
...   | PEA.τL _ s1 eqL = finishC-L nc eq eqL
          (bundle-τ-inv linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) s1)
...   | PEA.τR _ s2 eqR = finishC-R nc eq eqR
          (bundle-τ-inv linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) s2)

-- fold a link-BD bundle inversion into node D's successor
finishD-L : (nd : SN.NodeStateD) {D′ Bd′ M1 : NetProc}
  → D′ ≡ (Bd′ ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)))
  → Bd′ ≡ (M1 ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
  → BundleτR linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) M1
  → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′)
finishD-L nd eq eqL (bcsc st _ refl) rewrite eqL =
  SN.mkNodeD (csHead st) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bcss st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (ssHead st) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bbfc st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (bcHead st) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bbfs st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (bsHead st) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (btsc st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tcHead st) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (btss st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tsHead st) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bkac st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kcHead st) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bkas st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (ksHead st) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (blnc st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lncHead st) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (blns st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lnsHead st) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq

-- fold a link-CD bundle inversion into node D's successor
finishD-R : (nd : SN.NodeStateD) {D′ Bd′ M2 : NetProc}
  → D′ ≡ (Bd′ ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)))
  → Bd′ ≡ (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ M2)
  → BundleτR linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) M2
  → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′)
finishD-R nd eq eqR (bcsc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (csHead st) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-R nd eq eqR (bcss st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (ssHead st) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-R nd eq eqR (bbfc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (bcHead st) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-R nd eq eqR (bbfs st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (bsHead st) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-R nd eq eqR (btsc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tcHead st) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (btss st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tsHead st) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (bkac st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kcHead st) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (bkas st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (ksHead st) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (blnc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lncHead st) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (blns st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lnsHead st) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq

-- NODE-D τ-inversion
nodeD-τ-inv : (nd : SN.NodeStateD) {D′ : NetProc}
  → decNodeD nd ─[ τ ]─► D′ → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′)
nodeD-τ-inv nd step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decConsD linkBD (SN.NodeStateD.cons-BD nd))
           (decConsD linkCD (SN.NodeStateD.cons-CD nd)) ds
...   | PEA.τL _ ps _ = ⊥-elim (decConsD-no-τ linkBD (SN.NodeStateD.cons-BD nd) ps)
...   | PEA.τR _ qs _ = ⊥-elim (decConsD-no-τ linkCD (SN.NodeStateD.cons-CD nd) qs)
nodeD-τ-inv nd step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)) _ bs
...   | PEA.τL _ s1 eqL = finishD-L nd eq eqL
          (bundle-τ-inv linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) s1)
...   | PEA.τR _ s2 eqR = finishD-R nd eq eqR
          (bundle-τ-inv linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) s2)


------------------------------------------------------------------------
-- GROUP 5a — ABSTRACT-SIDE τ-FREEDOM (the `otauB` `aτ-nds` vacuity).
--
-- The abstract nodes decode to `tableSpec` peer bundles + the SHARED τ-free
-- drivers.  Every `tableSpec T q` is either `ret tt` (`isFin T q ≡ true`) or a
-- stable `react (tMenu T q) (λ _ _ → nothing)` (`isFin T q ≡ false`) — NEVER a
-- `sil` and NEVER a react with a firing τ-branch — so it admits NO τ.  Peeling
-- the abstract node/bundle `⦀` stacks refutes every operand, mirroring the
-- concrete `nodeX-τ-inv` backbone but with all branches VACUOUS.
------------------------------------------------------------------------

-- force of a `tableSpec` peer at a TERMINAL position: `ret tt`
tsForce-ret : {Pos : Set} (T : NS.Table Pos) (q : Pos)
  → NS.Table.isFin T q ≡ true → PTree.force (tableSpec T q) ≡ ret tt
tsForce-ret T q eqf = cong (tsNode T q) eqf

-- force of a `tableSpec` peer at a NON-terminal position: a stable react whose
-- τ-branch is everywhere `nothing` (the `nxt`-table visible-offer react)
tsForce-react : {Pos : Set} (T : NS.Table Pos) (q : Pos)
  → NS.Table.isFin T q ≡ false
  → PTree.force (tableSpec T q) ≡ react (tMenu T q) (λ _ _ → nothing)
tsForce-react T q eqf = cong (tsNode T q) eqf

-- a `tableSpec` peer admits NO τ (τ-free: `ret` or stable react, per `isFin`)
tableSpec-no-τ : {Pos : Set} (T : NS.Table Pos) (q : Pos) {M : NetProc}
  → ¬ (tableSpec T q ─[ τ ]─► M)
tableSpec-no-τ T q step with NS.Table.isFin T q in eqf
... | true  = ret-no-τ   {P = tableSpec T q} (tsForce-ret T q eqf) step
... | false = react-no-τ {P = tableSpec T q} (tsForce-react T q eqf) (λ _ _ → refl) step

-- the abstract 8-peer bundle is τ-free (peel the 7 `⦀`, refute each tableSpec peer)
absBundleG-no-τ : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos) {M : NetProc}
  → ¬ (absBundleG l cl sv qcc qcs qbc qbs ip ─[ τ ]─► M)
absBundleG-no-τ l cl sv qcc qcs qbc qbs ip step
  with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
... | PEA.τR _ q1 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...   | PEA.τR _ q2 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absCSc l cl qcc) _ q2
...     | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...     | PEA.τR _ q3 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absCSs l sv qcs) _ q3
...       | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...       | PEA.τR _ q4 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absBFc l cl qbc) _ q4
...         | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...         | PEA.τR _ q5 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absBFs l sv qbs) _ q5
...           | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...           | PEA.τR _ q6 _
                with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) (absTSs l sv (tss ip)) q6
...             | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...             | PEA.τR _ qs _ = tableSpec-no-τ _ _ qs

-- NODE-A abstract τ-freedom (bundle refuted by `absBundleG-no-τ`, driver by `decProd-no-τ`)
absNodeA-no-τ : (na : SN.NodeStateA) {A′ : NetProc} → ¬ (absNodeA na ─[ τ ]─► A′)
absNodeA-no-τ na step with reflect-node-τ _ _ step
... | driverτ _ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ ds
...   | PEA.τL _ ps _ = decProd-no-τ linkAB hi b1 (SN.NodeStateA.prod-AB na) ps
...   | PEA.τR _ qs _ = decProd-no-τ linkAC hi b1 (SN.NodeStateA.prod-AC na) qs
absNodeA-no-τ na step | bundleτ _ bs _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na)
                       (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _ bs
...   | PEA.τL _ s1 _ = absBundleG-no-τ linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) s1
...   | PEA.τR _ s2 _ = absBundleG-no-τ linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) s2

-- NODE-B abstract τ-freedom (single `decCP` driver)
absNodeB-no-τ : (nb : SN.NodeStateB) {B′ : NetProc} → ¬ (absNodeB nb ─[ τ ]─► B′)
absNodeB-no-τ nb step with reflect-node-τ _ _ step
... | driverτ _ ds _ = decCP-no-τ linkAB linkBD (SN.NodeStateB.cp-B nb) ds
absNodeB-no-τ nb step | bundleτ _ bs _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
                       (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)) _ bs
...   | PEA.τL _ s1 _ = absBundleG-no-τ linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) s1
...   | PEA.τR _ s2 _ = absBundleG-no-τ linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) s2

-- NODE-C abstract τ-freedom (single `decCP` driver)
absNodeC-no-τ : (nc : SN.NodeStateC) {C′ : NetProc} → ¬ (absNodeC nc ─[ τ ]─► C′)
absNodeC-no-τ nc step with reflect-node-τ _ _ step
... | driverτ _ ds _ = decCP-no-τ linkAC linkCD (SN.NodeStateC.cp-C nc) ds
absNodeC-no-τ nc step | bundleτ _ bs _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
                       (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)) _ bs
...   | PEA.τL _ s1 _ = absBundleG-no-τ linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) s1
...   | PEA.τR _ s2 _ = absBundleG-no-τ linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) s2

-- NODE-D abstract τ-freedom (two `decConsD` drivers)
absNodeD-no-τ : (nd : SN.NodeStateD) {D′ : NetProc} → ¬ (absNodeD nd ─[ τ ]─► D′)
absNodeD-no-τ nd step with reflect-node-τ _ _ step
... | driverτ _ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decConsD linkBD (SN.NodeStateD.cons-BD nd)) _ ds
...   | PEA.τL _ ps _ = decConsD-no-τ linkBD (SN.NodeStateD.cons-BD nd) ps
...   | PEA.τR _ qs _ = decConsD-no-τ linkCD (SN.NodeStateD.cons-CD nd) qs
absNodeD-no-τ nd step | bundleτ _ bs _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
                       (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)) _ bs
...   | PEA.τL _ s1 _ = absBundleG-no-τ linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) s1
...   | PEA.τR _ s2 _ = absBundleG-no-τ linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) s2

-- the whole abstract four-node `⦀` is τ-free (peel the 3 `⦀`, refute each node);
-- this is exactly the `aτ-nds` VACUITY the `otauB` assembly needs
absNodesOf-no-τ : (s : SysState) {M : NetProc} → ¬ (absNodesOf s ─[ τ ]─► M)
absNodesOf-no-τ s step with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absNodeA (nA s)) _ step
... | PEA.τL _ ps _ = absNodeA-no-τ (nA s) ps
... | PEA.τR _ q1 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absNodeB (nB s)) _ q1
...   | PEA.τL _ ps _ = absNodeB-no-τ (nB s) ps
...   | PEA.τR _ q2 _
        with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) q2
...     | PEA.τL _ ps _ = absNodeC-no-τ (nC s) ps
...     | PEA.τR _ qs _ = absNodeD-no-τ (nD s) qs

------------------------------------------------------------------------
-- GROUP 5b — ABSTRACT-SIDE ev INVERSION (the `oevB` peer leaf).
--
-- A `tableSpec T q` peer's visible offer map is `tMenu T q = tGo T ∘ nxt T q`,
-- so a visible step fires exactly one `nxt`-table edge: `nxt T q (e,a) ≡ just q′`
-- and the target is `tableSpec T q′`.  This is the table-driven positive
-- inversion the abstract driven peers (`absCSc`/`absCSs`/`absBFc`/`absBFs`) reuse.
------------------------------------------------------------------------

-- invert the `tGo`-image of a `nxt`-table lookup that yielded a `just` target
tGo-inv : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {A : Set 0ℓ} {e : Net_Api Payload A} {a : A} {M : NetProc}
  → tGo T (NS.Table.nxt T q (A , e) a) ≡ just M
  → Σ[ q′ ∈ Pos ] (NS.Table.nxt T q (A , e) a ≡ just q′) × (M ≡ tableSpec T q′)
tGo-inv T q {A} {e} {a} meq with NS.Table.nxt T q (A , e) a
... | just q′ = q′ , refl , sym (just-injective meq)
... | nothing with meq
...   | ()

-- `tableSpec` ev-inversion: a visible step of a `tableSpec` peer fires a unique
-- `nxt`-table edge, landing on that edge's target position (terminal `isFin`
-- position has no visible offer — a `ret` cannot `sVis`, refuted)
tableSpec-ev-inv : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {A : Set 0ℓ} {e : Net_Api Payload A} {a : A} {M : NetProc}
  → tableSpec T q ─[ ev (evl (evLabel A e a)) ]─► M
  → Σ[ q′ ∈ Pos ] (NS.Table.nxt T q (A , e) a ≡ just q′) × (M ≡ tableSpec T q′)
tableSpec-ev-inv T q step with NS.Table.isFin T q in eqf
... | true with ev-inv step
...   | v , τc , feq , veq with trans (sym feq) (tsForce-ret T q eqf)
...     | ()
tableSpec-ev-inv T q {A} {e} {a} step | false with ev-inv step
...   | v , τc , feq , veq with react-injective (trans (sym feq) (tsForce-react T q eqf))
...     | vEq , _ = tGo-inv T q (trans (sym (cong (λ w → w (A , e) a) vEq)) veq)

-- GAP-A forward direction: a `tableSpec` peer at a non-terminal position FIRES
-- the visible event of a `just`-valued `nxt` entry, landing on the table
-- successor (the constructor counterpart of `tableSpec-ev-inv`; the abstract
-- twin's step in the per-peer concrete↔abstract simulation)
tableSpec-ev-fwd : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {A : Set 0ℓ} {e : Net_Api Payload A} {a : A} {q′ : Pos}
  → NS.Table.isFin T q ≡ false
  → NS.Table.nxt T q (A , e) a ≡ just q′
  → tableSpec T q ─[ ev (evl (evLabel A e a)) ]─► tableSpec T q′
tableSpec-ev-fwd T q finEq nxtEq = sVis (tsForce-react T q finEq) (cong (tGo T) nxtEq)


------------------------------------------------------------------------
-- GROUP 1 (cell leaf) — copy-cell ev INVERSION.  A copy cell fires exactly
-- its phase's single visible offer: `empty ─[input l d id ? a]─► full a` and
-- `full x ─[output l d id ! x]─► draining x`; `draining` is a `sil` (no ev).
-- Mirrors `PerLink.Exp`'s proven `cp0-evL`/`cp1-evL` (identical `succV` cells),
-- at the Net-Payload alphabet `LN`.  The phase transition + target suffice for
-- the medium reconstruction (the delivered channel is fixed by the peel site).
------------------------------------------------------------------------

-- a `nothing ≡ just _` is absurd (level-polymorphic)
nothing-absurd : ∀ {a} {A : Set a} {x : A} → (nothing ≡ just x) → ⊥
nothing-absurd ()

-- the outcome of a copy-cell visible step: an input (empty→full a) or an
-- output (full x→draining x) firing, with the reconstructed target phase
data CopyEvR (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase) (M : NetProcN) : Set₁ where
  cevIn  : (x : Payload) → ph ≡ empty  → M ≡ decCopy l d id (full x)     → CopyEvR l d id ph M
  cevOut : (x : Payload) → ph ≡ full x → M ≡ decCopy l d id (draining x) → CopyEvR l d id ph M

-- `empty` (the `Copy` head) offers `input l d id ? x`, landing on `full x`
offer-empty : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → vis-of (PTree.force (decCopy l d id empty)) (Payload , input l d id) x
    ≡ just (decCopy l d id (full x))
offer-empty l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl

-- `full x` offers `output l d id ! x`, landing on `draining x`
offer-full : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , output l d id) x
    ≡ just (decCopy l d id (draining x))
offer-full l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id
                          | ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id | ≟-yes-refl x = refl

-- read the offer map of a copy cell at the fired event (from an `sVis` step)
cell-view : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id ph LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M
  → vis-of (PTree.force (decCopy l d id ph)) (A , e) a ≡ just M
cell-view l d id ph (LN.sVis eqf offer) = trans (cong (λ n → vis-of n _ _) eqf) offer

-- `empty` fires ONLY `input l d id` (any value), landing on `full a`; every
-- other channel / wrong instance offers `nothing` (refuted)
empty-evL : (l : Link) (d : Dir) (id : IDs)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M
  → CopyEvR l d id empty M
empty-evL l d id {e = input l₀ d₀ id₀} {a} step with l₀ ≟ l | d₀ ≟ d | id₀ ≟ id
... | yes refl | yes refl | yes refl =
      cevIn a refl (just-injective (trans (sym (cell-view l d id empty step)) (offer-empty l d id a)))
... | no ¬p | _ | _ = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l₀ d₀ id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) with l₀ ≟ l
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
... | yes refl | no ¬p | _ = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l d₀ id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) rewrite ≟-yes-refl l with d₀ ≟ d
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
... | yes refl | yes refl | no ¬p = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l d id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) rewrite ≟-yes-refl l | ≟-yes-refl d with id₀ ≟ id
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
empty-evL l d id {e = output l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = sndmsg l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = rcvmsg l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = tx     l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = sndack l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = rcvack l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = ack    l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)

-- `full x`'s force offers ONLY `output l d id ! x`; every other channel / wrong
-- instance / wrong value maps to `nothing` (the Output-prefix Cont guard)
full-menu-input  : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , input l₀ d₀ id₀) a′ ≡ nothing
full-menu-input  l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-sndmsg : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , sndmsg l₀ d₀ id₀) a′ ≡ nothing
full-menu-sndmsg l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-rcvmsg : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , rcvmsg l₀ d₀ id₀) a′ ≡ nothing
full-menu-rcvmsg l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-tx     : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , tx l₀ d₀ id₀) a′ ≡ nothing
full-menu-tx     l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-sndack : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : _} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (_ , sndack l₀ d₀ id₀) a′ ≡ nothing
full-menu-sndack l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-rcvack : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : _} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (_ , rcvack l₀ d₀ id₀) a′ ≡ nothing
full-menu-rcvack l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-ack    : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : _} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (_ , ack l₀ d₀ id₀) a′ ≡ nothing
full-menu-ack    l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl

-- `output` at a DIFFERENT value a′ ≢ x: `full x` offers nothing
full-menu-output-val : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} → ¬ (a′ ≡ x)
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , output l d id) a′ ≡ nothing
full-menu-output-val l d id x {a′} a≢
  rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id
        | ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id with a′ ≟ x
... | yes p = ⊥-elim (a≢ p)
... | no  _ = refl

-- an `output` off the diagonal channel/instance: `full x` offers nothing
full-out-off : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {M : NetProcN}
  → ¬ ((Payload , output l₀ d₀ id₀) ≡ (Payload , output l d id))
  → decCopy l d id (full x) LN.─[ LN.ev (LN.evl (LN.evLabel Payload (output l₀ d₀ id₀) a′)) ]─► M → ⊥
full-out-off l d id x {a′} {l₀} {d₀} {id₀} ¬eq step with cell-view l d id (full x) step
... | v rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id
      with Net-≟ (Payload , output l d id) (Payload , output l₀ d₀ id₀)
...   | no  _  = nothing-absurd v
...   | yes eq = ¬eq (sym eq)

-- `full x` fires ONLY `output l d id ! x`, landing on `draining x`
full-evL : (l : Link) (d : Dir) (id : IDs) (x : Payload)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id (full x) LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M
  → CopyEvR l d id (full x) M
full-evL l d id x {e = output l₀ d₀ id₀} {a} step with l₀ ≟ l | d₀ ≟ d | id₀ ≟ id | a ≟ x
... | yes refl | yes refl | yes refl | yes refl =
      cevOut x refl (just-injective (trans (sym (cell-view l d id (full x) step)) (offer-full l d id x)))
... | yes refl | yes refl | yes refl | no  a≢   =
      ⊥-elim (nothing-absurd (trans (sym (full-menu-output-val l d id x a≢)) (cell-view l d id (full x) step)))
... | no  ¬p   | _        | _        | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
... | yes refl | no  ¬p   | _        | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
... | yes refl | yes refl | no  ¬p   | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
full-evL l d id x {e = input  l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-input  l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = sndmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-sndmsg l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = rcvmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-rcvmsg l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = tx     l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-tx     l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = sndack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-sndack l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = rcvack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-rcvack l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = ack    l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-ack    l d id x)) (cell-view l d id (full x) step)))

-- `draining x` is a `sil` (the drain loop-back), so it has NO visible step
draining-evL : (l : Link) (d : Dir) (id : IDs) (x : Payload)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id (draining x) LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M → ⊥
draining-evL l d id x (LN.sVis feq _) with trans (sym feq) (fdrain l d id x)
... | ()

-- per-cell ev inversion: a copy-cell visible step is an input (empty→full) or
-- an output (full→draining) firing, reconstructing the target phase
decCopy-ev-inv : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id ph LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M
  → CopyEvR l d id ph M
decCopy-ev-inv l d id empty        step = empty-evL l d id step
decCopy-ev-inv l d id (full x)     step = full-evL  l d id x step
decCopy-ev-inv l d id (draining x) step = ⊥-elim (draining-evL l d id x step)

------------------------------------------------------------------------
-- GROUP 1 (channel-disjointness) — a copy cell fires ONLY its OWN (l,d,id)
-- channel.  `cell-key` extracts the fired event's channel identity (`input`
-- or `output` at exactly `(l,d,id)`); `cell-diff-noBoth` refutes the `evBoth`
-- case of the `⦀`-ev peel — two DISTINCT-key cells cannot fire the SAME event.
-- This is the one NEW non-mechanical piece the ev-lifts need (τ-side never has
-- an evBoth).  Distinct model keys `(l,d,id)` make the disjointness hold.
------------------------------------------------------------------------

-- the channel a copy-cell visible step fires: `input`/`output` at its OWN key
data CellChan (l : Link) (d : Dir) (id : IDs) : {X : Set 0ℓ} → Net Payload X → Set₁ where
  chIn  : CellChan l d id (input l d id)
  chOut : CellChan l d id (output l d id)

-- `empty` fires ONLY `input l d id` (the diagonal), refuting wrong keys/channels
cell-key-empty : (l : Link) (d : Dir) (id : IDs)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
  → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M → CellChan l d id e
cell-key-empty l d id {e = input l₀ d₀ id₀} {a} step with l₀ ≟ l | d₀ ≟ d | id₀ ≟ id
... | yes refl | yes refl | yes refl = chIn
... | no ¬p | _ | _ = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l₀ d₀ id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) with l₀ ≟ l
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
... | yes refl | no ¬p | _ = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l d₀ id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) rewrite ≟-yes-refl l with d₀ ≟ d
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
... | yes refl | yes refl | no ¬p = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l d id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) rewrite ≟-yes-refl l | ≟-yes-refl d with id₀ ≟ id
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
cell-key-empty l d id {e = output l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = sndmsg l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = rcvmsg l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = tx     l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = sndack l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = rcvack l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = ack    l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)

-- `full x` fires ONLY `output l d id` (the diagonal), refuting wrong keys/channels
cell-key-full : (l : Link) (d : Dir) (id : IDs) (x : Payload)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
  → decCopy l d id (full x) LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M → CellChan l d id e
cell-key-full l d id x {e = output l₀ d₀ id₀} {a} step with l₀ ≟ l | d₀ ≟ d | id₀ ≟ id
... | yes refl | yes refl | yes refl = chOut
... | no  ¬p   | _        | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
... | yes refl | no  ¬p   | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
... | yes refl | yes refl | no  ¬p   = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
cell-key-full l d id x {e = input  l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-input  l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = sndmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-sndmsg l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = rcvmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-rcvmsg l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = tx     l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-tx     l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = sndack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-sndack l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = rcvack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-rcvack l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = ack    l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-ack    l d id x)) (cell-view l d id (full x) step)))

-- any copy-cell visible step fires the cell's own channel (draining has none)
cell-key : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
  → decCopy l d id ph LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M → CellChan l d id e
cell-key l d id empty        step = cell-key-empty l d id step
cell-key l d id (full x)     step = cell-key-full  l d id x step
cell-key l d id (draining x) step = ⊥-elim (draining-evL l d id x step)

-- CHANNEL-DISJOINTNESS: two cells of the SAME link with DISTINCT `(d,id)` keys
-- cannot fire the SAME visible event (their channels are disjoint) — refutes the
-- `evBoth` case of a within-link `⦀⋆` peel.  Both `cell-key`s pin the SAME event
-- `e` to each cell's own key, forcing `(d,id) ≡ (d′,id′)`, contra the hypothesis.
cell-diff-noBoth : (l : Link) (d d′ : Dir) (id id′ : IDs) (ph ph′ : CopyPhase)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M M′ : NetProcN}
  → ¬ ((d , id) ≡ (d′ , id′))
  → decCopy l d  id  ph  LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M
  → decCopy l d′ id′ ph′ LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M′ → ⊥
cell-diff-noBoth l d d′ id id′ ph ph′ ¬eq s1 s2
  with cell-key l d id ph s1 | cell-key l d′ id′ ph′ s2
... | chIn  | chIn  = ¬eq refl
... | chOut | chOut = ¬eq refl

------------------------------------------------------------------------
-- GROUP 3 — DRIVER ev INVERSION.  The `decProd`/`decCons`/`decConsD`/`decCP`
-- drivers are NATIVE `Net_Api` prefix chains (no rename, no fold): each phase
-- forces to a single `Prefix`/`Output` react offering exactly ONE api event and
-- landing on the next phase.  A visible step therefore FIRES that api event and
-- advances the phase; the terminal (`ret`) phase has no visible step (refuted).
-- The producer driver `decProd` is done here (its phases are constant-tail
-- prefixes/outputs); it is REUSED by `decCP producing` and the `decConsD` tail.
------------------------------------------------------------------------

-- the Net_Api prefix/output step inversions (`⟶₀`-ev; generic in the channel)
import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) as PInv
open PInv using ( ⟶₀-ev-inv; Prefix-cont-fires )
-- the Net_Api prefix + output prefixes + their offer maps (the driver phases)
open Op using ( Prefix; Output; Output-cont )
open import Class.DecEq using ( DecEq )

-- a `ret`-forced tree has no visible (`evl`) step (only a `√`, ruled out here)
ret-no-ev : {R : Set} {r : R}
    {P M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → PTree.force P ≡ ret r → ¬ (P ─[ ev (evl (evLabel X e a)) ]─► M)
ret-no-ev feq (sVis feq′ _) with trans (sym feq′) feq
... | ()

-- an `Output` (`ce ! v ⟶ P`) visible step lands on its tail `P`.  `ce`/`v`/`P`
-- are IMPLICIT so the subject unifies at the PTree head; the offer-map `with`
-- is inlined HERE (where `ce`/`deqB`/`a` are variables, so `Output-cont` reduces
-- cleanly) rather than delegated — dodging the stuck-neutral unification block.
-- The `DecEq` instance is threaded EXPLICITLY (unified from the subject) to dodge
-- the ambiguous `DecEq-Header×Tip` instance search.  R-generic (⊤ producer /
-- Block₃ consumer chains both reuse it).
output-ev-inv : {R : Set} {B : Set 0ℓ} {deqB : DecEq B} {ce : Net_Api Payload B} {v : B}
    {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
  → (Output ⦃ deqB ⦄ ce v P) ─[ ev (evl (evLabel X e a)) ]─► M → M ≡ P
output-ev-inv {R} {B} {deqB} {ce} {v} {P} {X} {e} {a} (sVis refl br)
    with Net_Api-≟ {Payload} (B , ce) (X , e)
... | no  ¬eq  = ⊥-elim (nothing-absurd br)
... | yes refl with _≟_ ⦃ deqB ⦄ a v
...   | yes _  = sym (just-injective br)
...   | no  _  = ⊥-elim (nothing-absurd br)

-- a `Prefix` (`ce ⟶ P`) visible step lands on `P x` for the fired value `x`
-- (non-`₀`: the continuation may DEPEND on the received value — the consumer
-- driver's `recvCSRollforward`/`recvBFBlock` data-carrying phases)
prefix-ev-inv : {R : Set} {A : Set 0ℓ} {ce : Net_Api Payload A}
    {P : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
  → (Prefix ce P) ─[ ev (evl (evLabel X e a)) ]─► M → Σ[ x ∈ A ] (M ≡ P x)
prefix-ev-inv (sVis refl br) with Prefix-cont-fires br
... | refl , x , t′≡ = x , t′≡

-- which producer phase a visible step lands on (always the successor phase)
data ProdEvR (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh) (M : NetProc) : Set₁ where
  peR : (pp′ : ProdPh) → M ≡ decProd l d blk pp′ → ProdEvR l d blk pp M

-- producer-driver ev inversion: pp0..pp6 fire their head api event and advance
-- to the next phase (pp0→pp1 … pp6→pp7); pp7 = Skip = ret has no visible step
decProd-ev-inv : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M → ProdEvR l d blk pp M
decProd-ev-inv l d blk pp0 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp1 refl
decProd-ev-inv l d blk pp1 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp2 refl
decProd-ev-inv l d blk pp2 step = peR pp3 (output-ev-inv step)
decProd-ev-inv l d blk pp3 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp4 refl
decProd-ev-inv l d blk pp4 step = peR pp5 (output-ev-inv step)
decProd-ev-inv l d blk pp5 step = peR pp6 (output-ev-inv step)
decProd-ev-inv l d blk pp6 step = peR pp7 (output-ev-inv step)
decProd-ev-inv l d blk pp7 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp8 refl
decProd-ev-inv l d blk pp8 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp9 refl
decProd-ev-inv l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- which consumer phase (+ the block carried onward) a visible step lands on.
-- The consumer chain THREADS a block (unlike the fixed-`b1` producer): the
-- data-carrying phases cp1 (`recvCSRollforward`) / cp3 (`recvBFBlock`) update it
-- to the received value, so the result phase carries its own block `b′`.
data ConsEvR (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
     (M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃) : Set₁ where
  ceR : (b′ : Block₃) (cp′ : ConsPh)
      → M ≡ decCons l d b′ cp′ → ConsEvR l d b cp M

-- consumer-driver ev inversion: cp0..cp5 fire their head api event and advance
-- to the next phase (cp1/cp3 rebind the block to the received value — cp1 via
-- the named `consume-k` pattern-lambda that the refactor made shared, cp3 via
-- the inner `λ b′ →`); cp6 = `Ret b` has no visible step (refuted).
decCons-ev-inv : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M → ConsEvR l d b cp M
decCons-ev-inv l d b cp0 step with ⟶₀-ev-inv step
... | _ , _ , refl = ceR b cp1 refl
decCons-ev-inv l d b cp1 step with prefix-ev-inv step
... | (header b′ , _) , refl = ceR b′ cp2 refl
decCons-ev-inv l d b cp2 step = ceR b cp3 (output-ev-inv step)
decCons-ev-inv l d b cp3 step with prefix-ev-inv step
... | b′ , refl = ceR b′ cp4 refl
decCons-ev-inv l d b cp4 step = ceR b cp5 (output-ev-inv step)
decCons-ev-inv l d b cp5 step with ⟶₀-ev-inv step
... | _ , _ , refl = ceR b cp6 refl
decCons-ev-inv l d b cp6 step = ⊥-elim (ret-no-ev {P = decCons l d b cp6} refl step)

------------------------------------------------------------------------
-- decConsD / decCP ev INVERSION (G3 handoff).  The node-D consume driver
-- `decConsD = decCons … >> Skip` and the relay driver `decCP consuming =
-- decCons … >>= produce` lift `decCons-ev-inv` through a bind; the relay's
-- `consuming cp6 → producing pp0` handoff uses the definitional `Ret >>= k`
-- reduction; `producing`/the produce leg REUSE `decProd-ev-inv`.
------------------------------------------------------------------------

-- single-step bind ev inversion: a visible step of `P >>= k`, when `P` forces
-- to a react node, FIRES `P`'s event and lands on `t >>= k` for `P`'s
-- derivative `t` (mirrors `bind-elim-aux`'s react-ev case: `bindV-elim` +
-- `react-injective` transport of the fired offer entry)
bind-ev-inv : {S : Set} (k : Block₃ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) S)
    (P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃)
    {vp : (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃))}
    {τcp : (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃))}
  → PTree.force P ≡ react vp τcp
  → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) S}
  → (P >>= k) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ t ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃ ]
      (P ─[ ev (evl (evLabel X e a)) ]─► t) × (M ≡ t >>= k)
bind-ev-inv k P {vp} {τcp} feq (sVis {at = at} {a = a} eqf br)
  with bindV-elim k (react vp τcp)
         (subst (λ g → g at a ≡ just _)
                (sym (proj₁ (react-injective (trans (sym (fBind-react k P feq)) eqf)))) br)
... | t , vv , refl = t , sVis feq vv , refl

-- which phase (+ carried block) a visible step of node-D's `decCons … >> Skip`
-- lands on (the carried block `b′` threads through as in `ConsEvR`)
data ConsDEvR (l : Link) (cph : ConsDPh) (M : NetProc) : Set₁ where
  cdR : (b′ : Block₃) (cp′ : ConsPh) → M ≡ decConsD l (consD b′ cp′) → ConsDEvR l cph M

-- node-D consume-driver ev inversion: fire the consume event through the
-- `>> Skip` bind (`bind-ev-inv`), advance the phase (`decCons-ev-inv`); cp6 =
-- `Ret b1 >> Skip` forces (via `>>=`-on-ret) to `Skip = ret`, so no visible step.
decConsD-ev-inv : (l : Link) (cph : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cph ─[ ev (evl (evLabel X e a)) ]─► M → ConsDEvR l cph M
decConsD-ev-inv l (consD b cp0) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp0 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp1) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp1 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp2) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp2 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp3) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp3 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp4) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp4 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp5) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp5 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp6) step = ⊥-elim (ret-no-ev {P = decConsD l (consD b cp6)} refl step)

-- which phase a visible step of a relay `consume l₁ hi >>= produce l₂ hi` lands
-- on: still consuming (+ carried block), or — past the bind-ret boundary —
-- producing (the produce leg, reusing `decProd`).
data CPEvR (l₁ l₂ : Link) (ph : CPPh) (M : NetProc) : Set₁ where
  cpR-cons : (b′ : Block₃) (cp′ : ConsPh)
           → M ≡ decCP l₁ l₂ (consuming b′ cp′) → CPEvR l₁ l₂ ph M
  cpR-prod : (b′ : Block₃) (pp′ : ProdPh)
           → M ≡ decCP l₁ l₂ (producing b′ pp′) → CPEvR l₁ l₂ ph M

-- transport a step across a force-equality (a step only inspects `PTree.force`);
-- used to view the bind-ret boundary `decCP … (consuming cp6)` as `decProd … pp0`
-- (they are force-equal by the `Ret b1 >>= k` reduction, but not convertible as
-- neutral copattern terms without unfolding the `with` head)
step-fcong : {R : Set} {P Q M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {l : Label R}
  → PTree.force P ≡ PTree.force Q → P ─[ l ]─► M → Q ─[ l ]─► M
step-fcong fe (sRet feq)    = sRet (trans (sym fe) feq)
step-fcong fe (sSil feq)    = sSil (trans (sym fe) feq)
step-fcong fe (sVis feq br) = sVis (trans (sym fe) feq) br
step-fcong fe (sTau feq br) = sTau (trans (sym fe) feq) br

-- relay-driver ev inversion: consuming cp0..cp5 advance the consume phase (via
-- the `>>= produce` bind); consuming cp6 = `Ret b1 >>= produce l₂ hi` reduces
-- (via `>>=`-on-ret) to `decProd l₂ hi pp0`, so the fired event is produce's
-- first (the `consuming cp6 → producing pp0` handoff, made explicit through
-- `step-fcong refl`); producing pp delegates to `decProd-ev-inv`.
decCP-ev-inv : (l₁ l₂ : Link) (ph : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel X e a)) ]─► M → CPEvR l₁ l₂ ph M
decCP-ev-inv l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp0 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp1 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp2 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp3 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp4 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp5 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp6) step
  with decProd-ev-inv l₂ hi b pp0 (step-fcong refl step)
... | peR pp′ refl = cpR-prod b pp′ refl
decCP-ev-inv l₁ l₂ (producing b pp) step with decProd-ev-inv l₂ hi b pp step
... | peR pp′ refl = cpR-prod b pp′ refl

------------------------------------------------------------------------
-- GROUP 1 (medium-ev lift) — mirror the committed `medium-τ-inv` chain, but
-- for VISIBLE io steps.  A hidden io (`input`/`output`, `break ∉ ioES`) of the
-- medium is one cell firing: `⦀Fin-ev-inv` peels the four-link interleave to
-- one link (evBoth refuted by link-level channel disjointness), `△-ev-elim`
-- discards the `break` operand (io ≠ break), `renameMap-ev-reflect` reflects to
-- the source fold, `⦀⋆-ev-inv` peels one cell (evBoth refuted by the committed
-- `cell-diff-noBoth`), and `decCopy-ev-inv` flips that cell (empty→full input /
-- full→draining output).  The peels are noBoth-parameterised (generic); the
-- disjointness witnesses are supplied concretely.
------------------------------------------------------------------------

-- a native Net-Payload `ret` has no visible step (the `⦀⋆ []` = `Skip` tail)
retN-no-ev : {Rr : Set} {r : Rr} {P M : PTree (Net Payload) (ExtI (Net Payload)) Rr}
    {X : Set 0ℓ} {e : Net Payload X} {a : X}
  → PTree.force P ≡ ret r → ¬ (P LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M)
retN-no-ev feq (LN.sVis feq′ _) with trans (sym feq′) feq
... | ()

-- `⦀⋆` list ev-peel (generic, noBoth-parameterised): a visible step of `⦀⋆ Ps`
-- fires exactly one cell's offer (evSync impossible under `∅ES`; evBoth refuted
-- by the `noBoth` disjointness), returning position + operand step + updated fold
⦀⋆-ev-inv : (Ps : List NetProcN)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
  → ((i j : Fin (length Ps)) → i ≢ j → {Mi Mj : NetProcN}
       → lookup Ps i LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mi
       → lookup Ps j LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mj → ⊥)
  → ⦀⋆ Ps LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M
  → Σ[ k ∈ Fin (length Ps) ] Σ[ Mk ∈ NetProcN ]
       (lookup Ps k LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mk)
       × (M ≡ ⦀⋆ (updateAt Ps k (λ _ → Mk)))
⦀⋆-ev-inv []       nb step = ⊥-elim (retN-no-ev {P = Skip} refl step)
⦀⋆-ev-inv (P ∷ Ps) nb step with PEN.Par-ev-elim ∅ES (λ _ _ → tt) P (⦀⋆ Ps) step
... | PEN.evSync mem _ _ = ⊥-elim mem
... | PEN.evL _ ps = fzero , _ , ps , refl
... | PEN.evR _ qs
      with ⦀⋆-ev-inv Ps (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) qs
...   | k , Mk , lstep , meq = fsuc k , Mk , lstep , cong (P OpN.⦀_) meq
⦀⋆-ev-inv (P ∷ Ps) nb step | PEN.evBoth _ ps qs
      with ⦀⋆-ev-inv Ps (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) qs
...   | k , _ , lstep , _ = ⊥-elim (nb fzero (fsuc k) (λ ()) ps lstep)

-- `⦀Fin` link ev-peel (generic, noBoth-parameterised): a visible step of
-- `⦀Fin n f` fires one link's offer (evSync impossible; evBoth refuted by the
-- `noBoth` link disjointness); mirrors `⦀Fin-τ-inv`
⦀Fin-ev-inv : (n : ℕ) (f : Fin n → NetProc)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ((i j : Fin n) → i ≢ j → {Mi Mj : NetProc}
       → f i ─[ ev (evl (evLabel X e a)) ]─► Mi
       → f j ─[ ev (evl (evLabel X e a)) ]─► Mj → ⊥)
  → ⦀Fin n f ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ i ∈ Fin n ] Σ[ Mi ∈ NetProc ]
       (f i ─[ ev (evl (evLabel X e a)) ]─► Mi) × (M ≡ ⦀Fin n (finUpd f i Mi))
⦀Fin-ev-inv zero f nb step = ⊥-elim (ret-no-ev {P = ⦀Fin zero f} refl step)
⦀Fin-ev-inv (suc n) f nb step
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (f fzero) (⦀Fin n (λ i → f (fsuc i))) step
... | PEA.evSync mem _ _ = ⊥-elim mem
... | PEA.evL _ ps = fzero , _ , ps , refl
... | PEA.evR _ qs
      with ⦀Fin-ev-inv n (λ i → f (fsuc i))
             (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) qs
...   | i , Mi , istep , meq = fsuc i , Mi , istep , cong (f fzero ⦀_) meq
⦀Fin-ev-inv (suc n) f nb step | PEA.evBoth _ ps qs
      with ⦀Fin-ev-inv n (λ i → f (fsuc i))
             (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) qs
...   | i , _ , istep , _ = ⊥-elim (nb fzero (fsuc i) (λ ()) ps istep)

-- the link component a source copy-fold visible step fires: `input`/`output`
-- at exactly link `l` (all cells of the link share `l`)
data CellChanL (l : Link) : {X : Set 0ℓ} → Net Payload X → Set₁ where
  clIn  : {d : Dir} {id : IDs} → CellChanL l (input l d id)
  clOut : {d : Dir} {id : IDs} → CellChanL l (output l d id)

-- a cell's own channel identity lifts to the link's channel identity
cellChan→L : (l : Link) (d : Dir) (id : IDs) {X : Set 0ℓ} {e : Net Payload X}
  → CellChan l d id e → CellChanL l e
cellChan→L l d id chIn  = clIn
cellChan→L l d id chOut = clOut

-- `fold-key`: any visible step of a copy fold `⦀⋆ (map cf cfg)` fires a channel
-- at link `l` (cf is passed as a variable so the recursion keeps ONE cell fn;
-- `cfk` extracts each cell's link channel).  evSync impossible; evL/evBoth read
-- the head cell, evR recurses
fold-key : (l : Link) (cf : Dir × IDs → NetProcN)
    (cfk : (di : Dir × IDs) {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
           → cf di LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M → CellChanL l e)
    (cfg : List (Dir × IDs))
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {P′ : NetProcN}
  → ⦀⋆ (map cf cfg) LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► P′
  → CellChanL l e
fold-key l cf cfk []        step = ⊥-elim (retN-no-ev {P = Skip} refl step)
fold-key l cf cfk (di ∷ tl) step
    with PEN.Par-ev-elim ∅ES (λ _ _ → tt) (cf di) (⦀⋆ (map cf tl)) step
... | PEN.evSync mem _ _ = ⊥-elim mem
... | PEN.evL _ ps       = cfk di ps
... | PEN.evR _ qs       = fold-key l cf cfk tl qs
... | PEN.evBoth _ ps _  = cfk di ps

-- the Net_Api link component a broken/unbroken link fires under an io step
data ApiLinkChan (l : Link) : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  alIn  : {d : Dir} {id : IDs} → ApiLinkChan l (input l d id)
  alOut : {d : Dir} {id : IDs} → ApiLinkChan l (output l d id)

-- two links firing the SAME io event must be the same link (the event's link
-- component is pinned by each; `input`/`output` cross-cases are index-impossible)
apiLinkChan-inj : {X : Set 0ℓ} {e : Net_Api Payload X} (l l′ : Link)
  → ApiLinkChan l e → ApiLinkChan l′ e → l ≡ l′
apiLinkChan-inj l l′ alIn  alIn  = refl
apiLinkChan-inj l l′ alOut alOut = refl

-- LINK-level channel key: an io step of a link fires an `input`/`output` at
-- exactly that link `l`.  Broken (`Skip = ret`) has no visible step; unbroken
-- peels `△` (break refuses io), reflects the rename (recovering the ι-preimage),
-- and reads the source fold's channel — pinning the link component to `l`
link-io-chan : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decLink l ph b ─[ ev (evl (evLabel X e a)) ]─► M
  → ApiLinkChan l e
link-io-chan l ph true iomem step = ⊥-elim (ret-no-ev {P = decLink l ph true} refl step)
link-io-chan l ph false {e = input l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (MedNO.force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , _
        with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _
          with just-injective iota
...       | refl
            with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | clIn = alIn
link-io-chan l ph false {e = output l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (MedNO.force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , _
        with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _
          with just-injective iota
...       | refl
            with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | clOut = alOut
link-io-chan l ph false {e = sndmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = rcvmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = tx     l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = sndack l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = rcvack l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = ack    l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = done   l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiCS  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiBF  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiTS  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiKA  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiLN  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiLF  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = break  l₀}        iomem step = ⊥-elim iomem

-- LINK DISJOINTNESS (the `⦀Fin`-ev evBoth refutation): distinct links cannot
-- fire the SAME io event (their io channels carry distinct link components)
link-io-diff : (m : MedState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (i j : Link) → i ≢ j → {Mi Mj : NetProc}
  → decLink i (phase m i) (broken m i) ─[ ev (evl (evLabel X e a)) ]─► Mi
  → decLink j (phase m j) (broken m j) ─[ ev (evl (evLabel X e a)) ]─► Mj → ⊥
link-io-diff m iomem i j i≢j si sj =
  i≢j (apiLinkChan-inj i j (link-io-chan i (phase m i) (broken m i) iomem si)
                           (link-io-chan j (phase m j) (broken m j) iomem sj))

-- CELL DISJOINTNESS (the `⦀⋆`-ev evBoth refutation for a link's cell list):
-- distinct cell positions of the concrete `uniformCfg` fold cannot fire the
-- SAME event (distinct `(d,id)` keys ⇒ disjoint channels).  64 concrete cases:
-- diagonal absurd by `i≢j refl`, off-diagonal via the committed `cell-diff-noBoth`.
cell-noBoth : (l : Link) (ph : Dir → IDs → CopyPhase)
    {X : Set 0ℓ} {e : Net Payload X} {a : X}
    (i j : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))))
  → i ≢ j → {Mi Mj : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) i LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mi
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) j LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mj → ⊥
cell-noBoth l ph fzero fzero i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph fzero (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_KeepAlive (ph lo N2N_KeepAlive) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_ChainSync (ph lo N2N_KeepAlive) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_ChainSync (ph lo N2N_KeepAlive) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_BlockFetch (ph lo N2N_KeepAlive) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_BlockFetch (ph lo N2N_KeepAlive) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_TxSubmission (ph lo N2N_KeepAlive) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_TxSubmission (ph lo N2N_KeepAlive) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_KeepAlive (ph hi N2N_KeepAlive) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc fzero) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_ChainSync (ph hi N2N_KeepAlive) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_ChainSync (ph hi N2N_KeepAlive) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_BlockFetch (ph hi N2N_KeepAlive) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_BlockFetch (ph hi N2N_KeepAlive) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_TxSubmission (ph hi N2N_KeepAlive) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_TxSubmission (ph hi N2N_KeepAlive) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_KeepAlive (ph lo N2N_ChainSync) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_KeepAlive (ph lo N2N_ChainSync) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_ChainSync (ph lo N2N_ChainSync) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_BlockFetch (ph lo N2N_ChainSync) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_BlockFetch (ph lo N2N_ChainSync) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_TxSubmission (ph lo N2N_ChainSync) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_TxSubmission (ph lo N2N_ChainSync) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_KeepAlive (ph hi N2N_ChainSync) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_KeepAlive (ph hi N2N_ChainSync) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_ChainSync (ph hi N2N_ChainSync) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_BlockFetch (ph hi N2N_ChainSync) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_BlockFetch (ph hi N2N_ChainSync) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_TxSubmission (ph hi N2N_ChainSync) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_TxSubmission (ph hi N2N_ChainSync) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_KeepAlive (ph lo N2N_BlockFetch) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_KeepAlive (ph lo N2N_BlockFetch) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_ChainSync (ph lo N2N_BlockFetch) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_ChainSync (ph lo N2N_BlockFetch) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_BlockFetch (ph lo N2N_BlockFetch) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_TxSubmission (ph lo N2N_BlockFetch) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_TxSubmission (ph lo N2N_BlockFetch) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_KeepAlive (ph hi N2N_BlockFetch) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_KeepAlive (ph hi N2N_BlockFetch) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_ChainSync (ph hi N2N_BlockFetch) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_ChainSync (ph hi N2N_BlockFetch) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_BlockFetch (ph hi N2N_BlockFetch) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_TxSubmission (ph hi N2N_BlockFetch) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_TxSubmission (ph hi N2N_BlockFetch) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_KeepAlive (ph lo N2N_TxSubmission) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_KeepAlive (ph lo N2N_TxSubmission) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_ChainSync (ph lo N2N_TxSubmission) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_ChainSync (ph lo N2N_TxSubmission) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_BlockFetch (ph lo N2N_TxSubmission) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_BlockFetch (ph lo N2N_TxSubmission) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_TxSubmission (ph lo N2N_TxSubmission) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_KeepAlive (ph hi N2N_TxSubmission) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_KeepAlive (ph hi N2N_TxSubmission) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_ChainSync (ph hi N2N_TxSubmission) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_ChainSync (ph hi N2N_TxSubmission) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_BlockFetch (ph hi N2N_TxSubmission) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_BlockFetch (ph hi N2N_TxSubmission) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_TxSubmission (ph hi N2N_TxSubmission) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_LeiosNotify (ph lo N2N_KeepAlive) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_LeiosNotify (ph lo N2N_KeepAlive) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_LeiosFetch (ph lo N2N_KeepAlive) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_LeiosFetch (ph lo N2N_KeepAlive) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_LeiosNotify (ph hi N2N_KeepAlive) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_LeiosNotify (ph hi N2N_KeepAlive) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_LeiosFetch (ph hi N2N_KeepAlive) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_LeiosFetch (ph hi N2N_KeepAlive) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_LeiosNotify (ph lo N2N_ChainSync) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_LeiosNotify (ph lo N2N_ChainSync) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_LeiosFetch (ph lo N2N_ChainSync) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_LeiosFetch (ph lo N2N_ChainSync) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_LeiosNotify (ph hi N2N_ChainSync) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_LeiosNotify (ph hi N2N_ChainSync) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_LeiosFetch (ph hi N2N_ChainSync) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_LeiosFetch (ph hi N2N_ChainSync) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_LeiosNotify (ph lo N2N_BlockFetch) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_LeiosNotify (ph lo N2N_BlockFetch) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_LeiosFetch (ph lo N2N_BlockFetch) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_LeiosFetch (ph lo N2N_BlockFetch) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_LeiosNotify (ph hi N2N_BlockFetch) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_LeiosNotify (ph hi N2N_BlockFetch) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_LeiosFetch (ph hi N2N_BlockFetch) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_LeiosFetch (ph hi N2N_BlockFetch) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_LeiosNotify (ph lo N2N_TxSubmission) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_LeiosNotify (ph lo N2N_TxSubmission) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_LeiosFetch (ph lo N2N_TxSubmission) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_LeiosFetch (ph lo N2N_TxSubmission) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_LeiosNotify (ph hi N2N_TxSubmission) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_LeiosNotify (ph hi N2N_TxSubmission) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_LeiosFetch (ph hi N2N_TxSubmission) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_LeiosFetch (ph hi N2N_TxSubmission) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_KeepAlive (ph lo N2N_LeiosNotify) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_KeepAlive (ph lo N2N_LeiosNotify) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_ChainSync (ph lo N2N_LeiosNotify) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_ChainSync (ph lo N2N_LeiosNotify) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_BlockFetch (ph lo N2N_LeiosNotify) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_BlockFetch (ph lo N2N_LeiosNotify) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_TxSubmission (ph lo N2N_LeiosNotify) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_TxSubmission (ph lo N2N_LeiosNotify) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_LeiosNotify (ph lo N2N_LeiosNotify) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_LeiosFetch (ph lo N2N_LeiosNotify) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_LeiosFetch (ph lo N2N_LeiosNotify) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_KeepAlive (ph hi N2N_LeiosNotify) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_KeepAlive (ph hi N2N_LeiosNotify) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_ChainSync (ph hi N2N_LeiosNotify) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_ChainSync (ph hi N2N_LeiosNotify) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_BlockFetch (ph hi N2N_LeiosNotify) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_BlockFetch (ph hi N2N_LeiosNotify) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_TxSubmission (ph hi N2N_LeiosNotify) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_TxSubmission (ph hi N2N_LeiosNotify) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_LeiosNotify (ph hi N2N_LeiosNotify) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_LeiosFetch (ph hi N2N_LeiosNotify) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_LeiosFetch (ph hi N2N_LeiosNotify) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_KeepAlive (ph lo N2N_LeiosFetch) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_KeepAlive (ph lo N2N_LeiosFetch) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_ChainSync (ph lo N2N_LeiosFetch) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_ChainSync (ph lo N2N_LeiosFetch) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_BlockFetch (ph lo N2N_LeiosFetch) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_BlockFetch (ph lo N2N_LeiosFetch) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_TxSubmission (ph lo N2N_LeiosFetch) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_TxSubmission (ph lo N2N_LeiosFetch) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_LeiosNotify (ph lo N2N_LeiosFetch) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_LeiosNotify (ph lo N2N_LeiosFetch) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_LeiosFetch (ph lo N2N_LeiosFetch) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_KeepAlive (ph hi N2N_LeiosFetch) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_KeepAlive (ph hi N2N_LeiosFetch) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_ChainSync (ph hi N2N_LeiosFetch) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_ChainSync (ph hi N2N_LeiosFetch) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_BlockFetch (ph hi N2N_LeiosFetch) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_BlockFetch (ph hi N2N_LeiosFetch) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_TxSubmission (ph hi N2N_LeiosFetch) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_TxSubmission (ph hi N2N_LeiosFetch) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_LeiosNotify (ph hi N2N_LeiosFetch) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_LeiosNotify (ph hi N2N_LeiosFetch) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_LeiosFetch (ph hi N2N_LeiosFetch) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = ⊥-elim (i≢j refl)

-- set one cell `(d₀,id₀)` of a link's phase function to a new phase `np`
setCell : (Dir → IDs → CopyPhase) → Dir → IDs → CopyPhase → (Dir → IDs → CopyPhase)
setCell g d₀ id₀ np d id with d ≟ d₀ | id ≟ id₀
... | no  _ | _     = g d id
... | yes _ | no  _ = g d id
... | yes _ | yes _ = np

-- per-position cell FLIP: at concrete cell index `k` the cell `(dₖ,idₖ)` fired
-- (empty→full x input / full x→draining x output); the positional `updateAt`
-- equals the key-set `map` (distinct keys ⇒ each cell equality holds by `refl`)
cellFlipEv : (l : Link) (ph : Dir → IDs → CopyPhase)
    (k : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))))
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {Mk : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mk
  → Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ] Σ[ np ∈ CopyPhase ]
       (updateAt (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k (λ _ → Mk)
          ≡ map (λ { (d , id) → decCopy l d id (setCell ph d₀ id₀ np d id) }) (linkConfig l))
cellFlipEv l ph fzero cs with decCopy-ev-inv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_KeepAlive , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_KeepAlive , draining x , refl
cellFlipEv l ph (fsuc fzero) cs with decCopy-ev-inv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_KeepAlive , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_KeepAlive , draining x , refl
cellFlipEv l ph (fsuc (fsuc fzero)) cs with decCopy-ev-inv l lo N2N_ChainSync (ph lo N2N_ChainSync) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_ChainSync , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_ChainSync , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc fzero))) cs with decCopy-ev-inv l hi N2N_ChainSync (ph hi N2N_ChainSync) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_ChainSync , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_ChainSync , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc fzero)))) cs with decCopy-ev-inv l lo N2N_BlockFetch (ph lo N2N_BlockFetch) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_BlockFetch , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_BlockFetch , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) cs with decCopy-ev-inv l hi N2N_BlockFetch (ph hi N2N_BlockFetch) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_BlockFetch , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_BlockFetch , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) cs with decCopy-ev-inv l lo N2N_TxSubmission (ph lo N2N_TxSubmission) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_TxSubmission , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_TxSubmission , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) cs with decCopy-ev-inv l hi N2N_TxSubmission (ph hi N2N_TxSubmission) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_TxSubmission , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_TxSubmission , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) cs with decCopy-ev-inv l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_LeiosNotify , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_LeiosNotify , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) cs with decCopy-ev-inv l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_LeiosNotify , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_LeiosNotify , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) cs with decCopy-ev-inv l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_LeiosFetch , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_LeiosFetch , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) cs with decCopy-ev-inv l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_LeiosFetch , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_LeiosFetch , draining x , refl

-- LINK ev-inversion: an io step of an unbroken link is one cell firing; the
-- target is the same link with that cell's phase advanced (empty→full input /
-- full→draining output).  Mirrors `decLink-τ-inv`: `△-ev-elim` (break refuses
-- io) → `renameMap-ev-reflect` → `⦀⋆-ev-inv` (evBoth via `cell-noBoth`) →
-- `cellFlipEv` (the fired cell's phase set).  Broken (`Skip`) has no visible step.
decLink-ev-inv : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decLink l ph b ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ ph′ ∈ (Dir → IDs → CopyPhase) ] (b ≡ false) × (M ≡ decLink l ph′ false)
decLink-ev-inv l ph true iomem step = ⊥-elim (ret-no-ev {P = decLink l ph true} refl step)
decLink-ev-inv l ph false {e = input l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (MedNO.force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , Meq
        with MedNO.renameMap-ev-reflect leftStep
...     | e₁ , Q′ , srcStep , P′eq
          with ⦀⋆-ev-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
                         (cell-noBoth l ph) srcStep
...       | k , Mk , cellStep , Q′eq
            with cellFlipEv l ph k cellStep
...         | d₀ , id₀ , np , listEq =
              setCell ph d₀ id₀ np , refl ,
              trans Meq
                (trans (cong (λ z → z △ (break l ⟶₀ Op.Skip)) P′eq)
                  (trans (cong (λ z → renameMap z △ (break l ⟶₀ Op.Skip)) Q′eq)
                         (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Op.Skip)) listEq)))
decLink-ev-inv l ph false {e = output l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (MedNO.force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , Meq
        with MedNO.renameMap-ev-reflect leftStep
...     | e₁ , Q′ , srcStep , P′eq
          with ⦀⋆-ev-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
                         (cell-noBoth l ph) srcStep
...       | k , Mk , cellStep , Q′eq
            with cellFlipEv l ph k cellStep
...         | d₀ , id₀ , np , listEq =
              setCell ph d₀ id₀ np , refl ,
              trans Meq
                (trans (cong (λ z → z △ (break l ⟶₀ Op.Skip)) P′eq)
                  (trans (cong (λ z → renameMap z △ (break l ⟶₀ Op.Skip)) Q′eq)
                         (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Op.Skip)) listEq)))
decLink-ev-inv l ph false {e = sndmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = rcvmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = tx     l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = sndack l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = rcvack l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = ack    l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = done   l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiCS  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiBF  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiTS  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiKA  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiLN  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiLF  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = break  l₀}        iomem step = ⊥-elim iomem

-- MEDIUM ev-inversion (io delivery): `⦀Fin-ev-inv` peels the four-link
-- interleave to one link `i` (evBoth refuted by `link-io-diff`); `decLink-ev-inv`
-- advances that link's fired cell.  Reconstructs the `MedState` successor via the
-- committed `phase-upd`/`recon-decMed` bridge (mirrors `medium-τ-inv`).  Scoped
-- to hidden io (`break ∉ ioES`), matching the `cτ-io` classifier that supplies it.
medium-ev-inv : (m : MedState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decMed m ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ m′ ∈ MedState ] (M ≡ decMed m′)
medium-ev-inv m iomem step
    with ⦀Fin-ev-inv numLinks (λ l → decLink l (phase m l) (broken m l)) (link-io-diff m iomem) step
... | i , Mi , linkStep , Meq
      with decLink-ev-inv i (phase m i) (broken m i) iomem linkStep
...   | ph′ , brEq , MiEq =
        mkMed (phase-upd (phase m) i ph′) (broken m) ,
        trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                    (finUpd (λ l → decLink l (phase m l) (broken m l)) i z))
                    (trans MiEq (cong (decLink i ph′) (sym brEq))))
                 (recon-decMed m i ph′))

------------------------------------------------------------------------
-- G2 — PER-PEER VISIBLE-EVENT INVERSIONS (`dec{peer}-ev-inv`).
--
-- Foundation: the ITER-FORCE OFFER lemma.  A source-alphabet visible step of
-- a peer's react node (a loop `iter` head or a `succVC` mid derivative) lands
-- on the node's OFFERED continuation `succVC q at a` (the very expression the
-- fine mid positions are DEFINED by).  `step-target-*` reads off the offer
-- map at the fired event (via the manifest / `f*`-supplied force equality) so
-- non-firing events are refuted by `nothing-absurd`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( succVC; vis-ofC; CSProc; succVB; vis-ofB; BFProc )

-- the source-alphabet LTS instances (same module applications the peer
-- `renameMap-ev-reflect` reflects into, so their step types are convertible)
import Semantics.LTS {E = CS.CSEv} {I = ExtI CS.CSEv} as CSL
import Semantics.LTS {E = BF.BFEv} {I = ExtI BF.BFEv} as BFL

-- CS iter-force offer: `succVC q at a` is exactly the offered continuation
succVC-just : (q : CSProc) (at : AnyTypes CS.CSEv) (a : proj₁ at) {P′ : CSProc}
  → vis-ofC (PTree.force q) at a ≡ just P′ → succVC q at a ≡ P′
succVC-just q at a eq with vis-ofC (PTree.force q) at a
succVC-just q at a refl | just t = refl
succVC-just q at a ()   | nothing

-- CS: a visible source step lands on `succVC q (X , e) a`
succVC-inv : (q : CSProc) {X : Set 0ℓ} {e : CS.CSEv X} {a : X} {P′ : CSProc}
  → q CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e a)) ]─► P′
  → P′ ≡ succVC q (X , e) a
succVC-inv q {X} {e} {a} step with CSL.ev-inv step
... | v , τc , feq , veq =
      sym (succVC-just q (X , e) a (trans (cong (λ n → vis-ofC n (X , e) a) feq) veq))

-- CS: the fired offer entry at a KNOWN force (`refl` for a head / `f*` for a
-- mid); refutes a non-firing event via the reduced (`nothing`) offer map
step-target-CS : (q : CSProc)
    {V : (at : AnyTypes CS.CSEv) → ContinueType at (Maybe CSProc)}
    {T : (i : AnyTypes (ExtI CS.CSEv)) → ContinueType i (Maybe CSProc)}
    {X : Set 0ℓ} {e : CS.CSEv X} {a : X} {P′ : CSProc}
  → PTree.force q ≡ react V T
  → q CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e a)) ]─► P′
  → V (X , e) a ≡ just P′
step-target-CS q {V} {T} {X} {e} {a} feq step with CSL.ev-inv step
... | v , τc , feq′ , veq with react-injective (trans (sym feq) feq′)
...   | Veq , _ = trans (cong (λ w → w (X , e) a) Veq) veq

-- BF iter-force offer
succVB-just : (q : BFProc) (at : AnyTypes BF.BFEv) (a : proj₁ at) {P′ : BFProc}
  → vis-ofB (PTree.force q) at a ≡ just P′ → succVB q at a ≡ P′
succVB-just q at a eq with vis-ofB (PTree.force q) at a
succVB-just q at a refl | just t = refl
succVB-just q at a ()   | nothing

-- BF: a visible source step lands on `succVB q (X , e) a`
succVB-inv : (q : BFProc) {X : Set 0ℓ} {e : BF.BFEv X} {a : X} {P′ : BFProc}
  → q BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e a)) ]─► P′
  → P′ ≡ succVB q (X , e) a
succVB-inv q {X} {e} {a} step with BFL.ev-inv step
... | v , τc , feq , veq =
      sym (succVB-just q (X , e) a (trans (cong (λ n → vis-ofB n (X , e) a) feq) veq))

-- BF: the fired offer entry at a known force
step-target-BF : (q : BFProc)
    {V : (at : AnyTypes BF.BFEv) → ContinueType at (Maybe BFProc)}
    {T : (i : AnyTypes (ExtI BF.BFEv)) → ContinueType i (Maybe BFProc)}
    {X : Set 0ℓ} {e : BF.BFEv X} {a : X} {P′ : BFProc}
  → PTree.force q ≡ react V T
  → q BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e a)) ]─► P′
  → V (X , e) a ≡ just P′
step-target-BF q {V} {T} {X} {e} {a} feq step with BFL.ev-inv step
... | v , τc , feq′ , veq with react-injective (trans (sym feq) feq′)
...   | Veq , _ = trans (cong (λ w → w (X , e) a) Veq) veq

------------------------------------------------------------------------

------------------------------------------------------------------------
-- G2 — ChainSync CLIENT visible-event inversion (`decCSc-ev-inv`).
------------------------------------------------------------------------

-- extra event/payload constructors + value DecEq for the per-position menus
open import CSP.Examples.Cardano_network.Net p using
  ( sendCSRequestNext; sendCSFindIntersect; sendCSDone; sendCSAwaitReply
  ; sendCSRollForward; sendCSRollBackward; sendCSIntersectFound; sendCSIntersectNotFound
  ; recvCSRollforward; recvCSRollback; recvCSIntersectFound; recvCSIntersectNotFound
  ; reqCSRequestNext; reqCSFindIntersect )
open import CSP.Examples.Cardano_network.Data p using
  ( chainSync; keepAlive; blockFetch; txSubmission; leiosNotify; leiosFetch
  ; MsgCSRequestNext; MsgCSAwaitReply; MsgCSRollForward; MsgCSRollBackward
  ; MsgCSFindIntersect; MsgCSIntersectFound; MsgCSIntersectNotFound; MsgCSDone
  ; Point; Tip; DecEq-Header; DecEq-Tip; DecEq-Point )
open import CSP.Examples.Cardano_network.Base using ( FromInitiator )
open Params p using ( time₀; length₀ )
import Class.DecEq.Instances as DecEqI
import CSP.Rename {E₁ = CS.CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RenCS

instance
  DecEqO-H×T : DecEq (Header × Tip)
  DecEqO-H×T = DecEqI.DecEq-×
  DecEqO-P×T : DecEq (Point × Tip)
  DecEqO-P×T = DecEqI.DecEq-×

-- reduction bridges: the receiveCS-head firing lands on a mid position whose
-- own definition is a `succVC` STUCK on `l ≟ l`; `≟-yes-refl` unsticks both
-- sides (the head-value's first 3 components are wildcarded by `clientStep`)
brRF : (l : Link) (d : Dir) (h : Header) (t : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stCanAwait)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSRollForward h t)) ≡ decCSc-src l d (csRF1 h t)
brRF l d h t t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brRB : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stCanAwait)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)) ≡ decCSc-src l d (csRB1 pt tp)
brRB l d pt tp t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brAw : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stCanAwait)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync MsgCSAwaitReply) ≡ decCSc-src l d (csSil CS.stMustReply)
brAw l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brRF-MR : (l : Link) (d : Dir) (h : Header) (t : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stMustReply)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSRollForward h t)) ≡ decCSc-src l d (csRF1 h t)
brRF-MR l d h t t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brRB-MR : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stMustReply)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)) ≡ decCSc-src l d (csRB1 pt tp)
brRB-MR l d pt tp t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brIF : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stIntersect)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)) ≡ decCSc-src l d (csIF1 pt tp)
brIF l d pt tp t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brINF : (l : Link) (d : Dir) (tp : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stIntersect)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)) ≡ decCSc-src l d (csINF1 tp)
brINF l d tp t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

------------------------------------------------------------------------
-- GAP-A (ChainSync CLIENT) — per-peer concrete↔abstract simulation.  The
-- abstract twin `absCSc l d pos = tableSpec (…csCnxt…) (coarsenCSc pos)` fires
-- the SAME visible `(e,a)` to the coarsened successor.  `ιCS-inv-shape` pins
-- the renamed event's ι-image shape; each `ceqCSc*` witnesses that the abstract
-- `csCnxt` edge agrees with the coarsening (coarsen ∘ nxt COMMUTES), and `aCSc`
-- packages the agreement into the abstract `tableSpec` step.
------------------------------------------------------------------------

-- a renamed Net_Api event whose ι-preimage is a CS source event `e₁` is exactly
-- the ι-image `ιCS e₁` (recover `e₂ ≡ ιCS e₁` by casing the Net_Api channel)
ιCS-inv-shape : {X : Set 0ℓ} {e₂ : Net_Api Payload X} {e₁ : CS.CSEv X}
  → ιCS⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιCS e₁
ιCS-inv-shape {e₂ = input  _ _ N2N_ChainSync}    refl = refl
ιCS-inv-shape {e₂ = input  _ _ N2N_BlockFetch}   ()
ιCS-inv-shape {e₂ = input  _ _ N2N_TxSubmission} ()
ιCS-inv-shape {e₂ = input  _ _ N2N_KeepAlive}    ()
ιCS-inv-shape {e₂ = input  _ _ N2N_LeiosNotify}  ()
ιCS-inv-shape {e₂ = input  _ _ N2N_LeiosFetch}   ()
ιCS-inv-shape {e₂ = output _ _ N2N_ChainSync}    refl = refl
ιCS-inv-shape {e₂ = output _ _ N2N_BlockFetch}   ()
ιCS-inv-shape {e₂ = output _ _ N2N_TxSubmission} ()
ιCS-inv-shape {e₂ = output _ _ N2N_KeepAlive}    ()
ιCS-inv-shape {e₂ = output _ _ N2N_LeiosNotify}  ()
ιCS-inv-shape {e₂ = output _ _ N2N_LeiosFetch}   ()
ιCS-inv-shape {e₂ = done   _ _ N2N_ChainSync}    refl = refl
ιCS-inv-shape {e₂ = done   _ _ N2N_BlockFetch}   ()
ιCS-inv-shape {e₂ = done   _ _ N2N_TxSubmission} ()
ιCS-inv-shape {e₂ = done   _ _ N2N_KeepAlive}    ()
ιCS-inv-shape {e₂ = done   _ _ N2N_LeiosNotify}  ()
ιCS-inv-shape {e₂ = done   _ _ N2N_LeiosFetch}   ()
ιCS-inv-shape {e₂ = apiCS  _ _ _} refl = refl
ιCS-inv-shape {e₂ = sndmsg _ _ _} ()
ιCS-inv-shape {e₂ = rcvmsg _ _ _} ()
ιCS-inv-shape {e₂ = tx     _ _ _} ()
ιCS-inv-shape {e₂ = sndack _ _ _} ()
ιCS-inv-shape {e₂ = rcvack _ _ _} ()
ιCS-inv-shape {e₂ = ack    _ _ _} ()
ιCS-inv-shape {e₂ = apiBF  _ _ _} ()
ιCS-inv-shape {e₂ = apiTS  _ _ _} ()
ιCS-inv-shape {e₂ = apiKA  _ _ _} ()
ιCS-inv-shape {e₂ = apiLN  _ _ _} ()
ιCS-inv-shape {e₂ = apiLF  _ _ _} ()
ιCS-inv-shape {e₂ = break  _}     ()

-- package a `csCnxt` agreement into the abstract CS-client step (the abstract
-- peer is at a non-terminal coarsened position, so it offers the `nxt` react)
aCSc : (l : Link) (d : Dir) (pos pos′ : CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.csCfin (coarsenCSc pos) ≡ false
  → NS.csCnxt l d (coarsenCSc pos) (X , e) a ≡ just (coarsenCSc pos′)
  → absCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSc l d pos′
aCSc l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenCSc pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations (each: the abstract `csCnxt` fires the
-- SAME renamed event to the coarsened successor; `refl` after the `l/d`(+value)
-- `≟`-guards are unstuck)
ceqCSc01 : ∀ {a} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccIdle (_ , apiCS l d sendCSRequestNext) a ≡ just NS.ccWreq
ceqCSc01 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc02 : ∀ {ps} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccIdle (_ , apiCS l d sendCSFindIntersect) ps ≡ just (NS.ccWfi ps)
ceqCSc02 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc03 : ∀ {a} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccIdle (_ , apiCS l d sendCSDone) a ≡ just NS.ccWdone
ceqCSc03 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc04 : ∀ {t0 md ln} {h : Header} {t : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccAwait (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSRollForward h t)) ≡ just (NS.ccArf (h , t))
ceqCSc04 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc05 : ∀ {t0 md ln} {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccAwait (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)) ≡ just (NS.ccArb (pt , tp))
ceqCSc05 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc06 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccAwait (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync MsgCSAwaitReply) ≡ just NS.ccMust
ceqCSc06 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc07 : ∀ {t0 md ln} {h : Header} {t : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccMust (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSRollForward h t)) ≡ just (NS.ccArf (h , t))
ceqCSc07 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc08 : ∀ {t0 md ln} {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccMust (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)) ≡ just (NS.ccArb (pt , tp))
ceqCSc08 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc09 : ∀ {t0 md ln} {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccInt (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)) ≡ just (NS.ccAif (pt , tp))
ceqCSc09 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc10 : ∀ {t0 md ln} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccInt (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)) ≡ just (NS.ccAin tp)
ceqCSc10 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc11 : (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccWreq (_ , input l d N2N_ChainSync)
      (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just NS.ccAwait
ceqCSc11 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
ceqCSc12 : ∀ {ps} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccWfi ps) (_ , input l d N2N_ChainSync)
      (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just NS.ccInt
ceqCSc12 {ps} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
ceqCSc13 : (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccWdone (_ , input l d N2N_ChainSync)
      (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just NS.ccTerm
ceqCSc13 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
ceqCSc15 : ∀ {h : Header} {t : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccArf (h , t)) (_ , apiCS l d recvCSRollforward) (h , t) ≡ just NS.ccIdle
ceqCSc15 {h} {t} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl (h , t) = refl
ceqCSc16 : ∀ {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccArb (pt , tp)) (_ , apiCS l d recvCSRollback) (pt , tp) ≡ just NS.ccIdle
ceqCSc16 {pt} {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl (pt , tp) = refl
ceqCSc17 : ∀ {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccAif (pt , tp)) (_ , apiCS l d recvCSIntersectFound) (pt , tp) ≡ just NS.ccIdle
ceqCSc17 {pt} {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl (pt , tp) = refl
ceqCSc18 : ∀ {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccAin tp) (_ , apiCS l d recvCSIntersectNotFound) tp ≡ just NS.ccIdle
ceqCSc18 {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl tp = refl

-- SOURCE-side per-position ev inversion: a visible source step of a fine CS
-- client position lands on a representable fine position, AND the abstract
-- twin fires the same (renamed) event to the coarsened successor.
decCSc-src-ev-inv : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSc-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ CScPos ] (P′ ≡ decCSc-src l d pos′)
      × (absCSc l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absCSc l d pos′)
-- head stIdle : fires apiCSev sendCSRequestNext / FindIntersect / Done
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRequestNext} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csReqNext1 , succVC-inv (decCSc-src l d (csHead CS.stIdle)) s , aCSc l d (csHead CS.stIdle) csReqNext1 refl (ceqCSc01 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} {a} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csFindInt1 a , succVC-inv (decCSc-src l d (csHead CS.stIdle)) s , aCSc l d (csHead CS.stIdle) (csFindInt1 a) refl (ceqCSc02 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSDone} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csDone1 , succVC-inv (decCSc-src l d (csHead CS.stIdle)) s , aCSc l d (csHead CS.stIdle) csDone1 refl (ceqCSc03 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollForward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollBackward}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollforward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollback}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
-- head stCanAwait : fires receiveCS RollForward / RollBackward / AwaitReply
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRF1 h t , trans (succVC-inv (decCSc-src l d (csHead CS.stCanAwait)) s) (brRF l d h t t0 md ln) , aCSc l d (csHead CS.stCanAwait) (csRF1 h t) refl (ceqCSc04 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRB1 pt tp , trans (succVC-inv (decCSc-src l d (csHead CS.stCanAwait)) s) (brRB l d pt tp t0 md ln) , aCSc l d (csHead CS.stCanAwait) (csRB1 pt tp) refl (ceqCSc05 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csSil CS.stMustReply , trans (succVC-inv (decCSc-src l d (csHead CS.stCanAwait)) s) (brAw l d t0 md ln) , aCSc l d (csHead CS.stCanAwait) (csSil CS.stMustReply) refl (ceqCSc06 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
-- head stMustReply : fires receiveCS RollForward / RollBackward
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRF1 h t , trans (succVC-inv (decCSc-src l d (csHead CS.stMustReply)) s) (brRF-MR l d h t t0 md ln) , aCSc l d (csHead CS.stMustReply) (csRF1 h t) refl (ceqCSc07 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRB1 pt tp , trans (succVC-inv (decCSc-src l d (csHead CS.stMustReply)) s) (brRB-MR l d pt tp t0 md ln) , aCSc l d (csHead CS.stMustReply) (csRB1 pt tp) refl (ceqCSc08 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
-- head stIntersect : fires receiveCS IntersectFound / IntersectNotFound
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csIF1 pt tp , trans (succVC-inv (decCSc-src l d (csHead CS.stIntersect)) s) (brIF l d pt tp t0 md ln) , aCSc l d (csHead CS.stIntersect) (csIF1 pt tp) refl (ceqCSc09 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csINF1 tp , trans (succVC-inv (decCSc-src l d (csHead CS.stIntersect)) s) (brINF l d tp t0 md ln) , aCSc l d (csHead CS.stIntersect) (csINF1 tp) refl (ceqCSc10 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSc-src-ev-inv l d (csHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid csReqNext1 : fires sendCS payload → csSil stCanAwait
decCSc-src-ev-inv l d csReqNext1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stCanAwait , sym (just-injective offer) , aCSc l d csReqNext1 (csSil CS.stCanAwait) refl (ceqCSc11 l d)
decCSc-src-ev-inv l d csReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-ev-inv l d csReqNext1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-ev-inv l d csReqNext1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
-- mid csFindInt1 ps : fires sendCS payload → csSil stIntersect
decCSc-src-ev-inv l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIntersect , sym (just-injective offer) , aCSc l d (csFindInt1 ps) (csSil CS.stIntersect) refl (ceqCSc12 l d)
decCSc-src-ev-inv l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-ev-inv l d (csFindInt1 ps) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-ev-inv l d (csFindInt1 ps) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
-- mid csDone1 : fires sendCS payload → csSil stDone (client has no node-local done)
decCSc-src-ev-inv l d csDone1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stDone , sym (just-injective offer) , aCSc l d csDone1 (csSil CS.stDone) refl (ceqCSc13 l d)
decCSc-src-ev-inv l d csDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-ev-inv l d csDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-ev-inv l d csDone1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
-- mid csRF1 : fires apiCSev recvCSRollforward (h,t) → csSil stIdle
decCSc-src-ev-inv l d (csRF1 h t) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollforward) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (h , t)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIdle , sym (just-injective offer) , aCSc l d (csRF1 h t) (csSil CS.stIdle) refl (ceqCSc15 l d)
decCSc-src-ev-inv l d (csRF1 h t) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-ev-inv l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-ev-inv l d (csRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
-- mid csRB1 : fires apiCSev recvCSRollback (pt,tp) → csSil stIdle
decCSc-src-ev-inv l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollback) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIdle , sym (just-injective offer) , aCSc l d (csRB1 pt tp) (csSil CS.stIdle) refl (ceqCSc16 l d)
decCSc-src-ev-inv l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-ev-inv l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-ev-inv l d (csRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
-- mid csIF1 : fires apiCSev recvCSIntersectFound (pt,tp) → csSil stIdle
decCSc-src-ev-inv l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIdle , sym (just-injective offer) , aCSc l d (csIF1 pt tp) (csSil CS.stIdle) refl (ceqCSc17 l d)
decCSc-src-ev-inv l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-ev-inv l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-ev-inv l d (csIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
-- mid csINF1 : fires apiCSev recvCSIntersectNotFound tp → csSil stIdle
decCSc-src-ev-inv l d (csINF1 tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectNotFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ tp
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIdle , sym (just-injective offer) , aCSc l d (csINF1 tp) (csSil CS.stIdle) refl (ceqCSc18 l d)
decCSc-src-ev-inv l d (csINF1 tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-ev-inv l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-ev-inv l d (csINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
-- loop re-entry csSil : forces to `sil`, no visible step
decCSc-src-ev-inv l d (csSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- GAP-A (ChainSync CLIENT) per-peer simulation: reflect the renamed step to the
-- source FSM (keeping the ι-preimage), invert the source offer for the concrete
-- successor + the abstract twin's matching step, re-rename the concrete target,
-- and transport the abstract step onto the actual renamed event `e₂ ≡ ιCS e₁`.
simCSc : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pos′ ∈ CScPos ] (M ≡ decCSc l d pos′)
      × (absCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSc l d pos′)
simCSc l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decCSc-src-ev-inv l d pos srcStep | ιCS-inv-shape iota
...   | pos′ , P′eq , aStep | refl = pos′ , trans Meq (cong RenCS.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- G2 — ChainSync SERVER visible-event inversion (`decCSs-ev-inv`).
-- Dual of the client: `ssHead stIdle` RECEIVES on the wire; the other heads
-- SEND via api.  Same infra (succVC-inv / step-target-CS / RenCS / CSNO).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Base using ( FromResponder )
open import Data.List using ( List )

-- server-stIdle receive-firing bridges (target the mid positions, whose defs
-- are `succVC` stuck on `l ≟ l`; the received value's first 3 are wildcarded)
brSReq : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
       → succVC (decCSs-src l d (ssHead CS.stIdle)) (_ , CS.receiveCS l d)
                (t0 , md , ln , chainSync MsgCSRequestNext) ≡ decCSs-src l d ssReqNext1
brSReq l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brSFI : (l : Link) (d : Dir) (ps : List Point) (t0 : _) (md : _) (ln : _)
      → succVC (decCSs-src l d (ssHead CS.stIdle)) (_ , CS.receiveCS l d)
               (t0 , md , ln , chainSync (MsgCSFindIntersect ps)) ≡ decCSs-src l d (ssFindInt1 ps)
brSFI l d ps t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brSDN : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
      → succVC (decCSs-src l d (ssHead CS.stIdle)) (_ , CS.receiveCS l d)
               (t0 , md , ln , chainSync MsgCSDone) ≡ decCSs-src l d ssDone1
brSDN l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
-- server stMustReply reaches ssRF1/ssRB1 (defined via stCanAwait): bridge the state
brSRF-MR : (l : Link) (d : Dir) (a : Header × Tip)
  → succVC (decCSs-src l d (ssHead CS.stMustReply)) (_ , CS.apiCSev l d sendCSRollForward) a ≡ decCSs-src l d (ssRF1 (proj₁ a) (proj₂ a))
brSRF-MR l d a rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brSRB-MR : (l : Link) (d : Dir) (a : Point × Tip)
  → succVC (decCSs-src l d (ssHead CS.stMustReply)) (_ , CS.apiCSev l d sendCSRollBackward) a ≡ decCSs-src l d (ssRB1 (proj₁ a) (proj₂ a))
brSRB-MR l d a rewrite ≟-yes-refl l | ≟-yes-refl d = refl

------------------------------------------------------------------------
-- GAP-A (ChainSync SERVER) — per-peer concrete↔abstract simulation.  Dual of
-- the client: the abstract `csSnxt` table drives `absCSs l d pos`; `aCSs`
-- packages each `coarsen ∘ nxt` agreement (`ceqCSs*`) into the abstract step.
------------------------------------------------------------------------

-- package a `csSnxt` agreement into the abstract CS-server step
aCSs : (l : Link) (d : Dir) (pos pos′ : CSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.csSfin (coarsenCSs pos) ≡ false
  → NS.csSnxt l d (coarsenCSs pos) (X , e) a ≡ just (coarsenCSs pos′)
  → absCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSs l d pos′
aCSs l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenCSs pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations for the CS server
ceqCSs01 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csIdle (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync MsgCSRequestNext) ≡ just NS.csAreq
ceqCSs01 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs02 : ∀ {t0 md ln} {ps} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csIdle (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSFindIntersect ps)) ≡ just (NS.csAfi ps)
ceqCSs02 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs03 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csIdle (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync MsgCSDone) ≡ just NS.csDdone
ceqCSs03 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs04 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csCanAwait (_ , apiCS l d sendCSRollForward) a ≡ just (NS.csWrf a)
ceqCSs04 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs05 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csCanAwait (_ , apiCS l d sendCSRollBackward) a ≡ just (NS.csWrb a)
ceqCSs05 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs06 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csCanAwait (_ , apiCS l d sendCSAwaitReply) a ≡ just NS.csWar
ceqCSs06 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs07 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csMust (_ , apiCS l d sendCSRollForward) a ≡ just (NS.csWrf a)
ceqCSs07 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs08 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csMust (_ , apiCS l d sendCSRollBackward) a ≡ just (NS.csWrb a)
ceqCSs08 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs09 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csInt (_ , apiCS l d sendCSIntersectFound) a ≡ just (NS.csWif a)
ceqCSs09 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs10 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csInt (_ , apiCS l d sendCSIntersectNotFound) a ≡ just (NS.csWin a)
ceqCSs10 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs11 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csAreq (_ , apiCS l d reqCSRequestNext) a ≡ just NS.csCanAwait
ceqCSs11 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs12 : ∀ {ps} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csAfi ps) (_ , apiCS l d reqCSFindIntersect) ps ≡ just NS.csInt
ceqCSs12 {ps} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl ⦃ DecEqI.DecEq-List ⦃ DecEq-Point ⦄ ⦄ ps = refl
ceqCSs13 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csDdone (_ , done l d N2N_ChainSync) a ≡ just NS.csTerm
ceqCSs13 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs14 : ∀ {h : Header} {t : Tip} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csWrf (h , t)) (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just NS.csIdle
ceqCSs14 {h} {t} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
ceqCSs15 : ∀ {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csWrb (pt , tp)) (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just NS.csIdle
ceqCSs15 {pt} {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
ceqCSs16 : (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csWar (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just NS.csMust
ceqCSs16 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
ceqCSs17 : ∀ {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csWif (pt , tp)) (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just NS.csIdle
ceqCSs17 {pt} {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
ceqCSs18 : ∀ {tp : Tip} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csWin tp) (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just NS.csIdle
ceqCSs18 {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl

-- SOURCE-side per-position ev inversion for the CS server (+ the abstract twin's
-- matching step to the coarsened successor).
decCSs-src-ev-inv : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSs-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ CSsPos ] (P′ ≡ decCSs-src l d pos′)
      × (absCSs l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absCSs l d pos′)
-- head stIdle : receives RequestNext / FindIntersect / Done on the wire
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssReqNext1 , trans (succVC-inv (decCSs-src l d (ssHead CS.stIdle)) s) (brSReq l d t0 md ln) , aCSs l d (ssHead CS.stIdle) ssReqNext1 refl (ceqCSs01 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssFindInt1 ps , trans (succVC-inv (decCSs-src l d (ssHead CS.stIdle)) s) (brSFI l d ps t0 md ln) , aCSs l d (ssHead CS.stIdle) (ssFindInt1 ps) refl (ceqCSs02 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssDone1 , trans (succVC-inv (decCSs-src l d (ssHead CS.stIdle)) s) (brSDN l d t0 md ln) , aCSs l d (ssHead CS.stIdle) ssDone1 refl (ceqCSs03 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
-- head stCanAwait : sends RollForward / RollBackward / AwaitReply via api
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRF1 (proj₁ a) (proj₂ a) , succVC-inv (decCSs-src l d (ssHead CS.stCanAwait)) s , aCSs l d (ssHead CS.stCanAwait) (ssRF1 (proj₁ a) (proj₂ a)) refl (ceqCSs04 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRB1 (proj₁ a) (proj₂ a) , succVC-inv (decCSs-src l d (ssHead CS.stCanAwait)) s , aCSs l d (ssHead CS.stCanAwait) (ssRB1 (proj₁ a) (proj₂ a)) refl (ceqCSs05 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssAw1 , succVC-inv (decCSs-src l d (ssHead CS.stCanAwait)) s , aCSs l d (ssHead CS.stCanAwait) ssAw1 refl (ceqCSs06 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
-- head stMustReply : sends RollForward / RollBackward via api
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRF1 (proj₁ a) (proj₂ a) , trans (succVC-inv (decCSs-src l d (ssHead CS.stMustReply)) s) (brSRF-MR l d a) , aCSs l d (ssHead CS.stMustReply) (ssRF1 (proj₁ a) (proj₂ a)) refl (ceqCSs07 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRB1 (proj₁ a) (proj₂ a) , trans (succVC-inv (decCSs-src l d (ssHead CS.stMustReply)) s) (brSRB-MR l d a) , aCSs l d (ssHead CS.stMustReply) (ssRB1 (proj₁ a) (proj₂ a)) refl (ceqCSs08 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
-- head stIntersect : sends IntersectFound / IntersectNotFound via api
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssIF1 (proj₁ a) (proj₂ a) , succVC-inv (decCSs-src l d (ssHead CS.stIntersect)) s , aCSs l d (ssHead CS.stIntersect) (ssIF1 (proj₁ a) (proj₂ a)) refl (ceqCSs09 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssINF1 a , succVC-inv (decCSs-src l d (ssHead CS.stIntersect)) s , aCSs l d (ssHead CS.stIntersect) (ssINF1 a) refl (ceqCSs10 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollForward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollBackward}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollforward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollback}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSRequestNext}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSs-src-ev-inv l d (ssHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid ssReqNext1 : fires api reqCSRequestNext (Prefix₀) → ssSil stCanAwait
decCSs-src-ev-inv l d ssReqNext1 {e₁ = CS.apiCSev l' d' m} s with step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSRequestNext) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = ssSil CS.stCanAwait , sym (just-injective offer) , aCSs l d ssReqNext1 (ssSil CS.stCanAwait) refl (ceqCSs11 l d)
decCSs-src-ev-inv l d ssReqNext1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-ev-inv l d ssReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-ev-inv l d ssReqNext1 {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
-- mid ssFindInt1 ps : fires api reqCSFindIntersect ps (Output) → ssSil stIntersect
decCSs-src-ev-inv l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSFindIntersect) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ CS.DecEq-ListPoint ⦄ a ps
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIntersect , sym (just-injective offer) , aCSs l d (ssFindInt1 ps) (ssSil CS.stIntersect) refl (ceqCSs12 l d)
decCSs-src-ev-inv l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-ev-inv l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-ev-inv l d (ssFindInt1 ps) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
-- mid ssDone1 : fires doneCS (Prefix₀) → ssSil stDone
decCSs-src-ev-inv l d ssDone1 {e₁ = CS.doneCS l' d'} s with step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.doneCS l d) (_ , CS.doneCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = ssSil CS.stDone , sym (just-injective offer) , aCSs l d ssDone1 (ssSil CS.stDone) refl (ceqCSs13 l d)
decCSs-src-ev-inv l d ssDone1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-ev-inv l d ssDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-ev-inv l d ssDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
-- mid ssRF1 : fires sendCS payload → ssSil stIdle
decCSs-src-ev-inv l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIdle , sym (just-injective offer) , aCSs l d (ssRF1 h t) (ssSil CS.stIdle) refl (ceqCSs14 l d)
decCSs-src-ev-inv l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-ev-inv l d (ssRF1 h t) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-ev-inv l d (ssRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
-- mid ssRB1 : fires sendCS payload → ssSil stIdle
decCSs-src-ev-inv l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIdle , sym (just-injective offer) , aCSs l d (ssRB1 pt tp) (ssSil CS.stIdle) refl (ceqCSs15 l d)
decCSs-src-ev-inv l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-ev-inv l d (ssRB1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-ev-inv l d (ssRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
-- mid ssAw1 : fires sendCS payload → ssSil stMustReply
decCSs-src-ev-inv l d ssAw1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stMustReply , sym (just-injective offer) , aCSs l d ssAw1 (ssSil CS.stMustReply) refl (ceqCSs16 l d)
decCSs-src-ev-inv l d ssAw1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-ev-inv l d ssAw1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-ev-inv l d ssAw1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
-- mid ssIF1 : fires sendCS payload → ssSil stIdle
decCSs-src-ev-inv l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIdle , sym (just-injective offer) , aCSs l d (ssIF1 pt tp) (ssSil CS.stIdle) refl (ceqCSs17 l d)
decCSs-src-ev-inv l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-ev-inv l d (ssIF1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-ev-inv l d (ssIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
-- mid ssINF1 : fires sendCS payload → ssSil stIdle
decCSs-src-ev-inv l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIdle , sym (just-injective offer) , aCSs l d (ssINF1 tp) (ssSil CS.stIdle) refl (ceqCSs18 l d)
decCSs-src-ev-inv l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-ev-inv l d (ssINF1 tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-ev-inv l d (ssINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
-- loop re-entry ssSil : forces to `sil`, no visible step
decCSs-src-ev-inv l d (ssSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- GAP-A (ChainSync SERVER) per-peer simulation.
simCSs : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pos′ ∈ CSsPos ] (M ≡ decCSs l d pos′)
      × (absCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSs l d pos′)
simCSs l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decCSs-src-ev-inv l d pos srcStep | ιCS-inv-shape iota
...   | pos′ , P′eq , aStep | refl = pos′ , trans Meq (cong RenCS.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- G2 — BlockFetch CLIENT / SERVER visible-event inversions.
-- Same recipe over the BF alphabet (succVB-inv / step-target-BF / BFNO).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Net p using
  ( sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks
  ; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange )
open import CSP.Examples.Cardano_network.Data p using
  ( ChainRange; DecEq-ChainRange
  ; MsgRequestRange; MsgStartBatch; MsgNoBlocks; MsgBlock
  ; MsgBatchDone; MsgClientDone )
open Params p using ( Block; decBlock )
import CSP.Rename {E₁ = BF.BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF

-- BFc receive-firing bridges (stBusy / stStreaming heads → mid / sil positions)
brBcStart : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVB (decBFc-src l d (bcHead BF.stBusy)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch MsgStartBatch) ≡ decBFc-src l d (bcSil BF.stStreaming)
brBcStart l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brBcNoBlk : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVB (decBFc-src l d (bcHead BF.stBusy)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch MsgNoBlocks) ≡ decBFc-src l d (bcSil BF.stIdle)
brBcNoBlk l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brBcBlk : (l : Link) (d : Dir) (b : Block) (t0 : _) (md : _) (ln : _)
  → succVB (decBFc-src l d (bcHead BF.stStreaming)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch (MsgBlock b)) ≡ decBFc-src l d (bcBlk1 b)
brBcBlk l d b t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brBcBatch : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVB (decBFc-src l d (bcHead BF.stStreaming)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch MsgBatchDone) ≡ decBFc-src l d (bcSil BF.stIdle)
brBcBatch l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
-- BFs receive-firing bridges (stIdle head → mid positions)
brBsReq : (l : Link) (d : Dir) (r : ChainRange) (t0 : _) (md : _) (ln : _)
  → succVB (decBFs-src l d (bsHead BF.stIdle)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch (MsgRequestRange r)) ≡ decBFs-src l d (bsReq1 r)
brBsReq l d r t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brBsDone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVB (decBFs-src l d (bsHead BF.stIdle)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch MsgClientDone) ≡ decBFs-src l d bsDone1
brBsDone l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

------------------------------------------------------------------------
-- GAP-A (BlockFetch CLIENT / SERVER) — per-peer concrete↔abstract simulation.
-- `ιBF-inv-shape` pins the renamed event's ι-image; `aBFc`/`aBFs` package each
-- `coarsen ∘ nxt` agreement (`ceqBFc*`/`ceqBFs*`) into the abstract step.
------------------------------------------------------------------------

-- a renamed Net_Api event whose ι-preimage is a BF source event is its ι-image
ιBF-inv-shape : {X : Set 0ℓ} {e₂ : Net_Api Payload X} {e₁ : BF.BFEv X}
  → ιBF⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιBF e₁
ιBF-inv-shape {e₂ = input  _ _ N2N_BlockFetch}   refl = refl
ιBF-inv-shape {e₂ = input  _ _ N2N_ChainSync}    ()
ιBF-inv-shape {e₂ = input  _ _ N2N_TxSubmission} ()
ιBF-inv-shape {e₂ = input  _ _ N2N_KeepAlive}    ()
ιBF-inv-shape {e₂ = input  _ _ N2N_LeiosNotify}  ()
ιBF-inv-shape {e₂ = input  _ _ N2N_LeiosFetch}   ()
ιBF-inv-shape {e₂ = output _ _ N2N_BlockFetch}   refl = refl
ιBF-inv-shape {e₂ = output _ _ N2N_ChainSync}    ()
ιBF-inv-shape {e₂ = output _ _ N2N_TxSubmission} ()
ιBF-inv-shape {e₂ = output _ _ N2N_KeepAlive}    ()
ιBF-inv-shape {e₂ = output _ _ N2N_LeiosNotify}  ()
ιBF-inv-shape {e₂ = output _ _ N2N_LeiosFetch}   ()
ιBF-inv-shape {e₂ = done   _ _ N2N_BlockFetch}   refl = refl
ιBF-inv-shape {e₂ = done   _ _ N2N_ChainSync}    ()
ιBF-inv-shape {e₂ = done   _ _ N2N_TxSubmission} ()
ιBF-inv-shape {e₂ = done   _ _ N2N_KeepAlive}    ()
ιBF-inv-shape {e₂ = done   _ _ N2N_LeiosNotify}  ()
ιBF-inv-shape {e₂ = done   _ _ N2N_LeiosFetch}   ()
ιBF-inv-shape {e₂ = apiBF  _ _ _} refl = refl
ιBF-inv-shape {e₂ = sndmsg _ _ _} ()
ιBF-inv-shape {e₂ = rcvmsg _ _ _} ()
ιBF-inv-shape {e₂ = tx     _ _ _} ()
ιBF-inv-shape {e₂ = sndack _ _ _} ()
ιBF-inv-shape {e₂ = rcvack _ _ _} ()
ιBF-inv-shape {e₂ = ack    _ _ _} ()
ιBF-inv-shape {e₂ = apiCS  _ _ _} ()
ιBF-inv-shape {e₂ = apiTS  _ _ _} ()
ιBF-inv-shape {e₂ = apiKA  _ _ _} ()
ιBF-inv-shape {e₂ = apiLN  _ _ _} ()
ιBF-inv-shape {e₂ = apiLF  _ _ _} ()
ιBF-inv-shape {e₂ = break  _}     ()

-- package a `bfCnxt` agreement into the abstract BF-client step
aBFc : (l : Link) (d : Dir) (pos pos′ : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.bfCfin (coarsenBFc pos) ≡ false
  → NS.bfCnxt l d (coarsenBFc pos) (X , e) a ≡ just (coarsenBFc pos′)
  → absBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFc l d pos′
aBFc l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenBFc pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations for the BF client
ceqBFc01 : ∀ {r} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcIdle (_ , apiBF l d sendBFRequestRange) r ≡ just (NS.bcWrr r)
ceqBFc01 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc02 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcIdle (_ , apiBF l d sendBFClientDone) a ≡ just NS.bcWcd
ceqBFc02 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc03 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcBusy (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch MsgStartBatch) ≡ just NS.bcStream
ceqBFc03 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc04 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcBusy (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch MsgNoBlocks) ≡ just NS.bcIdle
ceqBFc04 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc05 : ∀ {t0 md ln} {b : Block} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcStream (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch (MsgBlock b)) ≡ just (NS.bcAblk b)
ceqBFc05 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc06 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcStream (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch MsgBatchDone) ≡ just NS.bcIdle
ceqBFc06 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc07 : ∀ {r} (l : Link) (d : Dir)
  → NS.bfCnxt l d (NS.bcWrr r) (_ , input l d N2N_BlockFetch)
      (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just NS.bcBusy
ceqBFc07 {r} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
ceqBFc08 : (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcWcd (_ , input l d N2N_BlockFetch)
      (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just NS.bcTerm
ceqBFc08 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
ceqBFc10 : ∀ {b : Block} (l : Link) (d : Dir)
  → NS.bfCnxt l d (NS.bcAblk b) (_ , apiBF l d recvBFBlock) b ≡ just NS.bcStream
ceqBFc10 {b} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl ⦃ decBlock ⦄ b = refl

-- SOURCE-side per-position ev inversion for the BF client (+ abstract twin step).
decBFc-src-ev-inv : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFc-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ BFcPos ] (P′ ≡ decBFc-src l d pos′)
      × (absBFc l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBFc l d pos′)
-- head stIdle : sends RequestRange / ClientDone via api
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFRequestRange} {a} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcReq1 a , succVB-inv (decBFc-src l d (bcHead BF.stIdle)) s , aBFc l d (bcHead BF.stIdle) (bcReq1 a) refl (ceqBFc01 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFClientDone} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcDone1 , succVB-inv (decBFc-src l d (bcHead BF.stIdle)) s , aBFc l d (bcHead BF.stIdle) bcDone1 refl (ceqBFc02 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' recvBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' reqBFRange}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
-- head stBusy : receives StartBatch / NoBlocks (both go straight to a re-entry sil)
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stStreaming , trans (succVB-inv (decBFc-src l d (bcHead BF.stBusy)) s) (brBcStart l d t0 md ln) , aBFc l d (bcHead BF.stBusy) (bcSil BF.stStreaming) refl (ceqBFc03 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stIdle , trans (succVB-inv (decBFc-src l d (bcHead BF.stBusy)) s) (brBcNoBlk l d t0 md ln) , aBFc l d (bcHead BF.stBusy) (bcSil BF.stIdle) refl (ceqBFc04 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
-- head stStreaming : receives Block (→ bcBlk1) / BatchDone (→ re-entry sil)
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcBlk1 b , trans (succVB-inv (decBFc-src l d (bcHead BF.stStreaming)) s) (brBcBlk l d b t0 md ln) , aBFc l d (bcHead BF.stStreaming) (bcBlk1 b) refl (ceqBFc05 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stIdle , trans (succVB-inv (decBFc-src l d (bcHead BF.stStreaming)) s) (brBcBatch l d t0 md ln) , aBFc l d (bcHead BF.stStreaming) (bcSil BF.stIdle) refl (ceqBFc06 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
-- head stDone : `ret`, no visible step
decBFc-src-ev-inv l d (bcHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bcReq1 r : fires sendBF payload → bcSil stBusy
decBFc-src-ev-inv l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bcSil BF.stBusy , sym (just-injective offer) , aBFc l d (bcReq1 r) (bcSil BF.stBusy) refl (ceqBFc07 l d)
decBFc-src-ev-inv l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-ev-inv l d (bcReq1 r) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-ev-inv l d (bcReq1 r) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
-- mid bcDone1 : fires sendBF payload → bcSil stDone (client has no node-local done)
decBFc-src-ev-inv l d bcDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bcSil BF.stDone , sym (just-injective offer) , aBFc l d bcDone1 (bcSil BF.stDone) refl (ceqBFc08 l d)
decBFc-src-ev-inv l d bcDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-ev-inv l d bcDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-ev-inv l d bcDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
-- mid bcBlk1 b : fires apiBFev recvBFBlock b → bcSil stStreaming
decBFc-src-ev-inv l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d recvBFBlock) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bcSil BF.stStreaming , sym (just-injective offer) , aBFc l d (bcBlk1 b) (bcSil BF.stStreaming) refl (ceqBFc10 l d)
decBFc-src-ev-inv l d (bcBlk1 b) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-ev-inv l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-ev-inv l d (bcBlk1 b) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
-- loop re-entry bcSil : forces to `sil`, no visible step
decBFc-src-ev-inv l d (bcSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- GAP-A (BlockFetch CLIENT) per-peer simulation.
simBFc : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pos′ ∈ BFcPos ] (M ≡ decBFc l d pos′)
      × (absBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFc l d pos′)
simBFc l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decBFc-src-ev-inv l d pos srcStep | ιBF-inv-shape iota
...   | pos′ , P′eq , aStep | refl = pos′ , trans Meq (cong RenBF.renameMap P′eq) , aStep

-- package a `bfSnxt` agreement into the abstract BF-server step
aBFs : (l : Link) (d : Dir) (pos pos′ : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.bfSfin (coarsenBFs pos) ≡ false
  → NS.bfSnxt l d (coarsenBFs pos) (X , e) a ≡ just (coarsenBFs pos′)
  → absBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFs l d pos′
aBFs l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenBFs pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations for the BF server
ceqBFs01 : ∀ {t0 md ln} {r} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsIdle (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch (MsgRequestRange r)) ≡ just (NS.bsAreq r)
ceqBFs01 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs02 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsIdle (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch MsgClientDone) ≡ just NS.bsDdone
ceqBFs02 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs03 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsBusy (_ , apiBF l d sendBFStartBatch) a ≡ just NS.bsWsb
ceqBFs03 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs04 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsBusy (_ , apiBF l d sendBFNoBlocks) a ≡ just NS.bsWnb
ceqBFs04 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs05 : ∀ {b : Block} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsStream (_ , apiBF l d sendBFBlock) b ≡ just (NS.bsWblk b)
ceqBFs05 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs06 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsStream (_ , apiBF l d sendBFBatchDone) a ≡ just NS.bsWbd
ceqBFs06 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs07 : ∀ {r} (l : Link) (d : Dir)
  → NS.bfSnxt l d (NS.bsAreq r) (_ , apiBF l d reqBFRange) r ≡ just NS.bsBusy
ceqBFs07 {r} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
ceqBFs08 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsDdone (_ , done l d N2N_BlockFetch) a ≡ just NS.bsTerm
ceqBFs08 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs09 : (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsWsb (_ , input l d N2N_BlockFetch)
      (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just NS.bsStream
ceqBFs09 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
ceqBFs10 : (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsWnb (_ , input l d N2N_BlockFetch)
      (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just NS.bsIdle
ceqBFs10 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
ceqBFs11 : ∀ {b : Block} (l : Link) (d : Dir)
  → NS.bfSnxt l d (NS.bsWblk b) (_ , input l d N2N_BlockFetch)
      (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just NS.bsStream
ceqBFs11 {b} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
ceqBFs12 : (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsWbd (_ , input l d N2N_BlockFetch)
      (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just NS.bsIdle
ceqBFs12 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl

-- SOURCE-side per-position ev inversion for the BF server (+ abstract twin step).
decBFs-src-ev-inv : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFs-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ BFsPos ] (P′ ≡ decBFs-src l d pos′)
      × (absBFs l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBFs l d pos′)
-- head stIdle : receives RequestRange (→ bsReq1) / ClientDone (→ bsDone1)
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsReq1 r , trans (succVB-inv (decBFs-src l d (bsHead BF.stIdle)) s) (brBsReq l d r t0 md ln) , aBFs l d (bsHead BF.stIdle) (bsReq1 r) refl (ceqBFs01 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsDone1 , trans (succVB-inv (decBFs-src l d (bsHead BF.stIdle)) s) (brBsDone l d t0 md ln) , aBFs l d (bsHead BF.stIdle) bsDone1 refl (ceqBFs02 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
-- head stBusy : sends StartBatch (→ bsStart1) / NoBlocks (→ bsNoBlk1) via api
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsStart1 , succVB-inv (decBFs-src l d (bsHead BF.stBusy)) s , aBFs l d (bsHead BF.stBusy) bsStart1 refl (ceqBFs03 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsNoBlk1 , succVB-inv (decBFs-src l d (bsHead BF.stBusy)) s , aBFs l d (bsHead BF.stBusy) bsNoBlk1 refl (ceqBFs04 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBatchDone}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
-- head stStreaming : sends Block (→ bsBlk1) / BatchDone (→ bsBatchDone1) via api
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBlock} {a} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsBlk1 a , succVB-inv (decBFs-src l d (bsHead BF.stStreaming)) s , aBFs l d (bsHead BF.stStreaming) (bsBlk1 a) refl (ceqBFs05 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBatchDone} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsBatchDone1 , succVB-inv (decBFs-src l d (bsHead BF.stStreaming)) s , aBFs l d (bsHead BF.stStreaming) bsBatchDone1 refl (ceqBFs06 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFStartBatch}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}     s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
-- head stDone : `ret`
decBFs-src-ev-inv l d (bsHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bsReq1 r : fires api reqBFRange r (Output) → bsSil stBusy
decBFs-src-ev-inv l d (bsReq1 r) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d reqBFRange) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stBusy , sym (just-injective offer) , aBFs l d (bsReq1 r) (bsSil BF.stBusy) refl (ceqBFs07 l d)
decBFs-src-ev-inv l d (bsReq1 r) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-ev-inv l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-ev-inv l d (bsReq1 r) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
-- mid bsDone1 : fires doneBF (Prefix₀) → bsSil stDone
decBFs-src-ev-inv l d bsDone1 {e₁ = BF.doneBF l' d'} s with step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.doneBF l d) (_ , BF.doneBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = bsSil BF.stDone , sym (just-injective offer) , aBFs l d bsDone1 (bsSil BF.stDone) refl (ceqBFs08 l d)
decBFs-src-ev-inv l d bsDone1 {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-ev-inv l d bsDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-ev-inv l d bsDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
-- mid bsStart1 : fires sendBF payload → bsSil stStreaming
decBFs-src-ev-inv l d bsStart1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stStreaming , sym (just-injective offer) , aBFs l d bsStart1 (bsSil BF.stStreaming) refl (ceqBFs09 l d)
decBFs-src-ev-inv l d bsStart1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-ev-inv l d bsStart1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-ev-inv l d bsStart1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
-- mid bsNoBlk1 : fires sendBF payload → bsSil stIdle
decBFs-src-ev-inv l d bsNoBlk1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stIdle , sym (just-injective offer) , aBFs l d bsNoBlk1 (bsSil BF.stIdle) refl (ceqBFs10 l d)
decBFs-src-ev-inv l d bsNoBlk1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-ev-inv l d bsNoBlk1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-ev-inv l d bsNoBlk1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
-- mid bsBlk1 b : fires sendBF payload → bsSil stStreaming
decBFs-src-ev-inv l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stStreaming , sym (just-injective offer) , aBFs l d (bsBlk1 b) (bsSil BF.stStreaming) refl (ceqBFs11 l d)
decBFs-src-ev-inv l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-ev-inv l d (bsBlk1 b) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-ev-inv l d (bsBlk1 b) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
-- mid bsBatchDone1 : fires sendBF payload → bsSil stIdle
decBFs-src-ev-inv l d bsBatchDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stIdle , sym (just-injective offer) , aBFs l d bsBatchDone1 (bsSil BF.stIdle) refl (ceqBFs12 l d)
decBFs-src-ev-inv l d bsBatchDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-ev-inv l d bsBatchDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-ev-inv l d bsBatchDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
-- loop re-entry bsSil : forces to `sil`, no visible step
decBFs-src-ev-inv l d (bsSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- GAP-A (BlockFetch SERVER) per-peer simulation.
simBFs : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pos′ ∈ BFsPos ] (M ≡ decBFs l d pos′)
      × (absBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFs l d pos′)
simBFs l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decBFs-src-ev-inv l d pos srcStep | ιBF-inv-shape iota
...   | pos′ , P′eq , aStep | refl = pos′ , trans Meq (cong RenBF.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- GAP-B FOUNDATION — inert-peer channel DISJOINTNESS (the non-offer leaves).
--
-- Unlike the τ routing (where the eight inert KA/TS/LN/LF peers are refuted
-- UNCONDITIONALLY by `*-no-τ`), an ev/io bundle peel cannot refute an inert
-- peer outright — each inert peer DOES offer its OWN protocol's visible/io
-- events.  So the ev/io peel is per-protocol: once the fired event is KNOWN to
-- be a ChainSync- or BlockFetch-channel event, the eight inert peers (and the
-- opposite driven protocol's pair) are refuted by NON-OFFER.  Each inert peer
-- is a renamed FSM `RenXX.renameMap (…StClient l d)`, and `ιXX⁻¹` sends every
-- FOREIGN (non-XX) channel to `nothing`, so `renameMap-noOffer-χ …refl` gives
-- the non-offer at ANY foreign event `e₂` with `ιXX⁻¹ e₂ ≡ nothing` (both io
-- channels `input/output _ _ N2N_{ChainSync,BlockFetch}` and the api events).
-- These are exactly the `evBoth`-refutation witnesses `bundle-ev-inv` consumes.
------------------------------------------------------------------------

-- SysStep qualified (its `RenNO` parameterised module is not brought in by the
-- `using` open above — a module member needs a qualified path)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep as SStep

-- RenNO instances for the four inert protocols (mirror SysStep's `CSNO`/`BFNO`;
-- the RenTC `KANO`/… names above are for the τ-freedom no-τ transport)
module KANOff = SStep.RenNO ιKA ιKA⁻¹ ιKA-linv
module TSNOff = SStep.RenNO ιTS ιTS⁻¹ ιTS-linv
module LNNOff = SStep.RenNO ιLN ιLN⁻¹ ιLN-linv
module LFNOff = SStep.RenNO ιLF ιLF⁻¹ ιLF-linv

-- KA client / server: no offer of any event whose ιKA-preimage is `nothing`
KAclientA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιKA⁻¹ e ≡ nothing → ¬ IoOffers (KAclientA l d) e a
KAclientA-noOffer l d eqn = KANOff.renameMap-noOffer-χ (KAclientStClient l d) eqn
KAserverA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιKA⁻¹ e ≡ nothing → ¬ IoOffers (KAserverA l d) e a
KAserverA-noOffer l d eqn = KANOff.renameMap-noOffer-χ (KAserverStClient l d) eqn

-- TS client / server: no offer of any event whose ιTS-preimage is `nothing`
TSclientA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιTS⁻¹ e ≡ nothing → ¬ IoOffers (TSclientA l d) e a
TSclientA-noOffer l d eqn = TSNOff.renameMap-noOffer-χ (TSclientStClient l d) eqn
TSserverA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιTS⁻¹ e ≡ nothing → ¬ IoOffers (TSserverA l d) e a
TSserverA-noOffer l d eqn = TSNOff.renameMap-noOffer-χ (TSserverStClient l d) eqn

-- generalised (position-independent) TS non-offers: at ANY tracked position a
-- TxSubmission peer offers only TS-channel events, so a foreign-channel event
-- (`ιTS⁻¹ e ≡ nothing`) is refused (channel mismatch survives the threading)
decTSc-noOffer : (l : Link) (d : Dir) (pos : TScPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιTS⁻¹ e ≡ nothing → ¬ IoOffers (decTSc l d pos) e a
decTSc-noOffer l d pos eqn = TSNOff.renameMap-noOffer-χ (decTSc-src l d pos) eqn
decTSs-noOffer : (l : Link) (d : Dir) (pos : TSsPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιTS⁻¹ e ≡ nothing → ¬ IoOffers (decTSs l d pos) e a
decTSs-noOffer l d pos eqn = TSNOff.renameMap-noOffer-χ (decTSs-src l d pos) eqn

-- position-general KA non-offer at a foreign channel (channel mismatch survives the threading)
decKAc-noOffer : (l : Link) (d : Dir) (pos : KAcPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιKA⁻¹ e ≡ nothing → ¬ IoOffers (decKAc l d pos) e a
decKAc-noOffer l d pos eqn = KANOff.renameMap-noOffer-χ (decKAc-src l d pos) eqn
decKAs-noOffer : (l : Link) (d : Dir) (pos : KAsPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιKA⁻¹ e ≡ nothing → ¬ IoOffers (decKAs l d pos) e a
decKAs-noOffer l d pos eqn = KANOff.renameMap-noOffer-χ (decKAs-src l d pos) eqn

-- position-general LN non-offer at a foreign channel (channel mismatch survives the threading)
decLNc-noOffer : (l : Link) (d : Dir) (pos : LNcPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLN⁻¹ e ≡ nothing → ¬ IoOffers (decLNc l d pos) e a
decLNc-noOffer l d pos eqn = LNNOff.renameMap-noOffer-χ (decLNc-src l d pos) eqn
decLNs-noOffer : (l : Link) (d : Dir) (pos : LNsPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLN⁻¹ e ≡ nothing → ¬ IoOffers (decLNs l d pos) e a
decLNs-noOffer l d pos eqn = LNNOff.renameMap-noOffer-χ (decLNs-src l d pos) eqn

-- LN client / server: no offer of any event whose ιLN-preimage is `nothing`
LNclientA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLN⁻¹ e ≡ nothing → ¬ IoOffers (LNclientA l d) e a
LNclientA-noOffer l d eqn = LNNOff.renameMap-noOffer-χ (LNclientStClient l d) eqn
LNserverA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLN⁻¹ e ≡ nothing → ¬ IoOffers (LNserverA l d) e a
LNserverA-noOffer l d eqn = LNNOff.renameMap-noOffer-χ (LNserverStClient l d) eqn

-- LF client / server: no offer of any event whose ιLF-preimage is `nothing`
LFclientA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLF⁻¹ e ≡ nothing → ¬ IoOffers (LFclientA l d) e a
LFclientA-noOffer l d eqn = LFNOff.renameMap-noOffer-χ (LFclientStClient l d) eqn
LFserverA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLF⁻¹ e ≡ nothing → ¬ IoOffers (LFserverA l d) e a
LFserverA-noOffer l d eqn = LFNOff.renameMap-noOffer-χ (LFserverStClient l d) eqn

------------------------------------------------------------------------
-- GAP-B L2 — concrete same-protocol disjointness (CSc↔CSs, BFc↔BFs).
-- The two driven peers of a protocol sit at DIFFERENT directions (`cl ≠ sv`
-- in every node bundle).  Every event a peer at direction `d` fires carries
-- `d` as its Net_Api direction component, so the same event cannot be fired
-- by both a `cl`-peer and an `sv`-peer — refuting the `⦀`-evBoth the bundle
-- ev-peel would otherwise leave as an overlap node.
------------------------------------------------------------------------

-- the direction component of a ChainSync source event
csEvDir : {X : Set 0ℓ} → CS.CSEv X → Dir
csEvDir (CS.sendCS l d)    = d
csEvDir (CS.receiveCS l d) = d
csEvDir (CS.apiCSev l d m) = d
csEvDir (CS.doneCS l d)    = d

-- the direction component of a BlockFetch source event
bfEvDir : {X : Set 0ℓ} → BF.BFEv X → Dir
bfEvDir (BF.sendBF l d)    = d
bfEvDir (BF.receiveBF l d) = d
bfEvDir (BF.apiBFev l d m) = d
bfEvDir (BF.doneBF l d)    = d
-- L2: decCSc-src-dir — the visible source step of a fine position fires
-- an event whose direction component is `d` (csEvDir extracts it).
decCSc-src-dir : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSc-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → csEvDir e₁ ≡ d
-- head stIdle : fires apiCSev sendCSRequestNext / FindIntersect / Done
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRequestNext} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} {a} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSDone} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollForward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollBackward}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollforward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollback}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
-- head stCanAwait : fires receiveCS RollForward / RollBackward / AwaitReply
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
-- head stMustReply : fires receiveCS RollForward / RollBackward
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
-- head stIntersect : fires receiveCS IntersectFound / IntersectNotFound
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSc-src-dir l d (csHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid csReqNext1 : fires sendCS payload → csSil stCanAwait
decCSc-src-dir l d csReqNext1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d csReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-dir l d csReqNext1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-dir l d csReqNext1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
-- mid csFindInt1 ps : fires sendCS payload → csSil stIntersect
decCSc-src-dir l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-dir l d (csFindInt1 ps) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-dir l d (csFindInt1 ps) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
-- mid csDone1 : fires sendCS payload → csSil stDone (client has no node-local done)
decCSc-src-dir l d csDone1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d csDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-dir l d csDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-dir l d csDone1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
-- mid csRF1 : fires apiCSev recvCSRollforward (h,t) → csSil stIdle
decCSc-src-dir l d (csRF1 h t) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollforward) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (h , t)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csRF1 h t) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-dir l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-dir l d (csRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
-- mid csRB1 : fires apiCSev recvCSRollback (pt,tp) → csSil stIdle
decCSc-src-dir l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollback) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-dir l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-dir l d (csRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
-- mid csIF1 : fires apiCSev recvCSIntersectFound (pt,tp) → csSil stIdle
decCSc-src-dir l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-dir l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-dir l d (csIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
-- mid csINF1 : fires apiCSev recvCSIntersectNotFound tp → csSil stIdle
decCSc-src-dir l d (csINF1 tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectNotFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ tp
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csINF1 tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-dir l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-dir l d (csINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
-- loop re-entry csSil : forces to `sil`, no visible step
decCSc-src-dir l d (csSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- L2: decCSs-src-dir — the visible source step of a fine position fires
-- an event whose direction component is `d` (csEvDir extracts it).
decCSs-src-dir : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSs-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → csEvDir e₁ ≡ d
-- head stIdle : receives RequestNext / FindIntersect / Done on the wire
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
-- head stCanAwait : sends RollForward / RollBackward / AwaitReply via api
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
-- head stMustReply : sends RollForward / RollBackward via api
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
-- head stIntersect : sends IntersectFound / IntersectNotFound via api
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollForward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollBackward}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollforward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollback}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSRequestNext}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSs-src-dir l d (ssHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid ssReqNext1 : fires api reqCSRequestNext (Prefix₀) → ssSil stCanAwait
decCSs-src-dir l d ssReqNext1 {e₁ = CS.apiCSev l' d' m} s with step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSRequestNext) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decCSs-src-dir l d ssReqNext1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-dir l d ssReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-dir l d ssReqNext1 {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
-- mid ssFindInt1 ps : fires api reqCSFindIntersect ps (Output) → ssSil stIntersect
decCSs-src-dir l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSFindIntersect) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ CS.DecEq-ListPoint ⦄ a ps
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-dir l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-dir l d (ssFindInt1 ps) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
-- mid ssDone1 : fires doneCS (Prefix₀) → ssSil stDone
decCSs-src-dir l d ssDone1 {e₁ = CS.doneCS l' d'} s with step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.doneCS l d) (_ , CS.doneCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decCSs-src-dir l d ssDone1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-dir l d ssDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-dir l d ssDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
-- mid ssRF1 : fires sendCS payload → ssSil stIdle
decCSs-src-dir l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-dir l d (ssRF1 h t) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-dir l d (ssRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
-- mid ssRB1 : fires sendCS payload → ssSil stIdle
decCSs-src-dir l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-dir l d (ssRB1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-dir l d (ssRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
-- mid ssAw1 : fires sendCS payload → ssSil stMustReply
decCSs-src-dir l d ssAw1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d ssAw1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-dir l d ssAw1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-dir l d ssAw1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
-- mid ssIF1 : fires sendCS payload → ssSil stIdle
decCSs-src-dir l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-dir l d (ssIF1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-dir l d (ssIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
-- mid ssINF1 : fires sendCS payload → ssSil stIdle
decCSs-src-dir l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-dir l d (ssINF1 tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-dir l d (ssINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
-- loop re-entry ssSil : forces to `sil`, no visible step
decCSs-src-dir l d (ssSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- L2: decBFc-src-dir — the visible source step of a fine position fires
-- an event whose direction component is `d` (bfEvDir extracts it).
decBFc-src-dir : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFc-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → bfEvDir e₁ ≡ d
-- head stIdle : sends RequestRange / ClientDone via api
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFRequestRange} {a} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFClientDone} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' recvBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' reqBFRange}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
-- head stBusy : receives StartBatch / NoBlocks (both go straight to a re-entry sil)
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
-- head stStreaming : receives Block (→ bcBlk1) / BatchDone (→ re-entry sil)
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
-- head stDone : `ret`, no visible step
decBFc-src-dir l d (bcHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bcReq1 r : fires sendBF payload → bcSil stBusy
decBFc-src-dir l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-dir l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-dir l d (bcReq1 r) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-dir l d (bcReq1 r) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
-- mid bcDone1 : fires sendBF payload → bcSil stDone
decBFc-src-dir l d bcDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-dir l d bcDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-dir l d bcDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-dir l d bcDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
-- mid bcBlk1 b : fires apiBFev recvBFBlock b → bcSil stStreaming
decBFc-src-dir l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d recvBFBlock) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-dir l d (bcBlk1 b) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-dir l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-dir l d (bcBlk1 b) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
-- loop re-entry bcSil : forces to `sil`, no visible step
decBFc-src-dir l d (bcSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- L2: decBFs-src-dir — the visible source step of a fine position fires
-- an event whose direction component is `d` (bfEvDir extracts it).
decBFs-src-dir : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFs-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → bfEvDir e₁ ≡ d
-- head stIdle : receives RequestRange (→ bsReq1) / ClientDone (→ bsDone1)
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
-- head stBusy : sends StartBatch (→ bsStart1) / NoBlocks (→ bsNoBlk1) via api
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBatchDone}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
-- head stStreaming : sends Block (→ bsBlk1) / BatchDone (→ bsBatchDone1) via api
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBlock} {a} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBatchDone} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFStartBatch}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}     s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
-- head stDone : `ret`
decBFs-src-dir l d (bsHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bsReq1 r : fires api reqBFRange r (Output) → bsSil stBusy
decBFs-src-dir l d (bsReq1 r) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d reqBFRange) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d (bsReq1 r) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-dir l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-dir l d (bsReq1 r) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
-- mid bsDone1 : fires doneBF (Prefix₀) → bsSil stDone
decBFs-src-dir l d bsDone1 {e₁ = BF.doneBF l' d'} s with step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.doneBF l d) (_ , BF.doneBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decBFs-src-dir l d bsDone1 {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-dir l d bsDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-dir l d bsDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
-- mid bsStart1 : fires sendBF payload → bsSil stStreaming
decBFs-src-dir l d bsStart1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d bsStart1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-dir l d bsStart1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-dir l d bsStart1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
-- mid bsNoBlk1 : fires sendBF payload → bsSil stIdle
decBFs-src-dir l d bsNoBlk1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d bsNoBlk1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-dir l d bsNoBlk1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-dir l d bsNoBlk1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
-- mid bsBlk1 b : fires sendBF payload → bsSil stStreaming
decBFs-src-dir l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-dir l d (bsBlk1 b) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-dir l d (bsBlk1 b) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
-- mid bsBatchDone1 : fires sendBF payload → bsSil stIdle
decBFs-src-dir l d bsBatchDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d bsBatchDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-dir l d bsBatchDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-dir l d bsBatchDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
-- loop re-entry bsSil : forces to `sil`, no visible step
decBFs-src-dir l d (bsSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()


-- a Net_Api event carrying direction `d` in its channel component (exactly the
-- constructor shapes the CS/BF peers emit under ιCS/ιBF)
data ApiHasDir (d : Dir) : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  ahIn   : ∀ {l ch} → ApiHasDir d (input  l d ch)
  ahOut  : ∀ {l ch} → ApiHasDir d (output l d ch)
  ahDone : ∀ {l ch} → ApiHasDir d (done   l d ch)
  ahCS   : ∀ {l m}  → ApiHasDir d (apiCS  l d m)
  ahBF   : ∀ {l m}  → ApiHasDir d (apiBF  l d m)

-- the direction of a fixed event is unique (both witnesses pin the same slot)
apiDir-inj : {X : Set 0ℓ} {e : Net_Api Payload X} {d d′ : Dir}
  → ApiHasDir d e → ApiHasDir d′ e → d ≡ d′
apiDir-inj ahIn   ahIn   = refl
apiDir-inj ahOut  ahOut  = refl
apiDir-inj ahDone ahDone = refl
apiDir-inj ahCS   ahCS   = refl
apiDir-inj ahBF   ahBF   = refl

-- ιCS carries the source direction into the Net_Api event
csApiDir : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ApiHasDir (csEvDir e₁) (ιCS e₁)
csApiDir (CS.sendCS l d)    = ahIn
csApiDir (CS.receiveCS l d) = ahOut
csApiDir (CS.apiCSev l d m) = ahCS
csApiDir (CS.doneCS l d)    = ahDone

-- ιBF carries the source direction into the Net_Api event
bfApiDir : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ApiHasDir (bfEvDir e₁) (ιBF e₁)
bfApiDir (BF.sendBF l d)    = ahIn
bfApiDir (BF.receiveBF l d) = ahOut
bfApiDir (BF.apiBFev l d m) = ahBF
bfApiDir (BF.doneBF l d)    = ahDone

-- the direction a driven CS-client step exposes on the Net_Api event
csc-ev-dir : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
csc-ev-dir l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιCS-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιCS e₁)) (decCSc-src-dir l d pos srcStep) (csApiDir e₁))

-- the direction a driven CS-server step exposes on the Net_Api event
css-ev-dir : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
css-ev-dir l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιCS-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιCS e₁)) (decCSs-src-dir l d pos srcStep) (csApiDir e₁))

-- the direction a driven BF-client step exposes on the Net_Api event
bfc-ev-dir : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
bfc-ev-dir l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιBF-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιBF e₁)) (decBFc-src-dir l d pos srcStep) (bfApiDir e₁))

-- the direction a driven BF-server step exposes on the Net_Api event
bfs-ev-dir : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
bfs-ev-dir l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιBF-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιBF e₁)) (decBFs-src-dir l d pos srcStep) (bfApiDir e₁))

-- L2 (CS): the client (dir cl) and server (dir sv≠cl) never fire the SAME event
CSc-CSs-noBoth : (l : Link) (cl sv : Dir) → cl ≢ sv → (pc : CScPos) (ps : CSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {Mc Ms : NetProc}
  → decCSc l cl pc ─[ ev (evl (evLabel X e₂ a)) ]─► Mc
  → decCSs l sv ps ─[ ev (evl (evLabel X e₂ a)) ]─► Ms → ⊥
CSc-CSs-noBoth l cl sv cl≢sv pc ps sc ss =
  cl≢sv (apiDir-inj (csc-ev-dir l cl pc sc) (css-ev-dir l sv ps ss))

-- L2 (BF): the client (dir cl) and server (dir sv≠cl) never fire the SAME event
BFc-BFs-noBoth : (l : Link) (cl sv : Dir) → cl ≢ sv → (pc : BFcPos) (ps : BFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {Mc Ms : NetProc}
  → decBFc l cl pc ─[ ev (evl (evLabel X e₂ a)) ]─► Mc
  → decBFs l sv ps ─[ ev (evl (evLabel X e₂ a)) ]─► Ms → ⊥
BFc-BFs-noBoth l cl sv cl≢sv pc ps sc ss =
  cl≢sv (apiDir-inj (bfc-ev-dir l cl pc sc) (bfs-ev-dir l sv ps ss))

------------------------------------------------------------------------
-- GAP-B L3 (core) — abstract-side peer viewV non-offer reductions.  The
-- abstract bundle reassembly (`⦀-ev-L/R` seals) needs each idle SIBLING's
-- `viewV (force …) ≡ nothing`.  Every abstract peer is a `tableSpec T q`, so
-- its offer map reduces to `tGo T ∘ nxt T q`; these bridge a `nxt`-nothing (a
-- position/event with no table edge) OR a terminal `isFin` to the seal's form.
------------------------------------------------------------------------

-- a non-terminal tableSpec peer offers nothing at a no-edge (e,a)
tableSpec-viewV-noOffer : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.Table.isFin T q ≡ false
  → NS.Table.nxt T q (X , e) a ≡ nothing
  → Op.viewV (PTree.force (tableSpec T q)) (X , e) a ≡ nothing
tableSpec-viewV-noOffer T q {X} {e} {a} finEq nxtEq =
  trans (cong (λ n → Op.viewV n (X , e) a) (tsForce-react T q finEq))
        (cong (tGo T) nxtEq)

-- a terminated tableSpec peer offers nothing at all
tableSpec-viewV-fin : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.Table.isFin T q ≡ true
  → Op.viewV (PTree.force (tableSpec T q)) (X , e) a ≡ nothing
tableSpec-viewV-fin T q {X} {e} {a} finEq =
  cong (λ n → Op.viewV n (X , e) a) (tsForce-ret T q finEq)

------------------------------------------------------------------------
-- GAP-B L3-full (foundations) — the ¬IoOffers↔viewV bridge and the
-- cross-protocol preimage facts.  These turn a peer's `¬ IoOffers` (the
-- SysStep non-offer currency) into the `viewV (force _) ≡ nothing` the
-- `⦀-ev-L/R` seals consume, and certify that a driven peer's ι-image event
-- has NO preimage under a sibling protocol's ι (so the sibling's ιX⁻¹-keyed
-- `*nxt-foreign` non-offer applies at the fired event).
------------------------------------------------------------------------

-- a process offering no visible step at (e,a) has `viewV (force _) ≡ nothing`
-- there (a `just` offer would give an `sVis` step, contradicting `¬ IoOffers`)
noOffer→viewV : (P : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IoOffers P e a
  → Op.viewV (PTree.force P) (X , e) a ≡ nothing
noOffer→viewV P {X} {e} {a} ¬off with PTree.force P in fEq
... | ret _       = refl
... | sil _       = refl
... | react v τc with v (X , e) a in vEq
...   | nothing   = refl
...   | just P′   = ⊥-elim (¬off (P′ , sVis fEq vEq))

-- viewV-of-⦀ group builder: a `⦀` group offers nothing at (e,a) when both
-- operands do (compose the per-operand `¬ IoOffers` via a `Par-ev-elim ∅ES`
-- peel, then bridge to `viewV`).  This is the sibling-group non-offer the
-- abstract-bundle `⦀-ev-L/R` reassembly threads past the driven peer.
⦀-viewV-nothing : (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IoOffers P e a → ¬ IoOffers Q e a
  → Op.viewV (PTree.force (P ⦀ Q)) (X , e) a ≡ nothing
⦀-viewV-nothing P Q {X} {e} {a} ¬P ¬Q =
  noOffer→viewV (P ⦀ Q) ¬PQ
  where
    -- the interleave `⦀` offers io only if some operand does (no ∅ES sync)
    ¬PQ : ¬ IoOffers (P ⦀ Q) e a
    ¬PQ (M , step) with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) P Q step
    ... | PEA.evSync mem _ _ = ⊥-elim mem
    ... | PEA.evL  _ sP     = ¬P (_ , sP)
    ... | PEA.evR  _ sQ     = ¬Q (_ , sQ)
    ... | PEA.evBoth _ sP _ = ¬P (_ , sP)

-- cross-protocol preimage: a ChainSync-image event has NO KeepAlive preimage
ιKA⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιKA⁻¹ (ιCS e₁) ≡ nothing
ιKA⁻¹∘ιCS (CS.sendCS l d)      = refl
ιKA⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιKA⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιKA⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a ChainSync-image event has NO BlockFetch preimage
ιBF⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιBF⁻¹ (ιCS e₁) ≡ nothing
ιBF⁻¹∘ιCS (CS.sendCS l d)      = refl
ιBF⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιBF⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιBF⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a ChainSync-image event has NO TxSubmission preimage
ιTS⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιTS⁻¹ (ιCS e₁) ≡ nothing
ιTS⁻¹∘ιCS (CS.sendCS l d)      = refl
ιTS⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιTS⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιTS⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO KeepAlive preimage
ιKA⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιKA⁻¹ (ιBF e₁) ≡ nothing
ιKA⁻¹∘ιBF (BF.sendBF l d)      = refl
ιKA⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιKA⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιKA⁻¹∘ιBF (BF.doneBF l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO ChainSync preimage
ιCS⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιCS⁻¹ (ιBF e₁) ≡ nothing
ιCS⁻¹∘ιBF (BF.sendBF l d)      = refl
ιCS⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιCS⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιCS⁻¹∘ιBF (BF.doneBF l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO TxSubmission preimage
ιTS⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιTS⁻¹ (ιBF e₁) ≡ nothing
ιTS⁻¹∘ιBF (BF.sendBF l d)      = refl
ιTS⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιTS⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιTS⁻¹∘ιBF (BF.doneBF l d)      = refl

-- cross-protocol preimage: a ChainSync-image event has NO LeiosNotify preimage
ιLN⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιLN⁻¹ (ιCS e₁) ≡ nothing
ιLN⁻¹∘ιCS (CS.sendCS l d)      = refl
ιLN⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιLN⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιLN⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a ChainSync-image event has NO LeiosFetch preimage
ιLF⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιLF⁻¹ (ιCS e₁) ≡ nothing
ιLF⁻¹∘ιCS (CS.sendCS l d)      = refl
ιLF⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιLF⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιLF⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO LeiosNotify preimage
ιLN⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιLN⁻¹ (ιBF e₁) ≡ nothing
ιLN⁻¹∘ιBF (BF.sendBF l d)      = refl
ιLN⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιLN⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιLN⁻¹∘ιBF (BF.doneBF l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO LeiosFetch preimage
ιLF⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιLF⁻¹ (ιBF e₁) ≡ nothing
ιLF⁻¹∘ιBF (BF.sendBF l d)      = refl
ιLF⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιLF⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιLF⁻¹∘ιBF (BF.doneBF l d)      = refl

------------------------------------------------------------------------
-- GAP-B L3-full — FOREIGN `nxt` non-offers (all `refl`, family-specific).
-- A sibling peer of protocol X never fires a driven peer's ι-image event of
-- a DIFFERENT protocol Y (its table clauses only match X-protocol events, so
-- a Y-image falls to the per-table catch-all `nothing`).  KA/TS peers are at a
-- FIXED spec head in `absBundleG`; CS/BF peers range over their coarse
-- positions.  SCRIPT-GENERATED (`.superpowers/sdd/gen-l3-foreign.py`).
------------------------------------------------------------------------

-- kaCnxt-noCS: the head-kcClient kaCnxt peer offers nothing at any CS.CSEv-image
kaCnxt-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.kaCnxt l d NS.kcClient (X , ιCS e₁) a ≡ nothing
kaCnxt-noCS l d (CS.sendCS _ _) = refl
kaCnxt-noCS l d (CS.receiveCS _ _) = refl
kaCnxt-noCS l d (CS.apiCSev _ _ _) = refl
kaCnxt-noCS l d (CS.doneCS _ _) = refl

-- kaCnxt-noBF: the head-kcClient kaCnxt peer offers nothing at any BF.BFEv-image
kaCnxt-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.kaCnxt l d NS.kcClient (X , ιBF e₁) a ≡ nothing
kaCnxt-noBF l d (BF.sendBF _ _) = refl
kaCnxt-noBF l d (BF.receiveBF _ _) = refl
kaCnxt-noBF l d (BF.apiBFev _ _ _) = refl
kaCnxt-noBF l d (BF.doneBF _ _) = refl

-- kaSnxt-noCS: the head-ksClient kaSnxt peer offers nothing at any CS.CSEv-image
kaSnxt-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.kaSnxt l d NS.ksClient (X , ιCS e₁) a ≡ nothing
kaSnxt-noCS l d (CS.sendCS _ _) = refl
kaSnxt-noCS l d (CS.receiveCS _ _) = refl
kaSnxt-noCS l d (CS.apiCSev _ _ _) = refl
kaSnxt-noCS l d (CS.doneCS _ _) = refl

-- kaSnxt-noBF: the head-ksClient kaSnxt peer offers nothing at any BF.BFEv-image
kaSnxt-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.kaSnxt l d NS.ksClient (X , ιBF e₁) a ≡ nothing
kaSnxt-noBF l d (BF.sendBF _ _) = refl
kaSnxt-noBF l d (BF.receiveBF _ _) = refl
kaSnxt-noBF l d (BF.apiBFev _ _ _) = refl
kaSnxt-noBF l d (BF.doneBF _ _) = refl

-- tsCnxt-noCS: the head-tcInit tsCnxt peer offers nothing at any CS.CSEv-image
tsCnxt-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.tsCnxt l d NS.tcInit (X , ιCS e₁) a ≡ nothing
tsCnxt-noCS l d (CS.sendCS _ _) = refl
tsCnxt-noCS l d (CS.receiveCS _ _) = refl
tsCnxt-noCS l d (CS.apiCSev _ _ _) = refl
tsCnxt-noCS l d (CS.doneCS _ _) = refl

-- tsCnxt-noBF: the head-tcInit tsCnxt peer offers nothing at any BF.BFEv-image
tsCnxt-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.tsCnxt l d NS.tcInit (X , ιBF e₁) a ≡ nothing
tsCnxt-noBF l d (BF.sendBF _ _) = refl
tsCnxt-noBF l d (BF.receiveBF _ _) = refl
tsCnxt-noBF l d (BF.apiBFev _ _ _) = refl
tsCnxt-noBF l d (BF.doneBF _ _) = refl

-- tsSnxt-noCS: the head-tsInit tsSnxt peer offers nothing at any CS.CSEv-image
tsSnxt-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.tsSnxt l d NS.tsInit (X , ιCS e₁) a ≡ nothing
tsSnxt-noCS l d (CS.sendCS _ _) = refl
tsSnxt-noCS l d (CS.receiveCS _ _) = refl
tsSnxt-noCS l d (CS.apiCSev _ _ _) = refl
tsSnxt-noCS l d (CS.doneCS _ _) = refl

-- tsSnxt-noBF: the head-tsInit tsSnxt peer offers nothing at any BF.BFEv-image
tsSnxt-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.tsSnxt l d NS.tsInit (X , ιBF e₁) a ≡ nothing
tsSnxt-noBF l d (BF.sendBF _ _) = refl
tsSnxt-noBF l d (BF.receiveBF _ _) = refl
tsSnxt-noBF l d (BF.apiBFev _ _ _) = refl
tsSnxt-noBF l d (BF.doneBF _ _) = refl

-- csCnxt-noBF: csCnxt offers no table edge at any BF.BFEv-image event
csCnxt-noBF : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.csCnxt l d q (X , ιBF e₁) a ≡ nothing
csCnxt-noBF l d NS.ccIdle (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccIdle (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccIdle (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccIdle (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccWreq (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccWreq (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccWreq (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccWreq (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccAwait (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccAwait (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccAwait (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccAwait (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccWfi _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccWfi _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccWfi _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccWfi _) (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccInt (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccInt (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccInt (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccInt (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccWdone (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccWdone (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccWdone (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccWdone (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccMust (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccMust (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccMust (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccMust (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccArf _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccArf _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccArf _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccArf _) (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccArb _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccArb _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccArb _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccArb _) (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccAif _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccAif _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccAif _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccAif _) (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccAin _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccAin _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccAin _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccAin _) (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccTerm (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccTerm (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccTerm (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccTerm (BF.doneBF _ _) = refl

-- csSnxt-noBF: csSnxt offers no table edge at any BF.BFEv-image event
csSnxt-noBF : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.csSnxt l d q (X , ιBF e₁) a ≡ nothing
csSnxt-noBF l d NS.csIdle (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csIdle (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csIdle (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csIdle (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csAreq (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csAreq (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csAreq (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csAreq (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csCanAwait (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csCanAwait (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csCanAwait (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csCanAwait (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csAfi _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csAfi _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csAfi _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csAfi _) (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csInt (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csInt (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csInt (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csInt (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csDdone (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csDdone (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csDdone (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csDdone (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csMust (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csMust (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csMust (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csMust (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csWrf _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csWrf _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csWrf _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csWrf _) (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csWrb _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csWrb _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csWrb _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csWrb _) (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csWar (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csWar (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csWar (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csWar (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csWif _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csWif _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csWif _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csWif _) (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csWin _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csWin _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csWin _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csWin _) (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csTerm (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csTerm (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csTerm (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csTerm (BF.doneBF _ _) = refl

-- bfCnxt-noCS: bfCnxt offers no table edge at any CS.CSEv-image event
bfCnxt-noCS : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.bfCnxt l d q (X , ιCS e₁) a ≡ nothing
bfCnxt-noCS l d NS.bcIdle (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcIdle (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcIdle (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcIdle (CS.doneCS _ _) = refl
bfCnxt-noCS l d (NS.bcWrr _) (CS.sendCS _ _) = refl
bfCnxt-noCS l d (NS.bcWrr _) (CS.receiveCS _ _) = refl
bfCnxt-noCS l d (NS.bcWrr _) (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d (NS.bcWrr _) (CS.doneCS _ _) = refl
bfCnxt-noCS l d NS.bcBusy (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcBusy (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcBusy (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcBusy (CS.doneCS _ _) = refl
bfCnxt-noCS l d NS.bcWcd (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcWcd (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcWcd (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcWcd (CS.doneCS _ _) = refl
bfCnxt-noCS l d NS.bcStream (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcStream (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcStream (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcStream (CS.doneCS _ _) = refl
bfCnxt-noCS l d (NS.bcAblk _) (CS.sendCS _ _) = refl
bfCnxt-noCS l d (NS.bcAblk _) (CS.receiveCS _ _) = refl
bfCnxt-noCS l d (NS.bcAblk _) (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d (NS.bcAblk _) (CS.doneCS _ _) = refl
bfCnxt-noCS l d NS.bcTerm (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcTerm (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcTerm (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcTerm (CS.doneCS _ _) = refl

-- bfSnxt-noCS: bfSnxt offers no table edge at any CS.CSEv-image event
bfSnxt-noCS : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.bfSnxt l d q (X , ιCS e₁) a ≡ nothing
bfSnxt-noCS l d NS.bsIdle (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsIdle (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsIdle (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsIdle (CS.doneCS _ _) = refl
bfSnxt-noCS l d (NS.bsAreq _) (CS.sendCS _ _) = refl
bfSnxt-noCS l d (NS.bsAreq _) (CS.receiveCS _ _) = refl
bfSnxt-noCS l d (NS.bsAreq _) (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d (NS.bsAreq _) (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsBusy (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsBusy (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsBusy (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsBusy (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsDdone (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsDdone (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsDdone (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsDdone (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsWsb (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsWsb (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsWsb (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsWsb (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsStream (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsStream (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsStream (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsStream (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsWnb (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsWnb (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsWnb (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsWnb (CS.doneCS _ _) = refl
bfSnxt-noCS l d (NS.bsWblk _) (CS.sendCS _ _) = refl
bfSnxt-noCS l d (NS.bsWblk _) (CS.receiveCS _ _) = refl
bfSnxt-noCS l d (NS.bsWblk _) (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d (NS.bsWblk _) (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsWbd (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsWbd (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsWbd (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsWbd (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsTerm (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsTerm (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsTerm (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsTerm (CS.doneCS _ _) = refl

------------------------------------------------------------------------
-- GAP-B L4 (abstract-bundle sibling non-offers) — the `¬ IoOffers` facts the
-- abstract-bundle `⦀-ev-L/R` reassembly threads past the driven peer.  The
-- `⦀-viewV-nothing` group builder consumes per-operand `¬ IoOffers`; these are
-- the CROSS-PROTOCOL siblings (a KA/TS/opposite-protocol spec peer never fires
-- the driven peer's ι-image event).  Built by the reverse-of-`noOffer→viewV`
-- bridge `viewV→noOffer` over the `tableSpec-viewV-{noOffer,fin}` reductions.
------------------------------------------------------------------------

-- reverse of `noOffer→viewV`: a `viewV (force P) ≡ nothing` at (e,a) rules out
-- any visible io step there (a step would give `v (e,a) ≡ just`, via `ev-inv`)
viewV→noOffer : (P : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → Op.viewV (PTree.force P) (X , e) a ≡ nothing → ¬ IoOffers P e a
viewV→noOffer P {X} {e} {a} vn (M , step) with ev-inv step
... | v , τc , feq , veq =
      nothing-absurd
        (trans (sym (trans (sym (cong (λ n → Op.viewV n (X , e) a) feq)) vn)) veq)

-- kaClientSpec never fires a ChainSync-image event (foreign to its KA table)
kaClientSpec-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (kaClientSpec l d) (ιCS e₁) a
kaClientSpec-noCS l d e₁ {a} = viewV→noOffer (kaClientSpec l d) {e = ιCS e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
     NS.kcClient {e = ιCS e₁} {a = a} refl (kaCnxt-noCS l d e₁ {a = a}))

-- kaServerSpec never fires a ChainSync-image event
kaServerSpec-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (kaServerSpec l d) (ιCS e₁) a
kaServerSpec-noCS l d e₁ {a} = viewV→noOffer (kaServerSpec l d) {e = ιCS e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
     NS.ksClient {e = ιCS e₁} {a = a} refl (kaSnxt-noCS l d e₁ {a = a}))

-- tsClientSpec never fires a ChainSync-image event
tsClientSpec-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (tsClientSpec l d) (ιCS e₁) a
tsClientSpec-noCS l d e₁ {a} = viewV→noOffer (tsClientSpec l d) {e = ιCS e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
     NS.tcInit {e = ιCS e₁} {a = a} refl (tsCnxt-noCS l d e₁ {a = a}))

-- tsServerSpec never fires a ChainSync-image event
tsServerSpec-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (tsServerSpec l d) (ιCS e₁) a
tsServerSpec-noCS l d e₁ {a} = viewV→noOffer (tsServerSpec l d) {e = ιCS e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
     NS.tsInit {e = ιCS e₁} {a = a} refl (tsSnxt-noCS l d e₁ {a = a}))

-- the abstract BF client never fires a ChainSync-image event (terminal or
-- foreign no-edge; case its coarse `isFin`)
absBFc-noCS : (l : Link) (d : Dir) (q : BFcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absBFc l d q) (ιCS e₁) a
absBFc-noCS l d q e₁ {a} with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιCS e₁} {a = a} fEq (bfCnxt-noCS l d (coarsenBFc q) e₁ {a = a}))

-- the abstract BF server never fires a ChainSync-image event
absBFs-noCS : (l : Link) (d : Dir) (q : BFsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absBFs l d q) (ιCS e₁) a
absBFs-noCS l d q e₁ {a} with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιCS e₁} {a = a} fEq (bfSnxt-noCS l d (coarsenBFs q) e₁ {a = a}))

-- kaClientSpec never fires a BlockFetch-image event
kaClientSpec-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (kaClientSpec l d) (ιBF e₁) a
kaClientSpec-noBF l d e₁ {a} = viewV→noOffer (kaClientSpec l d) {e = ιBF e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
     NS.kcClient {e = ιBF e₁} {a = a} refl (kaCnxt-noBF l d e₁ {a = a}))

-- kaServerSpec never fires a BlockFetch-image event
kaServerSpec-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (kaServerSpec l d) (ιBF e₁) a
kaServerSpec-noBF l d e₁ {a} = viewV→noOffer (kaServerSpec l d) {e = ιBF e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
     NS.ksClient {e = ιBF e₁} {a = a} refl (kaSnxt-noBF l d e₁ {a = a}))

-- tsClientSpec never fires a BlockFetch-image event
tsClientSpec-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (tsClientSpec l d) (ιBF e₁) a
tsClientSpec-noBF l d e₁ {a} = viewV→noOffer (tsClientSpec l d) {e = ιBF e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
     NS.tcInit {e = ιBF e₁} {a = a} refl (tsCnxt-noBF l d e₁ {a = a}))

-- tsServerSpec never fires a BlockFetch-image event
tsServerSpec-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (tsServerSpec l d) (ιBF e₁) a
tsServerSpec-noBF l d e₁ {a} = viewV→noOffer (tsServerSpec l d) {e = ιBF e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
     NS.tsInit {e = ιBF e₁} {a = a} refl (tsSnxt-noBF l d e₁ {a = a}))

-- tsCnxt-noCS-pos: the abstract tsCnxt peer offers no table edge at any CS.CSEv-image event (any position)
tsCnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.tsCnxt l d q (X , ιCS e₁) a ≡ nothing
tsCnxt-noCS-pos l d NS.tcInit (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcInit (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcInit (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcInit (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcIdle (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcIdle (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcIdle (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcIdle (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (Blocking , _ , _)) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (NonBlocking , _ , _)) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (Blocking , _ , _)) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (NonBlocking , _ , _)) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (Blocking , _ , _)) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (NonBlocking , _ , _)) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (Blocking , _ , _)) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (NonBlocking , _ , _)) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcBlk (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcBlk (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcBlk (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcBlk (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcNbl (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcNbl (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcNbl (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcNbl (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcArt _) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcArt _) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcArt _) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcArt _) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTxs (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTxs (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTxs (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcTxs (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWri _) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWri _) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWri _) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWri _) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcWdone (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcWdone (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcWdone (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcWdone (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWrt _) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWrt _) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWrt _) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWrt _) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTerm (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTerm (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTerm (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcTerm (CS.doneCS _ _) = refl

-- tsCnxt-noBF-pos: the abstract tsCnxt peer offers no table edge at any BF.BFEv-image event (any position)
tsCnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.tsCnxt l d q (X , ιBF e₁) a ≡ nothing
tsCnxt-noBF-pos l d NS.tcInit (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcInit (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcInit (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcInit (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcIdle (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcIdle (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcIdle (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcIdle (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (Blocking , _ , _)) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (NonBlocking , _ , _)) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (Blocking , _ , _)) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (NonBlocking , _ , _)) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (Blocking , _ , _)) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (NonBlocking , _ , _)) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (Blocking , _ , _)) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (NonBlocking , _ , _)) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcBlk (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcBlk (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcBlk (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcBlk (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcNbl (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcNbl (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcNbl (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcNbl (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcArt _) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcArt _) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcArt _) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcArt _) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTxs (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTxs (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTxs (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcTxs (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWri _) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWri _) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWri _) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWri _) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcWdone (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcWdone (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcWdone (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcWdone (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWrt _) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWrt _) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWrt _) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWrt _) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTerm (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTerm (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTerm (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcTerm (BF.doneBF _ _) = refl

-- tsSnxt-noCS-pos: the abstract tsSnxt peer offers no table edge at any CS.CSEv-image event (any position)
tsSnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.tsSnxt l d q (X , ιCS e₁) a ≡ nothing
tsSnxt-noCS-pos l d NS.tsInit (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsInit (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsInit (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsInit (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsIdle (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsIdle (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsIdle (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsIdle (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWib _) (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWib _) (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWib _) (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWib _) (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWin _) (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWin _) (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWin _) (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWin _) (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWrt _) (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWrt _) (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWrt _) (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWrt _) (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsBlk (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsBlk (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsBlk (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsBlk (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsNbl (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsNbl (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsNbl (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsNbl (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTxs (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTxs (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTxs (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsTxs (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsDdone (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsDdone (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsDdone (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsDdone (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTerm (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTerm (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTerm (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsTerm (CS.doneCS _ _) = refl

-- tsSnxt-noBF-pos: the abstract tsSnxt peer offers no table edge at any BF.BFEv-image event (any position)
tsSnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.tsSnxt l d q (X , ιBF e₁) a ≡ nothing
tsSnxt-noBF-pos l d NS.tsInit (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsInit (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsInit (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsInit (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsIdle (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsIdle (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsIdle (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsIdle (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWib _) (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWib _) (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWib _) (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWib _) (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWin _) (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWin _) (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWin _) (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWin _) (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWrt _) (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWrt _) (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWrt _) (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWrt _) (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsBlk (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsBlk (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsBlk (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsBlk (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsNbl (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsNbl (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsNbl (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsNbl (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTxs (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTxs (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTxs (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsTxs (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsDdone (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsDdone (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsDdone (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsDdone (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTerm (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTerm (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTerm (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsTerm (BF.doneBF _ _) = refl

-- the abstract TS client never fires a CS.CSEv-image event (any tracked position)
absTSc-noCS : (l : Link) (d : Dir) (q : TScPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absTSc l d q) (ιCS e₁) a
absTSc-noCS l d q e₁ {a} with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιCS e₁} {a = a} fEq (tsCnxt-noCS-pos l d (coarsenTSc q) e₁ {a = a}))

-- the abstract TS client never fires a BF.BFEv-image event (any tracked position)
absTSc-noBF : (l : Link) (d : Dir) (q : TScPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absTSc l d q) (ιBF e₁) a
absTSc-noBF l d q e₁ {a} with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιBF e₁} {a = a} fEq (tsCnxt-noBF-pos l d (coarsenTSc q) e₁ {a = a}))

-- the abstract TS server never fires a CS.CSEv-image event (any tracked position)
absTSs-noCS : (l : Link) (d : Dir) (q : TSsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absTSs l d q) (ιCS e₁) a
absTSs-noCS l d q e₁ {a} with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιCS e₁} {a = a} fEq (tsSnxt-noCS-pos l d (coarsenTSs q) e₁ {a = a}))

-- the abstract TS server never fires a BF.BFEv-image event (any tracked position)
absTSs-noBF : (l : Link) (d : Dir) (q : TSsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absTSs l d q) (ιBF e₁) a
absTSs-noBF l d q e₁ {a} with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιBF e₁} {a = a} fEq (tsSnxt-noBF-pos l d (coarsenTSs q) e₁ {a = a}))

-- KA table foreign-channel non-offers (position-enumerated: `kaCnxt`/`kaSnxt`
-- match the position first, so `refl` needs a concrete position; the foreign
-- CS/BF-image event then hits the `nothing` catch-all at every position)
kaCnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.KAcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.kaCnxt l d q (X , ιCS e₁) a ≡ nothing
kaCnxt-noCS-pos l d NS.kcClient (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcClient (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcClient (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d NS.kcClient (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcWmsg _) (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcWmsg _) (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcWmsg _) (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d (NS.kcWmsg _) (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcAwait _) (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcAwait _) (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcAwait _) (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d (NS.kcAwait _) (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcWdone (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcWdone (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcWdone (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d NS.kcWdone (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcErr _ _) (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcErr _ _) (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcErr _ _) (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d (NS.kcErr _ _) (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTerm (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTerm (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTerm (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d NS.kcTerm (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTermE (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTermE (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTermE (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d NS.kcTermE (CS.doneCS _ _) = refl
kaCnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.KAcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.kaCnxt l d q (X , ιBF e₁) a ≡ nothing
kaCnxt-noBF-pos l d NS.kcClient (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcClient (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcClient (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d NS.kcClient (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcWmsg _) (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcWmsg _) (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcWmsg _) (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d (NS.kcWmsg _) (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcAwait _) (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcAwait _) (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcAwait _) (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d (NS.kcAwait _) (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcWdone (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcWdone (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcWdone (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d NS.kcWdone (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcErr _ _) (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcErr _ _) (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcErr _ _) (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d (NS.kcErr _ _) (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTerm (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTerm (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTerm (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d NS.kcTerm (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTermE (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTermE (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTermE (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d NS.kcTermE (BF.doneBF _ _) = refl
kaSnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.KAsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.kaSnxt l d q (X , ιCS e₁) a ≡ nothing
kaSnxt-noCS-pos l d NS.ksClient (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksClient (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksClient (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d NS.ksClient (CS.doneCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksRecv _) (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksRecv _) (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksRecv _) (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d (NS.ksRecv _) (CS.doneCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksResp _) (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksResp _) (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksResp _) (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d (NS.ksResp _) (CS.doneCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksDdone (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksDdone (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksDdone (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d NS.ksDdone (CS.doneCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksTerm (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksTerm (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksTerm (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d NS.ksTerm (CS.doneCS _ _) = refl
kaSnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.KAsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.kaSnxt l d q (X , ιBF e₁) a ≡ nothing
kaSnxt-noBF-pos l d NS.ksClient (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksClient (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksClient (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d NS.ksClient (BF.doneBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksRecv _) (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksRecv _) (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksRecv _) (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d (NS.ksRecv _) (BF.doneBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksResp _) (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksResp _) (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksResp _) (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d (NS.ksResp _) (BF.doneBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksDdone (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksDdone (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksDdone (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d NS.ksDdone (BF.doneBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksTerm (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksTerm (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksTerm (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d NS.ksTerm (BF.doneBF _ _) = refl

-- the abstract KA client never fires a CS.CSEv-image event (any tracked position)
absKAc-noCS : (l : Link) (d : Dir) (q : KAcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absKAc l d q) (ιCS e₁) a
absKAc-noCS l d q e₁ {a} with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιCS e₁} {a = a} fEq (kaCnxt-noCS-pos l d (coarsenKAc q) e₁ {a = a}))

-- the abstract KA client never fires a BF.BFEv-image event (any tracked position)
absKAc-noBF : (l : Link) (d : Dir) (q : KAcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absKAc l d q) (ιBF e₁) a
absKAc-noBF l d q e₁ {a} with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιBF e₁} {a = a} fEq (kaCnxt-noBF-pos l d (coarsenKAc q) e₁ {a = a}))

-- the abstract KA server never fires a CS.CSEv-image event (any tracked position)
absKAs-noCS : (l : Link) (d : Dir) (q : KAsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absKAs l d q) (ιCS e₁) a
absKAs-noCS l d q e₁ {a} with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιCS e₁} {a = a} fEq (kaSnxt-noCS-pos l d (coarsenKAs q) e₁ {a = a}))

-- the abstract KA server never fires a BF.BFEv-image event (any tracked position)
absKAs-noBF : (l : Link) (d : Dir) (q : KAsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absKAs l d q) (ιBF e₁) a
absKAs-noBF l d q e₁ {a} with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιBF e₁} {a = a} fEq (kaSnxt-noBF-pos l d (coarsenKAs q) e₁ {a = a}))

-- the abstract CS client never fires a BlockFetch-image event
absCSc-noBF : (l : Link) (d : Dir) (q : CScPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absCSc l d q) (ιBF e₁) a
absCSc-noBF l d q e₁ {a} with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιBF e₁} {a = a} fEq (csCnxt-noBF l d (coarsenCSc q) e₁ {a = a}))

-- the abstract CS server never fires a BlockFetch-image event
absCSs-noBF : (l : Link) (d : Dir) (q : CSsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absCSs l d q) (ιBF e₁) a
absCSs-noBF l d q e₁ {a} with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιBF e₁} {a = a} fEq (csSnxt-noBF l d (coarsenCSs q) e₁ {a = a}))

------------------------------------------------------------------------
-- GAP-B step 2 — AUGMENTED per-peer sims.  Extend `sim{peer}` to ALSO expose
-- the source event `e₁`, the ι-image equation `e ≡ ιX e₁`, and the fired
-- direction `{cs,bf}EvDir e₁ ≡ d` — the extra data `bundle-{CS,BF}-ev-inv`
-- needs to ROUTE the peel (which protocol/direction) and rebuild the abstract
-- bundle.  Thin wrappers over the existing `sim{peer}` machinery.
------------------------------------------------------------------------

-- augmented CS-client sim (exposes e₁ / e≡ιCS e₁ / csEvDir e₁≡d)
simCSc′ : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ CS.CSEv X ] Σ[ pos′ ∈ CScPos ]
       (e ≡ ιCS e₁) × (csEvDir e₁ ≡ d) × (M ≡ decCSc l d pos′)
       × (absCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSc l d pos′)
simCSc′ l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decCSc-src-ev-inv l d pos srcStep | ιCS-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decCSc-src-dir l d pos srcStep ,
        trans Meq (cong RenCS.renameMap P′eq) , aStep

-- augmented CS-server sim
simCSs′ : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ CS.CSEv X ] Σ[ pos′ ∈ CSsPos ]
       (e ≡ ιCS e₁) × (csEvDir e₁ ≡ d) × (M ≡ decCSs l d pos′)
       × (absCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSs l d pos′)
simCSs′ l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decCSs-src-ev-inv l d pos srcStep | ιCS-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decCSs-src-dir l d pos srcStep ,
        trans Meq (cong RenCS.renameMap P′eq) , aStep

-- augmented BF-client sim
simBFc′ : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ BF.BFEv X ] Σ[ pos′ ∈ BFcPos ]
       (e ≡ ιBF e₁) × (bfEvDir e₁ ≡ d) × (M ≡ decBFc l d pos′)
       × (absBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFc l d pos′)
simBFc′ l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decBFc-src-ev-inv l d pos srcStep | ιBF-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decBFc-src-dir l d pos srcStep ,
        trans Meq (cong RenBF.renameMap P′eq) , aStep

-- augmented BF-server sim
simBFs′ : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ BF.BFEv X ] Σ[ pos′ ∈ BFsPos ]
       (e ≡ ιBF e₁) × (bfEvDir e₁ ≡ d) × (M ≡ decBFs l d pos′)
       × (absBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFs l d pos′)
simBFs′ l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decBFs-src-ev-inv l d pos srcStep | ιBF-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decBFs-src-dir l d pos srcStep ,
        trans Meq (cong RenBF.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- GAP-B step 1 — abstract-DIRECTION sibling non-offers.  The same-protocol
-- OPPOSITE-role abstract peer (at direction sv) never offers the driven
-- peer's event (which carries the driven direction cl ≢ sv): every firing
-- clause of the abstract `nxt` table guards on `d′ ≟ d`, so a wrong-direction
-- event falls to the per-table catch-all `nothing`.  SCRIPT-GENERATED
-- (`.superpowers/sdd/gen-l4-dir.py`).
------------------------------------------------------------------------
-- csSnxt-dir-no: a wrong-direction CS-image event (csEvDir e₁ ≢ d)
-- has no csSnxt table edge (every firing clause guards on d′ ≟ d)
csSnxt-dir-no : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ d → NS.csSnxt l d q (X , ιCS e₁) a ≡ nothing
csSnxt-dir-no l d NS.csIdle (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' reqCSRequestNext) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSAwaitReply) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollForward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollBackward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSIntersectFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csDdone (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csDdone (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csDdone (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d NS.csDdone (CS.doneCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csMust (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSRollForward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSRollBackward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWrf _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csWrf _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWrf _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d (NS.csWrf _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWrb _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csWrb _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWrb _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d (NS.csWrb _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csWar (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csWar (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csWar (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d NS.csWar (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWif _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csWif _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWif _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d (NS.csWif _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWin _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csWin _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWin _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d (NS.csWin _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csTerm (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csTerm (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csTerm (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d NS.csTerm (CS.doneCS l' d') ¬eq = refl

-- csCnxt-dir-no: a wrong-direction CS-image event (csEvDir e₁ ≢ d)
-- has no csCnxt table edge (every firing clause guards on d′ ≟ d)
csCnxt-dir-no : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ d → NS.csCnxt l d q (X , ιCS e₁) a ≡ nothing
csCnxt-dir-no l d NS.ccIdle (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRequestNext) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSFindIntersect) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccWreq (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccWreq (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccWreq (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccWreq (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccWfi _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccWfi _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccWfi _) (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d (NS.ccWfi _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccWdone (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccWdone (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccWdone (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccWdone (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollforward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollback) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccTerm (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccTerm (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccTerm (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccTerm (CS.doneCS l' d') ¬eq = refl

-- bfCnxt-dir-no: a wrong-direction BF-image event (bfEvDir e₁ ≢ d)
-- has no bfCnxt table edge (every firing clause guards on d′ ≟ d)
bfCnxt-dir-no : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ d → NS.bfCnxt l d q (X , ιBF e₁) a ≡ nothing
bfCnxt-dir-no l d NS.bcIdle (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFRequestRange) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFClientDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcWrr _) (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d (NS.bcWrr _) (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcWrr _) (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d (NS.bcWrr _) (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcWcd (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcWcd (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcWcd (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d NS.bcWcd (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' recvBFBlock) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcTerm (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcTerm (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcTerm (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d NS.bcTerm (BF.doneBF l' d') ¬eq = refl

-- bfSnxt-dir-no: a wrong-direction BF-image event (bfEvDir e₁ ≢ d)
-- has no bfSnxt table edge (every firing clause guards on d′ ≟ d)
bfSnxt-dir-no : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ d → NS.bfSnxt l d q (X , ιBF e₁) a ≡ nothing
bfSnxt-dir-no l d NS.bsIdle (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' reqBFRange) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFStartBatch) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFNoBlocks) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsDdone (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsDdone (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsDdone (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsDdone (BF.doneBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsWsb (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsWsb (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWsb (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsWsb (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFBlock) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFBatchDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWnb (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsWnb (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWnb (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsWnb (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsWblk _) (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d (NS.bsWblk _) (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsWblk _) (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d (NS.bsWblk _) (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWbd (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsWbd (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWbd (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsWbd (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsTerm (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsTerm (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsTerm (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsTerm (BF.doneBF l' d') ¬eq = refl

-- absCSs-dir-noBoth: the same-protocol OPPOSITE-role sibling (dir CS) does
-- not fire the driven peer's wrong-direction event (via csSnxt-dir-no)
absCSs-dir-noBoth : (l : Link) (sv : Dir) (q : CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ sv → ¬ IoOffers (absCSs l sv q) (ιCS e₁) a
absCSs-dir-noBoth l sv q e₁ {a} ¬d with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l sv })
                   (coarsenCSs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l sv })
                   (coarsenCSs q) {e = ιCS e₁} {a = a} fEq (csSnxt-dir-no l sv (coarsenCSs q) e₁ {a = a} ¬d))

-- absCSc-dir-noBoth: the same-protocol OPPOSITE-role sibling (dir CS) does
-- not fire the driven peer's wrong-direction event (via csCnxt-dir-no)
absCSc-dir-noBoth : (l : Link) (sv : Dir) (q : CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ sv → ¬ IoOffers (absCSc l sv q) (ιCS e₁) a
absCSc-dir-noBoth l sv q e₁ {a} ¬d with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l sv })
                   (coarsenCSc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l sv })
                   (coarsenCSc q) {e = ιCS e₁} {a = a} fEq (csCnxt-dir-no l sv (coarsenCSc q) e₁ {a = a} ¬d))

-- absBFc-dir-noBoth: the same-protocol OPPOSITE-role sibling (dir BF) does
-- not fire the driven peer's wrong-direction event (via bfCnxt-dir-no)
absBFc-dir-noBoth : (l : Link) (sv : Dir) (q : BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ sv → ¬ IoOffers (absBFc l sv q) (ιBF e₁) a
absBFc-dir-noBoth l sv q e₁ {a} ¬d with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l sv })
                   (coarsenBFc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l sv })
                   (coarsenBFc q) {e = ιBF e₁} {a = a} fEq (bfCnxt-dir-no l sv (coarsenBFc q) e₁ {a = a} ¬d))

-- absBFs-dir-noBoth: the same-protocol OPPOSITE-role sibling (dir BF) does
-- not fire the driven peer's wrong-direction event (via bfSnxt-dir-no)
absBFs-dir-noBoth : (l : Link) (sv : Dir) (q : BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ sv → ¬ IoOffers (absBFs l sv q) (ιBF e₁) a
absBFs-dir-noBoth l sv q e₁ {a} ¬d with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l sv })
                   (coarsenBFs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l sv })
                   (coarsenBFs q) {e = ιBF e₁} {a = a} fEq (bfSnxt-dir-no l sv (coarsenBFs q) e₁ {a = a} ¬d))



------------------------------------------------------------------------
-- GAP-B step 3 (abstract-bundle REASSEMBLY) — rebuild an `absBundleG` visible
-- step from a single driven-peer step, threading the sibling non-offers past
-- the eight `⦀` layers (`⦀-ev-L/R` take a `viewV (force _) ≡ nothing`; single
-- peers via `noOffer→viewV`, the sibling GROUP via `⦀-viewV-nothing`/`⦀-noOffer`).
-- Cross-protocol siblings by the committed `*-no{CS,BF}` leaves; the same-
-- protocol opposite-role sibling by the direction leaf `abs*-dir-noBoth`.
-- These are the UPWARD half of `bundle-{CS,BF}-ev-inv` (downward peel residual).
------------------------------------------------------------------------

-- CS-client advances: rebuild the abstract bundle step (dir cl, csEvDir e₁≡cl)
absBundle-CSc-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {qcc′ : CScPos}
  → cl ≢ sv → csEvDir e₁ ≡ cl
  → absCSc l cl qcc ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absCSc l cl qcc′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absBundleG l cl sv qcc′ qcs qbc qbs ip
absBundle-CSc-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-L (absCSc l cl qcc) _ astep
        (⦀-viewV-nothing (absCSs l sv qcs) _ (absCSs-dir-noBoth l sv qcs e₁ ¬sv)
          (SStep.⦀-noOffer (absBFc l cl qbc) _ (absBFc-noCS l cl qbc e₁)
            (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-noCS l sv qbs e₁)
              (SStep.⦀-noOffer (absTSc l cl (tsc ip)) (absTSs l sv (tss ip))
                (absTSc-noCS l cl (tsc ip) e₁) (absTSs-noCS l sv (tss ip) e₁))))))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noCS l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noCS l cl (kac ip) e₁))
  where ¬sv : csEvDir e₁ ≢ sv
        ¬sv q = cl≢sv (trans (sym eqd) q)

-- CS-server advances: rebuild the abstract bundle step (dir sv, csEvDir e₁≡sv)
absBundle-CSs-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {qcs′ : CSsPos}
  → cl ≢ sv → csEvDir e₁ ≡ sv
  → absCSs l sv qcs ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absCSs l sv qcs′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absBundleG l cl sv qcc qcs′ qbc qbs ip
absBundle-CSs-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-L (absCSs l sv qcs) _ astep
          (⦀-viewV-nothing (absBFc l cl qbc) _ (absBFc-noCS l cl qbc e₁)
            (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-noCS l sv qbs e₁)
              (SStep.⦀-noOffer (absTSc l cl (tsc ip)) (absTSs l sv (tss ip))
                (absTSc-noCS l cl (tsc ip) e₁) (absTSs-noCS l sv (tss ip) e₁)))))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-dir-noBoth l cl qcc e₁ ¬cl)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noCS l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noCS l cl (kac ip) e₁))
  where ¬cl : csEvDir e₁ ≢ cl
        ¬cl q = cl≢sv (sym (trans (sym eqd) q))

-- BF-client advances: rebuild the abstract bundle step (dir cl, bfEvDir e₁≡cl)
absBundle-BFc-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {qbc′ : BFcPos}
  → cl ≢ sv → bfEvDir e₁ ≡ cl
  → absBFc l cl qbc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBFc l cl qbc′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc′ qbs ip
absBundle-BFc-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-L (absBFc l cl qbc) _ astep
            (⦀-viewV-nothing (absBFs l sv qbs) _ (absBFs-dir-noBoth l sv qbs e₁ ¬sv)
              (SStep.⦀-noOffer (absTSc l cl (tsc ip)) (absTSs l sv (tss ip))
                (absTSc-noBF l cl (tsc ip) e₁) (absTSs-noBF l sv (tss ip) e₁))))
          (noOffer→viewV (absCSs l sv qcs) (absCSs-noBF l sv qcs e₁)))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-noBF l cl qcc e₁)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noBF l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noBF l cl (kac ip) e₁))
  where ¬sv : bfEvDir e₁ ≢ sv
        ¬sv q = cl≢sv (trans (sym eqd) q)

-- BF-server advances: rebuild the abstract bundle step (dir sv, bfEvDir e₁≡sv)
absBundle-BFs-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {qbs′ : BFsPos}
  → cl ≢ sv → bfEvDir e₁ ≡ sv
  → absBFs l sv qbs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBFs l sv qbs′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs′ ip
absBundle-BFs-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-R (absBFc l cl qbc) _
            (SStep.⦀-ev-L (absBFs l sv qbs) _ astep
              (⦀-viewV-nothing (absTSc l cl (tsc ip)) (absTSs l sv (tss ip))
                (absTSc-noBF l cl (tsc ip) e₁) (absTSs-noBF l sv (tss ip) e₁)))
            (noOffer→viewV (absBFc l cl qbc) (absBFc-dir-noBoth l cl qbc e₁ ¬cl)))
          (noOffer→viewV (absCSs l sv qcs) (absCSs-noBF l sv qcs e₁)))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-noBF l cl qcc e₁)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noBF l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noBF l cl (kac ip) e₁))
  where ¬cl : bfEvDir e₁ ≢ cl
        ¬cl q = cl≢sv (sym (trans (sym eqd) q))

------------------------------------------------------------------------
-- GAP-B step 3 (concrete-bundle leaves) — the CONCRETE-side non-offers the
-- DOWNWARD peel of `bundle-{CS,BF}-ev-inv` consumes to refute the wrong peers:
--   · the same-protocol opposite-role driven peer at the WRONG direction
--     (`dec*-dir-noOffer`, dual of `abs*-dir-noBoth`, via `*-ev-dir`+`apiDir-inj`);
--   · the opposite-PROTOCOL driven peer at ANY image event (`dec*-no*gen`, via
--     `RenNO.renameMap-noOffer-χ` + the committed cross-preimage `ιX⁻¹∘ιY`).
------------------------------------------------------------------------

-- RenNO instances for the two driven protocols (for the general cross-protocol
-- non-offers; `CSNO`/`BFNO` above are RenTC reflect modules, not RenNO)
module CSNOff = SStep.RenNO ιCS ιCS⁻¹ ιCS-linv
module BFNOff = SStep.RenNO ιBF ιBF⁻¹ ιBF-linv

-- concrete CS-client never fires a wrong-direction CS-image event
decCSc-dir-noOffer : (l : Link) (d : Dir) (pos : CScPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ d → ¬ IoOffers (decCSc l d pos) (ιCS e₁) a
decCSc-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (csc-ev-dir l d pos step) (csApiDir e₁)))

-- concrete CS-server never fires a wrong-direction CS-image event
decCSs-dir-noOffer : (l : Link) (d : Dir) (pos : CSsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ d → ¬ IoOffers (decCSs l d pos) (ιCS e₁) a
decCSs-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (css-ev-dir l d pos step) (csApiDir e₁)))

-- concrete BF-client never fires a wrong-direction BF-image event
decBFc-dir-noOffer : (l : Link) (d : Dir) (pos : BFcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ d → ¬ IoOffers (decBFc l d pos) (ιBF e₁) a
decBFc-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (bfc-ev-dir l d pos step) (bfApiDir e₁)))

-- concrete BF-server never fires a wrong-direction BF-image event
decBFs-dir-noOffer : (l : Link) (d : Dir) (pos : BFsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ d → ¬ IoOffers (decBFs l d pos) (ιBF e₁) a
decBFs-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (bfs-ev-dir l d pos step) (bfApiDir e₁)))

-- concrete BF peers never fire ANY CS-image event (opposite protocol)
decBFc-noCSgen : (l : Link) (d : Dir) (pos : BFcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (decBFc l d pos) (ιCS e₁) a
decBFc-noCSgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFc-src l d pos) (ιBF⁻¹∘ιCS e₁)
decBFs-noCSgen : (l : Link) (d : Dir) (pos : BFsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (decBFs l d pos) (ιCS e₁) a
decBFs-noCSgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFs-src l d pos) (ιBF⁻¹∘ιCS e₁)

-- concrete CS peers never fire ANY BF-image event (opposite protocol)
decCSc-noBFgen : (l : Link) (d : Dir) (pos : CScPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (decCSc l d pos) (ιBF e₁) a
decCSc-noBFgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSc-src l d pos) (ιCS⁻¹∘ιBF e₁)
decCSs-noBFgen : (l : Link) (d : Dir) (pos : CSsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (decCSs l d pos) (ιBF e₁) a
decCSs-noBFgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSs-src l d pos) (ιCS⁻¹∘ιBF e₁)

------------------------------------------------------------------------
-- GAP-B L4 — the 12-peer bundle ev-inversion (DOWNWARD peel), CS side.
-- A visible CS-image event `ιCS e₁` of `bundleG` is fired by exactly ONE of
-- the two driven CS peers (client at cl / server at sv); the ten siblings are
-- refuted by NON-OFFER (inert KA/TS/LN/LF via the `ιX⁻¹∘ιCS` cross-preimages;
-- opposite-protocol BF via `decBF*-noCSgen`; the same-protocol opposite-role
-- driven peer via the direction leaf, cl ≢ sv).  Peels the 11 `⦀` with
-- `PEA.Par-ev-elim ∅ESa`; the abstract step is rebuilt by `absBundle-CS{c,s}-ev`.
------------------------------------------------------------------------

-- tail (decBFc ⦀ decBFs ⦀ TS ⦀ LN ⦀ LF) offers no CS-image event (all BF/inert)
csTail-bfc-noOffer : (l : Link) (cl sv : Dir) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (decBFc l cl bfc ⦀ (decBFs l sv bfs
       ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (LFclientA l cl ⦀ LFserverA l sv))))))) (ιCS e₁) a
csTail-bfc-noOffer l cl sv bfc bfs ip e₁ =
  SStep.⦀-noOffer (decBFc l cl bfc) _ (decBFc-noCSgen l cl bfc e₁)
    (SStep.⦀-noOffer (decBFs l sv bfs) _ (decBFs-noCSgen l sv bfs e₁)
      (SStep.⦀-noOffer (decTSc l cl (tsc ip)) _ (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιCS e₁))
        (SStep.⦀-noOffer (decTSs l sv (tss ip)) _ (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιCS e₁))
          (SStep.⦀-noOffer (decLNc l cl (lnc ip)) _ (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιCS e₁))
            (SStep.⦀-noOffer (decLNs l sv (lns ip)) _ (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιCS e₁))
              (SStep.⦀-noOffer (LFclientA l cl) (LFserverA l sv)
                (LFclientA-noOffer l cl (ιLF⁻¹∘ιCS e₁))
                (LFserverA-noOffer l sv (ιLF⁻¹∘ιCS e₁))))))))

-- tail (decCSs ⦀ decBFc ⦀ …) offers no CS-image event when csEvDir e₁ ≢ sv
csTail-css-noOffer : (l : Link) (cl sv : Dir) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X} → csEvDir e₁ ≢ sv
  → ¬ IoOffers (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
       ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))))) (ιCS e₁) a
csTail-css-noOffer l cl sv css bfc bfs ip e₁ ¬sv =
  SStep.⦀-noOffer (decCSs l sv css) _ (decCSs-dir-noOffer l sv css e₁ ¬sv)
    (csTail-bfc-noOffer l cl sv bfc bfs ip e₁)

-- which driven CS peer of the bundle fired the CS-image event (+ target + abstract step)
data BundleCSEvR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : CS.CSEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bcscE : (csc′ : CScPos)
        → Bd′ ≡ bundleG l cl sv csc′ css bfc bfs ip
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absBundleG l cl sv csc′ css bfc bfs ip
        → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a Bd′
  bcssE : (css′ : CSsPos)
        → Bd′ ≡ bundleG l cl sv csc css′ bfc bfs ip
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absBundleG l cl sv csc css′ bfc bfs ip
        → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a CS-client driven step into the bundle result (target index is the
-- exact `⦀`-nesting the peel refines `Bd′` to; abstract step via `absBundle-CSc-ev`)
finishCSc-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decCSc l cl csc ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (P′
        ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))))))))
finishCSc-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simCSc′ l cl csc sM
... | _ , csc′ , _ , _ , Meq , aStep0 =
      bcscE csc′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (z
               ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (LFclientA l cl ⦀ LFserverA l sv))))))))))) Meq)
        (absBundle-CSc-ev l cl sv csc css bfc bfs ip {qcc′ = csc′} cl≢sv
          (sym (apiDir-inj (csc-ev-dir l cl csc sM) (csApiDir e₁))) aStep0)

-- fold a CS-server driven step into the bundle result
finishCSs-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decCSs l sv css ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (P′
        ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))))))))
finishCSs-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simCSs′ l sv css sM
... | _ , css′ , _ , _ , Meq , aStep0 =
      bcssE css′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (z
               ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (LFclientA l cl ⦀ LFserverA l sv))))))))))) Meq)
        (absBundle-CSs-ev l cl sv csc css bfc bfs ip {qcs′ = css′} cl≢sv
          (sym (apiDir-inj (css-ev-dir l sv css sM) (csApiDir e₁))) aStep0)

-- 12-peer bundle ev-inversion (CS): peel each `⦀`, refute the ten siblings, invert the driven CS peer
bundle-CS-ev-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a Bd′
bundle-CS-ev-inv l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL  _ sK     = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
... | PEA.evBoth _ sK _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL  _ sK     = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
...   | PEA.evBoth _ sK _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = finishCSc-ev l cl sv csc css bfc bfs ip cl≢sv sM
...     | PEA.evBoth _ sM sTail =
            ⊥-elim (csTail-css-noOffer l cl sv css bfc bfs ip e₁
                      (λ q → cl≢sv (trans (apiDir-inj (csc-ev-dir l cl csc sM) (csApiDir e₁)) q))
                      (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = finishCSs-ev l cl sv csc css bfc bfs ip cl≢sv sM
...       | PEA.evBoth _ sM sTail =
              ⊥-elim (csTail-bfc-noOffer l cl sv bfc bfs ip e₁ (_ , sTail))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = ⊥-elim (decBFc-noCSgen l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (decBFc-noCSgen l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = ⊥-elim (decBFs-noCSgen l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (decBFs-noCSgen l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (LFclientA l cl) (LFserverA l sv) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (LFclientA-noOffer l cl (ιLF⁻¹∘ιCS e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (LFclientA-noOffer l cl (ιLF⁻¹∘ιCS e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (LFserverA-noOffer l sv (ιLF⁻¹∘ιCS e₁) (_ , qs))

------------------------------------------------------------------------
-- GAP-B L4 — the 12-peer bundle ev-inversion (DOWNWARD peel), BF side.
-- Dual of the CS peel: a BF-image event `ιBF e₁` is fired by exactly one of
-- the two driven BF peers; the ten siblings are refuted (inert KA/TS/LN/LF via
-- the `ιX⁻¹∘ιBF` cross-preimages; opposite-protocol CS via `decCS*-noBFgen`;
-- the same-protocol opposite-role driven peer via the direction leaf, cl ≢ sv).
------------------------------------------------------------------------

-- tail (TS ⦀ LN ⦀ LF) offers no BF-image event (all inert)
bfTail-tsc-noOffer : (l : Link) (cl sv : Dir) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (LFclientA l cl ⦀ LFserverA l sv))))) (ιBF e₁) a
bfTail-tsc-noOffer l cl sv ip e₁ =
  SStep.⦀-noOffer (decTSc l cl (tsc ip)) _ (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιBF e₁))
    (SStep.⦀-noOffer (decTSs l sv (tss ip)) _ (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιBF e₁))
      (SStep.⦀-noOffer (decLNc l cl (lnc ip)) _ (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιBF e₁))
        (SStep.⦀-noOffer (decLNs l sv (lns ip)) _ (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιBF e₁))
          (SStep.⦀-noOffer (LFclientA l cl) (LFserverA l sv)
            (LFclientA-noOffer l cl (ιLF⁻¹∘ιBF e₁))
            (LFserverA-noOffer l sv (ιLF⁻¹∘ιBF e₁))))))

-- tail (decBFs ⦀ TS ⦀ …) offers no BF-image event when bfEvDir e₁ ≢ sv
bfTail-bfs-noOffer : (l : Link) (cl sv : Dir) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X} → bfEvDir e₁ ≢ sv
  → ¬ IoOffers (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))) (ιBF e₁) a
bfTail-bfs-noOffer l cl sv bfs ip e₁ ¬sv =
  SStep.⦀-noOffer (decBFs l sv bfs) _ (decBFs-dir-noOffer l sv bfs e₁ ¬sv)
    (bfTail-tsc-noOffer l cl sv ip e₁)

-- which driven BF peer of the bundle fired the BF-image event (+ target + abstract step)
data BundleBFEvR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bcbcE : (bfc′ : BFcPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc′ bfs ip
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBundleG l cl sv csc css bfc′ bfs ip
        → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a Bd′
  bcbsE : (bfs′ : BFsPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs′ ip
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs′ ip
        → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a BF-client driven step into the bundle result
finishBFc-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (P′
        ⦀ (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))))))))
finishBFc-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simBFc′ l cl bfc sM
... | _ , bfc′ , _ , _ , Meq , aStep0 =
      bcbcE bfc′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (z
               ⦀ (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (LFclientA l cl ⦀ LFserverA l sv))))))))))) Meq)
        (absBundle-BFc-ev l cl sv csc css bfc bfs ip {qbc′ = bfc′} cl≢sv
          (sym (apiDir-inj (bfc-ev-dir l cl bfc sM) (bfApiDir e₁))) aStep0)

-- fold a BF-server driven step into the bundle result
finishBFs-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (P′
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (LFclientA l cl ⦀ LFserverA l sv)))))))))))
finishBFs-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simBFs′ l sv bfs sM
... | _ , bfs′ , _ , _ , Meq , aStep0 =
      bcbsE bfs′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (z
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (LFclientA l cl ⦀ LFserverA l sv))))))))))) Meq)
        (absBundle-BFs-ev l cl sv csc css bfc bfs ip {qbs′ = bfs′} cl≢sv
          (sym (apiDir-inj (bfs-ev-dir l sv bfs sM) (bfApiDir e₁))) aStep0)

-- 12-peer bundle ev-inversion (BF): peel each `⦀`, refute the ten siblings, invert the driven BF peer
bundle-BF-ev-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a Bd′
bundle-BF-ev-inv l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL  _ sK     = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
... | PEA.evBoth _ sK _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL  _ sK     = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
...   | PEA.evBoth _ sK _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = ⊥-elim (decCSc-noBFgen l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (decCSc-noBFgen l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = ⊥-elim (decCSs-noBFgen l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (decCSs-noBFgen l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = finishBFc-ev l cl sv csc css bfc bfs ip cl≢sv sM
...         | PEA.evBoth _ sM sTail =
              ⊥-elim (bfTail-bfs-noOffer l cl sv bfs ip e₁
                        (λ q → cl≢sv (trans (apiDir-inj (bfc-ev-dir l cl bfc sM) (bfApiDir e₁)) q))
                        (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = finishBFs-ev l cl sv csc css bfc bfs ip cl≢sv sM
...           | PEA.evBoth _ sM sTail =
                ⊥-elim (bfTail-tsc-noOffer l cl sv ip e₁ (_ , sTail))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (LFclientA l cl) (LFserverA l sv) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (LFclientA-noOffer l cl (ιLF⁻¹∘ιBF e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (LFclientA-noOffer l cl (ιLF⁻¹∘ιBF e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (LFserverA-noOffer l sv (ιLF⁻¹∘ιBF e₁) (_ , qs))


------------------------------------------------------------------------
-- GAP-B LINK-pinning leaf (mirror of the DIRECTION layer).  Each driven
-- peer at any position fires only its OWN link's api/done events, so two
-- distinct-link bundles never fire the same api event (the node two-link
-- ⦀ evBoth refutation for the visible/api case).
------------------------------------------------------------------------

-- the link component of a ChainSync source event
csEvLink : {X : Set 0ℓ} → CS.CSEv X → Link
csEvLink (CS.sendCS l d)    = l
csEvLink (CS.receiveCS l d) = l
csEvLink (CS.apiCSev l d m) = l
csEvLink (CS.doneCS l d)    = l

-- the link component of a BlockFetch source event
bfEvLink : {X : Set 0ℓ} → BF.BFEv X → Link
bfEvLink (BF.sendBF l d)    = l
bfEvLink (BF.receiveBF l d) = l
bfEvLink (BF.apiBFev l d m) = l
bfEvLink (BF.doneBF l d)    = l

-- LINK: decCSc-src-link — the visible source step of a fine position fires
-- an event whose link component is `l` (csEvLink extracts it).
decCSc-src-link : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSc-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → csEvLink e₁ ≡ l
-- head stIdle : fires apiCSev sendCSRequestNext / FindIntersect / Done
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRequestNext} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} {a} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSDone} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollForward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollBackward}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollforward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollback}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
-- head stCanAwait : fires receiveCS RollForward / RollBackward / AwaitReply
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
-- head stMustReply : fires receiveCS RollForward / RollBackward
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
-- head stIntersect : fires receiveCS IntersectFound / IntersectNotFound
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSc-src-link l d (csHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid csReqNext1 : fires sendCS payload → csSil stCanAwait
decCSc-src-link l d csReqNext1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d csReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-link l d csReqNext1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-link l d csReqNext1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
-- mid csFindInt1 ps : fires sendCS payload → csSil stIntersect
decCSc-src-link l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-link l d (csFindInt1 ps) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-link l d (csFindInt1 ps) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
-- mid csDone1 : fires sendCS payload → csSil stDone
decCSc-src-link l d csDone1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d csDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-link l d csDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-link l d csDone1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
-- mid csRF1 : fires apiCSev recvCSRollforward (h,t) → csSil stIdle
decCSc-src-link l d (csRF1 h t) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollforward) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (h , t)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csRF1 h t) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-link l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-link l d (csRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
-- mid csRB1 : fires apiCSev recvCSRollback (pt,tp) → csSil stIdle
decCSc-src-link l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollback) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-link l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-link l d (csRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
-- mid csIF1 : fires apiCSev recvCSIntersectFound (pt,tp) → csSil stIdle
decCSc-src-link l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-link l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-link l d (csIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
-- mid csINF1 : fires apiCSev recvCSIntersectNotFound tp → csSil stIdle
decCSc-src-link l d (csINF1 tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectNotFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ tp
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csINF1 tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-link l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-link l d (csINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
-- loop re-entry csSil : forces to `sil`, no visible step
decCSc-src-link l d (csSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decCSs-src-link — the visible source step of a fine position fires
-- an event whose link component is `l` (csEvLink extracts it).
decCSs-src-link : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSs-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → csEvLink e₁ ≡ l
-- head stIdle : receives RequestNext / FindIntersect / Done on the wire
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
-- head stCanAwait : sends RollForward / RollBackward / AwaitReply via api
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
-- head stMustReply : sends RollForward / RollBackward via api
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
-- head stIntersect : sends IntersectFound / IntersectNotFound via api
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollForward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollBackward}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollforward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollback}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSRequestNext}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSs-src-link l d (ssHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid ssReqNext1 : fires api reqCSRequestNext (Prefix₀) → ssSil stCanAwait
decCSs-src-link l d ssReqNext1 {e₁ = CS.apiCSev l' d' m} s with step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSRequestNext) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decCSs-src-link l d ssReqNext1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-link l d ssReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-link l d ssReqNext1 {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
-- mid ssFindInt1 ps : fires api reqCSFindIntersect ps (Output) → ssSil stIntersect
decCSs-src-link l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSFindIntersect) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ CS.DecEq-ListPoint ⦄ a ps
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-link l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-link l d (ssFindInt1 ps) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
-- mid ssDone1 : fires doneCS (Prefix₀) → ssSil stDone
decCSs-src-link l d ssDone1 {e₁ = CS.doneCS l' d'} s with step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.doneCS l d) (_ , CS.doneCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decCSs-src-link l d ssDone1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-link l d ssDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-link l d ssDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
-- mid ssRF1 : fires sendCS payload → ssSil stIdle
decCSs-src-link l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-link l d (ssRF1 h t) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-link l d (ssRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
-- mid ssRB1 : fires sendCS payload → ssSil stIdle
decCSs-src-link l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-link l d (ssRB1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-link l d (ssRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
-- mid ssAw1 : fires sendCS payload → ssSil stMustReply
decCSs-src-link l d ssAw1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d ssAw1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-link l d ssAw1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-link l d ssAw1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
-- mid ssIF1 : fires sendCS payload → ssSil stIdle
decCSs-src-link l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-link l d (ssIF1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-link l d (ssIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
-- mid ssINF1 : fires sendCS payload → ssSil stIdle
decCSs-src-link l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-link l d (ssINF1 tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-link l d (ssINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
-- loop re-entry ssSil : forces to `sil`, no visible step
decCSs-src-link l d (ssSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decBFc-src-link — the visible source step of a fine position fires
-- an event whose link component is `l` (bfEvLink extracts it).
decBFc-src-link : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFc-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → bfEvLink e₁ ≡ l
-- head stIdle : sends RequestRange / ClientDone via api
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFRequestRange} {a} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFClientDone} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' recvBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' reqBFRange}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
-- head stBusy : receives StartBatch / NoBlocks (both go straight to a re-entry sil)
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
-- head stStreaming : receives Block (→ bcBlk1) / BatchDone (→ re-entry sil)
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
-- head stDone : `ret`, no visible step
decBFc-src-link l d (bcHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bcReq1 r : fires sendBF payload → bcSil stBusy
decBFc-src-link l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-link l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-link l d (bcReq1 r) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-link l d (bcReq1 r) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
-- mid bcDone1 : fires sendBF payload → bcSil stDone
decBFc-src-link l d bcDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-link l d bcDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-link l d bcDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-link l d bcDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
-- mid bcBlk1 b : fires apiBFev recvBFBlock b → bcSil stStreaming
decBFc-src-link l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d recvBFBlock) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-link l d (bcBlk1 b) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-link l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-link l d (bcBlk1 b) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
-- loop re-entry bcSil : forces to `sil`, no visible step
decBFc-src-link l d (bcSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decBFs-src-link — the visible source step of a fine position fires
-- an event whose link component is `l` (bfEvLink extracts it).
decBFs-src-link : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFs-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → bfEvLink e₁ ≡ l
-- head stIdle : receives RequestRange (→ bsReq1) / ClientDone (→ bsDone1)
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
-- head stBusy : sends StartBatch (→ bsStart1) / NoBlocks (→ bsNoBlk1) via api
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBatchDone}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
-- head stStreaming : sends Block (→ bsBlk1) / BatchDone (→ bsBatchDone1) via api
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBlock} {a} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBatchDone} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFStartBatch}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}     s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
-- head stDone : `ret`
decBFs-src-link l d (bsHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bsReq1 r : fires api reqBFRange r (Output) → bsSil stBusy
decBFs-src-link l d (bsReq1 r) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d reqBFRange) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d (bsReq1 r) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-link l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-link l d (bsReq1 r) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
-- mid bsDone1 : fires doneBF (Prefix₀) → bsSil stDone
decBFs-src-link l d bsDone1 {e₁ = BF.doneBF l' d'} s with step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.doneBF l d) (_ , BF.doneBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decBFs-src-link l d bsDone1 {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-link l d bsDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-link l d bsDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
-- mid bsStart1 : fires sendBF payload → bsSil stStreaming
decBFs-src-link l d bsStart1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d bsStart1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-link l d bsStart1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-link l d bsStart1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
-- mid bsNoBlk1 : fires sendBF payload → bsSil stIdle
decBFs-src-link l d bsNoBlk1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d bsNoBlk1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-link l d bsNoBlk1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-link l d bsNoBlk1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
-- mid bsBlk1 b : fires sendBF payload → bsSil stStreaming
decBFs-src-link l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-link l d (bsBlk1 b) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-link l d (bsBlk1 b) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
-- mid bsBatchDone1 : fires sendBF payload → bsSil stIdle
decBFs-src-link l d bsBatchDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d bsBatchDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-link l d bsBatchDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-link l d bsBatchDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
-- loop re-entry bsSil : forces to `sil`, no visible step
decBFs-src-link l d (bsSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- a Net_Api event carrying link `l` in its link component (exactly the
-- constructor shapes the CS/BF peers emit under ιCS/ιBF)
data ApiHasLink (l : Link) : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  ahlIn   : ∀ {d ch} → ApiHasLink l (input  l d ch)
  ahlOut  : ∀ {d ch} → ApiHasLink l (output l d ch)
  ahlDone : ∀ {d ch} → ApiHasLink l (done   l d ch)
  ahlCS   : ∀ {d m}  → ApiHasLink l (apiCS  l d m)
  ahlBF   : ∀ {d m}  → ApiHasLink l (apiBF  l d m)

-- the link of a fixed event is unique (both witnesses pin the same slot)
apiLink-inj : {X : Set 0ℓ} {e : Net_Api Payload X} {l l′ : Link}
  → ApiHasLink l e → ApiHasLink l′ e → l ≡ l′
apiLink-inj ahlIn   ahlIn   = refl
apiLink-inj ahlOut  ahlOut  = refl
apiLink-inj ahlDone ahlDone = refl
apiLink-inj ahlCS   ahlCS   = refl
apiLink-inj ahlBF   ahlBF   = refl

-- ιCS carries the source link into the Net_Api event
csApiLink : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ApiHasLink (csEvLink e₁) (ιCS e₁)
csApiLink (CS.sendCS l d)    = ahlIn
csApiLink (CS.receiveCS l d) = ahlOut
csApiLink (CS.apiCSev l d m) = ahlCS
csApiLink (CS.doneCS l d)    = ahlDone

-- ιBF carries the source link into the Net_Api event
bfApiLink : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ApiHasLink (bfEvLink e₁) (ιBF e₁)
bfApiLink (BF.sendBF l d)    = ahlIn
bfApiLink (BF.receiveBF l d) = ahlOut
bfApiLink (BF.apiBFev l d m) = ahlBF
bfApiLink (BF.doneBF l d)    = ahlDone

-- the link a driven CS-client step exposes on the Net_Api event
csc-ev-link : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
csc-ev-link l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιCS-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιCS e₁)) (decCSc-src-link l d pos srcStep) (csApiLink e₁))

-- the link a driven CS-server step exposes on the Net_Api event
css-ev-link : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
css-ev-link l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιCS-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιCS e₁)) (decCSs-src-link l d pos srcStep) (csApiLink e₁))

-- the link a driven BF-client step exposes on the Net_Api event
bfc-ev-link : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
bfc-ev-link l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιBF-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιBF e₁)) (decBFc-src-link l d pos srcStep) (bfApiLink e₁))

-- the link a driven BF-server step exposes on the Net_Api event
bfs-ev-link : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
bfs-ev-link l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιBF-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιBF e₁)) (decBFs-src-link l d pos srcStep) (bfApiLink e₁))


------------------------------------------------------------------------
-- GAP-B — bundle link-pinning.  A bundleG step on a CS/BF-image event pins the
-- bundle's OWN link (ApiHasLink l e), so two distinct-link bundles of a node
-- never both fire the same api event (the node two-link ⦀ evBoth refutation).
------------------------------------------------------------------------

-- a bundleG CS-image step pins the bundle's link
bundleCS-ev-link : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → ApiHasLink l (ιCS e₁)
bundleCS-ev-link l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL  _ sK     = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
... | PEA.evBoth _ sK _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL  _ sK     = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
...   | PEA.evBoth _ sK _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = csc-ev-link l cl csc sM
...     | PEA.evBoth _ sM sTail =
            ⊥-elim (csTail-css-noOffer l cl sv css bfc bfs ip e₁
                      (λ q → cl≢sv (trans (apiDir-inj (csc-ev-dir l cl csc sM) (csApiDir e₁)) q))
                      (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = css-ev-link l sv css sM
...       | PEA.evBoth _ sM sTail =
              ⊥-elim (csTail-bfc-noOffer l cl sv bfc bfs ip e₁ (_ , sTail))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = ⊥-elim (decBFc-noCSgen l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (decBFc-noCSgen l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = ⊥-elim (decBFs-noCSgen l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (decBFs-noCSgen l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (LFclientA l cl) (LFserverA l sv) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (LFclientA-noOffer l cl (ιLF⁻¹∘ιCS e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (LFclientA-noOffer l cl (ιLF⁻¹∘ιCS e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (LFserverA-noOffer l sv (ιLF⁻¹∘ιCS e₁) (_ , qs))

-- a bundleG BF-image step pins the bundle's link
bundleBF-ev-link : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → ApiHasLink l (ιBF e₁)
bundleBF-ev-link l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL  _ sK     = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
... | PEA.evBoth _ sK _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL  _ sK     = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
...   | PEA.evBoth _ sK _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = ⊥-elim (decCSc-noBFgen l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (decCSc-noBFgen l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = ⊥-elim (decCSs-noBFgen l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (decCSs-noBFgen l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = bfc-ev-link l cl bfc sM
...         | PEA.evBoth _ sM sTail =
              ⊥-elim (bfTail-bfs-noOffer l cl sv bfs ip e₁
                        (λ q → cl≢sv (trans (apiDir-inj (bfc-ev-dir l cl bfc sM) (bfApiDir e₁)) q))
                        (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = bfs-ev-link l sv bfs sM
...           | PEA.evBoth _ sM sTail =
                ⊥-elim (bfTail-tsc-noOffer l cl sv ip e₁ (_ , sTail))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (LFclientA l cl) (LFserverA l sv) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (LFclientA-noOffer l cl (ιLF⁻¹∘ιBF e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (LFclientA-noOffer l cl (ιLF⁻¹∘ιBF e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (LFserverA-noOffer l sv (ιLF⁻¹∘ιBF e₁) (_ , qs))


------------------------------------------------------------------------
-- GAP-B DRIVER link-pinning.  Every driver phase fires an api event on the
-- driver's OWN link (`apiCS l d …` / `apiBF l d …`); the fired event's link is
-- pinned by extracting the fired label and matching it against the phase's
-- head channel (`refl` unifies `e` to `apiCS/apiBF l d …` ⇒ `ahlCS`/`ahlBF`).
-- Needed to ALIGN the driver's firing link with the bundle's in `nodeX-ev-inv`
-- (and to refute the two-driver `⦀` evBoth of nodes A/D).
------------------------------------------------------------------------

-- an `Output` visible step exposes its own label (the fired event ≡ the head
-- channel `ce` at value `v`) — the label-returning twin of `output-ev-inv`
output-ev-lab : {R : Set} {B : Set 0ℓ} {deqB : DecEq B} {ce : Net_Api Payload B} {v : B}
    {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
  → (Output ⦃ deqB ⦄ ce v P) ─[ ev (evl (evLabel X e a)) ]─► M
  → evl {R = R} (evLabel X e a) ≡ evl (evLabel B ce v)
output-ev-lab {R} {B} {deqB} {ce} {v} {P} {X} {e} {a} (sVis refl br)
    with Net_Api-≟ {Payload} (B , ce) (X , e)
... | no  ¬eq  = ⊥-elim (nothing-absurd br)
... | yes refl with _≟_ ⦃ deqB ⦄ a v
...   | yes refl = refl
...   | no  _    = ⊥-elim (nothing-absurd br)

-- a `Prefix` visible step exposes its own label (the fired event ≡ the head
-- channel `ce`) — the label-returning twin of `prefix-ev-inv`
prefix-ev-lab : {R : Set} {A : Set 0ℓ} {ce : Net_Api Payload A}
    {P : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
  → (Prefix ce P) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ x ∈ A ] (evl {R = R} (evLabel X e a) ≡ evl (evLabel A ce x))
prefix-ev-lab {a = a} (sVis refl br) with Prefix-cont-fires br
... | refl , _ , _ = a , refl

-- producer-driver link-pinning: every phase fires apiCS/apiBF on link `l`
decProd-ev-link : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M → ApiHasLink l e
decProd-ev-link l d blk pp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlCS
decProd-ev-link l d blk pp1 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlCS
decProd-ev-link l d blk pp2 step with output-ev-lab step
... | refl = ahlCS
decProd-ev-link l d blk pp3 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlBF
decProd-ev-link l d blk pp4 step with output-ev-lab step
... | refl = ahlBF
decProd-ev-link l d blk pp5 step with output-ev-lab step
... | refl = ahlBF
decProd-ev-link l d blk pp6 step with output-ev-lab step
... | refl = ahlBF
decProd-ev-link l d blk pp7 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlDone
decProd-ev-link l d blk pp8 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlDone
decProd-ev-link l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- consumer-driver link-pinning: every phase fires apiCS/apiBF on link `l`
decCons-ev-link : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M → ApiHasLink l e
decCons-ev-link l d b cp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlCS
decCons-ev-link l d b cp1 step with prefix-ev-lab step
... | _ , refl = ahlCS
decCons-ev-link l d b cp2 step with output-ev-lab step
... | refl = ahlBF
decCons-ev-link l d b cp3 step with prefix-ev-lab step
... | _ , refl = ahlBF
decCons-ev-link l d b cp4 step with output-ev-lab step
... | refl = ahlBF
decCons-ev-link l d b cp5 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlCS
decCons-ev-link l d b cp6 step = ⊥-elim (ret-no-ev {P = decCons l d b cp6} refl step)

-- node-D consume-driver link-pinning (`decCons … >> Skip`): fire through the
-- bind, pin the inner consume event's link
decConsD-ev-link : (l : Link) (cph : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cph ─[ ev (evl (evLabel X e a)) ]─► M → ApiHasLink l e
decConsD-ev-link l (consD b cp0) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp0 sc
decConsD-ev-link l (consD b cp1) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp1 sc
decConsD-ev-link l (consD b cp2) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp2 sc
decConsD-ev-link l (consD b cp3) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp3 sc
decConsD-ev-link l (consD b cp4) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp4 sc
decConsD-ev-link l (consD b cp5) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp5 sc
decConsD-ev-link l (consD b cp6) step = ⊥-elim (ret-no-ev {P = decConsD l (consD b cp6)} refl step)

-- relay-driver link-pinning (`consume l₁ hi >>= produce l₂ hi`): consuming pins
-- `l₁`; the cp6 handoff + producing leg pin `l₂` (reusing `decProd-ev-link`)
decCP-ev-link : (l₁ l₂ : Link) (ph : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel X e a)) ]─► M
  → ApiHasLink l₁ e ⊎ ApiHasLink l₂ e
decCP-ev-link l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp0 sc)
decCP-ev-link l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp1 sc)
decCP-ev-link l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp2 sc)
decCP-ev-link l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp3 sc)
decCP-ev-link l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp4 sc)
decCP-ev-link l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp5 sc)
decCP-ev-link l₁ l₂ (consuming b cp6) step = inj₂ (decProd-ev-link l₂ hi b pp0 (step-fcong refl step))
decCP-ev-link l₁ l₂ (producing b pp) step = inj₂ (decProd-ev-link l₂ hi b pp step)


------------------------------------------------------------------------
-- GAP-B LEAF 1 — abstract-bundle idle-LINK sibling non-offers.  An idle
-- same-protocol abstract bundle at a DIFFERENT link l never offers the driven
-- peer's event (which carries the driven link cl ≢ l): every firing
-- clause of the abstract `nxt` table guards on `l′ ≟ l`, so a wrong-link
-- event falls to the per-table catch-all `nothing`.  SCRIPT-GENERATED
-- (`.superpowers/sdd/gen-l4-link.py`).
------------------------------------------------------------------------
-- csSnxt-link-no: a wrong-link CS-image event (csEvLink e₁ ≢ l)
-- has no csSnxt table edge (every firing clause guards on l′ ≟ l)
csSnxt-link-no : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → NS.csSnxt l d q (X , ιCS e₁) a ≡ nothing
csSnxt-link-no l d NS.csIdle (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' reqCSRequestNext) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSAwaitReply) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollForward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollBackward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csAfi _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSIntersectFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csDdone (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csDdone (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csDdone (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d NS.csDdone (CS.doneCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csMust (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSRollForward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSRollBackward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWrf _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csWrf _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWrf _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d (NS.csWrf _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWrb _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csWrb _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWrb _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d (NS.csWrb _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csWar (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csWar (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csWar (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d NS.csWar (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWif _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csWif _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWif _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d (NS.csWif _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWin _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csWin _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWin _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d (NS.csWin _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csTerm (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csTerm (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csTerm (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d NS.csTerm (CS.doneCS l' d') ¬eq = refl

-- csCnxt-link-no: a wrong-link CS-image event (csEvLink e₁ ≢ l)
-- has no csCnxt table edge (every firing clause guards on l′ ≟ l)
csCnxt-link-no : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → NS.csCnxt l d q (X , ιCS e₁) a ≡ nothing
csCnxt-link-no l d NS.ccIdle (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRequestNext) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSFindIntersect) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccWreq (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccWreq (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccWreq (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccWreq (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccWfi _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccWfi _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccWfi _) (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d (NS.ccWfi _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccWdone (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccWdone (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccWdone (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccWdone (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollforward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollback) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccTerm (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccTerm (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccTerm (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccTerm (CS.doneCS l' d') ¬eq = refl

-- bfCnxt-link-no: a wrong-link BF-image event (bfEvLink e₁ ≢ l)
-- has no bfCnxt table edge (every firing clause guards on l′ ≟ l)
bfCnxt-link-no : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → NS.bfCnxt l d q (X , ιBF e₁) a ≡ nothing
bfCnxt-link-no l d NS.bcIdle (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFRequestRange) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFClientDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcWrr _) (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d (NS.bcWrr _) (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcWrr _) (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d (NS.bcWrr _) (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcWcd (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcWcd (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcWcd (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d NS.bcWcd (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' recvBFBlock) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcTerm (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcTerm (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcTerm (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d NS.bcTerm (BF.doneBF l' d') ¬eq = refl

-- bfSnxt-link-no: a wrong-link BF-image event (bfEvLink e₁ ≢ l)
-- has no bfSnxt table edge (every firing clause guards on l′ ≟ l)
bfSnxt-link-no : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → NS.bfSnxt l d q (X , ιBF e₁) a ≡ nothing
bfSnxt-link-no l d NS.bsIdle (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' reqBFRange) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFStartBatch) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFNoBlocks) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsDdone (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsDdone (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsDdone (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsDdone (BF.doneBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsWsb (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsWsb (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWsb (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsWsb (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFBlock) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFBatchDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWnb (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsWnb (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWnb (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsWnb (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsWblk _) (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d (NS.bsWblk _) (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsWblk _) (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d (NS.bsWblk _) (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWbd (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsWbd (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWbd (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsWbd (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsTerm (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsTerm (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsTerm (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsTerm (BF.doneBF l' d') ¬eq = refl

-- absCSs-link-noBoth: an idle same-protocol bundle at a DIFFERENT link does
-- not fire the driven peer's event (which is on link cl ≢ l) (via csSnxt-link-no)
absCSs-link-noBoth : (l : Link) (sv : Dir) (q : CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → ¬ IoOffers (absCSs l sv q) (ιCS e₁) a
absCSs-link-noBoth l sv q e₁ {a} ¬l with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l sv })
                   (coarsenCSs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l sv })
                   (coarsenCSs q) {e = ιCS e₁} {a = a} fEq (csSnxt-link-no l sv (coarsenCSs q) e₁ {a = a} ¬l))

-- absCSc-link-noBoth: an idle same-protocol bundle at a DIFFERENT link does
-- not fire the driven peer's event (which is on link cl ≢ l) (via csCnxt-link-no)
absCSc-link-noBoth : (l : Link) (sv : Dir) (q : CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → ¬ IoOffers (absCSc l sv q) (ιCS e₁) a
absCSc-link-noBoth l sv q e₁ {a} ¬l with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l sv })
                   (coarsenCSc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l sv })
                   (coarsenCSc q) {e = ιCS e₁} {a = a} fEq (csCnxt-link-no l sv (coarsenCSc q) e₁ {a = a} ¬l))

-- absBFc-link-noBoth: an idle same-protocol bundle at a DIFFERENT link does
-- not fire the driven peer's event (which is on link cl ≢ l) (via bfCnxt-link-no)
absBFc-link-noBoth : (l : Link) (sv : Dir) (q : BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → ¬ IoOffers (absBFc l sv q) (ιBF e₁) a
absBFc-link-noBoth l sv q e₁ {a} ¬l with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l sv })
                   (coarsenBFc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l sv })
                   (coarsenBFc q) {e = ιBF e₁} {a = a} fEq (bfCnxt-link-no l sv (coarsenBFc q) e₁ {a = a} ¬l))

-- absBFs-link-noBoth: an idle same-protocol bundle at a DIFFERENT link does
-- not fire the driven peer's event (which is on link cl ≢ l) (via bfSnxt-link-no)
absBFs-link-noBoth : (l : Link) (sv : Dir) (q : BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → ¬ IoOffers (absBFs l sv q) (ιBF e₁) a
absBFs-link-noBoth l sv q e₁ {a} ¬l with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l sv })
                   (coarsenBFs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l sv })
                   (coarsenBFs q) {e = ιBF e₁} {a = a} fEq (bfSnxt-link-no l sv (coarsenBFs q) e₁ {a = a} ¬l))



------------------------------------------------------------------------
-- GAP-B LEAF 2 — driver io-non-offer.  The produce/consume/relay drivers
-- fire ONLY apiCS/apiBF events (their phases are api prefixes/outputs), never
-- an io `input`/`output`.  We first pin the fired head as apiCS-or-apiBF
-- (`IsApiCSBF`, a textual mirror of the `*-ev-link` link-pinnings), then a
-- non-apiCSBF (io) event refutes any driver offer — the `¬ IoOffers driver`
-- side of the node's `∥⇘apiES⇙` io-solo peel.
------------------------------------------------------------------------

-- witness that a Net_Api event is an api CS/BF event (the only kinds a driver fires)
data IsApiCSBF : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  aicCS   : ∀ {l d m}  → IsApiCSBF (apiCS l d m)
  aicBF   : ∀ {l d m}  → IsApiCSBF (apiBF l d m)
  aicDone : ∀ {l d ch} → IsApiCSBF (done  l d ch)   -- driver receives the CS server's api done callback

-- produce-driver fires an api CS/BF head (mirror of decProd-ev-link)
decProd-apiCSBF : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M → IsApiCSBF e
decProd-apiCSBF l d blk pp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCS
decProd-apiCSBF l d blk pp1 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCS
decProd-apiCSBF l d blk pp2 step with output-ev-lab step
... | refl = aicCS
decProd-apiCSBF l d blk pp3 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicBF
decProd-apiCSBF l d blk pp4 step with output-ev-lab step
... | refl = aicBF
decProd-apiCSBF l d blk pp5 step with output-ev-lab step
... | refl = aicBF
decProd-apiCSBF l d blk pp6 step with output-ev-lab step
... | refl = aicBF
decProd-apiCSBF l d blk pp7 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicDone
decProd-apiCSBF l d blk pp8 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicDone
decProd-apiCSBF l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- consume-driver fires an api CS/BF head (mirror of decCons-ev-link)
decCons-apiCSBF : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M → IsApiCSBF e
decCons-apiCSBF l d b cp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCS
decCons-apiCSBF l d b cp1 step with prefix-ev-lab step
... | _ , refl = aicCS
decCons-apiCSBF l d b cp2 step with output-ev-lab step
... | refl = aicBF
decCons-apiCSBF l d b cp3 step with prefix-ev-lab step
... | _ , refl = aicBF
decCons-apiCSBF l d b cp4 step with output-ev-lab step
... | refl = aicBF
decCons-apiCSBF l d b cp5 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCS
decCons-apiCSBF l d b cp6 step = ⊥-elim (ret-no-ev {P = decCons l d b cp6} refl step)

-- node-D consume-driver fires an api CS/BF head (mirror of decConsD-ev-link)
decConsD-apiCSBF : (l : Link) (cph : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cph ─[ ev (evl (evLabel X e a)) ]─► M → IsApiCSBF e
decConsD-apiCSBF l (consD b cp0) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp0 sc
decConsD-apiCSBF l (consD b cp1) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp1 sc
decConsD-apiCSBF l (consD b cp2) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp2 sc
decConsD-apiCSBF l (consD b cp3) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp3 sc
decConsD-apiCSBF l (consD b cp4) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp4 sc
decConsD-apiCSBF l (consD b cp5) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp5 sc
decConsD-apiCSBF l (consD b cp6) step = ⊥-elim (ret-no-ev {P = decConsD l (consD b cp6)} refl step)

-- relay-driver fires an api CS/BF head on one of its two links (mirror of decCP-ev-link)
decCP-apiCSBF : (l₁ l₂ : Link) (ph : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel X e a)) ]─► M → IsApiCSBF e
decCP-apiCSBF l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp0 sc
decCP-apiCSBF l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp1 sc
decCP-apiCSBF l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp2 sc
decCP-apiCSBF l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp3 sc
decCP-apiCSBF l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp4 sc
decCP-apiCSBF l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp5 sc
decCP-apiCSBF l₁ l₂ (consuming b cp6) step = decProd-apiCSBF l₂ hi b pp0 (step-fcong refl step)
decCP-apiCSBF l₁ l₂ (producing b pp) step = decProd-apiCSBF l₂ hi b pp step

-- driver io-non-offer: a non-apiCSBF (io) event has no produce-driver offer
decProd-io-no : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IsApiCSBF e → ¬ IoOffers (decProd l d blk pp) e a
decProd-io-no l d blk pp ¬api (_ , step) = ¬api (decProd-apiCSBF l d blk pp step)

-- driver io-non-offer: node-D consume driver
decConsD-io-no : (l : Link) (cph : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IsApiCSBF e → ¬ IoOffers (decConsD l cph) e a
decConsD-io-no l cph ¬api (_ , step) = ¬api (decConsD-apiCSBF l cph step)

-- driver io-non-offer: relay driver
decCP-io-no : (l₁ l₂ : Link) (ph : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IsApiCSBF e → ¬ IoOffers (decCP l₁ l₂ ph) e a
decCP-io-no l₁ l₂ ph ¬api (_ , step) = ¬api (decCP-apiCSBF l₁ l₂ ph step)


------------------------------------------------------------------------
-- GAP-B LEAF 1b — whole abstract-bundle idle-LINK non-offer.  An entire idle
-- `absBundleG` at link `l` offers NOTHING on a driven peer's event that lives
-- on a DIFFERENT link (`{cs,bf}EvLink e₁ ≢ l`): the same-protocol CS/BF peers
-- are refuted by the LINK leaf (LEAF 1 `abs*-link-noBoth`), the cross-protocol
-- KA/TS + opposite-protocol siblings by the committed `*-no{CS,BF}` leaves.
-- Composed over the eight `⦀` peers via `SStep.⦀-noOffer`.  This is the idle
-- sibling non-offer the node's two-link abstract `⦀-ev-L/R` reassembly needs.
------------------------------------------------------------------------

-- CS-image case: the whole idle bundle at `l` offers nothing on `ιCS e₁` (link ≢ l)
absBundleG-CS-link-noIoOffer : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) (ιCS e₁) a
absBundleG-CS-link-noIoOffer l cl sv qcc qcs qbc qbs ip e₁ ¬l =
  SStep.⦀-noOffer (absKAc l cl (kac ip)) _ (absKAc-noCS l cl (kac ip) e₁)
   (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-noCS l sv (kas ip) e₁)
    (SStep.⦀-noOffer (absCSc l cl qcc) _ (absCSc-link-noBoth l cl qcc e₁ ¬l)
     (SStep.⦀-noOffer (absCSs l sv qcs) _ (absCSs-link-noBoth l sv qcs e₁ ¬l)
      (SStep.⦀-noOffer (absBFc l cl qbc) _ (absBFc-noCS l cl qbc e₁)
       (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-noCS l sv qbs e₁)
        (SStep.⦀-noOffer (absTSc l cl (tsc ip)) (absTSs l sv (tss ip))
          (absTSc-noCS l cl (tsc ip) e₁) (absTSs-noCS l sv (tss ip) e₁)))))))

-- BF-image case: the whole idle bundle at `l` offers nothing on `ιBF e₁` (link ≢ l)
absBundleG-BF-link-noIoOffer : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) (ιBF e₁) a
absBundleG-BF-link-noIoOffer l cl sv qcc qcs qbc qbs ip e₁ ¬l =
  SStep.⦀-noOffer (absKAc l cl (kac ip)) _ (absKAc-noBF l cl (kac ip) e₁)
   (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-noBF l sv (kas ip) e₁)
    (SStep.⦀-noOffer (absCSc l cl qcc) _ (absCSc-noBF l cl qcc e₁)
     (SStep.⦀-noOffer (absCSs l sv qcs) _ (absCSs-noBF l sv qcs e₁)
      (SStep.⦀-noOffer (absBFc l cl qbc) _ (absBFc-link-noBoth l cl qbc e₁ ¬l)
       (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-link-noBoth l sv qbs e₁ ¬l)
        (SStep.⦀-noOffer (absTSc l cl (tsc ip)) (absTSs l sv (tss ip))
          (absTSc-noBF l cl (tsc ip) e₁) (absTSs-noBF l sv (tss ip) e₁)))))))


------------------------------------------------------------------------
-- GAP-B — node-A visible api-event inversion.  A node `= (bundleA linkAB ⦀
-- bundleA linkAC) ∥⇘apiES⇙ (decProd linkAB ⦀ decProd linkAC)`.  An api event
-- (∈ apiES) is a driver↔peer SYNC (`SStep.reflect-node-api`); the driver `⦀`
-- pins the firing link (evBoth by `apiLink-inj`+`linkAB≢linkAC`) and, via
-- `decProd-apiCSBF`, the protocol; the bundle `⦀` is aligned to the same link
-- and inverted by `bundle-{CS,BF}-ev-inv`; the driver phase by `decProd-ev-inv`.
-- The abstract node redoes the SAME sync (shared drivers; abstract bundle step
-- from the inversion; idle-link non-offer from `absBundleG-*-link-noIoOffer`).
-- Per-firing-link helpers (`nodeA-AB`/`nodeA-AC`) split protocol via FUNCTION
-- clauses so the deep bundle-peel `with`s never need ellipsis-popping.
------------------------------------------------------------------------

-- node-A visible-event result: the successor node-state + concrete/abstract match
data NodeAEvR (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (A′ : NetProc) : Set₁ where
  naEv : (na′ : SN.NodeStateA) → A′ ≡ decNodeA na′
       → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► absNodeA na′
       → NodeAEvR na e a A′

-- distinct node-A links (Fin 4 literals)
linkAB≢linkAC : ¬ (linkAB ≡ linkAC)
linkAB≢linkAC ()

-- driver on linkAC offers nothing on a linkAB-pinned api event (reuse apiLink-inj)
nodeA-drvAC-no : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkAB e → ¬ IoOffers (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) e a
nodeA-drvAC-no na ahl (_ , s) =
  linkAB≢linkAC (sym (apiLink-inj (decProd-ev-link linkAC hi b1 (SN.NodeStateA.prod-AC na) s) ahl))

-- driver on linkAB offers nothing on a linkAC-pinned api event
nodeA-drvAB-no : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkAC e → ¬ IoOffers (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) e a
nodeA-drvAB-no na ahl (_ , s) =
  linkAB≢linkAC (apiLink-inj (decProd-ev-link linkAB hi b1 (SN.NodeStateA.prod-AB na) s) ahl)

-- `produce` fires a `done` event ONLY at pp7 (ChainSync done-receipt, → pp8) and
-- pp8 (BlockFetch done-receipt, → pp9 = Skip): it pins the event to
-- `done l d N2N_ChainSync` / `done l d N2N_BlockFetch` and the target phase.  Used
-- by the `aicDone` co-move to reconstruct the driver leg + pin the event's protocol.
decProd-done-inv : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {a : ⊤U} {d₀ : Dir} {ch : IDs} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel ⊤U (done l d₀ ch) a)) ]─► M
  → (d₀ ≡ d) × ( (ch ≡ N2N_ChainSync  × M ≡ decProd l d blk pp8)
              ⊎ (ch ≡ N2N_BlockFetch × M ≡ decProd l d blk pp9) )
decProd-done-inv l d blk pp0 step with ⟶₀-ev-inv step
... | _ , () , _
decProd-done-inv l d blk pp1 step with ⟶₀-ev-inv step
... | _ , () , _
decProd-done-inv l d blk pp2 step with output-ev-lab step
... | ()
decProd-done-inv l d blk pp3 step with ⟶₀-ev-inv step
... | _ , () , _
decProd-done-inv l d blk pp4 step with output-ev-lab step
... | ()
decProd-done-inv l d blk pp5 step with output-ev-lab step
... | ()
decProd-done-inv l d blk pp6 step with output-ev-lab step
... | ()
decProd-done-inv l d blk pp7 step with ⟶₀-ev-inv step
... | _ , refl , refl = refl , inj₁ (refl , refl)
decProd-done-inv l d blk pp8 step with ⟶₀-ev-inv step
... | _ , refl , refl = refl , inj₂ (refl , refl)
decProd-done-inv l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- firing link = linkAB, protocol determined by `IsApiCSBF`/`ApiHasLink`
nodeA-AB : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁AB : NetProc}
  → apiES .mem (X , e) a
  → (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ─[ ev (evl (evLabel X e a)) ]─► D₁AB
  → IsApiCSBF e → ApiHasLink linkAB e
  → NodeAEvR na e a (B₁ ∥⇘ apiES ⇙ (D₁AB ⦀ decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)))
nodeA-AB na {X} {a = a} mem bStep sDAB aicCS (ahlCS {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.apiCSev linkAB d m} sBAB)
                     (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.apiCSev linkAB d m} sBAC)))
... | PEA.evR _ sBAC = ⊥-elim (linkAB≢linkAC (sym
        (apiLink-inj (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.apiCSev linkAB d m} sBAC) ahlCS)))
... | PEA.evL _ sBAB
    with bundle-CS-ev-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.apiCSev linkAB d m} sBAB
       | decProd-ev-inv linkAB hi b1 (SN.NodeStateA.prod-AB na) sDAB
...   | bcscE csc′ refl aStepAB | peR pp′ refl =
        naEv (SN.mkNodeA csc′ (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (CS.apiCSev linkAB d m) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na ahlCS))))
...   | bcssE css′ refl aStepAB | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) css′ (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (CS.apiCSev linkAB d m) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na ahlCS))))
nodeA-AB na {X} {a = a} mem bStep sDAB aicBF (ahlBF {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.apiBFev linkAB d m} sBAB)
                     (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.apiBFev linkAB d m} sBAC)))
... | PEA.evR _ sBAC = ⊥-elim (linkAB≢linkAC (sym
        (apiLink-inj (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.apiBFev linkAB d m} sBAC) ahlBF)))
... | PEA.evL _ sBAB
    with bundle-BF-ev-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.apiBFev linkAB d m} sBAB
       | decProd-ev-inv linkAB hi b1 (SN.NodeStateA.prod-AB na) sDAB
...   | bcbcE bfc′ refl aStepAB | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) bfc′ (SN.NodeStateA.bfS-AB na) pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (BF.apiBFev linkAB d m) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na ahlBF))))
...   | bcbsE bfs′ refl aStepAB | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) bfs′ pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (BF.apiBFev linkAB d m) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na ahlBF))))
-- linkAB `done` (ChainSync): the CS SERVER fires doneCS, synced with the produce driver's pp7 done-receipt
nodeA-AB na {X} {a = a} mem bStep sDAB aicDone (ahlDone {d} {ch})
  with decProd-done-inv linkAB hi b1 (SN.NodeStateA.prod-AB na) sDAB
nodeA-AB na {X} {a = a} mem bStep sDAB aicDone (ahlDone {d} {ch}) | refl , inj₁ (refl , refl)
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.doneCS linkAB hi} sBAB)
                     (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.doneCS linkAB hi} sBAC)))
... | PEA.evR _ sBAC = ⊥-elim (linkAB≢linkAC (sym
        (apiLink-inj (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.doneCS linkAB hi} sBAC) (ahlDone {d = hi} {ch = N2N_ChainSync}))))
... | PEA.evL _ sBAB
    with bundle-CS-ev-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.doneCS linkAB hi} sBAB
...   | bcscE csc′ refl aStepAB =
        naEv (SN.mkNodeA csc′ (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) pp8 (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (CS.doneCS linkAB hi) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na (ahlDone {d = hi} {ch = N2N_ChainSync})))))
...   | bcssE css′ refl aStepAB =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) css′ (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) pp8 (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (CS.doneCS linkAB hi) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na (ahlDone {d = hi} {ch = N2N_ChainSync})))))
-- linkAB `done` (BlockFetch): the BF SERVER fires doneBF, synced with the produce driver's pp8 done-receipt
nodeA-AB na {X} {a = a} mem bStep sDAB aicDone (ahlDone {d} {ch}) | refl , inj₂ (refl , refl)
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.doneBF linkAB hi} sBAB)
                     (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.doneBF linkAB hi} sBAC)))
... | PEA.evR _ sBAC = ⊥-elim (linkAB≢linkAC (sym
        (apiLink-inj (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.doneBF linkAB hi} sBAC) (ahlDone {d = hi} {ch = N2N_BlockFetch}))))
... | PEA.evL _ sBAB
    with bundle-BF-ev-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.doneBF linkAB hi} sBAB
...   | bcbcE bfc′ refl aStepAB =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) bfc′ (SN.NodeStateA.bfS-AB na) pp9 (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (BF.doneBF linkAB hi) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na (ahlDone {d = hi} {ch = N2N_BlockFetch})))))
...   | bcbsE bfs′ refl aStepAB =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) bfs′ pp9 (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (BF.doneBF linkAB hi) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na (ahlDone {d = hi} {ch = N2N_BlockFetch})))))

-- firing link = linkAC (mirror of nodeA-AB via `⦀-ev-R`)
nodeA-AC : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁AC : NetProc}
  → apiES .mem (X , e) a
  → (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decProd linkAC hi b1 (SN.NodeStateA.prod-AC na) ─[ ev (evl (evLabel X e a)) ]─► D₁AC
  → IsApiCSBF e → ApiHasLink linkAC e
  → NodeAEvR na e a (B₁ ∥⇘ apiES ⇙ (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ⦀ D₁AC))
nodeA-AC na {X} {a = a} mem bStep sDAC aicCS (ahlCS {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.apiCSev linkAC d m} sBAB)
                     (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.apiCSev linkAC d m} sBAC)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.apiCSev linkAC d m} sBAB) ahlCS))
... | PEA.evR _ sBAC
    with bundle-CS-ev-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.apiCSev linkAC d m} sBAC
       | decProd-ev-inv linkAC hi b1 (SN.NodeStateA.prod-AC na) sDAC
...   | bcscE csc′ refl aStepAC | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) pp′ (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (CS.apiCSev linkAC d m) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na ahlCS))))
...   | bcssE css′ refl aStepAC | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) css′ (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) pp′ (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (CS.apiCSev linkAC d m) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na ahlCS))))
nodeA-AC na {X} {a = a} mem bStep sDAC aicBF (ahlBF {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.apiBFev linkAC d m} sBAB)
                     (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.apiBFev linkAC d m} sBAC)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.apiBFev linkAC d m} sBAB) ahlBF))
... | PEA.evR _ sBAC
    with bundle-BF-ev-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.apiBFev linkAC d m} sBAC
       | decProd-ev-inv linkAC hi b1 (SN.NodeStateA.prod-AC na) sDAC
...   | bcbcE bfc′ refl aStepAC | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) bfc′ (SN.NodeStateA.bfS-AC na) pp′ (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (BF.apiBFev linkAC d m) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na ahlBF))))
...   | bcbsE bfs′ refl aStepAC | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) bfs′ pp′ (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (BF.apiBFev linkAC d m) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na ahlBF))))
-- linkAC `done` (ChainSync): mirror of the linkAB done co-move via `⦀-ev-R`
nodeA-AC na {X} {a = a} mem bStep sDAC aicDone (ahlDone {d} {ch})
  with decProd-done-inv linkAC hi b1 (SN.NodeStateA.prod-AC na) sDAC
nodeA-AC na {X} {a = a} mem bStep sDAC aicDone (ahlDone {d} {ch}) | refl , inj₁ (refl , refl)
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.doneCS linkAC hi} sBAB)
                     (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.doneCS linkAC hi} sBAC)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.doneCS linkAC hi} sBAB) (ahlDone {d = hi} {ch = N2N_ChainSync})))
... | PEA.evR _ sBAC
    with bundle-CS-ev-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.doneCS linkAC hi} sBAC
...   | bcscE csc′ refl aStepAC =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) pp8 (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (CS.doneCS linkAC hi) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na (ahlDone {d = hi} {ch = N2N_ChainSync})))))
...   | bcssE css′ refl aStepAC =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) css′ (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) pp8 (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (CS.doneCS linkAC hi) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na (ahlDone {d = hi} {ch = N2N_ChainSync})))))
-- linkAC `done` (BlockFetch): the BF SERVER fires doneBF, synced with the produce driver's pp8 done-receipt
nodeA-AC na {X} {a = a} mem bStep sDAC aicDone (ahlDone {d} {ch}) | refl , inj₂ (refl , refl)
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.doneBF linkAC hi} sBAB)
                     (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.doneBF linkAC hi} sBAC)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.doneBF linkAC hi} sBAB) (ahlDone {d = hi} {ch = N2N_BlockFetch})))
... | PEA.evR _ sBAC
    with bundle-BF-ev-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.doneBF linkAC hi} sBAC
...   | bcbcE bfc′ refl aStepAC =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) bfc′ (SN.NodeStateA.bfS-AC na) pp9 (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (BF.doneBF linkAC hi) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na (ahlDone {d = hi} {ch = N2N_BlockFetch})))))
...   | bcbsE bfs′ refl aStepAC =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) bfs′ pp9 (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (BF.doneBF linkAC hi) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na (ahlDone {d = hi} {ch = N2N_BlockFetch})))))

-- node-A api inversion: reflect the driver↔peer sync, peel the driver `⦀`, dispatch
nodeA-ev-api : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a
  → decNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → NodeAEvR na e a A′
nodeA-ev-api na {X} {e} {a} mem step
  with SStep.reflect-node-api
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi b1 (SN.NodeStateA.prod-AC na))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na)) (decProd linkAC hi b1 (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDAB =
        nodeA-AB na mem bStep sDAB
          (decProd-apiCSBF linkAB hi b1 (SN.NodeStateA.prod-AB na) sDAB)
          (decProd-ev-link linkAB hi b1 (SN.NodeStateA.prod-AB na) sDAB)
... | PEA.evR _ sDAC =
        nodeA-AC na mem bStep sDAC
          (decProd-apiCSBF linkAC hi b1 (SN.NodeStateA.prod-AC na) sDAC)
          (decProd-ev-link linkAC hi b1 (SN.NodeStateA.prod-AC na) sDAC)
... | PEA.evBoth _ sDAB sDAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi b1 (SN.NodeStateA.prod-AB na) sDAB)
                     (decProd-ev-link linkAC hi b1 (SN.NodeStateA.prod-AC na) sDAC)))

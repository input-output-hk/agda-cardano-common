{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 D3 (√ ret-transfer) — the terminal (`√`) leaf machinery
-- for `StepOracle.osqrt`/`osqrtB` (`Praos.SysSqrt`).
--
-- A `√` step is `sRet eqf : P ─[ ev (√ x) ]─► deadlock` with `eqf : force P ≡
-- ret x` — it fires iff the WHOLE composite `(decMed ∥⇘ioES⇙ nodesOf) ∖ ioES`
-- forces to `ret`, which (Hide/Par preserve `ret` structurally) happens iff
-- EVERY component forces to `ret`.  Since `decMed` and the drivers are SHARED
-- between the concrete `⟦_⟧`/`rdec` and the abstract `absDec`/`radec`, the √
-- ret-transfer reduces to the 24 PER-PEER facts
--   `force (decXc l d q) ≡ ret ⟺ isFin (coarsenXc q) ≡ true`
--   (i.e. `force (absXc l d q) ≡ ret`).
--
-- THIS MODULE builds:
--   · the GENERIC `ret`-preservation lemmas of `∖` (`fHide-ret{,-inv}`), `Par⊤`
--     (`Par⊤-ret-{intro,inv}`) and the abstract `tableSpec` peers
--     (`tableSpec-force-ret` / `tableSpec-ret-fin`);
--   · the 24 PER-PEER FORWARD transfers `decXc-ret→fin` (concrete peer rets ⇒
--     abstract coarse position is `Fin`) and their assembly into the whole-
--     system FORWARD transfer `sys-ret-transfer` (`force (rdec r) ≡ ret ⇒
--     force (radec r) ≡ ret`), which drives the FORWARD `osqrt`.
--
-- √ ASYMMETRY (the BACKWARD direction is NOT a mirror — documented, not
-- postulated): at a `xSil st` loop-re-entry position the CONCRETE peer forces to
-- `sil (iter step st)` (NOT `ret`) while the ABSTRACT peer coarsens `xSil st ↦
-- coarsenXSt st` and, at `st = stDone`, rets.  So `force (absXc l d (xSil
-- stDone)) ≡ ret` but `force (decXc l d (xSil stDone))` is a `sil`.  Hence the
-- backward `osqrtB` cannot use an immediate `ret`-transfer: the concrete side
-- must first do the loop-back `τ` (a WEAK run), which is a separate assembly
-- (see the report).  The FORWARD `osqrt` is unaffected: a concrete `ret` RULES
-- OUT every `xSil` position (they are `sil`), so all peers sit at their `xHead
-- stDone` / `kcTermE1` `ret` positions, whose coarse image is `Fin`.
--
-- No postulates, holes, or `--allow-unsolved-metas`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to ttU; ⊤ to ⊤U)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Level using () renaming (Level to Lvl)
open import Process_Trees using (PTree; ExtI; NodeKind; ret; sil; react)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysSqrt (blkA : Block₃) where

open PTree using (force)

------------------------------------------------------------------------
-- The shared alphabet, the whole-system process type, and the model.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
-- the whole-system decode + reachable-config foundation (for `sys-ret-transfer`)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; ⟦_⟧; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA using ( decMed )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; toSys; rdec; radec )

-- Net_Api operators (the whole-system alphabet)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; Par⊤; EventSet )

-- the whole-system process type (shared with `⟦_⟧` / `absDec` / the endpoints)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the source protocol FSM modules (state enums)
import CSP.Examples.Cardano_network.ChainSync    p as CS
import CSP.Examples.Cardano_network.BlockFetch   p as BF
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.KeepAlive    p as KA
import CSP.Examples.Cardano_network.LeiosNotify  p as LN
import CSP.Examples.Cardano_network.LeiosFetch   p as LF

-- the abstract peer table interpreter (`tsNode`/`tableSpec`/`isFin`)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs blkA as NS
open NS using ( tableSpec; tsNode )
open NS.Table using ( isFin )

-- the concrete fine positions + concrete renamed peer decodes (SysNode)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( CScPos; CSsPos; BFcPos; BFsPos; TScPos; TSsPos
        ; KAcPos; KAsPos; LNcPos; LNsPos; LFcPos; LFsPos
        ; csHead; csReqNext1; csFindInt1; csDone1; csRF1; csRB1; csIF1; csINF1; csSil
        ; ssHead; ssReqNext1; ssFindInt1; ssDone1; ssRF1; ssRB1; ssAw1; ssIF1; ssINF1; ssSil
        ; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
        ; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil
        ; tcHead; tcReqIdsB1; tcReqIdsNB1; tcReqTxs1; tcRepB1; tcDone1; tcRepNB1; tcRepTxs1; tcSil
        ; tsHead; tsDone1; tsReqB1; tsReqNB1; tsReqTxs1; tsSil
        ; kcHead; kcErr1; kcReq1; kcDone1; kcSil; kcTermE1
        ; ksHead; ksRecv1; ksDdone1; ksSil
        ; lncHead; lncRann1; lncRoff1; lncRtxs1; lncRvot1; lncReq1; lncDone1; lncSil
        ; lnsHead; lnsDone1; lnsWann1; lnsWoff1; lnsWtxs1; lnsWvot1; lnsSil
        ; lfcHead; lfcRblk1; lfcRbtx1; lfcRvot1; lfcRnext1; lfcRlast1
        ; lfcWblk1; lfcWtxs1; lfcWvot1; lfcWrng1; lfcDone1; lfcSil
        ; lfsHead; lfsDone1; lfsWblk1; lfsWtxs1; lfsWvot1; lfsWnext1; lfsWlast1; lfsSil
        ; decCSc; decCSs; decBFc; decBFs; decTSc; decTSs
        ; decKAc; decKAs; decLNc; decLNs; decLFc; decLFs
        ; decCSc-src; decCSs-src; decBFc-src; decBFs-src; decTSc-src; decTSs-src
        ; decKAc-src; decKAs-src; decLNc-src; decLNs-src; decLFc-src; decLFs-src
        -- the 12-peer bundle + InertPos + node decodes/states (constructors)
        ; bundleG; InertPos; mkInert
        ; decNodeA; decNodeB; decNodeC; decNodeD
        ; NodeStateA; NodeStateB; NodeStateC; NodeStateD
        ; mkNodeA; mkNodeB; mkNodeC; mkNodeD )

-- the abstract peer decodes + the coarsen maps (SysStep)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA as MSysStep
open MSysStep
  using ( absCSc; absCSs; absBFc; absBFs; absTSc; absTSs
        ; absKAc; absKAs; absLNc; absLNs; absLFc; absLFs
        ; coarsenCSc; coarsenCSs; coarsenBFc; coarsenBFs; coarsenTSc; coarsenTSs
        ; coarsenKAc; coarsenKAs; coarsenLNc; coarsenLNs; coarsenLFc; coarsenLFs
        ; absBundleG; absNodeA; absNodeB; absNodeC; absNodeD
        ; nodesOf; absNodesOf; absDec )

-- the abstract-peer `isFin` predicates (NodeSpecs)
open NS using ( csCfin; csSfin; bfCfin; bfSfin; tsCfin; tsSfin
              ; kaCfin; kaSfin; lnCfin; lnSfin; lfCfin; lfSfin )

-- the six per-protocol alphabet injections (for the `renameMap`-ret inverse)
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( ιCS; ιCS⁻¹; ιCS-linv; ιBF; ιBF⁻¹; ιBF-linv
        ; ιTS; ιTS⁻¹; ιTS-linv; ιKA; ιKA⁻¹; ιKA-linv
        ; ιLN; ιLN⁻¹; ιLN-linv; ιLF; ιLF⁻¹; ιLF-linv )
import CSP.Rename {E₁ = CS.CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RenCS
import CSP.Rename {E₁ = BF.BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF
import CSP.Rename {E₁ = TS.TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RenTS
import CSP.Rename {E₁ = KA.KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA
import CSP.Rename {E₁ = LN.LNEv} {E₂ = Net_Api Payload} ιLN ιLN⁻¹ ιLN-linv as RenLN
import CSP.Rename {E₁ = LF.LFEv} {E₂ = Net_Api Payload} ιLF ιLF⁻¹ ιLF-linv as RenLF

-- the SOURCE-force `react` leaf lemmas (unstick the offer-map DecEq guard) +
-- the per-peer `renameMap`-react transport (`RenTC` instances)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA
  using ( module CSNO; module BFNO; module TSNO; module KANO; module LNNO; module LFNO
        ; fReqNext1; fFindInt1; fDone1; fRF1; fRB1; fIF1; fINF1  -- ChainSync client / server leaves
        ; gReqNext1; gFindInt1; gDone1; gRF1; gRB1; gAw1; gIF1; gINF1
        -- BlockFetch client / server leaves
        ; hReq1; hcDone1; hBlk1
        ; kReq1; ksDone1; kStart1; kNoBlk1; kBlk1; kBatchDone1
        -- TxSubmission client / server leaves
        ; htcReqIdsB1; htcReqIdsNB1; htcReqTxs1; htcRepB1; htcDone1; htcRepNB1; htcRepTxs1
        ; htsDone1; htsReqB1; htsReqNB1; htsReqTxs1
        -- KeepAlive client / server leaves
        ; hkcReq1; hkcDone1; hksRecv1; hksDdone1
        -- LeiosNotify client / server leaves
        ; hlncRann1; hlncRoff1; hlncRtxs1; hlncRvot1; hlncReq1; hlncDone1
        ; hlnsDone1; hlnsWann1; hlnsWoff1; hlnsWtxs1; hlnsWvot1
        -- LeiosFetch client / server leaves
        ; hlfcRblk1; hlfcRbtx1; hlfcRvot1; hlfcRnext1; hlfcRlast1
        ; hlfcWblk1; hlfcWtxs1; hlfcWvot1; hlfcWrng1; hlfcDone1
        ; hlfsDone1; hlfsWblk1; hlfsWtxs1; hlfsWvot1; hlfsWnext1; hlfsWlast1 )

------------------------------------------------------------------------
-- `ret ≢ react`: a terminal node is not a branching node.
------------------------------------------------------------------------
ret≢react : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {x : R} {V T} → ret {E = E} {I = I} x ≡ react V T → ⊥
ret≢react ()

------------------------------------------------------------------------
-- Leaf refutation (per protocol): a source peer whose force is `react` cannot,
-- through the rename, force to `ret`.  The SOURCE `react` leaf lemma
-- characterises the STUCK source force (its `l ≟ l` guard is unstuck by
-- `≟-yes-refl`); generalising that stuck force by its characterising equation
-- lets `force (renameMap P)` reduce to a `react`, contradicting the `ret`.
renCS-react-not-ret : {Rr : Set} {P : PTree CS.CSEv (ExtI CS.CSEv) Rr}
      {V : _} {T : _} {x : Rr}
    → PTree.force P ≡ react V T → PTree.force (RenCS.renameMap P) ≡ ret x → ⊥
renCS-react-not-ret {P = P} req eq = ret≢react (trans (sym eq) (CSNO.force-renameMap-react {P = P} req))

renBF-react-not-ret : {Rr : Set} {P : PTree BF.BFEv (ExtI BF.BFEv) Rr}
      {V : _} {T : _} {x : Rr}
    → PTree.force P ≡ react V T → PTree.force (RenBF.renameMap P) ≡ ret x → ⊥
renBF-react-not-ret {P = P} req eq = ret≢react (trans (sym eq) (BFNO.force-renameMap-react {P = P} req))

renTS-react-not-ret : {Rr : Set} {P : PTree TS.TSEv (ExtI TS.TSEv) Rr}
      {V : _} {T : _} {x : Rr}
    → PTree.force P ≡ react V T → PTree.force (RenTS.renameMap P) ≡ ret x → ⊥
renTS-react-not-ret {P = P} req eq = ret≢react (trans (sym eq) (TSNO.force-renameMap-react {P = P} req))

renKA-react-not-ret : {Rr : Set} {P : PTree KA.KAEv (ExtI KA.KAEv) Rr}
      {V : _} {T : _} {x : Rr}
    → PTree.force P ≡ react V T → PTree.force (RenKA.renameMap P) ≡ ret x → ⊥
renKA-react-not-ret {P = P} req eq = ret≢react (trans (sym eq) (KANO.force-renameMap-react {P = P} req))

renLN-react-not-ret : {Rr : Set} {P : PTree LN.LNEv (ExtI LN.LNEv) Rr}
      {V : _} {T : _} {x : Rr}
    → PTree.force P ≡ react V T → PTree.force (RenLN.renameMap P) ≡ ret x → ⊥
renLN-react-not-ret {P = P} req eq = ret≢react (trans (sym eq) (LNNO.force-renameMap-react {P = P} req))

renLF-react-not-ret : {Rr : Set} {P : PTree LF.LFEv (ExtI LF.LFEv) Rr}
      {V : _} {T : _} {x : Rr}
    → PTree.force P ≡ react V T → PTree.force (RenLF.renameMap P) ≡ ret x → ⊥
renLF-react-not-ret {P = P} req eq = ret≢react (trans (sym eq) (LFNO.force-renameMap-react {P = P} req))

------------------------------------------------------------------------
-- GENERIC `ret`-preservation lemmas.
------------------------------------------------------------------------

-- `∖` preserves `ret` FORWARD: a hidden `ret` passes through unchanged.
fHide-ret : {P : NetProc} {A : EventSet} {x : ⊤ {0ℓ}}
          → force P ≡ ret x → force (P ∖ A) ≡ ret x
fHide-ret {P = P} eq with force P | eq
... | ret r | refl = refl

-- `∖` preserves `ret` BACKWARD: `(P ∖ A)` rets only when `P` rets.
fHide-ret-inv : {P : NetProc} {A : EventSet} {x : ⊤ {0ℓ}}
              → force (P ∖ A) ≡ ret x → force P ≡ ret x
fHide-ret-inv {P = P} eq with force P | eq
... | ret r | refl = refl

-- `Par⊤` preserves `ret` FORWARD: if both operands ret, the composite rets
-- (`merge = λ _ _ → tt`, so the joint value is `tt`).
Par⊤-ret-intro : (A : EventSet) {P Q : NetProc}
               → force P ≡ ret tt → force Q ≡ ret tt
               → force (Par⊤ A P Q) ≡ ret tt
Par⊤-ret-intro A {P} {Q} eqP eqQ with force P | force Q | eqP | eqQ
... | ret r₁ | ret r₂ | refl | refl = refl

-- `Par⊤` preserves `ret` BACKWARD: the composite rets only when both operands do.
Par⊤-ret-inv : (A : EventSet) {P Q : NetProc} {x : ⊤ {0ℓ}}
             → force (Par⊤ A P Q) ≡ ret x
             → (force P ≡ ret tt) × (force Q ≡ ret tt)
Par⊤-ret-inv A {P} {Q} eq with force P | force Q | eq
... | ret r₁    | ret r₂    | refl = refl , refl
... | ret _     | sil _     | ()
... | ret _     | react _ _ | ()
... | sil _     | ret _     | ()
... | sil _     | sil _     | ()
... | sil _     | react _ _ | ()
... | react _ _ | ret _     | ()
... | react _ _ | sil _     | ()
... | react _ _ | react _ _ | ()

-- `⦀` is `Par⊤ ∅ES`, so its `ret`-preservation is the `Par⊤` one at `∅ES`.
⦀-ret-intro : {P Q : NetProc}
            → force P ≡ ret tt → force Q ≡ ret tt → force (P ⦀ Q) ≡ ret tt
⦀-ret-intro = Par⊤-ret-intro Op.∅ES

⦀-ret-inv : {P Q : NetProc} {x : ⊤ {0ℓ}}
          → force (P ⦀ Q) ≡ ret x → (force P ≡ ret tt) × (force Q ≡ ret tt)
⦀-ret-inv = Par⊤-ret-inv Op.∅ES

-- `∥⇘ A ⇙` is `Par⊤ A`.
∥⇙-ret-intro : {A : EventSet} {P Q : NetProc}
             → force P ≡ ret tt → force Q ≡ ret tt → force (P ∥⇘ A ⇙ Q) ≡ ret tt
∥⇙-ret-intro {A = A} = Par⊤-ret-intro A

∥⇙-ret-inv : {A : EventSet} {P Q : NetProc} {x : ⊤ {0ℓ}}
           → force (P ∥⇘ A ⇙ Q) ≡ ret x → (force P ≡ ret tt) × (force Q ≡ ret tt)
∥⇙-ret-inv {A = A} = Par⊤-ret-inv A

-- an abstract `tableSpec` peer rets iff the position is `Fin`: `force (tableSpec
-- T q) = tsNode T q (isFin T q)`, and `tsNode _ _ true = ret tt`.
tableSpec-force-ret : {Pos : Set} (T : NS.Table Pos) (q : Pos)
                    → isFin T q ≡ true → force (tableSpec T q) ≡ ret tt
tableSpec-force-ret T q eq with isFin T q | eq
... | true | refl = refl

tableSpec-ret-fin : {Pos : Set} (T : NS.Table Pos) (q : Pos) {x : ⊤ {0ℓ}}
                  → force (tableSpec T q) ≡ ret x → isFin T q ≡ true
tableSpec-ret-fin T q eq with isFin T q | eq
... | true | refl = refl

------------------------------------------------------------------------
-- Per-peer FORWARD transfer (ChainSync client) — PROTOTYPE.
--
-- `force (decCSc l d q) ≡ ret` ⇒ `csCfin (coarsenCSc q) ≡ true`.  Only `csHead
-- stDone` forces to `ret` (every other position forces to `react`/`sil`, so the
-- hypothesis is absurd); its coarse image is `ccTerm`, the unique `Fin`.
decCSc-ret→fin : (l : Link) (d : Dir) (q : CScPos) {x : ⊤ {0ℓ}}
               → force (decCSc l d q) ≡ ret x → csCfin (coarsenCSc q) ≡ true
decCSc-ret→fin l d (csHead CS.stDone)      eq = refl
decCSc-ret→fin l d (csHead CS.stIdle)      ()
decCSc-ret→fin l d (csHead CS.stCanAwait)  ()
decCSc-ret→fin l d (csHead CS.stMustReply) ()
decCSc-ret→fin l d (csHead CS.stIntersect) ()
decCSc-ret→fin l d csReqNext1      eq = ⊥-elim (renCS-react-not-ret {P = decCSc-src l d csReqNext1}      (fReqNext1 l d) eq)
decCSc-ret→fin l d (csFindInt1 ps) eq = ⊥-elim (renCS-react-not-ret {P = decCSc-src l d (csFindInt1 ps)} (fFindInt1 l d ps) eq)
decCSc-ret→fin l d csDone1         eq = ⊥-elim (renCS-react-not-ret {P = decCSc-src l d csDone1}         (fDone1 l d) eq)
decCSc-ret→fin l d (csRF1 h t)     eq = ⊥-elim (renCS-react-not-ret {P = decCSc-src l d (csRF1 h t)}     (fRF1 l d h t) eq)
decCSc-ret→fin l d (csRB1 pt t)    eq = ⊥-elim (renCS-react-not-ret {P = decCSc-src l d (csRB1 pt t)}    (fRB1 l d pt t) eq)
decCSc-ret→fin l d (csIF1 pt t)    eq = ⊥-elim (renCS-react-not-ret {P = decCSc-src l d (csIF1 pt t)}    (fIF1 l d pt t) eq)
decCSc-ret→fin l d (csINF1 t)      eq = ⊥-elim (renCS-react-not-ret {P = decCSc-src l d (csINF1 t)}      (fINF1 l d t) eq)
decCSc-ret→fin l d (csSil st)              ()

-- ChainSync server
decCSs-ret→fin : (l : Link) (d : Dir) (q : CSsPos) {x : ⊤ {0ℓ}}
               → force (decCSs l d q) ≡ ret x → csSfin (coarsenCSs q) ≡ true
decCSs-ret→fin l d (ssHead CS.stDone)      eq = refl
decCSs-ret→fin l d (ssHead CS.stIdle)      ()
decCSs-ret→fin l d (ssHead CS.stCanAwait)  ()
decCSs-ret→fin l d (ssHead CS.stMustReply) ()
decCSs-ret→fin l d (ssHead CS.stIntersect) ()
decCSs-ret→fin l d ssReqNext1      eq = ⊥-elim (renCS-react-not-ret {P = decCSs-src l d ssReqNext1}      (gReqNext1 l d) eq)
decCSs-ret→fin l d (ssFindInt1 ps) eq = ⊥-elim (renCS-react-not-ret {P = decCSs-src l d (ssFindInt1 ps)} (gFindInt1 l d ps) eq)
decCSs-ret→fin l d ssDone1         eq = ⊥-elim (renCS-react-not-ret {P = decCSs-src l d ssDone1}         (gDone1 l d) eq)
decCSs-ret→fin l d (ssRF1 h t)     eq = ⊥-elim (renCS-react-not-ret {P = decCSs-src l d (ssRF1 h t)}     (gRF1 l d h t) eq)
decCSs-ret→fin l d (ssRB1 pt t)    eq = ⊥-elim (renCS-react-not-ret {P = decCSs-src l d (ssRB1 pt t)}    (gRB1 l d pt t) eq)
decCSs-ret→fin l d ssAw1           eq = ⊥-elim (renCS-react-not-ret {P = decCSs-src l d ssAw1}           (gAw1 l d) eq)
decCSs-ret→fin l d (ssIF1 pt t)    eq = ⊥-elim (renCS-react-not-ret {P = decCSs-src l d (ssIF1 pt t)}    (gIF1 l d pt t) eq)
decCSs-ret→fin l d (ssINF1 t)      eq = ⊥-elim (renCS-react-not-ret {P = decCSs-src l d (ssINF1 t)}      (gINF1 l d t) eq)
decCSs-ret→fin l d (ssSil st)              ()

-- BlockFetch client
decBFc-ret→fin : (l : Link) (d : Dir) (q : BFcPos) {x : ⊤ {0ℓ}}
               → force (decBFc l d q) ≡ ret x → bfCfin (coarsenBFc q) ≡ true
decBFc-ret→fin l d (bcHead BF.stDone)      eq = refl
decBFc-ret→fin l d (bcHead BF.stIdle)      ()
decBFc-ret→fin l d (bcHead BF.stBusy)      ()
decBFc-ret→fin l d (bcHead BF.stStreaming) ()
decBFc-ret→fin l d (bcReq1 r) eq = ⊥-elim (renBF-react-not-ret {P = decBFc-src l d (bcReq1 r)} (hReq1 l d r) eq)
decBFc-ret→fin l d bcDone1    eq = ⊥-elim (renBF-react-not-ret {P = decBFc-src l d bcDone1}    (hcDone1 l d) eq)
decBFc-ret→fin l d (bcBlk1 b) eq = ⊥-elim (renBF-react-not-ret {P = decBFc-src l d (bcBlk1 b)} (hBlk1 l d b) eq)
decBFc-ret→fin l d (bcSil st)              ()

-- BlockFetch server
decBFs-ret→fin : (l : Link) (d : Dir) (q : BFsPos) {x : ⊤ {0ℓ}}
               → force (decBFs l d q) ≡ ret x → bfSfin (coarsenBFs q) ≡ true
decBFs-ret→fin l d (bsHead BF.stDone)      eq = refl
decBFs-ret→fin l d (bsHead BF.stIdle)      ()
decBFs-ret→fin l d (bsHead BF.stBusy)      ()
decBFs-ret→fin l d (bsHead BF.stStreaming) ()
decBFs-ret→fin l d (bsReq1 r)    eq = ⊥-elim (renBF-react-not-ret {P = decBFs-src l d (bsReq1 r)}    (kReq1 l d r) eq)
decBFs-ret→fin l d bsDone1       eq = ⊥-elim (renBF-react-not-ret {P = decBFs-src l d bsDone1}       (ksDone1 l d) eq)
decBFs-ret→fin l d bsStart1      eq = ⊥-elim (renBF-react-not-ret {P = decBFs-src l d bsStart1}      (kStart1 l d) eq)
decBFs-ret→fin l d bsNoBlk1      eq = ⊥-elim (renBF-react-not-ret {P = decBFs-src l d bsNoBlk1}      (kNoBlk1 l d) eq)
decBFs-ret→fin l d (bsBlk1 b)    eq = ⊥-elim (renBF-react-not-ret {P = decBFs-src l d (bsBlk1 b)}    (kBlk1 l d b) eq)
decBFs-ret→fin l d bsBatchDone1  eq = ⊥-elim (renBF-react-not-ret {P = decBFs-src l d bsBatchDone1}  (kBatchDone1 l d) eq)
decBFs-ret→fin l d (bsSil st)              ()

-- TxSubmission client
decTSc-ret→fin : (l : Link) (d : Dir) (q : TScPos) {x : ⊤ {0ℓ}}
               → force (decTSc l d q) ≡ ret x → tsCfin (coarsenTSc q) ≡ true
decTSc-ret→fin l d (tcHead TS.stDone)             eq = refl
decTSc-ret→fin l d (tcHead TS.stInit)             ()
decTSc-ret→fin l d (tcHead TS.stIdle)             ()
decTSc-ret→fin l d (tcHead TS.stTxIdsBlocking)    ()
decTSc-ret→fin l d (tcHead TS.stTxIdsNonBlocking) ()
decTSc-ret→fin l d (tcHead TS.stTxs)              ()
decTSc-ret→fin l d (tcReqIdsB1 a r)  eq = ⊥-elim (renTS-react-not-ret {P = decTSc-src l d (tcReqIdsB1 a r)}  (htcReqIdsB1 l d a r) eq)
decTSc-ret→fin l d (tcReqIdsNB1 a r) eq = ⊥-elim (renTS-react-not-ret {P = decTSc-src l d (tcReqIdsNB1 a r)} (htcReqIdsNB1 l d a r) eq)
decTSc-ret→fin l d (tcReqTxs1 ids)   eq = ⊥-elim (renTS-react-not-ret {P = decTSc-src l d (tcReqTxs1 ids)}   (htcReqTxs1 l d ids) eq)
decTSc-ret→fin l d (tcRepB1 ids)     eq = ⊥-elim (renTS-react-not-ret {P = decTSc-src l d (tcRepB1 ids)}     (htcRepB1 l d ids) eq)
decTSc-ret→fin l d tcDone1           eq = ⊥-elim (renTS-react-not-ret {P = decTSc-src l d tcDone1}           (htcDone1 l d) eq)
decTSc-ret→fin l d (tcRepNB1 ids)    eq = ⊥-elim (renTS-react-not-ret {P = decTSc-src l d (tcRepNB1 ids)}    (htcRepNB1 l d ids) eq)
decTSc-ret→fin l d (tcRepTxs1 txs)   eq = ⊥-elim (renTS-react-not-ret {P = decTSc-src l d (tcRepTxs1 txs)}   (htcRepTxs1 l d txs) eq)
decTSc-ret→fin l d (tcSil st)              ()

-- TxSubmission server
decTSs-ret→fin : (l : Link) (d : Dir) (q : TSsPos) {x : ⊤ {0ℓ}}
               → force (decTSs l d q) ≡ ret x → tsSfin (coarsenTSs q) ≡ true
decTSs-ret→fin l d (tsHead TS.stDone)             eq = refl
decTSs-ret→fin l d (tsHead TS.stInit)             ()
decTSs-ret→fin l d (tsHead TS.stIdle)             ()
decTSs-ret→fin l d (tsHead TS.stTxIdsBlocking)    ()
decTSs-ret→fin l d (tsHead TS.stTxIdsNonBlocking) ()
decTSs-ret→fin l d (tsHead TS.stTxs)              ()
decTSs-ret→fin l d tsDone1        eq = ⊥-elim (renTS-react-not-ret {P = decTSs-src l d tsDone1}        (htsDone1 l d) eq)
decTSs-ret→fin l d (tsReqB1 ar)   eq = ⊥-elim (renTS-react-not-ret {P = decTSs-src l d (tsReqB1 ar)}   (htsReqB1 l d ar) eq)
decTSs-ret→fin l d (tsReqNB1 ar)  eq = ⊥-elim (renTS-react-not-ret {P = decTSs-src l d (tsReqNB1 ar)}  (htsReqNB1 l d ar) eq)
decTSs-ret→fin l d (tsReqTxs1 ids) eq = ⊥-elim (renTS-react-not-ret {P = decTSs-src l d (tsReqTxs1 ids)} (htsReqTxs1 l d ids) eq)
decTSs-ret→fin l d (tsSil st)              ()

-- KeepAlive client (special: kcErr1 forces to react via Output; kcTermE1 rets)
decKAc-ret→fin : (l : Link) (d : Dir) (q : KAcPos) {x : ⊤ {0ℓ}}
               → force (decKAc l d q) ≡ ret x → kaCfin (coarsenKAc q) ≡ true
decKAc-ret→fin l d (kcHead KA.stDone)       eq = refl
decKAc-ret→fin l d (kcHead KA.stClient)     ()
decKAc-ret→fin l d (kcHead (KA.stServer c)) ()
decKAc-ret→fin l d (kcErr1 cq cr ne)        ()
decKAc-ret→fin l d (kcReq1 c) eq = ⊥-elim (renKA-react-not-ret {P = decKAc-src l d (kcReq1 c)} (hkcReq1 l d c) eq)
decKAc-ret→fin l d kcDone1    eq = ⊥-elim (renKA-react-not-ret {P = decKAc-src l d kcDone1}    (hkcDone1 l d) eq)
decKAc-ret→fin l d (kcSil st)               ()
decKAc-ret→fin l d kcTermE1                 eq = refl

-- KeepAlive server
decKAs-ret→fin : (l : Link) (d : Dir) (q : KAsPos) {x : ⊤ {0ℓ}}
               → force (decKAs l d q) ≡ ret x → kaSfin (coarsenKAs q) ≡ true
decKAs-ret→fin l d (ksHead KA.stDone)       eq = refl
decKAs-ret→fin l d (ksHead KA.stClient)     ()
decKAs-ret→fin l d (ksHead (KA.stServer c)) ()
decKAs-ret→fin l d (ksRecv1 c) eq = ⊥-elim (renKA-react-not-ret {P = decKAs-src l d (ksRecv1 c)} (hksRecv1 l d c) eq)
decKAs-ret→fin l d ksDdone1    eq = ⊥-elim (renKA-react-not-ret {P = decKAs-src l d ksDdone1}    (hksDdone1 l d) eq)
decKAs-ret→fin l d (ksSil st)              ()

-- LeiosNotify client
decLNc-ret→fin : (l : Link) (d : Dir) (q : LNcPos) {x : ⊤ {0ℓ}}
               → force (decLNc l d q) ≡ ret x → lnCfin (coarsenLNc q) ≡ true
decLNc-ret→fin l d (lncHead LN.stDone) eq = refl
decLNc-ret→fin l d (lncHead LN.stIdle) ()
decLNc-ret→fin l d (lncHead LN.stBusy) ()
decLNc-ret→fin l d (lncRann1 h)  eq = ⊥-elim (renLN-react-not-ret {P = decLNc-src l d (lncRann1 h)}  (hlncRann1 l d h) eq)
decLNc-ret→fin l d (lncRoff1 q)  eq = ⊥-elim (renLN-react-not-ret {P = decLNc-src l d (lncRoff1 q)}  (hlncRoff1 l d q) eq)
decLNc-ret→fin l d (lncRtxs1 q)  eq = ⊥-elim (renLN-react-not-ret {P = decLNc-src l d (lncRtxs1 q)}  (hlncRtxs1 l d q) eq)
decLNc-ret→fin l d (lncRvot1 vs) eq = ⊥-elim (renLN-react-not-ret {P = decLNc-src l d (lncRvot1 vs)} (hlncRvot1 l d vs) eq)
decLNc-ret→fin l d lncReq1       eq = ⊥-elim (renLN-react-not-ret {P = decLNc-src l d lncReq1}       (hlncReq1 l d) eq)
decLNc-ret→fin l d lncDone1      eq = ⊥-elim (renLN-react-not-ret {P = decLNc-src l d lncDone1}      (hlncDone1 l d) eq)
decLNc-ret→fin l d (lncSil st)              ()

-- LeiosNotify server
decLNs-ret→fin : (l : Link) (d : Dir) (q : LNsPos) {x : ⊤ {0ℓ}}
               → force (decLNs l d q) ≡ ret x → lnSfin (coarsenLNs q) ≡ true
decLNs-ret→fin l d (lnsHead LN.stDone) eq = refl
decLNs-ret→fin l d (lnsHead LN.stIdle) ()
decLNs-ret→fin l d (lnsHead LN.stBusy) ()
decLNs-ret→fin l d lnsDone1      eq = ⊥-elim (renLN-react-not-ret {P = decLNs-src l d lnsDone1}      (hlnsDone1 l d) eq)
decLNs-ret→fin l d (lnsWann1 h)  eq = ⊥-elim (renLN-react-not-ret {P = decLNs-src l d (lnsWann1 h)}  (hlnsWann1 l d h) eq)
decLNs-ret→fin l d (lnsWoff1 q)  eq = ⊥-elim (renLN-react-not-ret {P = decLNs-src l d (lnsWoff1 q)}  (hlnsWoff1 l d q) eq)
decLNs-ret→fin l d (lnsWtxs1 q)  eq = ⊥-elim (renLN-react-not-ret {P = decLNs-src l d (lnsWtxs1 q)}  (hlnsWtxs1 l d q) eq)
decLNs-ret→fin l d (lnsWvot1 vs) eq = ⊥-elim (renLN-react-not-ret {P = decLNs-src l d (lnsWvot1 vs)} (hlnsWvot1 l d vs) eq)
decLNs-ret→fin l d (lnsSil st)              ()

-- LeiosFetch client
decLFc-ret→fin : (l : Link) (d : Dir) (q : LFcPos) {x : ⊤ {0ℓ}}
               → force (decLFc l d q) ≡ ret x → lfCfin (coarsenLFc q) ≡ true
decLFc-ret→fin l d (lfcHead LF.stDone)       eq = refl
decLFc-ret→fin l d (lfcHead LF.stIdle)       ()
decLFc-ret→fin l d (lfcHead LF.stBlock)      ()
decLFc-ret→fin l d (lfcHead LF.stBlockTxs)   ()
decLFc-ret→fin l d (lfcHead LF.stVotes)      ()
decLFc-ret→fin l d (lfcHead LF.stBlockRange) ()
decLFc-ret→fin l d (lfcRblk1 b)    eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcRblk1 b)}    (hlfcRblk1 l d b) eq)
decLFc-ret→fin l d (lfcRbtx1 ts)   eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcRbtx1 ts)}   (hlfcRbtx1 l d ts) eq)
decLFc-ret→fin l d (lfcRvot1 vs)   eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcRvot1 vs)}   (hlfcRvot1 l d vs) eq)
decLFc-ret→fin l d (lfcRnext1 b ts) eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcRnext1 b ts)} (hlfcRnext1 l d b ts) eq)
decLFc-ret→fin l d (lfcRlast1 b ts) eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcRlast1 b ts)} (hlfcRlast1 l d b ts) eq)
decLFc-ret→fin l d (lfcWblk1 pt)   eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcWblk1 pt)}   (hlfcWblk1 l d pt) eq)
decLFc-ret→fin l d (lfcWtxs1 pb)   eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcWtxs1 pb)}   (hlfcWtxs1 l d pb) eq)
decLFc-ret→fin l d (lfcWvot1 vs)   eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcWvot1 vs)}   (hlfcWvot1 l d vs) eq)
decLFc-ret→fin l d (lfcWrng1 r)    eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d (lfcWrng1 r)}    (hlfcWrng1 l d r) eq)
decLFc-ret→fin l d lfcDone1        eq = ⊥-elim (renLF-react-not-ret {P = decLFc-src l d lfcDone1}        (hlfcDone1 l d) eq)
decLFc-ret→fin l d (lfcSil st)              ()

-- LeiosFetch server
decLFs-ret→fin : (l : Link) (d : Dir) (q : LFsPos) {x : ⊤ {0ℓ}}
               → force (decLFs l d q) ≡ ret x → lfSfin (coarsenLFs q) ≡ true
decLFs-ret→fin l d (lfsHead LF.stDone)       eq = refl
decLFs-ret→fin l d (lfsHead LF.stIdle)       ()
decLFs-ret→fin l d (lfsHead LF.stBlock)      ()
decLFs-ret→fin l d (lfsHead LF.stBlockTxs)   ()
decLFs-ret→fin l d (lfsHead LF.stVotes)      ()
decLFs-ret→fin l d (lfsHead LF.stBlockRange) ()
decLFs-ret→fin l d lfsDone1       eq = ⊥-elim (renLF-react-not-ret {P = decLFs-src l d lfsDone1}       (hlfsDone1 l d) eq)
decLFs-ret→fin l d (lfsWblk1 b)   eq = ⊥-elim (renLF-react-not-ret {P = decLFs-src l d (lfsWblk1 b)}   (hlfsWblk1 l d b) eq)
decLFs-ret→fin l d (lfsWtxs1 ts)  eq = ⊥-elim (renLF-react-not-ret {P = decLFs-src l d (lfsWtxs1 ts)}  (hlfsWtxs1 l d ts) eq)
decLFs-ret→fin l d (lfsWvot1 vs)  eq = ⊥-elim (renLF-react-not-ret {P = decLFs-src l d (lfsWvot1 vs)}  (hlfsWvot1 l d vs) eq)
decLFs-ret→fin l d (lfsWnext1 bt) eq = ⊥-elim (renLF-react-not-ret {P = decLFs-src l d (lfsWnext1 bt)} (hlfsWnext1 l d bt) eq)
decLFs-ret→fin l d (lfsWlast1 bt) eq = ⊥-elim (renLF-react-not-ret {P = decLFs-src l d (lfsWlast1 bt)} (hlfsWlast1 l d bt) eq)
decLFs-ret→fin l d (lfsSil st)              ()

------------------------------------------------------------------------
-- Per-peer FORWARD ret-transfer: concrete peer rets ⇒ abstract peer rets
-- (`decXc-ret→fin` gives `isFin (coarsen q) ≡ true`; `tableSpec-force-ret`
-- turns that into `force (absXc l d q) ≡ ret tt`).
------------------------------------------------------------------------
decCSc-ret-transfer : (l : Link) (d : Dir) (q : CScPos) {x : ⊤ {0ℓ}}
  → force (decCSc l d q) ≡ ret x → force (absCSc l d q) ≡ ret tt
decCSc-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenCSc q) (decCSc-ret→fin l d q eq)

decCSs-ret-transfer : (l : Link) (d : Dir) (q : CSsPos) {x : ⊤ {0ℓ}}
  → force (decCSs l d q) ≡ ret x → force (absCSs l d q) ≡ ret tt
decCSs-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenCSs q) (decCSs-ret→fin l d q eq)

decBFc-ret-transfer : (l : Link) (d : Dir) (q : BFcPos) {x : ⊤ {0ℓ}}
  → force (decBFc l d q) ≡ ret x → force (absBFc l d q) ≡ ret tt
decBFc-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenBFc q) (decBFc-ret→fin l d q eq)

decBFs-ret-transfer : (l : Link) (d : Dir) (q : BFsPos) {x : ⊤ {0ℓ}}
  → force (decBFs l d q) ≡ ret x → force (absBFs l d q) ≡ ret tt
decBFs-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenBFs q) (decBFs-ret→fin l d q eq)

decTSc-ret-transfer : (l : Link) (d : Dir) (q : TScPos) {x : ⊤ {0ℓ}}
  → force (decTSc l d q) ≡ ret x → force (absTSc l d q) ≡ ret tt
decTSc-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenTSc q) (decTSc-ret→fin l d q eq)

decTSs-ret-transfer : (l : Link) (d : Dir) (q : TSsPos) {x : ⊤ {0ℓ}}
  → force (decTSs l d q) ≡ ret x → force (absTSs l d q) ≡ ret tt
decTSs-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenTSs q) (decTSs-ret→fin l d q eq)

decKAc-ret-transfer : (l : Link) (d : Dir) (q : KAcPos) {x : ⊤ {0ℓ}}
  → force (decKAc l d q) ≡ ret x → force (absKAc l d q) ≡ ret tt
decKAc-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenKAc q) (decKAc-ret→fin l d q eq)

decKAs-ret-transfer : (l : Link) (d : Dir) (q : KAsPos) {x : ⊤ {0ℓ}}
  → force (decKAs l d q) ≡ ret x → force (absKAs l d q) ≡ ret tt
decKAs-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenKAs q) (decKAs-ret→fin l d q eq)

decLNc-ret-transfer : (l : Link) (d : Dir) (q : LNcPos) {x : ⊤ {0ℓ}}
  → force (decLNc l d q) ≡ ret x → force (absLNc l d q) ≡ ret tt
decLNc-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenLNc q) (decLNc-ret→fin l d q eq)

decLNs-ret-transfer : (l : Link) (d : Dir) (q : LNsPos) {x : ⊤ {0ℓ}}
  → force (decLNs l d q) ≡ ret x → force (absLNs l d q) ≡ ret tt
decLNs-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenLNs q) (decLNs-ret→fin l d q eq)

decLFc-ret-transfer : (l : Link) (d : Dir) (q : LFcPos) {x : ⊤ {0ℓ}}
  → force (decLFc l d q) ≡ ret x → force (absLFc l d q) ≡ ret tt
decLFc-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenLFc q) (decLFc-ret→fin l d q eq)

decLFs-ret-transfer : (l : Link) (d : Dir) (q : LFsPos) {x : ⊤ {0ℓ}}
  → force (decLFs l d q) ≡ ret x → force (absLFs l d q) ≡ ret tt
decLFs-ret-transfer l d q eq = tableSpec-force-ret _ (coarsenLFs q) (decLFs-ret→fin l d q eq)

------------------------------------------------------------------------
-- Bundle FORWARD ret-transfer: a concrete 12-peer bundle rets ⇒ its abstract
-- counterpart rets (peel the 12 `⦀` with `⦀-ret-inv`, transfer each peer, and
-- rebuild the abstract bundle with `⦀-ret-intro`).
------------------------------------------------------------------------
bundleG-ret-transfer : (l : Link) (cl sv : Dir)
      (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos) {x : ⊤ {0ℓ}}
    → force (bundleG l cl sv csc css bfc bfs ip) ≡ ret x
    → force (absBundleG l cl sv csc css bfc bfs ip) ≡ ret tt
bundleG-ret-transfer l cl sv csc css bfc bfs (mkInert tsc' tss' kac' kas' lnc' lns' lfc' lfs') eq =
  let kacR , r1  = ⦀-ret-inv eq
      kasR , r2  = ⦀-ret-inv r1
      cscR , r3  = ⦀-ret-inv r2
      cssR , r4  = ⦀-ret-inv r3
      bfcR , r5  = ⦀-ret-inv r4
      bfsR , r6  = ⦀-ret-inv r5
      tscR , r7  = ⦀-ret-inv r6
      tssR , r8  = ⦀-ret-inv r7
      lncR , r9  = ⦀-ret-inv r8
      lnsR , r10 = ⦀-ret-inv r9
      lfcR , lfsR = ⦀-ret-inv r10
  in ⦀-ret-intro (decKAc-ret-transfer l cl kac' kacR)
       (⦀-ret-intro (decKAs-ret-transfer l sv kas' kasR)
         (⦀-ret-intro (decCSc-ret-transfer l cl csc cscR)
           (⦀-ret-intro (decCSs-ret-transfer l sv css cssR)
             (⦀-ret-intro (decBFc-ret-transfer l cl bfc bfcR)
               (⦀-ret-intro (decBFs-ret-transfer l sv bfs bfsR)
                 (⦀-ret-intro (decTSc-ret-transfer l cl tsc' tscR)
                   (⦀-ret-intro (decTSs-ret-transfer l sv tss' tssR)
                     (⦀-ret-intro (decLNc-ret-transfer l cl lnc' lncR)
                       (⦀-ret-intro (decLNs-ret-transfer l sv lns' lnsR)
                         (⦀-ret-intro (decLFc-ret-transfer l cl lfc' lfcR)
                                      (decLFs-ret-transfer l sv lfs' lfsR)))))))))))

------------------------------------------------------------------------
-- Per-node FORWARD ret-transfer: a concrete node rets ⇒ its abstract node rets.
-- Each node is `(bundle ⦀ bundle) ∥⇘ apiES ⇙ driver`; the drivers are SHARED
-- (identical concrete/abstract), so the driver-ret witness passes straight
-- through; the two bundles transfer via `bundleG-ret-transfer`.
------------------------------------------------------------------------
decNodeA-ret-transfer : (s : NodeStateA) {x : ⊤ {0ℓ}}
  → force (decNodeA s) ≡ ret x → force (absNodeA s) ≡ ret tt
decNodeA-ret-transfer (mkNodeA cscab cssab bfcab bfsab ppab cscac cssac bfcac bfsac ppac ipab ipac) eq =
  let bnds , drv = ∥⇙-ret-inv eq
      b1r , b2r  = ⦀-ret-inv bnds
  in ∥⇙-ret-intro (⦀-ret-intro (bundleG-ret-transfer linkAB lo hi cscab cssab bfcab bfsab ipab b1r)
                                (bundleG-ret-transfer linkAC lo hi cscac cssac bfcac bfsac ipac b2r))
                  drv

decNodeB-ret-transfer : (s : NodeStateB) {x : ⊤ {0ℓ}}
  → force (decNodeB s) ≡ ret x → force (absNodeB s) ≡ ret tt
decNodeB-ret-transfer (mkNodeB cscab cssab bfcab bfsab cscbd cssbd bfcbd bfsbd cpb ipab ipbd) eq =
  let bnds , drv = ∥⇙-ret-inv eq
      b1r , b2r  = ⦀-ret-inv bnds
  in ∥⇙-ret-intro (⦀-ret-intro (bundleG-ret-transfer linkAB hi lo cscab cssab bfcab bfsab ipab b1r)
                                (bundleG-ret-transfer linkBD lo hi cscbd cssbd bfcbd bfsbd ipbd b2r))
                  drv

decNodeC-ret-transfer : (s : NodeStateC) {x : ⊤ {0ℓ}}
  → force (decNodeC s) ≡ ret x → force (absNodeC s) ≡ ret tt
decNodeC-ret-transfer (mkNodeC cscac cssac bfcac bfsac csccd csscd bfccd bfscd cpc ipac ipcd) eq =
  let bnds , drv = ∥⇙-ret-inv eq
      b1r , b2r  = ⦀-ret-inv bnds
  in ∥⇙-ret-intro (⦀-ret-intro (bundleG-ret-transfer linkAC hi lo cscac cssac bfcac bfsac ipac b1r)
                                (bundleG-ret-transfer linkCD lo hi csccd csscd bfccd bfscd ipcd b2r))
                  drv

decNodeD-ret-transfer : (s : NodeStateD) {x : ⊤ {0ℓ}}
  → force (decNodeD s) ≡ ret x → force (absNodeD s) ≡ ret tt
decNodeD-ret-transfer (mkNodeD cscbd cssbd bfcbd bfsbd consbd csccd csscd bfccd bfscd conscd ipbd ipcd) eq =
  let bnds , drv = ∥⇙-ret-inv eq
      b1r , b2r  = ⦀-ret-inv bnds
  in ∥⇙-ret-intro (⦀-ret-intro (bundleG-ret-transfer linkBD hi lo cscbd cssbd bfcbd bfsbd ipbd b1r)
                                (bundleG-ret-transfer linkCD hi lo csccd csscd bfccd bfscd ipcd b2r))
                  drv

------------------------------------------------------------------------
-- Whole-nodes FORWARD ret-transfer (peel the 4-node `⦀`).
------------------------------------------------------------------------
nodes-ret-transfer : (s : SysState) {x : ⊤ {0ℓ}}
  → force (nodesOf s) ≡ ret x → force (absNodesOf s) ≡ ret tt
nodes-ret-transfer s eq =
  let aR , r1 = ⦀-ret-inv eq
      bR , r2 = ⦀-ret-inv r1
      cR , dR = ⦀-ret-inv r2
  in ⦀-ret-intro (decNodeA-ret-transfer (nA s) aR)
       (⦀-ret-intro (decNodeB-ret-transfer (nB s) bR)
         (⦀-ret-intro (decNodeC-ret-transfer (nC s) cR)
                      (decNodeD-ret-transfer (nD s) dR)))

------------------------------------------------------------------------
-- Whole-system FORWARD ret-transfer (the FORWARD √ leaf): `force (rdec r) ≡
-- ret ⇒ force (radec r) ≡ ret`.  `rdec`/`radec` share `decMed`; only the nodes
-- differ, bridged by `nodes-ret-transfer`.
------------------------------------------------------------------------
sys-ret-transfer : (r : RState) {x : ⊤ {0ℓ}}
  → force (rdec r) ≡ ret x → force (radec r) ≡ ret tt
sys-ret-transfer r {x} eq =
  fHide-ret {P = decMed (med (toSys r)) ∥⇘ ioES ⇙ absNodesOf (toSys r)} {A = ioES} absInner
  where
    inner : force (decMed (med (toSys r)) ∥⇘ ioES ⇙ nodesOf (toSys r)) ≡ ret x
    inner = fHide-ret-inv {P = decMed (med (toSys r)) ∥⇘ ioES ⇙ nodesOf (toSys r)} {A = ioES} eq
    medR : force (decMed (med (toSys r))) ≡ ret tt
    medR = proj₁ (∥⇙-ret-inv {A = ioES} {P = decMed (med (toSys r))} {Q = nodesOf (toSys r)} inner)
    nodesR : force (nodesOf (toSys r)) ≡ ret tt
    nodesR = proj₂ (∥⇙-ret-inv {A = ioES} {P = decMed (med (toSys r))} {Q = nodesOf (toSys r)} inner)
    absInner : force (decMed (med (toSys r)) ∥⇘ ioES ⇙ absNodesOf (toSys r)) ≡ ret tt
    absInner = ∥⇙-ret-intro {A = ioES} {P = decMed (med (toSys r))} {Q = absNodesOf (toSys r)}
                 medR (nodes-ret-transfer (toSys r) nodesR)

------------------------------------------------------------------------
-- BACKWARD √ (`osqrtB`) leaf machinery.  The √-asymmetry (documented above)
-- means the abstract side can `ret` at a coarse-terminal position whose
-- CONCRETE image sits at a loop-re-entry `xSil st` (a `sil`, not a `ret`).
-- So the backward transfer is a WEAK run: from `force (absXc l d q) ≡ ret`
-- (an abstract-terminal position, i.e. `isFin (coarsen q) ≡ true`) the
-- concrete peer τ*-collapses any pending `xSil` and reaches a `ret`.
------------------------------------------------------------------------

-- the LTS τ-step + weak τ* closure (peer-level, whole-system alphabet)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; sSil )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; τ*-trans )
-- the single-step τ-intro lifts + the committed CS/BF peer sil-steps
open MSysStep
  using ( ⦀-τ-L; ⦀-τ-R; ∥⇘⇙-τ-L; ∥⇘⇙-τ-R
        ; decCSc-sil-step; decCSs-sil-step; decBFc-sil-step; decBFs-sil-step )

------------------------------------------------------------------------
-- The 8 MISSING peer loop-re-entry sil-steps (TS/KA/LN/LF, client+server).
-- Each is `sSil refl`: the concrete peer at `xSil st` forces to `sil (xHead
-- st)` (the `iter`-loop-back), mirroring the committed CS/BF sil-steps.
------------------------------------------------------------------------
decTSc-sil-step : (l : Link) (d : Dir) (st : TS.TSState)
  → decTSc l d (tcSil st) ─[ τ ]─► decTSc l d (tcHead st)
decTSc-sil-step l d st = sSil refl
decTSs-sil-step : (l : Link) (d : Dir) (st : TS.TSState)
  → decTSs l d (tsSil st) ─[ τ ]─► decTSs l d (tsHead st)
decTSs-sil-step l d st = sSil refl
decKAc-sil-step : (l : Link) (d : Dir) (st : KA.KAState)
  → decKAc l d (kcSil st) ─[ τ ]─► decKAc l d (kcHead st)
decKAc-sil-step l d st = sSil refl
decKAs-sil-step : (l : Link) (d : Dir) (st : KA.KAState)
  → decKAs l d (ksSil st) ─[ τ ]─► decKAs l d (ksHead st)
decKAs-sil-step l d st = sSil refl
decLNc-sil-step : (l : Link) (d : Dir) (st : LN.LNState)
  → decLNc l d (lncSil st) ─[ τ ]─► decLNc l d (lncHead st)
decLNc-sil-step l d st = sSil refl
decLNs-sil-step : (l : Link) (d : Dir) (st : LN.LNState)
  → decLNs l d (lnsSil st) ─[ τ ]─► decLNs l d (lnsHead st)
decLNs-sil-step l d st = sSil refl
decLFc-sil-step : (l : Link) (d : Dir) (st : LF.LFState)
  → decLFc l d (lfcSil st) ─[ τ ]─► decLFc l d (lfcHead st)
decLFc-sil-step l d st = sSil refl
decLFs-sil-step : (l : Link) (d : Dir) (st : LF.LFState)
  → decLFs l d (lfsSil st) ─[ τ ]─► decLFs l d (lfsHead st)
decLFs-sil-step l d st = sSil refl

------------------------------------------------------------------------
-- τ* interleave / sync-gated lifts (fold the single-step τ-intro over a τ*
-- run) + the two-operand "run both" combinators.
------------------------------------------------------------------------
⦀-τ*-L : (P Q : NetProc) {P′ : NetProc} → P ─[τ*]─► P′ → (P ⦀ Q) ─[τ*]─► (P′ ⦀ Q)
⦀-τ*-L P Q τ*-refl = τ*-refl
⦀-τ*-L P Q (τ*-step {t′ = P₁} s rest) = τ*-step (⦀-τ-L P Q s) (⦀-τ*-L P₁ Q rest)
⦀-τ*-R : (P Q : NetProc) {Q′ : NetProc} → Q ─[τ*]─► Q′ → (P ⦀ Q) ─[τ*]─► (P ⦀ Q′)
⦀-τ*-R P Q τ*-refl = τ*-refl
⦀-τ*-R P Q (τ*-step {t′ = Q₁} s rest) = τ*-step (⦀-τ-R P Q s) (⦀-τ*-R P Q₁ rest)
∥⇘⇙-τ*-L : (A : EventSet) (P Q : NetProc) {P′ : NetProc}
         → P ─[τ*]─► P′ → (P ∥⇘ A ⇙ Q) ─[τ*]─► (P′ ∥⇘ A ⇙ Q)
∥⇘⇙-τ*-L A P Q τ*-refl = τ*-refl
∥⇘⇙-τ*-L A P Q (τ*-step {t′ = P₁} s rest) = τ*-step (∥⇘⇙-τ-L A P Q s) (∥⇘⇙-τ*-L A P₁ Q rest)
∥⇘⇙-τ*-R : (A : EventSet) (P Q : NetProc) {Q′ : NetProc}
         → Q ─[τ*]─► Q′ → (P ∥⇘ A ⇙ Q) ─[τ*]─► (P ∥⇘ A ⇙ Q′)
∥⇘⇙-τ*-R A P Q τ*-refl = τ*-refl
∥⇘⇙-τ*-R A P Q (τ*-step {t′ = Q₁} s rest) = τ*-step (∥⇘⇙-τ-R A P Q s) (∥⇘⇙-τ*-R A P Q₁ rest)

-- run BOTH operands of `⦀` (first the left, then the right past the left's target)
⦀-run2 : {P P′ Q Q′ : NetProc} → P ─[τ*]─► P′ → Q ─[τ*]─► Q′ → (P ⦀ Q) ─[τ*]─► (P′ ⦀ Q′)
⦀-run2 {P} {P′} {Q} {Q′} rP rQ = τ*-trans (⦀-τ*-L P Q rP) (⦀-τ*-R P′ Q rQ)

------------------------------------------------------------------------
-- Per-peer BACKWARD weak-ret: an abstract-terminal position (`isFin (coarsen
-- q) ≡ true`) ⇒ the concrete peer weak-runs to a `ret`.  Head-terminal ⇒
-- ZERO τ (`force-renameMap-ret`); sil-terminal ⇒ ONE loop-back τ then the
-- head `ret`; every non-terminal position is killed by the `false ≡ true`.
------------------------------------------------------------------------
WRet : NetProc → Set₁
WRet P = Σ[ Q ∈ NetProc ] (P ─[τ*]─► Q) × (force Q ≡ ret tt)

decCSc-fin→wret : (l : Link) (d : Dir) (q : CScPos)
  → csCfin (coarsenCSc q) ≡ true → WRet (decCSc l d q)
decCSc-fin→wret l d (csHead CS.stDone) _ =
  decCSc l d (csHead CS.stDone) , τ*-refl , CSNO.force-renameMap-ret {P = decCSc-src l d (csHead CS.stDone)} refl
decCSc-fin→wret l d (csHead CS.stIdle) ()
decCSc-fin→wret l d (csHead CS.stCanAwait) ()
decCSc-fin→wret l d (csHead CS.stMustReply) ()
decCSc-fin→wret l d (csHead CS.stIntersect) ()
decCSc-fin→wret l d csReqNext1 ()
decCSc-fin→wret l d (csFindInt1 ps) ()
decCSc-fin→wret l d csDone1 ()
decCSc-fin→wret l d (csRF1 h t) ()
decCSc-fin→wret l d (csRB1 pt t) ()
decCSc-fin→wret l d (csIF1 pt t) ()
decCSc-fin→wret l d (csINF1 t) ()
decCSc-fin→wret l d (csSil CS.stDone) _ =
  decCSc l d (csHead CS.stDone) , τ*-step (decCSc-sil-step l d CS.stDone) τ*-refl , CSNO.force-renameMap-ret {P = decCSc-src l d (csHead CS.stDone)} refl
decCSc-fin→wret l d (csSil CS.stIdle) ()
decCSc-fin→wret l d (csSil CS.stCanAwait) ()
decCSc-fin→wret l d (csSil CS.stMustReply) ()
decCSc-fin→wret l d (csSil CS.stIntersect) ()

decCSs-fin→wret : (l : Link) (d : Dir) (q : CSsPos)
  → csSfin (coarsenCSs q) ≡ true → WRet (decCSs l d q)
decCSs-fin→wret l d (ssHead CS.stDone) _ =
  decCSs l d (ssHead CS.stDone) , τ*-refl , CSNO.force-renameMap-ret {P = decCSs-src l d (ssHead CS.stDone)} refl
decCSs-fin→wret l d (ssHead CS.stIdle) ()
decCSs-fin→wret l d (ssHead CS.stCanAwait) ()
decCSs-fin→wret l d (ssHead CS.stMustReply) ()
decCSs-fin→wret l d (ssHead CS.stIntersect) ()
decCSs-fin→wret l d ssReqNext1 ()
decCSs-fin→wret l d (ssFindInt1 ps) ()
decCSs-fin→wret l d ssDone1 ()
decCSs-fin→wret l d (ssRF1 h t) ()
decCSs-fin→wret l d (ssRB1 pt t) ()
decCSs-fin→wret l d ssAw1 ()
decCSs-fin→wret l d (ssIF1 pt t) ()
decCSs-fin→wret l d (ssINF1 t) ()
decCSs-fin→wret l d (ssSil CS.stDone) _ =
  decCSs l d (ssHead CS.stDone) , τ*-step (decCSs-sil-step l d CS.stDone) τ*-refl , CSNO.force-renameMap-ret {P = decCSs-src l d (ssHead CS.stDone)} refl
decCSs-fin→wret l d (ssSil CS.stIdle) ()
decCSs-fin→wret l d (ssSil CS.stCanAwait) ()
decCSs-fin→wret l d (ssSil CS.stMustReply) ()
decCSs-fin→wret l d (ssSil CS.stIntersect) ()

decBFc-fin→wret : (l : Link) (d : Dir) (q : BFcPos)
  → bfCfin (coarsenBFc q) ≡ true → WRet (decBFc l d q)
decBFc-fin→wret l d (bcHead BF.stDone) _ =
  decBFc l d (bcHead BF.stDone) , τ*-refl , BFNO.force-renameMap-ret {P = decBFc-src l d (bcHead BF.stDone)} refl
decBFc-fin→wret l d (bcHead BF.stIdle) ()
decBFc-fin→wret l d (bcHead BF.stBusy) ()
decBFc-fin→wret l d (bcHead BF.stStreaming) ()
decBFc-fin→wret l d (bcReq1 r) ()
decBFc-fin→wret l d bcDone1 ()
decBFc-fin→wret l d (bcBlk1 b) ()
decBFc-fin→wret l d (bcSil BF.stDone) _ =
  decBFc l d (bcHead BF.stDone) , τ*-step (decBFc-sil-step l d BF.stDone) τ*-refl , BFNO.force-renameMap-ret {P = decBFc-src l d (bcHead BF.stDone)} refl
decBFc-fin→wret l d (bcSil BF.stIdle) ()
decBFc-fin→wret l d (bcSil BF.stBusy) ()
decBFc-fin→wret l d (bcSil BF.stStreaming) ()

decBFs-fin→wret : (l : Link) (d : Dir) (q : BFsPos)
  → bfSfin (coarsenBFs q) ≡ true → WRet (decBFs l d q)
decBFs-fin→wret l d (bsHead BF.stDone) _ =
  decBFs l d (bsHead BF.stDone) , τ*-refl , BFNO.force-renameMap-ret {P = decBFs-src l d (bsHead BF.stDone)} refl
decBFs-fin→wret l d (bsHead BF.stIdle) ()
decBFs-fin→wret l d (bsHead BF.stBusy) ()
decBFs-fin→wret l d (bsHead BF.stStreaming) ()
decBFs-fin→wret l d (bsReq1 r) ()
decBFs-fin→wret l d bsDone1 ()
decBFs-fin→wret l d bsStart1 ()
decBFs-fin→wret l d bsNoBlk1 ()
decBFs-fin→wret l d (bsBlk1 b) ()
decBFs-fin→wret l d bsBatchDone1 ()
decBFs-fin→wret l d (bsSil BF.stDone) _ =
  decBFs l d (bsHead BF.stDone) , τ*-step (decBFs-sil-step l d BF.stDone) τ*-refl , BFNO.force-renameMap-ret {P = decBFs-src l d (bsHead BF.stDone)} refl
decBFs-fin→wret l d (bsSil BF.stIdle) ()
decBFs-fin→wret l d (bsSil BF.stBusy) ()
decBFs-fin→wret l d (bsSil BF.stStreaming) ()

decTSc-fin→wret : (l : Link) (d : Dir) (q : TScPos)
  → tsCfin (coarsenTSc q) ≡ true → WRet (decTSc l d q)
decTSc-fin→wret l d (tcHead TS.stDone) _ =
  decTSc l d (tcHead TS.stDone) , τ*-refl , TSNO.force-renameMap-ret {P = decTSc-src l d (tcHead TS.stDone)} refl
decTSc-fin→wret l d (tcHead TS.stInit) ()
decTSc-fin→wret l d (tcHead TS.stIdle) ()
decTSc-fin→wret l d (tcHead TS.stTxIdsBlocking) ()
decTSc-fin→wret l d (tcHead TS.stTxIdsNonBlocking) ()
decTSc-fin→wret l d (tcHead TS.stTxs) ()
decTSc-fin→wret l d (tcReqIdsB1 a r) ()
decTSc-fin→wret l d (tcReqIdsNB1 a r) ()
decTSc-fin→wret l d (tcReqTxs1 ids) ()
decTSc-fin→wret l d (tcRepB1 ids) ()
decTSc-fin→wret l d tcDone1 ()
decTSc-fin→wret l d (tcRepNB1 ids) ()
decTSc-fin→wret l d (tcRepTxs1 txs) ()
decTSc-fin→wret l d (tcSil TS.stDone) _ =
  decTSc l d (tcHead TS.stDone) , τ*-step (decTSc-sil-step l d TS.stDone) τ*-refl , TSNO.force-renameMap-ret {P = decTSc-src l d (tcHead TS.stDone)} refl
decTSc-fin→wret l d (tcSil TS.stInit) ()
decTSc-fin→wret l d (tcSil TS.stIdle) ()
decTSc-fin→wret l d (tcSil TS.stTxIdsBlocking) ()
decTSc-fin→wret l d (tcSil TS.stTxIdsNonBlocking) ()
decTSc-fin→wret l d (tcSil TS.stTxs) ()

decTSs-fin→wret : (l : Link) (d : Dir) (q : TSsPos)
  → tsSfin (coarsenTSs q) ≡ true → WRet (decTSs l d q)
decTSs-fin→wret l d (tsHead TS.stDone) _ =
  decTSs l d (tsHead TS.stDone) , τ*-refl , TSNO.force-renameMap-ret {P = decTSs-src l d (tsHead TS.stDone)} refl
decTSs-fin→wret l d (tsHead TS.stInit) ()
decTSs-fin→wret l d (tsHead TS.stIdle) ()
decTSs-fin→wret l d (tsHead TS.stTxIdsBlocking) ()
decTSs-fin→wret l d (tsHead TS.stTxIdsNonBlocking) ()
decTSs-fin→wret l d (tsHead TS.stTxs) ()
decTSs-fin→wret l d tsDone1 ()
decTSs-fin→wret l d (tsReqB1 ar) ()
decTSs-fin→wret l d (tsReqNB1 ar) ()
decTSs-fin→wret l d (tsReqTxs1 ids) ()
decTSs-fin→wret l d (tsSil TS.stDone) _ =
  decTSs l d (tsHead TS.stDone) , τ*-step (decTSs-sil-step l d TS.stDone) τ*-refl , TSNO.force-renameMap-ret {P = decTSs-src l d (tsHead TS.stDone)} refl
decTSs-fin→wret l d (tsSil TS.stInit) ()
decTSs-fin→wret l d (tsSil TS.stIdle) ()
decTSs-fin→wret l d (tsSil TS.stTxIdsBlocking) ()
decTSs-fin→wret l d (tsSil TS.stTxIdsNonBlocking) ()
decTSs-fin→wret l d (tsSil TS.stTxs) ()

decKAc-fin→wret : (l : Link) (d : Dir) (q : KAcPos)
  → kaCfin (coarsenKAc q) ≡ true → WRet (decKAc l d q)
decKAc-fin→wret l d (kcHead KA.stDone) _ =
  decKAc l d (kcHead KA.stDone) , τ*-refl , KANO.force-renameMap-ret {P = decKAc-src l d (kcHead KA.stDone)} refl
decKAc-fin→wret l d (kcHead KA.stClient) ()
decKAc-fin→wret l d (kcHead (KA.stServer c)) ()
decKAc-fin→wret l d (kcErr1 cq cr ne) ()
decKAc-fin→wret l d (kcReq1 c) ()
decKAc-fin→wret l d kcDone1 ()
decKAc-fin→wret l d (kcSil KA.stDone) _ =
  decKAc l d (kcHead KA.stDone) , τ*-step (decKAc-sil-step l d KA.stDone) τ*-refl , KANO.force-renameMap-ret {P = decKAc-src l d (kcHead KA.stDone)} refl
decKAc-fin→wret l d (kcSil KA.stClient) ()
decKAc-fin→wret l d (kcSil (KA.stServer c)) ()
decKAc-fin→wret l d kcTermE1 _ =
  decKAc l d kcTermE1 , τ*-refl , KANO.force-renameMap-ret {P = decKAc-src l d kcTermE1} refl

decKAs-fin→wret : (l : Link) (d : Dir) (q : KAsPos)
  → kaSfin (coarsenKAs q) ≡ true → WRet (decKAs l d q)
decKAs-fin→wret l d (ksHead KA.stDone) _ =
  decKAs l d (ksHead KA.stDone) , τ*-refl , KANO.force-renameMap-ret {P = decKAs-src l d (ksHead KA.stDone)} refl
decKAs-fin→wret l d (ksHead KA.stClient) ()
decKAs-fin→wret l d (ksHead (KA.stServer c)) ()
decKAs-fin→wret l d (ksRecv1 c) ()
decKAs-fin→wret l d ksDdone1 ()
decKAs-fin→wret l d (ksSil KA.stDone) _ =
  decKAs l d (ksHead KA.stDone) , τ*-step (decKAs-sil-step l d KA.stDone) τ*-refl , KANO.force-renameMap-ret {P = decKAs-src l d (ksHead KA.stDone)} refl
decKAs-fin→wret l d (ksSil KA.stClient) ()
decKAs-fin→wret l d (ksSil (KA.stServer c)) ()

decLNc-fin→wret : (l : Link) (d : Dir) (q : LNcPos)
  → lnCfin (coarsenLNc q) ≡ true → WRet (decLNc l d q)
decLNc-fin→wret l d (lncHead LN.stDone) _ =
  decLNc l d (lncHead LN.stDone) , τ*-refl , LNNO.force-renameMap-ret {P = decLNc-src l d (lncHead LN.stDone)} refl
decLNc-fin→wret l d (lncHead LN.stIdle) ()
decLNc-fin→wret l d (lncHead LN.stBusy) ()
decLNc-fin→wret l d (lncRann1 h) ()
decLNc-fin→wret l d (lncRoff1 q) ()
decLNc-fin→wret l d (lncRtxs1 q) ()
decLNc-fin→wret l d (lncRvot1 vs) ()
decLNc-fin→wret l d lncReq1 ()
decLNc-fin→wret l d lncDone1 ()
decLNc-fin→wret l d (lncSil LN.stDone) _ =
  decLNc l d (lncHead LN.stDone) , τ*-step (decLNc-sil-step l d LN.stDone) τ*-refl , LNNO.force-renameMap-ret {P = decLNc-src l d (lncHead LN.stDone)} refl
decLNc-fin→wret l d (lncSil LN.stIdle) ()
decLNc-fin→wret l d (lncSil LN.stBusy) ()

decLNs-fin→wret : (l : Link) (d : Dir) (q : LNsPos)
  → lnSfin (coarsenLNs q) ≡ true → WRet (decLNs l d q)
decLNs-fin→wret l d (lnsHead LN.stDone) _ =
  decLNs l d (lnsHead LN.stDone) , τ*-refl , LNNO.force-renameMap-ret {P = decLNs-src l d (lnsHead LN.stDone)} refl
decLNs-fin→wret l d (lnsHead LN.stIdle) ()
decLNs-fin→wret l d (lnsHead LN.stBusy) ()
decLNs-fin→wret l d lnsDone1 ()
decLNs-fin→wret l d (lnsWann1 h) ()
decLNs-fin→wret l d (lnsWoff1 q) ()
decLNs-fin→wret l d (lnsWtxs1 q) ()
decLNs-fin→wret l d (lnsWvot1 vs) ()
decLNs-fin→wret l d (lnsSil LN.stDone) _ =
  decLNs l d (lnsHead LN.stDone) , τ*-step (decLNs-sil-step l d LN.stDone) τ*-refl , LNNO.force-renameMap-ret {P = decLNs-src l d (lnsHead LN.stDone)} refl
decLNs-fin→wret l d (lnsSil LN.stIdle) ()
decLNs-fin→wret l d (lnsSil LN.stBusy) ()

decLFc-fin→wret : (l : Link) (d : Dir) (q : LFcPos)
  → lfCfin (coarsenLFc q) ≡ true → WRet (decLFc l d q)
decLFc-fin→wret l d (lfcHead LF.stDone) _ =
  decLFc l d (lfcHead LF.stDone) , τ*-refl , LFNO.force-renameMap-ret {P = decLFc-src l d (lfcHead LF.stDone)} refl
decLFc-fin→wret l d (lfcHead LF.stIdle) ()
decLFc-fin→wret l d (lfcHead LF.stBlock) ()
decLFc-fin→wret l d (lfcHead LF.stBlockTxs) ()
decLFc-fin→wret l d (lfcHead LF.stVotes) ()
decLFc-fin→wret l d (lfcHead LF.stBlockRange) ()
decLFc-fin→wret l d (lfcRblk1 b) ()
decLFc-fin→wret l d (lfcRbtx1 ts) ()
decLFc-fin→wret l d (lfcRvot1 vs) ()
decLFc-fin→wret l d (lfcRnext1 b ts) ()
decLFc-fin→wret l d (lfcRlast1 b ts) ()
decLFc-fin→wret l d (lfcWblk1 pt) ()
decLFc-fin→wret l d (lfcWtxs1 pb) ()
decLFc-fin→wret l d (lfcWvot1 vs) ()
decLFc-fin→wret l d (lfcWrng1 r) ()
decLFc-fin→wret l d lfcDone1 ()
decLFc-fin→wret l d (lfcSil LF.stDone) _ =
  decLFc l d (lfcHead LF.stDone) , τ*-step (decLFc-sil-step l d LF.stDone) τ*-refl , LFNO.force-renameMap-ret {P = decLFc-src l d (lfcHead LF.stDone)} refl
decLFc-fin→wret l d (lfcSil LF.stIdle) ()
decLFc-fin→wret l d (lfcSil LF.stBlock) ()
decLFc-fin→wret l d (lfcSil LF.stBlockTxs) ()
decLFc-fin→wret l d (lfcSil LF.stVotes) ()
decLFc-fin→wret l d (lfcSil LF.stBlockRange) ()

decLFs-fin→wret : (l : Link) (d : Dir) (q : LFsPos)
  → lfSfin (coarsenLFs q) ≡ true → WRet (decLFs l d q)
decLFs-fin→wret l d (lfsHead LF.stDone) _ =
  decLFs l d (lfsHead LF.stDone) , τ*-refl , LFNO.force-renameMap-ret {P = decLFs-src l d (lfsHead LF.stDone)} refl
decLFs-fin→wret l d (lfsHead LF.stIdle) ()
decLFs-fin→wret l d (lfsHead LF.stBlock) ()
decLFs-fin→wret l d (lfsHead LF.stBlockTxs) ()
decLFs-fin→wret l d (lfsHead LF.stVotes) ()
decLFs-fin→wret l d (lfsHead LF.stBlockRange) ()
decLFs-fin→wret l d lfsDone1 ()
decLFs-fin→wret l d (lfsWblk1 b) ()
decLFs-fin→wret l d (lfsWtxs1 ts) ()
decLFs-fin→wret l d (lfsWvot1 vs) ()
decLFs-fin→wret l d (lfsWnext1 bt) ()
decLFs-fin→wret l d (lfsWlast1 bt) ()
decLFs-fin→wret l d (lfsSil LF.stDone) _ =
  decLFs l d (lfsHead LF.stDone) , τ*-step (decLFs-sil-step l d LF.stDone) τ*-refl , LFNO.force-renameMap-ret {P = decLFs-src l d (lfsHead LF.stDone)} refl
decLFs-fin→wret l d (lfsSil LF.stIdle) ()
decLFs-fin→wret l d (lfsSil LF.stBlock) ()
decLFs-fin→wret l d (lfsSil LF.stBlockTxs) ()
decLFs-fin→wret l d (lfsSil LF.stVotes) ()
decLFs-fin→wret l d (lfsSil LF.stBlockRange) ()

------------------------------------------------------------------------
-- Per-peer BACKWARD weak-ret from the ABSTRACT `ret` (`tableSpec-ret-fin`
-- extracts `isFin`, then `decX-fin→wret` supplies the concrete weak run).
------------------------------------------------------------------------
decCSc-wret : (l : Link) (d : Dir) (q : CScPos) → force (absCSc l d q) ≡ ret tt → WRet (decCSc l d q)
decCSc-wret l d q eq = decCSc-fin→wret l d q (tableSpec-ret-fin _ (coarsenCSc q) eq)
decCSs-wret : (l : Link) (d : Dir) (q : CSsPos) → force (absCSs l d q) ≡ ret tt → WRet (decCSs l d q)
decCSs-wret l d q eq = decCSs-fin→wret l d q (tableSpec-ret-fin _ (coarsenCSs q) eq)
decBFc-wret : (l : Link) (d : Dir) (q : BFcPos) → force (absBFc l d q) ≡ ret tt → WRet (decBFc l d q)
decBFc-wret l d q eq = decBFc-fin→wret l d q (tableSpec-ret-fin _ (coarsenBFc q) eq)
decBFs-wret : (l : Link) (d : Dir) (q : BFsPos) → force (absBFs l d q) ≡ ret tt → WRet (decBFs l d q)
decBFs-wret l d q eq = decBFs-fin→wret l d q (tableSpec-ret-fin _ (coarsenBFs q) eq)
decTSc-wret : (l : Link) (d : Dir) (q : TScPos) → force (absTSc l d q) ≡ ret tt → WRet (decTSc l d q)
decTSc-wret l d q eq = decTSc-fin→wret l d q (tableSpec-ret-fin _ (coarsenTSc q) eq)
decTSs-wret : (l : Link) (d : Dir) (q : TSsPos) → force (absTSs l d q) ≡ ret tt → WRet (decTSs l d q)
decTSs-wret l d q eq = decTSs-fin→wret l d q (tableSpec-ret-fin _ (coarsenTSs q) eq)
decKAc-wret : (l : Link) (d : Dir) (q : KAcPos) → force (absKAc l d q) ≡ ret tt → WRet (decKAc l d q)
decKAc-wret l d q eq = decKAc-fin→wret l d q (tableSpec-ret-fin _ (coarsenKAc q) eq)
decKAs-wret : (l : Link) (d : Dir) (q : KAsPos) → force (absKAs l d q) ≡ ret tt → WRet (decKAs l d q)
decKAs-wret l d q eq = decKAs-fin→wret l d q (tableSpec-ret-fin _ (coarsenKAs q) eq)
decLNc-wret : (l : Link) (d : Dir) (q : LNcPos) → force (absLNc l d q) ≡ ret tt → WRet (decLNc l d q)
decLNc-wret l d q eq = decLNc-fin→wret l d q (tableSpec-ret-fin _ (coarsenLNc q) eq)
decLNs-wret : (l : Link) (d : Dir) (q : LNsPos) → force (absLNs l d q) ≡ ret tt → WRet (decLNs l d q)
decLNs-wret l d q eq = decLNs-fin→wret l d q (tableSpec-ret-fin _ (coarsenLNs q) eq)
decLFc-wret : (l : Link) (d : Dir) (q : LFcPos) → force (absLFc l d q) ≡ ret tt → WRet (decLFc l d q)
decLFc-wret l d q eq = decLFc-fin→wret l d q (tableSpec-ret-fin _ (coarsenLFc q) eq)
decLFs-wret : (l : Link) (d : Dir) (q : LFsPos) → force (absLFs l d q) ≡ ret tt → WRet (decLFs l d q)
decLFs-wret l d q eq = decLFs-fin→wret l d q (tableSpec-ret-fin _ (coarsenLFs q) eq)

------------------------------------------------------------------------
-- Bundle BACKWARD weak-ret: peel the abstract 12-peer bundle `ret`, weak-run
-- each concrete peer to its `ret`, sequence the runs through the `⦀` nest.
------------------------------------------------------------------------
bundleG-wret : (l : Link) (cl sv : Dir)
      (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    → force (absBundleG l cl sv csc css bfc bfs ip) ≡ ret tt
    → WRet (bundleG l cl sv csc css bfc bfs ip)
bundleG-wret l cl sv csc css bfc bfs (mkInert tsc' tss' kac' kas' lnc' lns' lfc' lfs') eq =
  let kacR , r1  = ⦀-ret-inv eq
      kasR , r2  = ⦀-ret-inv r1
      cscR , r3  = ⦀-ret-inv r2
      cssR , r4  = ⦀-ret-inv r3
      bfcR , r5  = ⦀-ret-inv r4
      bfsR , r6  = ⦀-ret-inv r5
      tscR , r7  = ⦀-ret-inv r6
      tssR , r8  = ⦀-ret-inv r7
      lncR , r9  = ⦀-ret-inv r8
      lnsR , r10 = ⦀-ret-inv r9
      lfcR , lfsR = ⦀-ret-inv r10
      _ , runKAc , fKAc = decKAc-wret l cl kac' kacR
      _ , runKAs , fKAs = decKAs-wret l sv kas' kasR
      _ , runCSc , fCSc = decCSc-wret l cl csc cscR
      _ , runCSs , fCSs = decCSs-wret l sv css cssR
      _ , runBFc , fBFc = decBFc-wret l cl bfc bfcR
      _ , runBFs , fBFs = decBFs-wret l sv bfs bfsR
      _ , runTSc , fTSc = decTSc-wret l cl tsc' tscR
      _ , runTSs , fTSs = decTSs-wret l sv tss' tssR
      _ , runLNc , fLNc = decLNc-wret l cl lnc' lncR
      _ , runLNs , fLNs = decLNs-wret l sv lns' lnsR
      _ , runLFc , fLFc = decLFc-wret l cl lfc' lfcR
      _ , runLFs , fLFs = decLFs-wret l sv lfs' lfsR
  in _
   , ⦀-run2 runKAc (⦀-run2 runKAs (⦀-run2 runCSc (⦀-run2 runCSs (⦀-run2 runBFc
       (⦀-run2 runBFs (⦀-run2 runTSc (⦀-run2 runTSs (⦀-run2 runLNc (⦀-run2 runLNs
         (⦀-run2 runLFc runLFs))))))))))
   , ⦀-ret-intro fKAc (⦀-ret-intro fKAs (⦀-ret-intro fCSc (⦀-ret-intro fCSs
       (⦀-ret-intro fBFc (⦀-ret-intro fBFs (⦀-ret-intro fTSc (⦀-ret-intro fTSs
         (⦀-ret-intro fLNc (⦀-ret-intro fLNs (⦀-ret-intro fLFc fLFs))))))))))

------------------------------------------------------------------------
-- Per-node BACKWARD weak-ret: peel `(bundle ⦀ bundle) ∥⇘ apiES ⇙ driver`;
-- the driver is SHARED and rets (witness reused), the two bundles weak-run.
------------------------------------------------------------------------
decNodeA-wret : (s : NodeStateA) → force (absNodeA s) ≡ ret tt → WRet (decNodeA s)
decNodeA-wret (mkNodeA cscab cssab bfcab bfsab ppab cscac cssac bfcac bfsac ppac ipab ipac) eq =
  let bnds , drv = ∥⇙-ret-inv eq
      b1r , b2r  = ⦀-ret-inv bnds
      _ , run1 , f1 = bundleG-wret linkAB lo hi cscab cssab bfcab bfsab ipab b1r
      _ , run2 , f2 = bundleG-wret linkAC lo hi cscac cssac bfcac bfsac ipac b2r
  in _ , ∥⇘⇙-τ*-L apiES _ _ (⦀-run2 run1 run2) , ∥⇙-ret-intro (⦀-ret-intro f1 f2) drv

decNodeB-wret : (s : NodeStateB) → force (absNodeB s) ≡ ret tt → WRet (decNodeB s)
decNodeB-wret (mkNodeB cscab cssab bfcab bfsab cscbd cssbd bfcbd bfsbd cpb ipab ipbd) eq =
  let bnds , drv = ∥⇙-ret-inv eq
      b1r , b2r  = ⦀-ret-inv bnds
      _ , run1 , f1 = bundleG-wret linkAB hi lo cscab cssab bfcab bfsab ipab b1r
      _ , run2 , f2 = bundleG-wret linkBD lo hi cscbd cssbd bfcbd bfsbd ipbd b2r
  in _ , ∥⇘⇙-τ*-L apiES _ _ (⦀-run2 run1 run2) , ∥⇙-ret-intro (⦀-ret-intro f1 f2) drv

decNodeC-wret : (s : NodeStateC) → force (absNodeC s) ≡ ret tt → WRet (decNodeC s)
decNodeC-wret (mkNodeC cscac cssac bfcac bfsac csccd csscd bfccd bfscd cpc ipac ipcd) eq =
  let bnds , drv = ∥⇙-ret-inv eq
      b1r , b2r  = ⦀-ret-inv bnds
      _ , run1 , f1 = bundleG-wret linkAC hi lo cscac cssac bfcac bfsac ipac b1r
      _ , run2 , f2 = bundleG-wret linkCD lo hi csccd csscd bfccd bfscd ipcd b2r
  in _ , ∥⇘⇙-τ*-L apiES _ _ (⦀-run2 run1 run2) , ∥⇙-ret-intro (⦀-ret-intro f1 f2) drv

decNodeD-wret : (s : NodeStateD) → force (absNodeD s) ≡ ret tt → WRet (decNodeD s)
decNodeD-wret (mkNodeD cscbd cssbd bfcbd bfsbd consbd csccd csscd bfccd bfscd conscd ipbd ipcd) eq =
  let bnds , drv = ∥⇙-ret-inv eq
      b1r , b2r  = ⦀-ret-inv bnds
      _ , run1 , f1 = bundleG-wret linkBD hi lo cscbd cssbd bfcbd bfsbd ipbd b1r
      _ , run2 , f2 = bundleG-wret linkCD hi lo csccd csscd bfccd bfscd ipcd b2r
  in _ , ∥⇘⇙-τ*-L apiES _ _ (⦀-run2 run1 run2) , ∥⇙-ret-intro (⦀-ret-intro f1 f2) drv

------------------------------------------------------------------------
-- Whole-nodes BACKWARD weak-ret (sequence the 4-node `⦀` runs).
------------------------------------------------------------------------
nodes-wret : (s : SysState) → force (absNodesOf s) ≡ ret tt → WRet (nodesOf s)
nodes-wret s eq =
  let aR , r1 = ⦀-ret-inv eq
      bR , r2 = ⦀-ret-inv r1
      cR , dR = ⦀-ret-inv r2
      _ , runa , fa = decNodeA-wret (nA s) aR
      _ , runb , fb = decNodeB-wret (nB s) bR
      _ , runc , fc = decNodeC-wret (nC s) cR
      _ , rund , fd = decNodeD-wret (nD s) dR
  in _
   , ⦀-run2 runa (⦀-run2 runb (⦀-run2 runc rund))
   , ⦀-ret-intro fa (⦀-ret-intro fb (⦀-ret-intro fc fd))

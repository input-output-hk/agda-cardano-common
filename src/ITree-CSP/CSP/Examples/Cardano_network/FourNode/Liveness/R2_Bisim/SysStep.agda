{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 Task 4 — step characterizations for `sysBisim`
-- (`Praos.SysStep`).
--
-- R2 Task 5 assembles `sysBisim : breakableSystem ≈DR abstractSystem` from the
-- pieces built here.  `breakableSystem = ⟦ initial ⟧` (Praos.SysDecode) is the
-- concrete side (fine per-peer positions, R2 Task 2); `abstractSystem`
-- (Praos.AbstractSystem) is the τ-free side (the eight `tableSpec` peers of
-- Praos.NodeSpecs).  Concrete and abstract SHARE the breakable medium
-- `CopySpecBreakableA` and the drivers `produce`/`consume`; they differ ONLY
-- in the peer bundles (concrete = renamed τ-containing `miniProtocols`;
-- abstract = τ-free `specBundle`/`specBundleFlip`).
--
-- THE RELATION DESIGN
--   `absDec : SysState → NetProc` — the ABSTRACT-side decode: it rebuilds
--   `abstractSystem`'s exact skeleton `(medium ∥⇘ ioES ⇙ nodes) ∖ ioES`,
--   reusing the SHARED medium decode `decMed (med s)` and the SHARED driver
--   decodes (`decProd`/`decCons`/`decCP` from `SysNode`), and replacing each
--   concrete 12-peer bundle by its τ-free abstract counterpart (the eight
--   `tableSpec` peers).  Many concrete positions that differ only by internal
--   τ (peer `sil`, the `csSil`/`bsSil` re-entry positions) project onto the
--   SAME abstract position.  `absDec-init : absDec initial ≡ abstractSystem`
--   is `refl` (the all-idle abstract bundles reduce to `specBundle`/
--   `specBundleFlip` by η, exactly as the concrete `decNodeX-home` are `refl`).
--
--   The bisimulation relation is `R = { (⟦ s ⟧ , absDec s) : s : SysState }`.
--   A concrete internal τ (a hidden io-sync, or a peer/driver `sil`) advances
--   `⟦ s ⟧ → ⟦ s′ ⟧` with `absDec s ≡ absDec s′` (abstract matches by ZERO τ);
--   a concrete VISIBLE api event advances `⟦ s ⟧ → ⟦ s′ ⟧` matched by
--   `absDec s → absDec s′` doing the same visible event.
--
-- THE MEASURE `μ : SysState → ℕ` bounds the internal-τ activity of a state
--   (the medium's in-flight payloads plus each peer/driver's remaining
--   silent-step budget), feeding the `div→`/`div←` obligations (no infinite
--   τ-chain) that R2 Task 5 discharges from the per-τ decrease.
--
-- GENERIC TOP-LEVEL REFLECTION (`top-io-is-sync`, `reflect-⟦⟧-τ`) is proven
--   here GENUINELY (fully proven, no axioms) and INSTANTIATED at the REAL operands
--   `decMed (med s)` / the four `decNodeX` — it inverts any hidden-τ step of
--   `⟦ s ⟧` into either an inner `Par⊤ ioES` τ or a medium/nodes io-SYNC, with
--   NO `evBoth` on io (io ∈ ioES forces `evSync`).  This is the top-level seam
--   the route-1 congruence could not cross; it crosses cleanly on the real
--   system.  (See the R2 Task 4 report for what remains: the per-component
--   step inversions that CLOSE each reflection to a `SysState` move.)
--
-- No axioms, holes, or unsolved metas (R2 deliverable): checked under plain
-- `--guardedness` only.
------------------------------------------------------------------------

open import Level using (0ℓ; Level)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Process_Trees using
  ( PTree; ExtI; AnyTypes; ContinueType; NodeKind; react; ret; sil; react-injective )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep (blkA : Block₃) where

------------------------------------------------------------------------
-- The concrete model, the decode, and the abstract target.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi; IDs; Blocking; NonBlocking )
open IDs using ( N2N_ChainSync; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; input; output; apiCS; apiBF )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

-- the two FSM state enums (concrete peer positions embed these; the abstract
-- positions are keyed on the same enums)
import CSP.Examples.Cardano_network.ChainSync    p as CS
import CSP.Examples.Cardano_network.BlockFetch   p as BF
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.KeepAlive    p as KA
import CSP.Examples.Cardano_network.LeiosNotify  p as LN
import CSP.Examples.Cardano_network.LeiosFetch   p as LF

-- Net_Api operators (the whole-system alphabet): the io-gated stack + node ⦀
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; EventSet; ∅ES; viewV )
open EventSet using ( mem )

-- the whole-system process type (same alias as `⟦_⟧` / `abstractSystem`)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the concrete whole-system decode `⟦_⟧` + its state (R1 SysDecode, R2 Task 2 fine)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧; initial )
-- the medium sub-decode (SHARED between concrete and abstract)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; decMed )
-- the concrete node decodes + the fine per-peer positions and driver phases
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as MSysNode
open MSysNode
  using ( NodeStateA; NodeStateB; NodeStateC; NodeStateD; mkNodeA
        ; decNodeA; decNodeB; decNodeC; decNodeD
        ; CScPos; csHead; csReqNext1; csFindInt1; csDone1
        ; csRF1; csRB1; csIF1; csINF1; csSil
        ; CSsPos; ssHead; ssReqNext1; ssFindInt1; ssDone1
        ; ssRF1; ssRB1; ssAw1; ssIF1; ssINF1; ssSil
        ; BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
        ; BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil
        ; TScPos; tcHead; tcReqIdsB1; tcReqIdsNB1; tcReqTxs1; tcRepB1; tcDone1; tcRepNB1; tcRepTxs1; tcSil; TSsPos; tsHead; tsDone1; tsReqB1; tsReqNB1; tsReqTxs1; tsSil
        ; KAcPos; kcHead; kcErr1; kcReq1; kcDone1; kcSil; kcTermE1; KAsPos; ksHead; ksRecv1; ksDdone1; ksSil
        ; LNcPos; lncHead; lncRann1; lncRoff1; lncRtxs1; lncRvot1; lncReq1; lncDone1; lncSil; LNsPos; lnsHead; lnsDone1; lnsWann1; lnsWoff1; lnsWtxs1; lnsWvot1; lnsSil
        ; LFcPos; lfcHead; lfcRblk1; lfcRbtx1; lfcRvot1; lfcRnext1; lfcRlast1; lfcWblk1; lfcWtxs1; lfcWvot1; lfcWrng1; lfcDone1; lfcSil; LFsPos; lfsHead; lfsDone1; lfsWblk1; lfsWtxs1; lfsWvot1; lfsWnext1; lfsWlast1; lfsSil
        ; InertPos; mkInert; tsc; tss; kac; kas; lnc; lns; lfc; lfs
        ; decTSc; decTSs; decKAc; decKAs; decLNc; decLNs; decLFc; decLFs
        ; ProdPh; ConsPh; ConsDPh; CPPh; consuming; producing
        -- the SHARED driver decodes (identical to the abstract `produce`/`consume`)
        ; decProd; decConsD; decCP )
open NodeStateA ; open NodeStateB ; open NodeStateC ; open NodeStateD

-- the CS/BF alphabet injections (for the renameForce transport instances)
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( ιCS; ιCS⁻¹; ιCS-linv; ιBF; ιBF⁻¹; ιBF-linv )
-- the fine driven-peer decoders + their source-side counterparts (R2 Task 2)
open MSysNode
  using ( decCSc; decCSs; decBFc; decBFs
        ; decCSc-src; decCSs-src; decBFc-src; decBFs-src )
-- the SOURCE-alphabet ChainSync LTS (for the VALUE-route source non-offer);
-- same module instance `RenNO ιCS …` inverts to, so the step types agree
import Semantics.LTS {E = CS.CSEv} {I = ExtI CS.CSEv} as CSLTS
-- reply-payload constructors for the value-route instance
open import CSP.Examples.Cardano_network.Base using ( FromInitiator )
open import CSP.Examples.Cardano_network.Data p
  using ( Header; Tip; chainSync; MsgCSRollForward )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p using ( time₀; length₀ )

-- the abstract target `abstractSystem` (R2 Task 3) + the τ-free peer specs and
-- their tables (position-indexed, so any abstract position is directly nameable)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open NS.Table using ( isFin; nxt )
open NS using
  ( tableSpec
  ; kaClientSpec; kaServerSpec; tsClientSpec; tsServerSpec
  ; csClientSpec; csServerSpec; bfClientSpec; bfServerSpec
  ; csCfin; csCnxt; csSfin; csSnxt; bfCfin; bfCnxt; bfSfin; bfSnxt
  ; tsCfin; tsCnxt; tsSfin; tsSnxt; kaCfin; kaCnxt; kaSfin; kaSnxt
  ; lnCfin; lnCnxt; lnSfin; lnSnxt; lfCfin; lfCnxt; lfSfin; lfSnxt
  -- abstract LN-client / LN-server head positions (for coarsening)
  ; lncIdle; lncBusy; lncTerm; lncRann; lncRoff; lncRtxs; lncRvot; lnsIdle; lnsBusy; lnsDone; lnsTerm
  ; lncWreq; lncWdone; lnsWann; lnsWoff; lnsWtxs; lnsWvot
  -- abstract LF-client / LF-server head positions (for coarsening)
  ; lfcIdle; lfcBlk; lfcBtx; lfcVot; lfcRng; lfcTerm; lfcRblk; lfcRbtx; lfcRvot; lfcRnextRng; lfcRlastRng
  ; lfcWblk; lfcWtxs; lfcWvot; lfcWrng; lfcWdone
  ; lfsIdle; lfsBlk; lfsBtx; lfsVot; lfsRng; lfsDone; lfsTerm
  ; lfsWblk; lfsWtxs; lfsWvot; lfsWnext; lfsWlast
  -- abstract KA-client positions + abstract KA-server positions (for coarsening)
  ; kcClient; kcWmsg; kcAwait; kcWdone; kcErr; kcTerm; kcTermE
  ; ksClient; ksRecv; ksResp; ksDdone; ksTerm
  -- abstract TS-client positions (only head states needed for coarsening)
  ; tcInit; tcIdle; tcBlk; tcNbl; tcTxs; tcTerm; tcAri; tcArt; tcWri; tcWdone; tcWrt
  -- abstract TS-server positions
  ; tsInit; tsIdle; tsBlk; tsNbl; tsTxs; tsTerm; tsDdone; tsWib; tsWin; tsWrt
  -- abstract CS-client positions
  ; ccIdle; ccWreq; ccAwait; ccWfi; ccInt; ccWdone; ccMust
  ; ccArf; ccArb; ccAif; ccAin; ccTerm
  -- abstract CS-server positions
  ; csIdle; csAreq; csCanAwait; csAfi; csInt; csDdone; csMust
  ; csWrf; csWrb; csWar; csWif; csWin; csTerm
  -- abstract BF-client positions
  ; bcIdle; bcWrr; bcBusy; bcWcd; bcStream; bcAblk; bcTerm
  -- abstract BF-server positions
  ; bsIdle; bsAreq; bsBusy; bsDdone; bsWsb; bsStream; bsWnb; bsWblk; bsWbd; bsTerm )

------------------------------------------------------------------------
-- Symbolic step machinery (SYMBOLIC — inverts a hypothesised `─[_]─►` step;
-- NEVER forces the composite tree to WHNF, dodging the 2.5-min/20-GB wall).
------------------------------------------------------------------------

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; τ; evl; evLabel; sVis; sSil; sTau; Diverges )
open Diverges

-- the weak τ* closure (the ABSTRACT weak-τ target the DRbisim `.fwd .on-tau`
-- field wants: `absDec s ═[ τ ]═► absDec s′` unfolds to `wτ (… ─[τ*]─► …)`)
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev )

open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
  using ( ParevR; Par-ev-elim; ParτR; Par-τ-elim )
open ParevR
open ParτR
-- the generic τ-INTRO congruences for `Par` (reverse of `Par-τ-elim`); proven
-- once generically (operands are variables), so APPLYING them to any operands
-- is opaque function application — WHNF-safe (no operand is forced at our site)
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload})
  using ( Par-τ-L; Par-τ-R; Par-soloL; Par-soloR; Par-sync )
open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using ( HideτR; Hide-τ-elim; Hide-τ; HideevR; Hide-ev-elim; Hide-keep; Hide-hidden )
open HideτR
open HideevR

-- the top-level merge on ⊤ (what `∥⇘ ioES ⇙` / `⦀` use at the whole-system layer)
merge⊤ : ⊤ {0ℓ} → ⊤ {0ℓ} → ⊤ {0ℓ}
merge⊤ _ _ = tt

------------------------------------------------------------------------
-- The measure `μ : SysState → ℕ`.
--
-- μ bounds a state's remaining INTERNAL-τ activity.  In this scenario the
-- only τ sources are (a) the peers' loop re-entry `sil`s (the `…Sil`
-- positions), (b) the relay driver's pending `>>=` bind-`sil` (the switch from
-- consuming to producing), and (c) the hidden io-syncs of in-flight medium
-- payloads.  This measure sums (a)+(b) — the STRUCTURAL-sil potential.  The
-- io-sync summand (c) (a per-full-cell count over `MedState`) is the remaining
-- piece needed to make μ strictly decrease across EVERY τ; it is added
-- together with the `μ`-decrease proof (see the R2 Task 4 report — decrease is
-- coupled to `refl-τ`).  KA/TS loops are api-driven (visible), never τ, so
-- they contribute no τ potential.
------------------------------------------------------------------------

-- per-position structural-sil weight: a loop re-entry `sil` costs one τ
μCSc : CScPos → ℕ
μCSc (csSil _) = 1
μCSc _         = 0

μCSs : CSsPos → ℕ
μCSs (ssSil _) = 1
μCSs _         = 0

μBFc : BFcPos → ℕ
μBFc (bcSil _) = 1
μBFc _         = 0

μBFs : BFsPos → ℕ
μBFs (bsSil _) = 1
μBFs _         = 0

-- the produce/consume drivers advance on VISIBLE api events (no τ)
μProd : ProdPh → ℕ
μProd _ = 0

μCons : ConsPh → ℕ
μCons _ = 0

-- node-D consume-driver phase (block + straight chain) has no pending sil
μConsD : ConsDPh → ℕ
μConsD _ = 0

-- the relay driver: while `consuming`, one `>>=` bind-`sil` is pending to
-- switch to the `producing` leg
μCP : CPPh → ℕ
μCP (consuming _ _) = 1
μCP (producing _ _) = 0

-- the medium's structural-sil potential (the in-flight io-sync summand is
-- deferred with the decrease proof — see header)
μMed : MedState → ℕ
μMed _ = 0

-- per-node structural-sil potential (sum over the node's peer positions +
-- driver phases)
μNodeA : NodeStateA → ℕ
μNodeA s = μCSc (csC-AB s) + μCSs (csS-AB s) + μBFc (bfC-AB s) + μBFs (bfS-AB s) + μProd (prod-AB s)
         + μCSc (csC-AC s) + μCSs (csS-AC s) + μBFc (bfC-AC s) + μBFs (bfS-AC s) + μProd (prod-AC s)

μNodeB : NodeStateB → ℕ
μNodeB s = μCSc (csC-AB s) + μCSs (csS-AB s) + μBFc (bfC-AB s) + μBFs (bfS-AB s)
         + μCSc (csC-BD s) + μCSs (csS-BD s) + μBFc (bfC-BD s) + μBFs (bfS-BD s) + μCP (cp-B s)

μNodeC : NodeStateC → ℕ
μNodeC s = μCSc (csC-AC s) + μCSs (csS-AC s) + μBFc (bfC-AC s) + μBFs (bfS-AC s)
         + μCSc (csC-CD s) + μCSs (csS-CD s) + μBFc (bfC-CD s) + μBFs (bfS-CD s) + μCP (cp-C s)

μNodeD : NodeStateD → ℕ
μNodeD s = μCSc (csC-BD s) + μCSs (csS-BD s) + μBFc (bfC-BD s) + μBFs (bfS-BD s) + μConsD (cons-BD s)
         + μCSc (csC-CD s) + μCSs (csS-CD s) + μBFc (bfC-CD s) + μBFs (bfS-CD s) + μConsD (cons-CD s)

-- whole-system structural-sil measure
μ : SysState → ℕ
μ s = μMed (med s) + μNodeA (nA s) + μNodeB (nB s) + μNodeC (nC s) + μNodeD (nD s)

------------------------------------------------------------------------
-- Generic TOP-LEVEL reflection (fully proven, no axioms), instantiated at the REAL
-- system operands.  This is the top-level seam the route-1 congruence could
-- not cross; it crosses cleanly here.  Copied and cleaned from `Route2Spike`
-- (which proved these generic lemmas already, with no axioms).
------------------------------------------------------------------------

-- at the io-gated top `M ∥⇘ ioES ⇙ N`, ANY visible step on an io event is a
-- medium/nodes SYNC (`evSync`) — the `evL`/`evR`/`evBoth` cases carry
-- `¬ ioES.mem` and are refuted by io-membership.  So the inner-`⦀` `evBoth`
-- (the ⊓-overlap route 1 feared) NEVER surfaces on an io event here.
top-io-is-sync :
    (M N : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M′ : NetProc}
  → ioES .mem (X , e) a
  → (M ∥⇘ ioES ⇙ N) ─[ ev (evl (evLabel X e a)) ]─► M′
  → Σ[ M₁ ∈ NetProc ] Σ[ N₁ ∈ NetProc ]
       (M ─[ ev (evl (evLabel X e a)) ]─► M₁)
     × (N ─[ ev (evl (evLabel X e a)) ]─► N₁)
     × (M′ ≡ (M₁ ∥⇘ ioES ⇙ N₁))
top-io-is-sync M N iomem step with Par-ev-elim ioES merge⊤ M N step
... | evSync _ sM sN = _ , _ , sM , sN , refl
... | evL  ¬p _      = ⊥-elim (¬p iomem)
... | evR  ¬p _      = ⊥-elim (¬p iomem)
... | evBoth ¬p _ _  = ⊥-elim (¬p iomem)

-- the outcome of reflecting one hidden-τ step of `(M ∥⇘ ioES ⇙ N) ∖ ioES`
data ReflOut (M N : NetProc) (M″ : NetProc) : Set₁ where
  -- an internal τ of the inner `Par⊤ ioES M N` (medium/nodes/driver internal move)
  innerτ : (P′ : NetProc)
         → (M ∥⇘ ioES ⇙ N) ─[ τ ]─► P′ → M″ ≡ P′ ∖ ioES → ReflOut M N M″
  -- a hidden io event, medium-gated to a SYNC: BOTH sides step on the SAME io
  hidSync : ∀ {X} {e : Net_Api Payload X} {a : X} (M₁ N₁ : NetProc)
          → ioES .mem (X , e) a
          → M ─[ ev (evl (evLabel X e a)) ]─► M₁
          → N ─[ ev (evl (evLabel X e a)) ]─► N₁
          → M″ ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
          → ReflOut M N M″

-- reflect ONE hidden-τ step of the full-stack skeleton `(M ∥⇘ ioES ⇙ N) ∖ ioES`
reflect-hidden-io :
    (M N : NetProc) {M″ : NetProc}
  → ((M ∥⇘ ioES ⇙ N) ∖ ioES) ─[ τ ]─► M″
  → ReflOut M N M″
reflect-hidden-io M N step with Hide-τ-elim ioES (M ∥⇘ ioES ⇙ N) step
... | hτP P′ innerStep eq = innerτ P′ innerStep eq
... | hτH P′ iomem ioStep eq with top-io-is-sync M N iomem ioStep
...   | M₁ , N₁ , sM , sN , refl = hidSync M₁ N₁ iomem sM sN eq

-- the four-node nodes bundle at a `SysState` (the RHS operand of `⟦_⟧`)
nodesOf : SysState → NetProc
nodesOf s = decNodeA (nA s) ⦀ (decNodeB (nB s) ⦀ (decNodeC (nC s) ⦀ decNodeD (nD s)))

-- REPRESENTATIVE REFLECTION ON THE REAL SYSTEM: every hidden-τ of the REAL
-- `⟦ s ⟧` reflects to either an inner `Par⊤ ioES` τ or a medium/nodes io-SYNC,
-- with NO `evBoth` on io.  `⟦ s ⟧` is DEFINITIONALLY
-- `(decMed (med s) ∥⇘ ioES ⇙ nodesOf s) ∖ ioES`, so `reflect-hidden-io`
-- applies at the real operands — the top-level seam crosses on the real system.
reflect-⟦⟧-τ :
    (s : SysState) {M″ : NetProc}
  → ⟦ s ⟧ ─[ τ ]─► M″
  → ReflOut (decMed (med s)) (nodesOf s) M″
reflect-⟦⟧-τ s step = reflect-hidden-io (decMed (med s)) (nodesOf s) step

------------------------------------------------------------------------
-- ITEM 1 (the adjudicator) — the inner-`⦀` `evBoth` overlap is REFUTABLE, so
-- route 2 dodges the M4 wall by DISJOINTNESS, not by a ⊓-match.
--
-- VERDICT: DISJOINTNESS HOLDS, at (event, VALUE) granularity.  The M4 route-1
-- blocker is right STATICALLY at the CHANNEL level — both the CS client and
-- the CS server fire `sendCS`/`receiveCS` (↦ `input`/`output`) on their own
-- (l,d), and `nodeA`'s server and `nodeB`'s client sit on the SAME (linkAB,hi),
-- so both statically offer the `input/output linkAB hi N2N_ChainSync` CHANNEL.
-- BUT the react OFFER MAP is value-indexed: the client at `ccAwait`/`ccMust`/
-- `ccInt` accepts only REPLY messages (`MsgCSRollForward/…`), the server at
-- `csIdle` accepts only REQUEST messages (`MsgCSRequestNext/…`) — DISJOINT
-- value sets (and dually for the `input` sends: requests vs replies).  So for
-- any SPECIFIC delivered io `(e, a)` the message constructor in `a` selects a
-- UNIQUE recipient peer; the two candidate nodes' offer maps do not both fire
-- on that exact `(e, a)`.  Hence the inner-`⦀` `evBoth` (which needs BOTH
-- operands to step on the SAME `(e,a)`) cannot arise: it is REFUTED by the
-- non-offer of whichever side is not the recipient.  (`evSync` is refuted
-- outright — `∅ES .mem = ⊥`.)  This is the mechanised justification that the
-- direct bisim never meets the M4 overlap; route 1's `cong-⦀` could not use it
-- because it quantified over ALL operand-state pairs, including the impossible
-- both-sending config, whereas here the value pins the recipient per step.
--
-- `inner-io-single` packages this: GIVEN the value-disjointness fact (one side
-- does not offer `(e,a)`), an inner-`⦀` io step is a SOLO step of the unique
-- recipient — never the `evBoth` overlap node.  It is fully symbolic (`Par-ev-
-- elim`), never forces WHNF.  The per-peer non-offer facts themselves (that the
-- non-recipient node's twelve renamed peers do not offer the delivered `(e,a)`)
-- are the residual OffersOnly obligation — see the report split (item 1b).
------------------------------------------------------------------------

-- `P` offers the io event `(e, a)` — a single visible step on it
IoOffers : NetProc → {X : Set 0ℓ} → Net_Api Payload X → X → Set₁
IoOffers P {X} e a = Σ[ M ∈ NetProc ] (P ─[ ev (evl (evLabel X e a)) ]─► M)

-- VALUE-disjointness ⇒ an inner-`⦀` io step is a solo step of one operand
-- (the `evBoth` overlap and the `∅ES`-`evSync` are both refuted)
inner-io-single :
    (A B : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → (¬ IoOffers A e a) ⊎ (¬ IoOffers B e a)
  → (A ⦀ B) ─[ ev (evl (evLabel X e a)) ]─► M
  → (Σ[ A₁ ∈ NetProc ] (A ─[ ev (evl (evLabel X e a)) ]─► A₁))
  ⊎ (Σ[ B₁ ∈ NetProc ] (B ─[ ev (evl (evLabel X e a)) ]─► B₁))
inner-io-single A B disj step with Par-ev-elim ∅ES merge⊤ A B step
... | evSync () _ _
... | evL  _ sA        = inj₁ (_ , sA)
... | evR  _ sB        = inj₂ (_ , sB)
... | evBoth _ sA sB with disj
...   | inj₁ ¬A = ⊥-elim (¬A (_ , sA))
...   | inj₂ ¬B = ⊥-elim (¬B (_ , sB))

------------------------------------------------------------------------
-- ITEM 1b (down payment) — value-level non-offer from the `nxt` tables.
--
-- `inner-io-single`'s hypotheses are `¬ IoOffers …` facts.  They bottom out in
-- per-peer non-offer lemmas: a peer at a given position does NOT offer a given
-- io `(e, a)`.  For the τ-free `tableSpec` peers these are DECIDED by the `nxt`
-- table (`csCnxt`/`csSnxt`/`bfCnxt`/`bfSnxt` — the value-indexed maps whose
-- request/reply split IS the item-1 disjointness): `force (tableSpec T q) =
-- tsNode T q (isFin T q)`, a τ-free react whose visible offer map is
-- `tMenu T q = tGo T ∘ nxt T q`; so if the table has NO edge at `(q, e, a)` the
-- peer cannot fire it.  `tableSpec-noOffer` is that inversion — fully symbolic
-- (matches the single possible `sVis`, no WHNF).  These are exactly the facts
-- the coordinator flagged as provable "directly from the react offer maps".
--
-- (The remaining 1b work: the per-position/per-peer INSTANCES for every
-- delivered io, and — for `inner-io-single` on the CONCRETE `decNodeX` — the
-- transport of these through `renameForce` to the renamed `miniProtocols`
-- peers + the node/bundle assembly.  See the report.)
------------------------------------------------------------------------

-- a `tableSpec` peer does NOT offer io `(e,a)` when its table has no edge there
-- (non-terminal position; the visible offer map is `nothing` at `(e,a)`)
tableSpec-noOffer : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → isFin T q ≡ false
  → nxt T q (X , e) a ≡ nothing
  → ¬ (tableSpec T q ─[ ev (evl (evLabel X e a)) ]─► M)
tableSpec-noOffer T q {X} {e} {a} finEq nxtEq (sVis fEq vEq)
  with isFin T q  | finEq
...  | .false      | refl with fEq
...     | refl with nxt T q (X , e) a | nxtEq
...        | .nothing            | refl with vEq
...           | ()

-- REPRESENTATIVE value-level non-offer (mechanises item-1's verdict at the
-- offer map): the CS-client spec at its head `ccIdle` offers the api requests
-- only — it does NOT accept ANY `output N2N_ChainSync` delivery (the server's
-- receive channel), for any link/dir/value.  `csCnxt … ccIdle (output …)`
-- falls to the catch-all `nothing`, and `csCfin ccIdle = false`, so both
-- premises of `tableSpec-noOffer` are `refl`.
csClient-ccIdle-no-output :
    (l : Link) (d : Dir) (l′ : Link) (d′ : Dir) {a : _} {M : NetProc}
  → ¬ (csClientSpec l d
        ─[ ev (evl (evLabel _ (output l′ d′ N2N_ChainSync) a)) ]─► M)
csClient-ccIdle-no-output l d l′ d′ =
  tableSpec-noOffer (record { isFin = csCfin ; nxt = csCnxt l d }) ccIdle refl refl

------------------------------------------------------------------------
-- The ABSTRACT-side decode `absDec : SysState → NetProc`.
--
-- `absDec` rebuilds `abstractSystem`'s exact skeleton, reusing the SHARED
-- medium decode `decMed` and the SHARED driver decodes (`decProd`/`decCP`/
-- `decConsD`), and replacing each concrete 12-peer bundle by its τ-free
-- 8-peer abstract counterpart (`specBundle`/`specBundleFlip` rebuilt at
-- arbitrary abstract positions via the position-indexed `tableSpec`).  The
-- inert KA/TS peers stay at their spec heads; the CS/BF peers are placed at
-- the abstract position obtained by COARSENING the concrete fine position.
--
-- The coarsening `coarsen…` collapses every concrete τ-only distinction (the
-- loop re-entry `…Sil st` positions map to the same abstract head as `…Head
-- st`, since the abstract side is τ-free) and sends each concrete stable/leaf
-- position to its abstract counterpart.  This encodes the INTENDED per-peer
-- correspondence; its bisimulation-soundness is exactly the per-peer `≈DR`
-- obligation that R2 Task 5 discharges (see the report — this is the coarse-
-- grained direction of the concrete-to-abstract map, VALIDATED by the step
-- lemmas, not assumed).
------------------------------------------------------------------------

-- CS FSM state → abstract CS-client head position
coarsenCScSt : CS.CSState → NS.CScPos
coarsenCScSt CS.stIdle      = ccIdle
coarsenCScSt CS.stCanAwait  = ccAwait
coarsenCScSt CS.stMustReply = ccMust
coarsenCScSt CS.stIntersect = ccInt
coarsenCScSt CS.stDone      = ccTerm

-- concrete CS-client fine position → abstract CS-client position
coarsenCSc : CScPos → NS.CScPos
coarsenCSc (csHead st)     = coarsenCScSt st
coarsenCSc csReqNext1      = ccWreq
coarsenCSc (csFindInt1 ps) = ccWfi ps
coarsenCSc csDone1         = ccWdone
coarsenCSc (csRF1 h t)     = ccArf (h , t)
coarsenCSc (csRB1 pt t)    = ccArb (pt , t)
coarsenCSc (csIF1 pt t)    = ccAif (pt , t)
coarsenCSc (csINF1 t)      = ccAin t
coarsenCSc (csSil st)      = coarsenCScSt st

-- CS FSM state → abstract CS-server head position
coarsenCSsSt : CS.CSState → NS.CSsPos
coarsenCSsSt CS.stIdle      = csIdle
coarsenCSsSt CS.stCanAwait  = csCanAwait
coarsenCSsSt CS.stMustReply = csMust
coarsenCSsSt CS.stIntersect = csInt
coarsenCSsSt CS.stDone      = csTerm

-- concrete CS-server fine position → abstract CS-server position
coarsenCSs : CSsPos → NS.CSsPos
coarsenCSs (ssHead st)     = coarsenCSsSt st
coarsenCSs ssReqNext1      = csAreq
coarsenCSs (ssFindInt1 ps) = csAfi ps
coarsenCSs ssDone1         = csDdone
coarsenCSs (ssRF1 h t)     = csWrf (h , t)
coarsenCSs (ssRB1 pt t)    = csWrb (pt , t)
coarsenCSs ssAw1           = csWar
coarsenCSs (ssIF1 pt t)    = csWif (pt , t)
coarsenCSs (ssINF1 t)      = csWin t
coarsenCSs (ssSil st)      = coarsenCSsSt st

-- BF FSM state → abstract BF-client head position
coarsenBFcSt : BF.BFState → NS.BFcPos
coarsenBFcSt BF.stIdle      = bcIdle
coarsenBFcSt BF.stBusy      = bcBusy
coarsenBFcSt BF.stStreaming = bcStream
coarsenBFcSt BF.stDone      = bcTerm

-- concrete BF-client fine position → abstract BF-client position
coarsenBFc : BFcPos → NS.BFcPos
coarsenBFc (bcHead st) = coarsenBFcSt st
coarsenBFc (bcReq1 r)  = bcWrr r
coarsenBFc bcDone1     = bcWcd
coarsenBFc (bcBlk1 b)  = bcAblk b
coarsenBFc (bcSil st)  = coarsenBFcSt st

-- BF FSM state → abstract BF-server head position
coarsenBFsSt : BF.BFState → NS.BFsPos
coarsenBFsSt BF.stIdle      = bsIdle
coarsenBFsSt BF.stBusy      = bsBusy
coarsenBFsSt BF.stStreaming = bsStream
coarsenBFsSt BF.stDone      = bsTerm

-- concrete BF-server fine position → abstract BF-server position
coarsenBFs : BFsPos → NS.BFsPos
coarsenBFs (bsHead st)   = coarsenBFsSt st
coarsenBFs (bsReq1 r)    = bsAreq r
coarsenBFs bsDone1       = bsDdone
coarsenBFs bsStart1      = bsWsb
coarsenBFs bsNoBlk1      = bsWnb
coarsenBFs (bsBlk1 b)    = bsWblk b
coarsenBFs bsBatchDone1  = bsWbd
coarsenBFs (bsSil st)    = coarsenBFsSt st

-- the four abstract driven peers, placed at the coarsened position via the
-- position-indexed `tableSpec` (head position ⇒ the closed `…Spec l d`)
absCSc : Link → Dir → CScPos → NetProc
absCSc l d q = tableSpec (record { isFin = csCfin ; nxt = csCnxt l d }) (coarsenCSc q)

absCSs : Link → Dir → CSsPos → NetProc
absCSs l d q = tableSpec (record { isFin = csSfin ; nxt = csSnxt l d }) (coarsenCSs q)

absBFc : Link → Dir → BFcPos → NetProc
absBFc l d q = tableSpec (record { isFin = bfCfin ; nxt = bfCnxt l d }) (coarsenBFc q)

absBFs : Link → Dir → BFsPos → NetProc
absBFs l d q = tableSpec (record { isFin = bfSfin ; nxt = bfSnxt l d }) (coarsenBFs q)

-- TS FSM state → abstract TS-client head position
coarsenTScSt : TS.TSState → NS.TScPos
coarsenTScSt TS.stInit             = tcInit
coarsenTScSt TS.stIdle             = tcIdle
coarsenTScSt TS.stTxIdsBlocking    = tcBlk
coarsenTScSt TS.stTxIdsNonBlocking = tcNbl
coarsenTScSt TS.stTxs              = tcTxs
coarsenTScSt TS.stDone             = tcTerm

-- concrete TS-client fine position → abstract TS-client position (head and its
-- loop re-entry sil coarsen to the SAME abstract head — coarsening-invariance)
coarsenTSc : TScPos → NS.TScPos
coarsenTSc (tcHead st) = coarsenTScSt st
coarsenTSc (tcReqIdsB1 a r)  = tcAri (Blocking , a , r)
coarsenTSc (tcReqIdsNB1 a r) = tcAri (NonBlocking , a , r)
coarsenTSc (tcReqTxs1 ids)   = tcArt ids
coarsenTSc (tcRepB1 ids)  = tcWri ids
coarsenTSc tcDone1        = tcWdone
coarsenTSc (tcRepNB1 ids) = tcWri ids
coarsenTSc (tcRepTxs1 txs) = tcWrt txs
coarsenTSc (tcSil st)  = coarsenTScSt st

-- TS FSM state → abstract TS-server head position
coarsenTSsSt : TS.TSState → NS.TSsPos
coarsenTSsSt TS.stInit             = tsInit
coarsenTSsSt TS.stIdle             = tsIdle
coarsenTSsSt TS.stTxIdsBlocking    = tsBlk
coarsenTSsSt TS.stTxIdsNonBlocking = tsNbl
coarsenTSsSt TS.stTxs              = tsTxs
coarsenTSsSt TS.stDone             = tsTerm

-- concrete TS-server fine position → abstract TS-server position
coarsenTSs : TSsPos → NS.TSsPos
coarsenTSs (tsHead st) = coarsenTSsSt st
coarsenTSs tsDone1     = tsDdone
coarsenTSs (tsReqB1 ar)  = tsWib ar
coarsenTSs (tsReqNB1 ar) = tsWin ar
coarsenTSs (tsReqTxs1 ids) = tsWrt ids
coarsenTSs (tsSil st)  = coarsenTSsSt st

-- the two abstract TS peers, placed at the coarsened position via `tableSpec`
-- (at `tcHead stInit`/`tsHead stInit` this is the closed `tsClientSpec`/
-- `tsServerSpec l d`, so `absDec-init` stays refl)
absTSc : Link → Dir → TScPos → NetProc
absTSc l d q = tableSpec (record { isFin = tsCfin ; nxt = tsCnxt l d }) (coarsenTSc q)

absTSs : Link → Dir → TSsPos → NetProc
absTSs l d q = tableSpec (record { isFin = tsSfin ; nxt = tsSnxt l d }) (coarsenTSs q)

-- concrete KA-client state → abstract KA-client position
coarsenKAcSt : KA.KAState → NS.KAcPos
coarsenKAcSt KA.stClient       = kcClient
coarsenKAcSt (KA.stServer c)   = kcAwait c
coarsenKAcSt KA.stDone         = kcTerm

-- concrete KA-client fine position → abstract KA-client position
coarsenKAc : KAcPos → NS.KAcPos
coarsenKAc (kcHead st) = coarsenKAcSt st
-- io-case error leaf: the errCookie-emitting state coarsens to the abstract kcErr position
coarsenKAc (kcErr1 cq cr ne) = kcErr cq cr
-- io-case send leaves: the wire-send states coarsen to the abstract wire-send positions
coarsenKAc (kcReq1 c)  = kcWmsg c
coarsenKAc kcDone1     = kcWdone
coarsenKAc (kcSil st)  = coarsenKAcSt st
coarsenKAc kcTermE1    = kcTermE

-- concrete KA-server state → abstract KA-server position
coarsenKAsSt : KA.KAState → NS.KAsPos
coarsenKAsSt KA.stClient       = ksClient
coarsenKAsSt (KA.stServer c)   = ksResp c
coarsenKAsSt KA.stDone         = ksTerm

-- concrete KA-server fine position → abstract KA-server position
coarsenKAs : KAsPos → NS.KAsPos
coarsenKAs (ksHead st)  = coarsenKAsSt st
coarsenKAs (ksRecv1 c)  = ksRecv c
coarsenKAs ksDdone1     = ksDdone
coarsenKAs (ksSil st)   = coarsenKAsSt st

-- the two abstract KA peers, placed at the coarsened position via `tableSpec`
-- (at `kcHead stClient`/`ksHead stClient` this is the closed `kaClientSpec`/
-- `kaServerSpec l d`, so `absDec-init` stays refl)
absKAc : Link → Dir → KAcPos → NetProc
absKAc l d q = tableSpec (record { isFin = kaCfin ; nxt = kaCnxt l d }) (coarsenKAc q)

absKAs : Link → Dir → KAsPos → NetProc
absKAs l d q = tableSpec (record { isFin = kaSfin ; nxt = kaSnxt l d }) (coarsenKAs q)

-- concrete LN-client state → abstract LN-client head position (term-injective:
-- only stDone ↦ the √ position lncTerm)
coarsenLNcSt : LN.LNState → NS.LNcPos
coarsenLNcSt LN.stIdle = lncIdle
coarsenLNcSt LN.stBusy = lncBusy
coarsenLNcSt LN.stDone = lncTerm

-- concrete LN-client fine position → abstract LN-client position (head and its
-- loop re-entry sil coarsen to the SAME abstract head — coarsening-invariance)
coarsenLNc : LNcPos → NS.LNcPos
coarsenLNc (lncHead st) = coarsenLNcSt st
coarsenLNc (lncRann1 h)  = lncRann h
coarsenLNc (lncRoff1 q)  = lncRoff q
coarsenLNc (lncRtxs1 q)  = lncRtxs q
coarsenLNc (lncRvot1 vs) = lncRvot vs
coarsenLNc lncReq1       = lncWreq
coarsenLNc lncDone1      = lncWdone
coarsenLNc (lncSil st)  = coarsenLNcSt st

-- concrete LN-server state → abstract LN-server head position
coarsenLNsSt : LN.LNState → NS.LNsPos
coarsenLNsSt LN.stIdle = lnsIdle
coarsenLNsSt LN.stBusy = lnsBusy
coarsenLNsSt LN.stDone = lnsTerm

-- concrete LN-server fine position → abstract LN-server position
coarsenLNs : LNsPos → NS.LNsPos
coarsenLNs (lnsHead st) = coarsenLNsSt st
coarsenLNs lnsDone1     = lnsDone
coarsenLNs (lnsWann1 h)  = lnsWann h
coarsenLNs (lnsWoff1 q)  = lnsWoff q
coarsenLNs (lnsWtxs1 q)  = lnsWtxs q
coarsenLNs (lnsWvot1 vs) = lnsWvot vs
coarsenLNs (lnsSil st)  = coarsenLNsSt st

-- the two abstract LN peers, placed at the coarsened position via `tableSpec`
-- (at `lncHead stIdle`/`lnsHead stIdle` this is the closed `lnClientSpec`/
-- `lnServerSpec l d`, so `absDec-init` stays refl once LN is symmetrized in)
absLNc : Link → Dir → LNcPos → NetProc
absLNc l d q = tableSpec (record { isFin = lnCfin ; nxt = lnCnxt l d }) (coarsenLNc q)

absLNs : Link → Dir → LNsPos → NetProc
absLNs l d q = tableSpec (record { isFin = lnSfin ; nxt = lnSnxt l d }) (coarsenLNs q)

-- concrete LF-client state → abstract LF-client head position (term-injective:
-- only stDone ↦ lfcTerm)
coarsenLFcSt : LF.LFState → NS.LFcPos
coarsenLFcSt LF.stIdle       = lfcIdle
coarsenLFcSt LF.stBlock      = lfcBlk
coarsenLFcSt LF.stBlockTxs   = lfcBtx
coarsenLFcSt LF.stVotes      = lfcVot
coarsenLFcSt LF.stBlockRange = lfcRng
coarsenLFcSt LF.stDone       = lfcTerm

-- concrete LF-client fine position → abstract LF-client position
coarsenLFc : LFcPos → NS.LFcPos
coarsenLFc (lfcHead st) = coarsenLFcSt st
coarsenLFc (lfcRblk1 b)     = lfcRblk b
coarsenLFc (lfcRbtx1 ts)    = lfcRbtx ts
coarsenLFc (lfcRvot1 vs)    = lfcRvot vs
coarsenLFc (lfcRnext1 b ts) = lfcRnextRng (b , ts)
coarsenLFc (lfcRlast1 b ts) = lfcRlastRng (b , ts)
coarsenLFc (lfcWblk1 pt)  = lfcWblk pt
coarsenLFc (lfcWtxs1 pb)  = lfcWtxs pb
coarsenLFc (lfcWvot1 vs)  = lfcWvot vs
coarsenLFc (lfcWrng1 r)   = lfcWrng r
coarsenLFc lfcDone1       = lfcWdone
coarsenLFc (lfcSil st)  = coarsenLFcSt st

-- concrete LF-server state → abstract LF-server head position
coarsenLFsSt : LF.LFState → NS.LFsPos
coarsenLFsSt LF.stIdle       = lfsIdle
coarsenLFsSt LF.stBlock      = lfsBlk
coarsenLFsSt LF.stBlockTxs   = lfsBtx
coarsenLFsSt LF.stVotes      = lfsVot
coarsenLFsSt LF.stBlockRange = lfsRng
coarsenLFsSt LF.stDone       = lfsTerm

-- concrete LF-server fine position → abstract LF-server position
coarsenLFs : LFsPos → NS.LFsPos
coarsenLFs (lfsHead st) = coarsenLFsSt st
coarsenLFs lfsDone1     = lfsDone
coarsenLFs (lfsWblk1 b)  = lfsWblk b
coarsenLFs (lfsWtxs1 ts) = lfsWtxs ts
coarsenLFs (lfsWvot1 vs) = lfsWvot vs
coarsenLFs (lfsWnext1 bt) = lfsWnext bt
coarsenLFs (lfsWlast1 bt) = lfsWlast bt
coarsenLFs (lfsSil st)  = coarsenLFsSt st

-- the two abstract LF peers, placed at the coarsened position via `tableSpec`
absLFc : Link → Dir → LFcPos → NetProc
absLFc l d q = tableSpec (record { isFin = lfCfin ; nxt = lfCnxt l d }) (coarsenLFc q)

absLFs : Link → Dir → LFsPos → NetProc
absLFs l d q = tableSpec (record { isFin = lfSfin ; nxt = lfSnxt l d }) (coarsenLFs q)

-- the abstract 8-peer bundle at (l, cl, sv): KA at head, CS/BF/TS at their
-- coarsened positions (mirrors `bundleG`; at all-idle positions this is
-- exactly `specBundle`/`specBundleFlip l`, since each `absX l d …Head =
-- the closed …Spec l d`)
absBundleG : (l : Link) (cl sv : Dir)
           → CScPos → CSsPos → BFcPos → BFsPos → InertPos → NetProc
absBundleG l cl sv qcc qcs qbc qbs ip =
  absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip)
    ⦀ (absCSc l cl qcc ⦀ (absCSs l sv qcs
    ⦀ (absBFc l cl qbc ⦀ (absBFs l sv qbs
    ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip)
    ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
    ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))

-- the four abstract nodes (SAME skeleton as `decNodeX`, abstract bundles +
-- shared drivers) — each equals `nodeXSpec` at the initial positions
absNodeA : NodeStateA → NetProc
absNodeA s =
  (absBundleG linkAB lo hi (csC-AB s) (csS-AB s) (bfC-AB s) (bfS-AB s) (inert-AB s)
   ⦀ absBundleG linkAC lo hi (csC-AC s) (csS-AC s) (bfC-AC s) (bfS-AC s) (inert-AC s))
    ∥⇘ apiES ⇙ (decProd linkAB hi blkA (prod-AB s) ⦀ decProd linkAC hi blkA (prod-AC s))

absNodeB : NodeStateB → NetProc
absNodeB s =
  (absBundleG linkAB hi lo (csC-AB s) (csS-AB s) (bfC-AB s) (bfS-AB s) (inert-AB s)
   ⦀ absBundleG linkBD lo hi (csC-BD s) (csS-BD s) (bfC-BD s) (bfS-BD s) (inert-BD s))
    ∥⇘ apiES ⇙ decCP linkAB linkBD (cp-B s)

absNodeC : NodeStateC → NetProc
absNodeC s =
  (absBundleG linkAC hi lo (csC-AC s) (csS-AC s) (bfC-AC s) (bfS-AC s) (inert-AC s)
   ⦀ absBundleG linkCD lo hi (csC-CD s) (csS-CD s) (bfC-CD s) (bfS-CD s) (inert-CD s))
    ∥⇘ apiES ⇙ decCP linkAC linkCD (cp-C s)

absNodeD : NodeStateD → NetProc
absNodeD s =
  (absBundleG linkBD hi lo (csC-BD s) (csS-BD s) (bfC-BD s) (bfS-BD s) (inert-BD s)
   ⦀ absBundleG linkCD hi lo (csC-CD s) (csS-CD s) (bfC-CD s) (bfS-CD s) (inert-CD s))
    ∥⇘ apiES ⇙ (decConsD linkBD (cons-BD s) ⦀ decConsD linkCD (cons-CD s))

-- the whole-system ABSTRACT decode: shared medium + shared drivers + abstract
-- bundles, in `abstractSystem`'s exact `(medium ∥⇘ ioES ⇙ nodes) ∖ ioES` shape
absDec : SysState → NetProc
absDec s =
  (decMed (med s)
    ∥⇘ ioES ⇙
    (absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))))
  ∖ ioES

-- GENUINE home-equality: at `initial` (all peers idle, drivers at phase 0,
-- medium all-empty) every abstract bundle reduces to `specBundle`/
-- `specBundleFlip` and every shared driver to `produce`/`consume`, so `absDec
-- initial` is definitionally `abstractSystem` — a `refl`, no WHNF forcing.
absDec-init : absDec initial ≡ abstractSystem
absDec-init = refl

------------------------------------------------------------------------
-- ITEM 1b-REST (the ¬IoOffers transport) — the renameForce per-peer
-- non-offer + the ⦀/∥⇘apiES⇙ assembly that feed `inner-io-single`.
--
-- The concrete driven peers are the REAL renamed FSMs `RenXX.renameMap
-- (…-src l d pos)` (SysNode R2 Task 2), NOT `tableSpec`.  So the value-
-- level non-offer of a concrete peer is TRANSPORTED, through the rename,
-- to a value-level non-offer of the SOURCE FSM at the ι-preimage:
--   · `RenNO.renameMap-noOffer` — if for EVERY source pre-image `e₁`
--     (with `ι⁻¹ e₂ ≡ just e₁`) the source peer does not offer `(e₁, a)`,
--     the renamed peer does not offer `(e₂, a)`.  Fully symbolic: it
--     inverts the renamed react offer map (`force-renM-react-inv`) then
--     the `invPreimg`/`rnCollect`/`rnFan` pipeline (`with ι⁻¹ e₂`), never
--     forcing the composite tree.  This is item-1's VALUE disjointness.
--   · `RenNO.renameMap-noOffer-χ` — the PROTOCOL-mismatch corollary:
--     `ι⁻¹ e₂ ≡ nothing` (a foreign-channel io) ⇒ no offer, with NO
--     source reasoning (position-independent).  This discharges the CS
--     peers on a BF io, the BF peers on a CS io, and all four inert
--     KA/TS/LN/LF peers on any CS/BF io.
------------------------------------------------------------------------

-- generic renameForce non-offer transport, parametrised over an alphabet
-- injection `ι : E₁ → Net_Api Payload` (instantiated at ιCS / ιBF / ιKA / …)
module RenNO {ℓe₁ : Level} {E₁ : Set 0ℓ → Set ℓe₁}
  (ι      : ∀ {A} → E₁ A → Net_Api Payload A)
  (ι⁻¹    : ∀ {A} → Net_Api Payload A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  where
  open import CSP.Rename {E₁ = E₁} {E₂ = Net_Api Payload} ι ι⁻¹ ι-linv
    using ( renameMap; ι-vis-inv; invRel; invPreimg; rnFan; rnCollect )
  -- the SOURCE-alphabet LTS (renamed to avoid clash with the Net_Api one)
  open import Semantics.LTS {E = E₁} {I = ExtI E₁}
    renaming ( _─[_]─►_ to _─[_]─►₁_; sVis to sVis₁; ev to ev₁; evl to evl₁
             ; evLabel to evLabel₁ )
    using ()

  -- force-inversion: `renameMap P` is a react ⇒ so is `P`, and the renamed
  -- offer map is the `rnFan`/`rnCollect`/`invPreimg` pipeline over `P`'s map
  force-renM-react-inv : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr}
      {v′ : (bt : AnyTypes (Net_Api Payload))
          → ContinueType bt (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr))}
      {τc′ : (i : AnyTypes (ExtI (Net_Api Payload)))
          → ContinueType i (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr))}
    → PTree.force (renameMap P) ≡ react v′ τc′
    → Σ[ vP ∈ ((at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))) ]
      Σ[ τcP ∈ ((i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr))) ]
        (PTree.force P ≡ react vP τcP
         × v′ ≡ (λ bt b → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
                                (rnCollect vP (invPreimg ι-vis-inv bt b))))
  force-renM-react-inv {P = P} eq with PTree.force P
  ... | react vP τcP = vP , τcP , refl , sym (proj₁ (react-injective eq))

  -- VALUE-level non-offer transport (item-1 disjointness through the rename):
  -- if the source peer offers no ι-preimage of `(e₂, a)`, the renamed peer
  -- offers no `(e₂, a)`
  renameMap-noOffer : {Rr : Set} {X : Set 0ℓ}
      (P : PTree E₁ (ExtI E₁) Rr) {e₂ : Net_Api Payload X} {a : X}
    → (∀ (e₁ : E₁ X) → ι⁻¹ e₂ ≡ just e₁
         → ¬ (Σ[ P₁ ∈ PTree E₁ (ExtI E₁) Rr ]
                (P ─[ ev₁ (evl₁ (evLabel₁ X e₁ a)) ]─►₁ P₁)))
    → ¬ (Σ[ M ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr ]
           (renameMap P ─[ ev (evl (evLabel X e₂ a)) ]─► M))
  renameMap-noOffer {X = X} P {e₂} {a} src-no (M , sVis eq vEq)
    with force-renM-react-inv {P = P} eq
  ... | vP , τcP , eqP , refl with ι⁻¹ e₂
  ...  | nothing = case-vEq vEq
    where case-vEq : nothing ≡ just M → ⊥
          case-vEq ()
  ...  | just e₁ with vP (X , e₁) a in vpe
  ...    | nothing = case-vEq vEq
    where case-vEq : nothing ≡ just M → ⊥
          case-vEq ()
  ...    | just P₁ = src-no e₁ refl (P₁ , sVis₁ eqP vpe)

  -- PROTOCOL-mismatch corollary: a foreign-channel io (`ι⁻¹ e₂ ≡ nothing`)
  -- is offered by no renamed peer, at ANY source state (position-independent)
  renameMap-noOffer-χ : {Rr : Set} {X : Set 0ℓ}
      (P : PTree E₁ (ExtI E₁) Rr) {e₂ : Net_Api Payload X} {a : X}
    → ι⁻¹ e₂ ≡ nothing
    → ¬ (Σ[ M ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr ]
           (renameMap P ─[ ev (evl (evLabel X e₂ a)) ]─► M))
  renameMap-noOffer-χ P {e₂} eqn =
    renameMap-noOffer P (λ e₁ ie → ⊥-elim (bad (trans (sym ie) eqn)))
    where bad : ∀ {A}{x : A} → just x ≡ nothing → ⊥
          bad ()

------------------------------------------------------------------------
-- The ⦀ / ∥⇘ apiES ⇙ assembly (top-level, Net_Api).  A `⦀` offers io only
-- if some operand does (`Par-ev-elim ∅ES` — no sync); through the io-gated
-- node stack the io comes solely from the peer bundle (io ∉ apiES; the
-- driver offers only apiCS/apiBF ∈ apiES).
------------------------------------------------------------------------

-- a `⦀` bundle does not offer io `(e,a)` when neither operand does
⦀-noOffer : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} (A B : NetProc)
  → ¬ IoOffers A e a → ¬ IoOffers B e a → ¬ IoOffers (A ⦀ B) e a
⦀-noOffer A B ¬A ¬B (M , step) with Par-ev-elim ∅ES merge⊤ A B step
... | evSync () _ _
... | evL  _ sA     = ¬A (_ , sA)
... | evR  _ sB     = ¬B (_ , sB)
... | evBoth _ sA _ = ¬A (_ , sA)

-- io ∉ apiES (input / output are not api channels)
io∉apiES-input  : {l : Link} {d : Dir} {id : IDs} {a : Payload}
                → ¬ (apiES .mem (Payload , input l d id) a)
io∉apiES-input ()
io∉apiES-output : {l : Link} {d : Dir} {id : IDs} {a : Payload}
                → ¬ (apiES .mem (Payload , output l d id) a)
io∉apiES-output ()

-- passthrough: a node `bundle ∥⇘ apiES ⇙ driver` offers io only via the
-- bundle (io ∉ apiES rules out the medium-style sync; the driver's io-offer
-- is refuted by `¬ IoOffers driver`)
∥⇘apiES⇙-noOffer : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    (bundle driver : NetProc)
  → ¬ (apiES .mem (X , e) a)
  → ¬ IoOffers bundle e a
  → ¬ IoOffers driver e a
  → ¬ IoOffers (bundle ∥⇘ apiES ⇙ driver) e a
∥⇘apiES⇙-noOffer bundle driver ¬mem ¬B ¬D (M , step)
  with Par-ev-elim apiES merge⊤ bundle driver step
... | evSync p _ _  = ¬mem p
... | evL  _ sB     = ¬B (_ , sB)
... | evR  _ sD     = ¬D (_ , sD)
... | evBoth _ sB _ = ¬B (_ , sB)

------------------------------------------------------------------------
-- INSTANCES for the representative io delivery (a producer's block-fetch
-- output `output l d N2N_BlockFetch`).  The two driven protocols are
-- instantiated; the concrete peers are the REAL renamed FSMs `decCSc`/…
-- `= RenXX.renameMap (…-src l d pos)`, so each per-peer non-offer is a
-- `RenNO` transport of a source-FSM fact (protocol channel or value).
------------------------------------------------------------------------

-- the renameForce transport specialised to the ChainSync / BlockFetch injections
module CSNO = RenNO ιCS ιCS⁻¹ ιCS-linv
module BFNO = RenNO ιBF ιBF⁻¹ ιBF-linv

-- PROTOCOL-mismatch per-peer non-offers (position-INDEPENDENT): the CS peers
-- never offer a BlockFetch-channel io (`ιCS⁻¹ (output _ _ N2N_BlockFetch) ≡
-- nothing`); dually the BF peers never offer a ChainSync-channel io.  This is
-- the item-1 disjointness at the CHANNEL granularity, mechanised on the REAL
-- renamed peers via `renameMap-noOffer-χ`.
decCSc-noOffer-BF : (l : Link) (d : Dir) (pos : CScPos) {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decCSc l d pos) (output l′ d′ N2N_BlockFetch) a
decCSc-noOffer-BF l d pos = CSNO.renameMap-noOffer-χ (decCSc-src l d pos) refl

decCSs-noOffer-BF : (l : Link) (d : Dir) (pos : CSsPos) {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decCSs l d pos) (output l′ d′ N2N_BlockFetch) a
decCSs-noOffer-BF l d pos = CSNO.renameMap-noOffer-χ (decCSs-src l d pos) refl

decBFc-noOffer-CS : (l : Link) (d : Dir) (pos : BFcPos) {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decBFc l d pos) (output l′ d′ N2N_ChainSync) a
decBFc-noOffer-CS l d pos = BFNO.renameMap-noOffer-χ (decBFc-src l d pos) refl

decBFs-noOffer-CS : (l : Link) (d : Dir) (pos : BFsPos) {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decBFs l d pos) (output l′ d′ N2N_ChainSync) a
decBFs-noOffer-CS l d pos = BFNO.renameMap-noOffer-χ (decBFs-src l d pos) refl

------------------------------------------------------------------------
-- VALUE-route non-offer (item-1 disjointness at the VALUE granularity, on
-- the REAL renamed FSM).  `output l d N2N_ChainSync = ιCS (receiveCS l d)`
-- IS a channel the CS server owns — but the server at its head `stIdle`
-- accepts only REQUEST deliveries; it does NOT offer a ROLLFORWARD (reply)
-- delivery, whatever the header/tip.  The offer is refuted by the source
-- react map (`serverStep l d stIdle` matches only `MsgCSRequestNext/…`, a
-- RollForward payload falls to its `nothing` catch-all) transported through
-- `renameMap-noOffer`.  This is the dual of `csClient-ccIdle-no-output`, but
-- on the CONCRETE renamed peer rather than the τ-free `tableSpec`.
decCSs-idle-no-reply : (l : Link) (d : Dir) (h : Header) (t : Tip) {M : NetProc}
  → ¬ IoOffers (decCSs l d (ssHead CS.stIdle))
        (output l d N2N_ChainSync)
        (time₀ , FromInitiator , length₀ , chainSync (MsgCSRollForward h t))
decCSs-idle-no-reply l d h t =
  CSNO.renameMap-noOffer (decCSs-src l d (ssHead CS.stIdle))
    (λ { e₁ refl (P₁ , CSLTS.sVis eq vEq) → refute eq vEq })
  where
    -- the source react map at `stIdle`/`receiveCS` gives `nothing` on a reply
    refute : ∀ {v τc M}
           → PTree.force (decCSs-src l d (ssHead CS.stIdle)) ≡ react v τc
           → v (Payload , CS.receiveCS l d)
                (time₀ , FromInitiator , length₀ , chainSync (MsgCSRollForward h t)) ≡ just M
           → ⊥
    refute eq vEq with react-injective eq
    ... | refl , _ with vEq
    ...   | ()

------------------------------------------------------------------------
-- ASSEMBLY DEMONSTRATION — compose the per-peer transported non-offers up a
-- `⦀` interleave (`Par-ev-elim ∅ES`, no sync).  The ChainSync client+server
-- PAIR of a bundle does not offer a BlockFetch-channel io: both reject by the
-- protocol-mismatch transport, combined through `⦀-noOffer`.  This is the
-- shape every step of the 12-peer bundle assembly takes (peel one operand,
-- discharge its per-peer non-offer, recurse) feeding `inner-io-single` at each
-- inner-`⦀` split.
------------------------------------------------------------------------

csPair-noOffer-BF : (l : Link) (cl sv : Dir) (pc : CScPos) (ps : CSsPos)
    {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decCSc l cl pc ⦀ decCSs l sv ps) (output l′ d′ N2N_BlockFetch) a
csPair-noOffer-BF l cl sv pc ps =
  ⦀-noOffer (decCSc l cl pc) (decCSs l sv ps)
            (decCSc-noOffer-BF l cl pc) (decCSs-noOffer-BF l sv ps)

-- and dually the BlockFetch client+server pair on a ChainSync-channel io
bfPair-noOffer-CS : (l : Link) (cl sv : Dir) (pc : BFcPos) (ps : BFsPos)
    {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decBFc l cl pc ⦀ decBFs l sv ps) (output l′ d′ N2N_ChainSync) a
bfPair-noOffer-CS l cl sv pc ps =
  ⦀-noOffer (decBFc l cl pc) (decBFs l sv ps)
            (decBFc-noOffer-CS l cl pc) (decBFs-noOffer-CS l sv ps)

------------------------------------------------------------------------
-- R2 TASK 4 ITEM 2 — `refl-τ` (forward-τ step of the ≈DR bisim R = {(⟦ s ⟧,
-- absDec s)}).  Given a concrete internal τ `⟦ s ⟧ ─[τ]─► M″`, reflect it to a
-- target `s′ : SysState` with `M″ ≡ ⟦ s′ ⟧` AND an ABSTRACT weak-τ match
-- `absDec s ─[τ*]─► absDec s′` (ZERO-or-more τ).  The output record `ReflτOut`
-- packages exactly what the DRbisim `.fwd .on-tau` field consumes: recall
-- `absDec s ═[ τ ]═► absDec s′` unfolds to `wτ (absDec s ─[τ*]─► absDec s′)`
-- (Semantics.WeakBisim), and the residual relation entry is `(⟦ s′ ⟧, absDec s′)
-- ∈ R` witnessed by `tgt≡`.
--
-- STOP-RULE STATUS (see the R2 Task 4c report): this file delivers the SKELETON
--   · the ABSTRACT weak-τ target type `ReflτOut` (the `─[τ*]─► absDec s′` field);
--   · the TOP case-split — `reflect-⟦⟧-τ` (already above) ↝ `reflect-inner-τ`
--     (medium vs nodes, via `Par-τ-elim ioES`) ↝ `reflect-nodes-τ` (the four
--     nodes, via nested `Par-τ-elim ∅ES`) ↝ `reflect-nodeA-τ` (bundles vs
--     drivers, via `Par-τ-elim apiES`), all TOTAL and reusable;
--   · each τ flavor proven for a REPRESENTATIVE case.
-- The remaining per-peer/per-position enumeration + the peer-step LIFT up the
-- `⦀`/`∥⇘`/`∖` stack (to seal each branch into a `ReflτOut`) is the bounded
-- follow-up itemised in the report.
------------------------------------------------------------------------

-- THE ABSTRACT WEAK-τ TARGET TYPE: reflect a concrete internal τ of `⟦ s ⟧` to a
-- `SysState` move whose decode is the τ-target, matched on the abstract side by
-- a ZERO-or-more-τ run `absDec s ─[τ*]─► absDec s′`.
record ReflτOut (s : SysState) (M″ : NetProc) : Set₁ where
  constructor mkReflτ
  field
    tgt    : SysState                        -- the reflected target state s′
    tgt≡   : M″ ≡ ⟦ tgt ⟧                     -- concrete: M″ is s′'s decode
    absRun : absDec s ─[τ*]─► absDec tgt      -- abstract: matches by ZERO-or-more τ

------------------------------------------------------------------------
-- TOP CASE-SPLIT (structural, TOTAL) — invert the inner `Par⊤ ioES` τ.
------------------------------------------------------------------------

-- inner-τ inversion outcome (GENERIC over the operands `M`/`N`, mirroring
-- `top-io-is-sync`/`reflect-hidden-io` — so `Par-τ-elim ioES` forces only
-- variables, NEVER the concrete `decMed`/`nodesOf` composite to WHNF;
-- instantiate at `decMed (med s)`/`nodesOf s` by APPLICATION at the call site).
-- The inner `M ∥⇘ ioES ⇙ N` τ is either `M`'s τ (the MEDIUM, flavor 2, shared
-- verbatim) or `N`'s τ (the NODES; flavor 1 peer sil, recurse).
data InnerτR (M N : NetProc) (P′ : NetProc) : Set₁ where
  medτ   : (M′ : NetProc) → M ─[ τ ]─► M′ → P′ ≡ (M′ ∥⇘ ioES ⇙ N) → InnerτR M N P′
  nodesτ : (N′ : NetProc) → N ─[ τ ]─► N′ → P′ ≡ (M ∥⇘ ioES ⇙ N′) → InnerτR M N P′

-- reflect ONE inner `∥⇘ ioES ⇙` τ into the medium-vs-nodes split (TOTAL,
-- symbolic via `Par-τ-elim ioES`; τ never syncs, so no `evBoth`/io case here)
reflect-inner-τ : (M N : NetProc) {P′ : NetProc}
  → (M ∥⇘ ioES ⇙ N) ─[ τ ]─► P′ → InnerτR M N P′
reflect-inner-τ M N step with Par-τ-elim ioES merge⊤ M N step
... | τL M′ ms eq = medτ   M′ ms eq
... | τR N′ ns eq = nodesτ N′ ns eq

-- which of the four node operands carried the `A ⦀ (B ⦀ (C ⦀ D))` τ (GENERIC
-- over `A B C D`, matching `nodesOf`/`⟦_⟧`'s association; instantiate at the
-- four `decNodeX (nX s)` by application, so no concrete-node WHNF)
data NodesτR (A B C D : NetProc) (Nd′ : NetProc) : Set₁ where
  nAτ : (A′ : NetProc) → A ─[ τ ]─► A′ → Nd′ ≡ (A′ ⦀ (B ⦀ (C ⦀ D))) → NodesτR A B C D Nd′
  nBτ : (B′ : NetProc) → B ─[ τ ]─► B′ → Nd′ ≡ (A ⦀ (B′ ⦀ (C ⦀ D))) → NodesτR A B C D Nd′
  nCτ : (C′ : NetProc) → C ─[ τ ]─► C′ → Nd′ ≡ (A ⦀ (B ⦀ (C′ ⦀ D))) → NodesτR A B C D Nd′
  nDτ : (D′ : NetProc) → D ─[ τ ]─► D′ → Nd′ ≡ (A ⦀ (B ⦀ (C ⦀ D′))) → NodesτR A B C D Nd′

-- reflect ONE four-node `⦀` τ into the node split (TOTAL; three nested
-- `Par-τ-elim ∅ES`, no sync since `⦀` has empty sync alphabet; generic operands)
reflect-nodes-τ : (A B C D : NetProc) {Nd′ : NetProc}
  → (A ⦀ (B ⦀ (C ⦀ D))) ─[ τ ]─► Nd′ → NodesτR A B C D Nd′
reflect-nodes-τ A B C D step with Par-τ-elim ∅ES merge⊤ A (B ⦀ (C ⦀ D)) step
... | τL A′ as eq = nAτ A′ as eq
... | τR R′ rs eqR with Par-τ-elim ∅ES merge⊤ B (C ⦀ D) rs
...   | τL B′ bs eqB = nBτ B′ bs (trans eqR (cong (A ⦀_) eqB))
...   | τR R2 r2s eqR2 with Par-τ-elim ∅ES merge⊤ C D r2s
...     | τL C′ cs eqC = nCτ C′ cs (trans eqR (cong (A ⦀_) (trans eqR2 (cong (B ⦀_) eqC))))
...     | τR D′ ds eqD = nDτ D′ ds (trans eqR (cong (A ⦀_) (trans eqR2 (cong (B ⦀_) eqD))))

-- per-node split (GENERIC over the node's `bundle`/`driver` operands, mirroring
-- `top-io-is-sync`/`inner-io-single` — so `Par-τ-elim apiES` forces only the
-- ABSTRACT operand variables to WHNF, NOT a concrete 12-peer bundle; instantiate
-- at the real `decNodeX` operands at the call site).  A node τ is a BUNDLE τ (a
-- peer sil, flavor 1) or a DRIVER τ (flavor 2 — but `produce`/`consume` are
-- τ-free prefix chains, see the flavor-2 finding, so the driver branch carries
-- no actual reduction).  τ never syncs at `∥⇘ apiES ⇙`.
data NodeτR (bundle driver : NetProc) (A′ : NetProc) : Set₁ where
  bundleτ : (Bd′ : NetProc) → bundle ─[ τ ]─► Bd′
          → A′ ≡ (Bd′ ∥⇘ apiES ⇙ driver) → NodeτR bundle driver A′
  driverτ : (Dr′ : NetProc) → driver ─[ τ ]─► Dr′
          → A′ ≡ (bundle ∥⇘ apiES ⇙ Dr′) → NodeτR bundle driver A′

-- reflect ONE `bundle ∥⇘ apiES ⇙ driver` τ into the bundle-vs-driver split
-- (TOTAL, symbolic; generic operands ⇒ no concrete-bundle WHNF)
reflect-node-τ : (bundle driver : NetProc) {A′ : NetProc}
  → (bundle ∥⇘ apiES ⇙ driver) ─[ τ ]─► A′ → NodeτR bundle driver A′
reflect-node-τ bundle driver step
  with Par-τ-elim apiES merge⊤ bundle driver step
... | τL Bd′ bs eq = bundleτ Bd′ bs eq
... | τR Dr′ ds eq = driverτ Dr′ ds eq

------------------------------------------------------------------------
-- FLAVOR 1 (peer-internal sil) — the concrete peer τ + the abstract collapse.
--
-- The ONLY peer-internal τ is a loop RE-ENTRY sil `…Sil st → …Head st`: the
-- source `iter-bind (Ret (inj₁ st)) step` forces to `sil (iter step st)`
-- (Operators.iter-bind: `ret (inj₁ a′) ↦ sil (iter k a′)`) and `renameMap`
-- preserves `sil` (Rename: `sil P′ ↦ sil (renameMap P′)`), so the renamed peer
-- forces to `sil (decX l d (…Head st))`.  Each step is `sSil refl` — one LOCAL
-- force layer (the renamed peer), NOT the composite whole-system tree.
------------------------------------------------------------------------

-- CS-client loop re-entry sil → loop head (concrete peer τ)
decCSc-sil-step : (l : Link) (d : Dir) (st : CS.CSState)
  → decCSc l d (csSil st) ─[ τ ]─► decCSc l d (csHead st)
decCSc-sil-step l d st = sSil refl

-- CS-server loop re-entry sil → loop head (concrete peer τ)
decCSs-sil-step : (l : Link) (d : Dir) (st : CS.CSState)
  → decCSs l d (ssSil st) ─[ τ ]─► decCSs l d (ssHead st)
decCSs-sil-step l d st = sSil refl

-- BF-client loop re-entry sil → loop head (concrete peer τ)
decBFc-sil-step : (l : Link) (d : Dir) (st : BF.BFState)
  → decBFc l d (bcSil st) ─[ τ ]─► decBFc l d (bcHead st)
decBFc-sil-step l d st = sSil refl

-- BF-server loop re-entry sil → loop head (concrete peer τ)
decBFs-sil-step : (l : Link) (d : Dir) (st : BF.BFState)
  → decBFs l d (bsSil st) ─[ τ ]─► decBFs l d (bsHead st)
decBFs-sil-step l d st = sSil refl

-- ABSTRACT COLLAPSE (the relation-design soundness of the coarsening): the
-- τ-free abstract peer decode is DEFINITIONALLY IDENTICAL at `…Sil st` and
-- `…Head st` — both `coarsen… (…Sil st)` and `coarsen… (…Head st)` land on the
-- same abstract head `coarsen…St st` (see the `coarsenCSc (csSil st) =
-- coarsenCScSt st` clause), so `tableSpec` is applied at the same position.
-- Hence a peer sil is matched by ZERO abstract τ.  Confirmed `refl` (unfolds
-- only `absX`/`coarsen…`, never the composite tree).
absCSc-sil-collapse : (l : Link) (d : Dir) (st : CS.CSState)
  → absCSc l d (csSil st) ≡ absCSc l d (csHead st)
absCSc-sil-collapse l d st = refl

absCSs-sil-collapse : (l : Link) (d : Dir) (st : CS.CSState)
  → absCSs l d (ssSil st) ≡ absCSs l d (ssHead st)
absCSs-sil-collapse l d st = refl

absBFc-sil-collapse : (l : Link) (d : Dir) (st : BF.BFState)
  → absBFc l d (bcSil st) ≡ absBFc l d (bcHead st)
absBFc-sil-collapse l d st = refl

absBFs-sil-collapse : (l : Link) (d : Dir) (st : BF.BFState)
  → absBFs l d (bsSil st) ≡ absBFs l d (bsHead st)
absBFs-sil-collapse l d st = refl

-- FLAVOR 1 whole-system collapse (REPRESENTATIVE — node A, link AB, CS client).
-- The `SysState` move advancing `csC-AB` from `csSil st` to `csHead st` leaves
-- `absDec` UNCHANGED (the abstract decode is τ-free — coarsening absorbs the
-- sil).  Proven by `cong`-GLUE over the fixed operator skeleton (exactly the
-- `dec-init` pattern): the cheap peer-level `absCSc-sil-collapse` is plugged
-- into the 8-peer bundle ⦀ context, then the node ∥⇘ context, then the
-- whole-system `∥⇘ ioES ⇙`/`∖ ioES` context.  `cong` NEVER forces the plugged
-- operands (`kaClientSpec …`, `decMed m`, `absNodeB nb`, …) to WHNF, so the
-- typecheck stays fast — no composite-tree normalization.

-- lift the CS-client collapse to node A's link-AB 8-peer abstract bundle
absBundleAB-csC-collapse : (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos) (st : CS.CSState)
  → absBundleG linkAB lo hi (csSil  st) css bfc bfs ip
  ≡ absBundleG linkAB lo hi (csHead st) css bfc bfs ip
absBundleAB-csC-collapse css bfc bfs ip st =
  cong (λ c → absKAc linkAB lo (kac ip) ⦀ (absKAs linkAB hi (kas ip)
              ⦀ (c ⦀ (absCSs linkAB hi css ⦀ (absBFc linkAB lo bfc
              ⦀ (absBFs linkAB hi bfs ⦀ (absTSc linkAB lo (tsc ip) ⦀ (absTSs linkAB hi (tss ip)
              ⦀ (absLNc linkAB lo (lnc ip) ⦀ (absLNs linkAB hi (lns ip)
              ⦀ (absLFc linkAB lo (lfc ip) ⦀ absLFs linkAB hi (lfs ip))))))))))))
       (absCSc-sil-collapse linkAB lo st)

-- lift it to `absNodeA`
absNodeA-csC-AB-collapse :
    (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (pp : ProdPh)
    (csc′ : CScPos) (css′ : CSsPos) (bfc′ : BFcPos) (bfs′ : BFsPos) (ppac : ProdPh)
    (ip ipac : InertPos) (st : CS.CSState)
  → absNodeA (mkNodeA (csSil  st) css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac)
  ≡ absNodeA (mkNodeA (csHead st) css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac)
absNodeA-csC-AB-collapse css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac st =
  cong (λ bAB → (bAB ⦀ absBundleG linkAC lo hi csc′ css′ bfc′ bfs′ ipac)
                ∥⇘ apiES ⇙ (decProd linkAB hi blkA pp ⦀ decProd linkAC hi blkA ppac))
       (absBundleAB-csC-collapse css bfc bfs ip st)

-- the whole-system collapse (cheap `cong`-glue — the definitive whole-system
-- witness that the coarsening genuinely collapses peer-sil s/s′)
absDec-csC-AB-sil-collapse :
    (m : MedState) (nb : NodeStateB) (nc : NodeStateC) (nd : NodeStateD)
    (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (pp : ProdPh)
    (csc′ : CScPos) (css′ : CSsPos) (bfc′ : BFcPos) (bfs′ : BFsPos) (ppac : ProdPh)
    (ip ipac : InertPos) (st : CS.CSState)
  → absDec (mkSys m (mkNodeA (csSil  st) css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac) nb nc nd)
  ≡ absDec (mkSys m (mkNodeA (csHead st) css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac) nb nc nd)
absDec-csC-AB-sil-collapse m nb nc nd css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac st =
  cong (λ nA′ → (decMed m ∥⇘ ioES ⇙ (nA′ ⦀ (absNodeB nb ⦀ (absNodeC nc ⦀ absNodeD nd)))) ∖ ioES)
       (absNodeA-csC-AB-collapse css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac st)

-- the matching abstract weak-τ run for the representative move: ZERO τ,
-- transported along the (cheap) collapse equality with `subst` (avoiding the
-- expensive definitional recheck a bare `τ*-refl` would trigger).  This is the
-- `absRun` field a sealed flavor-1 `ReflτOut` supplies once the concrete
-- peer-sil LIFT up the ⦀/∥⇘/∖ stack is available (bounded follow-up).
absRun-csC-AB-sil :
    (m : MedState) (nb : NodeStateB) (nc : NodeStateC) (nd : NodeStateD)
    (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (pp : ProdPh)
    (csc′ : CScPos) (css′ : CSsPos) (bfc′ : BFcPos) (bfs′ : BFsPos) (ppac : ProdPh)
    (ip ipac : InertPos) (st : CS.CSState)
  → absDec (mkSys m (mkNodeA (csSil  st) css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac) nb nc nd)
    ─[τ*]─►
    absDec (mkSys m (mkNodeA (csHead st) css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac) nb nc nd)
absRun-csC-AB-sil m nb nc nd css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac st =
  subst (λ t → absDec (mkSys m (mkNodeA (csSil st) css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac) nb nc nd)
               ─[τ*]─► t)
        (absDec-csC-AB-sil-collapse m nb nc nd css bfc bfs pp csc′ css′ bfc′ bfs′ ppac ip ipac st)
        τ*-refl

------------------------------------------------------------------------
-- FLAVOR 2 (shared-component τ) — FINDING (drivers τ-free; medium sils EXIST;
-- a SysMedium `MedState` gap surfaces).
--
-- DRIVERS τ-FREE: `produce`/`consume` are straight api PREFIX chains ending in
-- `Skip`/`Ret`, and `>>=`/`>>` collapse a `ret` boundary WITHOUT a sil
-- (Operators.agda:338 `force (P >>= k)` on `ret r ↦ PTree.force (k r)`, NOT `sil
-- (k r)`).  So the relay switch `consume … >>= produce …` and the consumer
-- `consume … >> Skip` fire their last api event VISIBLY, landing directly on the
-- produce leg — no bind-τ.
--
-- MEDIUM SILS EXIST (NOT empty): each copy cell `Copy l d id = loop0 (pchoice
-- (copyMenu l d id))` loops via `iter`, so after every `output l d id` delivery
-- it re-enters through a `sil`.  Traced through the definitions: `decCopy l d id
-- (full x)` offers `output` and its output-successor is `iter-bind (Skip >>= (λ
-- a′ → Ret (inj₁ a′))) step`, whose force is `sil (Copy l d id)` (`Skip = Ret
-- tt`, so `Skip >>= g ↦ ret (inj₁ tt)`, and `iter-bind` maps `ret (inj₁ tt) ↦
-- sil (iter step tt) = sil (Copy l d id)`).  This is the SAME `iter`-loop-back
-- `sil` mechanism already mechanised for the peer sils (`decCSc-sil-step`).
--
-- >>> GAP (relation-design, SysMedium / R2 Task 1): the current `MedState`
-- (`empty | full x`) does NOT represent this post-`output` transient.  Both
-- `decCopy … empty = Copy` and `decCopy … (full x)` decode to REACT nodes, so no
-- `MedState` cell has decode `sil (Copy l d id)`.  Consequently BOTH (a) the
-- flavor-2 loop-back `sil (Copy) ─[τ]─► Copy` AND (b) the flavor-3 HIDDEN
-- `output`-delivery (which lands the cell ON `sil (Copy)`) cannot produce a
-- clean `s′` with `M ≡ ⟦ s′ ⟧`.  FIX: SysMedium adds a third cell phase (e.g.
-- `draining` ↦ the loop-back-sil node); THEN flavor 2 closes cleanly — the sil
-- is a SHARED-medium τ, matched by the IDENTICAL abstract sil (verbatim `decMed`
-- reuse), lifted by `lift-med-whole-τ` below.  This is a Task-1 enrichment, not
-- a fundamental obstruction.
------------------------------------------------------------------------

-- verbatim medium reuse (valid once the post-`output` phase exists): a medium τ
-- landing on `decMed m′` reflects to `mkSys m′ (nA s) …`; the abstract side does
-- the IDENTICAL step (`decMed` shared), lifted by `lift-med-whole-τ`.
medium-shared-step-target : (s : SysState) (m′ : MedState)
  → decMed (med s) ─[ τ ]─► decMed m′
  → SysState
medium-shared-step-target s m′ _ = mkSys m′ (nA s) (nB s) (nC s) (nD s)

------------------------------------------------------------------------
-- FLAVOR 3 (hidden io-sync) — the `hidSync` case of `reflect-⟦⟧-τ`.
--
-- `hidSync M₁ N₁ iomem sM sN eq` gives a hidden io delivered by BOTH the medium
-- (`sM : decMed (med s) ─[ev io]─► M₁`) and the nodes (`sN : nodesOf s ─[ev io]─►
-- N₁`).  The nodes step is pinned to a UNIQUE recipient peer by value-
-- disjointness: peel `nodesOf` with `inner-io-single` (× the node/bundle ⦀
-- nesting), discharging every non-recipient operand with the item-1b transports
-- (`decCSc-noOffer-BF`/`decBFc-noOffer-CS`/… for protocol mismatch,
-- `decCSs-idle-no-reply`/`csClient-ccIdle-no-output` for the value route),
-- ruling out `evBoth`.  The abstract side offers the SAME io at the coarsened
-- recipient position, so `absDec s ─[τ]─► absDec s′`.  This is where item-1b's
-- finite instance enumeration is consumed.  The full per-io recipient pin +
-- the abstract-offer match is the bounded follow-up (report); the building
-- blocks (`inner-io-single`, `⦀-noOffer`, `∥⇘apiES⇙-noOffer`, the transports)
-- are all in place above.
--
-- Representative recipient-pin skeleton: at a bundle `⦀` split on a BlockFetch
-- io, the CS client+server PAIR is NOT the recipient (`csPair-noOffer-BF`), so
-- `inner-io-single` routes the step to the other operand — the shape every
-- io-delivery recipient pin takes.
reflect-io-pin-BF :
    (l : Link) (cl sv : Dir) (pc : CScPos) (ps : CSsPos) (B : NetProc)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → ((decCSc l cl pc ⦀ decCSs l sv ps) ⦀ B)
      ─[ ev (evl (evLabel _ (output l′ d′ N2N_BlockFetch) a)) ]─► M
  → (Σ[ X₁ ∈ NetProc ]
       ((decCSc l cl pc ⦀ decCSs l sv ps)
          ─[ ev (evl (evLabel _ (output l′ d′ N2N_BlockFetch) a)) ]─► X₁))
  ⊎ (Σ[ B₁ ∈ NetProc ]
       (B ─[ ev (evl (evLabel _ (output l′ d′ N2N_BlockFetch) a)) ]─► B₁))
reflect-io-pin-BF l cl sv pc ps B step =
  inner-io-single (decCSc l cl pc ⦀ decCSs l sv ps) B
    (inj₁ (csPair-noOffer-BF l cl sv pc ps)) step

------------------------------------------------------------------------
-- LIFT 1 (peer-sil) — GENERIC τ-INTRO up the `⦀` / `∥⇘ apiES ⇙` / `∥⇘ ioES ⇙`
-- / `∖ ioES` stack, all operand-generic (siblings/medium/drivers are VARIABLES,
-- so no concrete peer/node is forced to WHNF).  The wrappers are `Par-τ-L`/
-- `Par-τ-R`/`Hide-τ` at the whole-system alphabet; composing them lifts a peer
-- `sSil` to a whole-`⟦⟧`-shape τ.  The concrete dispatcher (Task 5) instantiates
-- the operands at `decMed`/`decNodeX`/`bundleA`/`decProd` BY APPLICATION (opaque
-- ⇒ no WHNF); the abstract side matches by ZERO τ via the confirmed collapse.
------------------------------------------------------------------------

-- τ-intro through interleave `⦀` (left / right operand steps)
⦀-τ-L : (P Q : NetProc) {P′ : NetProc} → P ─[ τ ]─► P′ → (P ⦀ Q) ─[ τ ]─► (P′ ⦀ Q)
⦀-τ-L P Q = Par-τ-L ∅ES merge⊤ P Q
⦀-τ-R : (P Q : NetProc) {Q′ : NetProc} → Q ─[ τ ]─► Q′ → (P ⦀ Q) ─[ τ ]─► (P ⦀ Q′)
⦀-τ-R P Q = Par-τ-R ∅ES merge⊤ P Q

-- τ-intro through the sync-gated stack `∥⇘ A ⇙` (left / right operand steps)
∥⇘⇙-τ-L : (A : EventSet) (P Q : NetProc) {P′ : NetProc}
        → P ─[ τ ]─► P′ → (P ∥⇘ A ⇙ Q) ─[ τ ]─► (P′ ∥⇘ A ⇙ Q)
∥⇘⇙-τ-L A P Q = Par-τ-L A merge⊤ P Q
∥⇘⇙-τ-R : (A : EventSet) (P Q : NetProc) {Q′ : NetProc}
        → Q ─[ τ ]─► Q′ → (P ∥⇘ A ⇙ Q) ─[ τ ]─► (P ∥⇘ A ⇙ Q′)
∥⇘⇙-τ-R A P Q = Par-τ-R A merge⊤ P Q

-- τ-intro through hide `∖ A`
∖-τ : (A : EventSet) (P : NetProc) {P′ : NetProc}
    → P ─[ τ ]─► P′ → (P ∖ A) ─[ τ ]─► (P′ ∖ A)
∖-τ A P = Hide-τ A P

-- PER-PEER-KIND bundle lifts (the four driven peers' fixed positions in the
-- 12-peer `KAc ⦀ (KAs ⦀ (CSc ⦀ (CSs ⦀ (BFc ⦀ (BFs ⦀ rest)))))` interleave; all
-- siblings generic).  CS client = position 3 (R,R,L into the chain).
lift-CSc-bundle-τ : (kac kas csc rest : NetProc) {csc′ : NetProc}
    → csc ─[ τ ]─► csc′
    → (kac ⦀ (kas ⦀ (csc ⦀ rest))) ─[ τ ]─► (kac ⦀ (kas ⦀ (csc′ ⦀ rest)))
lift-CSc-bundle-τ kac kas csc rest step =
  ⦀-τ-R kac (kas ⦀ (csc ⦀ rest)) (⦀-τ-R kas (csc ⦀ rest) (⦀-τ-L csc rest step))

-- CS server = position 4 (R,R,R,L)
lift-CSs-bundle-τ : (kac kas csc css rest : NetProc) {css′ : NetProc}
    → css ─[ τ ]─► css′
    → (kac ⦀ (kas ⦀ (csc ⦀ (css ⦀ rest)))) ─[ τ ]─► (kac ⦀ (kas ⦀ (csc ⦀ (css′ ⦀ rest))))
lift-CSs-bundle-τ kac kas csc css rest step =
  ⦀-τ-R kac _ (⦀-τ-R kas _ (⦀-τ-R csc (css ⦀ rest) (⦀-τ-L css rest step)))

-- BF client = position 5 (R,R,R,R,L)
lift-BFc-bundle-τ : (kac kas csc css bfc rest : NetProc) {bfc′ : NetProc}
    → bfc ─[ τ ]─► bfc′
    → (kac ⦀ (kas ⦀ (csc ⦀ (css ⦀ (bfc ⦀ rest)))))
      ─[ τ ]─► (kac ⦀ (kas ⦀ (csc ⦀ (css ⦀ (bfc′ ⦀ rest)))))
lift-BFc-bundle-τ kac kas csc css bfc rest step =
  ⦀-τ-R kac _ (⦀-τ-R kas _ (⦀-τ-R csc _ (⦀-τ-R css (bfc ⦀ rest) (⦀-τ-L bfc rest step))))

-- BF server = position 6 (R,R,R,R,R,L)
lift-BFs-bundle-τ : (kac kas csc css bfc bfs rest : NetProc) {bfs′ : NetProc}
    → bfs ─[ τ ]─► bfs′
    → (kac ⦀ (kas ⦀ (csc ⦀ (css ⦀ (bfc ⦀ (bfs ⦀ rest))))))
      ─[ τ ]─► (kac ⦀ (kas ⦀ (csc ⦀ (css ⦀ (bfc ⦀ (bfs′ ⦀ rest))))))
lift-BFs-bundle-τ kac kas csc css bfc bfs rest step =
  ⦀-τ-R kac _ (⦀-τ-R kas _ (⦀-τ-R csc _ (⦀-τ-R css _ (⦀-τ-R bfc (bfs ⦀ rest) (⦀-τ-L bfs rest step)))))

-- lift a node's link-1 bundle τ to the node τ (two-bundle ⦀ then `∥⇘ apiES ⇙`
-- driver; the sibling bundle + driver generic)
lift-bundle1-node-τ : (bd1 bd2 driver : NetProc) {bd1′ : NetProc}
    → bd1 ─[ τ ]─► bd1′
    → ((bd1 ⦀ bd2) ∥⇘ apiES ⇙ driver) ─[ τ ]─► ((bd1′ ⦀ bd2) ∥⇘ apiES ⇙ driver)
lift-bundle1-node-τ bd1 bd2 driver step =
  ∥⇘⇙-τ-L apiES (bd1 ⦀ bd2) driver (⦀-τ-L bd1 bd2 step)

-- lift the FIRST node's τ to the whole four-node `⦀` bundle τ (siblings generic)
lift-node1-nodes-τ : (n1 n2 n3 n4 : NetProc) {n1′ : NetProc}
    → n1 ─[ τ ]─► n1′
    → (n1 ⦀ (n2 ⦀ (n3 ⦀ n4))) ─[ τ ]─► (n1′ ⦀ (n2 ⦀ (n3 ⦀ n4)))
lift-node1-nodes-τ n1 n2 n3 n4 step = ⦀-τ-L n1 (n2 ⦀ (n3 ⦀ n4)) step

-- lift a NODES τ to the whole-system `(Med ∥⇘ ioES ⇙ Nodes) ∖ ioES` τ (medium
-- generic on the left) — the top of the `⟦_⟧` stack
lift-nodes-whole-τ : (Med Nodes : NetProc) {Nodes′ : NetProc}
    → Nodes ─[ τ ]─► Nodes′
    → ((Med ∥⇘ ioES ⇙ Nodes) ∖ ioES) ─[ τ ]─► ((Med ∥⇘ ioES ⇙ Nodes′) ∖ ioES)
lift-nodes-whole-τ Med Nodes step = ∖-τ ioES (Med ∥⇘ ioES ⇙ Nodes) (∥⇘⇙-τ-R ioES Med Nodes step)

-- lift a MEDIUM τ to the whole-system τ (nodes generic on the right) — the
-- flavor-2 counterpart.  The medium operand is SHARED verbatim between `⟦_⟧`
-- and `absDec`, so the SAME step drives both; once SysMedium exposes the
-- post-`output` phase (see the flavor-2 GAP), this discharges flavor 2's
-- abstract match (`absDec s ─[τ]─► absDec s′`).
lift-med-whole-τ : (Med Nodes : NetProc) {Med′ : NetProc}
    → Med ─[ τ ]─► Med′
    → ((Med ∥⇘ ioES ⇙ Nodes) ∖ ioES) ─[ τ ]─► ((Med′ ∥⇘ ioES ⇙ Nodes) ∖ ioES)
lift-med-whole-τ Med Nodes step = ∖-τ ioES (Med ∥⇘ ioES ⇙ Nodes) (∥⇘⇙-τ-L ioES Med Nodes step)

-- REPRESENTATIVE full seal (node 1, its link-1 bundle, CS client): a CS-client
-- peer sil lifts all the way to a whole-`⟦⟧`-shape τ.  FULLY GENERIC over the
-- medium, the drivers, all sibling peers/bundles/nodes — so WHNF-safe; Task 5
-- instantiates at the concrete operands (⟦ s ⟧ / ⟦ s′ ⟧) by application, pairing
-- this concrete τ with the confirmed ZERO-τ abstract collapse (`absRun-csC-AB-sil`).
lift-CSc-whole-τ :
    (Med kac kas rest b2 driver n2 n3 n4 : NetProc) (csc : NetProc) {csc′ : NetProc}
  → csc ─[ τ ]─► csc′
  → ((Med ∥⇘ ioES ⇙ ((((kac ⦀ (kas ⦀ (csc  ⦀ rest))) ⦀ b2) ∥⇘ apiES ⇙ driver)
       ⦀ (n2 ⦀ (n3 ⦀ n4)))) ∖ ioES)
    ─[ τ ]─►
    ((Med ∥⇘ ioES ⇙ ((((kac ⦀ (kas ⦀ (csc′ ⦀ rest))) ⦀ b2) ∥⇘ apiES ⇙ driver)
       ⦀ (n2 ⦀ (n3 ⦀ n4)))) ∖ ioES)
lift-CSc-whole-τ Med kac kas rest b2 driver n2 n3 n4 csc step =
  lift-nodes-whole-τ Med _
    (lift-node1-nodes-τ _ n2 n3 n4
      (lift-bundle1-node-τ (kac ⦀ (kas ⦀ (csc ⦀ rest))) b2 driver
        (lift-CSc-bundle-τ kac kas csc rest step)))

------------------------------------------------------------------------
-- LIFT 3 (flavor-3 io recipient pins) — complete the family for the delivered
-- io `CS/BF × input/output`.  Each pins the unique recipient by routing the
-- inner-`⦀` io step AWAY from the wrong-protocol peer pair via `inner-io-single`
-- + the 1b protocol-mismatch transports.  `ιCS⁻¹`/`ιBF⁻¹` send the OTHER
-- protocol's `input` and `output` channels to `nothing` (catch-all), so the
-- `renameMap-noOffer-χ … refl` transport covers both io directions.  Shared
-- verbatim with the visible-api `fire` (items 3/4).
------------------------------------------------------------------------

-- CS peers never offer a BlockFetch-channel INPUT io (dual of `decCSc-noOffer-BF`)
decCSc-noOffer-BFin : (l : Link) (d : Dir) (pos : CScPos) {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decCSc l d pos) (input l′ d′ N2N_BlockFetch) a
decCSc-noOffer-BFin l d pos = CSNO.renameMap-noOffer-χ (decCSc-src l d pos) refl
decCSs-noOffer-BFin : (l : Link) (d : Dir) (pos : CSsPos) {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decCSs l d pos) (input l′ d′ N2N_BlockFetch) a
decCSs-noOffer-BFin l d pos = CSNO.renameMap-noOffer-χ (decCSs-src l d pos) refl
-- BF peers never offer a ChainSync-channel INPUT io (dual of `decBFc-noOffer-CS`)
decBFc-noOffer-CSin : (l : Link) (d : Dir) (pos : BFcPos) {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decBFc l d pos) (input l′ d′ N2N_ChainSync) a
decBFc-noOffer-CSin l d pos = BFNO.renameMap-noOffer-χ (decBFc-src l d pos) refl
decBFs-noOffer-CSin : (l : Link) (d : Dir) (pos : BFsPos) {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decBFs l d pos) (input l′ d′ N2N_ChainSync) a
decBFs-noOffer-CSin l d pos = BFNO.renameMap-noOffer-χ (decBFs-src l d pos) refl

-- CS pair does not offer a BF-channel INPUT io; BF pair does not offer a
-- CS-channel INPUT io (dual assemblies of `csPair-noOffer-BF`/`bfPair-noOffer-CS`)
csPair-noOffer-BFin : (l : Link) (cl sv : Dir) (pc : CScPos) (ps : CSsPos)
    {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decCSc l cl pc ⦀ decCSs l sv ps) (input l′ d′ N2N_BlockFetch) a
csPair-noOffer-BFin l cl sv pc ps =
  ⦀-noOffer (decCSc l cl pc) (decCSs l sv ps)
            (decCSc-noOffer-BFin l cl pc) (decCSs-noOffer-BFin l sv ps)
bfPair-noOffer-CSin : (l : Link) (cl sv : Dir) (pc : BFcPos) (ps : BFsPos)
    {l′ : Link} {d′ : Dir} {a : Payload}
  → ¬ IoOffers (decBFc l cl pc ⦀ decBFs l sv ps) (input l′ d′ N2N_ChainSync) a
bfPair-noOffer-CSin l cl sv pc ps =
  ⦀-noOffer (decBFc l cl pc) (decBFs l sv ps)
            (decBFc-noOffer-CSin l cl pc) (decBFs-noOffer-CSin l sv ps)

-- io PIN, BF INPUT: CS pair is not the recipient (dual of `reflect-io-pin-BF`)
reflect-io-pin-BFin :
    (l : Link) (cl sv : Dir) (pc : CScPos) (ps : CSsPos) (B : NetProc)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → ((decCSc l cl pc ⦀ decCSs l sv ps) ⦀ B)
      ─[ ev (evl (evLabel _ (input l′ d′ N2N_BlockFetch) a)) ]─► M
  → (Σ[ X₁ ∈ NetProc ] ((decCSc l cl pc ⦀ decCSs l sv ps)
        ─[ ev (evl (evLabel _ (input l′ d′ N2N_BlockFetch) a)) ]─► X₁))
  ⊎ (Σ[ B₁ ∈ NetProc ] (B ─[ ev (evl (evLabel _ (input l′ d′ N2N_BlockFetch) a)) ]─► B₁))
reflect-io-pin-BFin l cl sv pc ps B step =
  inner-io-single (decCSc l cl pc ⦀ decCSs l sv ps) B
    (inj₁ (csPair-noOffer-BFin l cl sv pc ps)) step

-- io PIN, CS OUTPUT: BF pair is not the recipient
reflect-io-pin-CS :
    (l : Link) (cl sv : Dir) (pc : BFcPos) (ps : BFsPos) (B : NetProc)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → ((decBFc l cl pc ⦀ decBFs l sv ps) ⦀ B)
      ─[ ev (evl (evLabel _ (output l′ d′ N2N_ChainSync) a)) ]─► M
  → (Σ[ X₁ ∈ NetProc ] ((decBFc l cl pc ⦀ decBFs l sv ps)
        ─[ ev (evl (evLabel _ (output l′ d′ N2N_ChainSync) a)) ]─► X₁))
  ⊎ (Σ[ B₁ ∈ NetProc ] (B ─[ ev (evl (evLabel _ (output l′ d′ N2N_ChainSync) a)) ]─► B₁))
reflect-io-pin-CS l cl sv pc ps B step =
  inner-io-single (decBFc l cl pc ⦀ decBFs l sv ps) B
    (inj₁ (bfPair-noOffer-CS l cl sv pc ps)) step

-- io PIN, CS INPUT: BF pair is not the recipient
reflect-io-pin-CSin :
    (l : Link) (cl sv : Dir) (pc : BFcPos) (ps : BFsPos) (B : NetProc)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → ((decBFc l cl pc ⦀ decBFs l sv ps) ⦀ B)
      ─[ ev (evl (evLabel _ (input l′ d′ N2N_ChainSync) a)) ]─► M
  → (Σ[ X₁ ∈ NetProc ] ((decBFc l cl pc ⦀ decBFs l sv ps)
        ─[ ev (evl (evLabel _ (input l′ d′ N2N_ChainSync) a)) ]─► X₁))
  ⊎ (Σ[ B₁ ∈ NetProc ] (B ─[ ev (evl (evLabel _ (input l′ d′ N2N_ChainSync) a)) ]─► B₁))
reflect-io-pin-CSin l cl sv pc ps B step =
  inner-io-single (decBFc l cl pc ⦀ decBFs l sv ps) B
    (inj₁ (bfPair-noOffer-CSin l cl sv pc ps)) step

------------------------------------------------------------------------
-- R2 TASK 4 ITEM 3 — `refl-ev` (the FORWARD VISIBLE step of the ≈DR bisim
-- R = {(⟦ s ⟧, absDec s)}, i.e. the `.fwd .on-ev` field).  Given a concrete
-- VISIBLE event `⟦ s ⟧ ─[ev a]─► M` (a ∈ {api*, break} — the only visible
-- events at `breakableSystem`'s top; io is HIDDEN, handled by `refl-τ`), reflect
-- it to a target `s′ : SysState` with `M ≡ ⟦ s′ ⟧` AND an ABSTRACT WEAK VISIBLE
-- run `absDec s ═[ ev a ]═► absDec s′` (the drivers + the break-medium are SHARED
-- verbatim, and the abstract spec peers sync on api exactly as the concrete
-- ones do, so the abstract side performs the SAME single visible event).
--
-- STOP-RULE STATUS (matching `refl-τ`'s bar): this delivers, all operand-GENERIC
-- (no concrete `⟦s⟧`/`decNodeX` WHNF):
--   · the output record `ReflevOut` (the `═[ ev a ]═► absDec s′` field the
--     `.fwd .on-ev` obligation consumes);
--   · the visible-event INVERSIONS — `reflect-top-ev` (hide passthrough for
--     a ∉ ioES, then medium-vs-nodes via `Par-ev-elim ioES`, io/evBoth refuted)
--     and `reflect-node-api` (an api event ∈ apiES is a driver↔peer `evSync`);
--     the nodes-`⦀` split reuses the generic `inner-io-single`;
--   · the visible-event INTRO lifts (`∖-ev`/`⦀-ev-L/R`/`∥⇘⇙-ev-sync`/
--     `∥⇘⇙-ev-soloL/R` = `Hide-keep`/`Par-soloL/R`/`Par-sync`) that rebuild the
--     event up the `⦀`/`∥⇘`/`∖` stack, and the representative whole-system seals
--     `lift-med-whole-ev` (break, medium solo) + `lift-api-whole-ev` (api, a
--     node-internal driver↔peer sync lifted through the node/nodes/hide stack).
-- The concrete dispatcher (which `s′`; the concrete non-offer facts feeding the
-- solo lifts) is Task 5's job, exactly as for `refl-τ`.
------------------------------------------------------------------------

-- the abstract four-node bundle at a `SysState` (the RHS operand of `absDec`)
absNodesOf : SysState → NetProc
absNodesOf s = absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))

-- THE FORWARD-VISIBLE OUTPUT: reflect a concrete visible event of `⟦ s ⟧` to a
-- `SysState` move whose decode is the event-target, matched on the abstract side
-- by the SAME visible event (a weak visible run `═[ ev a ]═►` = τ*·a·τ*, here
-- with ZERO padding τ).
record ReflevOut (s : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                 (M″ : NetProc) : Set₁ where
  constructor mkReflev
  field
    tgt    : SysState                                             -- the reflected s′
    tgt≡   : M″ ≡ ⟦ tgt ⟧                                          -- concrete: M″ is s′'s decode
    absRun : absDec s ═[ ev (evl (evLabel X e a)) ]═► absDec tgt   -- abstract: SAME visible event

-- package a single abstract visible step into the weak visible run the record
-- wants (ZERO padding τ — the abstract side matches the event exactly)
absRun-ev : {s s′ : SysState} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
          → absDec s ─[ ev (evl (evLabel X e a)) ]─► absDec s′
          → absDec s ═[ ev (evl (evLabel X e a)) ]═► absDec s′
absRun-ev step = wev τ*-refl step τ*-refl

------------------------------------------------------------------------
-- VISIBLE-EVENT INVERSIONS (operand-GENERIC; mirror the `refl-τ` splits).
------------------------------------------------------------------------

-- inversion of ONE visible non-io event of the hide-gated top `(M ∥⇘ ioES ⇙ N)
-- ∖ ioES`: since a ∉ ioES it passes the hide (a `keep`), and the inner `∥⇘ ioES ⇙`
-- is a SOLO of the medium (`break`) or the nodes (`api`) — the io-`evSync` is
-- refuted by ¬(a ∈ ioES) and the interleave `evBoth` by the given disjointness
data TopEvR (M N : NetProc) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
            (M″ : NetProc) : Set₁ where
  medEv   : (M₁ : NetProc) → M ─[ ev (evl (evLabel X e a)) ]─► M₁
          → M″ ≡ ((M₁ ∥⇘ ioES ⇙ N) ∖ ioES) → TopEvR M N e a M″
  nodesEv : (N₁ : NetProc) → N ─[ ev (evl (evLabel X e a)) ]─► N₁
          → M″ ≡ ((M ∥⇘ ioES ⇙ N₁) ∖ ioES) → TopEvR M N e a M″

-- reflect ONE visible non-io event of the full-stack skeleton (TOTAL, symbolic;
-- the disjointness — one of medium/nodes does NOT offer the event — kills the
-- interleave overlap, exactly as `inner-io-single` does for the io-`⦀`)
reflect-top-ev : (M N : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                 {M″ : NetProc}
  → (¬ IoOffers M e a) ⊎ (¬ IoOffers N e a)
  → ((M ∥⇘ ioES ⇙ N) ∖ ioES) ─[ ev (evl (evLabel X e a)) ]─► M″
  → TopEvR M N e a M″
reflect-top-ev M N disj step with Hide-ev-elim ioES (M ∥⇘ ioES ⇙ N) step
... | heV P′ ¬mem parStep with Par-ev-elim ioES merge⊤ M N parStep
...   | evSync p _ _   = ⊥-elim (¬mem p)
...   | evL  _ sM      = medEv _ sM refl
...   | evR  _ sN      = nodesEv _ sN refl
...   | evBoth _ sM sN with disj
...     | inj₁ ¬M = ⊥-elim (¬M (_ , sM))
...     | inj₂ ¬N = ⊥-elim (¬N (_ , sN))

-- inversion of an api event (∈ apiES) of a node `bundle ∥⇘ apiES ⇙ driver`: it
-- is a SYNC — BOTH the driver and the protocol-matching peer fire (the api
-- constructor pins the peer/protocol).  Solo/`evBoth`/`ev√` are all refuted
-- (they carry ¬(a ∈ apiES) / a √-label)
data NodeApiR (bundle driver : NetProc) {X : Set 0ℓ} (e : Net_Api Payload X)
              (a : X) (A′ : NetProc) : Set₁ where
  apiSync : (B₁ D₁ : NetProc)
          → bundle ─[ ev (evl (evLabel X e a)) ]─► B₁
          → driver ─[ ev (evl (evLabel X e a)) ]─► D₁
          → A′ ≡ (B₁ ∥⇘ apiES ⇙ D₁) → NodeApiR bundle driver e a A′

-- reflect ONE api event of a node into the driver↔peer sync (TOTAL, symbolic)
reflect-node-api : (bundle driver : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
                   {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a
  → (bundle ∥⇘ apiES ⇙ driver) ─[ ev (evl (evLabel X e a)) ]─► A′
  → NodeApiR bundle driver e a A′
reflect-node-api bundle driver mem step
  with Par-ev-elim apiES merge⊤ bundle driver step
... | evSync _ sB sD = apiSync _ _ sB sD refl
... | evL  ¬p _      = ⊥-elim (¬p mem)
... | evR  ¬p _      = ⊥-elim (¬p mem)
... | evBoth ¬p _ _  = ⊥-elim (¬p mem)

------------------------------------------------------------------------
-- VISIBLE-EVENT INTRO lifts (operand-GENERIC; mirror the `refl-τ` τ-intro
-- family).  They rebuild the event up the stack on the ABSTRACT side (for
-- `refl-ev`) and, symmetrically, on the CONCRETE side (reused by `fire`'s
-- `.bwd .on-ev`), since all operands are variables — WHNF-safe.
------------------------------------------------------------------------

-- visible-event intro through hide `∖ A` (a ∉ A survives as a `keep`)
∖-ev : (A : EventSet) (P : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
       {P′ : NetProc}
     → ¬ A .mem (X , e) a → P ─[ ev (evl (evLabel X e a)) ]─► P′
     → (P ∖ A) ─[ ev (evl (evLabel X e a)) ]─► (P′ ∖ A)
∖-ev A P ¬mem step = Hide-keep A P ¬mem step

-- solo visible-event intro through interleave `⦀` (left / right operand steps;
-- the idle sibling's NON-OFFER `viewV (force _) ≡ nothing` is a hypothesis)
⦀-ev-L : (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {P′ : NetProc}
       → P ─[ ev (evl (evLabel X e a)) ]─► P′
       → viewV (PTree.force Q) (X , e) a ≡ nothing
       → (P ⦀ Q) ─[ ev (evl (evLabel X e a)) ]─► (P′ ⦀ Q)
⦀-ev-L P Q step nq = Par-soloL ∅ES merge⊤ P Q (λ ()) step nq

⦀-ev-R : (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Q′ : NetProc}
       → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
       → viewV (PTree.force P) (X , e) a ≡ nothing
       → (P ⦀ Q) ─[ ev (evl (evLabel X e a)) ]─► (P ⦀ Q′)
⦀-ev-R P Q step np = Par-soloR ∅ES merge⊤ P Q (λ ()) step np

-- SYNC visible-event intro through the gated stack `∥⇘ A ⇙` (both operands fire
-- a shared event ∈ A — the api driver↔peer sync)
∥⇘⇙-ev-sync : (A : EventSet) (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
              {a : X} {P′ Q′ : NetProc}
            → A .mem (X , e) a
            → P ─[ ev (evl (evLabel X e a)) ]─► P′
            → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
            → (P ∥⇘ A ⇙ Q) ─[ ev (evl (evLabel X e a)) ]─► (P′ ∥⇘ A ⇙ Q′)
∥⇘⇙-ev-sync A P Q mem sP sQ = Par-sync A merge⊤ P Q mem sP sQ

-- solo visible-event intro through the gated stack `∥⇘ A ⇙` (event ∉ A, one
-- operand steps past the idle other; sibling non-offer a hypothesis)
∥⇘⇙-ev-soloL : (A : EventSet) (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
               {a : X} {P′ : NetProc}
             → ¬ A .mem (X , e) a → P ─[ ev (evl (evLabel X e a)) ]─► P′
             → viewV (PTree.force Q) (X , e) a ≡ nothing
             → (P ∥⇘ A ⇙ Q) ─[ ev (evl (evLabel X e a)) ]─► (P′ ∥⇘ A ⇙ Q)
∥⇘⇙-ev-soloL A P Q ¬mem step nq = Par-soloL A merge⊤ P Q ¬mem step nq

∥⇘⇙-ev-soloR : (A : EventSet) (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
               {a : X} {Q′ : NetProc}
             → ¬ A .mem (X , e) a → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
             → viewV (PTree.force P) (X , e) a ≡ nothing
             → (P ∥⇘ A ⇙ Q) ─[ ev (evl (evLabel X e a)) ]─► (P ∥⇘ A ⇙ Q′)
∥⇘⇙-ev-soloR A P Q ¬mem step np = Par-soloR A merge⊤ P Q ¬mem step np

-- lift a node-1 solo visible event to the four-node `⦀` bundle (sibling
-- non-offer a hypothesis)
lift-node1-nodes-ev : (n1 n2 n3 n4 : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
                      {a : X} {n1′ : NetProc}
                    → n1 ─[ ev (evl (evLabel X e a)) ]─► n1′
                    → viewV (PTree.force (n2 ⦀ (n3 ⦀ n4))) (X , e) a ≡ nothing
                    → (n1 ⦀ (n2 ⦀ (n3 ⦀ n4))) ─[ ev (evl (evLabel X e a)) ]─►
                      (n1′ ⦀ (n2 ⦀ (n3 ⦀ n4)))
lift-node1-nodes-ev n1 n2 n3 n4 step nq = ⦀-ev-L n1 (n2 ⦀ (n3 ⦀ n4)) step nq

-- lift a node-internal api driver↔peer sync to the whole node (a node =
-- `bundle ∥⇘ apiES ⇙ driver`)
lift-api-node-ev : (bundle driver : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
                   {a : X} {B′ D′ : NetProc}
                 → apiES .mem (X , e) a
                 → bundle ─[ ev (evl (evLabel X e a)) ]─► B′
                 → driver ─[ ev (evl (evLabel X e a)) ]─► D′
                 → (bundle ∥⇘ apiES ⇙ driver) ─[ ev (evl (evLabel X e a)) ]─►
                   (B′ ∥⇘ apiES ⇙ D′)
lift-api-node-ev bundle driver mem sB sD = ∥⇘⇙-ev-sync apiES bundle driver mem sB sD

-- lift a NODES visible event to the whole-system `(Med ∥⇘ ioES ⇙ Nodes) ∖ ioES`
-- (medium non-offer a hypothesis) — the api top of the `⟦_⟧`/`absDec` stack
lift-nodes-whole-ev : (Med Nodes : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
                      {a : X} {Nodes′ : NetProc}
                    → ¬ ioES .mem (X , e) a
                    → Nodes ─[ ev (evl (evLabel X e a)) ]─► Nodes′
                    → viewV (PTree.force Med) (X , e) a ≡ nothing
                    → ((Med ∥⇘ ioES ⇙ Nodes) ∖ ioES) ─[ ev (evl (evLabel X e a)) ]─►
                      ((Med ∥⇘ ioES ⇙ Nodes′) ∖ ioES)
lift-nodes-whole-ev Med Nodes ¬mem step nq =
  ∖-ev ioES (Med ∥⇘ ioES ⇙ Nodes) ¬mem (∥⇘⇙-ev-soloR ioES Med Nodes ¬mem step nq)

-- REPRESENTATIVE SEAL (break, flavor medium-solo): a medium visible event ∉ ioES
-- lifts to a whole-`⟦⟧`/`absDec`-shape visible event (medium solo through the
-- io-gate, nodes idle).  FULLY GENERIC — the medium/nodes operands are variables;
-- Task 5 instantiates at `decMed`/`nodesOf` (or the abstract `absNodesOf`) by
-- application, pairing this with the SHARED medium's identical break step.
lift-med-whole-ev : (Med Nodes : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
                    {a : X} {Med′ : NetProc}
                  → ¬ ioES .mem (X , e) a
                  → Med ─[ ev (evl (evLabel X e a)) ]─► Med′
                  → viewV (PTree.force Nodes) (X , e) a ≡ nothing
                  → ((Med ∥⇘ ioES ⇙ Nodes) ∖ ioES) ─[ ev (evl (evLabel X e a)) ]─►
                    ((Med′ ∥⇘ ioES ⇙ Nodes) ∖ ioES)
lift-med-whole-ev Med Nodes ¬mem step nq =
  ∖-ev ioES (Med ∥⇘ ioES ⇙ Nodes) ¬mem (∥⇘⇙-ev-soloL ioES Med Nodes ¬mem step nq)

-- REPRESENTATIVE SEAL (api, flavor node-sync): a node-internal driver↔peer api
-- sync at node 1 lifts all the way to a whole-`⟦⟧`/`absDec`-shape api event
-- (node-internal sync → node solo among the four → nodes solo through the io-gate
-- → hide keep).  FULLY GENERIC over the medium, siblings, bundle, driver; Task 5
-- instantiates at the concrete/abstract operands by application.
lift-api-whole-ev : (Med n2 n3 n4 bundle driver : NetProc) {X : Set 0ℓ}
                    {e : Net_Api Payload X} {a : X} {B′ D′ : NetProc}
                  → apiES .mem (X , e) a
                  → ¬ ioES .mem (X , e) a
                  → bundle ─[ ev (evl (evLabel X e a)) ]─► B′
                  → driver ─[ ev (evl (evLabel X e a)) ]─► D′
                  → viewV (PTree.force (n2 ⦀ (n3 ⦀ n4))) (X , e) a ≡ nothing
                  → viewV (PTree.force Med) (X , e) a ≡ nothing
                  → ((Med ∥⇘ ioES ⇙ ((bundle ∥⇘ apiES ⇙ driver) ⦀ (n2 ⦀ (n3 ⦀ n4))))
                       ∖ ioES) ─[ ev (evl (evLabel X e a)) ]─►
                    ((Med ∥⇘ ioES ⇙ ((B′ ∥⇘ apiES ⇙ D′) ⦀ (n2 ⦀ (n3 ⦀ n4))))
                       ∖ ioES)
lift-api-whole-ev Med n2 n3 n4 bundle driver mem ¬mem sB sD nqNodes nqMed =
  lift-nodes-whole-ev Med _ ¬mem
    (lift-node1-nodes-ev (bundle ∥⇘ apiES ⇙ driver) n2 n3 n4
      (lift-api-node-ev bundle driver mem sB sD) nqNodes)
    nqMed

------------------------------------------------------------------------
-- R2 TASK 4 ITEM 4 — `fire` (the BACKWARD step of the ≈DR bisim, i.e. the
-- `.bwd` field `WSimF (DRbisim R) (absDec s) (⟦ s ⟧)`): every step of
-- `absDec s` is matched by `⟦ s ⟧`.  The relation `R = {(⟦ s ⟧, absDec s)}` is
-- FUNCTIONAL in `s`, so `fire` reflects an abstract step to the SAME `s′` the
-- forward direction uses — a `SysState`-level transition realised by BOTH
-- decodes.  We exploit that symmetry: the visible-event INVERSIONS
-- (`reflect-top-ev`/`reflect-node-api`) and the INTRO lifts of item 3 are all
-- operand-GENERIC, so they apply at the ABSTRACT operands (to invert the
-- abstract step) AND at the CONCRETE operands (to rebuild the `⟦ s ⟧` run)
-- verbatim — nothing new is needed for the api/break `on-ev` case beyond
-- instantiating item 3's lifts at `decMed`/`nodesOf`.
--
--   · `.bwd .on-tau` — abstract τ sources are ONLY the shared-medium sils and
--     the hidden io-syncs (the abstract peers are τ-free ⇒ NO peer sils; the
--     drivers are τ-free).  `reflect-absDec-τ` inverts an abstract τ (reusing
--     the generic `reflect-hidden-io` at the abstract operands) into a medium τ
--     / a nodes τ / an io-sync.  The medium τ is matched by the IDENTICAL medium
--     τ of `⟦ s ⟧` (medium SHARED verbatim) via `lift-med-whole-τ`; the io-sync
--     by `lift-io-sync-whole-τ` (a medium+peer io-`Par-sync` hidden to a τ).  The
--     nodes-τ branch is VACUOUS (abstract peers/drivers τ-free) — its discharge
--     needs the concrete per-peer inversion (Task 5).
--   · `.bwd .on-ev` — mirror of item 3 (`reflect-top-ev`/`reflect-node-api` at
--     the abstract operands ↝ `lift-med-whole-ev`/`lift-api-whole-ev` at the
--     concrete operands).  Break is a SHARED-medium event, so the abstract step
--     IS the concrete step (`fire-ev-break-rep`).  Api rebuilds the concrete run
--     by `lift-api-whole-ev` at `decNodeA`'s operands (Task 5 dispatch).
--
-- STOP-RULE STATUS: SKELETON with a representative per case, all operand-GENERIC,
-- no postulates.  The medium τ / io-sync land on the SAME documented SysMedium
-- post-`output` GAP as `refl-τ` flavor 2/3 (a Task-1 enrichment, not an
-- obstruction); the concrete `s′` reflection + the nodes-τ vacuity are Task 5.
------------------------------------------------------------------------

-- THE BACKWARD-τ OUTPUT: reflect an abstract internal τ of `absDec s` to a
-- `SysState` move whose ABSTRACT decode is the τ-target, matched by a
-- ZERO-or-more-τ run of the concrete `⟦ s ⟧`.
record FireτOut (s : SysState) (N : NetProc) : Set₁ where
  constructor mkFireτ
  field
    tgt    : SysState                        -- the reflected target state s′
    tgt≡   : N ≡ absDec tgt                   -- abstract: N is s′'s abstract decode
    conRun : ⟦ s ⟧ ─[τ*]─► ⟦ tgt ⟧            -- concrete: matches by ZERO-or-more τ

-- THE BACKWARD-VISIBLE OUTPUT: reflect an abstract visible event of `absDec s`
-- to a `SysState` move, matched by the SAME visible event of `⟦ s ⟧` (a weak
-- visible run `═[ ev a ]═►`).
record FireevOut (s : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                 (N : NetProc) : Set₁ where
  constructor mkFireev
  field
    tgt    : SysState                                             -- the reflected s′
    tgt≡   : N ≡ absDec tgt                                        -- abstract: N is s′'s decode
    conRun : ⟦ s ⟧ ═[ ev (evl (evLabel X e a)) ]═► ⟦ tgt ⟧         -- concrete: SAME visible event

-- package a single concrete τ into the τ* run `FireτOut` wants
conRun-τ : {s s′ : SysState} → ⟦ s ⟧ ─[ τ ]─► ⟦ s′ ⟧ → ⟦ s ⟧ ─[τ*]─► ⟦ s′ ⟧
conRun-τ step = τ*-step step τ*-refl

-- package a single concrete visible step into the weak visible run `FireevOut`
-- wants (ZERO padding τ)
conRun-ev : {s s′ : SysState} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
          → ⟦ s ⟧ ─[ ev (evl (evLabel X e a)) ]─► ⟦ s′ ⟧
          → ⟦ s ⟧ ═[ ev (evl (evLabel X e a)) ]═► ⟦ s′ ⟧
conRun-ev step = wev τ*-refl step τ*-refl

------------------------------------------------------------------------
-- `.bwd .on-tau` — abstract-τ inversion + the shared-medium / io-sync matches.
------------------------------------------------------------------------

-- reflect ONE hidden-τ step of the abstract `absDec s` (the abstract-operand
-- instance of `reflect-hidden-io`): `absDec s` is DEFINITIONALLY
-- `(decMed (med s) ∥⇘ ioES ⇙ absNodesOf s) ∖ ioES`, so it inverts to an inner
-- `∥⇘ ioES ⇙` τ (medium / nodes) or a medium/nodes io-SYNC — no `evBoth` on io
reflect-absDec-τ : (s : SysState) {N : NetProc}
  → absDec s ─[ τ ]─► N
  → ReflOut (decMed (med s)) (absNodesOf s) N
reflect-absDec-τ s step = reflect-hidden-io (decMed (med s)) (absNodesOf s) step

-- lift a medium+nodes io-SYNC (both fire the SAME io ∈ ioES) to a HIDDEN whole-
-- system τ (`Hide-hidden` turns the synchronised io into a τ).  Operand-GENERIC;
-- shared by `refl-τ` flavor 3 and `fire`'s `.bwd .on-tau` io-sync branch.
lift-io-sync-whole-τ : (Med Nodes : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
                       {a : X} {Med′ Nodes′ : NetProc}
                     → ioES .mem (X , e) a
                     → Med ─[ ev (evl (evLabel X e a)) ]─► Med′
                     → Nodes ─[ ev (evl (evLabel X e a)) ]─► Nodes′
                     → ((Med ∥⇘ ioES ⇙ Nodes) ∖ ioES) ─[ τ ]─►
                       ((Med′ ∥⇘ ioES ⇙ Nodes′) ∖ ioES)
lift-io-sync-whole-τ Med Nodes iomem sM sN =
  Hide-hidden ioES (Med ∥⇘ ioES ⇙ Nodes) iomem
    (Par-sync ioES merge⊤ Med Nodes iomem sM sN)

-- REPRESENTATIVE (`.bwd .on-tau`, shared-medium τ): an abstract medium τ of
-- `absDec s` is driven by the IDENTICAL medium in `⟦ s ⟧` (the medium decode is
-- SHARED verbatim, so the abstract step IS a concrete step), lifted by the
-- operand-generic `lift-med-whole-τ`.  The same SysMedium post-`output` GAP as
-- flavor 2 governs which `Med′` is a clean `decMed m′` (Task-1 enrichment); the
-- τ-match itself is unconditional.
fire-tau-med-rep : (s : SysState) {Med′ : NetProc}
  → decMed (med s) ─[ τ ]─► Med′
  → ⟦ s ⟧ ─[ τ ]─► ((Med′ ∥⇘ ioES ⇙ nodesOf s) ∖ ioES)
fire-tau-med-rep s medStep = lift-med-whole-τ (decMed (med s)) (nodesOf s) medStep

------------------------------------------------------------------------
-- `.bwd .on-ev` — mirror of item 3: the abstract visible event is matched by
-- the SAME event of `⟦ s ⟧`, built with item 3's operand-generic intro lifts.
------------------------------------------------------------------------

-- REPRESENTATIVE (`.bwd .on-ev`, break): the abstract break event of `absDec s`
-- is a medium solo; because the medium is SHARED verbatim, that SAME medium
-- break step drives `⟦ s ⟧` back by the operand-generic `lift-med-whole-ev` (no
-- reflection needed — the abstract step is literally the concrete step).  Given
-- the shared-medium break step + the concrete-nodes non-offer of break.
fire-ev-break-rep : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {Med′ : NetProc}
  → ¬ ioES .mem (X , e) a
  → decMed (med s) ─[ ev (evl (evLabel X e a)) ]─► Med′
  → viewV (PTree.force (nodesOf s)) (X , e) a ≡ nothing
  → ⟦ s ⟧ ─[ ev (evl (evLabel X e a)) ]─► ((Med′ ∥⇘ ioES ⇙ nodesOf s) ∖ ioES)
fire-ev-break-rep s ¬mem medStep nq =
  lift-med-whole-ev (decMed (med s)) (nodesOf s) ¬mem medStep nq

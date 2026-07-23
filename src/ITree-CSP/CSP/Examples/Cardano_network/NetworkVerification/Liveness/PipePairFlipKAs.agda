{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- PipePairPeersKB — the KeepAlive + BlockFetch per-peer bisims of the
-- FourNode node-side pipeline milestone (M1, Part 12).
--
-- SPLIT RATIONALE (controller-sanctioned): the four KA/BF per-peer
-- `≈DR` bisims (KA server, BF server, KA client, BF client) are
-- relocated here out of `PipePair.agda` to respect the ~9k/file guard
-- once they are generalised over the link `l` (the firing clauses
-- quadruple).  `PipePair` keeps the contract surface, the spec tables,
-- the generic `tableSpec-OffersOnly`/`RenOO` transport, and the impl+spec
-- OffersOnly instances; this module `open import`s it and re-imports the
-- KA/BF source FSM + rename modules (their names are not re-exported).
-- `PipePairAssembly` will consume the bisims from here.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.Nat using (ℕ)
import Data.Fin as F
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees
open PTree

-- the concrete FourNode instantiation: the shared Params `p`, the `consume`
-- driver, the `apiES` sync set, and the two consume-side link ids
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; consume; apiES; linkBD; linkCD )

open import CSP.Examples.Cardano_network.Params using (Params)
open Params p   -- Cookie/Block/Txid/Time/Length/time₀/length₀ + DecEq instances

-- control enums (Dir/IDs/Mode/BlockingStyle) + their DecEq instances
open import CSP.Examples.Cardano_network.Base

-- the shared payload (message datatypes + DecEq instances)
open import CSP.Examples.Cardano_network.Data p

-- the shared alphabet (Net_Api events, api tag enums) — opened fully so
-- the tag/channel constructors and DecEq instances are all in scope
open import CSP.Examples.Cardano_network.Net p

-- the mini-protocol peer bundle (all eight renamed peers on the link) plus the
-- impl peers + their event injections (needed for the impl-side OffersOnly 2(b))
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( miniProtocols
        ; KAclientA; KAserverA; ιKA; ιKA⁻¹; ιKA-linv
        ; BFclientA; BFserverA; ιBF; ιBF⁻¹; ιBF-linv )
-- the KeepAlive source peer FSMs (client/server step functions + states)
open import CSP.Examples.Cardano_network.KeepAlive p
  using ( KAEv; KAEv-≟; sendKA; receiveKA; apiKAev; doneKA
        ; KAState; stClient; stServer; stDone; Rr
        ; clientStep; serverStep; KAclientStClient; KAserverStClient )
-- source-side operators for KAEv (name the impl bisim states: iter/iter-bind/Ret)
import CSP.Operators {E = KAEv} KAEv-≟ as SrcOp
-- the KA rename instance (the same module application NetworkPar's peers use)
import CSP.Rename {E₁ = KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA
-- the BlockFetch source peer FSM (qualified — its BFState/step/Rr names clash
-- with KeepAlive's stDone/serverStep/Rr, so it must NOT be opened)
import CSP.Examples.Cardano_network.BlockFetch p as BF
-- source-side operators for BFEv (name the BF server bisim's iter/iter-bind/Output states)
import CSP.Operators {E = BF.BFEv} BF.BFEv-≟ as SrcOpB
-- the BF rename instance (the same module application NetworkPar's peers use)
import CSP.Rename {E₁ = BF.BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _>>_; Skip )

open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _≈DR_; deadlock-no-τ )
-- weak steps + the relation→DRbisim coinduction principle (per-peer bisims)
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev )
open import Semantics.BisimFromRel {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( module DRFromRel )

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst; ≡-≟-identity)
open import Data.Product using (Σ-syntax)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; sRet; sSil; sVis; sTau; ev; evl; evLabel; Event√; √; Label; τ
        ; Diverges )

import CSP.Laws.Bisim.DRCongruenceRep
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; Disj; OffersOnly; MenuConf
        ; OffersOnly-deadlock; OffersOnly-Ret; OffersOnly-Skip; OffersOnly-mono
        ; OffersOnly-pchoice; OffersOnly-Prefix; OffersOnly-Prefix₀; OffersOnly-Output
        ; OffersOnly->>=; sep-from-OffersOnly )
open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload})
  using ( Sep; cong-⦀; cong-Par⊤-L )

open Op using ( ∅ES )
open import Process_Trees using (NodeKind)

-- the contract surface + spec tables + generic transport + OffersOnly
-- instances (all the KA/BF bisims' non-source-FSM dependencies)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePair


module CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairFlipKAs where


-- Item 3, FIRST PEER BISIM: `KAserverA linkBD hi ≈DR kaServerSpec linkBD hi`.
--
-- Architecture (the replication template for the other seven peers):
--   * a finite relation `KASRel` pairing each reachable IMPL tree (the
--     renamed `iter`/`iter-bind` states: one HOME react state per FSM
--     position + one SIL state per loop re-entry) with its spec table
--     position;
--   * the six step-matching functions demanded by the generic
--     `DRFromRel` coinduction principle (`Semantics.BisimFromRel`):
--     forward steps invert the renamed menu by CASE-ENUMERATING the
--     target event (16 `Net_Api` constructors; `Link`/`Dir` Fin-enumerated
--     because cross-module `≟`-gates do not with-share), backward steps
--     enumerate the spec table's edges (same-module gates DO with-share);
--     value-gated (`!`-output) offers are discharged by the `≟-diag`
--     rewrite idiom (`≡-≟-identity`);
--   * no divergence on either side: the spec is τ-free, and every impl τ
--     is a single loop re-entry `sil` into a stable state (`noτ-ib`).
-- Everything is CONCRETE at (linkBD , hi) so all forces compute; the
-- `∀ l d` closure is by (Fin 4 × Dir) enumeration at the assembly level.
------------------------------------------------------------------------

-- the KA server step function at the concrete (linkBD , hi) instance
kSrv : (l : Link) → KAState → PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)
kSrv l = serverStep l hi

-- the KA server spec table at the concrete (linkBD , hi) instance
Tks : (l : Link) → Table KAsPos
Tks l = record { isFin = kaSfin ; nxt = kaSnxt l hi }

-- impl HOME state: the renamed iter at a server FSM position
kasI : (l : Link) → KAState → NetTree
kasI l q = RenKA.renameMap (SrcOp.iter (kSrv l) q)

-- impl MID state: the renamed iter-bind of a residual body tree
kasIB : (l : Link) → PTree KAEv (ExtI KAEv) (KAState ⊎ Rr) → NetTree
kasIB l t = RenKA.renameMap (SrcOp.iter-bind t (kSrv l))

-- x ≟ x computes to yes refl for the Payload DecEq (repo ≟-diag idiom)
≟-diagP : (x : Payload) → (x ≟ x) ≡ yes refl
≟-diagP x = ≡-≟-identity _≟_ refl

-- the visible-menu application of a forced node (nothing on non-react shapes)
visOf : NetTree → (at : AnyTypes (Net_Api Payload)) → proj₁ at → Maybe NetTree
visOf P at a with PTree.force P
... | react v _ = v at a
... | ret _     = nothing
... | sil _     = nothing

-- the KA-server bisimulation relation: reachable impl states ↔ spec positions
data KASRel (l : Link) : NetTree → NetTree → Set₁ where
  rA : KASRel l (kasI l stClient) (tableSpec (Tks l) ksClient)
  rB : (c : Cookie) → KASRel l (kasIB l (SrcOp.Ret (inj₁ (stServer c)))) (tableSpec (Tks l) (ksResp c))
  rC : (c : Cookie) → KASRel l (kasI l (stServer c)) (tableSpec (Tks l) (ksResp c))
  rD : KASRel l (kasIB l (SrcOp.Ret (inj₁ stClient))) (tableSpec (Tks l) ksClient)
  rE : KASRel l (kasIB l (SrcOp.Prefix₀ (doneKA l hi) (SrcOp.Ret (inj₁ stDone)))) (tableSpec (Tks l) ksDdone)
  rF : KASRel l (kasIB l (SrcOp.Ret (inj₁ stDone))) (tableSpec (Tks l) ksTerm)
  rG : KASRel l (kasI l stDone) (tableSpec (Tks l) ksTerm)
  rH : KASRel l (deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} {R = ⊤ {0ℓ}}) deadlock

-- a renamed iter-bind over a STABLE source node (react, empty τ-part) has no τ
noτ-ib : (l : Link) (Q : PTree KAEv (ExtI KAEv) (KAState ⊎ Rr))
         {vq : (at : AnyTypes KAEv) → ContinueType at (Maybe (PTree KAEv (ExtI KAEv) (KAState ⊎ Rr)))}
       → PTree.force Q ≡ react vq SrcOp.∅t
       → ∀ {X} → kasIB l Q ─[ τ ]─► X → ⊥
noτ-ib l Q eqQ (sSil eqf) with PTree.force Q | eqQ | eqf
... | _ | refl | ()
noτ-ib l Q eqQ (sTau {i = A , eι₂} {a = a} eqf br) with PTree.force Q | eqQ
noτ-ib l Q eqQ (sTau {i = A , eι₂} {a = a} eqf br) | _ | refl
  with RenKA.extBwd eι₂
     | subst (λ g → g (A , eι₂) a ≡ just _) (sym (proj₂ (react-injective eqf))) br
... | nothing  | ()
... | just eι₁ | ()

-- the terminated impl home state (√) has no τ
noτ-ret : (l : Link) → ∀ {X} → kasI l stDone ─[ τ ]─► X → ⊥
noτ-ret l (sSil ())
noτ-ret l (sTau () _)

-- the τ-free spec table has no τ at any position
specNoτ : (l : Link) (q : KAsPos) {X : NetTree} → tableSpec (Tks l) q ─[ τ ]─► X → ⊥
specNoτ l ksClient    (sSil ())
specNoτ l ksClient    (sTau refl ())
specNoτ l (ksResp c)  (sSil ())
specNoτ l (ksResp c)  (sTau refl ())
specNoτ l ksDdone     (sSil ())
specNoτ l ksDdone     (sTau refl ())
specNoτ l ksTerm      (sSil ())
specNoτ l ksTerm      (sTau () _)

-- the impl response node fires its (value-gated) wire output (≟-diag rewrite)
implCfire : (l : Link) (c : Cookie)
          → visOf (kasI l (stServer c)) (Payload , input l hi N2N_KeepAlive)
                  (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
              ≡ just (kasIB l (SrcOp.Ret (inj₁ stClient)))
implCfire F.zero c rewrite ≟-diagP (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
implCfire (F.suc F.zero) c rewrite ≟-diagP (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
implCfire (F.suc (F.suc F.zero)) c rewrite ≟-diagP (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
implCfire (F.suc (F.suc (F.suc F.zero))) c rewrite ≟-diagP (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl

-- the spec response position fires the same (value-gated) wire input edge
specRespFire : (l : Link) (c : Cookie)
             → tMenu (Tks l) (ksResp c) (Payload , input l hi N2N_KeepAlive)
                     (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
                 ≡ just (tableSpec (Tks l) ksClient)
specRespFire F.zero c rewrite ≟-diagP (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
specRespFire (F.suc F.zero) c rewrite ≟-diagP (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
specRespFire (F.suc (F.suc F.zero)) c rewrite ≟-diagP (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
specRespFire (F.suc (F.suc (F.suc F.zero))) c rewrite ≟-diagP (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl

-- forward visible/√ simulation: every impl step is matched by a spec step
kasFwdE : (l : Link) → ∀ {p q} {lb : Event√ (⊤ {0ℓ})} {p′} → KASRel l p q → p ─[ ev lb ]─► p′
        → Σ[ q′ ∈ NetTree ] ((q ═[ ev lb ]═► q′) × KASRel l p′ q′)
kasFwdE F.zero rA (sRet ())
kasFwdE F.zero rA (sVis {at = _ , input _ _ N2N_KeepAlive}    refl ())
kasFwdE F.zero rA (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero rA (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero rA (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero rA (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero rA (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc (F.suc F.zero)) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc F.zero) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc F.zero) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE F.zero rA (sVis {at = _ , output F.zero hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rB c
kasFwdE F.zero rA (sVis {at = _ , output F.zero lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc (F.suc F.zero)) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc F.zero) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc F.zero) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE F.zero rA (sVis {at = _ , output F.zero hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rE
kasFwdE F.zero rA (sVis {at = _ , output F.zero lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE F.zero rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasFwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasFwdE F.zero rA (sVis {at = _ , done _ _ N2N_KeepAlive}    refl ())
kasFwdE F.zero rA (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero rA (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero rA (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero rA (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero rA (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero rA (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE F.zero rA (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE F.zero rA (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE F.zero rA (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE F.zero rA (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE F.zero rA (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE F.zero rA (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE F.zero rA (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE F.zero rA (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE F.zero rA (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE F.zero rA (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE F.zero rA (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE F.zero rA (sVis {at = _ , break _}      refl ())
kasFwdE F.zero (rB c) (sRet ())
kasFwdE F.zero (rB c) (sVis () _)
kasFwdE F.zero rD (sRet ())
kasFwdE F.zero rD (sVis () _)
kasFwdE F.zero rF (sRet ())
kasFwdE F.zero rF (sVis () _)
kasFwdE F.zero (rC c) (sRet ())
kasFwdE F.zero (rC c) (sVis {at = _ , input (F.suc (F.suc F.zero)) hi N2N_KeepAlive} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input (F.suc (F.suc F.zero)) lo N2N_KeepAlive} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input (F.suc F.zero) hi N2N_KeepAlive} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input (F.suc F.zero) lo N2N_KeepAlive} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input F.zero hi N2N_KeepAlive} {a = a} refl br)
  with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl = _ , wev τ*-refl (sVis refl (specRespFire F.zero c)) τ*-refl , rD
... | no _     | ()
kasFwdE F.zero (rC c) (sVis {at = _ , input F.zero lo N2N_KeepAlive} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , output _ _ N2N_KeepAlive}    refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , done _ _ N2N_KeepAlive}    refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE F.zero (rC c) (sVis {at = _ , break _}      refl ())
kasFwdE F.zero rE (sRet ())
kasFwdE F.zero rE (sVis {at = _ , done (F.suc (F.suc F.zero)) hi N2N_KeepAlive} refl ())
kasFwdE F.zero rE (sVis {at = _ , done (F.suc (F.suc F.zero)) lo N2N_KeepAlive} refl ())
kasFwdE F.zero rE (sVis {at = _ , done (F.suc F.zero) hi N2N_KeepAlive} refl ())
kasFwdE F.zero rE (sVis {at = _ , done (F.suc F.zero) lo N2N_KeepAlive} refl ())
kasFwdE F.zero rE (sVis {at = _ , done F.zero hi N2N_KeepAlive} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rF
kasFwdE F.zero rE (sVis {at = _ , done F.zero lo N2N_KeepAlive} refl ())
kasFwdE F.zero rE (sVis {at = _ , done (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} refl ())
kasFwdE F.zero rE (sVis {at = _ , done (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} refl ())
kasFwdE F.zero rE (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero rE (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero rE (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero rE (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero rE (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero rE (sVis {at = _ , input _ _ N2N_KeepAlive}    refl ())
kasFwdE F.zero rE (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero rE (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero rE (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero rE (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero rE (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero rE (sVis {at = _ , output _ _ N2N_KeepAlive}    refl ())
kasFwdE F.zero rE (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE F.zero rE (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE F.zero rE (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE F.zero rE (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE F.zero rE (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE F.zero rE (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE F.zero rE (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE F.zero rE (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE F.zero rE (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE F.zero rE (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE F.zero rE (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE F.zero rE (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE F.zero rE (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE F.zero rE (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE F.zero rE (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE F.zero rE (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE F.zero rE (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE F.zero rE (sVis {at = _ , break _}      refl ())
kasFwdE F.zero rG (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , rH
kasFwdE F.zero rG (sVis () _)
kasFwdE F.zero rH (sRet ())
kasFwdE F.zero rH (sVis refl ())
kasFwdE (F.suc F.zero) rA (sRet ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , input _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output F.zero hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output F.zero lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc F.zero) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rB c
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc F.zero) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output F.zero hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output F.zero lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc F.zero) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rE
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc F.zero) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , done _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc F.zero) rA (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc F.zero) (rB c) (sRet ())
kasFwdE (F.suc F.zero) (rB c) (sVis () _)
kasFwdE (F.suc F.zero) rD (sRet ())
kasFwdE (F.suc F.zero) rD (sVis () _)
kasFwdE (F.suc F.zero) rF (sRet ())
kasFwdE (F.suc F.zero) rF (sVis () _)
kasFwdE (F.suc F.zero) (rC c) (sRet ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input F.zero hi N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input F.zero lo N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input (F.suc (F.suc F.zero)) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input (F.suc (F.suc F.zero)) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input (F.suc F.zero) hi N2N_KeepAlive} {a = a} refl br)
  with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl = _ , wev τ*-refl (sVis refl (specRespFire (F.suc F.zero) c)) τ*-refl , rD
... | no _     | ()
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input (F.suc F.zero) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , output _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , done _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc F.zero) (rC c) (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc F.zero) rE (sRet ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done F.zero hi N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done F.zero lo N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done (F.suc (F.suc F.zero)) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done (F.suc (F.suc F.zero)) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done (F.suc F.zero) hi N2N_KeepAlive} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rF
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done (F.suc F.zero) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , input _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , output _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc F.zero) rE (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc F.zero) rG (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , rH
kasFwdE (F.suc F.zero) rG (sVis () _)
kasFwdE (F.suc F.zero) rH (sRet ())
kasFwdE (F.suc F.zero) rH (sVis refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sRet ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , input _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output F.zero hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output F.zero lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc F.zero) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc F.zero) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rB c
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output F.zero hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output F.zero lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc F.zero) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc F.zero) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rE
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , done _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc (F.suc F.zero)) (rB c) (sRet ())
kasFwdE (F.suc (F.suc F.zero)) (rB c) (sVis () _)
kasFwdE (F.suc (F.suc F.zero)) rD (sRet ())
kasFwdE (F.suc (F.suc F.zero)) rD (sVis () _)
kasFwdE (F.suc (F.suc F.zero)) rF (sRet ())
kasFwdE (F.suc (F.suc F.zero)) rF (sVis () _)
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sRet ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input F.zero hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input F.zero lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input (F.suc F.zero) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input (F.suc F.zero) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = a} refl br)
  with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl = _ , wev τ*-refl (sVis refl (specRespFire (F.suc (F.suc F.zero)) c)) τ*-refl , rD
... | no _     | ()
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input (F.suc (F.suc F.zero)) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , output _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , done _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sRet ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done F.zero hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done F.zero lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done (F.suc F.zero) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done (F.suc F.zero) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done (F.suc (F.suc F.zero)) hi N2N_KeepAlive} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rF
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done (F.suc (F.suc F.zero)) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , input _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , output _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc (F.suc F.zero)) rG (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , rH
kasFwdE (F.suc (F.suc F.zero)) rG (sVis () _)
kasFwdE (F.suc (F.suc F.zero)) rH (sRet ())
kasFwdE (F.suc (F.suc F.zero)) rH (sVis refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sRet ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , input _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output F.zero hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output F.zero lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc F.zero) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc F.zero) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rB c
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) lo N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output F.zero hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output F.zero lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc F.zero) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc F.zero) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rE
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) hi N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output (F.suc (F.suc F.zero)) lo N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , done _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sRet ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis () _)
kasFwdE (F.suc (F.suc (F.suc F.zero))) rD (sRet ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis () _)
kasFwdE (F.suc (F.suc (F.suc F.zero))) rF (sRet ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rF (sVis () _)
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sRet ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input F.zero hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input F.zero lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input (F.suc F.zero) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input (F.suc F.zero) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} {a = a} refl br)
  with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl = _ , wev τ*-refl (sVis refl (specRespFire (F.suc (F.suc (F.suc F.zero))) c)) τ*-refl , rD
... | no _     | ()
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input (F.suc (F.suc F.zero)) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input (F.suc (F.suc F.zero)) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , output _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , done _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sRet ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done F.zero hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done F.zero lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done (F.suc F.zero) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done (F.suc F.zero) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done (F.suc (F.suc (F.suc F.zero))) hi N2N_KeepAlive} refl refl) =
  _ , wev τ*-refl (sVis refl refl) τ*-refl , rF
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done (F.suc (F.suc (F.suc F.zero))) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done (F.suc (F.suc F.zero)) hi N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done (F.suc (F.suc F.zero)) lo N2N_KeepAlive} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , input _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , output _ _ N2N_KeepAlive}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , sndmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , rcvmsg _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , tx _ _ _}     refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , sndack _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , rcvack _ _ _} refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , ack _ _ _}    refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiKA _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiCS _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiBF _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiTS _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiLN _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiLF _ _ _}  refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , break _}      refl ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rG (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , rH
kasFwdE (F.suc (F.suc (F.suc F.zero))) rG (sVis () _)
kasFwdE (F.suc (F.suc (F.suc F.zero))) rH (sRet ())
kasFwdE (F.suc (F.suc (F.suc F.zero))) rH (sVis refl ())
-- rA: the request-await home state — fires only the two wire-output receives
-- rB/rD/rF: sil states — no visible/√ step
-- rC: the response home state — fires only the value-gated wire input send
-- rE: the done-handshake state — fires only the local done event
-- rG: the terminated home state — √ only, both sides deadlock
-- rH: deadlock offers nothing

-- forward τ simulation: the only impl τs are the loop re-entry sils
kasFwdT : (l : Link) → ∀ {p q p′} → KASRel l p q → p ─[ τ ]─► p′
        → Σ[ q′ ∈ NetTree ] ((q ═[ τ ]═► q′) × KASRel l p′ q′)
kasFwdT l rA     st = ⊥-elim (noτ-ib l (kSrv l stClient) refl st)
kasFwdT l (rB c) (sSil refl) = _ , wτ τ*-refl , rC c
kasFwdT l (rB c) (sTau () _)
kasFwdT l (rC c) st = ⊥-elim (noτ-ib l (kSrv l (stServer c)) refl st)
kasFwdT l rD     (sSil refl) = _ , wτ τ*-refl , rA
kasFwdT l rD     (sTau () _)
kasFwdT l rE     st = ⊥-elim (noτ-ib l (SrcOp.Prefix₀ (doneKA l hi) (SrcOp.Ret (inj₁ stDone))) refl st)
kasFwdT l rF     (sSil refl) = _ , wτ τ*-refl , rG
kasFwdT l rF     (sTau () _)
kasFwdT l rG     st = ⊥-elim (noτ-ret l st)
kasFwdT l rH     (sSil ())
kasFwdT l rH     (sTau refl ())

-- backward visible/√ simulation: every spec edge is (weakly) matched by the impl
kasBwdE : (l : Link) → ∀ {p q} {lb : Event√ (⊤ {0ℓ})} {q′} → KASRel l p q → q ─[ ev lb ]─► q′
        → Σ[ p′ ∈ NetTree ] ((p ═[ ev lb ]═► p′) × KASRel l p′ q′)
kasBwdE F.zero rA (sRet ())
kasBwdE F.zero rA (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ F.zero | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rB c
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE F.zero rA (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl br)
  with l′ ≟ F.zero | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rE
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasBwdE F.zero rA (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasBwdE F.zero rA (sVis {at = _ , input _ _ _}  refl ())
kasBwdE F.zero rA (sVis {at = _ , done _ _ _}   refl ())
kasBwdE F.zero rA (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE F.zero rA (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE F.zero rA (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE F.zero rA (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE F.zero rA (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE F.zero rA (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE F.zero rA (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE F.zero rA (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE F.zero rA (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE F.zero rA (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE F.zero rA (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE F.zero rA (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE F.zero rA (sVis {at = _ , break _}      refl ())
kasBwdE F.zero (rB c) (sRet ())
kasBwdE F.zero (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br)
  with l′ ≟ F.zero | d′ ≟ hi
kasBwdE F.zero (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br) | yes refl | yes refl
  with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl (implCfire F.zero c)) τ*-refl , rD
... | no _     | ()
kasBwdE F.zero (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | yes refl | no _ = case br of λ ()
kasBwdE F.zero (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | no _     | _    = case br of λ ()
kasBwdE F.zero (rB c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , output _ _ _} refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , done _ _ _}   refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE F.zero (rB c) (sVis {at = _ , break _}      refl ())
kasBwdE F.zero (rC c) (sRet ())
kasBwdE F.zero (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br)
  with l′ ≟ F.zero | d′ ≟ hi
kasBwdE F.zero (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br) | yes refl | yes refl
  with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl = _ , wev τ*-refl (sVis refl (implCfire F.zero c)) τ*-refl , rD
... | no _     | ()
kasBwdE F.zero (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | yes refl | no _ = case br of λ ()
kasBwdE F.zero (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | no _     | _    = case br of λ ()
kasBwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , output _ _ _} refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , done _ _ _}   refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE F.zero (rC c) (sVis {at = _ , break _}      refl ())
kasBwdE F.zero rD (sRet ())
kasBwdE F.zero rD (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ F.zero | d′ ≟ hi | br
... | yes refl | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl refl) τ*-refl , rB c
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE F.zero rD (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl br)
  with l′ ≟ F.zero | d′ ≟ hi | br
... | yes refl | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl refl) τ*-refl , rE
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasBwdE F.zero rD (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasBwdE F.zero rD (sVis {at = _ , input _ _ _}  refl ())
kasBwdE F.zero rD (sVis {at = _ , done _ _ _}   refl ())
kasBwdE F.zero rD (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE F.zero rD (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE F.zero rD (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE F.zero rD (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE F.zero rD (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE F.zero rD (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE F.zero rD (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE F.zero rD (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE F.zero rD (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE F.zero rD (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE F.zero rD (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE F.zero rD (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE F.zero rD (sVis {at = _ , break _}      refl ())
kasBwdE F.zero rE (sRet ())
kasBwdE F.zero rE (sVis {at = _ , done l′ d′ N2N_KeepAlive} refl br)
  with l′ ≟ F.zero | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rF
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE F.zero rE (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasBwdE F.zero rE (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasBwdE F.zero rE (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasBwdE F.zero rE (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasBwdE F.zero rE (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasBwdE F.zero rE (sVis {at = _ , input _ _ _}  refl ())
kasBwdE F.zero rE (sVis {at = _ , output _ _ _} refl ())
kasBwdE F.zero rE (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE F.zero rE (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE F.zero rE (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE F.zero rE (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE F.zero rE (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE F.zero rE (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE F.zero rE (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE F.zero rE (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE F.zero rE (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE F.zero rE (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE F.zero rE (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE F.zero rE (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE F.zero rE (sVis {at = _ , break _}      refl ())
kasBwdE F.zero rF (sRet refl) =
  _ , wev (τ*-step (sSil refl) τ*-refl) (sRet refl) τ*-refl , rH
kasBwdE F.zero rF (sVis () _)
kasBwdE F.zero rG (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , rH
kasBwdE F.zero rG (sVis () _)
kasBwdE F.zero rH (sRet ())
kasBwdE F.zero rH (sVis refl ())
kasBwdE (F.suc F.zero) rA (sRet ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ (F.suc F.zero) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rB c
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl br)
  with l′ ≟ (F.suc F.zero) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rE
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc F.zero) rA (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc F.zero) (rB c) (sRet ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br)
  with l′ ≟ (F.suc F.zero) | d′ ≟ hi
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br) | yes refl | yes refl
  with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl (implCfire (F.suc F.zero) c)) τ*-refl , rD
... | no _     | ()
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | yes refl | no _ = case br of λ ()
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | no _     | _    = case br of λ ()
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rB c) (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc F.zero) (rC c) (sRet ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br)
  with l′ ≟ (F.suc F.zero) | d′ ≟ hi
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br) | yes refl | yes refl
  with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl = _ , wev τ*-refl (sVis refl (implCfire (F.suc F.zero) c)) τ*-refl , rD
... | no _     | ()
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | yes refl | no _ = case br of λ ()
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | no _     | _    = case br of λ ()
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc F.zero) (rC c) (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc F.zero) rD (sRet ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ (F.suc F.zero) | d′ ≟ hi | br
... | yes refl | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl refl) τ*-refl , rB c
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl br)
  with l′ ≟ (F.suc F.zero) | d′ ≟ hi | br
... | yes refl | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl refl) τ*-refl , rE
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc F.zero) rD (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc F.zero) rE (sRet ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , done l′ d′ N2N_KeepAlive} refl br)
  with l′ ≟ (F.suc F.zero) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rF
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc F.zero) rE (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc F.zero) rF (sRet refl) =
  _ , wev (τ*-step (sSil refl) τ*-refl) (sRet refl) τ*-refl , rH
kasBwdE (F.suc F.zero) rF (sVis () _)
kasBwdE (F.suc F.zero) rG (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , rH
kasBwdE (F.suc F.zero) rG (sVis () _)
kasBwdE (F.suc F.zero) rH (sRet ())
kasBwdE (F.suc F.zero) rH (sVis refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sRet ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ (F.suc (F.suc F.zero)) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rB c
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl br)
  with l′ ≟ (F.suc (F.suc F.zero)) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rE
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rA (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sRet ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br)
  with l′ ≟ (F.suc (F.suc F.zero)) | d′ ≟ hi
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br) | yes refl | yes refl
  with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl (implCfire (F.suc (F.suc F.zero)) c)) τ*-refl , rD
... | no _     | ()
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | yes refl | no _ = case br of λ ()
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | no _     | _    = case br of λ ()
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rB c) (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sRet ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br)
  with l′ ≟ (F.suc (F.suc F.zero)) | d′ ≟ hi
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br) | yes refl | yes refl
  with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl = _ , wev τ*-refl (sVis refl (implCfire (F.suc (F.suc F.zero)) c)) τ*-refl , rD
... | no _     | ()
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | yes refl | no _ = case br of λ ()
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | no _     | _    = case br of λ ()
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) (rC c) (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sRet ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ (F.suc (F.suc F.zero)) | d′ ≟ hi | br
... | yes refl | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl refl) τ*-refl , rB c
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl br)
  with l′ ≟ (F.suc (F.suc F.zero)) | d′ ≟ hi | br
... | yes refl | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl refl) τ*-refl , rE
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rD (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sRet ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done l′ d′ N2N_KeepAlive} refl br)
  with l′ ≟ (F.suc (F.suc F.zero)) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rF
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc F.zero)) rE (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc F.zero)) rF (sRet refl) =
  _ , wev (τ*-step (sSil refl) τ*-refl) (sRet refl) τ*-refl , rH
kasBwdE (F.suc (F.suc F.zero)) rF (sVis () _)
kasBwdE (F.suc (F.suc F.zero)) rG (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , rH
kasBwdE (F.suc (F.suc F.zero)) rG (sVis () _)
kasBwdE (F.suc (F.suc F.zero)) rH (sRet ())
kasBwdE (F.suc (F.suc F.zero)) rH (sVis refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sRet ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ (F.suc (F.suc (F.suc F.zero))) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rB c
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl br)
  with l′ ≟ (F.suc (F.suc (F.suc F.zero))) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rE
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rA (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sRet ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br)
  with l′ ≟ (F.suc (F.suc (F.suc F.zero))) | d′ ≟ hi
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br) | yes refl | yes refl
  with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl (implCfire (F.suc (F.suc (F.suc F.zero))) c)) τ*-refl , rD
... | no _     | ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | yes refl | no _ = case br of λ ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | no _     | _    = case br of λ ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rB c) (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sRet ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br)
  with l′ ≟ (F.suc (F.suc (F.suc F.zero))) | d′ ≟ hi
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} {a = pl} refl br) | yes refl | yes refl
  with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) | br
... | yes refl | refl = _ , wev τ*-refl (sVis refl (implCfire (F.suc (F.suc (F.suc F.zero))) c)) τ*-refl , rD
... | no _     | ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | yes refl | no _ = case br of λ ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input l′ d′ N2N_KeepAlive} refl br) | no _     | _    = case br of λ ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , input _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) (rC c) (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sRet ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAlive c)} refl br)
  with l′ ≟ (F.suc (F.suc (F.suc F.zero))) | d′ ≟ hi | br
... | yes refl | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl refl) τ*-refl , rB c
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output l′ d′ N2N_KeepAlive} {a = t , m , len , keepAlive MsgKADone} refl br)
  with l′ ≟ (F.suc (F.suc (F.suc F.zero))) | d′ ≟ hi | br
... | yes refl | yes refl | refl =
      _ , wev (τ*-step (sSil refl) τ*-refl) (sVis refl refl) τ*-refl , rE
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , blockFetch _}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , chainSync _}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , txSubmission _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosNotify _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_KeepAlive} {a = t , m , len , leiosFetch _}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , output _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , done _ _ _}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rD (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sRet ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done l′ d′ N2N_KeepAlive} refl br)
  with l′ ≟ (F.suc (F.suc (F.suc F.zero))) | d′ ≟ hi | br
... | yes refl | yes refl | refl = _ , wev τ*-refl (sVis refl refl) τ*-refl , rF
... | yes refl | no _     | ()
... | no _     | _        | ()
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_ChainSync}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_BlockFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_TxSubmission} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_LeiosNotify}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , done _ _ N2N_LeiosFetch}   refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , input _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , output _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , sndmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , rcvmsg _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , tx _ _ _}     refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , sndack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , rcvack _ _ _} refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , ack _ _ _}    refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiKA _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiCS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiBF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiTS _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiLN _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , apiLF _ _ _}  refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rE (sVis {at = _ , break _}      refl ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rF (sRet refl) =
  _ , wev (τ*-step (sSil refl) τ*-refl) (sRet refl) τ*-refl , rH
kasBwdE (F.suc (F.suc (F.suc F.zero))) rF (sVis () _)
kasBwdE (F.suc (F.suc (F.suc F.zero))) rG (sRet refl) = _ , wev τ*-refl (sRet refl) τ*-refl , rH
kasBwdE (F.suc (F.suc (F.suc F.zero))) rG (sVis () _)
kasBwdE (F.suc (F.suc (F.suc F.zero))) rH (sRet ())
kasBwdE (F.suc (F.suc (F.suc F.zero))) rH (sVis refl ())
-- rA: spec ksClient — the two wire-output edges; impl home state fires directly
-- rB: spec ksResp — impl (sil state) pre-τs to the response node, then fires
-- rC: spec ksResp — impl response node fires directly
-- rD: spec ksClient — impl (sil state) pre-τs home, then fires
-- rE: spec ksDdone — the done edge; impl done node fires directly
-- rF: spec ksTerm (√) — impl pre-τs to its ret state, then √s
-- rG: spec ksTerm (√) — impl ret state √s directly
-- rH: deadlock offers nothing

-- backward τ simulation: the spec is τ-free (vacuous)
kasBwdT : (l : Link) → ∀ {p q q′} → KASRel l p q → q ─[ τ ]─► q′
        → Σ[ p′ ∈ NetTree ] ((p ═[ τ ]═► p′) × KASRel l p′ q′)
kasBwdT l rA     st = ⊥-elim (specNoτ l ksClient st)
kasBwdT l (rB c) st = ⊥-elim (specNoτ l (ksResp c) st)
kasBwdT l (rC c) st = ⊥-elim (specNoτ l (ksResp c) st)
kasBwdT l rD     st = ⊥-elim (specNoτ l ksClient st)
kasBwdT l rE     st = ⊥-elim (specNoτ l ksDdone st)
kasBwdT l rF     st = ⊥-elim (specNoτ l ksTerm st)
kasBwdT l rG     st = ⊥-elim (specNoτ l ksTerm st)
kasBwdT l rH     (sSil ())
kasBwdT l rH     (sTau refl ())

-- the impl never diverges: stable states have no τ; sil states τ once into a stable one
kasNdivL : (l : Link) → ∀ {p q} → KASRel l p q → Diverges p → ⊥
kasNdivL l rA     dv = noτ-ib l (kSrv l stClient) refl (dv .Diverges.step)
kasNdivL l (rB c) dv with dv .Diverges.next | dv .Diverges.step | dv .Diverges.rest
... | _ | sSil refl | rest = noτ-ib l (kSrv l (stServer c)) refl (rest .Diverges.step)
... | _ | sTau () _ | _
kasNdivL l (rC c) dv = noτ-ib l (kSrv l (stServer c)) refl (dv .Diverges.step)
kasNdivL l rD     dv with dv .Diverges.next | dv .Diverges.step | dv .Diverges.rest
... | _ | sSil refl | rest = noτ-ib l (kSrv l stClient) refl (rest .Diverges.step)
... | _ | sTau () _ | _
kasNdivL l rE     dv = noτ-ib l (SrcOp.Prefix₀ (doneKA l hi) (SrcOp.Ret (inj₁ stDone))) refl (dv .Diverges.step)
kasNdivL l rF     dv with dv .Diverges.next | dv .Diverges.step | dv .Diverges.rest
... | _ | sSil refl | rest = noτ-ret l (rest .Diverges.step)
... | _ | sTau () _ | _
kasNdivL l rG     dv = noτ-ret l (dv .Diverges.step)
kasNdivL l rH     dv = deadlock-no-τ (dv .Diverges.step)

-- the spec never diverges: it is τ-free at every position
kasNdivR : (l : Link) → ∀ {p q} → KASRel l p q → Diverges q → ⊥
kasNdivR l rA     dv = specNoτ l ksClient (dv .Diverges.step)
kasNdivR l (rB c) dv = specNoτ l (ksResp c) (dv .Diverges.step)
kasNdivR l (rC c) dv = specNoτ l (ksResp c) (dv .Diverges.step)
kasNdivR l rD     dv = specNoτ l ksClient (dv .Diverges.step)
kasNdivR l rE     dv = specNoτ l ksDdone (dv .Diverges.step)
kasNdivR l rF     dv = specNoτ l ksTerm (dv .Diverges.step)
kasNdivR l rG     dv = specNoτ l ksTerm (dv .Diverges.step)
kasNdivR l rH     dv = deadlock-no-τ (dv .Diverges.step)

-- the coinduction principle instantiated with the KA-server relation
module KASDR (l : Link) = DRFromRel (KASRel l) (kasFwdE l) (kasFwdT l) (kasBwdE l) (kasBwdT l) (kasNdivL l) (kasNdivR l)

-- THE FIRST PEER BISIM: the renamed KA server iter ≈DR its τ-free spec table
kaServer≈DRhi : (l : Link) → KAserverA l hi ≈DR kaServerSpec l hi
kaServer≈DRhi l = KASDR.rel→dr l rA

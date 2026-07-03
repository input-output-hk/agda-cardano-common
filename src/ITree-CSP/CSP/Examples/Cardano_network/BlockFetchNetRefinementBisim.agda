{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Task 4 (network), part 3: BFnetSpec ∖ bfMsgES ≈DR networkBF ∖ ioBF,
-- DIRECTLY as a divergence-respecting weak bisimulation.
--
-- Mirrors `BlockFetchAbsRefinementBisim` (the abstract single-hop version),
-- but the network routes every BlockFetch message through a COPY MEDIUM, so
-- each abstract single hidden `bfMsg` rendezvous becomes a TWO-hop cascade in
-- the network:  peer sends `bfIn!m` → copy holds (`Chold m`) → copy sends
-- `bfOut!m` → receiving peer + copy loop-backs.  The transition oracle
-- (`JN-τ-cases`, `JN-ev-apiBF`, the per-config `netX-τ` inversions and the
-- per-config `nd-*` divergence-freedom lemmas) is reused verbatim from
-- `BlockFetchNetRefinement` (part 1); `net-noDiv` from part 2; `spec3-noDiv`
-- from part 1.
--
-- Orientation (mirrors the abstract): `RState W S` relates a NETWORK config
-- `W` to a SPEC-hidden state `S`; `mkDR rsInit : (networkBF ∖ ioBF) ≈DR
-- (BFnetSpec ∖ bfMsgES)`, and the goal follows by `drbisim-sym`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.BlockFetchNetRefinementBisim (p : Params) where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; ≡-≟-identity)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

open import CSP.Examples.Cardano_network.BlockFetch p
open import CSP.Examples.Cardano_network.Net p
  using ( ApiBFTag; ApiBFCar
        ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch
        ; sendBFNoBlocks; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange )
open import CSP.Examples.Cardano_network.Data p using (ChainRange; DecEq-ChainRange)
open Params p

open import Semantics.LTS {E = BFNetEv} {I = ExtI BFNetEv}
open import Semantics.WeakBisim {E = BFNetEv} {I = ExtI BFNetEv}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF; τ*-trans)
open import Semantics.DRBisim {E = BFNetEv} {I = ExtI BFNetEv}
  using (Diverges; DRbisim; _≈DR_; drbisim-sym; deadlock-converges)
open import Semantics.FailuresDivergences {E = BFNetEv} {I = ExtI BFNetEv}
  using (_⊑FD_; _≈FD_)
open import Semantics.DRImpliesFD {E = BFNetEv} {I = ExtI BFNetEv}
  using (drbisim→≈FD)

-- the hide / parallel single-step INTRO builders (to construct spec / network
-- steps) and the ELIM lemmas (to invert spec-side visible steps), at the
-- network alphabet.  Part 1 imports these privately, so we re-import here.
open import CSP.Laws.Traces.TraceLawsHide BFNetEv-≟
  using (Hide-τ; Hide-keep; Hide-hidden; Hide-√
        ; Hide-τ-elim; hτP; hτH
        ; Hide-ev-elim; heV; he√)
open import CSP.Laws.Traces.TraceLawsParallel BFNetEv-≟
  using (Par-τ-L; Par-τ-R; Par-sync; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsParallelElim BFNetEv-≟
  using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR; evBoth; ev√)

-- the committed network transition oracle (part 1): JN-τ-cases / JN-ev-apiBF,
-- the per-config netX-τ inversions, the per-config nd-* divergence lemmas, the
-- spec states IT / S-loop / S-req / …, spec3-noDiv, and the joint configs.
open import CSP.Examples.Cardano_network.BlockFetchNetRefinement p
-- net-noDiv (part 2): the hidden network is divergence-free at every reach.
-- DEV-DECOUPLE: part 2 (net-noDiv) has no cached interface and is very slow to
-- cold-typecheck, so during development it is stubbed locally (see the
-- `net-noDiv` DEV-STUB near the builders) and this import is restored only for
-- the final full verify.  The RState CARRIER below does not use net-noDiv at
-- all (it is needed only in mkDR's div→ field), so the carrier increment checks
-- against part 1 (cached) alone.
-- open import CSP.Examples.Cardano_network.BlockFetchNetRefinementNet p using (net-noDiv)

open NetOps using (_∖_; Par⊤; Par; iter; iter-bind; Ret; Output; Prefix; Prefix₀; pchoice; Skip; loop0; loop; _⦀_; _∥⇘_⇙_; _>>=_; ∅ES; viewV; EventSet)
open DRbisim
open WSimF

------------------------------------------------------------------------
-- The (multi-valued) bisimulation relation, NETWORK config `W` ↔ SPEC-hidden
-- state `S`.  One constructor per GFP-related pair.  The network's two-hop
-- copy medium means each spec message-τ corresponds to a CASCADE of network
-- τ's, so a single spec state relates to several network configs (the
-- copy-hold / copy-drain interleavings).
--
-- NOTE (increment boundary — see the module report): the control phase is
-- NOT independently closed.  From the initial idle config the reachability
-- runs  idle → request-hop → both-busy → startBatch-hop → STREAMING, and the
-- guarded builder `mkDR` must be total over every constructor it transitively
-- references.  Hence the streaming constructors below cannot be omitted from a
-- file that also defines `mkDR` on `rsIdle`.  This first increment therefore
-- ships the RState CARRIER for the control phase (this data declaration, which
-- typechecks on its own) plus the reusable oracle wiring; the `mkDR`/`mkDRˢ`
-- builders are added together with the streaming constructors in the next
-- increment (they cannot be split — see report items (c),(d)).
------------------------------------------------------------------------
data RState : PTree BFNetEv (ExtI BFNetEv) Rr
            → PTree BFNetEv (ExtI BFNetEv) Rr → Set₁ where
  -- ── idle / done stable configs ──────────────────────────────────────────
  -- both peers idle, copy idle ↔ spec nIdle (this is the initial pair).
  rsIdle : RState (JN (Inner (ICn stIdle) (ISn stIdle)) Cidle)  (IT nIdle ∖ bfMsgES)
  -- both peers done, copy idle ↔ spec nDone (terminal).
  rsDone : RState (JN (Inner (ICn stDone) (ISn stDone)) Cidle)  (IT nDone ∖ bfMsgES)

  -- ── request hop: client idle→busy, message routed through the copy ───────
  -- each network config below is weakly ≈ the spec S-req r (before its bfMsg)
  -- or S-req2 r (after its bfMsg, offering reqBFRange); see part-1 netB..netB6.
  -- B  : client send-hold, copy idle ↔ S-req r.
  rsReqB  : ∀ r → RState (JN (Inner (CB-req r) (ISn stIdle)) Cidle)                   (S-req r ∖ bfMsgES)
  -- Bh : client looped, copy holds mRequestRange r ↔ S-req r.
  rsReqBh : ∀ r → RState (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r))) (S-req r ∖ bfMsgES)
  -- B2 : client back to busy, copy holds ↔ S-req r.
  rsReqB2 : ∀ r → RState (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)))     (S-req r ∖ bfMsgES)
  -- B3 : server got notify (SB-req r), copy draining (Cret) ↔ S-req2 r.
  rsReqB3 : ∀ r → RState (JN (Inner (CB-loop stBusy) (SB-req r)) Cret)                (S-req2 r ∖ bfMsgES)
  -- B4 : client looped, copy draining ↔ S-req2 r.
  rsReqB4 : ∀ r → RState (JN (Inner (ICn stBusy) (SB-req r)) Cret)                    (S-req2 r ∖ bfMsgES)
  -- B5 : server notify pending, copy drained ↔ S-req2 r.
  rsReqB5 : ∀ r → RState (JN (Inner (CB-loop stBusy) (SB-req r)) Cidle)               (S-req2 r ∖ bfMsgES)
  -- B6 : client looped, copy idle, server about to fire reqBFRange ↔ S-req2 r.
  rsReqB6 : ∀ r → RState (JN (Inner (ICn stBusy) (SB-req r)) Cidle)                   (S-req2 r ∖ bfMsgES)

  -- ── both busy stable config ↔ spec nBusy ─────────────────────────────────
  rsBusy : RState (JN (Inner (ICn stBusy) (ISn stBusy)) Cidle)  (IT nBusy ∖ bfMsgES)

  -- ── clientDone hop: client idle→done, message routed through the copy ─────
  -- Cd  : client send-hold mClientDone, copy idle ↔ S-cdone.
  rsCd  : RState (JN (Inner CB-cdone (ISn stIdle)) Cidle)                 (S-cdone ∖ bfMsgES)
  -- Cdh : client looped, copy holds mClientDone ↔ S-cdone.
  rsCdh : RState (JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone)) (S-cdone ∖ bfMsgES)
  -- Cd2 : client done, copy holds mClientDone ↔ S-cdone.
  rsCd2 : RState (JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone))     (S-cdone ∖ bfMsgES)
  -- CdR : server done (SB-loop stDone), copy draining (Cret) ↔ S-loop nDone.
  rsCdR : RState (JN (Inner (ICn stDone) (SB-loop stDone)) Cret)          (S-loop nDone ∖ bfMsgES)

  -- ── request re-issue while a prior round still drains the copy/server ─────
  -- client committed to a fresh request (CB-req r) before the copy/server of the
  -- previous round settled; still pre-delivery ↔ S-req r.
  -- ReqR  : client send-hold, copy draining ↔ S-req r.
  rsReqR  : ∀ r → RState (JN (Inner (CB-req r) (ISn stIdle)) Cret)               (S-req r ∖ bfMsgES)
  -- ReqSi : client send-hold, server looping to idle, copy idle ↔ S-req r.
  rsReqSi : ∀ r → RState (JN (Inner (CB-req r) (SB-loop stIdle)) Cidle)          (S-req r ∖ bfMsgES)
  -- ReqSr : client send-hold, server looping to idle, copy draining ↔ S-req r.
  rsReqSr : ∀ r → RState (JN (Inner (CB-req r) (SB-loop stIdle)) Cret)           (S-req r ∖ bfMsgES)
  -- IBSirr: request still in copy, server looping to idle, client busy ↔ S-req r.
  rsIBSirr : ∀ r → RState (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r))) (S-req r ∖ bfMsgES)
  -- LbBh  : request still in copy, both looping (client busy / server idle) ↔ S-req r.
  rsLbBh : ∀ r → RState (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r))) (S-req r ∖ bfMsgES)

  -- ── both-busy region (request delivered, reqBFRange fired) ────────────────
  -- server settled (ISn stBusy) → offers the busy choices ↔ IT nBusy;
  -- server looping (SB-loop stBusy) → nothing offered yet ↔ S-loop nBusy.
  -- G7 : both busy, copy draining ↔ nBusy.
  rsG7 : RState (JN (Inner (ICn stBusy) (ISn stBusy)) Cret)          (IT nBusy ∖ bfMsgES)
  -- I  : client looping, server busy, copy idle ↔ nBusy.
  rsBI : RState (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle)     (IT nBusy ∖ bfMsgES)
  -- G5 : client looping, server busy, copy draining ↔ nBusy.
  rsG5 : RState (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret)      (IT nBusy ∖ bfMsgES)
  -- Fl : server looping, copy idle ↔ S-loop nBusy.
  rsFl : RState (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle)     (S-loop nBusy ∖ bfMsgES)
  -- G3a: server looping, copy draining ↔ S-loop nBusy.
  rsG3a : RState (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret)     (S-loop nBusy ∖ bfMsgES)
  -- G3 : both looping, copy draining ↔ S-loop nBusy.
  rsG3 : RState (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret)  (S-loop nBusy ∖ bfMsgES)
  -- G6 : both looping, copy idle ↔ S-loop nBusy.
  rsG6 : RState (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle) (S-loop nBusy ∖ bfMsgES)

  -- ── clientDone still in flight (server not yet done) ↔ S-cdone ────────────
  -- CdR  : client send-hold, copy draining ↔ S-cdone.
  rsCdRi : RState (JN (Inner CB-cdone (ISn stIdle)) Cret)                        (S-cdone ∖ bfMsgES)
  -- CdSi : client send-hold, server looping to idle, copy idle ↔ S-cdone.
  rsCdSi : RState (JN (Inner CB-cdone (SB-loop stIdle)) Cidle)                   (S-cdone ∖ bfMsgES)
  -- CdSr : client send-hold, server looping to idle, copy draining ↔ S-cdone.
  rsCdSr : RState (JN (Inner CB-cdone (SB-loop stIdle)) Cret)                    (S-cdone ∖ bfMsgES)
  -- IDScd: mClientDone in copy, server looping to idle, client done ↔ S-cdone.
  rsIDScd : RState (JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone)) (S-cdone ∖ bfMsgES)
  -- LdCdh: mClientDone in copy, server looping to idle, client looping ↔ S-cdone.
  rsLdCdh : RState (JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone)) (S-cdone ∖ bfMsgES)

  -- ── done region (clientDone delivered, both peers heading to nDone) ───────
  -- both settled (ICn stDone / ISn stDone) ↔ IT nDone; else ↔ S-loop nDone.
  -- Cd7: both done, copy draining ↔ nDone.
  rsCd7 : RState (JN (Inner (ICn stDone) (ISn stDone)) Cret)         (IT nDone ∖ bfMsgES)
  -- Cd3: both looping to done, copy draining ↔ S-loop nDone.
  rsCd3 : RState (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret) (S-loop nDone ∖ bfMsgES)
  -- Cd5: client looping, server done, copy draining ↔ S-loop nDone.
  rsCd5 : RState (JN (Inner (CB-loop stDone) (ISn stDone)) Cret)     (S-loop nDone ∖ bfMsgES)
  -- Cd6: both looping, copy idle ↔ S-loop nDone.
  rsCd6 : RState (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle) (S-loop nDone ∖ bfMsgES)
  -- Cd8: server looping to done, copy idle ↔ S-loop nDone.
  rsCd8 : RState (JN (Inner (ICn stDone) (SB-loop stDone)) Cidle)    (S-loop nDone ∖ bfMsgES)
  -- Cd9: client looping, server done, copy idle ↔ S-loop nDone.
  rsCd9 : RState (JN (Inner (CB-loop stDone) (ISn stDone)) Cidle)    (S-loop nDone ∖ bfMsgES)

  -- ── noBlocks hop: server busy→idle, message routed through the copy ───────
  --   server sends noBlocks; until the client receives it the spec offers
  --   nothing ↔ S-noblk (→ S-loop nIdle → nIdle).  After delivery the client
  --   returns to idle (the idle-return region below).
  -- N   : server send-hold noBlocks, copy idle ↔ S-noblk.
  rsN   : RState (JN (Inner (ICn stBusy) SB-noblk) Cidle)                        (S-noblk ∖ bfMsgES)
  -- IBNr: server send-hold noBlocks, copy draining ↔ S-noblk.
  rsIBNr : RState (JN (Inner (ICn stBusy) SB-noblk) Cret)                        (S-noblk ∖ bfMsgES)
  -- LbNi: server send-hold noBlocks, client looping, copy idle ↔ S-noblk.
  rsLbNi : RState (JN (Inner (CB-loop stBusy) SB-noblk) Cidle)                   (S-noblk ∖ bfMsgES)
  -- LbNr: server send-hold noBlocks, client looping, copy draining ↔ S-noblk.
  rsLbNr : RState (JN (Inner (CB-loop stBusy) SB-noblk) Cret)                    (S-noblk ∖ bfMsgES)
  -- Nh  : mNoBlocks in copy, server looping to idle, client busy ↔ S-noblk.
  rsNh  : RState (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks))    (S-noblk ∖ bfMsgES)
  -- N2  : mNoBlocks in copy, server idle, client busy ↔ S-noblk.
  rsN2  : RState (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks))        (S-noblk ∖ bfMsgES)
  -- LbNh: mNoBlocks in copy, server looping to idle, client looping ↔ S-noblk.
  rsLbNh : RState (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks)) (S-noblk ∖ bfMsgES)
  -- LbN2: mNoBlocks in copy, server idle, client looping ↔ S-noblk.
  rsLbN2 : RState (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks))   (S-noblk ∖ bfMsgES)

  -- ── idle-return region (noBlocks delivered; both peers at idle) ───────────
  -- client is the idle driver: client settled (ICn stIdle) ↔ IT nIdle;
  -- client looping (CB-loop stIdle) ↔ S-loop nIdle.
  -- N4: client idle, server looping, copy draining ↔ nIdle.
  rsN4 : RState (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret)      (IT nIdle ∖ bfMsgES)
  -- N7: both idle, copy draining ↔ nIdle.
  rsN7 : RState (JN (Inner (ICn stIdle) (ISn stIdle)) Cret)          (IT nIdle ∖ bfMsgES)
  -- N8: client idle, server looping, copy idle ↔ nIdle.
  rsN8 : RState (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle)     (IT nIdle ∖ bfMsgES)
  -- N3: both looping, copy draining ↔ S-loop nIdle.
  rsN3 : RState (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret)  (S-loop nIdle ∖ bfMsgES)
  -- N5: client looping, server idle, copy draining ↔ S-loop nIdle.
  rsN5 : RState (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret)      (S-loop nIdle ∖ bfMsgES)
  -- N6: both looping, copy idle ↔ S-loop nIdle.
  rsN6 : RState (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle) (S-loop nIdle ∖ bfMsgES)
  -- N9: client looping, server idle, copy idle ↔ S-loop nIdle.
  rsN9 : RState (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle)     (S-loop nIdle ∖ bfMsgES)

  -- ── startBatch hop: server busy→streaming, message routed through copy ────
  --   the transition to streaming is SERVER-SIDE: while the server is still
  --   send-holding startBatch (SB-sbatch) the spec is S-sbatch; once the server
  --   has moved to stStreaming (startBatch now in copy en route to the client)
  --   the server already offers the empty-buffer streaming choices ↔ nStr0.
  -- M   : server send-hold startBatch, copy idle ↔ S-sbatch.
  rsM   : RState (JN (Inner (ICn stBusy) SB-sbatch) Cidle)                       (S-sbatch ∖ bfMsgES)
  -- IBMr: server send-hold startBatch, copy draining ↔ S-sbatch.
  rsIBMr : RState (JN (Inner (ICn stBusy) SB-sbatch) Cret)                       (S-sbatch ∖ bfMsgES)
  -- LbMi: server send-hold startBatch, client looping, copy idle ↔ S-sbatch.
  rsLbMi : RState (JN (Inner (CB-loop stBusy) SB-sbatch) Cidle)                  (S-sbatch ∖ bfMsgES)
  -- LbMr: server send-hold startBatch, client looping, copy draining ↔ S-sbatch.
  rsLbMr : RState (JN (Inner (CB-loop stBusy) SB-sbatch) Cret)                   (S-sbatch ∖ bfMsgES)
  -- M2  : mStartBatch in copy, server streaming (settled), client busy ↔ nStr0.
  rsSbM2 : RState (JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch)) (IT nStr0 ∖ bfMsgES)
  -- LbM2: mStartBatch in copy, server streaming (settled), client looping ↔ nStr0.
  rsLbM2 : RState (JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch)) (IT nStr0 ∖ bfMsgES)
  -- Mh  : mStartBatch in copy, server looping to streaming, client busy ↔ S-loop nStr0.
  rsMh  : RState (JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch)) (S-loop nStr0 ∖ bfMsgES)
  -- LbMh: mStartBatch in copy, server looping to streaming, client looping ↔ S-loop nStr0.
  rsLbMh : RState (JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch)) (S-loop nStr0 ∖ bfMsgES)

  -- ── streaming, empty buffer (nStr0) ──────────────────────────────────────
  -- server is the streaming driver: server settled (ISn stStreaming) ↔ IT nStr0;
  -- server looping (SB-loop stStreaming) ↔ S-loop nStr0.
  -- V0: both settled streaming, copy idle ↔ nStr0.
  rsV0 : RState (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle)          (IT nStr0 ∖ bfMsgES)
  -- M7: both settled, copy draining ↔ nStr0.
  rsM7 : RState (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret)           (IT nStr0 ∖ bfMsgES)
  -- M9: client looping, server settled, copy idle ↔ nStr0.
  rsM9 : RState (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle)      (IT nStr0 ∖ bfMsgES)
  -- M5: client looping, server settled, copy draining ↔ nStr0.
  rsM5 : RState (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret)       (IT nStr0 ∖ bfMsgES)
  -- M4: server looping, copy draining ↔ S-loop nStr0.
  rsM4 : RState (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret)       (S-loop nStr0 ∖ bfMsgES)
  -- M8: server looping, copy idle ↔ S-loop nStr0.
  rsM8 : RState (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle)      (S-loop nStr0 ∖ bfMsgES)
  -- M3: both looping, copy draining ↔ S-loop nStr0.
  rsM3 : RState (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret)   (S-loop nStr0 ∖ bfMsgES)
  -- M6: both looping, copy idle ↔ S-loop nStr0.
  rsM6 : RState (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle)  (S-loop nStr0 ∖ bfMsgES)
  -- M9′: same config as rsM9, GFP-closure duplicate of rsM9 (τ-adjacent witness
  -- S-loop nStr0, reached when the head is delivered from IT (nStr1 b) → S-loop nStr0).
  rsM9′ : RState (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle)      (S-loop nStr0 ∖ bfMsgES)
  -- M5′: same config as rsM5, GFP-closure duplicate of rsM5 (τ-adjacent witness S-loop nStr0).
  rsM5′ : RState (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret)       (S-loop nStr0 ∖ bfMsgES)

  -- ── streaming, occupancy 1 — block held at the CLIENT slot (deliverable) ──
  -- client head CB-blk b offers recvBFBlock b ↔ nStr1 b; server settled ↔ IT,
  -- server looping ↔ S-loop.
  -- Vocc1: client head, server settled, copy idle ↔ nStr1 b.
  rsVocc1 : ∀ b → RState (JN (Inner (CB-blk b) (ISn stStreaming)) Cidle)        (IT (nStr1 b) ∖ bfMsgES)
  -- W4   : client head, server settled, copy draining ↔ nStr1 b.
  rsW4 : ∀ b → RState (JN (Inner (CB-blk b) (ISn stStreaming)) Cret)            (IT (nStr1 b) ∖ bfMsgES)
  -- W4′: same config as rsW4, GFP-closure duplicate of rsW4 (τ-adjacent witness
  -- S-loop (nStr1 b), reached when the block is delivered from S-blk0 b).
  rsW4′ : ∀ b → RState (JN (Inner (CB-blk b) (ISn stStreaming)) Cret)           (S-loop (nStr1 b) ∖ bfMsgES)
  -- W5   : client head, server looping, copy idle ↔ S-loop (nStr1 b).
  rsW5 : ∀ b → RState (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle)       (S-loop (nStr1 b) ∖ bfMsgES)
  -- W3   : client head, server looping, copy draining ↔ S-loop (nStr1 b).
  rsW3 : ∀ b → RState (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret)        (S-loop (nStr1 b) ∖ bfMsgES)

  -- ── streaming, occupancy 1 — block still IN FLIGHT (copy or server slot) ──
  -- the head is not yet at the client, so the block is buffer-filling ↔ S-blk0 b.
  -- W  : block at server slot, client/server idle-streaming, copy idle ↔ S-blk0 b.
  rsW  : ∀ b → RState (JN (Inner (ICn stStreaming) (SB-blk b)) Cidle)           (S-blk0 b ∖ bfMsgES)
  -- WX1: block at server slot, client looping, copy idle ↔ S-blk0 b.
  rsWX1 : ∀ b → RState (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle)      (S-blk0 b ∖ bfMsgES)
  -- WX3: block at server slot, client looping, copy draining ↔ S-blk0 b.
  rsWX3 : ∀ b → RState (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret)       (S-blk0 b ∖ bfMsgES)
  -- WX3a: block at server slot, client streaming, copy draining ↔ S-blk0 b.
  rsWX3a : ∀ b → RState (JN (Inner (ICn stStreaming) (SB-blk b)) Cret)          (S-blk0 b ∖ bfMsgES)
  -- W2 : block in copy slot, both settled streaming ↔ S-blk0 b.
  rsW2 : ∀ b → RState (JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b))) (S-blk0 b ∖ bfMsgES)
  -- Wh : block in copy slot, server looping, client streaming ↔ S-blk0 b.
  rsWh : ∀ b → RState (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) (S-blk0 b ∖ bfMsgES)
  -- W2d: block in copy slot, client looping, server settled ↔ S-blk0 b.
  rsW2d : ∀ b → RState (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b))) (S-blk0 b ∖ bfMsgES)
  -- WX2: block in copy slot, both looping ↔ S-blk0 b.
  rsWX2 : ∀ b → RState (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) (S-blk0 b ∖ bfMsgES)

  -- ── streaming, occupancy 2 — client holds head; second block copy/server ─
  -- head b at client ↔ nStr2 b b′ (head b, then b′); server settled ↔ IT,
  -- server looping ↔ S-loop.
  -- W2a: client head b, copy b′, server settled ↔ nStr2 b b′.
  rsW2a : ∀ b b′ → RState (JN (Inner (CB-blk b) (ISn stStreaming)) (Chold (mBlock b′))) (IT (nStr2 b b′) ∖ bfMsgES)
  -- W2h: client head b, copy b′, server looping ↔ S-loop (nStr2 b b′).
  rsW2h : ∀ b b′ → RState (JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′))) (S-loop (nStr2 b b′) ∖ bfMsgES)
  -- W2e: client head b, server slot b′, copy idle ↔ nStr2 b b′.
  rsW2e : ∀ b b′ → RState (JN (Inner (CB-blk b) (SB-blk b′)) Cidle)             (IT (nStr2 b b′) ∖ bfMsgES)
  -- W3b: client head b, server slot b′, copy draining ↔ nStr2 b b′.
  rsW3b : ∀ b b′ → RState (JN (Inner (CB-blk b) (SB-blk b′)) Cret)              (IT (nStr2 b b′) ∖ bfMsgES)

  -- ── streaming, occupancy 2 — head NOT at client (copy b + server b′) ──────
  -- buffer filling with two blocks in flight, head b in copy ahead of b′ ↔ S-blk1 b b′.
  -- W3a: copy b, server b′, client streaming ↔ S-blk1 b b′.
  rsW3a : ∀ b b′ → RState (JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b))) (S-blk1 b b′ ∖ bfMsgES)
  -- W3d: copy b, server b′, client looping ↔ S-blk1 b b′.
  rsW3d : ∀ b b′ → RState (JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b))) (S-blk1 b b′ ∖ bfMsgES)

  -- ── streaming, occupancy 3 (saturated: all three slots full) ──────────────
  -- client head b, copy b′, server b″ ↔ nStr3 b b′ b″.
  rsW3e : ∀ b b′ b″ → RState (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))) (IT (nStr3 b b′ b″) ∖ bfMsgES)

  -- ── startBatch cascade with a block/batchDone already queued behind it ────
  -- the server has moved past startBatch (still in copy) and produced the next
  -- server-side event; the buffer content picks the spec state.
  -- IBblksb: mStartBatch in copy, server holds a block ↔ S-blk0 b.
  rsIBblksb : ∀ b → RState (JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch)) (S-blk0 b ∖ bfMsgES)
  -- LbBLKsb: mStartBatch in copy, client looping, server holds a block ↔ S-blk0 b.
  rsLbBLKsb : ∀ b → RState (JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch)) (S-blk0 b ∖ bfMsgES)
  -- IBbdsb : mStartBatch in copy, server send-hold batchDone (empty batch) ↔ S-bd0.
  rsIBbdsb : RState (JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch))      (S-bd0 ∖ bfMsgES)
  -- LbBDsb : mStartBatch in copy, client looping, server send-hold batchDone ↔ S-bd0.
  rsLbBDsb : RState (JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch))  (S-bd0 ∖ bfMsgES)

  -- ── batch-done, buffer EMPTY (drains silently to idle) ↔ S-bd0 ────────────
  -- BD0e : server send-hold batchDone, copy idle ↔ S-bd0.
  rsBD0e : RState (JN (Inner (ICn stStreaming) SB-bdone) Cidle)                 (S-bd0 ∖ bfMsgES)
  -- BD0a : mBatchDone in copy, server idle, client streaming ↔ S-bd0.
  rsBD0a : RState (JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone)) (S-bd0 ∖ bfMsgES)
  -- BD0h : mBatchDone in copy, server looping to idle, client streaming ↔ S-bd0.
  rsBD0h : RState (JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) (S-bd0 ∖ bfMsgES)
  -- BX1  : server send-hold batchDone, client looping, copy idle ↔ S-bd0.
  rsBX1 : RState (JN (Inner (CB-loop stStreaming) SB-bdone) Cidle)              (S-bd0 ∖ bfMsgES)
  -- BX2  : mBatchDone in copy, client looping, server looping to idle ↔ S-bd0.
  rsBX2 : RState (JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) (S-bd0 ∖ bfMsgES)
  -- BX3  : server send-hold batchDone, client looping, copy draining ↔ S-bd0.
  rsBX3 : RState (JN (Inner (CB-loop stStreaming) SB-bdone) Cret)               (S-bd0 ∖ bfMsgES)
  -- BX3a : server send-hold batchDone, client streaming, copy draining ↔ S-bd0.
  rsBX3a : RState (JN (Inner (ICn stStreaming) SB-bdone) Cret)                  (S-bd0 ∖ bfMsgES)
  -- BD1d : mBatchDone in copy, client looping, server idle (empty) ↔ S-bd0.
  rsBD1d : RState (JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone)) (S-bd0 ∖ bfMsgES)

  -- ── batch-done drain, occupancy 1 — head at CLIENT slot ↔ nStrD1 b ────────
  -- BD1a: client head b, mBatchDone in copy, server idle ↔ nStrD1 b.
  rsBD1a : ∀ b → RState (JN (Inner (CB-blk b) (ISn stIdle)) (Chold mBatchDone)) (IT (nStrD1 b) ∖ bfMsgES)
  -- BD1e: client head b, server send-hold batchDone, copy idle ↔ nStrD1 b.
  rsBD1e : ∀ b → RState (JN (Inner (CB-blk b) SB-bdone) Cidle)                  (IT (nStrD1 b) ∖ bfMsgES)
  -- BD1h: client head b, mBatchDone in copy, server looping to idle ↔ nStrD1 b.
  rsBD1h : ∀ b → RState (JN (Inner (CB-blk b) (SB-loop stIdle)) (Chold mBatchDone)) (IT (nStrD1 b) ∖ bfMsgES)
  -- BD2b: client head b, server send-hold batchDone, copy draining ↔ nStrD1 b.
  rsBD2b : ∀ b → RState (JN (Inner (CB-blk b) SB-bdone) Cret)                   (IT (nStrD1 b) ∖ bfMsgES)

  -- ── batch-done drain, occupancy 1 — block still in copy (not at client) ───
  -- the single buffered block b is still in the copy en route to the client ↔ S-bd1 b.
  -- BD2a: block b in copy, server send-hold batchDone, client streaming ↔ S-bd1 b.
  rsBD2a : ∀ b → RState (JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b))) (S-bd1 b ∖ bfMsgES)
  -- BD2d: block b in copy, server send-hold batchDone, client looping ↔ S-bd1 b.
  rsBD2d : ∀ b → RState (JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b))) (S-bd1 b ∖ bfMsgES)

  -- ── batch-done drain, occupancy 2 — client head b, copy b′ ↔ nStrD2 b b′ ──
  rsBD2e : ∀ b b′ → RState (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))) (IT (nStrD2 b b′) ∖ bfMsgES)

  -- ── drain→idle junction duplicates (batch-done empty drains to nIdle) ──────
  -- The batch-done-empty drain reaches the idle-return CLIENT-LOOPING configs
  -- (rsN3/N5/N6/N9 ↔ S-loop nIdle) while the SPEC is still at the drain state
  -- IT nStrD0 (whose only τ lands IT nIdle).  These GFP-closure duplicates pair
  -- those same idle configs with IT nStrD0 (τ-adjacent: IT nStrD0 →τ→ IT nIdle).
  rsN3D0 : RState (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret)  (IT nStrD0 ∖ bfMsgES)
  rsN5D0 : RState (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret)      (IT nStrD0 ∖ bfMsgES)
  rsN6D0 : RState (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle) (IT nStrD0 ∖ bfMsgES)
  rsN9D0 : RState (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle)     (IT nStrD0 ∖ bfMsgES)
  -- S-loop nStrD0 layer: the bfMsg(mBatchDone) is consumed by the client (bfOut)
  -- exactly at BD0h→N3 / BD0a→N5, where the spec is at S-loop nStrD0 (one τ before
  -- IT nStrD0).  These pair those two configs with S-loop nStrD0.
  rsN3D0s : RState (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret) (S-loop nStrD0 ∖ bfMsgES)
  rsN5D0s : RState (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret)     (S-loop nStrD0 ∖ bfMsgES)
  -- S-loop nStrD0 twins of the S-bd0 configs: reached when the occ-1 batch-done
  -- head is delivered (recvBFBlock) from IT (nStrD1 b) → S-loop nStrD0; the net
  -- lands an S-bd0 config while the spec has already advanced to S-loop nStrD0.
  rsBD0eD0s : RState (JN (Inner (ICn stStreaming) SB-bdone) Cidle)                 (S-loop nStrD0 ∖ bfMsgES)
  rsBD0hD0s : RState (JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) (S-loop nStrD0 ∖ bfMsgES)
  rsBD0aD0s : RState (JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone))    (S-loop nStrD0 ∖ bfMsgES)
  rsBX1D0s  : RState (JN (Inner (CB-loop stStreaming) SB-bdone) Cidle)             (S-loop nStrD0 ∖ bfMsgES)
  rsBX2D0s  : RState (JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) (S-loop nStrD0 ∖ bfMsgES)
  rsBX3D0s  : RState (JN (Inner (CB-loop stStreaming) SB-bdone) Cret)              (S-loop nStrD0 ∖ bfMsgES)
  rsBX3aD0s : RState (JN (Inner (ICn stStreaming) SB-bdone) Cret)                  (S-loop nStrD0 ∖ bfMsgES)
  rsBD1dD0s : RState (JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone)) (S-loop nStrD0 ∖ bfMsgES)
  -- S-loop nStrD1 twins of the block-in-copy occ-1 batch-done configs: reached
  -- when the occ-2 batch-done head is delivered (IT (nStrD2 b b′) → S-loop (nStrD1 b′))
  -- and when S-bd1 emits its hidden bfMsg (→ S-loop (nStrD1 b)).
  rsBD2aD1s : ∀ b → RState (JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)))     (S-loop (nStrD1 b) ∖ bfMsgES)
  rsBD2bD1s : ∀ b → RState (JN (Inner (CB-blk b) SB-bdone) Cret)                          (S-loop (nStrD1 b) ∖ bfMsgES)
  rsBD2dD1s : ∀ b → RState (JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b))) (S-loop (nStrD1 b) ∖ bfMsgES)

  -- ── streaming→batch-done bridge: head-at-client + server batchDone, paired ─
  -- with the transient S-bd_k / S-loop nStrD_k (reached from streaming's
  -- sendBFBatchDone at occupancy k; the client still holds a deliverable head).
  rsBD1e′ : ∀ b → RState (JN (Inner (CB-blk b) SB-bdone) Cidle)                  (S-bd1 b ∖ bfMsgES)
  rsBD1eD1s : ∀ b → RState (JN (Inner (CB-blk b) SB-bdone) Cidle)                (S-loop (nStrD1 b) ∖ bfMsgES)
  rsBD2b′ : ∀ b → RState (JN (Inner (CB-blk b) SB-bdone) Cret)                   (S-bd1 b ∖ bfMsgES)
  rsBD2e′ : ∀ b b′ → RState (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))) (S-bd2 b b′ ∖ bfMsgES)
  rsBD2eD2s : ∀ b b′ → RState (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))) (S-loop (nStrD2 b b′) ∖ bfMsgES)

  -- ── streaming occ-1 in-flight S-loop nStr1 twins (block still filling) ─────
  rsW′ : ∀ b → RState (JN (Inner (ICn stStreaming) (SB-blk b)) Cidle)           (S-loop (nStr1 b) ∖ bfMsgES)
  rsWh′ : ∀ b → RState (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) (S-loop (nStr1 b) ∖ bfMsgES)
  rsWX3a′ : ∀ b → RState (JN (Inner (ICn stStreaming) (SB-blk b)) Cret)         (S-loop (nStr1 b) ∖ bfMsgES)
  rsWX1′ : ∀ b → RState (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle)     (S-loop (nStr1 b) ∖ bfMsgES)
  rsWX3′ : ∀ b → RState (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret)      (S-loop (nStr1 b) ∖ bfMsgES)
  rsWX2′ : ∀ b → RState (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) (S-loop (nStr1 b) ∖ bfMsgES)
  rsW2′ : ∀ b → RState (JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b))) (S-loop (nStr1 b) ∖ bfMsgES)
  rsW2d′ : ∀ b → RState (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b))) (S-loop (nStr1 b) ∖ bfMsgES)
  -- ── streaming occ-2 in-flight S-loop nStr2 twins (head in copy) ────────────
  rsW3a′ : ∀ b b′ → RState (JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b))) (S-loop (nStr2 b b′) ∖ bfMsgES)
  rsW3d′ : ∀ b b′ → RState (JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b))) (S-loop (nStr2 b b′) ∖ bfMsgES)
  -- ── streaming sendBFBlock S-blk-transient twins (occ-2 head-at-client) ─────
  rsW2e′ : ∀ b b′ → RState (JN (Inner (CB-blk b) (SB-blk b′)) Cidle)            (S-blk1 b b′ ∖ bfMsgES)
  rsW3b′ : ∀ b b′ → RState (JN (Inner (CB-blk b) (SB-blk b′)) Cret)             (S-blk1 b b′ ∖ bfMsgES)
  -- ── streaming occ-3 saturated twins (S-blk2 transient / S-loop nStr3) ──────
  rsW3e′ : ∀ b b′ b″ → RState (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))) (S-blk2 b b′ b″ ∖ bfMsgES)
  rsW3e″ : ∀ b b′ b″ → RState (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))) (S-loop (nStr3 b b′ b″) ∖ bfMsgES)
  -- W2h config ↔ IT (nStr2 b b′): the settled-IT twin of rsW2h (needed because
  -- rsW2e ↔ IT nStr2 τ-steps to W2h while the spec IT nStr2 is stable).
  rsW2hI : ∀ b b′ → RState (JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′))) (IT (nStr2 b b′) ∖ bfMsgES)

  -- ── terminal deadlock ↔ deadlock ─────────────────────────────────────────
  rsDL : RState deadlock deadlock

------------------------------------------------------------------------
-- Standalone per-constructor weak-simulation helper lemmas (increment 3b).
-- Each RState constructor gets four helpers (fwd/bwd × ev/tau) that invert
-- one transition on the given side and rebuild the matching weak step on the
-- other side, landing in a sibling RState.  They are self-contained (no mkDR
-- yet), so guardedness is irrelevant here.
------------------------------------------------------------------------

-- shorthand for the spec-successor Σ shape used by every helper.
PT : Set₁
PT = PTree BFNetEv (ExtI BFNetEv) Rr

------------------------------------------------------------------------
-- (a) API event-label abbreviations (all apiBF, hence ∉ bfMsgES / ∉ ioBF).
------------------------------------------------------------------------
nReq : ChainRange → Event√ Rr
nReq r = evl (record { A = ApiBFCar sendBFRequestRange ; e = apiBF sendBFRequestRange ; a = r })
nCDone : Event√ Rr
nCDone = evl (record { A = ApiBFCar sendBFClientDone ; e = apiBF sendBFClientDone ; a = tt })
nReqR : ChainRange → Event√ Rr
nReqR r = evl (record { A = ApiBFCar reqBFRange ; e = apiBF reqBFRange ; a = r })
nSBatch : Event√ Rr
nSBatch = evl (record { A = ApiBFCar sendBFStartBatch ; e = apiBF sendBFStartBatch ; a = tt })
nNoBlk : Event√ Rr
nNoBlk = evl (record { A = ApiBFCar sendBFNoBlocks ; e = apiBF sendBFNoBlocks ; a = tt })

------------------------------------------------------------------------
-- (b) SPEC-side api event builders (Hide-keep of the iter offer; api ∉ bfMsgES).
------------------------------------------------------------------------
-- IT nBusy fires sendBFStartBatch → S-sbatch.
sp-nBusy-sbatch : (IT nBusy ∖ bfMsgES) ─[ ev nSBatch ]─► (S-sbatch ∖ bfMsgES)
sp-nBusy-sbatch = Hide-keep bfMsgES (IT nBusy) (λ z → z) (sVis refl refl)
-- IT nBusy fires sendBFNoBlocks → S-noblk.
sp-nBusy-noblk : (IT nBusy ∖ bfMsgES) ─[ ev nNoBlk ]─► (S-noblk ∖ bfMsgES)
sp-nBusy-noblk = Hide-keep bfMsgES (IT nBusy) (λ z → z) (sVis refl refl)

------------------------------------------------------------------------
-- (c) NETWORK-side api event builders (Hide-keep of a nested Par-solo; api ∉ ioBF).
------------------------------------------------------------------------
-- server leaf: ISn stBusy fires sendBFStartBatch → SB-sbatch.
sv-ISbusy-sbatch : ISn stBusy ─[ ev nSBatch ]─► SB-sbatch
sv-ISbusy-sbatch = sVis refl refl
-- server leaf: ISn stBusy fires sendBFNoBlocks → SB-noblk.
sv-ISbusy-noblk : ISn stBusy ─[ ev nNoBlk ]─► SB-noblk
sv-ISbusy-noblk = sVis refl refl
-- server (ISn stBusy) fires sendBFStartBatch solo from the both-busy config.
im-J-sbatch : JN (Inner (ICn stBusy) (ISn stBusy)) Cidle ─[ ev nSBatch ]─► JN (Inner (ICn stBusy) SB-sbatch) Cidle
im-J-sbatch = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cidle) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cidle (λ z → z)
    (Par-soloR ∅ES mrg (ICn stBusy) (ISn stBusy) (λ z → z) sv-ISbusy-sbatch refl) refl)
-- server (ISn stBusy) fires sendBFNoBlocks solo from the both-busy config.
im-J-noblk : JN (Inner (ICn stBusy) (ISn stBusy)) Cidle ─[ ev nNoBlk ]─► JN (Inner (ICn stBusy) SB-noblk) Cidle
im-J-noblk = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cidle) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cidle (λ z → z)
    (Par-soloR ∅ES mrg (ICn stBusy) (ISn stBusy) (λ z → z) sv-ISbusy-noblk refl) refl)

------------------------------------------------------------------------
-- rsDL : deadlock ≈ deadlock.  No transitions on either side.
------------------------------------------------------------------------
rs_DL_fwd_ev : ∀ {l W′} → deadlock ─[ ev l ]─► W′ → Σ[ S′ ∈ PT ] (deadlock ═[ ev l ]═► S′ × RState W′ S′)
rs_DL_fwd_ev (sRet ())
rs_DL_fwd_ev (sVis refl ())
rs_DL_fwd_tau : ∀ {W′} → deadlock ─[ τ ]─► W′ → Σ[ S′ ∈ PT ] (deadlock ═[ τ ]═► S′ × RState W′ S′)
rs_DL_fwd_tau (sSil ())
rs_DL_fwd_tau (sTau refl ())
rs_DL_bwd_ev : ∀ {l S′} → deadlock ─[ ev l ]─► S′ → Σ[ W′ ∈ PT ] (deadlock ═[ ev l ]═► W′ × RState W′ S′)
rs_DL_bwd_ev (sRet ())
rs_DL_bwd_ev (sVis refl ())
rs_DL_bwd_tau : ∀ {S′} → deadlock ─[ τ ]─► S′ → Σ[ W′ ∈ PT ] (deadlock ═[ τ ]═► W′ × RState W′ S′)
rs_DL_bwd_tau (sSil ())
rs_DL_bwd_tau (sTau refl ())

------------------------------------------------------------------------
-- rsBusy : JN (Inner (ICn stBusy) (ISn stBusy)) Cidle  ≈  IT nBusy.
------------------------------------------------------------------------
rs_Busy_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) (ISn stBusy)) Cidle ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((IT nBusy ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Busy_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = ISn stBusy} {cp = Cidle} (ICn-no-bfMsg {stBusy}) (ISn-no-bfMsg {stBusy}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (ISn stBusy) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst with ISbusy-api svst
...       | inj₁ (refl , refl) = _ , wev τ*-refl sp-nBusy-sbatch τ*-refl , rsM
...       | inj₂ (refl , refl) = _ , wev τ*-refl sp-nBusy-noblk τ*-refl , rsN

rs_Busy_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) (ISn stBusy)) Cidle ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((IT nBusy ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Busy_fwd_tau st = ⊥-elim (netJ-noτ st)

rs_Busy_bwd_ev : ∀ {l S′} → (IT nBusy ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stBusy)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Busy_bwd_ev st with Hide-ev-elim bfMsgES (IT nBusy) st
... | he√ ()
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) =
        _ , wev τ*-refl im-J-sbatch τ*-refl , rsM
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl refl) =
        _ , wev τ*-refl im-J-noblk τ*-refl , rsN
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
... | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
... | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())

rs_Busy_bwd_tau : ∀ {S′} → (IT nBusy ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stBusy)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Busy_bwd_tau st = ⊥-elim (spec-noτ sBusy st)

------------------------------------------------------------------------
-- rsIdle : JN (Inner (ICn stIdle) (ISn stIdle)) Cidle  ≈  IT nIdle.
------------------------------------------------------------------------
-- SPEC builders: IT nIdle fires the client apis.
sp-nIdle-req : ∀ r → (IT nIdle ∖ bfMsgES) ─[ ev (nReq r) ]─► (S-req r ∖ bfMsgES)
sp-nIdle-req r = Hide-keep bfMsgES (IT nIdle) (λ z → z) (sVis refl refl)
sp-nIdle-cdone : (IT nIdle ∖ bfMsgES) ─[ ev nCDone ]─► (S-cdone ∖ bfMsgES)
sp-nIdle-cdone = Hide-keep bfMsgES (IT nIdle) (λ z → z) (sVis refl refl)
-- client leaves at stIdle.
cl-ICidle-req : ∀ r → ICn stIdle ─[ ev (nReq r) ]─► CB-req r
cl-ICidle-req r = sVis refl refl
cl-ICidle-cdone : ICn stIdle ─[ ev nCDone ]─► CB-cdone
cl-ICidle-cdone = sVis refl refl
-- NETWORK builders: client fires solo from the idle config.
im-A-req : ∀ r → JN (Inner (ICn stIdle) (ISn stIdle)) Cidle ─[ ev (nReq r) ]─► JN (Inner (CB-req r) (ISn stIdle)) Cidle
im-A-req r = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle (λ z → z)
    (Par-soloL ∅ES mrg (ICn stIdle) (ISn stIdle) (λ z → z) (cl-ICidle-req r) refl) refl)
im-A-cdone : JN (Inner (ICn stIdle) (ISn stIdle)) Cidle ─[ ev nCDone ]─► JN (Inner CB-cdone (ISn stIdle)) Cidle
im-A-cdone = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle (λ z → z)
    (Par-soloL ∅ES mrg (ICn stIdle) (ISn stIdle) (λ z → z) cl-ICidle-cdone refl) refl)

rs_Idle_fwd_ev : ∀ {l W′} → JN (Inner (ICn stIdle) (ISn stIdle)) Cidle ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((IT nIdle ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Idle_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stIdle} {sv = ISn stIdle} {cp = Cidle} (ICn-no-bfMsg {stIdle}) (ISn-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stIdle) (ISn stIdle) ist
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ISidle-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) =
              _ , wev τ*-refl (sp-nIdle-req aa) τ*-refl , rsReqB aa
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) =
              _ , wev τ*-refl sp-nIdle-cdone τ*-refl , rsCd
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())

rs_Idle_fwd_tau : ∀ {W′} → JN (Inner (ICn stIdle) (ISn stIdle)) Cidle ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((IT nIdle ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Idle_fwd_tau st = ⊥-elim (netA-noτ st)

rs_Idle_bwd_ev : ∀ {l S′} → (IT nIdle ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stIdle) (ISn stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Idle_bwd_ev st with Hide-ev-elim bfMsgES (IT nIdle) st
... | he√ ()
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = r} refl refl) =
        _ , wev τ*-refl (im-A-req r) τ*-refl , rsReqB r
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl refl) =
        _ , wev τ*-refl im-A-cdone τ*-refl , rsCd
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
... | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
... | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())

rs_Idle_bwd_tau : ∀ {S′} → (IT nIdle ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (ICn stIdle) (ISn stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Idle_bwd_tau st = ⊥-elim (spec-noτ sIdle st)

------------------------------------------------------------------------
-- S-req2 cluster (rsReqB3/B4/B5/B6): the server SB-req r fires reqBFRange!r
-- (value-restricted), matched by the spec S-req2's reqBFRange!r.
------------------------------------------------------------------------
-- decidable-equality diagonal on ChainRange (reqBFRange is value-restricted).
≟-diagR : ∀ (r : ChainRange) → (r ≟ r) ≡ yes refl
≟-diagR r = ≡-≟-identity _≟_ refl
-- spec: S-req2 r fires reqBFRange!r → S-loop nBusy.
sp-req2-reqR : ∀ r → (S-req2 r ∖ bfMsgES) ─[ ev (nReqR r) ]─► (S-loop nBusy ∖ bfMsgES)
sp-req2-reqR r = Hide-keep bfMsgES (S-req2 r) (λ z → z) (sVis refl (h r))
  where h : ∀ r → viewV (PTree.force (S-req2 r)) (ApiBFCar reqBFRange , apiBF reqBFRange) r ≡ just (S-loop nBusy)
        h r rewrite ≟-diagR r = refl
-- server leaf: SB-req r fires reqBFRange!r → SB-loop stBusy.
sv-SBreq-reqR : ∀ r → SB-req r ─[ ev (nReqR r) ]─► SB-loop stBusy
sv-SBreq-reqR r = sVis refl (h r)
  where h : ∀ r → viewV (PTree.force (SB-req r)) (ApiBFCar reqBFRange , apiBF reqBFRange) r ≡ just (SB-loop stBusy)
        h r rewrite ≟-diagR r = refl
-- network reqBFRange builders (server solo) for the four B3..B6 frames.
im-B3-reqR : ∀ r → JN (Inner (CB-loop stBusy) (SB-req r)) Cret ─[ ev (nReqR r) ]─► JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret
im-B3-reqR r = Hide-keep ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-req r)) Cret) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (CB-loop stBusy) (SB-req r)) Cret (λ z → z)
    (Par-soloR ∅ES mrg (CB-loop stBusy) (SB-req r) (λ z → z) (sv-SBreq-reqR r) refl) refl)
im-B4-reqR : ∀ r → JN (Inner (ICn stBusy) (SB-req r)) Cret ─[ ev (nReqR r) ]─► JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret
im-B4-reqR r = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-req r)) Cret) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stBusy) (SB-req r)) Cret (λ z → z)
    (Par-soloR ∅ES mrg (ICn stBusy) (SB-req r) (λ z → z) (sv-SBreq-reqR r) refl) refl)
im-B5-reqR : ∀ r → JN (Inner (CB-loop stBusy) (SB-req r)) Cidle ─[ ev (nReqR r) ]─► JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle
im-B5-reqR r = Hide-keep ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-req r)) Cidle) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (CB-loop stBusy) (SB-req r)) Cidle (λ z → z)
    (Par-soloR ∅ES mrg (CB-loop stBusy) (SB-req r) (λ z → z) (sv-SBreq-reqR r) refl) refl)
im-B6-reqR : ∀ r → JN (Inner (ICn stBusy) (SB-req r)) Cidle ─[ ev (nReqR r) ]─► JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle
im-B6-reqR r = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-req r)) Cidle) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stBusy) (SB-req r)) Cidle (λ z → z)
    (Par-soloR ∅ES mrg (ICn stBusy) (SB-req r) (λ z → z) (sv-SBreq-reqR r) refl) refl)

------------------------------------------------------------------------
-- rsReqB3 : JN (Inner (CB-loop stBusy) (SB-req r)) Cret  ≈  S-req2 r.
------------------------------------------------------------------------
rs_ReqB3_fwd_ev : ∀ r {l W′} → JN (Inner (CB-loop stBusy) (SB-req r)) Cret ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req2 r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqB3_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-req r)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-req r} {cp = Cret} (CBloop-no-bfMsg {stBusy}) (SBreq-no-bfMsg {r}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (SB-req r)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (SB-req r) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl q) with aa ≟ r
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-req2-reqR r) τ*-refl , rsG3
rs_ReqB3_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl ()) | no _
rs_ReqB3_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_ReqB3_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_ReqB3_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_ReqB3_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_ReqB3_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_ReqB3_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_ReqB3_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())

rs_ReqB3_fwd_tau : ∀ r {W′} → JN (Inner (CB-loop stBusy) (SB-req r)) Cret ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req2 r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqB3_fwd_tau r st with netB3-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsReqB4 r
... | inj₂ refl = _ , wτ τ*-refl , rsReqB5 r

rs_ReqB3_bwd_ev : ∀ r {l S′} → (S-req2 r ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-req r)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqB3_bwd_ev r st with Hide-ev-elim bfMsgES (S-req2 r) st
... | he√ ()
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl q) with a ≟ r
...   | yes refl with q
...     | refl = _ , wev τ*-refl (im-B3-reqR r) τ*-refl , rsG3
rs_ReqB3_bwd_ev r st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
rs_ReqB3_bwd_ev r st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_ReqB3_bwd_ev r st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())

rs_ReqB3_bwd_tau : ∀ r {S′} → (S-req2 r ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-req r)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_ReqB3_bwd_tau r st = ⊥-elim (S-req2-noτ st)

------------------------------------------------------------------------
-- rsReqB4 : JN (Inner (ICn stBusy) (SB-req r)) Cret  ≈  S-req2 r.
------------------------------------------------------------------------
rs_ReqB4_fwd_ev : ∀ r {l W′} → JN (Inner (ICn stBusy) (SB-req r)) Cret ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req2 r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqB4_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-req r)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-req r} {cp = Cret} (ICn-no-bfMsg {stBusy}) (SBreq-no-bfMsg {r}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (SB-req r)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (SB-req r) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl q) with aa ≟ r
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-req2-reqR r) τ*-refl , rsG3a
rs_ReqB4_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl ()) | no _
rs_ReqB4_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_ReqB4_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_ReqB4_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_ReqB4_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_ReqB4_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_ReqB4_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_ReqB4_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())

rs_ReqB4_fwd_tau : ∀ r {W′} → JN (Inner (ICn stBusy) (SB-req r)) Cret ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req2 r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqB4_fwd_tau r st with netB3a-τ st
... | refl = _ , wτ τ*-refl , rsReqB6 r

rs_ReqB4_bwd_ev : ∀ r {l S′} → (S-req2 r ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-req r)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqB4_bwd_ev r st with Hide-ev-elim bfMsgES (S-req2 r) st
... | he√ ()
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl q) with a ≟ r
...   | yes refl with q
...     | refl = _ , wev τ*-refl (im-B4-reqR r) τ*-refl , rsG3a
rs_ReqB4_bwd_ev r st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
rs_ReqB4_bwd_ev r st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_ReqB4_bwd_ev r st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())

rs_ReqB4_bwd_tau : ∀ r {S′} → (S-req2 r ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-req r)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_ReqB4_bwd_tau r st = ⊥-elim (S-req2-noτ st)

------------------------------------------------------------------------
-- rsReqB5 : JN (Inner (CB-loop stBusy) (SB-req r)) Cidle  ≈  S-req2 r.
------------------------------------------------------------------------
rs_ReqB5_fwd_ev : ∀ r {l W′} → JN (Inner (CB-loop stBusy) (SB-req r)) Cidle ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req2 r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqB5_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-req r)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-req r} {cp = Cidle} (CBloop-no-bfMsg {stBusy}) (SBreq-no-bfMsg {r}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (SB-req r)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (SB-req r) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl q) with aa ≟ r
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-req2-reqR r) τ*-refl , rsG6
rs_ReqB5_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl ()) | no _
rs_ReqB5_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_ReqB5_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_ReqB5_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_ReqB5_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_ReqB5_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_ReqB5_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_ReqB5_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())

rs_ReqB5_fwd_tau : ∀ r {W′} → JN (Inner (CB-loop stBusy) (SB-req r)) Cidle ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req2 r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqB5_fwd_tau r st with netB5-τ st
... | refl = _ , wτ τ*-refl , rsReqB6 r

rs_ReqB5_bwd_ev : ∀ r {l S′} → (S-req2 r ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-req r)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqB5_bwd_ev r st with Hide-ev-elim bfMsgES (S-req2 r) st
... | he√ ()
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl q) with a ≟ r
...   | yes refl with q
...     | refl = _ , wev τ*-refl (im-B5-reqR r) τ*-refl , rsG6
rs_ReqB5_bwd_ev r st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
rs_ReqB5_bwd_ev r st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_ReqB5_bwd_ev r st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())

rs_ReqB5_bwd_tau : ∀ r {S′} → (S-req2 r ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-req r)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_ReqB5_bwd_tau r st = ⊥-elim (S-req2-noτ st)

------------------------------------------------------------------------
-- rsReqB6 : JN (Inner (ICn stBusy) (SB-req r)) Cidle  ≈  S-req2 r.
------------------------------------------------------------------------
rs_ReqB6_fwd_ev : ∀ r {l W′} → JN (Inner (ICn stBusy) (SB-req r)) Cidle ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req2 r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqB6_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-req r)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-req r} {cp = Cidle} (ICn-no-bfMsg {stBusy}) (SBreq-no-bfMsg {r}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (SB-req r)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (SB-req r) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl q) with aa ≟ r
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-req2-reqR r) τ*-refl , rsFl
rs_ReqB6_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl ()) | no _
rs_ReqB6_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_ReqB6_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_ReqB6_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_ReqB6_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_ReqB6_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_ReqB6_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_ReqB6_fwd_ev r st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())

rs_ReqB6_fwd_tau : ∀ r {W′} → JN (Inner (ICn stBusy) (SB-req r)) Cidle ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req2 r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqB6_fwd_tau r st = ⊥-elim (netB4-noτ st)

rs_ReqB6_bwd_ev : ∀ r {l S′} → (S-req2 r ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-req r)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqB6_bwd_ev r st with Hide-ev-elim bfMsgES (S-req2 r) st
... | he√ ()
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl q) with a ≟ r
...   | yes refl with q
...     | refl = _ , wev τ*-refl (im-B6-reqR r) τ*-refl , rsFl
rs_ReqB6_bwd_ev r st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
rs_ReqB6_bwd_ev r st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_ReqB6_bwd_ev r st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())

rs_ReqB6_bwd_tau : ∀ r {S′} → (S-req2 r ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-req r)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_ReqB6_bwd_tau r st = ⊥-elim (S-req2-noτ st)

------------------------------------------------------------------------
-- IT-nBusy stutter cluster (rsG7/rsBI/rsG5): server ISn stBusy fires
-- sendBFStartBatch / sendBFNoBlocks; copy-drain τ's stutter (0 spec steps).
------------------------------------------------------------------------
-- network sbatch/noblk builders (server solo) for the three frames.
im-G7-sbatch : JN (Inner (ICn stBusy) (ISn stBusy)) Cret ─[ ev nSBatch ]─► JN (Inner (ICn stBusy) SB-sbatch) Cret
im-G7-sbatch = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cret) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cret (λ z → z)
    (Par-soloR ∅ES mrg (ICn stBusy) (ISn stBusy) (λ z → z) sv-ISbusy-sbatch refl) refl)
im-G7-noblk : JN (Inner (ICn stBusy) (ISn stBusy)) Cret ─[ ev nNoBlk ]─► JN (Inner (ICn stBusy) SB-noblk) Cret
im-G7-noblk = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cret) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cret (λ z → z)
    (Par-soloR ∅ES mrg (ICn stBusy) (ISn stBusy) (λ z → z) sv-ISbusy-noblk refl) refl)
im-BI-sbatch : JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle ─[ ev nSBatch ]─► JN (Inner (CB-loop stBusy) SB-sbatch) Cidle
im-BI-sbatch = Hide-keep ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cidle) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cidle (λ z → z)
    (Par-soloR ∅ES mrg (CB-loop stBusy) (ISn stBusy) (λ z → z) sv-ISbusy-sbatch refl) refl)
im-BI-noblk : JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle ─[ ev nNoBlk ]─► JN (Inner (CB-loop stBusy) SB-noblk) Cidle
im-BI-noblk = Hide-keep ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cidle) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cidle (λ z → z)
    (Par-soloR ∅ES mrg (CB-loop stBusy) (ISn stBusy) (λ z → z) sv-ISbusy-noblk refl) refl)
im-G5-sbatch : JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret ─[ ev nSBatch ]─► JN (Inner (CB-loop stBusy) SB-sbatch) Cret
im-G5-sbatch = Hide-keep ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cret) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cret (λ z → z)
    (Par-soloR ∅ES mrg (CB-loop stBusy) (ISn stBusy) (λ z → z) sv-ISbusy-sbatch refl) refl)
im-G5-noblk : JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret ─[ ev nNoBlk ]─► JN (Inner (CB-loop stBusy) SB-noblk) Cret
im-G5-noblk = Hide-keep ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cret) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cret (λ z → z)
    (Par-soloR ∅ES mrg (CB-loop stBusy) (ISn stBusy) (λ z → z) sv-ISbusy-noblk refl) refl)

------------------------------------------------------------------------
-- rsG7 : JN (Inner (ICn stBusy) (ISn stBusy)) Cret  ≈  IT nBusy.
------------------------------------------------------------------------
rs_G7_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) (ISn stBusy)) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nBusy ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_G7_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = ISn stBusy} {cp = Cret} (ICn-no-bfMsg {stBusy}) (ISn-no-bfMsg {stBusy}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (ISn stBusy)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (ISn stBusy) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst with ISbusy-api svst
...       | inj₁ (refl , refl) = _ , wev τ*-refl sp-nBusy-sbatch τ*-refl , rsIBMr
...       | inj₂ (refl , refl) = _ , wev τ*-refl sp-nBusy-noblk τ*-refl , rsIBNr

rs_G7_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) (ISn stBusy)) Cret ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((IT nBusy ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_G7_fwd_tau st with netG7-τ st
... | refl = _ , wτ τ*-refl , rsBusy

rs_G7_bwd_ev : ∀ {l S′} → (IT nBusy ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stBusy)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_G7_bwd_ev st with Hide-ev-elim bfMsgES (IT nBusy) st
... | he√ ()
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) =
        _ , wev τ*-refl im-G7-sbatch τ*-refl , rsIBMr
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl refl) =
        _ , wev τ*-refl im-G7-noblk τ*-refl , rsIBNr
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
... | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
... | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())

rs_G7_bwd_tau : ∀ {S′} → (IT nBusy ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stBusy)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_G7_bwd_tau st = ⊥-elim (spec-noτ sBusy st)

------------------------------------------------------------------------
-- rsBI : JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle  ≈  IT nBusy.
------------------------------------------------------------------------
rs_BI_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nBusy ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BI_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = ISn stBusy} {cp = Cidle} (CBloop-no-bfMsg {stBusy}) (ISn-no-bfMsg {stBusy}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (ISn stBusy) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst with ISbusy-api svst
...       | inj₁ (refl , refl) = _ , wev τ*-refl sp-nBusy-sbatch τ*-refl , rsLbMi
...       | inj₂ (refl , refl) = _ , wev τ*-refl sp-nBusy-noblk τ*-refl , rsLbNi

rs_BI_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((IT nBusy ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BI_fwd_tau st with netI-τ st
... | refl = _ , wτ τ*-refl , rsBusy

rs_BI_bwd_ev : ∀ {l S′} → (IT nBusy ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_BI_bwd_ev st with Hide-ev-elim bfMsgES (IT nBusy) st
... | he√ ()
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) =
        _ , wev τ*-refl im-BI-sbatch τ*-refl , rsLbMi
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl refl) =
        _ , wev τ*-refl im-BI-noblk τ*-refl , rsLbNi
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
... | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
... | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())

rs_BI_bwd_tau : ∀ {S′} → (IT nBusy ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_BI_bwd_tau st = ⊥-elim (spec-noτ sBusy st)

------------------------------------------------------------------------
-- rsG5 : JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret  ≈  IT nBusy.
------------------------------------------------------------------------
rs_G5_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nBusy ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_G5_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = ISn stBusy} {cp = Cret} (CBloop-no-bfMsg {stBusy}) (ISn-no-bfMsg {stBusy}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (ISn stBusy)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (ISn stBusy) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst with ISbusy-api svst
...       | inj₁ (refl , refl) = _ , wev τ*-refl sp-nBusy-sbatch τ*-refl , rsLbMr
...       | inj₂ (refl , refl) = _ , wev τ*-refl sp-nBusy-noblk τ*-refl , rsLbNr

rs_G5_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((IT nBusy ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_G5_fwd_tau st with netG5-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsG7
... | inj₂ refl = _ , wτ τ*-refl , rsBI

rs_G5_bwd_ev : ∀ {l S′} → (IT nBusy ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_G5_bwd_ev st with Hide-ev-elim bfMsgES (IT nBusy) st
... | he√ ()
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) =
        _ , wev τ*-refl im-G5-sbatch τ*-refl , rsLbMr
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl refl) =
        _ , wev τ*-refl im-G5-noblk τ*-refl , rsLbNr
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = bfMsg}                    P' ¬m (sVis {at = (_ , bfMsg)}                    refl ())
... | heV {e = bfIn}                     P' ¬m (sVis {at = (_ , bfIn)}                     refl ())
... | heV {e = bfOut}                    P' ¬m (sVis {at = (_ , bfOut)}                    refl ())

rs_G5_bwd_tau : ∀ {S′} → (IT nBusy ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_G5_bwd_tau st = ⊥-elim (spec-noτ sBusy st)

------------------------------------------------------------------------
-- S-loop nBusy cluster (rsFl/rsG3a/rsG3/rsG6): the spec S-loop nBusy is a pure
-- τ loop-back to IT nBusy; each network config either stutters onto a sibling
-- S-loop config or hops (one server/copy loop-back τ) to a paired IT-nBusy
-- config.  No visible events on either side.
------------------------------------------------------------------------
-- spec loop-back τ: S-loop s → IT s.
sp-Sloop-τ : ∀ s → (S-loop s ∖ bfMsgES) ─[ τ ]─► (IT s ∖ bfMsgES)
sp-Sloop-τ s = Hide-τ bfMsgES (S-loop s) (sSil refl)
-- server iter loop-back leaf: SB-loop s → ISn s.
sv-SBloop-τ : ∀ s → SB-loop s ─[ τ ]─► ISn s
sv-SBloop-τ s = sSil refl
-- client iter loop-back leaf: CB-loop s → ICn s.
cl-CBloop-τ : ∀ s → CB-loop s ─[ τ ]─► ICn s
cl-CBloop-τ s = sSil refl
-- network server-loop τ builders (server SB-loop stBusy → ISn stBusy) per frame.
im-Fl-svloop : JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle ─[ τ ]─► JN (Inner (ICn stBusy) (ISn stBusy)) Cidle
im-Fl-svloop = Hide-τ ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-loop stBusy)) Cidle)
  (Par-τ-L ioBF mrg2 (Inner (ICn stBusy) (SB-loop stBusy)) Cidle
    (Par-τ-R ∅ES mrg (ICn stBusy) (SB-loop stBusy) (sv-SBloop-τ stBusy)))
im-G3a-svloop : JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret ─[ τ ]─► JN (Inner (ICn stBusy) (ISn stBusy)) Cret
im-G3a-svloop = Hide-τ ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-loop stBusy)) Cret)
  (Par-τ-L ioBF mrg2 (Inner (ICn stBusy) (SB-loop stBusy)) Cret
    (Par-τ-R ∅ES mrg (ICn stBusy) (SB-loop stBusy) (sv-SBloop-τ stBusy)))
im-G3-svloop : JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret ─[ τ ]─► JN (Inner (CB-loop stBusy) (ISn stBusy)) Cret
im-G3-svloop = Hide-τ ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret)
  (Par-τ-L ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret
    (Par-τ-R ∅ES mrg (CB-loop stBusy) (SB-loop stBusy) (sv-SBloop-τ stBusy)))
im-G6-svloop : JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle ─[ τ ]─► JN (Inner (CB-loop stBusy) (ISn stBusy)) Cidle
im-G6-svloop = Hide-τ ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle)
  (Par-τ-L ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle
    (Par-τ-R ∅ES mrg (CB-loop stBusy) (SB-loop stBusy) (sv-SBloop-τ stBusy)))

------------------------------------------------------------------------
-- rsFl : JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle  ≈  S-loop nBusy.
------------------------------------------------------------------------
rs_Fl_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nBusy ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Fl_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-loop stBusy)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-loop stBusy} {cp = Cidle} (ICn-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stBusy}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (SB-loop stBusy)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (SB-loop stBusy) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)

rs_Fl_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nBusy ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Fl_fwd_tau st with netFl-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ nBusy) τ*-refl) , rsBusy

rs_Fl_bwd_ev : ∀ {l S′} → (S-loop nBusy ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Fl_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nBusy) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_Fl_bwd_tau : ∀ {S′} → (S-loop nBusy ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Fl_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step im-Fl-svloop τ*-refl) , rsBusy

------------------------------------------------------------------------
-- rsG3a : JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret  ≈  S-loop nBusy.
------------------------------------------------------------------------
rs_G3a_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nBusy ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_G3a_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-loop stBusy)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-loop stBusy} {cp = Cret} (ICn-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stBusy}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (SB-loop stBusy)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (SB-loop stBusy) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)

rs_G3a_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-loop nBusy ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_G3a_fwd_tau st with netG3a-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nBusy) τ*-refl) , rsG7
... | inj₂ refl = _ , wτ τ*-refl , rsFl

rs_G3a_bwd_ev : ∀ {l S′} → (S-loop nBusy ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_G3a_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nBusy) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_G3a_bwd_tau : ∀ {S′} → (S-loop nBusy ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stBusy)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_G3a_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step im-G3a-svloop τ*-refl) , rsG7

------------------------------------------------------------------------
-- rsG3 : JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret  ≈  S-loop nBusy.
------------------------------------------------------------------------
rs_G3_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nBusy ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_G3_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-loop stBusy} {cp = Cret} (CBloop-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stBusy}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (SB-loop stBusy) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_G3_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nBusy ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_G3_fwd_tau st with netG3-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsG3a
... | inj₂ (inj₁ refl) = _ , wτ (τ*-step (sp-Sloop-τ nBusy) τ*-refl) , rsG5
... | inj₂ (inj₂ refl) = _ , wτ τ*-refl , rsG6

rs_G3_bwd_ev : ∀ {l S′} → (S-loop nBusy ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_G3_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nBusy) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_G3_bwd_tau : ∀ {S′} → (S-loop nBusy ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_G3_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step im-G3-svloop τ*-refl) , rsG5

------------------------------------------------------------------------
-- rsG6 : JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle  ≈  S-loop nBusy.
------------------------------------------------------------------------
rs_G6_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nBusy ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_G6_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-loop stBusy} {cp = Cidle} (CBloop-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stBusy}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (SB-loop stBusy) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_G6_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nBusy ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_G6_fwd_tau st with netG6-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsFl
... | inj₂ refl = _ , wτ (τ*-step (sp-Sloop-τ nBusy) τ*-refl) , rsBI

rs_G6_bwd_ev : ∀ {l S′} → (S-loop nBusy ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_G6_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nBusy) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_G6_bwd_tau : ∀ {S′} → (S-loop nBusy ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stBusy)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_G6_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step im-G6-svloop τ*-refl) , rsBI

------------------------------------------------------------------------
-- S-loop nDone cluster (rsCdR/rsCd3/rsCd5/rsCd6/rsCd8/rsCd9): the spec
-- S-loop nDone τ-loops to IT nDone; the peers loop-back to stDone.  No visible
-- events.  bwd_tau builds client/server loop-back τ's to a paired IT-nDone
-- config (rsCd7 = Cret / rsDone = Cidle).
------------------------------------------------------------------------
-- done-frame server loop-back τ builders.
svl-ICdone-Cret : JN (Inner (ICn stDone) (SB-loop stDone)) Cret ─[ τ ]─► JN (Inner (ICn stDone) (ISn stDone)) Cret
svl-ICdone-Cret = Hide-τ ioBF (Par ioBF mrg2 (Inner (ICn stDone) (SB-loop stDone)) Cret)
  (Par-τ-L ioBF mrg2 (Inner (ICn stDone) (SB-loop stDone)) Cret
    (Par-τ-R ∅ES mrg (ICn stDone) (SB-loop stDone) (sv-SBloop-τ stDone)))
svl-ICdone-Cidle : JN (Inner (ICn stDone) (SB-loop stDone)) Cidle ─[ τ ]─► JN (Inner (ICn stDone) (ISn stDone)) Cidle
svl-ICdone-Cidle = Hide-τ ioBF (Par ioBF mrg2 (Inner (ICn stDone) (SB-loop stDone)) Cidle)
  (Par-τ-L ioBF mrg2 (Inner (ICn stDone) (SB-loop stDone)) Cidle
    (Par-τ-R ∅ES mrg (ICn stDone) (SB-loop stDone) (sv-SBloop-τ stDone)))
-- done-frame client loop-back τ builders.
cll-ISdone-Cret : JN (Inner (CB-loop stDone) (ISn stDone)) Cret ─[ τ ]─► JN (Inner (ICn stDone) (ISn stDone)) Cret
cll-ISdone-Cret = Hide-τ ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (ISn stDone)) Cret)
  (Par-τ-L ioBF mrg2 (Inner (CB-loop stDone) (ISn stDone)) Cret
    (Par-τ-L ∅ES mrg (CB-loop stDone) (ISn stDone) (cl-CBloop-τ stDone)))
cll-ISdone-Cidle : JN (Inner (CB-loop stDone) (ISn stDone)) Cidle ─[ τ ]─► JN (Inner (ICn stDone) (ISn stDone)) Cidle
cll-ISdone-Cidle = Hide-τ ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (ISn stDone)) Cidle)
  (Par-τ-L ioBF mrg2 (Inner (CB-loop stDone) (ISn stDone)) Cidle
    (Par-τ-L ∅ES mrg (CB-loop stDone) (ISn stDone) (cl-CBloop-τ stDone)))
cll-SBloop-Cret : JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret ─[ τ ]─► JN (Inner (ICn stDone) (SB-loop stDone)) Cret
cll-SBloop-Cret = Hide-τ ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stDone)) Cret)
  (Par-τ-L ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stDone)) Cret
    (Par-τ-L ∅ES mrg (CB-loop stDone) (SB-loop stDone) (cl-CBloop-τ stDone)))
cll-SBloop-Cidle : JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle ─[ τ ]─► JN (Inner (ICn stDone) (SB-loop stDone)) Cidle
cll-SBloop-Cidle = Hide-τ ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stDone)) Cidle)
  (Par-τ-L ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stDone)) Cidle
    (Par-τ-L ∅ES mrg (CB-loop stDone) (SB-loop stDone) (cl-CBloop-τ stDone)))

------------------------------------------------------------------------
-- rsCdR : JN (Inner (ICn stDone) (SB-loop stDone)) Cret  ≈  S-loop nDone.
------------------------------------------------------------------------
rs_CdR_fwd_ev : ∀ {l W′} → JN (Inner (ICn stDone) (SB-loop stDone)) Cret ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_CdR_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stDone) (SB-loop stDone)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stDone} {sv = SB-loop stDone} {cp = Cret} (ICn-no-bfMsg {stDone}) (SBloop-no-bfMsg {stDone}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stDone) (SB-loop stDone)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stDone) (SB-loop stDone) ist
...     | evL ¬m3 clst = ⊥-elim (ICdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICdone-no-api clst)

rs_CdR_fwd_tau : ∀ {W′} → JN (Inner (ICn stDone) (SB-loop stDone)) Cret ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_CdR_fwd_tau st with netCd4-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nDone) τ*-refl) , rsCd7
... | inj₂ refl = _ , wτ τ*-refl , rsCd8

rs_CdR_bwd_ev : ∀ {l S′} → (S-loop nDone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (SB-loop stDone)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_CdR_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nDone) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_CdR_bwd_tau : ∀ {S′} → (S-loop nDone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (SB-loop stDone)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_CdR_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step svl-ICdone-Cret τ*-refl) , rsCd7

------------------------------------------------------------------------
-- rsCd3 : JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret  ≈  S-loop nDone.
------------------------------------------------------------------------
rs_Cd3_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cd3_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stDone)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stDone} {sv = SB-loop stDone} {cp = Cret} (CBloop-no-bfMsg {stDone}) (SBloop-no-bfMsg {stDone}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stDone)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stDone) (SB-loop stDone) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_Cd3_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cd3_fwd_tau st with netCd3-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsCdR
... | inj₂ (inj₁ refl) = _ , wτ τ*-refl , rsCd5
... | inj₂ (inj₂ refl) = _ , wτ τ*-refl , rsCd6

rs_Cd3_bwd_ev : ∀ {l S′} → (S-loop nDone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_Cd3_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nDone) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_Cd3_bwd_tau : ∀ {S′} → (S-loop nDone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_Cd3_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step cll-SBloop-Cret (τ*-step svl-ICdone-Cret τ*-refl)) , rsCd7

------------------------------------------------------------------------
-- rsCd5 : JN (Inner (CB-loop stDone) (ISn stDone)) Cret  ≈  S-loop nDone.
------------------------------------------------------------------------
rs_Cd5_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stDone) (ISn stDone)) Cret ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cd5_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (ISn stDone)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stDone} {sv = ISn stDone} {cp = Cret} (CBloop-no-bfMsg {stDone}) (ISn-no-bfMsg {stDone}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stDone) (ISn stDone)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stDone) (ISn stDone) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_Cd5_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stDone) (ISn stDone)) Cret ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cd5_fwd_tau st with netCd5-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nDone) τ*-refl) , rsCd7
... | inj₂ refl = _ , wτ τ*-refl , rsCd9

rs_Cd5_bwd_ev : ∀ {l S′} → (S-loop nDone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (ISn stDone)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_Cd5_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nDone) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_Cd5_bwd_tau : ∀ {S′} → (S-loop nDone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (ISn stDone)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_Cd5_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step cll-ISdone-Cret τ*-refl) , rsCd7

------------------------------------------------------------------------
-- rsCd6 : JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle  ≈  S-loop nDone.
------------------------------------------------------------------------
rs_Cd6_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cd6_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stDone)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stDone} {sv = SB-loop stDone} {cp = Cidle} (CBloop-no-bfMsg {stDone}) (SBloop-no-bfMsg {stDone}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stDone)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stDone) (SB-loop stDone) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_Cd6_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cd6_fwd_tau st with netCd6-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsCd8
... | inj₂ refl = _ , wτ τ*-refl , rsCd9

rs_Cd6_bwd_ev : ∀ {l S′} → (S-loop nDone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Cd6_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nDone) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_Cd6_bwd_tau : ∀ {S′} → (S-loop nDone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (SB-loop stDone)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Cd6_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step cll-SBloop-Cidle (τ*-step svl-ICdone-Cidle τ*-refl)) , rsDone

------------------------------------------------------------------------
-- rsCd8 : JN (Inner (ICn stDone) (SB-loop stDone)) Cidle  ≈  S-loop nDone.
------------------------------------------------------------------------
rs_Cd8_fwd_ev : ∀ {l W′} → JN (Inner (ICn stDone) (SB-loop stDone)) Cidle ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cd8_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stDone) (SB-loop stDone)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stDone} {sv = SB-loop stDone} {cp = Cidle} (ICn-no-bfMsg {stDone}) (SBloop-no-bfMsg {stDone}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stDone) (SB-loop stDone)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stDone) (SB-loop stDone) ist
...     | evL ¬m3 clst = ⊥-elim (ICdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICdone-no-api clst)

rs_Cd8_fwd_tau : ∀ {W′} → JN (Inner (ICn stDone) (SB-loop stDone)) Cidle ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cd8_fwd_tau st with netCd8-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ nDone) τ*-refl) , rsDone

rs_Cd8_bwd_ev : ∀ {l S′} → (S-loop nDone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (SB-loop stDone)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Cd8_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nDone) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_Cd8_bwd_tau : ∀ {S′} → (S-loop nDone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (SB-loop stDone)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Cd8_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step svl-ICdone-Cidle τ*-refl) , rsDone

------------------------------------------------------------------------
-- rsCd9 : JN (Inner (CB-loop stDone) (ISn stDone)) Cidle  ≈  S-loop nDone.
------------------------------------------------------------------------
rs_Cd9_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stDone) (ISn stDone)) Cidle ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cd9_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (ISn stDone)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stDone} {sv = ISn stDone} {cp = Cidle} (CBloop-no-bfMsg {stDone}) (ISn-no-bfMsg {stDone}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stDone) (ISn stDone)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stDone) (ISn stDone) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_Cd9_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stDone) (ISn stDone)) Cidle ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-loop nDone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cd9_fwd_tau st with netCd9-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ nDone) τ*-refl) , rsDone

rs_Cd9_bwd_ev : ∀ {l S′} → (S-loop nDone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (ISn stDone)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Cd9_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nDone) st
... | he√ ()
... | heV P' ¬m (sVis () _)

rs_Cd9_bwd_tau : ∀ {S′} → (S-loop nDone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (ISn stDone)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Cd9_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step cll-ISdone-Cidle τ*-refl) , rsDone

------------------------------------------------------------------------
-- S-req r cluster (rsReqB/rsReqBh/rsReqB2): the spec S-req r hides a bfMsg τ
-- to S-req2 r.  In the network this is a TWO-hop copy cascade: client
-- bfIn!(mRequestRange r) → copy holds → copy bfOut!(mRequestRange r) → server
-- notify.  We build the two hidden sync τ's (via Par-sync + Hide-hidden).
------------------------------------------------------------------------
-- decidable-equality diagonal on BFMsg (bfIn/bfOut are value-restricted).
≟-diagM : ∀ (m : BFMsg) → (m ≟ m) ≡ yes refl
≟-diagM m = ≡-≟-identity _≟_ refl
-- spec hidden bfMsg τ: S-req r → S-req2 r.
sp-Sreq-τ : ∀ r → (S-req r ∖ bfMsgES) ─[ τ ]─► (S-req2 r ∖ bfMsgES)
sp-Sreq-τ r = Hide-hidden bfMsgES (S-req r) Poly.tt (sVis refl (h r))
  where h : ∀ r → viewV (PTree.force (S-req r)) (BFMsg , bfMsg) (mRequestRange r) ≡ just (S-req2 r)
        h r rewrite ≟-diagM (mRequestRange r) = refl
-- client leaf: CB-req r sends bfIn!(mRequestRange r) → CB-loop stBusy.
cl-CBreq-bfin : ∀ r → CB-req r ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = mRequestRange r })) ]─► CB-loop stBusy
cl-CBreq-bfin r = sVis refl (h r)
  where h : ∀ r → viewV (PTree.force (CB-req r)) (BFMsg , bfIn) (mRequestRange r) ≡ just (CB-loop stBusy)
        h r rewrite ≟-diagM (mRequestRange r) = refl
-- copy leaf: Cidle receives bfIn!m → Chold m.
copy-Cidle-bfin : ∀ m → Cidle ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = m })) ]─► Chold m
copy-Cidle-bfin m = sVis refl refl
-- copy leaf: Chold m sends bfOut!m → Cret.
copy-Chold-bfout : ∀ m → Chold m ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = m })) ]─► Cret
copy-Chold-bfout m = sVis refl (h m)
  where h : ∀ m → viewV (PTree.force (Chold m)) (BFMsg , bfOut) m ≡ just Cret
        h m rewrite ≟-diagM m = refl
-- server leaf: ISn stIdle receives bfOut!(mRequestRange r) → SB-req r.
sv-ISidle-bfout-req : ∀ r → ISn stIdle ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = mRequestRange r })) ]─► SB-req r
sv-ISidle-bfout-req r = sVis refl refl
-- hop 1 (bfIn sync): B → Bh.
im-B-bfin : ∀ r → JN (Inner (CB-req r) (ISn stIdle)) Cidle ─[ τ ]─► JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r))
im-B-bfin r = Hide-hidden ioBF (Par ioBF mrg2 (Inner (CB-req r) (ISn stIdle)) Cidle) Poly.tt
  (Par-sync ioBF mrg2 (Inner (CB-req r) (ISn stIdle)) Cidle Poly.tt
    (Par-soloL ∅ES mrg (CB-req r) (ISn stIdle) (λ z → z) (cl-CBreq-bfin r) refl)
    (copy-Cidle-bfin (mRequestRange r)))
-- hop 2 (bfOut sync): Bh → B3 (server notify, copy drains).
im-Bh-bfout : ∀ r → JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► JN (Inner (CB-loop stBusy) (SB-req r)) Cret
im-Bh-bfout r = Hide-hidden ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r))) Poly.tt
  (Par-sync ioBF mrg2 (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)) Poly.tt
    (Par-soloR ∅ES mrg (CB-loop stBusy) (ISn stIdle) (λ z → z) (sv-ISidle-bfout-req r) refl)
    (copy-Chold-bfout (mRequestRange r)))
-- hop 2 (bfOut sync) with client settled: B2 → B4.
im-B2-bfout : ∀ r → JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► JN (Inner (ICn stBusy) (SB-req r)) Cret
im-B2-bfout r = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r))) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)) Poly.tt
    (Par-soloR ∅ES mrg (ICn stBusy) (ISn stIdle) (λ z → z) (sv-ISidle-bfout-req r) refl)
    (copy-Chold-bfout (mRequestRange r)))

------------------------------------------------------------------------
-- rsReqB : JN (Inner (CB-req r) (ISn stIdle)) Cidle  ≈  S-req r.
------------------------------------------------------------------------
rs_ReqB_fwd_ev : ∀ r {l W′} → JN (Inner (CB-req r) (ISn stIdle)) Cidle ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqB_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-req r) (ISn stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-req r} {sv = ISn stIdle} {cp = Cidle} CBreq-no-bfMsg (ISn-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-req r) (ISn stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-req r) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBreq-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBreq-no-api clst)

rs_ReqB_fwd_tau : ∀ r {W′} → JN (Inner (CB-req r) (ISn stIdle)) Cidle ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqB_fwd_tau r st with netB-τ st
... | refl = _ , wτ τ*-refl , rsReqBh r

rs_ReqB_bwd_ev : ∀ r {l S′} → (S-req r ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-req r) (ISn stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqB_bwd_ev r st with Hide-ev-elim bfMsgES (S-req r) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_ReqB_bwd_tau : ∀ r {S′} → (S-req r ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-req r) (ISn stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_ReqB_bwd_tau r st with S-req-τ st
... | refl = _ , wτ (τ*-step (im-B-bfin r) (τ*-step (im-Bh-bfout r) τ*-refl)) , rsReqB3 r

------------------------------------------------------------------------
-- rsReqBh : JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r))  ≈  S-req r.
------------------------------------------------------------------------
rs_ReqBh_fwd_ev : ∀ r {l W′} → JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqBh_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = ISn stIdle} {cp = Chold (mRequestRange r)} (CBloop-no-bfMsg {stBusy}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_ReqBh_fwd_tau : ∀ r {W′} → JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqBh_fwd_tau r st with netBh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsReqB2 r
... | inj₂ refl = _ , wτ (τ*-step (sp-Sreq-τ r) τ*-refl) , rsReqB3 r

rs_ReqBh_bwd_ev : ∀ r {l S′} → (S-req r ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqBh_bwd_ev r st with Hide-ev-elim bfMsgES (S-req r) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_ReqBh_bwd_tau : ∀ r {S′} → (S-req r ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ═[ τ ]═► W′ × RState W′ S′)
rs_ReqBh_bwd_tau r st with S-req-τ st
... | refl = _ , wτ (τ*-step (im-Bh-bfout r) τ*-refl) , rsReqB3 r

------------------------------------------------------------------------
-- rsReqB2 : JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r))  ≈  S-req r.
------------------------------------------------------------------------
rs_ReqB2_fwd_ev : ∀ r {l W′} → JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqB2_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = ISn stIdle} {cp = Chold (mRequestRange r)} (ICn-no-bfMsg {stBusy}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)

rs_ReqB2_fwd_tau : ∀ r {W′} → JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqB2_fwd_tau r st with netB2-τ st
... | refl = _ , wτ (τ*-step (sp-Sreq-τ r) τ*-refl) , rsReqB4 r

rs_ReqB2_bwd_ev : ∀ r {l S′} → (S-req r ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqB2_bwd_ev r st with Hide-ev-elim bfMsgES (S-req r) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_ReqB2_bwd_tau : ∀ r {S′} → (S-req r ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold (mRequestRange r)) ═[ τ ]═► W′ × RState W′ S′)
rs_ReqB2_bwd_tau r st with S-req-τ st
... | refl = _ , wτ (τ*-step (im-B2-bfout r) τ*-refl) , rsReqB4 r

------------------------------------------------------------------------
-- S-cdone core (rsCd/rsCdh/rsCd2): the spec S-cdone hides a bfMsg(mClientDone)
-- τ to S-loop nDone; the network routes mClientDone through the copy (bfIn then
-- bfOut), the server receiving it goes SB-loop stDone.
------------------------------------------------------------------------
-- spec hidden bfMsg τ: S-cdone → S-loop nDone.
sp-Scdone-τ : (S-cdone ∖ bfMsgES) ─[ τ ]─► (S-loop nDone ∖ bfMsgES)
sp-Scdone-τ = Hide-hidden bfMsgES S-cdone {e = bfMsg} {a = mClientDone} Poly.tt (sVis refl h)
  where h : viewV (PTree.force S-cdone) (BFMsg , bfMsg) mClientDone ≡ just (S-loop nDone)
        h rewrite ≟-diagM mClientDone = refl
-- client leaf: CB-cdone sends bfIn!mClientDone → CB-loop stDone.
cl-CBcdone-bfin : CB-cdone ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = mClientDone })) ]─► CB-loop stDone
cl-CBcdone-bfin = sVis refl h
  where h : viewV (PTree.force CB-cdone) (BFMsg , bfIn) mClientDone ≡ just (CB-loop stDone)
        h rewrite ≟-diagM mClientDone = refl
-- server leaf: ISn stIdle receives bfOut!mClientDone → SB-loop stDone.
sv-ISidle-bfout-cdone : ISn stIdle ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = mClientDone })) ]─► SB-loop stDone
sv-ISidle-bfout-cdone = sVis refl refl
-- hop 1 (bfIn sync): Cd → Cdh.
im-Cd-bfin : JN (Inner CB-cdone (ISn stIdle)) Cidle ─[ τ ]─► JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone)
im-Cd-bfin = Hide-hidden ioBF (Par ioBF mrg2 (Inner CB-cdone (ISn stIdle)) Cidle) Poly.tt
  (Par-sync ioBF mrg2 (Inner CB-cdone (ISn stIdle)) Cidle Poly.tt
    (Par-soloL ∅ES mrg CB-cdone (ISn stIdle) (λ z → z) cl-CBcdone-bfin refl)
    (copy-Cidle-bfin mClientDone))
-- hop 2 (bfOut sync), client looped: Cdh → Cd3.
im-Cdh-bfout : JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone) ─[ τ ]─► JN (Inner (CB-loop stDone) (SB-loop stDone)) Cret
im-Cdh-bfout = Hide-hidden ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone)) Poly.tt
  (Par-sync ioBF mrg2 (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone) Poly.tt
    (Par-soloR ∅ES mrg (CB-loop stDone) (ISn stIdle) (λ z → z) sv-ISidle-bfout-cdone refl)
    (copy-Chold-bfout mClientDone))
-- hop 2 (bfOut sync), client settled done: Cd2 → CdR.
im-Cd2-bfout : JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone) ─[ τ ]─► JN (Inner (ICn stDone) (SB-loop stDone)) Cret
im-Cd2-bfout = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone)) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone) Poly.tt
    (Par-soloR ∅ES mrg (ICn stDone) (ISn stIdle) (λ z → z) sv-ISidle-bfout-cdone refl)
    (copy-Chold-bfout mClientDone))

------------------------------------------------------------------------
-- rsCd : JN (Inner CB-cdone (ISn stIdle)) Cidle  ≈  S-cdone.
------------------------------------------------------------------------
rs_Cd_fwd_ev : ∀ {l W′} → JN (Inner CB-cdone (ISn stIdle)) Cidle ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cd_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner CB-cdone (ISn stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-cdone} {sv = ISn stIdle} {cp = Cidle} CBcdone-no-bfMsg (ISn-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner CB-cdone (ISn stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg CB-cdone (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBcdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBcdone-no-api clst)

rs_Cd_fwd_tau : ∀ {W′} → JN (Inner CB-cdone (ISn stIdle)) Cidle ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cd_fwd_tau st with netCdone-τ st
... | refl = _ , wτ τ*-refl , rsCdh

rs_Cd_bwd_ev : ∀ {l S′} → (S-cdone ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner CB-cdone (ISn stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Cd_bwd_ev st with Hide-ev-elim bfMsgES S-cdone st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_Cd_bwd_tau : ∀ {S′} → (S-cdone ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner CB-cdone (ISn stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Cd_bwd_tau st with S-cdone-τ st
... | refl = _ , wτ (τ*-step im-Cd-bfin (τ*-step im-Cdh-bfout τ*-refl)) , rsCd3

------------------------------------------------------------------------
-- rsCdh : JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone)  ≈  S-cdone.
------------------------------------------------------------------------
rs_Cdh_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone) ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cdh_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stDone} {sv = ISn stIdle} {cp = Chold mClientDone} (CBloop-no-bfMsg {stDone}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stDone) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_Cdh_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone) ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cdh_fwd_tau st with netCdh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsCd2
... | inj₂ refl = _ , wτ (τ*-step sp-Scdone-τ τ*-refl) , rsCd3

rs_Cdh_bwd_ev : ∀ {l S′} → (S-cdone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_Cdh_bwd_ev st with Hide-ev-elim bfMsgES S-cdone st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_Cdh_bwd_tau : ∀ {S′} → (S-cdone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (ISn stIdle)) (Chold mClientDone) ═[ τ ]═► W′ × RState W′ S′)
rs_Cdh_bwd_tau st with S-cdone-τ st
... | refl = _ , wτ (τ*-step im-Cdh-bfout τ*-refl) , rsCd3

------------------------------------------------------------------------
-- rsCd2 : JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone)  ≈  S-cdone.
------------------------------------------------------------------------
rs_Cd2_fwd_ev : ∀ {l W′} → JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone) ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cd2_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stDone} {sv = ISn stIdle} {cp = Chold mClientDone} (ICn-no-bfMsg {stDone}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stDone) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICdone-no-api clst)

rs_Cd2_fwd_tau : ∀ {W′} → JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone) ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cd2_fwd_tau st with netCd2-τ st
... | refl = _ , wτ (τ*-step sp-Scdone-τ τ*-refl) , rsCdR

rs_Cd2_bwd_ev : ∀ {l S′} → (S-cdone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_Cd2_bwd_ev st with Hide-ev-elim bfMsgES S-cdone st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_Cd2_bwd_tau : ∀ {S′} → (S-cdone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (ISn stIdle)) (Chold mClientDone) ═[ τ ]═► W′ × RState W′ S′)
rs_Cd2_bwd_tau st with S-cdone-τ st
... | refl = _ , wτ (τ*-step im-Cd2-bfout τ*-refl) , rsCdR

------------------------------------------------------------------------
-- rsDone / rsCd7 : the done configs.  Spec IT nDone now DEADLOCKS (empty
-- react): no √, no visible, no τ; the network done-config likewise offers
-- nothing (both peers ret, but the copy blocks the outer √).  All four helpers
-- are vacuous / noτ.
------------------------------------------------------------------------
-- rsDone : JN (Inner (ICn stDone) (ISn stDone)) Cidle  ≈  IT nDone.
rs_Done_fwd_ev : ∀ {l W′} → JN (Inner (ICn stDone) (ISn stDone)) Cidle ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((IT nDone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Done_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stDone) (ISn stDone)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stDone} {sv = ISn stDone} {cp = Cidle} (ICn-no-bfMsg {stDone}) (ISn-no-bfMsg {stDone}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stDone) (ISn stDone)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stDone) (ISn stDone) ist
...     | evL ¬m3 clst = ⊥-elim (ICdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICdone-no-api clst)

rs_Done_fwd_tau : ∀ {W′} → JN (Inner (ICn stDone) (ISn stDone)) Cidle ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((IT nDone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Done_fwd_tau st = ⊥-elim (netZ-noτ st)

rs_Done_bwd_ev : ∀ {l S′} → (IT nDone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (ISn stDone)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Done_bwd_ev st with Hide-ev-elim bfMsgES (IT nDone) st
... | he√ ()
... | heV P' ¬m (sVis refl ())

rs_Done_bwd_tau : ∀ {S′} → (IT nDone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (ISn stDone)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Done_bwd_tau st = ⊥-elim (spec-noτ sDone st)

-- rsCd7 : JN (Inner (ICn stDone) (ISn stDone)) Cret  ≈  IT nDone.
rs_Cd7_fwd_ev : ∀ {l W′} → JN (Inner (ICn stDone) (ISn stDone)) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nDone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Cd7_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stDone) (ISn stDone)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stDone} {sv = ISn stDone} {cp = Cret} (ICn-no-bfMsg {stDone}) (ISn-no-bfMsg {stDone}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stDone) (ISn stDone)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stDone) (ISn stDone) ist
...     | evL ¬m3 clst = ⊥-elim (ICdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICdone-no-api clst)

rs_Cd7_fwd_tau : ∀ {W′} → JN (Inner (ICn stDone) (ISn stDone)) Cret ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((IT nDone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Cd7_fwd_tau st with netCd7-τ st
... | refl = _ , wτ τ*-refl , rsDone

rs_Cd7_bwd_ev : ∀ {l S′} → (IT nDone ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (ISn stDone)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_Cd7_bwd_ev st with Hide-ev-elim bfMsgES (IT nDone) st
... | he√ ()
... | heV P' ¬m (sVis refl ())

rs_Cd7_bwd_tau : ∀ {S′} → (IT nDone ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (ISn stDone)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_Cd7_bwd_tau st = ⊥-elim (spec-noτ sDone st)

------------------------------------------------------------------------
-- Re-issue clusters (rsReqR/Si/Sr/IBSirr/LbBh ↔ S-req r ; rsCdRi/Si/Sr/IDScd/
-- LdCdh ↔ S-cdone): configs where a prior round still drains the copy/server
-- while the client re-commits.  Every network τ merely advances an
-- interleaving (fwd_tau = stutter into a sibling); bwd_tau builds a longer
-- copy-drain + loop-back + bfIn/bfOut-sync cascade to a paired S-req2 / S-loop
-- nDone config.  We use three POLYMORPHIC loop-back τ builders.
------------------------------------------------------------------------
-- copy loop-back leaf: Cret → Cidle.
copy-Cret-τ : Cret ─[ τ ]─► Cidle
copy-Cret-τ = sSil refl
-- polymorphic copy-drain τ: Cret → Cidle in any (cl,sv) frame.
im-cploop : ∀ cl sv → JN (Inner cl sv) Cret ─[ τ ]─► JN (Inner cl sv) Cidle
im-cploop cl sv = Hide-τ ioBF (Par ioBF mrg2 (Inner cl sv) Cret)
  (Par-τ-R ioBF mrg2 (Inner cl sv) Cret copy-Cret-τ)
-- polymorphic server loop-back τ: SB-loop s → ISn s in any (cl,cp) frame.
im-svloop : ∀ cl cp s → JN (Inner cl (SB-loop s)) cp ─[ τ ]─► JN (Inner cl (ISn s)) cp
im-svloop cl cp s = Hide-τ ioBF (Par ioBF mrg2 (Inner cl (SB-loop s)) cp)
  (Par-τ-L ioBF mrg2 (Inner cl (SB-loop s)) cp (Par-τ-R ∅ES mrg cl (SB-loop s) (sv-SBloop-τ s)))
-- polymorphic client loop-back τ: CB-loop s → ICn s in any (sv,cp) frame.
im-clloop : ∀ sv cp s → JN (Inner (CB-loop s) sv) cp ─[ τ ]─► JN (Inner (ICn s) sv) cp
im-clloop sv cp s = Hide-τ ioBF (Par ioBF mrg2 (Inner (CB-loop s) sv) cp)
  (Par-τ-L ioBF mrg2 (Inner (CB-loop s) sv) cp (Par-τ-L ∅ES mrg (CB-loop s) sv (cl-CBloop-τ s)))

------------------------------------------------------------------------
-- rsReqR : JN (Inner (CB-req r) (ISn stIdle)) Cret  ≈  S-req r.
------------------------------------------------------------------------
rs_ReqR_fwd_ev : ∀ r {l W′} → JN (Inner (CB-req r) (ISn stIdle)) Cret ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqR_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-req r) (ISn stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-req r} {sv = ISn stIdle} {cp = Cret} CBreq-no-bfMsg (ISn-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-req r) (ISn stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-req r) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBreq-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBreq-no-api clst)

rs_ReqR_fwd_tau : ∀ r {W′} → JN (Inner (CB-req r) (ISn stIdle)) Cret ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqR_fwd_tau r st with netReqR-τ st
... | refl = _ , wτ τ*-refl , rsReqB r

rs_ReqR_bwd_ev : ∀ r {l S′} → (S-req r ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-req r) (ISn stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqR_bwd_ev r st with Hide-ev-elim bfMsgES (S-req r) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_ReqR_bwd_tau : ∀ r {S′} → (S-req r ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-req r) (ISn stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_ReqR_bwd_tau r st with S-req-τ st
... | refl = _ , wτ (τ*-step (im-cploop (CB-req r) (ISn stIdle)) (τ*-step (im-B-bfin r) (τ*-step (im-Bh-bfout r) τ*-refl))) , rsReqB3 r

------------------------------------------------------------------------
-- rsReqSi : JN (Inner (CB-req r) (SB-loop stIdle)) Cidle  ≈  S-req r.
------------------------------------------------------------------------
rs_ReqSi_fwd_ev : ∀ r {l W′} → JN (Inner (CB-req r) (SB-loop stIdle)) Cidle ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqSi_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-req r) (SB-loop stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-req r} {sv = SB-loop stIdle} {cp = Cidle} CBreq-no-bfMsg (SBloop-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-req r) (SB-loop stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-req r) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBreq-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBreq-no-api clst)

rs_ReqSi_fwd_tau : ∀ r {W′} → JN (Inner (CB-req r) (SB-loop stIdle)) Cidle ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqSi_fwd_tau r st with netReqSi-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsReqB r
... | inj₂ refl = _ , wτ τ*-refl , rsLbBh r

rs_ReqSi_bwd_ev : ∀ r {l S′} → (S-req r ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-req r) (SB-loop stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqSi_bwd_ev r st with Hide-ev-elim bfMsgES (S-req r) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_ReqSi_bwd_tau : ∀ r {S′} → (S-req r ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (CB-req r) (SB-loop stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_ReqSi_bwd_tau r st with S-req-τ st
... | refl = _ , wτ (τ*-step (im-svloop (CB-req r) Cidle stIdle) (τ*-step (im-B-bfin r) (τ*-step (im-Bh-bfout r) τ*-refl))) , rsReqB3 r

------------------------------------------------------------------------
-- rsReqSr : JN (Inner (CB-req r) (SB-loop stIdle)) Cret  ≈  S-req r.
------------------------------------------------------------------------
rs_ReqSr_fwd_ev : ∀ r {l W′} → JN (Inner (CB-req r) (SB-loop stIdle)) Cret ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_ReqSr_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-req r) (SB-loop stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-req r} {sv = SB-loop stIdle} {cp = Cret} CBreq-no-bfMsg (SBloop-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-req r) (SB-loop stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-req r) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBreq-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBreq-no-api clst)

rs_ReqSr_fwd_tau : ∀ r {W′} → JN (Inner (CB-req r) (SB-loop stIdle)) Cret ─[ τ ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_ReqSr_fwd_tau r st with netReqSr-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsReqR r
... | inj₂ refl = _ , wτ τ*-refl , rsReqSi r

rs_ReqSr_bwd_ev : ∀ r {l S′} → (S-req r ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-req r) (SB-loop stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_ReqSr_bwd_ev r st with Hide-ev-elim bfMsgES (S-req r) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_ReqSr_bwd_tau : ∀ r {S′} → (S-req r ∖ bfMsgES) ─[ τ ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (CB-req r) (SB-loop stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_ReqSr_bwd_tau r st with S-req-τ st
... | refl = _ , wτ (τ*-step (im-svloop (CB-req r) Cret stIdle) (τ*-step (im-cploop (CB-req r) (ISn stIdle)) (τ*-step (im-B-bfin r) (τ*-step (im-Bh-bfout r) τ*-refl)))) , rsReqB3 r

------------------------------------------------------------------------
-- rsIBSirr : JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r))  ≈  S-req r.
------------------------------------------------------------------------
rs_IBSirr_fwd_ev : ∀ r {l W′} → JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ─[ ev l ]─► W′
                → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_IBSirr_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-loop stIdle} {cp = Chold (mRequestRange r)} (ICn-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)

rs_IBSirr_fwd_tau : ∀ r {W′} → JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► W′
                 → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_IBSirr_fwd_tau r st with netIBSirr-τ st
... | refl = _ , wτ τ*-refl , rsReqB2 r

rs_IBSirr_bwd_ev : ∀ r {l S′} → (S-req r ∖ bfMsgES) ─[ ev l ]─► S′
                → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ═[ ev l ]═► W′ × RState W′ S′)
rs_IBSirr_bwd_ev r st with Hide-ev-elim bfMsgES (S-req r) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_IBSirr_bwd_tau : ∀ r {S′} → (S-req r ∖ bfMsgES) ─[ τ ]─► S′
                 → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ═[ τ ]═► W′ × RState W′ S′)
rs_IBSirr_bwd_tau r st with S-req-τ st
... | refl = _ , wτ (τ*-step (im-svloop (ICn stBusy) (Chold (mRequestRange r)) stIdle) (τ*-step (im-B2-bfout r) τ*-refl)) , rsReqB4 r

------------------------------------------------------------------------
-- rsLbBh : JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r))  ≈  S-req r.
------------------------------------------------------------------------
rs_LbBh_fwd_ev : ∀ r {l W′} → JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbBh_fwd_ev r st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-loop stIdle} {cp = Chold (mRequestRange r)} (CBloop-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_LbBh_fwd_tau : ∀ r {W′} → JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-req r ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbBh_fwd_tau r st with netLbBh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsIBSirr r
... | inj₂ refl = _ , wτ τ*-refl , rsReqBh r

rs_LbBh_bwd_ev : ∀ r {l S′} → (S-req r ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ═[ ev l ]═► W′ × RState W′ S′)
rs_LbBh_bwd_ev r st with Hide-ev-elim bfMsgES (S-req r) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_LbBh_bwd_tau : ∀ r {S′} → (S-req r ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold (mRequestRange r)) ═[ τ ]═► W′ × RState W′ S′)
rs_LbBh_bwd_tau r st with S-req-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) (Chold (mRequestRange r)) stBusy) (τ*-step (im-svloop (ICn stBusy) (Chold (mRequestRange r)) stIdle) (τ*-step (im-B2-bfout r) τ*-refl))) , rsReqB4 r

------------------------------------------------------------------------
-- rsCdRi : JN (Inner CB-cdone (ISn stIdle)) Cret  ≈  S-cdone.
------------------------------------------------------------------------
rs_CdRi_fwd_ev : ∀ {l W′} → JN (Inner CB-cdone (ISn stIdle)) Cret ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_CdRi_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner CB-cdone (ISn stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-cdone} {sv = ISn stIdle} {cp = Cret} CBcdone-no-bfMsg (ISn-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner CB-cdone (ISn stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg CB-cdone (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBcdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBcdone-no-api clst)

rs_CdRi_fwd_tau : ∀ {W′} → JN (Inner CB-cdone (ISn stIdle)) Cret ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_CdRi_fwd_tau st with netCdR-τ st
... | refl = _ , wτ τ*-refl , rsCd

rs_CdRi_bwd_ev : ∀ {l S′} → (S-cdone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner CB-cdone (ISn stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_CdRi_bwd_ev st with Hide-ev-elim bfMsgES S-cdone st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_CdRi_bwd_tau : ∀ {S′} → (S-cdone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner CB-cdone (ISn stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_CdRi_bwd_tau st with S-cdone-τ st
... | refl = _ , wτ (τ*-step (im-cploop CB-cdone (ISn stIdle)) (τ*-step im-Cd-bfin (τ*-step im-Cdh-bfout τ*-refl))) , rsCd3

------------------------------------------------------------------------
-- rsCdSi : JN (Inner CB-cdone (SB-loop stIdle)) Cidle  ≈  S-cdone.
------------------------------------------------------------------------
rs_CdSi_fwd_ev : ∀ {l W′} → JN (Inner CB-cdone (SB-loop stIdle)) Cidle ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_CdSi_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner CB-cdone (SB-loop stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-cdone} {sv = SB-loop stIdle} {cp = Cidle} CBcdone-no-bfMsg (SBloop-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner CB-cdone (SB-loop stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg CB-cdone (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBcdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBcdone-no-api clst)

rs_CdSi_fwd_tau : ∀ {W′} → JN (Inner CB-cdone (SB-loop stIdle)) Cidle ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_CdSi_fwd_tau st with netCdSi-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsCd
... | inj₂ refl = _ , wτ τ*-refl , rsLdCdh

rs_CdSi_bwd_ev : ∀ {l S′} → (S-cdone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner CB-cdone (SB-loop stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_CdSi_bwd_ev st with Hide-ev-elim bfMsgES S-cdone st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_CdSi_bwd_tau : ∀ {S′} → (S-cdone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner CB-cdone (SB-loop stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_CdSi_bwd_tau st with S-cdone-τ st
... | refl = _ , wτ (τ*-step (im-svloop CB-cdone Cidle stIdle) (τ*-step im-Cd-bfin (τ*-step im-Cdh-bfout τ*-refl))) , rsCd3

------------------------------------------------------------------------
-- rsCdSr : JN (Inner CB-cdone (SB-loop stIdle)) Cret  ≈  S-cdone.
------------------------------------------------------------------------
rs_CdSr_fwd_ev : ∀ {l W′} → JN (Inner CB-cdone (SB-loop stIdle)) Cret ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_CdSr_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner CB-cdone (SB-loop stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-cdone} {sv = SB-loop stIdle} {cp = Cret} CBcdone-no-bfMsg (SBloop-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner CB-cdone (SB-loop stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg CB-cdone (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBcdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBcdone-no-api clst)

rs_CdSr_fwd_tau : ∀ {W′} → JN (Inner CB-cdone (SB-loop stIdle)) Cret ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_CdSr_fwd_tau st with netCdSr-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsCdRi
... | inj₂ refl = _ , wτ τ*-refl , rsCdSi

rs_CdSr_bwd_ev : ∀ {l S′} → (S-cdone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner CB-cdone (SB-loop stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_CdSr_bwd_ev st with Hide-ev-elim bfMsgES S-cdone st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_CdSr_bwd_tau : ∀ {S′} → (S-cdone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner CB-cdone (SB-loop stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_CdSr_bwd_tau st with S-cdone-τ st
... | refl = _ , wτ (τ*-step (im-svloop CB-cdone Cret stIdle) (τ*-step (im-cploop CB-cdone (ISn stIdle)) (τ*-step im-Cd-bfin (τ*-step im-Cdh-bfout τ*-refl)))) , rsCd3

------------------------------------------------------------------------
-- rsIDScd : JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone)  ≈  S-cdone.
------------------------------------------------------------------------
rs_IDScd_fwd_ev : ∀ {l W′} → JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone) ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_IDScd_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stDone} {sv = SB-loop stIdle} {cp = Chold mClientDone} (ICn-no-bfMsg {stDone}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stDone) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICdone-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICdone-no-api clst)

rs_IDScd_fwd_tau : ∀ {W′} → JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone) ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_IDScd_fwd_tau st with netIDScd-τ st
... | refl = _ , wτ τ*-refl , rsCd2

rs_IDScd_bwd_ev : ∀ {l S′} → (S-cdone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_IDScd_bwd_ev st with Hide-ev-elim bfMsgES S-cdone st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_IDScd_bwd_tau : ∀ {S′} → (S-cdone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stDone) (SB-loop stIdle)) (Chold mClientDone) ═[ τ ]═► W′ × RState W′ S′)
rs_IDScd_bwd_tau st with S-cdone-τ st
... | refl = _ , wτ (τ*-step (im-svloop (ICn stDone) (Chold mClientDone) stIdle) (τ*-step im-Cd2-bfout τ*-refl)) , rsCdR

------------------------------------------------------------------------
-- rsLdCdh : JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone)  ≈  S-cdone.
------------------------------------------------------------------------
rs_LdCdh_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone) ─[ ev l ]─► W′
              → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LdCdh_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stDone} {sv = SB-loop stIdle} {cp = Chold mClientDone} (CBloop-no-bfMsg {stDone}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stDone) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)

rs_LdCdh_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone) ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-cdone ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LdCdh_fwd_tau st with netLdCdh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsIDScd
... | inj₂ refl = _ , wτ τ*-refl , rsCdh

rs_LdCdh_bwd_ev : ∀ {l S′} → (S-cdone ∖ bfMsgES) ─[ ev l ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_LdCdh_bwd_ev st with Hide-ev-elim bfMsgES S-cdone st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())

rs_LdCdh_bwd_tau : ∀ {S′} → (S-cdone ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stDone) (SB-loop stIdle)) (Chold mClientDone) ═[ τ ]═► W′ × RState W′ S′)
rs_LdCdh_bwd_tau st with S-cdone-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) (Chold mClientDone) stDone) (τ*-step (im-svloop (ICn stDone) (Chold mClientDone) stIdle) (τ*-step im-Cd2-bfout τ*-refl))) , rsCdR

------------------------------------------------------------------------
-- noBlocks hop (rsN/IBNr/LbNi/LbNr/Nh/N2/LbNh/LbN2 ↔ S-noblk): the SERVER
-- sends mNoBlocks (SB-noblk → SB-loop stIdle) into the copy, which delivers it
-- to the CLIENT (ICn stBusy → CB-loop stIdle).  Spec S-noblk hides a
-- bfMsg(mNoBlocks) τ to S-loop nIdle (realised in the network at CLIENT
-- delivery, i.e. the copy bfOut hop).
------------------------------------------------------------------------
-- spec hidden bfMsg τ: S-noblk → S-loop nIdle.
sp-Snoblk-τ : (S-noblk ∖ bfMsgES) ─[ τ ]─► (S-loop nIdle ∖ bfMsgES)
sp-Snoblk-τ = Hide-hidden bfMsgES S-noblk {e = bfMsg} {a = mNoBlocks} Poly.tt (sVis refl h)
  where h : viewV (PTree.force S-noblk) (BFMsg , bfMsg) mNoBlocks ≡ just (S-loop nIdle)
        h rewrite ≟-diagM mNoBlocks = refl
-- server leaf: SB-noblk sends bfIn!mNoBlocks → SB-loop stIdle.
sv-SBnoblk-bfin : SB-noblk ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = mNoBlocks })) ]─► SB-loop stIdle
sv-SBnoblk-bfin = sVis refl h
  where h : viewV (PTree.force SB-noblk) (BFMsg , bfIn) mNoBlocks ≡ just (SB-loop stIdle)
        h rewrite ≟-diagM mNoBlocks = refl
-- client leaf: ICn stBusy receives bfOut!mNoBlocks → CB-loop stIdle.
cl-ICbusy-bfout-noblk : ICn stBusy ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = mNoBlocks })) ]─► CB-loop stIdle
cl-ICbusy-bfout-noblk = sVis refl refl
-- hop 1 (server bfIn sync): N → Nh.
im-N-bfin : JN (Inner (ICn stBusy) SB-noblk) Cidle ─[ τ ]─► JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks)
im-N-bfin = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stBusy) SB-noblk) Cidle) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stBusy) SB-noblk) Cidle Poly.tt
    (Par-soloR ∅ES mrg (ICn stBusy) SB-noblk (λ z → z) sv-SBnoblk-bfin refl)
    (copy-Cidle-bfin mNoBlocks))
-- hop 2 (client bfOut sync): Nh → N3.
im-Nh-bfout : JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ─[ τ ]─► JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret
im-Nh-bfout = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks)) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks) Poly.tt
    (Par-soloL ∅ES mrg (ICn stBusy) (SB-loop stIdle) (λ z → z) cl-ICbusy-bfout-noblk refl)
    (copy-Chold-bfout mNoBlocks))
-- hop 2 (client bfOut sync), server already settled idle: N2 → N5.
im-N2-bfout : JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks) ─[ τ ]─► JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret
im-N2-bfout = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks)) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks) Poly.tt
    (Par-soloL ∅ES mrg (ICn stBusy) (ISn stIdle) (λ z → z) cl-ICbusy-bfout-noblk refl)
    (copy-Chold-bfout mNoBlocks))

-- rsN : JN (Inner (ICn stBusy) SB-noblk) Cidle  ≈  S-noblk.
rs_N_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) SB-noblk) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) SB-noblk) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-noblk} {cp = Cidle} (ICn-no-bfMsg {stBusy}) SBnoblk-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) SB-noblk) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) SB-noblk ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBnoblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_N_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) SB-noblk) Cidle ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N_fwd_tau st with netN-τ st
... | refl = _ , wτ τ*-refl , rsNh
rs_N_bwd_ev : ∀ {l S′} → (S-noblk ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-noblk) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_N_bwd_ev st with Hide-ev-elim bfMsgES S-noblk st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_N_bwd_tau : ∀ {S′} → (S-noblk ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-noblk) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_N_bwd_tau st with S-noblk-τ st
... | refl = _ , wτ (τ*-step im-N-bfin (τ*-step im-Nh-bfout τ*-refl)) , rsN3

-- rsIBNr : JN (Inner (ICn stBusy) SB-noblk) Cret  ≈  S-noblk.
rs_IBNr_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) SB-noblk) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_IBNr_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) SB-noblk) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-noblk} {cp = Cret} (ICn-no-bfMsg {stBusy}) SBnoblk-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) SB-noblk) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) SB-noblk ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBnoblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_IBNr_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) SB-noblk) Cret ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_IBNr_fwd_tau st with netIBNr-τ st
... | refl = _ , wτ τ*-refl , rsN
rs_IBNr_bwd_ev : ∀ {l S′} → (S-noblk ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-noblk) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_IBNr_bwd_ev st with Hide-ev-elim bfMsgES S-noblk st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_IBNr_bwd_tau : ∀ {S′} → (S-noblk ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-noblk) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_IBNr_bwd_tau st with S-noblk-τ st
... | refl = _ , wτ (τ*-step (im-cploop (ICn stBusy) SB-noblk) (τ*-step im-N-bfin (τ*-step im-Nh-bfout τ*-refl))) , rsN3

-- rsLbNi : JN (Inner (CB-loop stBusy) SB-noblk) Cidle  ≈  S-noblk.
rs_LbNi_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) SB-noblk) Cidle ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbNi_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) SB-noblk) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-noblk} {cp = Cidle} (CBloop-no-bfMsg {stBusy}) SBnoblk-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) SB-noblk) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) SB-noblk ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBnoblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbNi_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) SB-noblk) Cidle ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbNi_fwd_tau st with netLbNi-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsN
... | inj₂ refl = _ , wτ τ*-refl , rsLbNh
rs_LbNi_bwd_ev : ∀ {l S′} → (S-noblk ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-noblk) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_LbNi_bwd_ev st with Hide-ev-elim bfMsgES S-noblk st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_LbNi_bwd_tau : ∀ {S′} → (S-noblk ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-noblk) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_LbNi_bwd_tau st with S-noblk-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-noblk Cidle stBusy) (τ*-step im-N-bfin (τ*-step im-Nh-bfout τ*-refl))) , rsN3

-- rsLbNr : JN (Inner (CB-loop stBusy) SB-noblk) Cret  ≈  S-noblk.
rs_LbNr_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) SB-noblk) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbNr_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) SB-noblk) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-noblk} {cp = Cret} (CBloop-no-bfMsg {stBusy}) SBnoblk-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) SB-noblk) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) SB-noblk ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBnoblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbNr_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) SB-noblk) Cret ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbNr_fwd_tau st with netLbNr-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsIBNr
... | inj₂ refl = _ , wτ τ*-refl , rsLbNi
rs_LbNr_bwd_ev : ∀ {l S′} → (S-noblk ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-noblk) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_LbNr_bwd_ev st with Hide-ev-elim bfMsgES S-noblk st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_LbNr_bwd_tau : ∀ {S′} → (S-noblk ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-noblk) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_LbNr_bwd_tau st with S-noblk-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-noblk Cret stBusy) (τ*-step (im-cploop (ICn stBusy) SB-noblk) (τ*-step im-N-bfin (τ*-step im-Nh-bfout τ*-refl)))) , rsN3

-- rsNh : JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks)  ≈  S-noblk.
rs_Nh_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Nh_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-loop stIdle} {cp = Chold mNoBlocks} (ICn-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_Nh_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Nh_fwd_tau st with netNh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsN2
... | inj₂ refl = _ , wτ (τ*-step sp-Snoblk-τ τ*-refl) , rsN3
rs_Nh_bwd_ev : ∀ {l S′} → (S-noblk ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ═[ ev l ]═► W′ × RState W′ S′)
rs_Nh_bwd_ev st with Hide-ev-elim bfMsgES S-noblk st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_Nh_bwd_tau : ∀ {S′} → (S-noblk ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ═[ τ ]═► W′ × RState W′ S′)
rs_Nh_bwd_tau st with S-noblk-τ st
... | refl = _ , wτ (τ*-step im-Nh-bfout τ*-refl) , rsN3

-- rsN2 : JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks)  ≈  S-noblk.
rs_N2_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks) ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N2_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = ISn stIdle} {cp = Chold mNoBlocks} (ICn-no-bfMsg {stBusy}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_N2_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks) ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N2_fwd_tau st with netN2-τ st
... | refl = _ , wτ (τ*-step sp-Snoblk-τ τ*-refl) , rsN5
rs_N2_bwd_ev : ∀ {l S′} → (S-noblk ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks) ═[ ev l ]═► W′ × RState W′ S′)
rs_N2_bwd_ev st with Hide-ev-elim bfMsgES S-noblk st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_N2_bwd_tau : ∀ {S′} → (S-noblk ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stIdle)) (Chold mNoBlocks) ═[ τ ]═► W′ × RState W′ S′)
rs_N2_bwd_tau st with S-noblk-τ st
... | refl = _ , wτ (τ*-step im-N2-bfout τ*-refl) , rsN5

-- rsLbNh : JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks)  ≈  S-noblk.
rs_LbNh_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbNh_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-loop stIdle} {cp = Chold mNoBlocks} (CBloop-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbNh_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbNh_fwd_tau st with netLbNh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsNh
... | inj₂ refl = _ , wτ τ*-refl , rsLbN2
rs_LbNh_bwd_ev : ∀ {l S′} → (S-noblk ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ═[ ev l ]═► W′ × RState W′ S′)
rs_LbNh_bwd_ev st with Hide-ev-elim bfMsgES S-noblk st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_LbNh_bwd_tau : ∀ {S′} → (S-noblk ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stIdle)) (Chold mNoBlocks) ═[ τ ]═► W′ × RState W′ S′)
rs_LbNh_bwd_tau st with S-noblk-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) (Chold mNoBlocks) stBusy) (τ*-step im-Nh-bfout τ*-refl)) , rsN3

-- rsLbN2 : JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks)  ≈  S-noblk.
rs_LbN2_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks) ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbN2_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = ISn stIdle} {cp = Chold mNoBlocks} (CBloop-no-bfMsg {stBusy}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbN2_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks) ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-noblk ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbN2_fwd_tau st with netLbN2-τ st
... | refl = _ , wτ τ*-refl , rsN2
rs_LbN2_bwd_ev : ∀ {l S′} → (S-noblk ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks) ═[ ev l ]═► W′ × RState W′ S′)
rs_LbN2_bwd_ev st with Hide-ev-elim bfMsgES S-noblk st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_LbN2_bwd_tau : ∀ {S′} → (S-noblk ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stIdle)) (Chold mNoBlocks) ═[ τ ]═► W′ × RState W′ S′)
rs_LbN2_bwd_tau st with S-noblk-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stIdle) (Chold mNoBlocks) stBusy) (τ*-step im-N2-bfout τ*-refl)) , rsN5

------------------------------------------------------------------------
-- idle-return region (rsN4/N7/N8 ↔ IT nIdle ; rsN3/N5/N6/N9 ↔ S-loop nIdle):
-- noBlocks delivered, both peers heading to idle.  IT nIdle is stable but
-- OFFERS the client apis (req/cdone); S-loop nIdle is a pure τ loop-back.
------------------------------------------------------------------------
-- polymorphic client req/cdone emit from a (ICn stIdle) frame.
im-idle-req : ∀ sv cp r → viewV (PTree.force sv) (ApiBFCar sendBFRequestRange , apiBF sendBFRequestRange) r ≡ nothing
            → viewV (PTree.force cp) (ApiBFCar sendBFRequestRange , apiBF sendBFRequestRange) r ≡ nothing
            → JN (Inner (ICn stIdle) sv) cp ─[ ev (nReq r) ]─► JN (Inner (CB-req r) sv) cp
im-idle-req sv cp r pv qv = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stIdle) sv) cp) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stIdle) sv) cp (λ z → z)
    (Par-soloL ∅ES mrg (ICn stIdle) sv (λ z → z) (cl-ICidle-req r) pv) qv)
im-idle-cdone : ∀ sv cp → viewV (PTree.force sv) (ApiBFCar sendBFClientDone , apiBF sendBFClientDone) tt ≡ nothing
              → viewV (PTree.force cp) (ApiBFCar sendBFClientDone , apiBF sendBFClientDone) tt ≡ nothing
              → JN (Inner (ICn stIdle) sv) cp ─[ ev nCDone ]─► JN (Inner CB-cdone sv) cp
im-idle-cdone sv cp pv qv = Hide-keep ioBF (Par ioBF mrg2 (Inner (ICn stIdle) sv) cp) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (ICn stIdle) sv) cp (λ z → z)
    (Par-soloL ∅ES mrg (ICn stIdle) sv (λ z → z) cl-ICidle-cdone pv) qv)

-- rsN4 : JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret  ≈  IT nIdle.
rs_N4_fwd_ev : ∀ {l W′} → JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nIdle ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N4_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stIdle) (SB-loop stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stIdle} {sv = SB-loop stIdle} {cp = Cret} (ICn-no-bfMsg {stIdle}) (SBloop-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stIdle) (SB-loop stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stIdle) (SB-loop stIdle) ist
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBloop-no-ev svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) = _ , wev τ*-refl (sp-nIdle-req aa) τ*-refl , rsReqSr aa
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = _ , wev τ*-refl sp-nIdle-cdone τ*-refl , rsCdSr
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_N4_fwd_tau : ∀ {W′} → JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nIdle ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N4_fwd_tau st with netN4-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsN7
... | inj₂ refl = _ , wτ τ*-refl , rsN8
rs_N4_bwd_ev : ∀ {l S′} → (IT nIdle ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_N4_bwd_ev st with Hide-ev-elim bfMsgES (IT nIdle) st
... | he√ ()
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = r} refl refl) = _ , wev τ*-refl (im-idle-req (SB-loop stIdle) Cret r refl refl) τ*-refl , rsReqSr r
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = _ , wev τ*-refl (im-idle-cdone (SB-loop stIdle) Cret refl refl) τ*-refl , rsCdSr
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_N4_bwd_tau : ∀ {S′} → (IT nIdle ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_N4_bwd_tau st = ⊥-elim (spec-noτ sIdle st)

-- rsN7 : JN (Inner (ICn stIdle) (ISn stIdle)) Cret  ≈  IT nIdle.
rs_N7_fwd_ev : ∀ {l W′} → JN (Inner (ICn stIdle) (ISn stIdle)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nIdle ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N7_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stIdle} {sv = ISn stIdle} {cp = Cret} (ICn-no-bfMsg {stIdle}) (ISn-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stIdle) (ISn stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stIdle) (ISn stIdle) ist
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ISidle-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) = _ , wev τ*-refl (sp-nIdle-req aa) τ*-refl , rsReqR aa
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = _ , wev τ*-refl sp-nIdle-cdone τ*-refl , rsCdRi
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_N7_fwd_tau : ∀ {W′} → JN (Inner (ICn stIdle) (ISn stIdle)) Cret ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nIdle ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N7_fwd_tau st with netN7-τ st
... | refl = _ , wτ τ*-refl , rsIdle
rs_N7_bwd_ev : ∀ {l S′} → (IT nIdle ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stIdle) (ISn stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_N7_bwd_ev st with Hide-ev-elim bfMsgES (IT nIdle) st
... | he√ ()
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = r} refl refl) = _ , wev τ*-refl (im-idle-req (ISn stIdle) Cret r refl refl) τ*-refl , rsReqR r
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = _ , wev τ*-refl (im-idle-cdone (ISn stIdle) Cret refl refl) τ*-refl , rsCdRi
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_N7_bwd_tau : ∀ {S′} → (IT nIdle ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stIdle) (ISn stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_N7_bwd_tau st = ⊥-elim (spec-noτ sIdle st)

-- rsN8 : JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle  ≈  IT nIdle.
rs_N8_fwd_ev : ∀ {l W′} → JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nIdle ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N8_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stIdle) (SB-loop stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stIdle} {sv = SB-loop stIdle} {cp = Cidle} (ICn-no-bfMsg {stIdle}) (SBloop-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stIdle) (SB-loop stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stIdle) (SB-loop stIdle) ist
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBloop-no-ev svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) = _ , wev τ*-refl (sp-nIdle-req aa) τ*-refl , rsReqSi aa
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = _ , wev τ*-refl sp-nIdle-cdone τ*-refl , rsCdSi
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_N8_fwd_tau : ∀ {W′} → JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nIdle ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N8_fwd_tau st with netN8-τ st
... | refl = _ , wτ τ*-refl , rsIdle
rs_N8_bwd_ev : ∀ {l S′} → (IT nIdle ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_N8_bwd_ev st with Hide-ev-elim bfMsgES (IT nIdle) st
... | he√ ()
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = r} refl refl) = _ , wev τ*-refl (im-idle-req (SB-loop stIdle) Cidle r refl refl) τ*-refl , rsReqSi r
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = _ , wev τ*-refl (im-idle-cdone (SB-loop stIdle) Cidle refl refl) τ*-refl , rsCdSi
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_N8_bwd_tau : ∀ {S′} → (IT nIdle ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stIdle) (SB-loop stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_N8_bwd_tau st = ⊥-elim (spec-noτ sIdle st)

-- rsN3 : JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret  ≈  S-loop nIdle.
rs_N3_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nIdle ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N3_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = SB-loop stIdle} {cp = Cret} (CBloop-no-bfMsg {stIdle}) (SBloop-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N3_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nIdle ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N3_fwd_tau st with netN3-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nIdle) τ*-refl) , rsN4
... | inj₂ (inj₁ refl) = _ , wτ τ*-refl , rsN5
... | inj₂ (inj₂ refl) = _ , wτ τ*-refl , rsN6
rs_N3_bwd_ev : ∀ {l S′} → (S-loop nIdle ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_N3_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nIdle) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N3_bwd_tau : ∀ {S′} → (S-loop nIdle ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_N3_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) Cret stIdle) τ*-refl) , rsN4

-- rsN5 : JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret  ≈  S-loop nIdle.
rs_N5_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nIdle ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N5_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = ISn stIdle} {cp = Cret} (CBloop-no-bfMsg {stIdle}) (ISn-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N5_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nIdle ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N5_fwd_tau st with netN5-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nIdle) τ*-refl) , rsN7
... | inj₂ refl = _ , wτ τ*-refl , rsN9
rs_N5_bwd_ev : ∀ {l S′} → (S-loop nIdle ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_N5_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nIdle) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N5_bwd_tau : ∀ {S′} → (S-loop nIdle ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_N5_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stIdle) Cret stIdle) τ*-refl) , rsN7

-- rsN6 : JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle  ≈  S-loop nIdle.
rs_N6_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nIdle ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N6_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = SB-loop stIdle} {cp = Cidle} (CBloop-no-bfMsg {stIdle}) (SBloop-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N6_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nIdle ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N6_fwd_tau st with netN6-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nIdle) τ*-refl) , rsN8
... | inj₂ refl = _ , wτ τ*-refl , rsN9
rs_N6_bwd_ev : ∀ {l S′} → (S-loop nIdle ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_N6_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nIdle) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N6_bwd_tau : ∀ {S′} → (S-loop nIdle ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_N6_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) Cidle stIdle) τ*-refl) , rsN8

-- rsN9 : JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle  ≈  S-loop nIdle.
rs_N9_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nIdle ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N9_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = ISn stIdle} {cp = Cidle} (CBloop-no-bfMsg {stIdle}) (ISn-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N9_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nIdle ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N9_fwd_tau st with netN9-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ nIdle) τ*-refl) , rsIdle
rs_N9_bwd_ev : ∀ {l S′} → (S-loop nIdle ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_N9_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nIdle) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N9_bwd_tau : ∀ {S′} → (S-loop nIdle ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_N9_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stIdle) Cidle stIdle) τ*-refl) , rsIdle

------------------------------------------------------------------------
-- startBatch hop (rsM/IBMr/LbMi/LbMr ↔ S-sbatch ; rsMh/LbMh/M4/M8/M3/M6 ↔
-- S-loop nStr0): the SERVER sends mStartBatch (SB-sbatch → SB-loop stStreaming)
-- into the copy.  The spec S-sbatch hides a bfMsg(mStartBatch) τ to S-loop
-- nStr0, realised at the SERVER send (the parent maps the msg-in-copy configs
-- to the post-hop spec state).
------------------------------------------------------------------------
-- spec hidden bfMsg τ: S-sbatch → S-loop nStr0.
sp-Ssbatch-τ : (S-sbatch ∖ bfMsgES) ─[ τ ]─► (S-loop nStr0 ∖ bfMsgES)
sp-Ssbatch-τ = Hide-hidden bfMsgES S-sbatch {e = bfMsg} {a = mStartBatch} Poly.tt (sVis refl h)
  where h : viewV (PTree.force S-sbatch) (BFMsg , bfMsg) mStartBatch ≡ just (S-loop nStr0)
        h rewrite ≟-diagM mStartBatch = refl
-- server leaf: SB-sbatch sends bfIn!mStartBatch → SB-loop stStreaming.
sv-SBsbatch-bfin : SB-sbatch ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = mStartBatch })) ]─► SB-loop stStreaming
sv-SBsbatch-bfin = sVis refl h
  where h : viewV (PTree.force SB-sbatch) (BFMsg , bfIn) mStartBatch ≡ just (SB-loop stStreaming)
        h rewrite ≟-diagM mStartBatch = refl
-- hop 1 (server bfIn sync): M → Mh.
im-M-bfin : JN (Inner (ICn stBusy) SB-sbatch) Cidle ─[ τ ]─► JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch)
im-M-bfin = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stBusy) SB-sbatch) Cidle) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stBusy) SB-sbatch) Cidle Poly.tt
    (Par-soloR ∅ES mrg (ICn stBusy) SB-sbatch (λ z → z) sv-SBsbatch-bfin refl)
    (copy-Cidle-bfin mStartBatch))

-- rsM : JN (Inner (ICn stBusy) SB-sbatch) Cidle  ≈  S-sbatch.
rs_M_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) SB-sbatch) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-sbatch ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) SB-sbatch) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-sbatch} {cp = Cidle} (ICn-no-bfMsg {stBusy}) SBsbatch-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) SB-sbatch) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) SB-sbatch ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBsbatch-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_M_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) SB-sbatch) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-sbatch ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M_fwd_tau st with netM-τ st
... | refl = _ , wτ (τ*-step sp-Ssbatch-τ τ*-refl) , rsMh
rs_M_bwd_ev : ∀ {l S′} → (S-sbatch ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-sbatch) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_M_bwd_ev st with Hide-ev-elim bfMsgES S-sbatch st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_M_bwd_tau : ∀ {S′} → (S-sbatch ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-sbatch) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_M_bwd_tau st with S-sbatch-τ st
... | refl = _ , wτ (τ*-step im-M-bfin τ*-refl) , rsMh

-- rsIBMr : JN (Inner (ICn stBusy) SB-sbatch) Cret  ≈  S-sbatch.
rs_IBMr_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) SB-sbatch) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-sbatch ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_IBMr_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) SB-sbatch) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-sbatch} {cp = Cret} (ICn-no-bfMsg {stBusy}) SBsbatch-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) SB-sbatch) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) SB-sbatch ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBsbatch-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_IBMr_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) SB-sbatch) Cret ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-sbatch ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_IBMr_fwd_tau st with netIBMr-τ st
... | refl = _ , wτ τ*-refl , rsM
rs_IBMr_bwd_ev : ∀ {l S′} → (S-sbatch ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-sbatch) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_IBMr_bwd_ev st with Hide-ev-elim bfMsgES S-sbatch st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_IBMr_bwd_tau : ∀ {S′} → (S-sbatch ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-sbatch) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_IBMr_bwd_tau st with S-sbatch-τ st
... | refl = _ , wτ (τ*-step (im-cploop (ICn stBusy) SB-sbatch) (τ*-step im-M-bfin τ*-refl)) , rsMh

-- rsLbMi : JN (Inner (CB-loop stBusy) SB-sbatch) Cidle  ≈  S-sbatch.
rs_LbMi_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) SB-sbatch) Cidle ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-sbatch ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbMi_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) SB-sbatch) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-sbatch} {cp = Cidle} (CBloop-no-bfMsg {stBusy}) SBsbatch-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) SB-sbatch) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) SB-sbatch ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBsbatch-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbMi_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) SB-sbatch) Cidle ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-sbatch ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbMi_fwd_tau st with netLbMi-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsM
... | inj₂ refl = _ , wτ (τ*-step sp-Ssbatch-τ τ*-refl) , rsLbMh
rs_LbMi_bwd_ev : ∀ {l S′} → (S-sbatch ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-sbatch) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_LbMi_bwd_ev st with Hide-ev-elim bfMsgES S-sbatch st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_LbMi_bwd_tau : ∀ {S′} → (S-sbatch ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-sbatch) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_LbMi_bwd_tau st with S-sbatch-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-sbatch Cidle stBusy) (τ*-step im-M-bfin τ*-refl)) , rsMh

-- rsLbMr : JN (Inner (CB-loop stBusy) SB-sbatch) Cret  ≈  S-sbatch.
rs_LbMr_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) SB-sbatch) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-sbatch ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbMr_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) SB-sbatch) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-sbatch} {cp = Cret} (CBloop-no-bfMsg {stBusy}) SBsbatch-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) SB-sbatch) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) SB-sbatch ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBsbatch-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbMr_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) SB-sbatch) Cret ─[ τ ]─► W′
              → Σ[ S′ ∈ PT ] ((S-sbatch ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbMr_fwd_tau st with netLbMr-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsIBMr
... | inj₂ refl = _ , wτ τ*-refl , rsLbMi
rs_LbMr_bwd_ev : ∀ {l S′} → (S-sbatch ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-sbatch) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_LbMr_bwd_ev st with Hide-ev-elim bfMsgES S-sbatch st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_LbMr_bwd_tau : ∀ {S′} → (S-sbatch ∖ bfMsgES) ─[ τ ]─► S′
              → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-sbatch) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_LbMr_bwd_tau st with S-sbatch-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-sbatch Cret stBusy) (τ*-step (im-cploop (ICn stBusy) SB-sbatch) (τ*-step im-M-bfin τ*-refl))) , rsMh

-- rsMh : JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch)  ≈  S-loop nStr0.
rs_Mh_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Mh_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-loop stStreaming} {cp = Chold mStartBatch} (ICn-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_Mh_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Mh_fwd_tau st with netMh-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsSbM2
... | inj₂ refl = _ , wτ τ*-refl , rsM3
rs_Mh_bwd_ev : ∀ {l S′} → (S-loop nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ═[ ev l ]═► W′ × RState W′ S′)
rs_Mh_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStr0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_Mh_bwd_tau : ∀ {S′} → (S-loop nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ═[ τ ]═► W′ × RState W′ S′)
rs_Mh_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-svloop (ICn stBusy) (Chold mStartBatch) stStreaming) τ*-refl) , rsSbM2

-- rsLbMh : JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch)  ≈  S-loop nStr0.
rs_LbMh_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbMh_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-loop stStreaming} {cp = Chold mStartBatch} (CBloop-no-bfMsg {stBusy}) (SBloop-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbMh_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbMh_fwd_tau st with netLbMh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsMh
... | inj₂ refl = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsLbM2
rs_LbMh_bwd_ev : ∀ {l S′} → (S-loop nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ═[ ev l ]═► W′ × RState W′ S′)
rs_LbMh_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStr0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_LbMh_bwd_tau : ∀ {S′} → (S-loop nStr0 ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-loop stStreaming)) (Chold mStartBatch) ═[ τ ]═► W′ × RState W′ S′)
rs_LbMh_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stStreaming) (Chold mStartBatch) stBusy) (τ*-step (im-svloop (ICn stBusy) (Chold mStartBatch) stStreaming) τ*-refl)) , rsSbM2

-- rsM4 : JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret  ≈  S-loop nStr0.
rs_M4_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M4_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-loop stStreaming} {cp = Cret} (ICn-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stStreaming}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_M4_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M4_fwd_tau st with netM4-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsM7
... | inj₂ refl = _ , wτ τ*-refl , rsM8
rs_M4_bwd_ev : ∀ {l S′} → (S-loop nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_M4_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStr0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_M4_bwd_tau : ∀ {S′} → (S-loop nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_M4_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-svloop (ICn stStreaming) Cret stStreaming) τ*-refl) , rsM7

-- rsM8 : JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle  ≈  S-loop nStr0.
rs_M8_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M8_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-loop stStreaming} {cp = Cidle} (ICn-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stStreaming}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_M8_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M8_fwd_tau st with netM8-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsV0
rs_M8_bwd_ev : ∀ {l S′} → (S-loop nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_M8_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStr0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_M8_bwd_tau : ∀ {S′} → (S-loop nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_M8_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-svloop (ICn stStreaming) Cidle stStreaming) τ*-refl) , rsV0

-- rsM3 : JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret  ≈  S-loop nStr0.
rs_M3_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M3_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-loop stStreaming} {cp = Cret} (CBloop-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stStreaming}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_M3_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M3_fwd_tau st with netM3-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsM4
... | inj₂ (inj₁ refl) = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsM5
... | inj₂ (inj₂ refl) = _ , wτ τ*-refl , rsM6
rs_M3_bwd_ev : ∀ {l S′} → (S-loop nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_M3_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStr0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_M3_bwd_tau : ∀ {S′} → (S-loop nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_M3_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-svloop (CB-loop stStreaming) Cret stStreaming) τ*-refl) , rsM5

-- rsM6 : JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle  ≈  S-loop nStr0.
rs_M6_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M6_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-loop stStreaming} {cp = Cidle} (CBloop-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stStreaming}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_M6_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M6_fwd_tau st with netM6-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsM8
... | inj₂ refl = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsM9
rs_M6_bwd_ev : ∀ {l S′} → (S-loop nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_M6_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStr0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_M6_bwd_tau : ∀ {S′} → (S-loop nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_M6_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-svloop (CB-loop stStreaming) Cidle stStreaming) τ*-refl) , rsM9

------------------------------------------------------------------------
-- streaming entry, empty buffer (rsV0/M7/M9/M5/SbM2/LbM2 ↔ IT nStr0): the
-- SERVER (ISn stStreaming) offers the streaming apis sendBFBlock b (→ S-blk0 b)
-- and sendBFBatchDone (→ S-bd0).  Successors are Phase-C/D streaming/batch-done
-- constructors (declared, helpers land later).
------------------------------------------------------------------------
-- streaming api event labels.
nSBlk : Block → Event√ Rr
nSBlk b = evl (record { A = ApiBFCar sendBFBlock ; e = apiBF sendBFBlock ; a = b })
nBDone : Event√ Rr
nBDone = evl (record { A = ApiBFCar sendBFBatchDone ; e = apiBF sendBFBatchDone ; a = tt })
-- spec: IT nStr0 fires sendBFBlock b → S-blk0 b / sendBFBatchDone → S-bd0.
sp-nStr0-blk : ∀ b → (IT nStr0 ∖ bfMsgES) ─[ ev (nSBlk b) ]─► (S-blk0 b ∖ bfMsgES)
sp-nStr0-blk b = Hide-keep bfMsgES (IT nStr0) (λ z → z) (sVis refl refl)
sp-nStr0-bdone : (IT nStr0 ∖ bfMsgES) ─[ ev nBDone ]─► (S-bd0 ∖ bfMsgES)
sp-nStr0-bdone = Hide-keep bfMsgES (IT nStr0) (λ z → z) (sVis refl refl)
-- server leaves: ISn stStreaming fires sendBFBlock b → SB-blk b / sendBFBatchDone → SB-bdone.
sv-ISstr-blk : ∀ b → ISn stStreaming ─[ ev (nSBlk b) ]─► SB-blk b
sv-ISstr-blk b = sVis refl refl
sv-ISstr-bdone : ISn stStreaming ─[ ev nBDone ]─► SB-bdone
sv-ISstr-bdone = sVis refl refl
-- polymorphic server-solo streaming emits (server RIGHT of Inner) in any (cl,cp) frame.
im-str-blk : ∀ cl cp b → viewV (PTree.force cl) (ApiBFCar sendBFBlock , apiBF sendBFBlock) b ≡ nothing
           → viewV (PTree.force cp) (ApiBFCar sendBFBlock , apiBF sendBFBlock) b ≡ nothing
           → JN (Inner cl (ISn stStreaming)) cp ─[ ev (nSBlk b) ]─► JN (Inner cl (SB-blk b)) cp
im-str-blk cl cp b pv qv = Hide-keep ioBF (Par ioBF mrg2 (Inner cl (ISn stStreaming)) cp) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner cl (ISn stStreaming)) cp (λ z → z)
    (Par-soloR ∅ES mrg cl (ISn stStreaming) (λ z → z) (sv-ISstr-blk b) pv) qv)
im-str-bdone : ∀ cl cp → viewV (PTree.force cl) (ApiBFCar sendBFBatchDone , apiBF sendBFBatchDone) tt ≡ nothing
             → viewV (PTree.force cp) (ApiBFCar sendBFBatchDone , apiBF sendBFBatchDone) tt ≡ nothing
             → JN (Inner cl (ISn stStreaming)) cp ─[ ev nBDone ]─► JN (Inner cl SB-bdone) cp
im-str-bdone cl cp pv qv = Hide-keep ioBF (Par ioBF mrg2 (Inner cl (ISn stStreaming)) cp) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner cl (ISn stStreaming)) cp (λ z → z)
    (Par-soloR ∅ES mrg cl (ISn stStreaming) (λ z → z) sv-ISstr-bdone pv) qv)

-- rsV0 : JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle  ≈  IT nStr0.
rs_V0_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_V0_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = ISn stStreaming} {cp = Cidle} (ICn-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) = _ , wev τ*-refl (sp-nStr0-blk bb) τ*-refl , rsW bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl sp-nStr0-bdone τ*-refl , rsBD0e
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_V0_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_V0_fwd_tau st = ⊥-elim (netV0-noτ st)
rs_V0_bwd_ev : ∀ {l S′} → (IT nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_V0_bwd_ev st with Hide-ev-elim bfMsgES (IT nStr0) st
... | he√ ()
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev τ*-refl (im-str-blk (ICn stStreaming) Cidle b refl refl) τ*-refl , rsW b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (ICn stStreaming) Cidle refl refl) τ*-refl , rsBD0e
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_V0_bwd_tau : ∀ {S′} → (IT nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_V0_bwd_tau st = ⊥-elim (spec-noτ sStr0 st)

-- rsM7 : JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret  ≈  IT nStr0.
rs_M7_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M7_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = ISn stStreaming} {cp = Cret} (ICn-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) = _ , wev τ*-refl (sp-nStr0-blk bb) τ*-refl , rsWX3a bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl sp-nStr0-bdone τ*-refl , rsBX3a
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_M7_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M7_fwd_tau st with netM7-τ st
... | refl = _ , wτ τ*-refl , rsV0
rs_M7_bwd_ev : ∀ {l S′} → (IT nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_M7_bwd_ev st with Hide-ev-elim bfMsgES (IT nStr0) st
... | he√ ()
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev τ*-refl (im-str-blk (ICn stStreaming) Cret b refl refl) τ*-refl , rsWX3a b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (ICn stStreaming) Cret refl refl) τ*-refl , rsBX3a
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_M7_bwd_tau : ∀ {S′} → (IT nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stStreaming)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_M7_bwd_tau st = ⊥-elim (spec-noτ sStr0 st)

-- rsM9 : JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle  ≈  IT nStr0.
rs_M9_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M9_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = ISn stStreaming} {cp = Cidle} (CBloop-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) = _ , wev τ*-refl (sp-nStr0-blk bb) τ*-refl , rsWX1 bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl sp-nStr0-bdone τ*-refl , rsBX1
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_M9_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M9_fwd_tau st with netM9-τ st
... | refl = _ , wτ τ*-refl , rsV0
rs_M9_bwd_ev : ∀ {l S′} → (IT nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_M9_bwd_ev st with Hide-ev-elim bfMsgES (IT nStr0) st
... | he√ ()
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev τ*-refl (im-str-blk (CB-loop stStreaming) Cidle b refl refl) τ*-refl , rsWX1 b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (CB-loop stStreaming) Cidle refl refl) τ*-refl , rsBX1
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_M9_bwd_tau : ∀ {S′} → (IT nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_M9_bwd_tau st = ⊥-elim (spec-noτ sStr0 st)

-- rsM5 : JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret  ≈  IT nStr0.
rs_M5_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M5_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = ISn stStreaming} {cp = Cret} (CBloop-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) = _ , wev τ*-refl (sp-nStr0-blk bb) τ*-refl , rsWX3 bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl sp-nStr0-bdone τ*-refl , rsBX3
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_M5_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M5_fwd_tau st with netM5-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsM7
... | inj₂ refl = _ , wτ τ*-refl , rsM9
rs_M5_bwd_ev : ∀ {l S′} → (IT nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_M5_bwd_ev st with Hide-ev-elim bfMsgES (IT nStr0) st
... | he√ ()
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev τ*-refl (im-str-blk (CB-loop stStreaming) Cret b refl refl) τ*-refl , rsWX3 b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (CB-loop stStreaming) Cret refl refl) τ*-refl , rsBX3
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_M5_bwd_tau : ∀ {S′} → (IT nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_M5_bwd_tau st = ⊥-elim (spec-noτ sStr0 st)

-- rsSbM2 : JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch)  ≈  IT nStr0.
rs_SbM2_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch) ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_SbM2_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = ISn stStreaming} {cp = Chold mStartBatch} (ICn-no-bfMsg {stBusy}) (ISn-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) = _ , wev τ*-refl (sp-nStr0-blk bb) τ*-refl , rsIBblksb bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl sp-nStr0-bdone τ*-refl , rsIBbdsb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_SbM2_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch) ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_SbM2_fwd_tau st with netM2-τ st
... | refl = _ , wτ τ*-refl , rsM5
rs_SbM2_bwd_ev : ∀ {l S′} → (IT nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch) ═[ ev l ]═► W′ × RState W′ S′)
rs_SbM2_bwd_ev st with Hide-ev-elim bfMsgES (IT nStr0) st
... | he√ ()
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev τ*-refl (im-str-blk (ICn stBusy) (Chold mStartBatch) b refl refl) τ*-refl , rsIBblksb b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (ICn stBusy) (Chold mStartBatch) refl refl) τ*-refl , rsIBbdsb
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_SbM2_bwd_tau : ∀ {S′} → (IT nStr0 ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (ISn stStreaming)) (Chold mStartBatch) ═[ τ ]═► W′ × RState W′ S′)
rs_SbM2_bwd_tau st = ⊥-elim (spec-noτ sStr0 st)

-- rsLbM2 : JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch)  ≈  IT nStr0.
rs_LbM2_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch) ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbM2_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = ISn stStreaming} {cp = Chold mStartBatch} (CBloop-no-bfMsg {stBusy}) (ISn-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) = _ , wev τ*-refl (sp-nStr0-blk bb) τ*-refl , rsLbBLKsb bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl sp-nStr0-bdone τ*-refl , rsLbBDsb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_LbM2_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch) ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((IT nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbM2_fwd_tau st with netLbM2-τ st
... | refl = _ , wτ τ*-refl , rsSbM2
rs_LbM2_bwd_ev : ∀ {l S′} → (IT nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch) ═[ ev l ]═► W′ × RState W′ S′)
rs_LbM2_bwd_ev st with Hide-ev-elim bfMsgES (IT nStr0) st
... | he√ ()
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev τ*-refl (im-str-blk (CB-loop stBusy) (Chold mStartBatch) b refl refl) τ*-refl , rsLbBLKsb b
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (CB-loop stBusy) (Chold mStartBatch) refl refl) τ*-refl , rsLbBDsb
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_LbM2_bwd_tau : ∀ {S′} → (IT nStr0 ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (ISn stStreaming)) (Chold mStartBatch) ═[ τ ]═► W′ × RState W′ S′)
rs_LbM2_bwd_tau st = ⊥-elim (spec-noτ sStr0 st)

------------------------------------------------------------------------
-- Phase C: streaming core.  A resident block occupies one of three slots:
-- client CB-blk b (owes the observable recvBFBlock b, DELIVERABLE head), copy
-- Chold (mBlock b), server send-hold SB-blk b.  Head-order client ≻ copy ≻
-- server.  A bfIn sync drains a server-hold into the copy; a bfOut sync drains
-- the copy into the client (raising the client slot).
------------------------------------------------------------------------
-- Block decidable-equality diagonal (recvBFBlock / bfIn / bfOut are value-restricted).
≟-diagB : ∀ (b : Block) → (b ≟ b) ≡ yes refl
≟-diagB b = ≡-≟-identity _≟_ refl
-- spec hidden bfMsg τ: S-blk0 b → S-loop (nStr1 b).
sp-Sblk0-τ : ∀ b → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► (S-loop (nStr1 b) ∖ bfMsgES)
sp-Sblk0-τ b = Hide-hidden bfMsgES (S-blk0 b) {e = bfMsg} {a = mBlock b} Poly.tt (sVis refl (h b))
  where h : ∀ b → viewV (PTree.force (S-blk0 b)) (BFMsg , bfMsg) (mBlock b) ≡ just (S-loop (nStr1 b))
        h b rewrite ≟-diagM (mBlock b) = refl
-- spec hidden bfMsg τ: S-blk1 b b′ → S-loop (nStr2 b b′).
sp-Sblk1-τ : ∀ b b′ → (S-blk1 b b′ ∖ bfMsgES) ─[ τ ]─► (S-loop (nStr2 b b′) ∖ bfMsgES)
sp-Sblk1-τ b b′ = Hide-hidden bfMsgES (S-blk1 b b′) {e = bfMsg} {a = mBlock b′} Poly.tt (sVis refl (h b b′))
  where h : ∀ b b′ → viewV (PTree.force (S-blk1 b b′)) (BFMsg , bfMsg) (mBlock b′) ≡ just (S-loop (nStr2 b b′))
        h b b′ rewrite ≟-diagM (mBlock b′) = refl
-- server leaf: SB-blk b sends bfIn!(mBlock b) → SB-loop stStreaming.
sv-SBblk-bfin : ∀ b → SB-blk b ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = mBlock b })) ]─► SB-loop stStreaming
sv-SBblk-bfin b = sVis refl (h b)
  where h : ∀ b → viewV (PTree.force (SB-blk b)) (BFMsg , bfIn) (mBlock b) ≡ just (SB-loop stStreaming)
        h b rewrite ≟-diagM (mBlock b) = refl
-- client leaf: ICn stStreaming receives bfOut!(mBlock b) → CB-blk b.
cl-ICstr-bfout-blk : ∀ b → ICn stStreaming ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = mBlock b })) ]─► CB-blk b
cl-ICstr-bfout-blk b = sVis refl refl
-- client leaf: ICn stBusy receives bfOut!mStartBatch → CB-loop stStreaming.
cl-ICbusy-bfout-sbatch : ICn stBusy ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = mStartBatch })) ]─► CB-loop stStreaming
cl-ICbusy-bfout-sbatch = sVis refl refl
-- block-fill sync (server bfIn): (ICn stStreaming, SB-blk b, Cidle) → (…, SB-loop, Chold b).
im-Wsv-bfin : ∀ b → JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ─[ τ ]─► JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))
im-Wsv-bfin b = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cidle) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cidle Poly.tt
    (Par-soloR ∅ES mrg (ICn stStreaming) (SB-blk b) (λ z → z) (sv-SBblk-bfin b) refl)
    (copy-Cidle-bfin (mBlock b)))
-- block-deliver sync (client bfOut): (ICn stStreaming, SB-loop, Chold b) → (CB-blk b, SB-loop, Cret).
im-Wh-bfout : ∀ b → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ τ ]─► JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret
im-Wh-bfout b = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) Poly.tt
    (Par-soloL ∅ES mrg (ICn stStreaming) (SB-loop stStreaming) (λ z → z) (cl-ICstr-bfout-blk b) refl)
    (copy-Chold-bfout (mBlock b)))
-- startBatch-deliver sync (client bfOut): (ICn stBusy, SB-blk b, Chold sbatch) → (CB-loop stStreaming, SB-blk b, Cret).
im-IBblk-bfout : ∀ b → JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch) ─[ τ ]─► JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret
im-IBblk-bfout b = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch)) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch) Poly.tt
    (Par-soloL ∅ES mrg (ICn stBusy) (SB-blk b) (λ z → z) cl-ICbusy-bfout-sbatch refl)
    (copy-Chold-bfout mStartBatch))

-- rsW : JN (Inner (ICn stStreaming) (SB-blk b)) Cidle  ≈  S-blk0 b.
rs_W_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-blk b} {cp = Cidle} (ICn-no-bfMsg {stStreaming}) SBblk-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_W_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W_fwd_tau b st with netW-τ st
... | refl = _ , wτ τ*-refl , rsWh b
rs_W_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_W_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_W_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_W_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) τ*-refl)) , rsW3 b

-- rsWh : JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))  ≈  S-blk0 b.
rs_Wh_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Wh_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-loop stStreaming} {cp = Chold (mBlock b)} (ICn-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_Wh_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Wh_fwd_tau b st with netWh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsW2 b
... | inj₂ refl = _ , wτ (τ*-step (sp-Sblk0-τ b) τ*-refl) , rsW3 b
rs_Wh_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_Wh_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_Wh_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_Wh_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-Wh-bfout b) τ*-refl) , rsW3 b

-- rsWX3a : JN (Inner (ICn stStreaming) (SB-blk b)) Cret  ≈  S-blk0 b.
rs_WX3a_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) (SB-blk b)) Cret ─[ ev l ]─► W′
             → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_WX3a_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-blk b} {cp = Cret} (ICn-no-bfMsg {stStreaming}) SBblk-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_WX3a_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) (SB-blk b)) Cret ─[ τ ]─► W′
             → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_WX3a_fwd_tau b st with netWX3a-τ st
... | refl = _ , wτ τ*-refl , rsW b
rs_WX3a_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_WX3a_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_WX3a_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
             → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_WX3a_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-cploop (ICn stStreaming) (SB-blk b)) (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) τ*-refl))) , rsW3 b

-- rsWX1 : JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle  ≈  S-blk0 b.
rs_WX1_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_WX1_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-blk b} {cp = Cidle} (CBloop-no-bfMsg {stStreaming}) SBblk-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_WX1_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_WX1_fwd_tau b st with netWX1-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsW b
... | inj₂ refl = _ , wτ τ*-refl , rsWX2 b
rs_WX1_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_WX1_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_WX1_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_WX1_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-blk b) Cidle stStreaming) (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) τ*-refl))) , rsW3 b

-- rsWX3 : JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret  ≈  S-blk0 b.
rs_WX3_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_WX3_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-blk b} {cp = Cret} (CBloop-no-bfMsg {stStreaming}) SBblk-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_WX3_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_WX3_fwd_tau b st with netWX3-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsWX3a b
... | inj₂ refl = _ , wτ τ*-refl , rsWX1 b
rs_WX3_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_WX3_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_WX3_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_WX3_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-blk b) Cret stStreaming) (τ*-step (im-cploop (ICn stStreaming) (SB-blk b)) (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) τ*-refl)))) , rsW3 b

-- rsWX2 : JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))  ≈  S-blk0 b.
rs_WX2_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_WX2_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-loop stStreaming} {cp = Chold (mBlock b)} (CBloop-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_WX2_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_WX2_fwd_tau b st with netWX2-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsWh b
... | inj₂ refl = _ , wτ τ*-refl , rsW2d b
rs_WX2_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_WX2_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_WX2_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_WX2_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stStreaming) (Chold (mBlock b)) stStreaming) (τ*-step (im-Wh-bfout b) τ*-refl)) , rsW3 b

-- rsIBblksb : JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch)  ≈  S-blk0 b.
rs_IBblksb_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch) ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_IBblksb_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-blk b} {cp = Chold mStartBatch} (ICn-no-bfMsg {stBusy}) SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_IBblksb_fwd_tau : ∀ b {W′} → JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch) ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_IBblksb_fwd_tau b st with netIBblksb-τ st
... | refl = _ , wτ τ*-refl , rsWX3 b
rs_IBblksb_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch) ═[ ev l ]═► W′ × RState W′ S′)
rs_IBblksb_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_IBblksb_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) (SB-blk b)) (Chold mStartBatch) ═[ τ ]═► W′ × RState W′ S′)
rs_IBblksb_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-IBblk-bfout b) (τ*-step (im-clloop (SB-blk b) Cret stStreaming) (τ*-step (im-cploop (ICn stStreaming) (SB-blk b)) (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) τ*-refl))))) , rsW3 b

-- rsLbBLKsb : JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch)  ≈  S-blk0 b.
rs_LbBLKsb_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch) ─[ ev l ]─► W′
               → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbBLKsb_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-blk b} {cp = Chold mStartBatch} (CBloop-no-bfMsg {stBusy}) SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbBLKsb_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch) ─[ τ ]─► W′
               → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbBLKsb_fwd_tau b st with netLbBLKsb-τ st
... | refl = _ , wτ τ*-refl , rsIBblksb b
rs_LbBLKsb_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch) ═[ ev l ]═► W′ × RState W′ S′)
rs_LbBLKsb_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_LbBLKsb_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
               → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) (SB-blk b)) (Chold mStartBatch) ═[ τ ]═► W′ × RState W′ S′)
rs_LbBLKsb_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-blk b) (Chold mStartBatch) stBusy) (τ*-step (im-IBblk-bfout b) (τ*-step (im-clloop (SB-blk b) Cret stStreaming) (τ*-step (im-cploop (ICn stStreaming) (SB-blk b)) (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) τ*-refl)))))) , rsW3 b

------------------------------------------------------------------------
-- Phase C2a: occ-1 head-delivery (rsW5/rsW3 ↔ S-loop (nStr1 b); the client
-- CB-blk b delivers the observable recvBFBlock b, dropping to occ-0) and occ-2
-- head-in-copy in-flight (rsW3a/rsW3d ↔ S-blk1 b b′; head b still en route).
------------------------------------------------------------------------
-- recvBFBlock delivery event label.
nRecv : Block → Event√ Rr
nRecv b = evl (record { A = ApiBFCar recvBFBlock ; e = apiBF recvBFBlock ; a = b })
-- spec: IT (nStr1 b) delivers recvBFBlock!b → S-loop nStr0 (value-restricted).
sp-nStr1-recv : ∀ b → (IT (nStr1 b) ∖ bfMsgES) ─[ ev (nRecv b) ]─► (S-loop nStr0 ∖ bfMsgES)
sp-nStr1-recv b = Hide-keep bfMsgES (IT (nStr1 b)) (λ z → z) (sVis refl (h b))
  where h : ∀ b → viewV (PTree.force (IT (nStr1 b))) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (S-loop nStr0)
        h b rewrite ≟-diagB b = refl
-- client leaf: CB-blk b delivers recvBFBlock!b → CB-loop stStreaming (value-restricted).
cl-CBblk-recv : ∀ b → CB-blk b ─[ ev (nRecv b) ]─► CB-loop stStreaming
cl-CBblk-recv b = sVis refl (h b)
  where h : ∀ b → viewV (PTree.force (CB-blk b)) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (CB-loop stStreaming)
        h b rewrite ≟-diagB b = refl
-- block-deliver sync (client bfOut) with a second block at the server: W3a → W3b.
im-W3a-bfout : ∀ b b′ → JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ τ ]─► JN (Inner (CB-blk b) (SB-blk b′)) Cret
im-W3a-bfout b b′ = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b))) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) Poly.tt
    (Par-soloL ∅ES mrg (ICn stStreaming) (SB-blk b′) (λ z → z) (cl-ICstr-bfout-blk b) refl)
    (copy-Chold-bfout (mBlock b)))
-- block-fill sync (server bfIn) with the client holding a head: W2e → W2h.
im-W2e-bfin : ∀ b b′ → JN (Inner (CB-blk b) (SB-blk b′)) Cidle ─[ τ ]─► JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′))
im-W2e-bfin b b′ = Hide-hidden ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cidle) Poly.tt
  (Par-sync ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cidle Poly.tt
    (Par-soloR ∅ES mrg (CB-blk b) (SB-blk b′) (λ z → z) (sv-SBblk-bfin b′) refl)
    (copy-Cidle-bfin (mBlock b′)))

-- rsW5 : JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle  ≈  S-loop (nStr1 b).
rs_W5_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W5_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-loop stStreaming)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-loop stStreaming} {cp = Cidle} CBblk-no-bfMsg (SBloop-no-bfMsg {stStreaming}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-loop stStreaming)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-loop stStreaming) ist
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBloop-no-ev svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-recv b) τ*-refl , rsM6
rs_W5_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W5_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W5_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W5_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W5_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W5_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W5_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W5_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W5_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W5_fwd_tau b st with netW5-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) , rsVocc1 b
rs_W5_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_W5_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W5_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_W5_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-svloop (CB-blk b) Cidle stStreaming) τ*-refl) , rsVocc1 b

-- rsW3 : JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret  ≈  S-loop (nStr1 b).
rs_W3_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-loop stStreaming)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-loop stStreaming} {cp = Cret} CBblk-no-bfMsg (SBloop-no-bfMsg {stStreaming}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-loop stStreaming)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-loop stStreaming) ist
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBloop-no-ev svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-recv b) τ*-refl , rsM3
rs_W3_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W3_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W3_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W3_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W3_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W3_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W3_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W3_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3_fwd_tau b st with netW3-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) , rsW4 b
... | inj₂ refl = _ , wτ τ*-refl , rsW5 b
rs_W3_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_W3_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W3_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stStreaming)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_W3_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-svloop (CB-blk b) Cret stStreaming) τ*-refl) , rsW4 b

-- rsW3a : JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b))  ≈  S-blk1 b b′.
rs_W3a_fwd_ev : ∀ b b′ {l W′} → JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk1 b b′ ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3a_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-blk b′} {cp = Chold (mBlock b)} (ICn-no-bfMsg {stStreaming}) SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-blk b′) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_W3a_fwd_tau : ∀ b b′ {W′} → JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk1 b b′ ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3a_fwd_tau b b′ st with netW3a-τ st
... | refl = _ , wτ (τ*-step (sp-Sblk1-τ b b′) (τ*-step (sp-Sloop-τ (nStr2 b b′)) τ*-refl)) , rsW3b b b′
rs_W3a_bwd_ev : ∀ b b′ {l S′} → (S-blk1 b b′ ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W3a_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-blk1 b b′) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_W3a_bwd_tau : ∀ b b′ {S′} → (S-blk1 b b′ ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_W3a_bwd_tau b b′ st with S-blk1-τ st
... | refl = _ , wτ (τ*-step (im-W3a-bfout b b′) (τ*-step (im-cploop (CB-blk b) (SB-blk b′)) (τ*-step (im-W2e-bfin b b′) τ*-refl))) , rsW2h b b′

-- rsW3d : JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b))  ≈  S-blk1 b b′.
rs_W3d_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk1 b b′ ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3d_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-blk b′} {cp = Chold (mBlock b)} (CBloop-no-bfMsg {stStreaming}) SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-blk b′) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_W3d_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk1 b b′ ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3d_fwd_tau b b′ st with netW3d-τ st
... | refl = _ , wτ τ*-refl , rsW3a b b′
rs_W3d_bwd_ev : ∀ b b′ {l S′} → (S-blk1 b b′ ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W3d_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-blk1 b b′) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_W3d_bwd_tau : ∀ b b′ {S′} → (S-blk1 b b′ ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_W3d_bwd_tau b b′ st with S-blk1-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-blk b′) (Chold (mBlock b)) stStreaming) (τ*-step (im-W3a-bfout b b′) (τ*-step (im-cploop (CB-blk b) (SB-blk b′)) (τ*-step (im-W2e-bfin b b′) τ*-refl)))) , rsW2h b b′

------------------------------------------------------------------------
-- Phase C-dup batch 1: rsW4′ (GFP-closure duplicate of rsW4, τ-adjacent
-- witness S-loop (nStr1 b)) and the server-settled S-blk0 b configs rsW2/rsW2d,
-- whose bwd_tau (spec S-blk0 b → S-loop (nStr1 b)) lands in the rsW4 config,
-- now paired via rsW4′.
------------------------------------------------------------------------
-- spec: IT (nStr1 b) fires sendBFBlock b′ → S-blk1 b b′ / sendBFBatchDone → S-bd1 b.
sp-nStr1-blk : ∀ b b′ → (IT (nStr1 b) ∖ bfMsgES) ─[ ev (nSBlk b′) ]─► (S-blk1 b b′ ∖ bfMsgES)
sp-nStr1-blk b b′ = Hide-keep bfMsgES (IT (nStr1 b)) (λ z → z) (sVis refl refl)
sp-nStr1-bdone : ∀ b → (IT (nStr1 b) ∖ bfMsgES) ─[ ev nBDone ]─► (S-bd1 b ∖ bfMsgES)
sp-nStr1-bdone b = Hide-keep bfMsgES (IT (nStr1 b)) (λ z → z) (sVis refl refl)
-- spec hidden bfMsg τ: S-bd1 b → S-loop (nStrD1 b).
sp-Sbd1-τ : ∀ b → (S-bd1 b ∖ bfMsgES) ─[ τ ]─► (S-loop (nStrD1 b) ∖ bfMsgES)
sp-Sbd1-τ b = Hide-hidden bfMsgES (S-bd1 b) {e = bfMsg} {a = mBatchDone} Poly.tt (sVis refl (h b))
  where h : ∀ b → viewV (PTree.force (S-bd1 b)) (BFMsg , bfMsg) mBatchDone ≡ just (S-loop (nStrD1 b))
        h b rewrite ≟-diagM mBatchDone = refl
-- block-deliver sync (client bfOut) with server settled: W2 → W4 config.
im-W2-bfout : ∀ b → JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ τ ]─► JN (Inner (CB-blk b) (ISn stStreaming)) Cret
im-W2-bfout b = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b))) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) Poly.tt
    (Par-soloL ∅ES mrg (ICn stStreaming) (ISn stStreaming) (λ z → z) (cl-ICstr-bfout-blk b) refl)
    (copy-Chold-bfout (mBlock b)))

-- rsW4′ : JN (Inner (CB-blk b) (ISn stStreaming)) Cret  ≈  S-loop (nStr1 b).
rs_W4p_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) (ISn stStreaming)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W4p_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (ISn stStreaming)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = ISn stStreaming} {cp = Cret} CBblk-no-bfMsg (ISn-no-bfMsg {stStreaming}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (ISn stStreaming)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (ISn stStreaming) ist
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-recv b) (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsM5
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) =
  _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-blk b bb) (τ*-step (sp-Sblk1-τ b bb) (τ*-step (sp-Sloop-τ (nStr2 b bb)) τ*-refl)) , rsW3b b bb
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) =
  _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-bdone b) (τ*-step (sp-Sbd1-τ b) (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl)) , rsBD2b b
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl _) (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) _
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) _
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) _
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) _
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) _
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) _
rs_W4p_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ()) _

rs_W4p_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) (ISn stStreaming)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W4p_fwd_tau b st with netW4-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) , rsVocc1 b
rs_W4p_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stStreaming)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_W4p_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W4p_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stStreaming)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_W4p_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-cploop (CB-blk b) (ISn stStreaming)) τ*-refl) , rsVocc1 b

-- rsW2 : JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b))  ≈  S-blk0 b.
rs_W2_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = ISn stStreaming} {cp = Chold (mBlock b)} (ICn-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) =
              _ , wev (τ*-step (sp-Sblk0-τ b) (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl)) (sp-nStr1-blk b bb) τ*-refl , rsW3a b bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) =
              _ , wev (τ*-step (sp-Sblk0-τ b) (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl)) (sp-nStr1-bdone b) τ*-refl , rsBD2a b
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2_fwd_tau b st with netW2-τ st
... | refl = _ , wτ (τ*-step (sp-Sblk0-τ b) (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl)) , rsW4 b
rs_W2_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W2_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_W2_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_W2_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-W2-bfout b) τ*-refl) , rsW4′ b

-- rsW2d : JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b))  ≈  S-blk0 b.
rs_W2d_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2d_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = ISn stStreaming} {cp = Chold (mBlock b)} (CBloop-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) =
              _ , wev (τ*-step (sp-Sblk0-τ b) (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl)) (sp-nStr1-blk b bb) τ*-refl , rsW3d b bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) =
              _ , wev (τ*-step (sp-Sblk0-τ b) (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl)) (sp-nStr1-bdone b) τ*-refl , rsBD2d b
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2d_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-blk0 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2d_fwd_tau b st with netW2d-τ st
... | refl = _ , wτ τ*-refl , rsW2 b
rs_W2d_bwd_ev : ∀ b {l S′} → (S-blk0 b ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W2d_bwd_ev b st with Hide-ev-elim bfMsgES (S-blk0 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_W2d_bwd_tau : ∀ b {S′} → (S-blk0 b ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_W2d_bwd_tau b st with S-blk0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stStreaming) (Chold (mBlock b)) stStreaming) (τ*-step (im-W2-bfout b) τ*-refl)) , rsW4′ b

------------------------------------------------------------------------
-- Phase C-dup batch 2: rsM9′/rsM5′ (GFP-closure duplicates of rsM9/rsM5,
-- τ-adjacent witness S-loop nStr0; reached when the head is delivered from
-- IT (nStr1 b) → S-loop nStr0 in the occ-1 configs rsVocc1/rsW4).
------------------------------------------------------------------------
-- rsM9′ : JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle  ≈  S-loop nStr0.
rs_M9p_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M9p_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = ISn stStreaming} {cp = Cidle} (CBloop-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) = _ , wev (τ*-step (sp-Sloop-τ nStr0) τ*-refl) (sp-nStr0-blk bb) τ*-refl , rsWX1 bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-step (sp-Sloop-τ nStr0) τ*-refl) sp-nStr0-bdone τ*-refl , rsBX1
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_M9p_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M9p_fwd_tau st with netM9-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsV0
rs_M9p_bwd_ev : ∀ {l S′} → (S-loop nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_M9p_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStr0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_M9p_bwd_tau : ∀ {S′} → (S-loop nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_M9p_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stStreaming) Cidle stStreaming) τ*-refl) , rsV0

-- rsM5′ : JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret  ≈  S-loop nStr0.
rs_M5p_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_M5p_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = ISn stStreaming} {cp = Cret} (CBloop-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) = _ , wev (τ*-step (sp-Sloop-τ nStr0) τ*-refl) (sp-nStr0-blk bb) τ*-refl , rsWX3 bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-step (sp-Sloop-τ nStr0) τ*-refl) sp-nStr0-bdone τ*-refl , rsBX3
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_M5p_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStr0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_M5p_fwd_tau st with netM5-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsM7
... | inj₂ refl = _ , wτ (τ*-step (sp-Sloop-τ nStr0) τ*-refl) , rsM9
rs_M5p_bwd_ev : ∀ {l S′} → (S-loop nStr0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_M5p_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStr0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_M5p_bwd_tau : ∀ {S′} → (S-loop nStr0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_M5p_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stStreaming) Cret stStreaming) τ*-refl) , rsM7

------------------------------------------------------------------------
-- Phase D-dup batch 1: drain→idle junction duplicates rsN3D0/N5D0/N6D0/N9D0
-- (idle client-looping configs paired with the drain state IT nStrD0; the
-- batch-done-empty drain reaches them while the spec is still at IT nStrD0).
------------------------------------------------------------------------
-- spec: IT nStrD0 is an iter loop-back transient; its single τ lands IT nIdle.
sp-strD0-τ : (IT nStrD0 ∖ bfMsgES) ─[ τ ]─► (IT nIdle ∖ bfMsgES)
sp-strD0-τ = Hide-τ bfMsgES (IT nStrD0) (sSil refl)

-- rsN3D0 : JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret  ≈  IT nStrD0.
rs_N3D0_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N3D0_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = SB-loop stIdle} {cp = Cret} (CBloop-no-bfMsg {stIdle}) (SBloop-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N3D0_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N3D0_fwd_tau st with netN3-τ st
... | inj₁ refl = _ , wτ (τ*-step sp-strD0-τ τ*-refl) , rsN4
... | inj₂ (inj₁ refl) = _ , wτ τ*-refl , rsN5D0
... | inj₂ (inj₂ refl) = _ , wτ τ*-refl , rsN6D0
rs_N3D0_bwd_ev : ∀ {l S′} → (IT nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_N3D0_bwd_ev st with Hide-ev-elim bfMsgES (IT nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N3D0_bwd_tau : ∀ {S′} → (IT nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_N3D0_bwd_tau st with S-strD0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) Cret stIdle) τ*-refl) , rsN4

-- rsN5D0 : JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret  ≈  IT nStrD0.
rs_N5D0_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N5D0_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = ISn stIdle} {cp = Cret} (CBloop-no-bfMsg {stIdle}) (ISn-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N5D0_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N5D0_fwd_tau st with netN5-τ st
... | inj₁ refl = _ , wτ (τ*-step sp-strD0-τ τ*-refl) , rsN7
... | inj₂ refl = _ , wτ τ*-refl , rsN9D0
rs_N5D0_bwd_ev : ∀ {l S′} → (IT nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_N5D0_bwd_ev st with Hide-ev-elim bfMsgES (IT nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N5D0_bwd_tau : ∀ {S′} → (IT nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_N5D0_bwd_tau st with S-strD0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stIdle) Cret stIdle) τ*-refl) , rsN7

-- rsN6D0 : JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle  ≈  IT nStrD0.
rs_N6D0_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N6D0_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = SB-loop stIdle} {cp = Cidle} (CBloop-no-bfMsg {stIdle}) (SBloop-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N6D0_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N6D0_fwd_tau st with netN6-τ st
... | inj₁ refl = _ , wτ (τ*-step sp-strD0-τ τ*-refl) , rsN8
... | inj₂ refl = _ , wτ τ*-refl , rsN9D0
rs_N6D0_bwd_ev : ∀ {l S′} → (IT nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_N6D0_bwd_ev st with Hide-ev-elim bfMsgES (IT nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N6D0_bwd_tau : ∀ {S′} → (IT nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_N6D0_bwd_tau st with S-strD0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) Cidle stIdle) τ*-refl) , rsN8

-- rsN9D0 : JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle  ≈  IT nStrD0.
rs_N9D0_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N9D0_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = ISn stIdle} {cp = Cidle} (CBloop-no-bfMsg {stIdle}) (ISn-no-bfMsg {stIdle}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N9D0_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((IT nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N9D0_fwd_tau st with netN9-τ st
... | refl = _ , wτ (τ*-step sp-strD0-τ τ*-refl) , rsIdle
rs_N9D0_bwd_ev : ∀ {l S′} → (IT nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_N9D0_bwd_ev st with Hide-ev-elim bfMsgES (IT nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N9D0_bwd_tau : ∀ {S′} → (IT nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_N9D0_bwd_tau st with S-strD0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stIdle) Cidle stIdle) τ*-refl) , rsIdle

-- rsN3D0s : JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret  ≈  S-loop nStrD0.
rs_N3D0s_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N3D0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = SB-loop stIdle} {cp = Cret} (CBloop-no-bfMsg {stIdle}) (SBloop-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N3D0s_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N3D0s_fwd_tau st with netN3-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nStrD0) (τ*-step sp-strD0-τ τ*-refl)) , rsN4
... | inj₂ (inj₁ refl) = _ , wτ (τ*-step (sp-Sloop-τ nStrD0) τ*-refl) , rsN5D0
... | inj₂ (inj₂ refl) = _ , wτ (τ*-step (sp-Sloop-τ nStrD0) τ*-refl) , rsN6D0
rs_N3D0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_N3D0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N3D0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_N3D0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ τ*-refl , rsN3D0

-- rsN5D0s : JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret  ≈  S-loop nStrD0.
rs_N5D0s_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ─[ ev l ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_N5D0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stIdle} {sv = ISn stIdle} {cp = Cret} (CBloop-no-bfMsg {stIdle}) (ISn-no-bfMsg {stIdle}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stIdle) (ISn stIdle)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stIdle) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_N5D0s_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ─[ τ ]─► W′
            → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_N5D0s_fwd_tau st with netN5-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Sloop-τ nStrD0) (τ*-step sp-strD0-τ τ*-refl)) , rsN7
... | inj₂ refl = _ , wτ (τ*-step (sp-Sloop-τ nStrD0) τ*-refl) , rsN9D0
rs_N5D0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_N5D0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_N5D0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
            → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_N5D0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ τ*-refl , rsN5D0

------------------------------------------------------------------------
-- Phase D batch 2: batch-done EMPTY buffer (rsBD0e/BD0h/BD0a ↔ S-bd0); the
-- server's mBatchDone routes through the copy and the client consumes it,
-- returning to idle (drains into the rsN3D0s/N5D0s ↔ S-loop nStrD0 layer).
------------------------------------------------------------------------
-- spec hidden bfMsg τ: S-bd0 → S-loop nStrD0.
sp-Sbd0-τ : (S-bd0 ∖ bfMsgES) ─[ τ ]─► (S-loop nStrD0 ∖ bfMsgES)
sp-Sbd0-τ = Hide-hidden bfMsgES S-bd0 {e = bfMsg} {a = mBatchDone} Poly.tt (sVis refl h)
  where h : viewV (PTree.force S-bd0) (BFMsg , bfMsg) mBatchDone ≡ just (S-loop nStrD0)
        h rewrite ≟-diagM mBatchDone = refl
-- server leaf: SB-bdone sends bfIn!mBatchDone → SB-loop stIdle.
sv-SBbdone-bfin : SB-bdone ─[ ev (evl (record { A = BFMsg ; e = bfIn ; a = mBatchDone })) ]─► SB-loop stIdle
sv-SBbdone-bfin = sVis refl h
  where h : viewV (PTree.force SB-bdone) (BFMsg , bfIn) mBatchDone ≡ just (SB-loop stIdle)
        h rewrite ≟-diagM mBatchDone = refl
-- client leaf: ICn stStreaming receives bfOut!mBatchDone → CB-loop stIdle.
cl-ICstr-bfout-bdone : ICn stStreaming ─[ ev (evl (record { A = BFMsg ; e = bfOut ; a = mBatchDone })) ]─► CB-loop stIdle
cl-ICstr-bfout-bdone = sVis refl refl
-- batch-done fill sync (server bfIn): BD0e → BD0h.
im-bd0e-bfin : JN (Inner (ICn stStreaming) SB-bdone) Cidle ─[ τ ]─► JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone)
im-bd0e-bfin = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cidle) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cidle Poly.tt
    (Par-soloR ∅ES mrg (ICn stStreaming) SB-bdone (λ z → z) sv-SBbdone-bfin refl)
    (copy-Cidle-bfin mBatchDone))
-- batch-done deliver sync (client bfOut), server looping: BD0h → N3.
im-bd0h-bfout : JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► JN (Inner (CB-loop stIdle) (SB-loop stIdle)) Cret
im-bd0h-bfout = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) Poly.tt
    (Par-soloL ∅ES mrg (ICn stStreaming) (SB-loop stIdle) (λ z → z) cl-ICstr-bfout-bdone refl)
    (copy-Chold-bfout mBatchDone))
-- batch-done deliver sync (client bfOut), server settled idle: BD0a → N5.
im-bd0a-bfout : JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► JN (Inner (CB-loop stIdle) (ISn stIdle)) Cret
im-bd0a-bfout = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone)) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) Poly.tt
    (Par-soloL ∅ES mrg (ICn stStreaming) (ISn stIdle) (λ z → z) cl-ICstr-bfout-bdone refl)
    (copy-Chold-bfout mBatchDone))

-- rsBD0e : JN (Inner (ICn stStreaming) SB-bdone) Cidle  ≈  S-bd0.
rs_BD0e_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) SB-bdone) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD0e_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-bdone} {cp = Cidle} (ICn-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BD0e_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) SB-bdone) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD0e_fwd_tau st with netBD0e-τ st
... | refl = _ , wτ τ*-refl , rsBD0h
rs_BD0e_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_BD0e_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD0e_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_BD0e_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl)) , rsN3D0s

-- rsBD0h : JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone)  ≈  S-bd0.
rs_BD0h_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD0h_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-loop stIdle} {cp = Chold mBatchDone} (ICn-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BD0h_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD0h_fwd_tau st with netBD0h-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsBD0a
... | inj₂ refl = _ , wτ (τ*-step sp-Sbd0-τ τ*-refl) , rsN3D0s
rs_BD0h_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD0h_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD0h_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BD0h_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step im-bd0h-bfout τ*-refl) , rsN3D0s

-- rsBD0a : JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone)  ≈  S-bd0.
rs_BD0a_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD0a_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = ISn stIdle} {cp = Chold mBatchDone} (ICn-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BD0a_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD0a_fwd_tau st with netBD0a-τ st
... | refl = _ , wτ (τ*-step sp-Sbd0-τ τ*-refl) , rsN5D0s
rs_BD0a_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD0a_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD0a_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BD0a_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step im-bd0a-bfout τ*-refl) , rsN5D0s

------------------------------------------------------------------------
-- Phase D batch 3: remaining S-bd0 configs (client/server looping variants
-- and the startBatch-cascade entries rsIBbdsb/LbBDsb).  All ↔ S-bd0; drain to
-- the rsN3D0s/N5D0s ↔ S-loop nStrD0 layer via the batch-done syncs above.
------------------------------------------------------------------------
-- startBatch-deliver sync (client bfOut) with server send-holding batchDone: IBbdsb → BX3.
im-IBbd-bfout : JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch) ─[ τ ]─► JN (Inner (CB-loop stStreaming) SB-bdone) Cret
im-IBbd-bfout = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch)) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch) Poly.tt
    (Par-soloL ∅ES mrg (ICn stBusy) SB-bdone (λ z → z) cl-ICbusy-bfout-sbatch refl)
    (copy-Chold-bfout mStartBatch))

-- rsBX1 : JN (Inner (CB-loop stStreaming) SB-bdone) Cidle  ≈  S-bd0.
rs_BX1_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BX1_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-bdone} {cp = Cidle} (CBloop-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BX1_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BX1_fwd_tau st with netBX1-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsBD0e
... | inj₂ refl = _ , wτ τ*-refl , rsBX2
rs_BX1_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_BX1_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BX1_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_BX1_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-bdone Cidle stStreaming) (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl))) , rsN3D0s

-- rsBX2 : JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone)  ≈  S-bd0.
rs_BX2_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BX2_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-loop stIdle} {cp = Chold mBatchDone} (CBloop-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BX2_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BX2_fwd_tau st with netBX2-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsBD0h
... | inj₂ refl = _ , wτ τ*-refl , rsBD1d
rs_BX2_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BX2_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BX2_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BX2_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) (Chold mBatchDone) stStreaming) (τ*-step im-bd0h-bfout τ*-refl)) , rsN3D0s

-- rsBX3 : JN (Inner (CB-loop stStreaming) SB-bdone) Cret  ≈  S-bd0.
rs_BX3_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) SB-bdone) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BX3_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-bdone} {cp = Cret} (CBloop-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BX3_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) SB-bdone) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BX3_fwd_tau st with netBX3-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsBX3a
... | inj₂ refl = _ , wτ τ*-refl , rsBX1
rs_BX3_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_BX3_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BX3_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_BX3_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step (im-cploop (CB-loop stStreaming) SB-bdone) (τ*-step (im-clloop SB-bdone Cidle stStreaming) (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl)))) , rsN3D0s

-- rsBX3a : JN (Inner (ICn stStreaming) SB-bdone) Cret  ≈  S-bd0.
rs_BX3a_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) SB-bdone) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BX3a_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-bdone} {cp = Cret} (ICn-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BX3a_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) SB-bdone) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BX3a_fwd_tau st with netBX3a-τ st
... | refl = _ , wτ τ*-refl , rsBD0e
rs_BX3a_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_BX3a_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BX3a_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_BX3a_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step (im-cploop (ICn stStreaming) SB-bdone) (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl))) , rsN3D0s

-- rsBD1d : JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone)  ≈  S-bd0.
rs_BD1d_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD1d_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = ISn stIdle} {cp = Chold mBatchDone} (CBloop-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BD1d_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD1d_fwd_tau st with netBD1d-τ st
... | refl = _ , wτ τ*-refl , rsBD0a
rs_BD1d_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD1d_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD1d_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BD1d_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stIdle) (Chold mBatchDone) stStreaming) (τ*-step im-bd0a-bfout τ*-refl)) , rsN5D0s

-- rsIBbdsb : JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch)  ≈  S-bd0.
rs_IBbdsb_fwd_ev : ∀ {l W′} → JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_IBbdsb_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stBusy} {sv = SB-bdone} {cp = Chold mStartBatch} (ICn-no-bfMsg {stBusy}) SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stBusy) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (ICbusy-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICbusy-no-api clst)
rs_IBbdsb_fwd_tau : ∀ {W′} → JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_IBbdsb_fwd_tau st with netIBbdsb-τ st
... | refl = _ , wτ τ*-refl , rsBX3
rs_IBbdsb_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch) ═[ ev l ]═► W′ × RState W′ S′)
rs_IBbdsb_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_IBbdsb_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stBusy) SB-bdone) (Chold mStartBatch) ═[ τ ]═► W′ × RState W′ S′)
rs_IBbdsb_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step im-IBbd-bfout (τ*-step (im-cploop (CB-loop stStreaming) SB-bdone) (τ*-step (im-clloop SB-bdone Cidle stStreaming) (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl))))) , rsN3D0s

-- rsLbBDsb : JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch)  ≈  S-bd0.
rs_LbBDsb_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_LbBDsb_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stBusy} {sv = SB-bdone} {cp = Chold mStartBatch} (CBloop-no-bfMsg {stBusy}) SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stBusy) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_LbBDsb_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_LbBDsb_fwd_tau st with netLbBDsb-τ st
... | refl = _ , wτ τ*-refl , rsIBbdsb
rs_LbBDsb_bwd_ev : ∀ {l S′} → (S-bd0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch) ═[ ev l ]═► W′ × RState W′ S′)
rs_LbBDsb_bwd_ev st with Hide-ev-elim bfMsgES S-bd0 st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_LbBDsb_bwd_tau : ∀ {S′} → (S-bd0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stBusy) SB-bdone) (Chold mStartBatch) ═[ τ ]═► W′ × RState W′ S′)
rs_LbBDsb_bwd_tau st with S-bd0-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-bdone (Chold mStartBatch) stBusy) (τ*-step im-IBbd-bfout (τ*-step (im-cploop (CB-loop stStreaming) SB-bdone) (τ*-step (im-clloop SB-bdone Cidle stStreaming) (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl)))))) , rsN3D0s

------------------------------------------------------------------------
-- Phase D batch 4: occ-1/occ-2 batch-done drain infrastructure.
------------------------------------------------------------------------
-- polymorphic client-solo recvBFBlock delivery (client LEFT of Inner), any (sv,cp) frame.
im-cl-recv : ∀ sv cp b → viewV (PTree.force sv) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ nothing
           → viewV (PTree.force cp) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ nothing
           → JN (Inner (CB-blk b) sv) cp ─[ ev (nRecv b) ]─► JN (Inner (CB-loop stStreaming) sv) cp
im-cl-recv sv cp b pv qv = Hide-keep ioBF (Par ioBF mrg2 (Inner (CB-blk b) sv) cp) (λ z → z)
  (Par-soloL ioBF mrg2 (Inner (CB-blk b) sv) cp (λ z → z)
    (Par-soloL ∅ES mrg (CB-blk b) sv (λ z → z) (cl-CBblk-recv b) pv) qv)
-- block-deliver sync (client bfOut) with server send-holding batchDone: BD2a → BD2b.
im-bd2a-bfout : ∀ b → JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ─[ τ ]─► JN (Inner (CB-blk b) SB-bdone) Cret
im-bd2a-bfout b = Hide-hidden ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b))) Poly.tt
  (Par-sync ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) Poly.tt
    (Par-soloL ∅ES mrg (ICn stStreaming) SB-bdone (λ z → z) (cl-ICstr-bfout-blk b) refl)
    (copy-Chold-bfout (mBlock b)))
-- spec: IT (nStrD1 b) delivers recvBFBlock!b → S-loop nStrD0 (value-restricted).
sp-nStrD1-recv : ∀ b → (IT (nStrD1 b) ∖ bfMsgES) ─[ ev (nRecv b) ]─► (S-loop nStrD0 ∖ bfMsgES)
sp-nStrD1-recv b = Hide-keep bfMsgES (IT (nStrD1 b)) (λ z → z) (sVis refl (h b))
  where h : ∀ b → viewV (PTree.force (IT (nStrD1 b))) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (S-loop nStrD0)
        h b rewrite ≟-diagB b = refl
-- spec: IT (nStrD2 b b′) delivers recvBFBlock!b → S-loop (nStrD1 b′) (value-restricted).
sp-nStrD2-recv : ∀ b b′ → (IT (nStrD2 b b′) ∖ bfMsgES) ─[ ev (nRecv b) ]─► (S-loop (nStrD1 b′) ∖ bfMsgES)
sp-nStrD2-recv b b′ = Hide-keep bfMsgES (IT (nStrD2 b b′)) (λ z → z) (sVis refl (h b b′))
  where h : ∀ b b′ → viewV (PTree.force (IT (nStrD2 b b′))) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (S-loop (nStrD1 b′))
        h b b′ rewrite ≟-diagB b = refl

-- rsBD0eD0s : (ICn stStreaming, SB-bdone, Cidle)  ≈  S-loop nStrD0.
rs_BD0eD0s_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) SB-bdone) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD0eD0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-bdone} {cp = Cidle} (ICn-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BD0eD0s_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) SB-bdone) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD0eD0s_fwd_tau st with netBD0e-τ st
... | refl = _ , wτ τ*-refl , rsBD0hD0s
rs_BD0eD0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_BD0eD0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD0eD0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_BD0eD0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl)) , rsN3D0

-- rsBD0hD0s : (ICn stStreaming, SB-loop stIdle, Chold mBatchDone)  ≈  S-loop nStrD0.
rs_BD0hD0s_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD0hD0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-loop stIdle} {cp = Chold mBatchDone} (ICn-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BD0hD0s_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD0hD0s_fwd_tau st with netBD0h-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsBD0aD0s
... | inj₂ refl = _ , wτ τ*-refl , rsN3D0s
rs_BD0hD0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD0hD0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD0hD0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BD0hD0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step im-bd0h-bfout τ*-refl) , rsN3D0

-- rsBD0aD0s : (ICn stStreaming, ISn stIdle, Chold mBatchDone)  ≈  S-loop nStrD0.
rs_BD0aD0s_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD0aD0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = ISn stIdle} {cp = Chold mBatchDone} (ICn-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BD0aD0s_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD0aD0s_fwd_tau st with netBD0a-τ st
... | refl = _ , wτ τ*-refl , rsN5D0s
rs_BD0aD0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD0aD0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD0aD0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BD0aD0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step im-bd0a-bfout τ*-refl) , rsN5D0

-- rsBD1dD0s : (CB-loop stStreaming, ISn stIdle, Chold mBatchDone)  ≈  S-loop nStrD0.
rs_BD1dD0s_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD1dD0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = ISn stIdle} {cp = Chold mBatchDone} (CBloop-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (ISn stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BD1dD0s_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD1dD0s_fwd_tau st with netBD1d-τ st
... | refl = _ , wτ τ*-refl , rsBD0aD0s
rs_BD1dD0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD1dD0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD1dD0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BD1dD0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stIdle) (Chold mBatchDone) stStreaming) (τ*-step im-bd0a-bfout τ*-refl)) , rsN5D0

-- rsBX1D0s : (CB-loop stStreaming, SB-bdone, Cidle)  ≈  S-loop nStrD0.
rs_BX1D0s_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BX1D0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-bdone} {cp = Cidle} (CBloop-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BX1D0s_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BX1D0s_fwd_tau st with netBX1-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsBD0eD0s
... | inj₂ refl = _ , wτ τ*-refl , rsBX2D0s
rs_BX1D0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_BX1D0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BX1D0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_BX1D0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-bdone Cidle stStreaming) (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl))) , rsN3D0

-- rsBX2D0s : (CB-loop stStreaming, SB-loop stIdle, Chold mBatchDone)  ≈  S-loop nStrD0.
rs_BX2D0s_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BX2D0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-loop stIdle} {cp = Chold mBatchDone} (CBloop-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-loop stIdle) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BX2D0s_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BX2D0s_fwd_tau st with netBX2-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsBD0hD0s
... | inj₂ refl = _ , wτ τ*-refl , rsBD1dD0s
rs_BX2D0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BX2D0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BX2D0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BX2D0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stIdle) (Chold mBatchDone) stStreaming) (τ*-step im-bd0h-bfout τ*-refl)) , rsN3D0

-- rsBX3D0s : (CB-loop stStreaming, SB-bdone, Cret)  ≈  S-loop nStrD0.
rs_BX3D0s_fwd_ev : ∀ {l W′} → JN (Inner (CB-loop stStreaming) SB-bdone) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BX3D0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-bdone} {cp = Cret} (CBloop-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BX3D0s_fwd_tau : ∀ {W′} → JN (Inner (CB-loop stStreaming) SB-bdone) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BX3D0s_fwd_tau st with netBX3-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsBX3aD0s
... | inj₂ refl = _ , wτ τ*-refl , rsBX1D0s
rs_BX3D0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_BX3D0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BX3D0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_BX3D0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-cploop (CB-loop stStreaming) SB-bdone) (τ*-step (im-clloop SB-bdone Cidle stStreaming) (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl)))) , rsN3D0

-- rsBX3aD0s : (ICn stStreaming, SB-bdone, Cret)  ≈  S-loop nStrD0.
rs_BX3aD0s_fwd_ev : ∀ {l W′} → JN (Inner (ICn stStreaming) SB-bdone) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BX3aD0s_fwd_ev st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-bdone} {cp = Cret} (ICn-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BX3aD0s_fwd_tau : ∀ {W′} → JN (Inner (ICn stStreaming) SB-bdone) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop nStrD0 ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BX3aD0s_fwd_tau st with netBX3a-τ st
... | refl = _ , wτ τ*-refl , rsBD0eD0s
rs_BX3aD0s_bwd_ev : ∀ {l S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_BX3aD0s_bwd_ev st with Hide-ev-elim bfMsgES (S-loop nStrD0) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BX3aD0s_bwd_tau : ∀ {S′} → (S-loop nStrD0 ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_BX3aD0s_bwd_tau st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-cploop (ICn stStreaming) SB-bdone) (τ*-step im-bd0e-bfin (τ*-step im-bd0h-bfout τ*-refl))) , rsN3D0

------------------------------------------------------------------------
-- Phase D batch 5: occ-1 batch-done head-at-client configs (rsBD1a/BD1e/BD1h/BD2b
-- ↔ IT (nStrD1 b)); the client CB-blk b delivers recvBFBlock b → S-loop nStrD0,
-- landing the S-loop nStrD0 twins built above.
------------------------------------------------------------------------
-- rsBD1a : JN (Inner (CB-blk b) (ISn stIdle)) (Chold mBatchDone)  ≈  IT (nStrD1 b).
rs_BD1a_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) (ISn stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD1a_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (ISn stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = ISn stIdle} {cp = Chold mBatchDone} CBblk-no-bfMsg (ISn-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (ISn stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (ISn stIdle) ist
...     | evR ¬m3 svst = ⊥-elim (ISidle-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ISidle-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStrD1-recv b) τ*-refl , rsBD1dD0s
rs_BD1a_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD1a_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD1a_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD1a_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD1a_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD1a_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD1a_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD1a_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD1a_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) (ISn stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD1a_fwd_tau b st = ⊥-elim (netBD1a-noτ st)
rs_BD1a_bwd_ev : ∀ b {l S′} → (IT (nStrD1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD1a_bwd_ev b st with Hide-ev-elim bfMsgES (IT (nStrD1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (ISn stIdle) (Chold mBatchDone) b refl refl) τ*-refl , rsBD1dD0s
rs_BD1a_bwd_ev b st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_BD1a_bwd_ev b st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD1a_bwd_ev b st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD1a_bwd_ev b st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD1a_bwd_ev b st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD1a_bwd_ev b st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD1a_bwd_ev b st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD1a_bwd_ev b st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD1a_bwd_ev b st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_BD1a_bwd_ev b st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_BD1a_bwd_ev b st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_BD1a_bwd_ev b st | he√ ()
rs_BD1a_bwd_tau : ∀ b {S′} → (IT (nStrD1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BD1a_bwd_tau b st = ⊥-elim (spec-noτ sStrD1 st)

-- rsBD1e : JN (Inner (CB-blk b) SB-bdone) Cidle  ≈  IT (nStrD1 b).
rs_BD1e_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) SB-bdone) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD1e_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Cidle} CBblk-no-bfMsg SBbdone-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStrD1-recv b) τ*-refl , rsBX1D0s
rs_BD1e_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD1e_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD1e_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD1e_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD1e_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD1e_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD1e_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD1e_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD1e_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) SB-bdone) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD1e_fwd_tau b st with netBD1e-τ st
... | refl = _ , wτ τ*-refl , rsBD1h b
rs_BD1e_bwd_ev : ∀ b {l S′} → (IT (nStrD1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_BD1e_bwd_ev b st with Hide-ev-elim bfMsgES (IT (nStrD1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv SB-bdone Cidle b refl refl) τ*-refl , rsBX1D0s
rs_BD1e_bwd_ev b st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_BD1e_bwd_ev b st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD1e_bwd_ev b st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD1e_bwd_ev b st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD1e_bwd_ev b st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD1e_bwd_ev b st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD1e_bwd_ev b st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD1e_bwd_ev b st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD1e_bwd_ev b st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_BD1e_bwd_ev b st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_BD1e_bwd_ev b st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_BD1e_bwd_ev b st | he√ ()
rs_BD1e_bwd_tau : ∀ b {S′} → (IT (nStrD1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_BD1e_bwd_tau b st = ⊥-elim (spec-noτ sStrD1 st)

-- rsBD1h : JN (Inner (CB-blk b) (SB-loop stIdle)) (Chold mBatchDone)  ≈  IT (nStrD1 b).
rs_BD1h_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) (SB-loop stIdle)) (Chold mBatchDone) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD1h_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-loop stIdle)) (Chold mBatchDone)) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-loop stIdle} {cp = Chold mBatchDone} CBblk-no-bfMsg (SBloop-no-bfMsg {stIdle}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-loop stIdle)) (Chold mBatchDone) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-loop stIdle) ist
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBloop-no-ev svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStrD1-recv b) τ*-refl , rsBX2D0s
rs_BD1h_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD1h_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD1h_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD1h_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD1h_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD1h_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD1h_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD1h_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD1h_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) (SB-loop stIdle)) (Chold mBatchDone) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD1h_fwd_tau b st with netBD1h-τ st
... | refl = _ , wτ τ*-refl , rsBD1a b
rs_BD1h_bwd_ev : ∀ b {l S′} → (IT (nStrD1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stIdle)) (Chold mBatchDone) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD1h_bwd_ev b st with Hide-ev-elim bfMsgES (IT (nStrD1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (SB-loop stIdle) (Chold mBatchDone) b refl refl) τ*-refl , rsBX2D0s
rs_BD1h_bwd_ev b st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_BD1h_bwd_ev b st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD1h_bwd_ev b st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD1h_bwd_ev b st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD1h_bwd_ev b st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD1h_bwd_ev b st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD1h_bwd_ev b st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD1h_bwd_ev b st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD1h_bwd_ev b st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_BD1h_bwd_ev b st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_BD1h_bwd_ev b st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_BD1h_bwd_ev b st | he√ ()
rs_BD1h_bwd_tau : ∀ b {S′} → (IT (nStrD1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stIdle)) (Chold mBatchDone) ═[ τ ]═► W′ × RState W′ S′)
rs_BD1h_bwd_tau b st = ⊥-elim (spec-noτ sStrD1 st)

-- rsBD2b : JN (Inner (CB-blk b) SB-bdone) Cret  ≈  IT (nStrD1 b).
rs_BD2b_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) SB-bdone) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2b_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Cret} CBblk-no-bfMsg SBbdone-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStrD1-recv b) τ*-refl , rsBX3D0s
rs_BD2b_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD2b_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD2b_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD2b_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD2b_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD2b_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD2b_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD2b_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD2b_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) SB-bdone) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2b_fwd_tau b st with netBD2b-τ st
... | refl = _ , wτ τ*-refl , rsBD1e b
rs_BD2b_bwd_ev : ∀ b {l S′} → (IT (nStrD1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2b_bwd_ev b st with Hide-ev-elim bfMsgES (IT (nStrD1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv SB-bdone Cret b refl refl) τ*-refl , rsBX3D0s
rs_BD2b_bwd_ev b st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_BD2b_bwd_ev b st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD2b_bwd_ev b st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD2b_bwd_ev b st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD2b_bwd_ev b st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD2b_bwd_ev b st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD2b_bwd_ev b st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD2b_bwd_ev b st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD2b_bwd_ev b st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_BD2b_bwd_ev b st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_BD2b_bwd_ev b st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_BD2b_bwd_ev b st | he√ ()
rs_BD2b_bwd_tau : ∀ b {S′} → (IT (nStrD1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_BD2b_bwd_tau b st = ⊥-elim (spec-noτ sStrD1 st)

------------------------------------------------------------------------
-- Phase D batch 6: occ-1 batch-done block-in-copy configs (rsBD2a/BD2d ↔ S-bd1 b)
-- and their S-loop nStrD1 twins (rsBD2aD1s/BD2dD1s), reached from occ-2 delivery.
------------------------------------------------------------------------
-- rsBD2a : JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b))  ≈  S-bd1 b.
rs_BD2a_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd1 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2a_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-bdone} {cp = Chold (mBlock b)} (ICn-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BD2a_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd1 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2a_fwd_tau b st with netBD2a-τ st
... | refl = _ , wτ (τ*-step (sp-Sbd1-τ b) τ*-refl) , rsBD2bD1s b
rs_BD2a_bwd_ev : ∀ b {l S′} → (S-bd1 b ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2a_bwd_ev b st with Hide-ev-elim bfMsgES (S-bd1 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD2a_bwd_tau : ∀ b {S′} → (S-bd1 b ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_BD2a_bwd_tau b st with S-bd1-τ st
... | refl = _ , wτ (τ*-step (im-bd2a-bfout b) τ*-refl) , rsBD2bD1s b

-- rsBD2d : JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b))  ≈  S-bd1 b.
rs_BD2d_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd1 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2d_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-bdone} {cp = Chold (mBlock b)} (CBloop-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BD2d_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd1 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2d_fwd_tau b st with netBD2d-τ st
... | refl = _ , wτ τ*-refl , rsBD2a b
rs_BD2d_bwd_ev : ∀ b {l S′} → (S-bd1 b ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2d_bwd_ev b st with Hide-ev-elim bfMsgES (S-bd1 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD2d_bwd_tau : ∀ b {S′} → (S-bd1 b ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_BD2d_bwd_tau b st with S-bd1-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-bdone (Chold (mBlock b)) stStreaming) (τ*-step (im-bd2a-bfout b) τ*-refl)) , rsBD2bD1s b

-- rsBD2aD1s : JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b))  ≈  S-loop (nStrD1 b).
rs_BD2aD1s_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2aD1s_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-bdone} {cp = Chold (mBlock b)} (ICn-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_BD2aD1s_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2aD1s_fwd_tau b st with netBD2a-τ st
... | refl = _ , wτ τ*-refl , rsBD2bD1s b
rs_BD2aD1s_bwd_ev : ∀ b {l S′} → (S-loop (nStrD1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2aD1s_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStrD1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD2aD1s_bwd_tau : ∀ b {S′} → (S-loop (nStrD1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) SB-bdone) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_BD2aD1s_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-bd2a-bfout b) τ*-refl) , rsBD2b b

-- rsBD2dD1s : JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b))  ≈  S-loop (nStrD1 b).
rs_BD2dD1s_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2dD1s_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-bdone} {cp = Chold (mBlock b)} (CBloop-no-bfMsg {stStreaming}) SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) SB-bdone ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_BD2dD1s_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2dD1s_fwd_tau b st with netBD2d-τ st
... | refl = _ , wτ τ*-refl , rsBD2aD1s b
rs_BD2dD1s_bwd_ev : ∀ b {l S′} → (S-loop (nStrD1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2dD1s_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStrD1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD2dD1s_bwd_tau : ∀ b {S′} → (S-loop (nStrD1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) SB-bdone) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_BD2dD1s_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop SB-bdone (Chold (mBlock b)) stStreaming) (τ*-step (im-bd2a-bfout b) τ*-refl)) , rsBD2b b

-- rsBD2bD1s : JN (Inner (CB-blk b) SB-bdone) Cret  ≈  S-loop (nStrD1 b).
rs_BD2bD1s_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) SB-bdone) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2bD1s_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Cret} CBblk-no-bfMsg SBbdone-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl) (sp-nStrD1-recv b) τ*-refl , rsBX3D0s
rs_BD2bD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD2bD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD2bD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD2bD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD2bD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD2bD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD2bD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD2bD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD2bD1s_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) SB-bdone) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2bD1s_fwd_tau b st with netBD2b-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl) , rsBD1e b
rs_BD2bD1s_bwd_ev : ∀ b {l S′} → (S-loop (nStrD1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2bD1s_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStrD1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD2bD1s_bwd_tau : ∀ b {S′} → (S-loop (nStrD1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_BD2bD1s_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-cploop (CB-blk b) SB-bdone) τ*-refl) , rsBD1e b

-- rsBD2e : JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))  ≈  IT (nStrD2 b b′).
rs_BD2e_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2e_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Chold (mBlock b′)} CBblk-no-bfMsg SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStrD2-recv b b′) τ*-refl , rsBD2dD1s b′
rs_BD2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD2e_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStrD2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2e_fwd_tau b b′ st = ⊥-elim (netBD2e-noτ st)
rs_BD2e_bwd_ev : ∀ b b′ {l S′} → (IT (nStrD2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2e_bwd_ev b b′ st with Hide-ev-elim bfMsgES (IT (nStrD2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv SB-bdone (Chold (mBlock b′)) b refl refl) τ*-refl , rsBD2dD1s b′
rs_BD2e_bwd_ev b b′ st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_BD2e_bwd_ev b b′ st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_BD2e_bwd_ev b b′ st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_BD2e_bwd_ev b b′ st | he√ ()
rs_BD2e_bwd_tau : ∀ b b′ {S′} → (IT (nStrD2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_BD2e_bwd_tau b b′ st = ⊥-elim (spec-noτ sStrD2 st)

------------------------------------------------------------------------
-- Phase E (region C): streaming→batch-done bridge.  When streaming fires
-- sendBFBatchDone while the client still holds a deliverable head, the net
-- lands a head-at-client batchDone config paired with the spec transient
-- S-bd_k (and its S-loop nStrD_k twin).
------------------------------------------------------------------------
-- spec hidden bfMsg τ: S-bd2 b b′ → S-loop (nStrD2 b b′).
sp-Sbd2-τ : ∀ b b′ → (S-bd2 b b′ ∖ bfMsgES) ─[ τ ]─► (S-loop (nStrD2 b b′) ∖ bfMsgES)
sp-Sbd2-τ b b′ = Hide-hidden bfMsgES (S-bd2 b b′) {e = bfMsg} {a = mBatchDone} Poly.tt (sVis refl (h b b′))
  where h : ∀ b b′ → viewV (PTree.force (S-bd2 b b′)) (BFMsg , bfMsg) mBatchDone ≡ just (S-loop (nStrD2 b b′))
        h b b′ rewrite ≟-diagM mBatchDone = refl

-- rsBD1e′ : JN (Inner (CB-blk b) SB-bdone) Cidle  ≈  S-bd1 b.
rs_BD1ep_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) SB-bdone) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd1 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD1ep_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Cidle} CBblk-no-bfMsg SBbdone-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sbd1-τ b) (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl)) (sp-nStrD1-recv b) τ*-refl , rsBX1D0s
rs_BD1ep_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD1ep_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD1ep_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD1ep_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD1ep_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD1ep_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD1ep_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD1ep_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD1ep_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) SB-bdone) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd1 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD1ep_fwd_tau b st with netBD1e-τ st
... | refl = _ , wτ (τ*-step (sp-Sbd1-τ b) (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl)) , rsBD1h b
rs_BD1ep_bwd_ev : ∀ b {l S′} → (S-bd1 b ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_BD1ep_bwd_ev b st with Hide-ev-elim bfMsgES (S-bd1 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD1ep_bwd_tau : ∀ b {S′} → (S-bd1 b ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_BD1ep_bwd_tau b st with S-bd1-τ st
... | refl = _ , wτ τ*-refl , rsBD1eD1s b

-- rsBD1eD1s : JN (Inner (CB-blk b) SB-bdone) Cidle  ≈  S-loop (nStrD1 b).
rs_BD1eD1s_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) SB-bdone) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD1eD1s_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Cidle} CBblk-no-bfMsg SBbdone-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl) (sp-nStrD1-recv b) τ*-refl , rsBX1D0s
rs_BD1eD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD1eD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD1eD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD1eD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD1eD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD1eD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD1eD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD1eD1s_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD1eD1s_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) SB-bdone) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD1eD1s_fwd_tau b st with netBD1e-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl) , rsBD1h b
rs_BD1eD1s_bwd_ev : ∀ b {l S′} → (S-loop (nStrD1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_BD1eD1s_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStrD1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD1eD1s_bwd_tau : ∀ b {S′} → (S-loop (nStrD1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_BD1eD1s_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ τ*-refl , rsBD1e b

-- rsBD2b′ : JN (Inner (CB-blk b) SB-bdone) Cret  ≈  S-bd1 b.
rs_BD2bp_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) SB-bdone) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd1 b ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2bp_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Cret} CBblk-no-bfMsg SBbdone-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sbd1-τ b) (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl)) (sp-nStrD1-recv b) τ*-refl , rsBX3D0s
rs_BD2bp_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD2bp_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD2bp_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD2bp_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD2bp_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD2bp_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD2bp_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD2bp_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD2bp_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) SB-bdone) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd1 b ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2bp_fwd_tau b st with netBD2b-τ st
... | refl = _ , wτ τ*-refl , rsBD1e′ b
rs_BD2bp_bwd_ev : ∀ b {l S′} → (S-bd1 b ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2bp_bwd_ev b st with Hide-ev-elim bfMsgES (S-bd1 b) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD2bp_bwd_tau : ∀ b {S′} → (S-bd1 b ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_BD2bp_bwd_tau b st with S-bd1-τ st
... | refl = _ , wτ (τ*-step (im-cploop (CB-blk b) SB-bdone) τ*-refl) , rsBD1eD1s b

-- rsBD2e′ : JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))  ≈  S-bd2 b b′.
rs_BD2ep_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd2 b b′ ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2ep_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Chold (mBlock b′)} CBblk-no-bfMsg SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sbd2-τ b b′) (τ*-step (sp-Sloop-τ (nStrD2 b b′)) τ*-refl)) (sp-nStrD2-recv b b′) τ*-refl , rsBD2dD1s b′
rs_BD2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD2ep_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-bd2 b b′ ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2ep_fwd_tau b b′ st = ⊥-elim (netBD2e-noτ st)
rs_BD2ep_bwd_ev : ∀ b b′ {l S′} → (S-bd2 b b′ ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2ep_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-bd2 b b′) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_BD2ep_bwd_tau : ∀ b b′ {S′} → (S-bd2 b b′ ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_BD2ep_bwd_tau b b′ st with S-bd2-τ st
... | refl = _ , wτ τ*-refl , rsBD2eD2s b b′

-- rsBD2eD2s : JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))  ≈  S-loop (nStrD2 b b′).
rs_BD2eD2s_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_BD2eD2s_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-bdone} {cp = Chold (mBlock b′)} CBblk-no-bfMsg SBbdone-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) SB-bdone ist
...     | evR ¬m3 svst = ⊥-elim (SBbdone-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBbdone-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sloop-τ (nStrD2 b b′)) τ*-refl) (sp-nStrD2-recv b b′) τ*-refl , rsBD2dD1s b′
rs_BD2eD2s_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_BD2eD2s_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_BD2eD2s_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_BD2eD2s_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_BD2eD2s_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_BD2eD2s_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_BD2eD2s_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_BD2eD2s_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_BD2eD2s_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStrD2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_BD2eD2s_fwd_tau b b′ st = ⊥-elim (netBD2e-noτ st)
rs_BD2eD2s_bwd_ev : ∀ b b′ {l S′} → (S-loop (nStrD2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_BD2eD2s_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-loop (nStrD2 b b′)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_BD2eD2s_bwd_tau : ∀ b b′ {S′} → (S-loop (nStrD2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) SB-bdone) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_BD2eD2s_bwd_tau b b′ st with S-loop-τ st
... | refl = _ , wτ τ*-refl , rsBD2e b b′

------------------------------------------------------------------------
-- Phase F (region D): streaming.  occ-1 in-flight S-loop nStr1 twins
-- rsW′/rsWh′/rsWX3a′/rsWX1′/rsWX3′/rsWX2′/rsW2′/rsW2d′ (same configs as the
-- ↔ S-blk0 originals, paired with the τ-adjacent S-loop (nStr1 b)).
------------------------------------------------------------------------
-- rsW′ : JN (Inner (ICn stStreaming) (SB-blk b)) Cidle  ≈  S-loop (nStr1 b).
rs_Wp_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Wp_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-blk b} {cp = Cidle} (ICn-no-bfMsg {stStreaming}) SBblk-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_Wp_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Wp_fwd_tau b st with netW-τ st
... | refl = _ , wτ τ*-refl , rsWh′ b
rs_Wp_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Wp_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_Wp_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Wp_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) (τ*-step (im-svloop (CB-blk b) Cret stStreaming) τ*-refl))) , rsW4 b

-- rsWh′ : JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))  ≈  S-loop (nStr1 b).
rs_Whp_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Whp_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-loop stStreaming} {cp = Chold (mBlock b)} (ICn-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_Whp_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Whp_fwd_tau b st with netWh-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsW2′ b
... | inj₂ refl = _ , wτ τ*-refl , rsW3 b
rs_Whp_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_Whp_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_Whp_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_Whp_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-Wh-bfout b) (τ*-step (im-svloop (CB-blk b) Cret stStreaming) τ*-refl)) , rsW4 b

-- rsWX3a′ : JN (Inner (ICn stStreaming) (SB-blk b)) Cret  ≈  S-loop (nStr1 b).
rs_WX3ap_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) (SB-blk b)) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_WX3ap_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-blk b} {cp = Cret} (ICn-no-bfMsg {stStreaming}) SBblk-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_WX3ap_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) (SB-blk b)) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_WX3ap_fwd_tau b st with netWX3a-τ st
... | refl = _ , wτ τ*-refl , rsW′ b
rs_WX3ap_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_WX3ap_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_WX3ap_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_WX3ap_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-cploop (ICn stStreaming) (SB-blk b)) (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) (τ*-step (im-svloop (CB-blk b) Cret stStreaming) τ*-refl)))) , rsW4 b

-- rsWX1′ : JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle  ≈  S-loop (nStr1 b).
rs_WX1p_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_WX1p_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-blk b} {cp = Cidle} (CBloop-no-bfMsg {stStreaming}) SBblk-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_WX1p_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_WX1p_fwd_tau b st with netWX1-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsW′ b
... | inj₂ refl = _ , wτ τ*-refl , rsWX2′ b
rs_WX1p_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_WX1p_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_WX1p_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_WX1p_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-blk b) Cidle stStreaming) (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) (τ*-step (im-svloop (CB-blk b) Cret stStreaming) τ*-refl)))) , rsW4 b

-- rsWX3′ : JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret  ≈  S-loop (nStr1 b).
rs_WX3p_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_WX3p_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-blk b} {cp = Cret} (CBloop-no-bfMsg {stStreaming}) SBblk-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-blk b) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_WX3p_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_WX3p_fwd_tau b st with netWX3-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsWX3a′ b
... | inj₂ refl = _ , wτ τ*-refl , rsWX1′ b
rs_WX3p_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_WX3p_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_WX3p_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_WX3p_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-blk b) Cret stStreaming) (τ*-step (im-cploop (ICn stStreaming) (SB-blk b)) (τ*-step (im-Wsv-bfin b) (τ*-step (im-Wh-bfout b) (τ*-step (im-svloop (CB-blk b) Cret stStreaming) τ*-refl))))) , rsW4 b

-- rsWX2′ : JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))  ≈  S-loop (nStr1 b).
rs_WX2p_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_WX2p_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-loop stStreaming} {cp = Chold (mBlock b)} (CBloop-no-bfMsg {stStreaming}) (SBloop-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-loop stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_WX2p_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_WX2p_fwd_tau b st with netWX2-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsWh′ b
... | inj₂ refl = _ , wτ τ*-refl , rsW2d′ b
rs_WX2p_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_WX2p_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_WX2p_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-loop stStreaming)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_WX2p_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-loop stStreaming) (Chold (mBlock b)) stStreaming) (τ*-step (im-Wh-bfout b) (τ*-step (im-svloop (CB-blk b) Cret stStreaming) τ*-refl))) , rsW4 b

-- rsW2′ : JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b))  ≈  S-loop (nStr1 b).
rs_W2p_fwd_ev : ∀ b {l W′} → JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2p_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = ISn stStreaming} {cp = Chold (mBlock b)} (ICn-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) =
              _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-blk b bb) τ*-refl , rsW3a b bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) =
              _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-bdone b) τ*-refl , rsBD2a b
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2p_fwd_tau : ∀ b {W′} → JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2p_fwd_tau b st with netW2-τ st
... | refl = _ , wτ τ*-refl , rsW4′ b
rs_W2p_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W2p_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W2p_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_W2p_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-W2-bfout b) τ*-refl) , rsW4 b

-- rsW2d′ : JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b))  ≈  S-loop (nStr1 b).
rs_W2dp_fwd_ev : ∀ b {l W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2dp_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = ISn stStreaming} {cp = Chold (mBlock b)} (CBloop-no-bfMsg {stStreaming}) (ISn-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (ISn stStreaming) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) =
              _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-blk b bb) τ*-refl , rsW3d b bb
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) =
              _ , wev (τ*-step (sp-Sloop-τ (nStr1 b)) τ*-refl) (sp-nStr1-bdone b) τ*-refl , rsBD2d b
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...     | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2dp_fwd_tau : ∀ b {W′} → JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2dp_fwd_tau b st with netW2d-τ st
... | refl = _ , wτ τ*-refl , rsW2′ b
rs_W2dp_bwd_ev : ∀ b {l S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W2dp_bwd_ev b st with Hide-ev-elim bfMsgES (S-loop (nStr1 b)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W2dp_bwd_tau : ∀ b {S′} → (S-loop (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (ISn stStreaming)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_W2dp_bwd_tau b st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (ISn stStreaming) (Chold (mBlock b)) stStreaming) (τ*-step (im-W2-bfout b) τ*-refl)) , rsW4 b

------------------------------------------------------------------------
-- Phase F cont.: occ-2/occ-3 spec builders + occ-2 in-flight S-loop nStr2
-- twins (rsW3a′/rsW3d′) and the sendBFBlock S-blk-transient twins.
------------------------------------------------------------------------
-- spec: IT (nStr2 b b′) delivers recvBFBlock!b → S-loop (nStr1 b′) (value-restricted).
sp-nStr2-recv : ∀ b b′ → (IT (nStr2 b b′) ∖ bfMsgES) ─[ ev (nRecv b) ]─► (S-loop (nStr1 b′) ∖ bfMsgES)
sp-nStr2-recv b b′ = Hide-keep bfMsgES (IT (nStr2 b b′)) (λ z → z) (sVis refl (h b b′))
  where h : ∀ b b′ → viewV (PTree.force (IT (nStr2 b b′))) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (S-loop (nStr1 b′))
        h b b′ rewrite ≟-diagB b = refl
-- spec: IT (nStr2 b b′) fires sendBFBlock b″ → S-blk2 b b′ b″ / sendBFBatchDone → S-bd2 b b′.
sp-nStr2-blk : ∀ b b′ b″ → (IT (nStr2 b b′) ∖ bfMsgES) ─[ ev (nSBlk b″) ]─► (S-blk2 b b′ b″ ∖ bfMsgES)
sp-nStr2-blk b b′ b″ = Hide-keep bfMsgES (IT (nStr2 b b′)) (λ z → z) (sVis refl refl)
sp-nStr2-bdone : ∀ b b′ → (IT (nStr2 b b′) ∖ bfMsgES) ─[ ev nBDone ]─► (S-bd2 b b′ ∖ bfMsgES)
sp-nStr2-bdone b b′ = Hide-keep bfMsgES (IT (nStr2 b b′)) (λ z → z) (sVis refl refl)
-- spec: IT (nStr3 b b′ b″) delivers recvBFBlock!b → S-loop (nStr2 b′ b″) (value-restricted; saturated).
sp-nStr3-recv : ∀ b b′ b″ → (IT (nStr3 b b′ b″) ∖ bfMsgES) ─[ ev (nRecv b) ]─► (S-loop (nStr2 b′ b″) ∖ bfMsgES)
sp-nStr3-recv b b′ b″ = Hide-keep bfMsgES (IT (nStr3 b b′ b″)) (λ z → z) (sVis refl (h b b′ b″))
  where h : ∀ b b′ b″ → viewV (PTree.force (IT (nStr3 b b′ b″))) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (S-loop (nStr2 b′ b″))
        h b b′ b″ rewrite ≟-diagB b = refl
-- spec hidden bfMsg τ: S-blk2 b b′ b″ → S-loop (nStr3 b b′ b″).
sp-Sblk2-τ : ∀ b b′ b″ → (S-blk2 b b′ b″ ∖ bfMsgES) ─[ τ ]─► (S-loop (nStr3 b b′ b″) ∖ bfMsgES)
sp-Sblk2-τ b b′ b″ = Hide-hidden bfMsgES (S-blk2 b b′ b″) {e = bfMsg} {a = mBlock b″} Poly.tt (sVis refl (h b b′ b″))
  where h : ∀ b b′ b″ → viewV (PTree.force (S-blk2 b b′ b″)) (BFMsg , bfMsg) (mBlock b″) ≡ just (S-loop (nStr3 b b′ b″))
        h b b′ b″ rewrite ≟-diagM (mBlock b″) = refl

-- rsW3a′ : JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b))  ≈  S-loop (nStr2 b b′).
rs_W3ap_fwd_ev : ∀ b b′ {l W′} → JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3ap_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = ICn stStreaming} {sv = SB-blk b′} {cp = Chold (mBlock b)} (ICn-no-bfMsg {stStreaming}) SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (ICn stStreaming) (SB-blk b′) ist
...     | evL ¬m3 clst = ⊥-elim (ICstr-no-api clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (ICstr-no-api clst)
rs_W3ap_fwd_tau : ∀ b b′ {W′} → JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3ap_fwd_tau b b′ st with netW3a-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ (nStr2 b b′)) τ*-refl) , rsW3b b b′
rs_W3ap_bwd_ev : ∀ b b′ {l S′} → (S-loop (nStr2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W3ap_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-loop (nStr2 b b′)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W3ap_bwd_tau : ∀ b b′ {S′} → (S-loop (nStr2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (ICn stStreaming) (SB-blk b′)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_W3ap_bwd_tau b b′ st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-W3a-bfout b b′) (τ*-step (im-cploop (CB-blk b) (SB-blk b′)) (τ*-step (im-W2e-bfin b b′) (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl)))) , rsW2a b b′

-- rsW3d′ : JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b))  ≈  S-loop (nStr2 b b′).
rs_W3dp_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3dp_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-loop stStreaming} {sv = SB-blk b′} {cp = Chold (mBlock b)} (CBloop-no-bfMsg {stStreaming}) SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-loop stStreaming) (SB-blk b′) ist
...     | evL ¬m3 clst = ⊥-elim (CBloop-no-ev clst)
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (CBloop-no-ev clst)
rs_W3dp_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3dp_fwd_tau b b′ st with netW3d-τ st
... | refl = _ , wτ τ*-refl , rsW3a′ b b′
rs_W3dp_bwd_ev : ∀ b b′ {l S′} → (S-loop (nStr2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W3dp_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-loop (nStr2 b b′)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W3dp_bwd_tau : ∀ b b′ {S′} → (S-loop (nStr2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-loop stStreaming) (SB-blk b′)) (Chold (mBlock b)) ═[ τ ]═► W′ × RState W′ S′)
rs_W3dp_bwd_tau b b′ st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-clloop (SB-blk b′) (Chold (mBlock b)) stStreaming) (τ*-step (im-W3a-bfout b b′) (τ*-step (im-cploop (CB-blk b) (SB-blk b′)) (τ*-step (im-W2e-bfin b b′) (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl))))) , rsW2a b b′

-- rsW2e′ : JN (Inner (CB-blk b) (SB-blk b′)) Cidle  ≈  S-blk1 b b′.
rs_W2ep_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) (SB-blk b′)) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk1 b b′ ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2ep_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-blk b′} {cp = Cidle} CBblk-no-bfMsg SBblk-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-blk b′) ist
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBblk-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sblk1-τ b b′) (τ*-step (sp-Sloop-τ (nStr2 b b′)) τ*-refl)) (sp-nStr2-recv b b′) τ*-refl , rsWX1′ b′
rs_W2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W2ep_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2ep_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) (SB-blk b′)) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk1 b b′ ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2ep_fwd_tau b b′ st with netW2e-τ st
... | refl = _ , wτ (τ*-step (sp-Sblk1-τ b b′) τ*-refl) , rsW2h b b′
rs_W2ep_bwd_ev : ∀ b b′ {l S′} → (S-blk1 b b′ ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b′)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_W2ep_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-blk1 b b′) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_W2ep_bwd_tau : ∀ b b′ {S′} → (S-blk1 b b′ ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b′)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_W2ep_bwd_tau b b′ st with S-blk1-τ st
... | refl = _ , wτ (τ*-step (im-W2e-bfin b b′) τ*-refl) , rsW2h b b′

-- rsW3b′ : JN (Inner (CB-blk b) (SB-blk b′)) Cret  ≈  S-blk1 b b′.
rs_W3bp_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) (SB-blk b′)) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk1 b b′ ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3bp_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-blk b′} {cp = Cret} CBblk-no-bfMsg SBblk-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-blk b′) ist
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBblk-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sblk1-τ b b′) (τ*-step (sp-Sloop-τ (nStr2 b b′)) τ*-refl)) (sp-nStr2-recv b b′) τ*-refl , rsWX3′ b′
rs_W3bp_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W3bp_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3bp_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W3bp_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W3bp_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W3bp_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W3bp_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W3bp_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W3bp_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) (SB-blk b′)) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk1 b b′ ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3bp_fwd_tau b b′ st with netW3b-τ st
... | refl = _ , wτ τ*-refl , rsW2e′ b b′
rs_W3bp_bwd_ev : ∀ b b′ {l S′} → (S-blk1 b b′ ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b′)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_W3bp_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-blk1 b b′) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_W3bp_bwd_tau : ∀ b b′ {S′} → (S-blk1 b b′ ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b′)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_W3bp_bwd_tau b b′ st with S-blk1-τ st
... | refl = _ , wτ (τ*-step (im-cploop (CB-blk b) (SB-blk b′)) (τ*-step (im-W2e-bfin b b′) τ*-refl)) , rsW2h b b′

-- rsW3e′ : JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))  ≈  S-blk2 b b′ b″.
rs_W3ep_fwd_ev : ∀ b b′ b″ {l W′} → JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk2 b b′ b″ ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3ep_fwd_ev b b′ b″ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-blk b″} {cp = Chold (mBlock b′)} CBblk-no-bfMsg SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-blk b″) ist
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBblk-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sblk2-τ b b′ b″) (τ*-step (sp-Sloop-τ (nStr3 b b′ b″)) τ*-refl)) (sp-nStr3-recv b b′ b″) τ*-refl , rsW3d′ b′ b″
rs_W3ep_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W3ep_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3ep_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W3ep_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W3ep_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W3ep_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W3ep_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W3ep_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W3ep_fwd_tau : ∀ b b′ b″ {W′} → JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-blk2 b b′ b″ ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3ep_fwd_tau b b′ b″ st = ⊥-elim (netW3e-noτ st)
rs_W3ep_bwd_ev : ∀ b b′ b″ {l S′} → (S-blk2 b b′ b″ ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W3ep_bwd_ev b b′ b″ st with Hide-ev-elim bfMsgES (S-blk2 b b′ b″) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
... | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
... | heV {e = apiBF m} P' ¬m (sVis {at = (_ , apiBF m)} refl ())
rs_W3ep_bwd_tau : ∀ b b′ b″ {S′} → (S-blk2 b b′ b″ ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_W3ep_bwd_tau b b′ b″ st with S-blk2-τ st
... | refl = _ , wτ τ*-refl , rsW3e″ b b′ b″

-- rsW3e″ : JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))  ≈  S-loop (nStr3 b b′ b″).
rs_W3eq_fwd_ev : ∀ b b′ b″ {l W′} → JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr3 b b′ b″) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3eq_fwd_ev b b′ b″ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-blk b″} {cp = Chold (mBlock b′)} CBblk-no-bfMsg SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-blk b″) ist
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBblk-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sloop-τ (nStr3 b b′ b″)) τ*-refl) (sp-nStr3-recv b b′ b″) τ*-refl , rsW3d′ b′ b″
rs_W3eq_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W3eq_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3eq_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W3eq_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W3eq_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W3eq_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W3eq_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W3eq_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W3eq_fwd_tau : ∀ b b′ b″ {W′} → JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr3 b b′ b″) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3eq_fwd_tau b b′ b″ st = ⊥-elim (netW3e-noτ st)
rs_W3eq_bwd_ev : ∀ b b′ b″ {l S′} → (S-loop (nStr3 b b′ b″) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W3eq_bwd_ev b b′ b″ st with Hide-ev-elim bfMsgES (S-loop (nStr3 b b′ b″)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W3eq_bwd_tau : ∀ b b′ b″ {S′} → (S-loop (nStr3 b b′ b″) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_W3eq_bwd_tau b b′ b″ st with S-loop-τ st
... | refl = _ , wτ τ*-refl , rsW3e b b′ b″

------------------------------------------------------------------------
-- Phase F (region D) originals: the occ-1/occ-2/occ-3 streaming head configs.
------------------------------------------------------------------------
-- rsW2h : JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′))  ≈  S-loop (nStr2 b b′).
rs_W2h_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2h_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-loop stStreaming} {cp = Chold (mBlock b′)} CBblk-no-bfMsg (SBloop-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-loop stStreaming) ist
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBloop-no-ev svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev (τ*-step (sp-Sloop-τ (nStr2 b b′)) τ*-refl) (sp-nStr2-recv b b′) τ*-refl , rsWX2′ b′
rs_W2h_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W2h_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2h_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2h_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2h_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2h_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W2h_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W2h_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2h_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((S-loop (nStr2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2h_fwd_tau b b′ st with netW2h-τ st
... | refl = _ , wτ (τ*-step (sp-Sloop-τ (nStr2 b b′)) τ*-refl) , rsW2a b b′
rs_W2h_bwd_ev : ∀ b b′ {l S′} → (S-loop (nStr2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W2h_bwd_ev b b′ st with Hide-ev-elim bfMsgES (S-loop (nStr2 b b′)) st
... | he√ ()
... | heV P' ¬m (sVis () _)
rs_W2h_bwd_tau : ∀ b b′ {S′} → (S-loop (nStr2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_W2h_bwd_tau b b′ st with S-loop-τ st
... | refl = _ , wτ (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl) , rsW2a b b′

-- rsW2hI : JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′))  ≈  IT (nStr2 b b′).
rs_W2hI_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2hI_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-loop stStreaming} {cp = Chold (mBlock b′)} CBblk-no-bfMsg (SBloop-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-loop stStreaming) ist
...     | evR ¬m3 svst = ⊥-elim (SBloop-no-ev svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBloop-no-ev svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStr2-recv b b′) τ*-refl , rsWX2′ b′
rs_W2hI_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W2hI_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2hI_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2hI_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2hI_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2hI_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W2hI_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W2hI_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2hI_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2hI_fwd_tau b b′ st with netW2h-τ st
... | refl = _ , wτ τ*-refl , rsW2a b b′
rs_W2hI_bwd_ev : ∀ b b′ {l S′} → (IT (nStr2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W2hI_bwd_ev b b′ st with Hide-ev-elim bfMsgES (IT (nStr2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (SB-loop stStreaming) (Chold (mBlock b′)) b refl refl) τ*-refl , rsWX2′ b′
rs_W2hI_bwd_ev b b′ st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_W2hI_bwd_ev b b′ st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b″} refl refl) = _ , wev (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl) (im-str-blk (CB-blk b) (Chold (mBlock b′)) b″ refl refl) τ*-refl , rsW3e′ b b′ b″
rs_W2hI_bwd_ev b b′ st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl) (im-str-bdone (CB-blk b) (Chold (mBlock b′)) refl refl) τ*-refl , rsBD2e′ b b′
rs_W2hI_bwd_ev b b′ st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2hI_bwd_ev b b′ st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2hI_bwd_ev b b′ st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2hI_bwd_ev b b′ st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2hI_bwd_ev b b′ st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2hI_bwd_ev b b′ st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_W2hI_bwd_ev b b′ st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_W2hI_bwd_ev b b′ st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_W2hI_bwd_ev b b′ st | he√ ()
rs_W2hI_bwd_tau : ∀ b b′ {S′} → (IT (nStr2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-loop stStreaming)) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_W2hI_bwd_tau b b′ st = ⊥-elim (spec-noτ sStr2 st)

-- rsW3e : JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))  ≈  IT (nStr3 b b′ b″).
rs_W3e_fwd_ev : ∀ b b′ b″ {l W′} → JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr3 b b′ b″) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3e_fwd_ev b b′ b″ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-blk b″} {cp = Chold (mBlock b′)} CBblk-no-bfMsg SBblk-no-bfMsg Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-blk b″) ist
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBblk-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStr3-recv b b′ b″) τ*-refl , rsW3d′ b′ b″
rs_W3e_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W3e_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3e_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W3e_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W3e_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W3e_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W3e_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W3e_fwd_ev b b′ b″ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W3e_fwd_tau : ∀ b b′ b″ {W′} → JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr3 b b′ b″) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3e_fwd_tau b b′ b″ st = ⊥-elim (netW3e-noτ st)
rs_W3e_bwd_ev : ∀ b b′ b″ {l S′} → (IT (nStr3 b b′ b″) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W3e_bwd_ev b b′ b″ st with Hide-ev-elim bfMsgES (IT (nStr3 b b′ b″)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (SB-blk b″) (Chold (mBlock b′)) b refl refl) τ*-refl , rsW3d′ b′ b″
rs_W3e_bwd_ev b b′ b″ st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_W3e_bwd_ev b b′ b″ st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_W3e_bwd_ev b b′ b″ st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_W3e_bwd_ev b b′ b″ st | he√ ()
rs_W3e_bwd_tau : ∀ b b′ b″ {S′} → (IT (nStr3 b b′ b″) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b″)) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_W3e_bwd_tau b b′ b″ st = ⊥-elim (spec-noτ sStr3 st)

-- rsVocc1 : JN (Inner (CB-blk b) (ISn stStreaming)) Cidle  ≈  IT (nStr1 b).
rs_Vocc1_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) (ISn stStreaming)) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_Vocc1_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (ISn stStreaming)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = ISn stStreaming} {cp = Cidle} CBblk-no-bfMsg (ISn-no-bfMsg {stStreaming}) Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (ISn stStreaming)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (ISn stStreaming) ist
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStr1-recv b) τ*-refl , rsM9′
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) =
  _ , wev τ*-refl (sp-nStr1-blk b bb) (τ*-step (sp-Sblk1-τ b bb) (τ*-step (sp-Sloop-τ (nStr2 b bb)) τ*-refl)) , rsW2e b bb
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) =
  _ , wev τ*-refl (sp-nStr1-bdone b) (τ*-step (sp-Sbd1-τ b) (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl)) , rsBD1e b
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl _) (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) _
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) _
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) _
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) _
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) _
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) _
rs_Vocc1_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ()) _
rs_Vocc1_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) (ISn stStreaming)) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_Vocc1_fwd_tau b st = ⊥-elim (netVocc1-noτ st)
rs_Vocc1_bwd_ev : ∀ b {l S′} → (IT (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stStreaming)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_Vocc1_bwd_ev b st with Hide-ev-elim bfMsgES (IT (nStr1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (ISn stStreaming) Cidle b refl refl) τ*-refl , rsM9′
rs_Vocc1_bwd_ev b st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_Vocc1_bwd_ev b st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b′} refl refl) = _ , wev τ*-refl (im-str-blk (CB-blk b) Cidle b′ refl refl) τ*-refl , rsW2e′ b b′
rs_Vocc1_bwd_ev b st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (CB-blk b) Cidle refl refl) τ*-refl , rsBD1e′ b
rs_Vocc1_bwd_ev b st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_Vocc1_bwd_ev b st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_Vocc1_bwd_ev b st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_Vocc1_bwd_ev b st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_Vocc1_bwd_ev b st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_Vocc1_bwd_ev b st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_Vocc1_bwd_ev b st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_Vocc1_bwd_ev b st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_Vocc1_bwd_ev b st | he√ ()
rs_Vocc1_bwd_tau : ∀ b {S′} → (IT (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stStreaming)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_Vocc1_bwd_tau b st = ⊥-elim (spec-noτ sStr1 st)

-- rsW4 : JN (Inner (CB-blk b) (ISn stStreaming)) Cret  ≈  IT (nStr1 b).
rs_W4_fwd_ev : ∀ b {l W′} → JN (Inner (CB-blk b) (ISn stStreaming)) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr1 b) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W4_fwd_ev b st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (ISn stStreaming)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = ISn stStreaming} {cp = Cret} CBblk-no-bfMsg (ISn-no-bfMsg {stStreaming}) Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (ISn stStreaming)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (ISn stStreaming) ist
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStr1-recv b) τ*-refl , rsM5′
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = bb} refl refl) =
  _ , wev τ*-refl (sp-nStr1-blk b bb) (τ*-step (sp-Sblk1-τ b bb) (τ*-step (sp-Sloop-τ (nStr2 b bb)) τ*-refl)) , rsW3b b bb
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) =
  _ , wev τ*-refl (sp-nStr1-bdone b) (τ*-step (sp-Sbd1-τ b) (τ*-step (sp-Sloop-τ (nStrD1 b)) τ*-refl)) , rsBD2b b
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl _) (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) _
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) _
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) _
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) _
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) _
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) _
rs_W4_fwd_ev b st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ()) _
rs_W4_fwd_tau : ∀ b {W′} → JN (Inner (CB-blk b) (ISn stStreaming)) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr1 b) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W4_fwd_tau b st with netW4-τ st
... | refl = _ , wτ τ*-refl , rsVocc1 b
rs_W4_bwd_ev : ∀ b {l S′} → (IT (nStr1 b) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stStreaming)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_W4_bwd_ev b st with Hide-ev-elim bfMsgES (IT (nStr1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (ISn stStreaming) Cret b refl refl) τ*-refl , rsM5′
rs_W4_bwd_ev b st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_W4_bwd_ev b st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b′} refl refl) = _ , wev τ*-refl (im-str-blk (CB-blk b) Cret b′ refl refl) τ*-refl , rsW3b′ b b′
rs_W4_bwd_ev b st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (CB-blk b) Cret refl refl) τ*-refl , rsBD2b′ b
rs_W4_bwd_ev b st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W4_bwd_ev b st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W4_bwd_ev b st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W4_bwd_ev b st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W4_bwd_ev b st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W4_bwd_ev b st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_W4_bwd_ev b st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_W4_bwd_ev b st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_W4_bwd_ev b st | he√ ()
rs_W4_bwd_tau : ∀ b {S′} → (IT (nStr1 b) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stStreaming)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_W4_bwd_tau b st = ⊥-elim (spec-noτ sStr1 st)

-- rsW2a : JN (Inner (CB-blk b) (ISn stStreaming)) (Chold (mBlock b′))  ≈  IT (nStr2 b b′).
rs_W2a_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) (ISn stStreaming)) (Chold (mBlock b′)) ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2a_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (ISn stStreaming)) (Chold (mBlock b′))) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = ISn stStreaming} {cp = Chold (mBlock b′)} CBblk-no-bfMsg (ISn-no-bfMsg {stStreaming}) Chold-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (ISn stStreaming)) (Chold (mBlock b′)) pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Chold-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Chold-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (ISn stStreaming) ist
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStr2-recv b b′) τ*-refl , rsW2d′ b′
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} {a = b″} refl refl) =
  _ , wev τ*-refl (sp-nStr2-blk b b′ b″) τ*-refl , rsW3e′ b b′ b″
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) =
  _ , wev τ*-refl (sp-nStr2-bdone b b′) τ*-refl , rsBD2e′ b b′
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evR ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} refl _) (sVis {at = (_ , apiBF recvBFBlock)} refl ())
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) _
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) _
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) _
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) _
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) _
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) _
rs_W2a_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evBoth ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ()) _
rs_W2a_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) (ISn stStreaming)) (Chold (mBlock b′)) ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2a_fwd_tau b b′ st = ⊥-elim (netW2a-noτ st)
rs_W2a_bwd_ev : ∀ b b′ {l S′} → (IT (nStr2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stStreaming)) (Chold (mBlock b′)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W2a_bwd_ev b b′ st with Hide-ev-elim bfMsgES (IT (nStr2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (ISn stStreaming) (Chold (mBlock b′)) b refl refl) τ*-refl , rsW2d′ b′
rs_W2a_bwd_ev b b′ st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_W2a_bwd_ev b b′ st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b″} refl refl) = _ , wev τ*-refl (im-str-blk (CB-blk b) (Chold (mBlock b′)) b″ refl refl) τ*-refl , rsW3e′ b b′ b″
rs_W2a_bwd_ev b b′ st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (im-str-bdone (CB-blk b) (Chold (mBlock b′)) refl refl) τ*-refl , rsBD2e′ b b′
rs_W2a_bwd_ev b b′ st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2a_bwd_ev b b′ st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2a_bwd_ev b b′ st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2a_bwd_ev b b′ st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2a_bwd_ev b b′ st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2a_bwd_ev b b′ st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_W2a_bwd_ev b b′ st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_W2a_bwd_ev b b′ st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_W2a_bwd_ev b b′ st | he√ ()
rs_W2a_bwd_tau : ∀ b b′ {S′} → (IT (nStr2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (ISn stStreaming)) (Chold (mBlock b′)) ═[ τ ]═► W′ × RState W′ S′)
rs_W2a_bwd_tau b b′ st = ⊥-elim (spec-noτ sStr2 st)

-- rsW2e : JN (Inner (CB-blk b) (SB-blk b′)) Cidle  ≈  IT (nStr2 b b′).
rs_W2e_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) (SB-blk b′)) Cidle ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2e_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cidle) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-blk b′} {cp = Cidle} CBblk-no-bfMsg SBblk-no-bfMsg Cidle-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cidle pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cidle-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cidle-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-blk b′) ist
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBblk-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStr2-recv b b′) τ*-refl , rsWX1′ b′
rs_W2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W2e_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2e_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) (SB-blk b′)) Cidle ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W2e_fwd_tau b b′ st with netW2e-τ st
... | refl = _ , wτ τ*-refl , rsW2hI b b′
rs_W2e_bwd_ev : ∀ b b′ {l S′} → (IT (nStr2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b′)) Cidle ═[ ev l ]═► W′ × RState W′ S′)
rs_W2e_bwd_ev b b′ st with Hide-ev-elim bfMsgES (IT (nStr2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (SB-blk b′) Cidle b refl refl) τ*-refl , rsWX1′ b′
rs_W2e_bwd_ev b b′ st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_W2e_bwd_ev b b′ st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b″} refl refl) = _ , wev (τ*-step (im-W2e-bfin b b′) (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl)) (im-str-blk (CB-blk b) (Chold (mBlock b′)) b″ refl refl) τ*-refl , rsW3e′ b b′ b″
rs_W2e_bwd_ev b b′ st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-step (im-W2e-bfin b b′) (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl)) (im-str-bdone (CB-blk b) (Chold (mBlock b′)) refl refl) τ*-refl , rsBD2e′ b b′
rs_W2e_bwd_ev b b′ st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W2e_bwd_ev b b′ st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W2e_bwd_ev b b′ st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W2e_bwd_ev b b′ st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W2e_bwd_ev b b′ st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W2e_bwd_ev b b′ st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_W2e_bwd_ev b b′ st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_W2e_bwd_ev b b′ st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_W2e_bwd_ev b b′ st | he√ ()
rs_W2e_bwd_tau : ∀ b b′ {S′} → (IT (nStr2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b′)) Cidle ═[ τ ]═► W′ × RState W′ S′)
rs_W2e_bwd_tau b b′ st = ⊥-elim (spec-noτ sStr2 st)

-- rsW3b : JN (Inner (CB-blk b) (SB-blk b′)) Cret  ≈  IT (nStr2 b b′).
rs_W3b_fwd_ev : ∀ b b′ {l W′} → JN (Inner (CB-blk b) (SB-blk b′)) Cret ─[ ev l ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr2 b b′) ∖ bfMsgES) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3b_fwd_ev b b′ st with Hide-ev-elim ioBF (Par ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cret) st
... | he√ ()
... | heV {e = bfMsg} P' ¬m pev = ⊥-elim (JN-no-bfMsg {cl = CB-blk b} {sv = SB-blk b′} {cp = Cret} CBblk-no-bfMsg SBblk-no-bfMsg Cret-no-bfMsg pev)
... | heV {e = bfIn} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = bfOut} P' ¬m pev = ⊥-elim (¬m Poly.tt)
... | heV {e = apiBF m} P' ¬m pev with Par-ev-elim ioBF mrg2 (Inner (CB-blk b) (SB-blk b′)) Cret pev
...   | evSync mm _ _ = ⊥-elim mm
...   | evR ¬m2 cst = ⊥-elim (Cret-no-api cst)
...   | evBoth ¬m2 _ cst = ⊥-elim (Cret-no-api cst)
...   | evL ¬m2 ist with Par-ev-elim ∅ES mrg (CB-blk b) (SB-blk b′) ist
...     | evR ¬m3 svst = ⊥-elim (SBblk-no-api svst)
...     | evBoth ¬m3 clst svst = ⊥-elim (SBblk-no-api svst)
...     | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl q) with aa ≟ b
...       | yes refl with q
...         | refl = _ , wev τ*-refl (sp-nStr2-recv b b′) τ*-refl , rsWX3′ b′
rs_W3b_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _
rs_W3b_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3b_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W3b_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W3b_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W3b_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
rs_W3b_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
rs_W3b_fwd_ev b b′ st | heV {e = apiBF m} P' ¬m pev | evL ¬m2 ist | evL ¬m3 (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W3b_fwd_tau : ∀ b b′ {W′} → JN (Inner (CB-blk b) (SB-blk b′)) Cret ─[ τ ]─► W′
           → Σ[ S′ ∈ PT ] ((IT (nStr2 b b′) ∖ bfMsgES) ═[ τ ]═► S′ × RState W′ S′)
rs_W3b_fwd_tau b b′ st with netW3b-τ st
... | refl = _ , wτ τ*-refl , rsW2e b b′
rs_W3b_bwd_ev : ∀ b b′ {l S′} → (IT (nStr2 b b′) ∖ bfMsgES) ─[ ev l ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b′)) Cret ═[ ev l ]═► W′ × RState W′ S′)
rs_W3b_bwd_ev b b′ st with Hide-ev-elim bfMsgES (IT (nStr2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev τ*-refl (im-cl-recv (SB-blk b′) Cret b refl refl) τ*-refl , rsWX3′ b′
rs_W3b_bwd_ev b b′ st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_W3b_bwd_ev b b′ st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b″} refl refl) = _ , wev (τ*-step (im-cploop (CB-blk b) (SB-blk b′)) (τ*-step (im-W2e-bfin b b′) (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl))) (im-str-blk (CB-blk b) (Chold (mBlock b′)) b″ refl refl) τ*-refl , rsW3e′ b b′ b″
rs_W3b_bwd_ev b b′ st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-step (im-cploop (CB-blk b) (SB-blk b′)) (τ*-step (im-W2e-bfin b b′) (τ*-step (im-svloop (CB-blk b) (Chold (mBlock b′)) stStreaming) τ*-refl))) (im-str-bdone (CB-blk b) (Chold (mBlock b′)) refl refl) τ*-refl , rsBD2e′ b b′
rs_W3b_bwd_ev b b′ st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3b_bwd_ev b b′ st | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
rs_W3b_bwd_ev b b′ st | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
rs_W3b_bwd_ev b b′ st | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
rs_W3b_bwd_ev b b′ st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
rs_W3b_bwd_ev b b′ st | heV {e = bfMsg} P' ¬m (sVis {at = (_ , bfMsg)} refl ())
rs_W3b_bwd_ev b b′ st | heV {e = bfIn} P' ¬m (sVis {at = (_ , bfIn)} refl ())
rs_W3b_bwd_ev b b′ st | heV {e = bfOut} P' ¬m (sVis {at = (_ , bfOut)} refl ())
rs_W3b_bwd_ev b b′ st | he√ ()
rs_W3b_bwd_tau : ∀ b b′ {S′} → (IT (nStr2 b b′) ∖ bfMsgES) ─[ τ ]─► S′
           → Σ[ W′ ∈ PT ] (JN (Inner (CB-blk b) (SB-blk b′)) Cret ═[ τ ]═► W′ × RState W′ S′)
rs_W3b_bwd_tau b b′ st = ⊥-elim (spec-noτ sStr2 st)

------------------------------------------------------------------------
-- Phase E: assemble the guarded builders mkDR / mkDRˢ over all RState
-- constructors (generated: one clause-block per constructor), then the
-- theorem netSpec≈DR and the FD corollary.
------------------------------------------------------------------------
-- the two guarded builders (mkDRˢ = swapped orientation).
mkDR  : ∀ {W S} → RState W S → DRbisim Rr W S
mkDRˢ : ∀ {W S} → RState W S → DRbisim Rr S W
mkDR rsIdle .fwd .on-ev  st = let q = rs_Idle_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIdle .fwd .on-tau st = let q = rs_Idle_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIdle .bwd .on-ev  st = let q = rs_Idle_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIdle .bwd .on-tau st = let q = rs_Idle_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIdle .div→ d = ⊥-elim (nd-A d)
mkDR rsIdle .div← d = ⊥-elim (spec-nd-IT sIdle d)
mkDR rsDone .fwd .on-ev  st = let q = rs_Done_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsDone .fwd .on-tau st = let q = rs_Done_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsDone .bwd .on-ev  st = let q = rs_Done_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsDone .bwd .on-tau st = let q = rs_Done_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsDone .div→ d = ⊥-elim (nd-Z d)
mkDR rsDone .div← d = ⊥-elim (spec-nd-IT sDone d)
mkDR (rsReqB r) .fwd .on-ev  st = let q = rs_ReqB_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB r) .fwd .on-tau st = let q = rs_ReqB_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB r) .bwd .on-ev  st = let q = rs_ReqB_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB r) .bwd .on-tau st = let q = rs_ReqB_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB r) .div→ d = ⊥-elim (nd-B d)
mkDR (rsReqB r) .div← d = ⊥-elim (spec-nd-req d)
mkDR (rsReqBh r) .fwd .on-ev  st = let q = rs_ReqBh_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqBh r) .fwd .on-tau st = let q = rs_ReqBh_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqBh r) .bwd .on-ev  st = let q = rs_ReqBh_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqBh r) .bwd .on-tau st = let q = rs_ReqBh_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqBh r) .div→ d = ⊥-elim (nd-Bh d)
mkDR (rsReqBh r) .div← d = ⊥-elim (spec-nd-req d)
mkDR (rsReqB2 r) .fwd .on-ev  st = let q = rs_ReqB2_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB2 r) .fwd .on-tau st = let q = rs_ReqB2_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB2 r) .bwd .on-ev  st = let q = rs_ReqB2_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB2 r) .bwd .on-tau st = let q = rs_ReqB2_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB2 r) .div→ d = ⊥-elim (nd-B2 d)
mkDR (rsReqB2 r) .div← d = ⊥-elim (spec-nd-req d)
mkDR (rsReqB3 r) .fwd .on-ev  st = let q = rs_ReqB3_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB3 r) .fwd .on-tau st = let q = rs_ReqB3_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB3 r) .bwd .on-ev  st = let q = rs_ReqB3_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB3 r) .bwd .on-tau st = let q = rs_ReqB3_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB3 r) .div→ d = ⊥-elim (nd-B3 d)
mkDR (rsReqB3 r) .div← d = ⊥-elim (spec-nd-req2 d)
mkDR (rsReqB4 r) .fwd .on-ev  st = let q = rs_ReqB4_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB4 r) .fwd .on-tau st = let q = rs_ReqB4_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB4 r) .bwd .on-ev  st = let q = rs_ReqB4_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB4 r) .bwd .on-tau st = let q = rs_ReqB4_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB4 r) .div→ d = ⊥-elim (nd-B3a d)
mkDR (rsReqB4 r) .div← d = ⊥-elim (spec-nd-req2 d)
mkDR (rsReqB5 r) .fwd .on-ev  st = let q = rs_ReqB5_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB5 r) .fwd .on-tau st = let q = rs_ReqB5_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB5 r) .bwd .on-ev  st = let q = rs_ReqB5_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB5 r) .bwd .on-tau st = let q = rs_ReqB5_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB5 r) .div→ d = ⊥-elim (nd-B5 d)
mkDR (rsReqB5 r) .div← d = ⊥-elim (spec-nd-req2 d)
mkDR (rsReqB6 r) .fwd .on-ev  st = let q = rs_ReqB6_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB6 r) .fwd .on-tau st = let q = rs_ReqB6_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqB6 r) .bwd .on-ev  st = let q = rs_ReqB6_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB6 r) .bwd .on-tau st = let q = rs_ReqB6_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqB6 r) .div→ d = ⊥-elim (nd-B4 d)
mkDR (rsReqB6 r) .div← d = ⊥-elim (spec-nd-req2 d)
mkDR rsBusy .fwd .on-ev  st = let q = rs_Busy_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBusy .fwd .on-tau st = let q = rs_Busy_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBusy .bwd .on-ev  st = let q = rs_Busy_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBusy .bwd .on-tau st = let q = rs_Busy_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBusy .div→ d = ⊥-elim (nd-J d)
mkDR rsBusy .div← d = ⊥-elim (spec-nd-IT sBusy d)
mkDR rsCd .fwd .on-ev  st = let q = rs_Cd_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd .fwd .on-tau st = let q = rs_Cd_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd .bwd .on-ev  st = let q = rs_Cd_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd .bwd .on-tau st = let q = rs_Cd_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd .div→ d = ⊥-elim (nd-Cdone d)
mkDR rsCd .div← d = ⊥-elim (spec-nd-cdone d)
mkDR rsCdh .fwd .on-ev  st = let q = rs_Cdh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdh .fwd .on-tau st = let q = rs_Cdh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdh .bwd .on-ev  st = let q = rs_Cdh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdh .bwd .on-tau st = let q = rs_Cdh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdh .div→ d = ⊥-elim (nd-Cdh d)
mkDR rsCdh .div← d = ⊥-elim (spec-nd-cdone d)
mkDR rsCd2 .fwd .on-ev  st = let q = rs_Cd2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd2 .fwd .on-tau st = let q = rs_Cd2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd2 .bwd .on-ev  st = let q = rs_Cd2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd2 .bwd .on-tau st = let q = rs_Cd2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd2 .div→ d = ⊥-elim (nd-Cd2 d)
mkDR rsCd2 .div← d = ⊥-elim (spec-nd-cdone d)
mkDR rsCdR .fwd .on-ev  st = let q = rs_CdR_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdR .fwd .on-tau st = let q = rs_CdR_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdR .bwd .on-ev  st = let q = rs_CdR_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdR .bwd .on-tau st = let q = rs_CdR_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdR .div→ d = ⊥-elim (nd-Cd4 d)
mkDR rsCdR .div← d = ⊥-elim (spec-nd-loop sDone d)
mkDR (rsReqR r) .fwd .on-ev  st = let q = rs_ReqR_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqR r) .fwd .on-tau st = let q = rs_ReqR_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqR r) .bwd .on-ev  st = let q = rs_ReqR_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqR r) .bwd .on-tau st = let q = rs_ReqR_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqR r) .div→ d = ⊥-elim (nd-ReqR d)
mkDR (rsReqR r) .div← d = ⊥-elim (spec-nd-req d)
mkDR (rsReqSi r) .fwd .on-ev  st = let q = rs_ReqSi_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqSi r) .fwd .on-tau st = let q = rs_ReqSi_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqSi r) .bwd .on-ev  st = let q = rs_ReqSi_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqSi r) .bwd .on-tau st = let q = rs_ReqSi_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqSi r) .div→ d = ⊥-elim (nd-ReqSi d)
mkDR (rsReqSi r) .div← d = ⊥-elim (spec-nd-req d)
mkDR (rsReqSr r) .fwd .on-ev  st = let q = rs_ReqSr_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqSr r) .fwd .on-tau st = let q = rs_ReqSr_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsReqSr r) .bwd .on-ev  st = let q = rs_ReqSr_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqSr r) .bwd .on-tau st = let q = rs_ReqSr_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsReqSr r) .div→ d = ⊥-elim (nd-ReqSr d)
mkDR (rsReqSr r) .div← d = ⊥-elim (spec-nd-req d)
mkDR (rsIBSirr r) .fwd .on-ev  st = let q = rs_IBSirr_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsIBSirr r) .fwd .on-tau st = let q = rs_IBSirr_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsIBSirr r) .bwd .on-ev  st = let q = rs_IBSirr_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsIBSirr r) .bwd .on-tau st = let q = rs_IBSirr_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsIBSirr r) .div→ d = ⊥-elim (nd-IBSirr d)
mkDR (rsIBSirr r) .div← d = ⊥-elim (spec-nd-req d)
mkDR (rsLbBh r) .fwd .on-ev  st = let q = rs_LbBh_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsLbBh r) .fwd .on-tau st = let q = rs_LbBh_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsLbBh r) .bwd .on-ev  st = let q = rs_LbBh_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsLbBh r) .bwd .on-tau st = let q = rs_LbBh_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsLbBh r) .div→ d = ⊥-elim (nd-LbBh d)
mkDR (rsLbBh r) .div← d = ⊥-elim (spec-nd-req d)
mkDR rsG7 .fwd .on-ev  st = let q = rs_G7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG7 .fwd .on-tau st = let q = rs_G7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG7 .bwd .on-ev  st = let q = rs_G7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG7 .bwd .on-tau st = let q = rs_G7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG7 .div→ d = ⊥-elim (nd-G7 d)
mkDR rsG7 .div← d = ⊥-elim (spec-nd-IT sBusy d)
mkDR rsBI .fwd .on-ev  st = let q = rs_BI_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBI .fwd .on-tau st = let q = rs_BI_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBI .bwd .on-ev  st = let q = rs_BI_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBI .bwd .on-tau st = let q = rs_BI_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBI .div→ d = ⊥-elim (nd-I d)
mkDR rsBI .div← d = ⊥-elim (spec-nd-IT sBusy d)
mkDR rsG5 .fwd .on-ev  st = let q = rs_G5_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG5 .fwd .on-tau st = let q = rs_G5_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG5 .bwd .on-ev  st = let q = rs_G5_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG5 .bwd .on-tau st = let q = rs_G5_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG5 .div→ d = ⊥-elim (nd-G5 d)
mkDR rsG5 .div← d = ⊥-elim (spec-nd-IT sBusy d)
mkDR rsFl .fwd .on-ev  st = let q = rs_Fl_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsFl .fwd .on-tau st = let q = rs_Fl_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsFl .bwd .on-ev  st = let q = rs_Fl_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsFl .bwd .on-tau st = let q = rs_Fl_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsFl .div→ d = ⊥-elim (nd-Fl d)
mkDR rsFl .div← d = ⊥-elim (spec-nd-loop sBusy d)
mkDR rsG3a .fwd .on-ev  st = let q = rs_G3a_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG3a .fwd .on-tau st = let q = rs_G3a_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG3a .bwd .on-ev  st = let q = rs_G3a_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG3a .bwd .on-tau st = let q = rs_G3a_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG3a .div→ d = ⊥-elim (nd-G3a d)
mkDR rsG3a .div← d = ⊥-elim (spec-nd-loop sBusy d)
mkDR rsG3 .fwd .on-ev  st = let q = rs_G3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG3 .fwd .on-tau st = let q = rs_G3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG3 .bwd .on-ev  st = let q = rs_G3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG3 .bwd .on-tau st = let q = rs_G3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG3 .div→ d = ⊥-elim (nd-G3 d)
mkDR rsG3 .div← d = ⊥-elim (spec-nd-loop sBusy d)
mkDR rsG6 .fwd .on-ev  st = let q = rs_G6_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG6 .fwd .on-tau st = let q = rs_G6_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG6 .bwd .on-ev  st = let q = rs_G6_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG6 .bwd .on-tau st = let q = rs_G6_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG6 .div→ d = ⊥-elim (nd-G6 d)
mkDR rsG6 .div← d = ⊥-elim (spec-nd-loop sBusy d)
mkDR rsCdRi .fwd .on-ev  st = let q = rs_CdRi_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdRi .fwd .on-tau st = let q = rs_CdRi_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdRi .bwd .on-ev  st = let q = rs_CdRi_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdRi .bwd .on-tau st = let q = rs_CdRi_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdRi .div→ d = ⊥-elim (nd-CdR d)
mkDR rsCdRi .div← d = ⊥-elim (spec-nd-cdone d)
mkDR rsCdSi .fwd .on-ev  st = let q = rs_CdSi_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdSi .fwd .on-tau st = let q = rs_CdSi_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdSi .bwd .on-ev  st = let q = rs_CdSi_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdSi .bwd .on-tau st = let q = rs_CdSi_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdSi .div→ d = ⊥-elim (nd-CdSi d)
mkDR rsCdSi .div← d = ⊥-elim (spec-nd-cdone d)
mkDR rsCdSr .fwd .on-ev  st = let q = rs_CdSr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdSr .fwd .on-tau st = let q = rs_CdSr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCdSr .bwd .on-ev  st = let q = rs_CdSr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdSr .bwd .on-tau st = let q = rs_CdSr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCdSr .div→ d = ⊥-elim (nd-CdSr d)
mkDR rsCdSr .div← d = ⊥-elim (spec-nd-cdone d)
mkDR rsIDScd .fwd .on-ev  st = let q = rs_IDScd_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIDScd .fwd .on-tau st = let q = rs_IDScd_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIDScd .bwd .on-ev  st = let q = rs_IDScd_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIDScd .bwd .on-tau st = let q = rs_IDScd_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIDScd .div→ d = ⊥-elim (nd-IDScd d)
mkDR rsIDScd .div← d = ⊥-elim (spec-nd-cdone d)
mkDR rsLdCdh .fwd .on-ev  st = let q = rs_LdCdh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLdCdh .fwd .on-tau st = let q = rs_LdCdh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLdCdh .bwd .on-ev  st = let q = rs_LdCdh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLdCdh .bwd .on-tau st = let q = rs_LdCdh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLdCdh .div→ d = ⊥-elim (nd-LdCdh d)
mkDR rsLdCdh .div← d = ⊥-elim (spec-nd-cdone d)
mkDR rsCd7 .fwd .on-ev  st = let q = rs_Cd7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd7 .fwd .on-tau st = let q = rs_Cd7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd7 .bwd .on-ev  st = let q = rs_Cd7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd7 .bwd .on-tau st = let q = rs_Cd7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd7 .div→ d = ⊥-elim (nd-Cd7 d)
mkDR rsCd7 .div← d = ⊥-elim (spec-nd-IT sDone d)
mkDR rsCd3 .fwd .on-ev  st = let q = rs_Cd3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd3 .fwd .on-tau st = let q = rs_Cd3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd3 .bwd .on-ev  st = let q = rs_Cd3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd3 .bwd .on-tau st = let q = rs_Cd3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd3 .div→ d = ⊥-elim (nd-Cd3 d)
mkDR rsCd3 .div← d = ⊥-elim (spec-nd-loop sDone d)
mkDR rsCd5 .fwd .on-ev  st = let q = rs_Cd5_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd5 .fwd .on-tau st = let q = rs_Cd5_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd5 .bwd .on-ev  st = let q = rs_Cd5_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd5 .bwd .on-tau st = let q = rs_Cd5_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd5 .div→ d = ⊥-elim (nd-Cd5 d)
mkDR rsCd5 .div← d = ⊥-elim (spec-nd-loop sDone d)
mkDR rsCd6 .fwd .on-ev  st = let q = rs_Cd6_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd6 .fwd .on-tau st = let q = rs_Cd6_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd6 .bwd .on-ev  st = let q = rs_Cd6_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd6 .bwd .on-tau st = let q = rs_Cd6_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd6 .div→ d = ⊥-elim (nd-Cd6 d)
mkDR rsCd6 .div← d = ⊥-elim (spec-nd-loop sDone d)
mkDR rsCd8 .fwd .on-ev  st = let q = rs_Cd8_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd8 .fwd .on-tau st = let q = rs_Cd8_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd8 .bwd .on-ev  st = let q = rs_Cd8_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd8 .bwd .on-tau st = let q = rs_Cd8_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd8 .div→ d = ⊥-elim (nd-Cd8 d)
mkDR rsCd8 .div← d = ⊥-elim (spec-nd-loop sDone d)
mkDR rsCd9 .fwd .on-ev  st = let q = rs_Cd9_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd9 .fwd .on-tau st = let q = rs_Cd9_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsCd9 .bwd .on-ev  st = let q = rs_Cd9_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd9 .bwd .on-tau st = let q = rs_Cd9_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsCd9 .div→ d = ⊥-elim (nd-Cd9 d)
mkDR rsCd9 .div← d = ⊥-elim (spec-nd-loop sDone d)
mkDR rsN .fwd .on-ev  st = let q = rs_N_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN .fwd .on-tau st = let q = rs_N_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN .bwd .on-ev  st = let q = rs_N_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN .bwd .on-tau st = let q = rs_N_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN .div→ d = ⊥-elim (nd-N d)
mkDR rsN .div← d = ⊥-elim (spec-nd-noblk d)
mkDR rsIBNr .fwd .on-ev  st = let q = rs_IBNr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIBNr .fwd .on-tau st = let q = rs_IBNr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIBNr .bwd .on-ev  st = let q = rs_IBNr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIBNr .bwd .on-tau st = let q = rs_IBNr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIBNr .div→ d = ⊥-elim (nd-IBNr d)
mkDR rsIBNr .div← d = ⊥-elim (spec-nd-noblk d)
mkDR rsLbNi .fwd .on-ev  st = let q = rs_LbNi_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbNi .fwd .on-tau st = let q = rs_LbNi_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbNi .bwd .on-ev  st = let q = rs_LbNi_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbNi .bwd .on-tau st = let q = rs_LbNi_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbNi .div→ d = ⊥-elim (nd-LbNi d)
mkDR rsLbNi .div← d = ⊥-elim (spec-nd-noblk d)
mkDR rsLbNr .fwd .on-ev  st = let q = rs_LbNr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbNr .fwd .on-tau st = let q = rs_LbNr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbNr .bwd .on-ev  st = let q = rs_LbNr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbNr .bwd .on-tau st = let q = rs_LbNr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbNr .div→ d = ⊥-elim (nd-LbNr d)
mkDR rsLbNr .div← d = ⊥-elim (spec-nd-noblk d)
mkDR rsNh .fwd .on-ev  st = let q = rs_Nh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsNh .fwd .on-tau st = let q = rs_Nh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsNh .bwd .on-ev  st = let q = rs_Nh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsNh .bwd .on-tau st = let q = rs_Nh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsNh .div→ d = ⊥-elim (nd-Nh d)
mkDR rsNh .div← d = ⊥-elim (spec-nd-noblk d)
mkDR rsN2 .fwd .on-ev  st = let q = rs_N2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN2 .fwd .on-tau st = let q = rs_N2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN2 .bwd .on-ev  st = let q = rs_N2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN2 .bwd .on-tau st = let q = rs_N2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN2 .div→ d = ⊥-elim (nd-N2 d)
mkDR rsN2 .div← d = ⊥-elim (spec-nd-noblk d)
mkDR rsLbNh .fwd .on-ev  st = let q = rs_LbNh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbNh .fwd .on-tau st = let q = rs_LbNh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbNh .bwd .on-ev  st = let q = rs_LbNh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbNh .bwd .on-tau st = let q = rs_LbNh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbNh .div→ d = ⊥-elim (nd-LbNh d)
mkDR rsLbNh .div← d = ⊥-elim (spec-nd-noblk d)
mkDR rsLbN2 .fwd .on-ev  st = let q = rs_LbN2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbN2 .fwd .on-tau st = let q = rs_LbN2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbN2 .bwd .on-ev  st = let q = rs_LbN2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbN2 .bwd .on-tau st = let q = rs_LbN2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbN2 .div→ d = ⊥-elim (nd-LbN2 d)
mkDR rsLbN2 .div← d = ⊥-elim (spec-nd-noblk d)
mkDR rsN4 .fwd .on-ev  st = let q = rs_N4_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN4 .fwd .on-tau st = let q = rs_N4_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN4 .bwd .on-ev  st = let q = rs_N4_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN4 .bwd .on-tau st = let q = rs_N4_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN4 .div→ d = ⊥-elim (nd-N4 d)
mkDR rsN4 .div← d = ⊥-elim (spec-nd-IT sIdle d)
mkDR rsN7 .fwd .on-ev  st = let q = rs_N7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN7 .fwd .on-tau st = let q = rs_N7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN7 .bwd .on-ev  st = let q = rs_N7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN7 .bwd .on-tau st = let q = rs_N7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN7 .div→ d = ⊥-elim (nd-N7 d)
mkDR rsN7 .div← d = ⊥-elim (spec-nd-IT sIdle d)
mkDR rsN8 .fwd .on-ev  st = let q = rs_N8_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN8 .fwd .on-tau st = let q = rs_N8_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN8 .bwd .on-ev  st = let q = rs_N8_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN8 .bwd .on-tau st = let q = rs_N8_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN8 .div→ d = ⊥-elim (nd-N8 d)
mkDR rsN8 .div← d = ⊥-elim (spec-nd-IT sIdle d)
mkDR rsN3 .fwd .on-ev  st = let q = rs_N3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN3 .fwd .on-tau st = let q = rs_N3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN3 .bwd .on-ev  st = let q = rs_N3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN3 .bwd .on-tau st = let q = rs_N3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN3 .div→ d = ⊥-elim (nd-N3 d)
mkDR rsN3 .div← d = ⊥-elim (spec-nd-loop sIdle d)
mkDR rsN5 .fwd .on-ev  st = let q = rs_N5_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN5 .fwd .on-tau st = let q = rs_N5_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN5 .bwd .on-ev  st = let q = rs_N5_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN5 .bwd .on-tau st = let q = rs_N5_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN5 .div→ d = ⊥-elim (nd-N5 d)
mkDR rsN5 .div← d = ⊥-elim (spec-nd-loop sIdle d)
mkDR rsN6 .fwd .on-ev  st = let q = rs_N6_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN6 .fwd .on-tau st = let q = rs_N6_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN6 .bwd .on-ev  st = let q = rs_N6_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN6 .bwd .on-tau st = let q = rs_N6_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN6 .div→ d = ⊥-elim (nd-N6 d)
mkDR rsN6 .div← d = ⊥-elim (spec-nd-loop sIdle d)
mkDR rsN9 .fwd .on-ev  st = let q = rs_N9_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN9 .fwd .on-tau st = let q = rs_N9_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN9 .bwd .on-ev  st = let q = rs_N9_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN9 .bwd .on-tau st = let q = rs_N9_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN9 .div→ d = ⊥-elim (nd-N9 d)
mkDR rsN9 .div← d = ⊥-elim (spec-nd-loop sIdle d)
mkDR rsM .fwd .on-ev  st = let q = rs_M_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM .fwd .on-tau st = let q = rs_M_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM .bwd .on-ev  st = let q = rs_M_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM .bwd .on-tau st = let q = rs_M_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM .div→ d = ⊥-elim (nd-M d)
mkDR rsM .div← d = ⊥-elim (spec-nd-sbatch d)
mkDR rsIBMr .fwd .on-ev  st = let q = rs_IBMr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIBMr .fwd .on-tau st = let q = rs_IBMr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIBMr .bwd .on-ev  st = let q = rs_IBMr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIBMr .bwd .on-tau st = let q = rs_IBMr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIBMr .div→ d = ⊥-elim (nd-IBMr d)
mkDR rsIBMr .div← d = ⊥-elim (spec-nd-sbatch d)
mkDR rsLbMi .fwd .on-ev  st = let q = rs_LbMi_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbMi .fwd .on-tau st = let q = rs_LbMi_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbMi .bwd .on-ev  st = let q = rs_LbMi_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbMi .bwd .on-tau st = let q = rs_LbMi_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbMi .div→ d = ⊥-elim (nd-LbMi d)
mkDR rsLbMi .div← d = ⊥-elim (spec-nd-sbatch d)
mkDR rsLbMr .fwd .on-ev  st = let q = rs_LbMr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbMr .fwd .on-tau st = let q = rs_LbMr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbMr .bwd .on-ev  st = let q = rs_LbMr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbMr .bwd .on-tau st = let q = rs_LbMr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbMr .div→ d = ⊥-elim (nd-LbMr d)
mkDR rsLbMr .div← d = ⊥-elim (spec-nd-sbatch d)
mkDR rsSbM2 .fwd .on-ev  st = let q = rs_SbM2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsSbM2 .fwd .on-tau st = let q = rs_SbM2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsSbM2 .bwd .on-ev  st = let q = rs_SbM2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsSbM2 .bwd .on-tau st = let q = rs_SbM2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsSbM2 .div→ d = ⊥-elim (nd-M2 d)
mkDR rsSbM2 .div← d = ⊥-elim (spec-nd-IT sStr0 d)
mkDR rsLbM2 .fwd .on-ev  st = let q = rs_LbM2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbM2 .fwd .on-tau st = let q = rs_LbM2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbM2 .bwd .on-ev  st = let q = rs_LbM2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbM2 .bwd .on-tau st = let q = rs_LbM2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbM2 .div→ d = ⊥-elim (nd-LbM2 d)
mkDR rsLbM2 .div← d = ⊥-elim (spec-nd-IT sStr0 d)
mkDR rsMh .fwd .on-ev  st = let q = rs_Mh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsMh .fwd .on-tau st = let q = rs_Mh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsMh .bwd .on-ev  st = let q = rs_Mh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsMh .bwd .on-tau st = let q = rs_Mh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsMh .div→ d = ⊥-elim (nd-Mh d)
mkDR rsMh .div← d = ⊥-elim (spec-nd-loop sStr0 d)
mkDR rsLbMh .fwd .on-ev  st = let q = rs_LbMh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbMh .fwd .on-tau st = let q = rs_LbMh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbMh .bwd .on-ev  st = let q = rs_LbMh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbMh .bwd .on-tau st = let q = rs_LbMh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbMh .div→ d = ⊥-elim (nd-LbMh d)
mkDR rsLbMh .div← d = ⊥-elim (spec-nd-loop sStr0 d)
mkDR rsV0 .fwd .on-ev  st = let q = rs_V0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsV0 .fwd .on-tau st = let q = rs_V0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsV0 .bwd .on-ev  st = let q = rs_V0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsV0 .bwd .on-tau st = let q = rs_V0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsV0 .div→ d = ⊥-elim (nd-V0 d)
mkDR rsV0 .div← d = ⊥-elim (spec-nd-IT sStr0 d)
mkDR rsM7 .fwd .on-ev  st = let q = rs_M7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM7 .fwd .on-tau st = let q = rs_M7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM7 .bwd .on-ev  st = let q = rs_M7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM7 .bwd .on-tau st = let q = rs_M7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM7 .div→ d = ⊥-elim (nd-M7 d)
mkDR rsM7 .div← d = ⊥-elim (spec-nd-IT sStr0 d)
mkDR rsM9 .fwd .on-ev  st = let q = rs_M9_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM9 .fwd .on-tau st = let q = rs_M9_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM9 .bwd .on-ev  st = let q = rs_M9_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM9 .bwd .on-tau st = let q = rs_M9_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM9 .div→ d = ⊥-elim (nd-M9 d)
mkDR rsM9 .div← d = ⊥-elim (spec-nd-IT sStr0 d)
mkDR rsM5 .fwd .on-ev  st = let q = rs_M5_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM5 .fwd .on-tau st = let q = rs_M5_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM5 .bwd .on-ev  st = let q = rs_M5_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM5 .bwd .on-tau st = let q = rs_M5_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM5 .div→ d = ⊥-elim (nd-M5 d)
mkDR rsM5 .div← d = ⊥-elim (spec-nd-IT sStr0 d)
mkDR rsM4 .fwd .on-ev  st = let q = rs_M4_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM4 .fwd .on-tau st = let q = rs_M4_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM4 .bwd .on-ev  st = let q = rs_M4_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM4 .bwd .on-tau st = let q = rs_M4_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM4 .div→ d = ⊥-elim (nd-M4 d)
mkDR rsM4 .div← d = ⊥-elim (spec-nd-loop sStr0 d)
mkDR rsM8 .fwd .on-ev  st = let q = rs_M8_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM8 .fwd .on-tau st = let q = rs_M8_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM8 .bwd .on-ev  st = let q = rs_M8_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM8 .bwd .on-tau st = let q = rs_M8_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM8 .div→ d = ⊥-elim (nd-M8 d)
mkDR rsM8 .div← d = ⊥-elim (spec-nd-loop sStr0 d)
mkDR rsM3 .fwd .on-ev  st = let q = rs_M3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM3 .fwd .on-tau st = let q = rs_M3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM3 .bwd .on-ev  st = let q = rs_M3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM3 .bwd .on-tau st = let q = rs_M3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM3 .div→ d = ⊥-elim (nd-M3 d)
mkDR rsM3 .div← d = ⊥-elim (spec-nd-loop sStr0 d)
mkDR rsM6 .fwd .on-ev  st = let q = rs_M6_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM6 .fwd .on-tau st = let q = rs_M6_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM6 .bwd .on-ev  st = let q = rs_M6_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM6 .bwd .on-tau st = let q = rs_M6_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM6 .div→ d = ⊥-elim (nd-M6 d)
mkDR rsM6 .div← d = ⊥-elim (spec-nd-loop sStr0 d)
mkDR rsM9′ .fwd .on-ev  st = let q = rs_M9p_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM9′ .fwd .on-tau st = let q = rs_M9p_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM9′ .bwd .on-ev  st = let q = rs_M9p_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM9′ .bwd .on-tau st = let q = rs_M9p_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM9′ .div→ d = ⊥-elim (nd-M9 d)
mkDR rsM9′ .div← d = ⊥-elim (spec-nd-loop sStr0 d)
mkDR rsM5′ .fwd .on-ev  st = let q = rs_M5p_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM5′ .fwd .on-tau st = let q = rs_M5p_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM5′ .bwd .on-ev  st = let q = rs_M5p_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM5′ .bwd .on-tau st = let q = rs_M5p_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM5′ .div→ d = ⊥-elim (nd-M5 d)
mkDR rsM5′ .div← d = ⊥-elim (spec-nd-loop sStr0 d)
mkDR (rsVocc1 b) .fwd .on-ev  st = let q = rs_Vocc1_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsVocc1 b) .fwd .on-tau st = let q = rs_Vocc1_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsVocc1 b) .bwd .on-ev  st = let q = rs_Vocc1_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsVocc1 b) .bwd .on-tau st = let q = rs_Vocc1_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsVocc1 b) .div→ d = ⊥-elim (nd-Vocc1 d)
mkDR (rsVocc1 b) .div← d = ⊥-elim (spec-nd-IT sStr1 d)
mkDR (rsW4 b) .fwd .on-ev  st = let q = rs_W4_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4 b) .fwd .on-tau st = let q = rs_W4_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4 b) .bwd .on-ev  st = let q = rs_W4_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4 b) .bwd .on-tau st = let q = rs_W4_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4 b) .div→ d = ⊥-elim (nd-W4 d)
mkDR (rsW4 b) .div← d = ⊥-elim (spec-nd-IT sStr1 d)
mkDR (rsW4′ b) .fwd .on-ev  st = let q = rs_W4p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4′ b) .fwd .on-tau st = let q = rs_W4p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4′ b) .bwd .on-ev  st = let q = rs_W4p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4′ b) .bwd .on-tau st = let q = rs_W4p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4′ b) .div→ d = ⊥-elim (nd-W4 d)
mkDR (rsW4′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsW5 b) .fwd .on-ev  st = let q = rs_W5_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW5 b) .fwd .on-tau st = let q = rs_W5_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW5 b) .bwd .on-ev  st = let q = rs_W5_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW5 b) .bwd .on-tau st = let q = rs_W5_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW5 b) .div→ d = ⊥-elim (nd-W5 d)
mkDR (rsW5 b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsW3 b) .fwd .on-ev  st = let q = rs_W3_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3 b) .fwd .on-tau st = let q = rs_W3_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3 b) .bwd .on-ev  st = let q = rs_W3_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3 b) .bwd .on-tau st = let q = rs_W3_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3 b) .div→ d = ⊥-elim (nd-W3 d)
mkDR (rsW3 b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsW b) .fwd .on-ev  st = let q = rs_W_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW b) .fwd .on-tau st = let q = rs_W_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW b) .bwd .on-ev  st = let q = rs_W_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW b) .bwd .on-tau st = let q = rs_W_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW b) .div→ d = ⊥-elim (nd-W d)
mkDR (rsW b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsWX1 b) .fwd .on-ev  st = let q = rs_WX1_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX1 b) .fwd .on-tau st = let q = rs_WX1_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX1 b) .bwd .on-ev  st = let q = rs_WX1_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX1 b) .bwd .on-tau st = let q = rs_WX1_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX1 b) .div→ d = ⊥-elim (nd-WX1 d)
mkDR (rsWX1 b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsWX3 b) .fwd .on-ev  st = let q = rs_WX3_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX3 b) .fwd .on-tau st = let q = rs_WX3_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX3 b) .bwd .on-ev  st = let q = rs_WX3_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX3 b) .bwd .on-tau st = let q = rs_WX3_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX3 b) .div→ d = ⊥-elim (nd-WX3 d)
mkDR (rsWX3 b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsWX3a b) .fwd .on-ev  st = let q = rs_WX3a_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX3a b) .fwd .on-tau st = let q = rs_WX3a_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX3a b) .bwd .on-ev  st = let q = rs_WX3a_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX3a b) .bwd .on-tau st = let q = rs_WX3a_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX3a b) .div→ d = ⊥-elim (nd-WX3a d)
mkDR (rsWX3a b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsW2 b) .fwd .on-ev  st = let q = rs_W2_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2 b) .fwd .on-tau st = let q = rs_W2_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2 b) .bwd .on-ev  st = let q = rs_W2_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2 b) .bwd .on-tau st = let q = rs_W2_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2 b) .div→ d = ⊥-elim (nd-W2 d)
mkDR (rsW2 b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsWh b) .fwd .on-ev  st = let q = rs_Wh_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWh b) .fwd .on-tau st = let q = rs_Wh_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWh b) .bwd .on-ev  st = let q = rs_Wh_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWh b) .bwd .on-tau st = let q = rs_Wh_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWh b) .div→ d = ⊥-elim (nd-Wh d)
mkDR (rsWh b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsW2d b) .fwd .on-ev  st = let q = rs_W2d_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2d b) .fwd .on-tau st = let q = rs_W2d_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2d b) .bwd .on-ev  st = let q = rs_W2d_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2d b) .bwd .on-tau st = let q = rs_W2d_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2d b) .div→ d = ⊥-elim (nd-W2d d)
mkDR (rsW2d b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsWX2 b) .fwd .on-ev  st = let q = rs_WX2_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX2 b) .fwd .on-tau st = let q = rs_WX2_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX2 b) .bwd .on-ev  st = let q = rs_WX2_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX2 b) .bwd .on-tau st = let q = rs_WX2_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX2 b) .div→ d = ⊥-elim (nd-WX2 d)
mkDR (rsWX2 b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsW2a b b′) .fwd .on-ev  st = let q = rs_W2a_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2a b b′) .fwd .on-tau st = let q = rs_W2a_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2a b b′) .bwd .on-ev  st = let q = rs_W2a_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2a b b′) .bwd .on-tau st = let q = rs_W2a_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2a b b′) .div→ d = ⊥-elim (nd-W2a d)
mkDR (rsW2a b b′) .div← d = ⊥-elim (spec-nd-IT sStr2 d)
mkDR (rsW2h b b′) .fwd .on-ev  st = let q = rs_W2h_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2h b b′) .fwd .on-tau st = let q = rs_W2h_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2h b b′) .bwd .on-ev  st = let q = rs_W2h_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2h b b′) .bwd .on-tau st = let q = rs_W2h_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2h b b′) .div→ d = ⊥-elim (nd-W2h d)
mkDR (rsW2h b b′) .div← d = ⊥-elim (spec-nd-loop sStr2 d)
mkDR (rsW2e b b′) .fwd .on-ev  st = let q = rs_W2e_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2e b b′) .fwd .on-tau st = let q = rs_W2e_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2e b b′) .bwd .on-ev  st = let q = rs_W2e_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2e b b′) .bwd .on-tau st = let q = rs_W2e_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2e b b′) .div→ d = ⊥-elim (nd-W2e d)
mkDR (rsW2e b b′) .div← d = ⊥-elim (spec-nd-IT sStr2 d)
mkDR (rsW3b b b′) .fwd .on-ev  st = let q = rs_W3b_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3b b b′) .fwd .on-tau st = let q = rs_W3b_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3b b b′) .bwd .on-ev  st = let q = rs_W3b_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3b b b′) .bwd .on-tau st = let q = rs_W3b_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3b b b′) .div→ d = ⊥-elim (nd-W3b d)
mkDR (rsW3b b b′) .div← d = ⊥-elim (spec-nd-IT sStr2 d)
mkDR (rsW3a b b′) .fwd .on-ev  st = let q = rs_W3a_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3a b b′) .fwd .on-tau st = let q = rs_W3a_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3a b b′) .bwd .on-ev  st = let q = rs_W3a_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3a b b′) .bwd .on-tau st = let q = rs_W3a_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3a b b′) .div→ d = ⊥-elim (nd-W3a d)
mkDR (rsW3a b b′) .div← d = ⊥-elim (spec-nd-blk1 d)
mkDR (rsW3d b b′) .fwd .on-ev  st = let q = rs_W3d_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3d b b′) .fwd .on-tau st = let q = rs_W3d_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3d b b′) .bwd .on-ev  st = let q = rs_W3d_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3d b b′) .bwd .on-tau st = let q = rs_W3d_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3d b b′) .div→ d = ⊥-elim (nd-W3d d)
mkDR (rsW3d b b′) .div← d = ⊥-elim (spec-nd-blk1 d)
mkDR (rsW3e b b′ b″) .fwd .on-ev  st = let q = rs_W3e_fwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3e b b′ b″) .fwd .on-tau st = let q = rs_W3e_fwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3e b b′ b″) .bwd .on-ev  st = let q = rs_W3e_bwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3e b b′ b″) .bwd .on-tau st = let q = rs_W3e_bwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3e b b′ b″) .div→ d = ⊥-elim (nd-W3e d)
mkDR (rsW3e b b′ b″) .div← d = ⊥-elim (spec-nd-IT sStr3 d)
mkDR (rsIBblksb b) .fwd .on-ev  st = let q = rs_IBblksb_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsIBblksb b) .fwd .on-tau st = let q = rs_IBblksb_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsIBblksb b) .bwd .on-ev  st = let q = rs_IBblksb_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsIBblksb b) .bwd .on-tau st = let q = rs_IBblksb_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsIBblksb b) .div→ d = ⊥-elim (nd-IBblksb d)
mkDR (rsIBblksb b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR (rsLbBLKsb b) .fwd .on-ev  st = let q = rs_LbBLKsb_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsLbBLKsb b) .fwd .on-tau st = let q = rs_LbBLKsb_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsLbBLKsb b) .bwd .on-ev  st = let q = rs_LbBLKsb_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsLbBLKsb b) .bwd .on-tau st = let q = rs_LbBLKsb_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsLbBLKsb b) .div→ d = ⊥-elim (nd-LbBLKsb d)
mkDR (rsLbBLKsb b) .div← d = ⊥-elim (spec-nd-blk0 d)
mkDR rsIBbdsb .fwd .on-ev  st = let q = rs_IBbdsb_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIBbdsb .fwd .on-tau st = let q = rs_IBbdsb_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsIBbdsb .bwd .on-ev  st = let q = rs_IBbdsb_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIBbdsb .bwd .on-tau st = let q = rs_IBbdsb_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsIBbdsb .div→ d = ⊥-elim (nd-IBbdsb d)
mkDR rsIBbdsb .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsLbBDsb .fwd .on-ev  st = let q = rs_LbBDsb_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbBDsb .fwd .on-tau st = let q = rs_LbBDsb_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsLbBDsb .bwd .on-ev  st = let q = rs_LbBDsb_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbBDsb .bwd .on-tau st = let q = rs_LbBDsb_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsLbBDsb .div→ d = ⊥-elim (nd-LbBDsb d)
mkDR rsLbBDsb .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsBD0e .fwd .on-ev  st = let q = rs_BD0e_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0e .fwd .on-tau st = let q = rs_BD0e_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0e .bwd .on-ev  st = let q = rs_BD0e_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0e .bwd .on-tau st = let q = rs_BD0e_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0e .div→ d = ⊥-elim (nd-BD0e d)
mkDR rsBD0e .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsBD0a .fwd .on-ev  st = let q = rs_BD0a_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0a .fwd .on-tau st = let q = rs_BD0a_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0a .bwd .on-ev  st = let q = rs_BD0a_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0a .bwd .on-tau st = let q = rs_BD0a_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0a .div→ d = ⊥-elim (nd-BD0a d)
mkDR rsBD0a .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsBD0h .fwd .on-ev  st = let q = rs_BD0h_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0h .fwd .on-tau st = let q = rs_BD0h_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0h .bwd .on-ev  st = let q = rs_BD0h_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0h .bwd .on-tau st = let q = rs_BD0h_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0h .div→ d = ⊥-elim (nd-BD0h d)
mkDR rsBD0h .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsBX1 .fwd .on-ev  st = let q = rs_BX1_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX1 .fwd .on-tau st = let q = rs_BX1_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX1 .bwd .on-ev  st = let q = rs_BX1_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX1 .bwd .on-tau st = let q = rs_BX1_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX1 .div→ d = ⊥-elim (nd-BX1 d)
mkDR rsBX1 .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsBX2 .fwd .on-ev  st = let q = rs_BX2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX2 .fwd .on-tau st = let q = rs_BX2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX2 .bwd .on-ev  st = let q = rs_BX2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX2 .bwd .on-tau st = let q = rs_BX2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX2 .div→ d = ⊥-elim (nd-BX2 d)
mkDR rsBX2 .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsBX3 .fwd .on-ev  st = let q = rs_BX3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX3 .fwd .on-tau st = let q = rs_BX3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX3 .bwd .on-ev  st = let q = rs_BX3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX3 .bwd .on-tau st = let q = rs_BX3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX3 .div→ d = ⊥-elim (nd-BX3 d)
mkDR rsBX3 .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsBX3a .fwd .on-ev  st = let q = rs_BX3a_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX3a .fwd .on-tau st = let q = rs_BX3a_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX3a .bwd .on-ev  st = let q = rs_BX3a_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX3a .bwd .on-tau st = let q = rs_BX3a_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX3a .div→ d = ⊥-elim (nd-BX3a d)
mkDR rsBX3a .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR rsBD1d .fwd .on-ev  st = let q = rs_BD1d_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD1d .fwd .on-tau st = let q = rs_BD1d_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD1d .bwd .on-ev  st = let q = rs_BD1d_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD1d .bwd .on-tau st = let q = rs_BD1d_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD1d .div→ d = ⊥-elim (nd-BD1d d)
mkDR rsBD1d .div← d = ⊥-elim (spec-nd-bd0 d)
mkDR (rsBD1a b) .fwd .on-ev  st = let q = rs_BD1a_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1a b) .fwd .on-tau st = let q = rs_BD1a_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1a b) .bwd .on-ev  st = let q = rs_BD1a_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1a b) .bwd .on-tau st = let q = rs_BD1a_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1a b) .div→ d = ⊥-elim (nd-BD1a d)
mkDR (rsBD1a b) .div← d = ⊥-elim (spec-nd-IT sStrD1 d)
mkDR (rsBD1e b) .fwd .on-ev  st = let q = rs_BD1e_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1e b) .fwd .on-tau st = let q = rs_BD1e_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1e b) .bwd .on-ev  st = let q = rs_BD1e_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1e b) .bwd .on-tau st = let q = rs_BD1e_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1e b) .div→ d = ⊥-elim (nd-BD1e d)
mkDR (rsBD1e b) .div← d = ⊥-elim (spec-nd-IT sStrD1 d)
mkDR (rsBD1h b) .fwd .on-ev  st = let q = rs_BD1h_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1h b) .fwd .on-tau st = let q = rs_BD1h_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1h b) .bwd .on-ev  st = let q = rs_BD1h_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1h b) .bwd .on-tau st = let q = rs_BD1h_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1h b) .div→ d = ⊥-elim (nd-BD1h d)
mkDR (rsBD1h b) .div← d = ⊥-elim (spec-nd-IT sStrD1 d)
mkDR (rsBD2b b) .fwd .on-ev  st = let q = rs_BD2b_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2b b) .fwd .on-tau st = let q = rs_BD2b_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2b b) .bwd .on-ev  st = let q = rs_BD2b_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2b b) .bwd .on-tau st = let q = rs_BD2b_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2b b) .div→ d = ⊥-elim (nd-BD2b d)
mkDR (rsBD2b b) .div← d = ⊥-elim (spec-nd-IT sStrD1 d)
mkDR (rsBD2a b) .fwd .on-ev  st = let q = rs_BD2a_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2a b) .fwd .on-tau st = let q = rs_BD2a_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2a b) .bwd .on-ev  st = let q = rs_BD2a_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2a b) .bwd .on-tau st = let q = rs_BD2a_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2a b) .div→ d = ⊥-elim (nd-BD2a d)
mkDR (rsBD2a b) .div← d = ⊥-elim (spec-nd-bd1 d)
mkDR (rsBD2d b) .fwd .on-ev  st = let q = rs_BD2d_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2d b) .fwd .on-tau st = let q = rs_BD2d_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2d b) .bwd .on-ev  st = let q = rs_BD2d_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2d b) .bwd .on-tau st = let q = rs_BD2d_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2d b) .div→ d = ⊥-elim (nd-BD2d d)
mkDR (rsBD2d b) .div← d = ⊥-elim (spec-nd-bd1 d)
mkDR (rsBD2e b b′) .fwd .on-ev  st = let q = rs_BD2e_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2e b b′) .fwd .on-tau st = let q = rs_BD2e_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2e b b′) .bwd .on-ev  st = let q = rs_BD2e_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2e b b′) .bwd .on-tau st = let q = rs_BD2e_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2e b b′) .div→ d = ⊥-elim (nd-BD2e d)
mkDR (rsBD2e b b′) .div← d = ⊥-elim (spec-nd-IT sStrD2 d)
mkDR rsN3D0 .fwd .on-ev  st = let q = rs_N3D0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN3D0 .fwd .on-tau st = let q = rs_N3D0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN3D0 .bwd .on-ev  st = let q = rs_N3D0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN3D0 .bwd .on-tau st = let q = rs_N3D0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN3D0 .div→ d = ⊥-elim (nd-N3 d)
mkDR rsN3D0 .div← d = ⊥-elim (spec-nd-strD0 d)
mkDR rsN5D0 .fwd .on-ev  st = let q = rs_N5D0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN5D0 .fwd .on-tau st = let q = rs_N5D0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN5D0 .bwd .on-ev  st = let q = rs_N5D0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN5D0 .bwd .on-tau st = let q = rs_N5D0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN5D0 .div→ d = ⊥-elim (nd-N5 d)
mkDR rsN5D0 .div← d = ⊥-elim (spec-nd-strD0 d)
mkDR rsN6D0 .fwd .on-ev  st = let q = rs_N6D0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN6D0 .fwd .on-tau st = let q = rs_N6D0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN6D0 .bwd .on-ev  st = let q = rs_N6D0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN6D0 .bwd .on-tau st = let q = rs_N6D0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN6D0 .div→ d = ⊥-elim (nd-N6 d)
mkDR rsN6D0 .div← d = ⊥-elim (spec-nd-strD0 d)
mkDR rsN9D0 .fwd .on-ev  st = let q = rs_N9D0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN9D0 .fwd .on-tau st = let q = rs_N9D0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN9D0 .bwd .on-ev  st = let q = rs_N9D0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN9D0 .bwd .on-tau st = let q = rs_N9D0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN9D0 .div→ d = ⊥-elim (nd-N9 d)
mkDR rsN9D0 .div← d = ⊥-elim (spec-nd-strD0 d)
mkDR rsN3D0s .fwd .on-ev  st = let q = rs_N3D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN3D0s .fwd .on-tau st = let q = rs_N3D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN3D0s .bwd .on-ev  st = let q = rs_N3D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN3D0s .bwd .on-tau st = let q = rs_N3D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN3D0s .div→ d = ⊥-elim (nd-N3 d)
mkDR rsN3D0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsN5D0s .fwd .on-ev  st = let q = rs_N5D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN5D0s .fwd .on-tau st = let q = rs_N5D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN5D0s .bwd .on-ev  st = let q = rs_N5D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN5D0s .bwd .on-tau st = let q = rs_N5D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN5D0s .div→ d = ⊥-elim (nd-N5 d)
mkDR rsN5D0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsBD0eD0s .fwd .on-ev  st = let q = rs_BD0eD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0eD0s .fwd .on-tau st = let q = rs_BD0eD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0eD0s .bwd .on-ev  st = let q = rs_BD0eD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0eD0s .bwd .on-tau st = let q = rs_BD0eD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0eD0s .div→ d = ⊥-elim (nd-BD0e d)
mkDR rsBD0eD0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsBD0hD0s .fwd .on-ev  st = let q = rs_BD0hD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0hD0s .fwd .on-tau st = let q = rs_BD0hD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0hD0s .bwd .on-ev  st = let q = rs_BD0hD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0hD0s .bwd .on-tau st = let q = rs_BD0hD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0hD0s .div→ d = ⊥-elim (nd-BD0h d)
mkDR rsBD0hD0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsBD0aD0s .fwd .on-ev  st = let q = rs_BD0aD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0aD0s .fwd .on-tau st = let q = rs_BD0aD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD0aD0s .bwd .on-ev  st = let q = rs_BD0aD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0aD0s .bwd .on-tau st = let q = rs_BD0aD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD0aD0s .div→ d = ⊥-elim (nd-BD0a d)
mkDR rsBD0aD0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsBX1D0s .fwd .on-ev  st = let q = rs_BX1D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX1D0s .fwd .on-tau st = let q = rs_BX1D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX1D0s .bwd .on-ev  st = let q = rs_BX1D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX1D0s .bwd .on-tau st = let q = rs_BX1D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX1D0s .div→ d = ⊥-elim (nd-BX1 d)
mkDR rsBX1D0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsBX2D0s .fwd .on-ev  st = let q = rs_BX2D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX2D0s .fwd .on-tau st = let q = rs_BX2D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX2D0s .bwd .on-ev  st = let q = rs_BX2D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX2D0s .bwd .on-tau st = let q = rs_BX2D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX2D0s .div→ d = ⊥-elim (nd-BX2 d)
mkDR rsBX2D0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsBX3D0s .fwd .on-ev  st = let q = rs_BX3D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX3D0s .fwd .on-tau st = let q = rs_BX3D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX3D0s .bwd .on-ev  st = let q = rs_BX3D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX3D0s .bwd .on-tau st = let q = rs_BX3D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX3D0s .div→ d = ⊥-elim (nd-BX3 d)
mkDR rsBX3D0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsBX3aD0s .fwd .on-ev  st = let q = rs_BX3aD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX3aD0s .fwd .on-tau st = let q = rs_BX3aD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBX3aD0s .bwd .on-ev  st = let q = rs_BX3aD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX3aD0s .bwd .on-tau st = let q = rs_BX3aD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBX3aD0s .div→ d = ⊥-elim (nd-BX3a d)
mkDR rsBX3aD0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR rsBD1dD0s .fwd .on-ev  st = let q = rs_BD1dD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD1dD0s .fwd .on-tau st = let q = rs_BD1dD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsBD1dD0s .bwd .on-ev  st = let q = rs_BD1dD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD1dD0s .bwd .on-tau st = let q = rs_BD1dD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsBD1dD0s .div→ d = ⊥-elim (nd-BD1d d)
mkDR rsBD1dD0s .div← d = ⊥-elim (spec-nd-loop-strD0 d)
mkDR (rsBD2aD1s b) .fwd .on-ev  st = let q = rs_BD2aD1s_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2aD1s b) .fwd .on-tau st = let q = rs_BD2aD1s_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2aD1s b) .bwd .on-ev  st = let q = rs_BD2aD1s_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2aD1s b) .bwd .on-tau st = let q = rs_BD2aD1s_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2aD1s b) .div→ d = ⊥-elim (nd-BD2a d)
mkDR (rsBD2aD1s b) .div← d = ⊥-elim (spec-nd-loop sStrD1 d)
mkDR (rsBD2bD1s b) .fwd .on-ev  st = let q = rs_BD2bD1s_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2bD1s b) .fwd .on-tau st = let q = rs_BD2bD1s_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2bD1s b) .bwd .on-ev  st = let q = rs_BD2bD1s_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2bD1s b) .bwd .on-tau st = let q = rs_BD2bD1s_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2bD1s b) .div→ d = ⊥-elim (nd-BD2b d)
mkDR (rsBD2bD1s b) .div← d = ⊥-elim (spec-nd-loop sStrD1 d)
mkDR (rsBD2dD1s b) .fwd .on-ev  st = let q = rs_BD2dD1s_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2dD1s b) .fwd .on-tau st = let q = rs_BD2dD1s_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2dD1s b) .bwd .on-ev  st = let q = rs_BD2dD1s_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2dD1s b) .bwd .on-tau st = let q = rs_BD2dD1s_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2dD1s b) .div→ d = ⊥-elim (nd-BD2d d)
mkDR (rsBD2dD1s b) .div← d = ⊥-elim (spec-nd-loop sStrD1 d)
mkDR (rsBD1e′ b) .fwd .on-ev  st = let q = rs_BD1ep_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1e′ b) .fwd .on-tau st = let q = rs_BD1ep_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1e′ b) .bwd .on-ev  st = let q = rs_BD1ep_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1e′ b) .bwd .on-tau st = let q = rs_BD1ep_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1e′ b) .div→ d = ⊥-elim (nd-BD1e d)
mkDR (rsBD1e′ b) .div← d = ⊥-elim (spec-nd-bd1 d)
mkDR (rsBD1eD1s b) .fwd .on-ev  st = let q = rs_BD1eD1s_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1eD1s b) .fwd .on-tau st = let q = rs_BD1eD1s_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD1eD1s b) .bwd .on-ev  st = let q = rs_BD1eD1s_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1eD1s b) .bwd .on-tau st = let q = rs_BD1eD1s_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD1eD1s b) .div→ d = ⊥-elim (nd-BD1e d)
mkDR (rsBD1eD1s b) .div← d = ⊥-elim (spec-nd-loop sStrD1 d)
mkDR (rsBD2b′ b) .fwd .on-ev  st = let q = rs_BD2bp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2b′ b) .fwd .on-tau st = let q = rs_BD2bp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2b′ b) .bwd .on-ev  st = let q = rs_BD2bp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2b′ b) .bwd .on-tau st = let q = rs_BD2bp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2b′ b) .div→ d = ⊥-elim (nd-BD2b d)
mkDR (rsBD2b′ b) .div← d = ⊥-elim (spec-nd-bd1 d)
mkDR (rsBD2e′ b b′) .fwd .on-ev  st = let q = rs_BD2ep_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2e′ b b′) .fwd .on-tau st = let q = rs_BD2ep_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2e′ b b′) .bwd .on-ev  st = let q = rs_BD2ep_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2e′ b b′) .bwd .on-tau st = let q = rs_BD2ep_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2e′ b b′) .div→ d = ⊥-elim (nd-BD2e d)
mkDR (rsBD2e′ b b′) .div← d = ⊥-elim (spec-nd-bd2 d)
mkDR (rsBD2eD2s b b′) .fwd .on-ev  st = let q = rs_BD2eD2s_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2eD2s b b′) .fwd .on-tau st = let q = rs_BD2eD2s_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsBD2eD2s b b′) .bwd .on-ev  st = let q = rs_BD2eD2s_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2eD2s b b′) .bwd .on-tau st = let q = rs_BD2eD2s_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsBD2eD2s b b′) .div→ d = ⊥-elim (nd-BD2e d)
mkDR (rsBD2eD2s b b′) .div← d = ⊥-elim (spec-nd-loop sStrD2 d)
mkDR (rsW′ b) .fwd .on-ev  st = let q = rs_Wp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW′ b) .fwd .on-tau st = let q = rs_Wp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW′ b) .bwd .on-ev  st = let q = rs_Wp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW′ b) .bwd .on-tau st = let q = rs_Wp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW′ b) .div→ d = ⊥-elim (nd-W d)
mkDR (rsW′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsWh′ b) .fwd .on-ev  st = let q = rs_Whp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWh′ b) .fwd .on-tau st = let q = rs_Whp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWh′ b) .bwd .on-ev  st = let q = rs_Whp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWh′ b) .bwd .on-tau st = let q = rs_Whp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWh′ b) .div→ d = ⊥-elim (nd-Wh d)
mkDR (rsWh′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsWX3a′ b) .fwd .on-ev  st = let q = rs_WX3ap_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX3a′ b) .fwd .on-tau st = let q = rs_WX3ap_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX3a′ b) .bwd .on-ev  st = let q = rs_WX3ap_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX3a′ b) .bwd .on-tau st = let q = rs_WX3ap_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX3a′ b) .div→ d = ⊥-elim (nd-WX3a d)
mkDR (rsWX3a′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsWX1′ b) .fwd .on-ev  st = let q = rs_WX1p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX1′ b) .fwd .on-tau st = let q = rs_WX1p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX1′ b) .bwd .on-ev  st = let q = rs_WX1p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX1′ b) .bwd .on-tau st = let q = rs_WX1p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX1′ b) .div→ d = ⊥-elim (nd-WX1 d)
mkDR (rsWX1′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsWX3′ b) .fwd .on-ev  st = let q = rs_WX3p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX3′ b) .fwd .on-tau st = let q = rs_WX3p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX3′ b) .bwd .on-ev  st = let q = rs_WX3p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX3′ b) .bwd .on-tau st = let q = rs_WX3p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX3′ b) .div→ d = ⊥-elim (nd-WX3 d)
mkDR (rsWX3′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsWX2′ b) .fwd .on-ev  st = let q = rs_WX2p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX2′ b) .fwd .on-tau st = let q = rs_WX2p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWX2′ b) .bwd .on-ev  st = let q = rs_WX2p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX2′ b) .bwd .on-tau st = let q = rs_WX2p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWX2′ b) .div→ d = ⊥-elim (nd-WX2 d)
mkDR (rsWX2′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsW2′ b) .fwd .on-ev  st = let q = rs_W2p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2′ b) .fwd .on-tau st = let q = rs_W2p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2′ b) .bwd .on-ev  st = let q = rs_W2p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2′ b) .bwd .on-tau st = let q = rs_W2p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2′ b) .div→ d = ⊥-elim (nd-W2 d)
mkDR (rsW2′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsW2d′ b) .fwd .on-ev  st = let q = rs_W2dp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2d′ b) .fwd .on-tau st = let q = rs_W2dp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2d′ b) .bwd .on-ev  st = let q = rs_W2dp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2d′ b) .bwd .on-tau st = let q = rs_W2dp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2d′ b) .div→ d = ⊥-elim (nd-W2d d)
mkDR (rsW2d′ b) .div← d = ⊥-elim (spec-nd-loop sStr1 d)
mkDR (rsW3a′ b b′) .fwd .on-ev  st = let q = rs_W3ap_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3a′ b b′) .fwd .on-tau st = let q = rs_W3ap_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3a′ b b′) .bwd .on-ev  st = let q = rs_W3ap_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3a′ b b′) .bwd .on-tau st = let q = rs_W3ap_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3a′ b b′) .div→ d = ⊥-elim (nd-W3a d)
mkDR (rsW3a′ b b′) .div← d = ⊥-elim (spec-nd-loop sStr2 d)
mkDR (rsW3d′ b b′) .fwd .on-ev  st = let q = rs_W3dp_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3d′ b b′) .fwd .on-tau st = let q = rs_W3dp_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3d′ b b′) .bwd .on-ev  st = let q = rs_W3dp_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3d′ b b′) .bwd .on-tau st = let q = rs_W3dp_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3d′ b b′) .div→ d = ⊥-elim (nd-W3d d)
mkDR (rsW3d′ b b′) .div← d = ⊥-elim (spec-nd-loop sStr2 d)
mkDR (rsW2e′ b b′) .fwd .on-ev  st = let q = rs_W2ep_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2e′ b b′) .fwd .on-tau st = let q = rs_W2ep_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2e′ b b′) .bwd .on-ev  st = let q = rs_W2ep_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2e′ b b′) .bwd .on-tau st = let q = rs_W2ep_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2e′ b b′) .div→ d = ⊥-elim (nd-W2e d)
mkDR (rsW2e′ b b′) .div← d = ⊥-elim (spec-nd-blk1 d)
mkDR (rsW3b′ b b′) .fwd .on-ev  st = let q = rs_W3bp_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3b′ b b′) .fwd .on-tau st = let q = rs_W3bp_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3b′ b b′) .bwd .on-ev  st = let q = rs_W3bp_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3b′ b b′) .bwd .on-tau st = let q = rs_W3bp_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3b′ b b′) .div→ d = ⊥-elim (nd-W3b d)
mkDR (rsW3b′ b b′) .div← d = ⊥-elim (spec-nd-blk1 d)
mkDR (rsW3e′ b b′ b″) .fwd .on-ev  st = let q = rs_W3ep_fwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3e′ b b′ b″) .fwd .on-tau st = let q = rs_W3ep_fwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3e′ b b′ b″) .bwd .on-ev  st = let q = rs_W3ep_bwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3e′ b b′ b″) .bwd .on-tau st = let q = rs_W3ep_bwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3e′ b b′ b″) .div→ d = ⊥-elim (nd-W3e d)
mkDR (rsW3e′ b b′ b″) .div← d = ⊥-elim (spec-nd-blk2 d)
mkDR (rsW3e″ b b′ b″) .fwd .on-ev  st = let q = rs_W3eq_fwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3e″ b b′ b″) .fwd .on-tau st = let q = rs_W3eq_fwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3e″ b b′ b″) .bwd .on-ev  st = let q = rs_W3eq_bwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3e″ b b′ b″) .bwd .on-tau st = let q = rs_W3eq_bwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3e″ b b′ b″) .div→ d = ⊥-elim (nd-W3e d)
mkDR (rsW3e″ b b′ b″) .div← d = ⊥-elim (spec-nd-loop sStr3 d)
mkDR (rsW2hI b b′) .fwd .on-ev  st = let q = rs_W2hI_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2hI b b′) .fwd .on-tau st = let q = rs_W2hI_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2hI b b′) .bwd .on-ev  st = let q = rs_W2hI_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2hI b b′) .bwd .on-tau st = let q = rs_W2hI_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2hI b b′) .div→ d = ⊥-elim (nd-W2h d)
mkDR (rsW2hI b b′) .div← d = ⊥-elim (spec-nd-IT sStr2 d)
mkDR rsDL .fwd .on-ev  st = let q = rs_DL_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsDL .fwd .on-tau st = let q = rs_DL_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsDL .bwd .on-ev  st = let q = rs_DL_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsDL .bwd .on-tau st = let q = rs_DL_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsDL .div→ d = ⊥-elim (deadlock-converges d)
mkDR rsDL .div← d = ⊥-elim (deadlock-converges d)

mkDRˢ rsIdle .fwd .on-ev  st = let q = rs_Idle_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIdle .fwd .on-tau st = let q = rs_Idle_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIdle .bwd .on-ev  st = let q = rs_Idle_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIdle .bwd .on-tau st = let q = rs_Idle_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIdle .div→ d = ⊥-elim (spec-nd-IT sIdle d)
mkDRˢ rsIdle .div← d = ⊥-elim (nd-A d)
mkDRˢ rsDone .fwd .on-ev  st = let q = rs_Done_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsDone .fwd .on-tau st = let q = rs_Done_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsDone .bwd .on-ev  st = let q = rs_Done_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsDone .bwd .on-tau st = let q = rs_Done_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsDone .div→ d = ⊥-elim (spec-nd-IT sDone d)
mkDRˢ rsDone .div← d = ⊥-elim (nd-Z d)
mkDRˢ (rsReqB r) .fwd .on-ev  st = let q = rs_ReqB_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB r) .fwd .on-tau st = let q = rs_ReqB_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB r) .bwd .on-ev  st = let q = rs_ReqB_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB r) .bwd .on-tau st = let q = rs_ReqB_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB r) .div→ d = ⊥-elim (spec-nd-req d)
mkDRˢ (rsReqB r) .div← d = ⊥-elim (nd-B d)
mkDRˢ (rsReqBh r) .fwd .on-ev  st = let q = rs_ReqBh_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqBh r) .fwd .on-tau st = let q = rs_ReqBh_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqBh r) .bwd .on-ev  st = let q = rs_ReqBh_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqBh r) .bwd .on-tau st = let q = rs_ReqBh_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqBh r) .div→ d = ⊥-elim (spec-nd-req d)
mkDRˢ (rsReqBh r) .div← d = ⊥-elim (nd-Bh d)
mkDRˢ (rsReqB2 r) .fwd .on-ev  st = let q = rs_ReqB2_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB2 r) .fwd .on-tau st = let q = rs_ReqB2_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB2 r) .bwd .on-ev  st = let q = rs_ReqB2_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB2 r) .bwd .on-tau st = let q = rs_ReqB2_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB2 r) .div→ d = ⊥-elim (spec-nd-req d)
mkDRˢ (rsReqB2 r) .div← d = ⊥-elim (nd-B2 d)
mkDRˢ (rsReqB3 r) .fwd .on-ev  st = let q = rs_ReqB3_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB3 r) .fwd .on-tau st = let q = rs_ReqB3_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB3 r) .bwd .on-ev  st = let q = rs_ReqB3_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB3 r) .bwd .on-tau st = let q = rs_ReqB3_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB3 r) .div→ d = ⊥-elim (spec-nd-req2 d)
mkDRˢ (rsReqB3 r) .div← d = ⊥-elim (nd-B3 d)
mkDRˢ (rsReqB4 r) .fwd .on-ev  st = let q = rs_ReqB4_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB4 r) .fwd .on-tau st = let q = rs_ReqB4_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB4 r) .bwd .on-ev  st = let q = rs_ReqB4_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB4 r) .bwd .on-tau st = let q = rs_ReqB4_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB4 r) .div→ d = ⊥-elim (spec-nd-req2 d)
mkDRˢ (rsReqB4 r) .div← d = ⊥-elim (nd-B3a d)
mkDRˢ (rsReqB5 r) .fwd .on-ev  st = let q = rs_ReqB5_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB5 r) .fwd .on-tau st = let q = rs_ReqB5_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB5 r) .bwd .on-ev  st = let q = rs_ReqB5_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB5 r) .bwd .on-tau st = let q = rs_ReqB5_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB5 r) .div→ d = ⊥-elim (spec-nd-req2 d)
mkDRˢ (rsReqB5 r) .div← d = ⊥-elim (nd-B5 d)
mkDRˢ (rsReqB6 r) .fwd .on-ev  st = let q = rs_ReqB6_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB6 r) .fwd .on-tau st = let q = rs_ReqB6_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqB6 r) .bwd .on-ev  st = let q = rs_ReqB6_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB6 r) .bwd .on-tau st = let q = rs_ReqB6_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqB6 r) .div→ d = ⊥-elim (spec-nd-req2 d)
mkDRˢ (rsReqB6 r) .div← d = ⊥-elim (nd-B4 d)
mkDRˢ rsBusy .fwd .on-ev  st = let q = rs_Busy_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBusy .fwd .on-tau st = let q = rs_Busy_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBusy .bwd .on-ev  st = let q = rs_Busy_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBusy .bwd .on-tau st = let q = rs_Busy_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBusy .div→ d = ⊥-elim (spec-nd-IT sBusy d)
mkDRˢ rsBusy .div← d = ⊥-elim (nd-J d)
mkDRˢ rsCd .fwd .on-ev  st = let q = rs_Cd_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd .fwd .on-tau st = let q = rs_Cd_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd .bwd .on-ev  st = let q = rs_Cd_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd .bwd .on-tau st = let q = rs_Cd_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd .div→ d = ⊥-elim (spec-nd-cdone d)
mkDRˢ rsCd .div← d = ⊥-elim (nd-Cdone d)
mkDRˢ rsCdh .fwd .on-ev  st = let q = rs_Cdh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdh .fwd .on-tau st = let q = rs_Cdh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdh .bwd .on-ev  st = let q = rs_Cdh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdh .bwd .on-tau st = let q = rs_Cdh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdh .div→ d = ⊥-elim (spec-nd-cdone d)
mkDRˢ rsCdh .div← d = ⊥-elim (nd-Cdh d)
mkDRˢ rsCd2 .fwd .on-ev  st = let q = rs_Cd2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd2 .fwd .on-tau st = let q = rs_Cd2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd2 .bwd .on-ev  st = let q = rs_Cd2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd2 .bwd .on-tau st = let q = rs_Cd2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd2 .div→ d = ⊥-elim (spec-nd-cdone d)
mkDRˢ rsCd2 .div← d = ⊥-elim (nd-Cd2 d)
mkDRˢ rsCdR .fwd .on-ev  st = let q = rs_CdR_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdR .fwd .on-tau st = let q = rs_CdR_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdR .bwd .on-ev  st = let q = rs_CdR_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdR .bwd .on-tau st = let q = rs_CdR_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdR .div→ d = ⊥-elim (spec-nd-loop sDone d)
mkDRˢ rsCdR .div← d = ⊥-elim (nd-Cd4 d)
mkDRˢ (rsReqR r) .fwd .on-ev  st = let q = rs_ReqR_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqR r) .fwd .on-tau st = let q = rs_ReqR_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqR r) .bwd .on-ev  st = let q = rs_ReqR_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqR r) .bwd .on-tau st = let q = rs_ReqR_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqR r) .div→ d = ⊥-elim (spec-nd-req d)
mkDRˢ (rsReqR r) .div← d = ⊥-elim (nd-ReqR d)
mkDRˢ (rsReqSi r) .fwd .on-ev  st = let q = rs_ReqSi_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqSi r) .fwd .on-tau st = let q = rs_ReqSi_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqSi r) .bwd .on-ev  st = let q = rs_ReqSi_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqSi r) .bwd .on-tau st = let q = rs_ReqSi_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqSi r) .div→ d = ⊥-elim (spec-nd-req d)
mkDRˢ (rsReqSi r) .div← d = ⊥-elim (nd-ReqSi d)
mkDRˢ (rsReqSr r) .fwd .on-ev  st = let q = rs_ReqSr_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqSr r) .fwd .on-tau st = let q = rs_ReqSr_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsReqSr r) .bwd .on-ev  st = let q = rs_ReqSr_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqSr r) .bwd .on-tau st = let q = rs_ReqSr_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsReqSr r) .div→ d = ⊥-elim (spec-nd-req d)
mkDRˢ (rsReqSr r) .div← d = ⊥-elim (nd-ReqSr d)
mkDRˢ (rsIBSirr r) .fwd .on-ev  st = let q = rs_IBSirr_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsIBSirr r) .fwd .on-tau st = let q = rs_IBSirr_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsIBSirr r) .bwd .on-ev  st = let q = rs_IBSirr_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsIBSirr r) .bwd .on-tau st = let q = rs_IBSirr_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsIBSirr r) .div→ d = ⊥-elim (spec-nd-req d)
mkDRˢ (rsIBSirr r) .div← d = ⊥-elim (nd-IBSirr d)
mkDRˢ (rsLbBh r) .fwd .on-ev  st = let q = rs_LbBh_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsLbBh r) .fwd .on-tau st = let q = rs_LbBh_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsLbBh r) .bwd .on-ev  st = let q = rs_LbBh_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsLbBh r) .bwd .on-tau st = let q = rs_LbBh_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsLbBh r) .div→ d = ⊥-elim (spec-nd-req d)
mkDRˢ (rsLbBh r) .div← d = ⊥-elim (nd-LbBh d)
mkDRˢ rsG7 .fwd .on-ev  st = let q = rs_G7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG7 .fwd .on-tau st = let q = rs_G7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG7 .bwd .on-ev  st = let q = rs_G7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG7 .bwd .on-tau st = let q = rs_G7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG7 .div→ d = ⊥-elim (spec-nd-IT sBusy d)
mkDRˢ rsG7 .div← d = ⊥-elim (nd-G7 d)
mkDRˢ rsBI .fwd .on-ev  st = let q = rs_BI_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBI .fwd .on-tau st = let q = rs_BI_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBI .bwd .on-ev  st = let q = rs_BI_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBI .bwd .on-tau st = let q = rs_BI_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBI .div→ d = ⊥-elim (spec-nd-IT sBusy d)
mkDRˢ rsBI .div← d = ⊥-elim (nd-I d)
mkDRˢ rsG5 .fwd .on-ev  st = let q = rs_G5_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG5 .fwd .on-tau st = let q = rs_G5_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG5 .bwd .on-ev  st = let q = rs_G5_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG5 .bwd .on-tau st = let q = rs_G5_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG5 .div→ d = ⊥-elim (spec-nd-IT sBusy d)
mkDRˢ rsG5 .div← d = ⊥-elim (nd-G5 d)
mkDRˢ rsFl .fwd .on-ev  st = let q = rs_Fl_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsFl .fwd .on-tau st = let q = rs_Fl_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsFl .bwd .on-ev  st = let q = rs_Fl_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsFl .bwd .on-tau st = let q = rs_Fl_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsFl .div→ d = ⊥-elim (spec-nd-loop sBusy d)
mkDRˢ rsFl .div← d = ⊥-elim (nd-Fl d)
mkDRˢ rsG3a .fwd .on-ev  st = let q = rs_G3a_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG3a .fwd .on-tau st = let q = rs_G3a_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG3a .bwd .on-ev  st = let q = rs_G3a_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG3a .bwd .on-tau st = let q = rs_G3a_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG3a .div→ d = ⊥-elim (spec-nd-loop sBusy d)
mkDRˢ rsG3a .div← d = ⊥-elim (nd-G3a d)
mkDRˢ rsG3 .fwd .on-ev  st = let q = rs_G3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG3 .fwd .on-tau st = let q = rs_G3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG3 .bwd .on-ev  st = let q = rs_G3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG3 .bwd .on-tau st = let q = rs_G3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG3 .div→ d = ⊥-elim (spec-nd-loop sBusy d)
mkDRˢ rsG3 .div← d = ⊥-elim (nd-G3 d)
mkDRˢ rsG6 .fwd .on-ev  st = let q = rs_G6_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG6 .fwd .on-tau st = let q = rs_G6_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG6 .bwd .on-ev  st = let q = rs_G6_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG6 .bwd .on-tau st = let q = rs_G6_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG6 .div→ d = ⊥-elim (spec-nd-loop sBusy d)
mkDRˢ rsG6 .div← d = ⊥-elim (nd-G6 d)
mkDRˢ rsCdRi .fwd .on-ev  st = let q = rs_CdRi_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdRi .fwd .on-tau st = let q = rs_CdRi_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdRi .bwd .on-ev  st = let q = rs_CdRi_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdRi .bwd .on-tau st = let q = rs_CdRi_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdRi .div→ d = ⊥-elim (spec-nd-cdone d)
mkDRˢ rsCdRi .div← d = ⊥-elim (nd-CdR d)
mkDRˢ rsCdSi .fwd .on-ev  st = let q = rs_CdSi_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdSi .fwd .on-tau st = let q = rs_CdSi_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdSi .bwd .on-ev  st = let q = rs_CdSi_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdSi .bwd .on-tau st = let q = rs_CdSi_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdSi .div→ d = ⊥-elim (spec-nd-cdone d)
mkDRˢ rsCdSi .div← d = ⊥-elim (nd-CdSi d)
mkDRˢ rsCdSr .fwd .on-ev  st = let q = rs_CdSr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdSr .fwd .on-tau st = let q = rs_CdSr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCdSr .bwd .on-ev  st = let q = rs_CdSr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdSr .bwd .on-tau st = let q = rs_CdSr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCdSr .div→ d = ⊥-elim (spec-nd-cdone d)
mkDRˢ rsCdSr .div← d = ⊥-elim (nd-CdSr d)
mkDRˢ rsIDScd .fwd .on-ev  st = let q = rs_IDScd_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIDScd .fwd .on-tau st = let q = rs_IDScd_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIDScd .bwd .on-ev  st = let q = rs_IDScd_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIDScd .bwd .on-tau st = let q = rs_IDScd_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIDScd .div→ d = ⊥-elim (spec-nd-cdone d)
mkDRˢ rsIDScd .div← d = ⊥-elim (nd-IDScd d)
mkDRˢ rsLdCdh .fwd .on-ev  st = let q = rs_LdCdh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLdCdh .fwd .on-tau st = let q = rs_LdCdh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLdCdh .bwd .on-ev  st = let q = rs_LdCdh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLdCdh .bwd .on-tau st = let q = rs_LdCdh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLdCdh .div→ d = ⊥-elim (spec-nd-cdone d)
mkDRˢ rsLdCdh .div← d = ⊥-elim (nd-LdCdh d)
mkDRˢ rsCd7 .fwd .on-ev  st = let q = rs_Cd7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd7 .fwd .on-tau st = let q = rs_Cd7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd7 .bwd .on-ev  st = let q = rs_Cd7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd7 .bwd .on-tau st = let q = rs_Cd7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd7 .div→ d = ⊥-elim (spec-nd-IT sDone d)
mkDRˢ rsCd7 .div← d = ⊥-elim (nd-Cd7 d)
mkDRˢ rsCd3 .fwd .on-ev  st = let q = rs_Cd3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd3 .fwd .on-tau st = let q = rs_Cd3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd3 .bwd .on-ev  st = let q = rs_Cd3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd3 .bwd .on-tau st = let q = rs_Cd3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd3 .div→ d = ⊥-elim (spec-nd-loop sDone d)
mkDRˢ rsCd3 .div← d = ⊥-elim (nd-Cd3 d)
mkDRˢ rsCd5 .fwd .on-ev  st = let q = rs_Cd5_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd5 .fwd .on-tau st = let q = rs_Cd5_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd5 .bwd .on-ev  st = let q = rs_Cd5_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd5 .bwd .on-tau st = let q = rs_Cd5_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd5 .div→ d = ⊥-elim (spec-nd-loop sDone d)
mkDRˢ rsCd5 .div← d = ⊥-elim (nd-Cd5 d)
mkDRˢ rsCd6 .fwd .on-ev  st = let q = rs_Cd6_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd6 .fwd .on-tau st = let q = rs_Cd6_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd6 .bwd .on-ev  st = let q = rs_Cd6_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd6 .bwd .on-tau st = let q = rs_Cd6_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd6 .div→ d = ⊥-elim (spec-nd-loop sDone d)
mkDRˢ rsCd6 .div← d = ⊥-elim (nd-Cd6 d)
mkDRˢ rsCd8 .fwd .on-ev  st = let q = rs_Cd8_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd8 .fwd .on-tau st = let q = rs_Cd8_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd8 .bwd .on-ev  st = let q = rs_Cd8_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd8 .bwd .on-tau st = let q = rs_Cd8_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd8 .div→ d = ⊥-elim (spec-nd-loop sDone d)
mkDRˢ rsCd8 .div← d = ⊥-elim (nd-Cd8 d)
mkDRˢ rsCd9 .fwd .on-ev  st = let q = rs_Cd9_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd9 .fwd .on-tau st = let q = rs_Cd9_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsCd9 .bwd .on-ev  st = let q = rs_Cd9_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd9 .bwd .on-tau st = let q = rs_Cd9_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsCd9 .div→ d = ⊥-elim (spec-nd-loop sDone d)
mkDRˢ rsCd9 .div← d = ⊥-elim (nd-Cd9 d)
mkDRˢ rsN .fwd .on-ev  st = let q = rs_N_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN .fwd .on-tau st = let q = rs_N_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN .bwd .on-ev  st = let q = rs_N_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN .bwd .on-tau st = let q = rs_N_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN .div→ d = ⊥-elim (spec-nd-noblk d)
mkDRˢ rsN .div← d = ⊥-elim (nd-N d)
mkDRˢ rsIBNr .fwd .on-ev  st = let q = rs_IBNr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIBNr .fwd .on-tau st = let q = rs_IBNr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIBNr .bwd .on-ev  st = let q = rs_IBNr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIBNr .bwd .on-tau st = let q = rs_IBNr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIBNr .div→ d = ⊥-elim (spec-nd-noblk d)
mkDRˢ rsIBNr .div← d = ⊥-elim (nd-IBNr d)
mkDRˢ rsLbNi .fwd .on-ev  st = let q = rs_LbNi_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbNi .fwd .on-tau st = let q = rs_LbNi_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbNi .bwd .on-ev  st = let q = rs_LbNi_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbNi .bwd .on-tau st = let q = rs_LbNi_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbNi .div→ d = ⊥-elim (spec-nd-noblk d)
mkDRˢ rsLbNi .div← d = ⊥-elim (nd-LbNi d)
mkDRˢ rsLbNr .fwd .on-ev  st = let q = rs_LbNr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbNr .fwd .on-tau st = let q = rs_LbNr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbNr .bwd .on-ev  st = let q = rs_LbNr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbNr .bwd .on-tau st = let q = rs_LbNr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbNr .div→ d = ⊥-elim (spec-nd-noblk d)
mkDRˢ rsLbNr .div← d = ⊥-elim (nd-LbNr d)
mkDRˢ rsNh .fwd .on-ev  st = let q = rs_Nh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsNh .fwd .on-tau st = let q = rs_Nh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsNh .bwd .on-ev  st = let q = rs_Nh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsNh .bwd .on-tau st = let q = rs_Nh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsNh .div→ d = ⊥-elim (spec-nd-noblk d)
mkDRˢ rsNh .div← d = ⊥-elim (nd-Nh d)
mkDRˢ rsN2 .fwd .on-ev  st = let q = rs_N2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN2 .fwd .on-tau st = let q = rs_N2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN2 .bwd .on-ev  st = let q = rs_N2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN2 .bwd .on-tau st = let q = rs_N2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN2 .div→ d = ⊥-elim (spec-nd-noblk d)
mkDRˢ rsN2 .div← d = ⊥-elim (nd-N2 d)
mkDRˢ rsLbNh .fwd .on-ev  st = let q = rs_LbNh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbNh .fwd .on-tau st = let q = rs_LbNh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbNh .bwd .on-ev  st = let q = rs_LbNh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbNh .bwd .on-tau st = let q = rs_LbNh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbNh .div→ d = ⊥-elim (spec-nd-noblk d)
mkDRˢ rsLbNh .div← d = ⊥-elim (nd-LbNh d)
mkDRˢ rsLbN2 .fwd .on-ev  st = let q = rs_LbN2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbN2 .fwd .on-tau st = let q = rs_LbN2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbN2 .bwd .on-ev  st = let q = rs_LbN2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbN2 .bwd .on-tau st = let q = rs_LbN2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbN2 .div→ d = ⊥-elim (spec-nd-noblk d)
mkDRˢ rsLbN2 .div← d = ⊥-elim (nd-LbN2 d)
mkDRˢ rsN4 .fwd .on-ev  st = let q = rs_N4_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN4 .fwd .on-tau st = let q = rs_N4_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN4 .bwd .on-ev  st = let q = rs_N4_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN4 .bwd .on-tau st = let q = rs_N4_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN4 .div→ d = ⊥-elim (spec-nd-IT sIdle d)
mkDRˢ rsN4 .div← d = ⊥-elim (nd-N4 d)
mkDRˢ rsN7 .fwd .on-ev  st = let q = rs_N7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN7 .fwd .on-tau st = let q = rs_N7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN7 .bwd .on-ev  st = let q = rs_N7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN7 .bwd .on-tau st = let q = rs_N7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN7 .div→ d = ⊥-elim (spec-nd-IT sIdle d)
mkDRˢ rsN7 .div← d = ⊥-elim (nd-N7 d)
mkDRˢ rsN8 .fwd .on-ev  st = let q = rs_N8_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN8 .fwd .on-tau st = let q = rs_N8_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN8 .bwd .on-ev  st = let q = rs_N8_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN8 .bwd .on-tau st = let q = rs_N8_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN8 .div→ d = ⊥-elim (spec-nd-IT sIdle d)
mkDRˢ rsN8 .div← d = ⊥-elim (nd-N8 d)
mkDRˢ rsN3 .fwd .on-ev  st = let q = rs_N3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN3 .fwd .on-tau st = let q = rs_N3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN3 .bwd .on-ev  st = let q = rs_N3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN3 .bwd .on-tau st = let q = rs_N3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN3 .div→ d = ⊥-elim (spec-nd-loop sIdle d)
mkDRˢ rsN3 .div← d = ⊥-elim (nd-N3 d)
mkDRˢ rsN5 .fwd .on-ev  st = let q = rs_N5_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN5 .fwd .on-tau st = let q = rs_N5_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN5 .bwd .on-ev  st = let q = rs_N5_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN5 .bwd .on-tau st = let q = rs_N5_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN5 .div→ d = ⊥-elim (spec-nd-loop sIdle d)
mkDRˢ rsN5 .div← d = ⊥-elim (nd-N5 d)
mkDRˢ rsN6 .fwd .on-ev  st = let q = rs_N6_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN6 .fwd .on-tau st = let q = rs_N6_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN6 .bwd .on-ev  st = let q = rs_N6_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN6 .bwd .on-tau st = let q = rs_N6_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN6 .div→ d = ⊥-elim (spec-nd-loop sIdle d)
mkDRˢ rsN6 .div← d = ⊥-elim (nd-N6 d)
mkDRˢ rsN9 .fwd .on-ev  st = let q = rs_N9_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN9 .fwd .on-tau st = let q = rs_N9_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN9 .bwd .on-ev  st = let q = rs_N9_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN9 .bwd .on-tau st = let q = rs_N9_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN9 .div→ d = ⊥-elim (spec-nd-loop sIdle d)
mkDRˢ rsN9 .div← d = ⊥-elim (nd-N9 d)
mkDRˢ rsM .fwd .on-ev  st = let q = rs_M_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM .fwd .on-tau st = let q = rs_M_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM .bwd .on-ev  st = let q = rs_M_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM .bwd .on-tau st = let q = rs_M_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM .div→ d = ⊥-elim (spec-nd-sbatch d)
mkDRˢ rsM .div← d = ⊥-elim (nd-M d)
mkDRˢ rsIBMr .fwd .on-ev  st = let q = rs_IBMr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIBMr .fwd .on-tau st = let q = rs_IBMr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIBMr .bwd .on-ev  st = let q = rs_IBMr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIBMr .bwd .on-tau st = let q = rs_IBMr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIBMr .div→ d = ⊥-elim (spec-nd-sbatch d)
mkDRˢ rsIBMr .div← d = ⊥-elim (nd-IBMr d)
mkDRˢ rsLbMi .fwd .on-ev  st = let q = rs_LbMi_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbMi .fwd .on-tau st = let q = rs_LbMi_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbMi .bwd .on-ev  st = let q = rs_LbMi_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbMi .bwd .on-tau st = let q = rs_LbMi_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbMi .div→ d = ⊥-elim (spec-nd-sbatch d)
mkDRˢ rsLbMi .div← d = ⊥-elim (nd-LbMi d)
mkDRˢ rsLbMr .fwd .on-ev  st = let q = rs_LbMr_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbMr .fwd .on-tau st = let q = rs_LbMr_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbMr .bwd .on-ev  st = let q = rs_LbMr_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbMr .bwd .on-tau st = let q = rs_LbMr_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbMr .div→ d = ⊥-elim (spec-nd-sbatch d)
mkDRˢ rsLbMr .div← d = ⊥-elim (nd-LbMr d)
mkDRˢ rsSbM2 .fwd .on-ev  st = let q = rs_SbM2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsSbM2 .fwd .on-tau st = let q = rs_SbM2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsSbM2 .bwd .on-ev  st = let q = rs_SbM2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsSbM2 .bwd .on-tau st = let q = rs_SbM2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsSbM2 .div→ d = ⊥-elim (spec-nd-IT sStr0 d)
mkDRˢ rsSbM2 .div← d = ⊥-elim (nd-M2 d)
mkDRˢ rsLbM2 .fwd .on-ev  st = let q = rs_LbM2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbM2 .fwd .on-tau st = let q = rs_LbM2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbM2 .bwd .on-ev  st = let q = rs_LbM2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbM2 .bwd .on-tau st = let q = rs_LbM2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbM2 .div→ d = ⊥-elim (spec-nd-IT sStr0 d)
mkDRˢ rsLbM2 .div← d = ⊥-elim (nd-LbM2 d)
mkDRˢ rsMh .fwd .on-ev  st = let q = rs_Mh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsMh .fwd .on-tau st = let q = rs_Mh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsMh .bwd .on-ev  st = let q = rs_Mh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsMh .bwd .on-tau st = let q = rs_Mh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsMh .div→ d = ⊥-elim (spec-nd-loop sStr0 d)
mkDRˢ rsMh .div← d = ⊥-elim (nd-Mh d)
mkDRˢ rsLbMh .fwd .on-ev  st = let q = rs_LbMh_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbMh .fwd .on-tau st = let q = rs_LbMh_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbMh .bwd .on-ev  st = let q = rs_LbMh_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbMh .bwd .on-tau st = let q = rs_LbMh_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbMh .div→ d = ⊥-elim (spec-nd-loop sStr0 d)
mkDRˢ rsLbMh .div← d = ⊥-elim (nd-LbMh d)
mkDRˢ rsV0 .fwd .on-ev  st = let q = rs_V0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsV0 .fwd .on-tau st = let q = rs_V0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsV0 .bwd .on-ev  st = let q = rs_V0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsV0 .bwd .on-tau st = let q = rs_V0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsV0 .div→ d = ⊥-elim (spec-nd-IT sStr0 d)
mkDRˢ rsV0 .div← d = ⊥-elim (nd-V0 d)
mkDRˢ rsM7 .fwd .on-ev  st = let q = rs_M7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM7 .fwd .on-tau st = let q = rs_M7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM7 .bwd .on-ev  st = let q = rs_M7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM7 .bwd .on-tau st = let q = rs_M7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM7 .div→ d = ⊥-elim (spec-nd-IT sStr0 d)
mkDRˢ rsM7 .div← d = ⊥-elim (nd-M7 d)
mkDRˢ rsM9 .fwd .on-ev  st = let q = rs_M9_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM9 .fwd .on-tau st = let q = rs_M9_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM9 .bwd .on-ev  st = let q = rs_M9_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM9 .bwd .on-tau st = let q = rs_M9_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM9 .div→ d = ⊥-elim (spec-nd-IT sStr0 d)
mkDRˢ rsM9 .div← d = ⊥-elim (nd-M9 d)
mkDRˢ rsM5 .fwd .on-ev  st = let q = rs_M5_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM5 .fwd .on-tau st = let q = rs_M5_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM5 .bwd .on-ev  st = let q = rs_M5_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM5 .bwd .on-tau st = let q = rs_M5_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM5 .div→ d = ⊥-elim (spec-nd-IT sStr0 d)
mkDRˢ rsM5 .div← d = ⊥-elim (nd-M5 d)
mkDRˢ rsM4 .fwd .on-ev  st = let q = rs_M4_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM4 .fwd .on-tau st = let q = rs_M4_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM4 .bwd .on-ev  st = let q = rs_M4_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM4 .bwd .on-tau st = let q = rs_M4_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM4 .div→ d = ⊥-elim (spec-nd-loop sStr0 d)
mkDRˢ rsM4 .div← d = ⊥-elim (nd-M4 d)
mkDRˢ rsM8 .fwd .on-ev  st = let q = rs_M8_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM8 .fwd .on-tau st = let q = rs_M8_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM8 .bwd .on-ev  st = let q = rs_M8_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM8 .bwd .on-tau st = let q = rs_M8_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM8 .div→ d = ⊥-elim (spec-nd-loop sStr0 d)
mkDRˢ rsM8 .div← d = ⊥-elim (nd-M8 d)
mkDRˢ rsM3 .fwd .on-ev  st = let q = rs_M3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM3 .fwd .on-tau st = let q = rs_M3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM3 .bwd .on-ev  st = let q = rs_M3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM3 .bwd .on-tau st = let q = rs_M3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM3 .div→ d = ⊥-elim (spec-nd-loop sStr0 d)
mkDRˢ rsM3 .div← d = ⊥-elim (nd-M3 d)
mkDRˢ rsM6 .fwd .on-ev  st = let q = rs_M6_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM6 .fwd .on-tau st = let q = rs_M6_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM6 .bwd .on-ev  st = let q = rs_M6_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM6 .bwd .on-tau st = let q = rs_M6_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM6 .div→ d = ⊥-elim (spec-nd-loop sStr0 d)
mkDRˢ rsM6 .div← d = ⊥-elim (nd-M6 d)
mkDRˢ rsM9′ .fwd .on-ev  st = let q = rs_M9p_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM9′ .fwd .on-tau st = let q = rs_M9p_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM9′ .bwd .on-ev  st = let q = rs_M9p_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM9′ .bwd .on-tau st = let q = rs_M9p_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM9′ .div→ d = ⊥-elim (spec-nd-loop sStr0 d)
mkDRˢ rsM9′ .div← d = ⊥-elim (nd-M9 d)
mkDRˢ rsM5′ .fwd .on-ev  st = let q = rs_M5p_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM5′ .fwd .on-tau st = let q = rs_M5p_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM5′ .bwd .on-ev  st = let q = rs_M5p_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM5′ .bwd .on-tau st = let q = rs_M5p_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM5′ .div→ d = ⊥-elim (spec-nd-loop sStr0 d)
mkDRˢ rsM5′ .div← d = ⊥-elim (nd-M5 d)
mkDRˢ (rsVocc1 b) .fwd .on-ev  st = let q = rs_Vocc1_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsVocc1 b) .fwd .on-tau st = let q = rs_Vocc1_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsVocc1 b) .bwd .on-ev  st = let q = rs_Vocc1_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsVocc1 b) .bwd .on-tau st = let q = rs_Vocc1_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsVocc1 b) .div→ d = ⊥-elim (spec-nd-IT sStr1 d)
mkDRˢ (rsVocc1 b) .div← d = ⊥-elim (nd-Vocc1 d)
mkDRˢ (rsW4 b) .fwd .on-ev  st = let q = rs_W4_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4 b) .fwd .on-tau st = let q = rs_W4_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4 b) .bwd .on-ev  st = let q = rs_W4_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4 b) .bwd .on-tau st = let q = rs_W4_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4 b) .div→ d = ⊥-elim (spec-nd-IT sStr1 d)
mkDRˢ (rsW4 b) .div← d = ⊥-elim (nd-W4 d)
mkDRˢ (rsW4′ b) .fwd .on-ev  st = let q = rs_W4p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4′ b) .fwd .on-tau st = let q = rs_W4p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4′ b) .bwd .on-ev  st = let q = rs_W4p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4′ b) .bwd .on-tau st = let q = rs_W4p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsW4′ b) .div← d = ⊥-elim (nd-W4 d)
mkDRˢ (rsW5 b) .fwd .on-ev  st = let q = rs_W5_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW5 b) .fwd .on-tau st = let q = rs_W5_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW5 b) .bwd .on-ev  st = let q = rs_W5_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW5 b) .bwd .on-tau st = let q = rs_W5_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW5 b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsW5 b) .div← d = ⊥-elim (nd-W5 d)
mkDRˢ (rsW3 b) .fwd .on-ev  st = let q = rs_W3_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3 b) .fwd .on-tau st = let q = rs_W3_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3 b) .bwd .on-ev  st = let q = rs_W3_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3 b) .bwd .on-tau st = let q = rs_W3_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3 b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsW3 b) .div← d = ⊥-elim (nd-W3 d)
mkDRˢ (rsW b) .fwd .on-ev  st = let q = rs_W_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW b) .fwd .on-tau st = let q = rs_W_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW b) .bwd .on-ev  st = let q = rs_W_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW b) .bwd .on-tau st = let q = rs_W_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsW b) .div← d = ⊥-elim (nd-W d)
mkDRˢ (rsWX1 b) .fwd .on-ev  st = let q = rs_WX1_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX1 b) .fwd .on-tau st = let q = rs_WX1_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX1 b) .bwd .on-ev  st = let q = rs_WX1_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX1 b) .bwd .on-tau st = let q = rs_WX1_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX1 b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsWX1 b) .div← d = ⊥-elim (nd-WX1 d)
mkDRˢ (rsWX3 b) .fwd .on-ev  st = let q = rs_WX3_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX3 b) .fwd .on-tau st = let q = rs_WX3_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX3 b) .bwd .on-ev  st = let q = rs_WX3_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX3 b) .bwd .on-tau st = let q = rs_WX3_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX3 b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsWX3 b) .div← d = ⊥-elim (nd-WX3 d)
mkDRˢ (rsWX3a b) .fwd .on-ev  st = let q = rs_WX3a_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX3a b) .fwd .on-tau st = let q = rs_WX3a_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX3a b) .bwd .on-ev  st = let q = rs_WX3a_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX3a b) .bwd .on-tau st = let q = rs_WX3a_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX3a b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsWX3a b) .div← d = ⊥-elim (nd-WX3a d)
mkDRˢ (rsW2 b) .fwd .on-ev  st = let q = rs_W2_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2 b) .fwd .on-tau st = let q = rs_W2_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2 b) .bwd .on-ev  st = let q = rs_W2_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2 b) .bwd .on-tau st = let q = rs_W2_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2 b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsW2 b) .div← d = ⊥-elim (nd-W2 d)
mkDRˢ (rsWh b) .fwd .on-ev  st = let q = rs_Wh_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWh b) .fwd .on-tau st = let q = rs_Wh_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWh b) .bwd .on-ev  st = let q = rs_Wh_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWh b) .bwd .on-tau st = let q = rs_Wh_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWh b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsWh b) .div← d = ⊥-elim (nd-Wh d)
mkDRˢ (rsW2d b) .fwd .on-ev  st = let q = rs_W2d_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2d b) .fwd .on-tau st = let q = rs_W2d_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2d b) .bwd .on-ev  st = let q = rs_W2d_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2d b) .bwd .on-tau st = let q = rs_W2d_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2d b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsW2d b) .div← d = ⊥-elim (nd-W2d d)
mkDRˢ (rsWX2 b) .fwd .on-ev  st = let q = rs_WX2_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX2 b) .fwd .on-tau st = let q = rs_WX2_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX2 b) .bwd .on-ev  st = let q = rs_WX2_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX2 b) .bwd .on-tau st = let q = rs_WX2_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX2 b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsWX2 b) .div← d = ⊥-elim (nd-WX2 d)
mkDRˢ (rsW2a b b′) .fwd .on-ev  st = let q = rs_W2a_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2a b b′) .fwd .on-tau st = let q = rs_W2a_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2a b b′) .bwd .on-ev  st = let q = rs_W2a_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2a b b′) .bwd .on-tau st = let q = rs_W2a_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2a b b′) .div→ d = ⊥-elim (spec-nd-IT sStr2 d)
mkDRˢ (rsW2a b b′) .div← d = ⊥-elim (nd-W2a d)
mkDRˢ (rsW2h b b′) .fwd .on-ev  st = let q = rs_W2h_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2h b b′) .fwd .on-tau st = let q = rs_W2h_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2h b b′) .bwd .on-ev  st = let q = rs_W2h_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2h b b′) .bwd .on-tau st = let q = rs_W2h_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2h b b′) .div→ d = ⊥-elim (spec-nd-loop sStr2 d)
mkDRˢ (rsW2h b b′) .div← d = ⊥-elim (nd-W2h d)
mkDRˢ (rsW2e b b′) .fwd .on-ev  st = let q = rs_W2e_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2e b b′) .fwd .on-tau st = let q = rs_W2e_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2e b b′) .bwd .on-ev  st = let q = rs_W2e_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2e b b′) .bwd .on-tau st = let q = rs_W2e_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2e b b′) .div→ d = ⊥-elim (spec-nd-IT sStr2 d)
mkDRˢ (rsW2e b b′) .div← d = ⊥-elim (nd-W2e d)
mkDRˢ (rsW3b b b′) .fwd .on-ev  st = let q = rs_W3b_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3b b b′) .fwd .on-tau st = let q = rs_W3b_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3b b b′) .bwd .on-ev  st = let q = rs_W3b_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3b b b′) .bwd .on-tau st = let q = rs_W3b_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3b b b′) .div→ d = ⊥-elim (spec-nd-IT sStr2 d)
mkDRˢ (rsW3b b b′) .div← d = ⊥-elim (nd-W3b d)
mkDRˢ (rsW3a b b′) .fwd .on-ev  st = let q = rs_W3a_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3a b b′) .fwd .on-tau st = let q = rs_W3a_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3a b b′) .bwd .on-ev  st = let q = rs_W3a_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3a b b′) .bwd .on-tau st = let q = rs_W3a_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3a b b′) .div→ d = ⊥-elim (spec-nd-blk1 d)
mkDRˢ (rsW3a b b′) .div← d = ⊥-elim (nd-W3a d)
mkDRˢ (rsW3d b b′) .fwd .on-ev  st = let q = rs_W3d_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3d b b′) .fwd .on-tau st = let q = rs_W3d_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3d b b′) .bwd .on-ev  st = let q = rs_W3d_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3d b b′) .bwd .on-tau st = let q = rs_W3d_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3d b b′) .div→ d = ⊥-elim (spec-nd-blk1 d)
mkDRˢ (rsW3d b b′) .div← d = ⊥-elim (nd-W3d d)
mkDRˢ (rsW3e b b′ b″) .fwd .on-ev  st = let q = rs_W3e_bwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3e b b′ b″) .fwd .on-tau st = let q = rs_W3e_bwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3e b b′ b″) .bwd .on-ev  st = let q = rs_W3e_fwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3e b b′ b″) .bwd .on-tau st = let q = rs_W3e_fwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3e b b′ b″) .div→ d = ⊥-elim (spec-nd-IT sStr3 d)
mkDRˢ (rsW3e b b′ b″) .div← d = ⊥-elim (nd-W3e d)
mkDRˢ (rsIBblksb b) .fwd .on-ev  st = let q = rs_IBblksb_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsIBblksb b) .fwd .on-tau st = let q = rs_IBblksb_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsIBblksb b) .bwd .on-ev  st = let q = rs_IBblksb_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsIBblksb b) .bwd .on-tau st = let q = rs_IBblksb_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsIBblksb b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsIBblksb b) .div← d = ⊥-elim (nd-IBblksb d)
mkDRˢ (rsLbBLKsb b) .fwd .on-ev  st = let q = rs_LbBLKsb_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsLbBLKsb b) .fwd .on-tau st = let q = rs_LbBLKsb_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsLbBLKsb b) .bwd .on-ev  st = let q = rs_LbBLKsb_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsLbBLKsb b) .bwd .on-tau st = let q = rs_LbBLKsb_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsLbBLKsb b) .div→ d = ⊥-elim (spec-nd-blk0 d)
mkDRˢ (rsLbBLKsb b) .div← d = ⊥-elim (nd-LbBLKsb d)
mkDRˢ rsIBbdsb .fwd .on-ev  st = let q = rs_IBbdsb_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIBbdsb .fwd .on-tau st = let q = rs_IBbdsb_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsIBbdsb .bwd .on-ev  st = let q = rs_IBbdsb_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIBbdsb .bwd .on-tau st = let q = rs_IBbdsb_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsIBbdsb .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsIBbdsb .div← d = ⊥-elim (nd-IBbdsb d)
mkDRˢ rsLbBDsb .fwd .on-ev  st = let q = rs_LbBDsb_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbBDsb .fwd .on-tau st = let q = rs_LbBDsb_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsLbBDsb .bwd .on-ev  st = let q = rs_LbBDsb_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbBDsb .bwd .on-tau st = let q = rs_LbBDsb_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsLbBDsb .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsLbBDsb .div← d = ⊥-elim (nd-LbBDsb d)
mkDRˢ rsBD0e .fwd .on-ev  st = let q = rs_BD0e_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0e .fwd .on-tau st = let q = rs_BD0e_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0e .bwd .on-ev  st = let q = rs_BD0e_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0e .bwd .on-tau st = let q = rs_BD0e_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0e .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsBD0e .div← d = ⊥-elim (nd-BD0e d)
mkDRˢ rsBD0a .fwd .on-ev  st = let q = rs_BD0a_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0a .fwd .on-tau st = let q = rs_BD0a_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0a .bwd .on-ev  st = let q = rs_BD0a_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0a .bwd .on-tau st = let q = rs_BD0a_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0a .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsBD0a .div← d = ⊥-elim (nd-BD0a d)
mkDRˢ rsBD0h .fwd .on-ev  st = let q = rs_BD0h_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0h .fwd .on-tau st = let q = rs_BD0h_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0h .bwd .on-ev  st = let q = rs_BD0h_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0h .bwd .on-tau st = let q = rs_BD0h_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0h .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsBD0h .div← d = ⊥-elim (nd-BD0h d)
mkDRˢ rsBX1 .fwd .on-ev  st = let q = rs_BX1_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX1 .fwd .on-tau st = let q = rs_BX1_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX1 .bwd .on-ev  st = let q = rs_BX1_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX1 .bwd .on-tau st = let q = rs_BX1_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX1 .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsBX1 .div← d = ⊥-elim (nd-BX1 d)
mkDRˢ rsBX2 .fwd .on-ev  st = let q = rs_BX2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX2 .fwd .on-tau st = let q = rs_BX2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX2 .bwd .on-ev  st = let q = rs_BX2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX2 .bwd .on-tau st = let q = rs_BX2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX2 .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsBX2 .div← d = ⊥-elim (nd-BX2 d)
mkDRˢ rsBX3 .fwd .on-ev  st = let q = rs_BX3_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX3 .fwd .on-tau st = let q = rs_BX3_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX3 .bwd .on-ev  st = let q = rs_BX3_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX3 .bwd .on-tau st = let q = rs_BX3_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX3 .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsBX3 .div← d = ⊥-elim (nd-BX3 d)
mkDRˢ rsBX3a .fwd .on-ev  st = let q = rs_BX3a_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX3a .fwd .on-tau st = let q = rs_BX3a_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX3a .bwd .on-ev  st = let q = rs_BX3a_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX3a .bwd .on-tau st = let q = rs_BX3a_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX3a .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsBX3a .div← d = ⊥-elim (nd-BX3a d)
mkDRˢ rsBD1d .fwd .on-ev  st = let q = rs_BD1d_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD1d .fwd .on-tau st = let q = rs_BD1d_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD1d .bwd .on-ev  st = let q = rs_BD1d_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD1d .bwd .on-tau st = let q = rs_BD1d_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD1d .div→ d = ⊥-elim (spec-nd-bd0 d)
mkDRˢ rsBD1d .div← d = ⊥-elim (nd-BD1d d)
mkDRˢ (rsBD1a b) .fwd .on-ev  st = let q = rs_BD1a_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1a b) .fwd .on-tau st = let q = rs_BD1a_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1a b) .bwd .on-ev  st = let q = rs_BD1a_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1a b) .bwd .on-tau st = let q = rs_BD1a_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1a b) .div→ d = ⊥-elim (spec-nd-IT sStrD1 d)
mkDRˢ (rsBD1a b) .div← d = ⊥-elim (nd-BD1a d)
mkDRˢ (rsBD1e b) .fwd .on-ev  st = let q = rs_BD1e_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1e b) .fwd .on-tau st = let q = rs_BD1e_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1e b) .bwd .on-ev  st = let q = rs_BD1e_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1e b) .bwd .on-tau st = let q = rs_BD1e_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1e b) .div→ d = ⊥-elim (spec-nd-IT sStrD1 d)
mkDRˢ (rsBD1e b) .div← d = ⊥-elim (nd-BD1e d)
mkDRˢ (rsBD1h b) .fwd .on-ev  st = let q = rs_BD1h_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1h b) .fwd .on-tau st = let q = rs_BD1h_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1h b) .bwd .on-ev  st = let q = rs_BD1h_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1h b) .bwd .on-tau st = let q = rs_BD1h_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1h b) .div→ d = ⊥-elim (spec-nd-IT sStrD1 d)
mkDRˢ (rsBD1h b) .div← d = ⊥-elim (nd-BD1h d)
mkDRˢ (rsBD2b b) .fwd .on-ev  st = let q = rs_BD2b_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2b b) .fwd .on-tau st = let q = rs_BD2b_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2b b) .bwd .on-ev  st = let q = rs_BD2b_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2b b) .bwd .on-tau st = let q = rs_BD2b_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2b b) .div→ d = ⊥-elim (spec-nd-IT sStrD1 d)
mkDRˢ (rsBD2b b) .div← d = ⊥-elim (nd-BD2b d)
mkDRˢ (rsBD2a b) .fwd .on-ev  st = let q = rs_BD2a_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2a b) .fwd .on-tau st = let q = rs_BD2a_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2a b) .bwd .on-ev  st = let q = rs_BD2a_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2a b) .bwd .on-tau st = let q = rs_BD2a_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2a b) .div→ d = ⊥-elim (spec-nd-bd1 d)
mkDRˢ (rsBD2a b) .div← d = ⊥-elim (nd-BD2a d)
mkDRˢ (rsBD2d b) .fwd .on-ev  st = let q = rs_BD2d_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2d b) .fwd .on-tau st = let q = rs_BD2d_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2d b) .bwd .on-ev  st = let q = rs_BD2d_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2d b) .bwd .on-tau st = let q = rs_BD2d_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2d b) .div→ d = ⊥-elim (spec-nd-bd1 d)
mkDRˢ (rsBD2d b) .div← d = ⊥-elim (nd-BD2d d)
mkDRˢ (rsBD2e b b′) .fwd .on-ev  st = let q = rs_BD2e_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2e b b′) .fwd .on-tau st = let q = rs_BD2e_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2e b b′) .bwd .on-ev  st = let q = rs_BD2e_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2e b b′) .bwd .on-tau st = let q = rs_BD2e_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2e b b′) .div→ d = ⊥-elim (spec-nd-IT sStrD2 d)
mkDRˢ (rsBD2e b b′) .div← d = ⊥-elim (nd-BD2e d)
mkDRˢ rsN3D0 .fwd .on-ev  st = let q = rs_N3D0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN3D0 .fwd .on-tau st = let q = rs_N3D0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN3D0 .bwd .on-ev  st = let q = rs_N3D0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN3D0 .bwd .on-tau st = let q = rs_N3D0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN3D0 .div→ d = ⊥-elim (spec-nd-strD0 d)
mkDRˢ rsN3D0 .div← d = ⊥-elim (nd-N3 d)
mkDRˢ rsN5D0 .fwd .on-ev  st = let q = rs_N5D0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN5D0 .fwd .on-tau st = let q = rs_N5D0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN5D0 .bwd .on-ev  st = let q = rs_N5D0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN5D0 .bwd .on-tau st = let q = rs_N5D0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN5D0 .div→ d = ⊥-elim (spec-nd-strD0 d)
mkDRˢ rsN5D0 .div← d = ⊥-elim (nd-N5 d)
mkDRˢ rsN6D0 .fwd .on-ev  st = let q = rs_N6D0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN6D0 .fwd .on-tau st = let q = rs_N6D0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN6D0 .bwd .on-ev  st = let q = rs_N6D0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN6D0 .bwd .on-tau st = let q = rs_N6D0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN6D0 .div→ d = ⊥-elim (spec-nd-strD0 d)
mkDRˢ rsN6D0 .div← d = ⊥-elim (nd-N6 d)
mkDRˢ rsN9D0 .fwd .on-ev  st = let q = rs_N9D0_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN9D0 .fwd .on-tau st = let q = rs_N9D0_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN9D0 .bwd .on-ev  st = let q = rs_N9D0_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN9D0 .bwd .on-tau st = let q = rs_N9D0_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN9D0 .div→ d = ⊥-elim (spec-nd-strD0 d)
mkDRˢ rsN9D0 .div← d = ⊥-elim (nd-N9 d)
mkDRˢ rsN3D0s .fwd .on-ev  st = let q = rs_N3D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN3D0s .fwd .on-tau st = let q = rs_N3D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN3D0s .bwd .on-ev  st = let q = rs_N3D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN3D0s .bwd .on-tau st = let q = rs_N3D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN3D0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsN3D0s .div← d = ⊥-elim (nd-N3 d)
mkDRˢ rsN5D0s .fwd .on-ev  st = let q = rs_N5D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN5D0s .fwd .on-tau st = let q = rs_N5D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN5D0s .bwd .on-ev  st = let q = rs_N5D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN5D0s .bwd .on-tau st = let q = rs_N5D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN5D0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsN5D0s .div← d = ⊥-elim (nd-N5 d)
mkDRˢ rsBD0eD0s .fwd .on-ev  st = let q = rs_BD0eD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0eD0s .fwd .on-tau st = let q = rs_BD0eD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0eD0s .bwd .on-ev  st = let q = rs_BD0eD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0eD0s .bwd .on-tau st = let q = rs_BD0eD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0eD0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsBD0eD0s .div← d = ⊥-elim (nd-BD0e d)
mkDRˢ rsBD0hD0s .fwd .on-ev  st = let q = rs_BD0hD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0hD0s .fwd .on-tau st = let q = rs_BD0hD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0hD0s .bwd .on-ev  st = let q = rs_BD0hD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0hD0s .bwd .on-tau st = let q = rs_BD0hD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0hD0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsBD0hD0s .div← d = ⊥-elim (nd-BD0h d)
mkDRˢ rsBD0aD0s .fwd .on-ev  st = let q = rs_BD0aD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0aD0s .fwd .on-tau st = let q = rs_BD0aD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD0aD0s .bwd .on-ev  st = let q = rs_BD0aD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0aD0s .bwd .on-tau st = let q = rs_BD0aD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD0aD0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsBD0aD0s .div← d = ⊥-elim (nd-BD0a d)
mkDRˢ rsBX1D0s .fwd .on-ev  st = let q = rs_BX1D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX1D0s .fwd .on-tau st = let q = rs_BX1D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX1D0s .bwd .on-ev  st = let q = rs_BX1D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX1D0s .bwd .on-tau st = let q = rs_BX1D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX1D0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsBX1D0s .div← d = ⊥-elim (nd-BX1 d)
mkDRˢ rsBX2D0s .fwd .on-ev  st = let q = rs_BX2D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX2D0s .fwd .on-tau st = let q = rs_BX2D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX2D0s .bwd .on-ev  st = let q = rs_BX2D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX2D0s .bwd .on-tau st = let q = rs_BX2D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX2D0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsBX2D0s .div← d = ⊥-elim (nd-BX2 d)
mkDRˢ rsBX3D0s .fwd .on-ev  st = let q = rs_BX3D0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX3D0s .fwd .on-tau st = let q = rs_BX3D0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX3D0s .bwd .on-ev  st = let q = rs_BX3D0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX3D0s .bwd .on-tau st = let q = rs_BX3D0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX3D0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsBX3D0s .div← d = ⊥-elim (nd-BX3 d)
mkDRˢ rsBX3aD0s .fwd .on-ev  st = let q = rs_BX3aD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX3aD0s .fwd .on-tau st = let q = rs_BX3aD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBX3aD0s .bwd .on-ev  st = let q = rs_BX3aD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX3aD0s .bwd .on-tau st = let q = rs_BX3aD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBX3aD0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsBX3aD0s .div← d = ⊥-elim (nd-BX3a d)
mkDRˢ rsBD1dD0s .fwd .on-ev  st = let q = rs_BD1dD0s_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD1dD0s .fwd .on-tau st = let q = rs_BD1dD0s_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsBD1dD0s .bwd .on-ev  st = let q = rs_BD1dD0s_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD1dD0s .bwd .on-tau st = let q = rs_BD1dD0s_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsBD1dD0s .div→ d = ⊥-elim (spec-nd-loop-strD0 d)
mkDRˢ rsBD1dD0s .div← d = ⊥-elim (nd-BD1d d)
mkDRˢ (rsBD2aD1s b) .fwd .on-ev  st = let q = rs_BD2aD1s_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2aD1s b) .fwd .on-tau st = let q = rs_BD2aD1s_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2aD1s b) .bwd .on-ev  st = let q = rs_BD2aD1s_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2aD1s b) .bwd .on-tau st = let q = rs_BD2aD1s_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2aD1s b) .div→ d = ⊥-elim (spec-nd-loop sStrD1 d)
mkDRˢ (rsBD2aD1s b) .div← d = ⊥-elim (nd-BD2a d)
mkDRˢ (rsBD2bD1s b) .fwd .on-ev  st = let q = rs_BD2bD1s_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2bD1s b) .fwd .on-tau st = let q = rs_BD2bD1s_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2bD1s b) .bwd .on-ev  st = let q = rs_BD2bD1s_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2bD1s b) .bwd .on-tau st = let q = rs_BD2bD1s_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2bD1s b) .div→ d = ⊥-elim (spec-nd-loop sStrD1 d)
mkDRˢ (rsBD2bD1s b) .div← d = ⊥-elim (nd-BD2b d)
mkDRˢ (rsBD2dD1s b) .fwd .on-ev  st = let q = rs_BD2dD1s_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2dD1s b) .fwd .on-tau st = let q = rs_BD2dD1s_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2dD1s b) .bwd .on-ev  st = let q = rs_BD2dD1s_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2dD1s b) .bwd .on-tau st = let q = rs_BD2dD1s_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2dD1s b) .div→ d = ⊥-elim (spec-nd-loop sStrD1 d)
mkDRˢ (rsBD2dD1s b) .div← d = ⊥-elim (nd-BD2d d)
mkDRˢ (rsBD1e′ b) .fwd .on-ev  st = let q = rs_BD1ep_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1e′ b) .fwd .on-tau st = let q = rs_BD1ep_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1e′ b) .bwd .on-ev  st = let q = rs_BD1ep_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1e′ b) .bwd .on-tau st = let q = rs_BD1ep_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1e′ b) .div→ d = ⊥-elim (spec-nd-bd1 d)
mkDRˢ (rsBD1e′ b) .div← d = ⊥-elim (nd-BD1e d)
mkDRˢ (rsBD1eD1s b) .fwd .on-ev  st = let q = rs_BD1eD1s_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1eD1s b) .fwd .on-tau st = let q = rs_BD1eD1s_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD1eD1s b) .bwd .on-ev  st = let q = rs_BD1eD1s_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1eD1s b) .bwd .on-tau st = let q = rs_BD1eD1s_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD1eD1s b) .div→ d = ⊥-elim (spec-nd-loop sStrD1 d)
mkDRˢ (rsBD1eD1s b) .div← d = ⊥-elim (nd-BD1e d)
mkDRˢ (rsBD2b′ b) .fwd .on-ev  st = let q = rs_BD2bp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2b′ b) .fwd .on-tau st = let q = rs_BD2bp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2b′ b) .bwd .on-ev  st = let q = rs_BD2bp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2b′ b) .bwd .on-tau st = let q = rs_BD2bp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2b′ b) .div→ d = ⊥-elim (spec-nd-bd1 d)
mkDRˢ (rsBD2b′ b) .div← d = ⊥-elim (nd-BD2b d)
mkDRˢ (rsBD2e′ b b′) .fwd .on-ev  st = let q = rs_BD2ep_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2e′ b b′) .fwd .on-tau st = let q = rs_BD2ep_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2e′ b b′) .bwd .on-ev  st = let q = rs_BD2ep_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2e′ b b′) .bwd .on-tau st = let q = rs_BD2ep_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2e′ b b′) .div→ d = ⊥-elim (spec-nd-bd2 d)
mkDRˢ (rsBD2e′ b b′) .div← d = ⊥-elim (nd-BD2e d)
mkDRˢ (rsBD2eD2s b b′) .fwd .on-ev  st = let q = rs_BD2eD2s_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2eD2s b b′) .fwd .on-tau st = let q = rs_BD2eD2s_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsBD2eD2s b b′) .bwd .on-ev  st = let q = rs_BD2eD2s_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2eD2s b b′) .bwd .on-tau st = let q = rs_BD2eD2s_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsBD2eD2s b b′) .div→ d = ⊥-elim (spec-nd-loop sStrD2 d)
mkDRˢ (rsBD2eD2s b b′) .div← d = ⊥-elim (nd-BD2e d)
mkDRˢ (rsW′ b) .fwd .on-ev  st = let q = rs_Wp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW′ b) .fwd .on-tau st = let q = rs_Wp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW′ b) .bwd .on-ev  st = let q = rs_Wp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW′ b) .bwd .on-tau st = let q = rs_Wp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsW′ b) .div← d = ⊥-elim (nd-W d)
mkDRˢ (rsWh′ b) .fwd .on-ev  st = let q = rs_Whp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWh′ b) .fwd .on-tau st = let q = rs_Whp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWh′ b) .bwd .on-ev  st = let q = rs_Whp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWh′ b) .bwd .on-tau st = let q = rs_Whp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWh′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsWh′ b) .div← d = ⊥-elim (nd-Wh d)
mkDRˢ (rsWX3a′ b) .fwd .on-ev  st = let q = rs_WX3ap_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX3a′ b) .fwd .on-tau st = let q = rs_WX3ap_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX3a′ b) .bwd .on-ev  st = let q = rs_WX3ap_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX3a′ b) .bwd .on-tau st = let q = rs_WX3ap_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX3a′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsWX3a′ b) .div← d = ⊥-elim (nd-WX3a d)
mkDRˢ (rsWX1′ b) .fwd .on-ev  st = let q = rs_WX1p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX1′ b) .fwd .on-tau st = let q = rs_WX1p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX1′ b) .bwd .on-ev  st = let q = rs_WX1p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX1′ b) .bwd .on-tau st = let q = rs_WX1p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX1′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsWX1′ b) .div← d = ⊥-elim (nd-WX1 d)
mkDRˢ (rsWX3′ b) .fwd .on-ev  st = let q = rs_WX3p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX3′ b) .fwd .on-tau st = let q = rs_WX3p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX3′ b) .bwd .on-ev  st = let q = rs_WX3p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX3′ b) .bwd .on-tau st = let q = rs_WX3p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX3′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsWX3′ b) .div← d = ⊥-elim (nd-WX3 d)
mkDRˢ (rsWX2′ b) .fwd .on-ev  st = let q = rs_WX2p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX2′ b) .fwd .on-tau st = let q = rs_WX2p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWX2′ b) .bwd .on-ev  st = let q = rs_WX2p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX2′ b) .bwd .on-tau st = let q = rs_WX2p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWX2′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsWX2′ b) .div← d = ⊥-elim (nd-WX2 d)
mkDRˢ (rsW2′ b) .fwd .on-ev  st = let q = rs_W2p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2′ b) .fwd .on-tau st = let q = rs_W2p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2′ b) .bwd .on-ev  st = let q = rs_W2p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2′ b) .bwd .on-tau st = let q = rs_W2p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsW2′ b) .div← d = ⊥-elim (nd-W2 d)
mkDRˢ (rsW2d′ b) .fwd .on-ev  st = let q = rs_W2dp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2d′ b) .fwd .on-tau st = let q = rs_W2dp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2d′ b) .bwd .on-ev  st = let q = rs_W2dp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2d′ b) .bwd .on-tau st = let q = rs_W2dp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2d′ b) .div→ d = ⊥-elim (spec-nd-loop sStr1 d)
mkDRˢ (rsW2d′ b) .div← d = ⊥-elim (nd-W2d d)
mkDRˢ (rsW3a′ b b′) .fwd .on-ev  st = let q = rs_W3ap_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3a′ b b′) .fwd .on-tau st = let q = rs_W3ap_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3a′ b b′) .bwd .on-ev  st = let q = rs_W3ap_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3a′ b b′) .bwd .on-tau st = let q = rs_W3ap_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3a′ b b′) .div→ d = ⊥-elim (spec-nd-loop sStr2 d)
mkDRˢ (rsW3a′ b b′) .div← d = ⊥-elim (nd-W3a d)
mkDRˢ (rsW3d′ b b′) .fwd .on-ev  st = let q = rs_W3dp_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3d′ b b′) .fwd .on-tau st = let q = rs_W3dp_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3d′ b b′) .bwd .on-ev  st = let q = rs_W3dp_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3d′ b b′) .bwd .on-tau st = let q = rs_W3dp_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3d′ b b′) .div→ d = ⊥-elim (spec-nd-loop sStr2 d)
mkDRˢ (rsW3d′ b b′) .div← d = ⊥-elim (nd-W3d d)
mkDRˢ (rsW2e′ b b′) .fwd .on-ev  st = let q = rs_W2ep_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2e′ b b′) .fwd .on-tau st = let q = rs_W2ep_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2e′ b b′) .bwd .on-ev  st = let q = rs_W2ep_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2e′ b b′) .bwd .on-tau st = let q = rs_W2ep_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2e′ b b′) .div→ d = ⊥-elim (spec-nd-blk1 d)
mkDRˢ (rsW2e′ b b′) .div← d = ⊥-elim (nd-W2e d)
mkDRˢ (rsW3b′ b b′) .fwd .on-ev  st = let q = rs_W3bp_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3b′ b b′) .fwd .on-tau st = let q = rs_W3bp_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3b′ b b′) .bwd .on-ev  st = let q = rs_W3bp_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3b′ b b′) .bwd .on-tau st = let q = rs_W3bp_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3b′ b b′) .div→ d = ⊥-elim (spec-nd-blk1 d)
mkDRˢ (rsW3b′ b b′) .div← d = ⊥-elim (nd-W3b d)
mkDRˢ (rsW3e′ b b′ b″) .fwd .on-ev  st = let q = rs_W3ep_bwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3e′ b b′ b″) .fwd .on-tau st = let q = rs_W3ep_bwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3e′ b b′ b″) .bwd .on-ev  st = let q = rs_W3ep_fwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3e′ b b′ b″) .bwd .on-tau st = let q = rs_W3ep_fwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3e′ b b′ b″) .div→ d = ⊥-elim (spec-nd-blk2 d)
mkDRˢ (rsW3e′ b b′ b″) .div← d = ⊥-elim (nd-W3e d)
mkDRˢ (rsW3e″ b b′ b″) .fwd .on-ev  st = let q = rs_W3eq_bwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3e″ b b′ b″) .fwd .on-tau st = let q = rs_W3eq_bwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3e″ b b′ b″) .bwd .on-ev  st = let q = rs_W3eq_fwd_ev b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3e″ b b′ b″) .bwd .on-tau st = let q = rs_W3eq_fwd_tau b b′ b″ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3e″ b b′ b″) .div→ d = ⊥-elim (spec-nd-loop sStr3 d)
mkDRˢ (rsW3e″ b b′ b″) .div← d = ⊥-elim (nd-W3e d)
mkDRˢ (rsW2hI b b′) .fwd .on-ev  st = let q = rs_W2hI_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2hI b b′) .fwd .on-tau st = let q = rs_W2hI_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2hI b b′) .bwd .on-ev  st = let q = rs_W2hI_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2hI b b′) .bwd .on-tau st = let q = rs_W2hI_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2hI b b′) .div→ d = ⊥-elim (spec-nd-IT sStr2 d)
mkDRˢ (rsW2hI b b′) .div← d = ⊥-elim (nd-W2h d)
mkDRˢ rsDL .fwd .on-ev  st = let q = rs_DL_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsDL .fwd .on-tau st = let q = rs_DL_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsDL .bwd .on-ev  st = let q = rs_DL_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsDL .bwd .on-tau st = let q = rs_DL_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsDL .div→ d = ⊥-elim (deadlock-converges d)
mkDRˢ rsDL .div← d = ⊥-elim (deadlock-converges d)

------------------------------------------------------------------------
-- THE THEOREM: BFnetSpec ∖ bfMsgES ≈DR networkBF.
-- (networkBF ≡ JN (Inner (ICn stIdle) (ISn stIdle)) Cidle and BFnetSpec ≡
--  IT nIdle both hold definitionally — networkBF already hides ioBF — so the
--  witnessing relation is exactly mkDR rsIdle, re-oriented by drbisim-sym.)
------------------------------------------------------------------------
-- the cap-3 sequential spec and the copy-medium network are ≈DR (msgs hidden).
netSpec≈DR : (BFnetSpec ∖ bfMsgES) ≈DR networkBF
netSpec≈DR = drbisim-sym (mkDR rsIdle)

-- failures-divergences equivalence, via the DR→FD bridge.
netSpec≈FD : (BFnetSpec ∖ bfMsgES) ≈FD networkBF
netSpec≈FD = drbisim→≈FD netSpec≈DR

-- FD refinement, both directions (≈FD unfolds to mutual ⊑FD).
spec⊑FD-net : (BFnetSpec ∖ bfMsgES) ⊑FD networkBF
spec⊑FD-net = proj₁ netSpec≈FD

net⊑FD-spec : networkBF ⊑FD (BFnetSpec ∖ bfMsgES)
net⊑FD-spec = proj₂ netSpec≈FD
